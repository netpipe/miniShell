#!/usr/bin/env python3
"""Throw malformed and adversarial input at the shell and look for crashes,
hangs, and sanitizer complaints.  Wrong output is fine here; dying is not."""
import subprocess, sys, os, tempfile, random, itertools

MSH = os.path.abspath(sys.argv[1])
SEED = int(sys.argv[2]) if len(sys.argv) > 2 else 1

HAND = [
    "", " ", "\n", "\n\n\n", "#", "# comment only",
    "[", "]", "[ ]", "[ ", "test", "test -", "[ a", "[ a =", "[ a = ]",
    "[ ( ]", "[ ( 1 = 1 ]", "[ ! ]", "[ -a ]", "[ a -a ]", "[ -f ]",
    "echo ${", "echo ${}", "echo ${:-}", "echo ${x:", "echo ${x:-",
    "echo ${#}", "echo ${##}", "echo ${x#", "echo ${x%%", "echo ${1}",
    "echo $", "echo $$", "echo $?", "echo $!", "echo $@", "echo $*", "echo $#",
    "echo $(", "echo $()", "echo $((", "echo $(()", "echo $(())",
    "echo $((1/0))", "echo $((1%0))", "echo $((()))", "echo $((a b))",
    "echo $((999999999999999999999999))", "echo $((1+))", "echo $((+))",
    "echo `", "echo ``", "echo `echo`", "echo `echo `echo``",
    'echo "', "echo '", "echo \\", 'echo "$', "echo '$", 'echo "`',
    "{", "}", "{ }", "{ ; }", "(", ")", "()", "( )", "(;)",
    "|", "||", "&&", "&", ";", ";;", "; ;", "|&", "> ", "< ", ">>", "<<",
    "echo |", "| echo", "echo ||", "echo &&", "echo a |", "echo a &&",
    "if", "if ;", "if then", "if true", "if true; then", "if true; then fi",
    "then", "else", "elif", "fi", "do", "done", "esac", "in",
    "while", "while ;", "while true", "while true; do", "until", "until true; do",
    "for", "for i", "for i in", "for i in a", "for i in a; do", "for ; do done",
    "for 1 in a; do echo; done", 'for "x" in a; do echo; done',
    "case", "case x", "case x in", "case x in esac", "case x in )", "case x in *)",
    "case x in *) ;;", "case x in *) echo ;; esac", "case in in in) echo;; esac",
    "f()", "f() {", "f() { }", "f(){ f; }", "() { echo; }", "f() ; ",
    "function", "function f", "function f {", "function f { echo; }",
    "break", "continue", "return", "shift", "shift 99", "shift -1",
    "exit abc", "exit -1", "exit 999", "set -", "set -q", "set --",
    "local x", "read", "read 1x", "printf", 'printf "%"', 'printf "%z" a',
    'printf "%s"', 'printf "%d" notanumber', 'printf "%999999999d" 1',
    "unset", "unset 1x", "export 1x", "export =", "cd / / /",
    ". ", ". /nonexistent", "eval", "eval 'eval eval'", "eval '('",
    "<<EOF", "cat <<EOF", "cat <<EOF\n", "cat <<", "cat <<-",
    "cat <<EOF\nunterminated",
    "echo a > /", "echo a > ''", "echo a 99999999>x", "echo a 3>&99",
    "echo a >&-", "echo a <&-", "exec 3>&1", "echo a 2>&x",
    "echo *", "echo **", "echo [", "echo []", "echo [a", "echo [!]",
    # omitted: exponential across the filesystem, dash hangs on it too

    "echo ~", "echo ~~", "echo ~/x", "echo ~nosuchuser",
    "IFS=; echo $x", "IFS=" + chr(0o41) + "; echo a",
    "x=1; x=2 x=3; echo $x",
    "echo " + "a" * 5000,
    "echo " + "$" * 200,
    "echo " + "(" * 100,
    "echo " + "{" * 100,
    "$(" * 40 + ")" * 40,
    "`" * 60,
    '"' * 60,
    "'" * 60,
    "echo " + "$((" * 30 + "1" + "))" * 30,
    "f() { f; }; f",
    # arrays
    "a=(", "a=()", "a=(1", "a=(1 2", "a=)", "a+=(", "a[]=1", "a[=1",
    "a[1]=", "a[-1]=x", "a[-99]=x", "a[abc]=1", "a[1+]=1", "a[999999999]=x",
    "echo ${a[", "echo ${a[]}", "echo ${a[@}", "echo ${a[@]", "echo ${a[-]}",
    "echo ${#a[", "echo ${!a[", "echo ${!a}", "echo ${!}", "echo ${a[@]:}",
    "echo ${a[@]::}", "echo ${a[@]:1:}", "echo ${a[@]:-1:-1}", "echo ${a:x:y}",
    "a=(1 2); echo ${a[9999999]}", "a=(1 2); unset a[99]", "unset a[",
    "unset a[]", "unset [1]", "a=(1 2); echo $((a[9999]))", "echo $((a[",
    "local a=(1 2)", "declare a=(", "a=(1 2) b=(3 4) echo hi",
    "a=(1 2); a[0]+=x; echo ${a[0]}", "a=($(echo))", "a=(*)",
    "readonly a=(1)", "export a=(1)", "a=(a b); a=(); echo ${#a[@]}",
    "while true; do break; done",
    "for i in $(echo); do echo; done",
]

ATOMS = ['echo', 'a', '$x', '${x}', '$(x)', '`x`', '$((1))', '"', "'", '\\',
         'a=(1 2)', '${a[@]}', '${a[0]}', '${#a[@]}', '${!a[@]}', 'a[0]=z',
         'a+=(x)', '${a[@]:1:1}', 'local', 'unset', '[1]',
         '|', '&&', '||', ';', ';;', '&', '>', '<', '>>', '<<', '2>&1',
         '(', ')', '{', '}', 'if', 'then', 'fi', 'while', 'do', 'done',
         'for', 'in', 'case', 'esac', '!', '[', ']', '=', '-eq', 'x=1',
         '\n', '#', '*', '?', '~', ':', '.', 'f()', 'break', 'return']

random.seed(SEED)
cases = list(HAND)
for _ in range(int(os.environ.get("FUZZ_N", 1000))):
    n = random.randint(1, 12)
    cases.append(" ".join(random.choice(ATOMS) for _ in range(n)))

env = dict(os.environ)
env["ASAN_OPTIONS"] = "detect_leaks=1"
env["UBSAN_OPTIONS"] = "print_stacktrace=1"

crashes = []
for src in cases:
    with tempfile.NamedTemporaryFile("w", suffix=".sh", delete=False) as f:
        f.write(src)
        path = f.name
    try:
        p = subprocess.run([MSH, path], capture_output=True, timeout=5,
                           text=True, errors="replace", env=env,
                           stdin=subprocess.DEVNULL, cwd="/tmp")
        rc, err = p.returncode, p.stderr
    except subprocess.TimeoutExpired:
        rc, err = -99, "<<TIMEOUT>>"
    os.unlink(path)

    trouble = (rc < 0 or rc == -99 or "Sanitizer" in err or
               "runtime error:" in err or "TIMEOUT" in err)
    if trouble:
        crashes.append((src, rc, err[:900]))

print("%d cases, %d crashed/hung/tripped a sanitizer" % (len(cases), len(crashes)))
seen = set()
for src, rc, err in crashes:
    key = err.split("\n")[0][:120]
    if key in seen:
        continue
    seen.add(key)
    print("=" * 60)
    print("INPUT %r  rc=%s" % (src[:160], rc))
    print(err)
