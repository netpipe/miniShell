# miniShell

A small POSIX-ish shell interpreter in C. One file, no dependencies.

```sh
make
./minishell script.sh
./minishell -c 'echo "hello $((6*7))"'
./minishell                 # interactive
```

## What it does

Pipelines, `&&` / `||` / `;` / `&`, `!` negation, subshells `( )` and
groups `{ }`. `if`/`elif`/`else`, `while`, `until`, `for`, `case`,
functions with positional parameters and `local`.

Redirections: `<`, `>`, `>>`, `n>`, `>&`, `<&`, `>&-`, heredocs `<<` and
`<<-` — on simple *and* compound commands, so `while ...; done < file`
works.

Expansion: `$var`, `${var}`, `${var:-word}` and the rest of the `:- - := =
:+ + :? ? # ## % %%` family, `${#var}`, `$@`, `$*`, `$#`, `$?`, `$$`,
`$!`, `$0`..`$9`, command substitution `$( )` and backticks, arithmetic
`$(( ))`, `~`, globbing `* ? [a-z] [!abc]`, quoting, and field splitting
that honours `IFS`.

Builtins: `cd`, `pwd`, `echo`, `printf`, `export`, `unset`, `test` / `[`,
`true`, `false`, `:`, `read`, `shift`, `set` (`--`, `-e`, `-x`, `-u`),
`local`, `eval`, `.` / `source`, `break`, `continue`, `return`, `wait`,
`exit`.

The interactive prompt reads until the command is complete, so multi-line
`if`, `for`, functions and heredocs work at the prompt (`PS2`, default
`> `).

## Tests

The expectations were produced by running `dash` (and `bash` for four
cases where dash's exit codes are its own), not by running miniShell and
recording what it printed — so the suite can fail, and does on the version
before the fixes.

```sh
make check      # 287 cases against tests/expected.txt
make difftest   # same cases, compared against dash/bash live
make asan       # the suite under ASan + UBSan + leak detection
make fuzz       # 1200 malformed inputs; nothing may crash, hang or leak
make sample     # run test.sh
```

`make check` needs python3; `make difftest` also needs `dash` and `bash`.

## Notes

`FIXES.md` records what was broken before, how each fault was found, and
what is deliberately not implemented (`trap`, job control, `getopts`,
arrays, `[[ ]]`).
