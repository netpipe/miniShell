/*
 * miniShell - a small POSIX-ish shell interpreter in C.
 *
 * Structure follows the original: lexer -> AST -> tree-walking executor.
 * See FIXES.md for what changed and why.
 */

#define _POSIX_C_SOURCE 200809L

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>
#include <ctype.h>
#include <signal.h>
#include <dirent.h>
#include <sys/wait.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <errno.h>

static int last_status = 0;
static int shell_exit = 0;
static int exit_requested = 0;

static int opt_errexit = 0;
static int opt_xtrace = 0;
static int opt_nounset = 0;
static int noerrexit = 0;          /* >0 while in a condition context */
static long cmdsub_count = 0;      /* command substitutions performed */
static int interactive = 0;
static pid_t last_bg_pid = 0;

enum {
    FLOW_NORMAL = 0,
    FLOW_BREAK,
    FLOW_CONTINUE,
    FLOW_RETURN
};

/*
 * A runaway recursive function used to walk off the end of the C stack.
 * On Linux that is a segfault; on a kernel with small fixed per-thread
 * stacks it is a fault with no message at all, so the depth is capped
 * here.  Each level costs roughly a kilobyte of stack - lower this if
 * the thread stacks are small.
 */
#define MAX_FUNC_DEPTH 512

static int func_depth = 0;

static int flow = FLOW_NORMAL;
static int flow_count = 1;
static int return_status = 0;
static int loop_depth = 0;

static void *xmalloc(size_t n) {
    void *p = malloc(n);
    if (!p) {
        fprintf(stderr, "out of memory\n");
        exit(1);
    }
    return p;
}

static void *xrealloc(void *p, size_t n) {
    void *r = realloc(p, n);
    if (!r) {
        fprintf(stderr, "out of memory\n");
        exit(1);
    }
    return r;
}

static char *xstrdup(const char *s) {
    if (!s) return NULL;
    size_t n = strlen(s) + 1;
    char *p = xmalloc(n);
    memcpy(p, s, n);
    return p;
}

typedef struct {
    char *s;
    size_t len;
    size_t cap;
} Str;

static void str_init(Str *st) {
    st->cap = 64;
    st->s = xmalloc(st->cap);
    st->len = 0;
    st->s[0] = '\0';
}

static void str_reserve(Str *st, size_t extra) {
    size_t need = st->len + extra + 1;
    if (need > st->cap) {
        while (st->cap < need) st->cap *= 2;
        st->s = xrealloc(st->s, st->cap);
    }
}

static void str_addch(Str *st, char c) {
    str_reserve(st, 1);
    st->s[st->len++] = c;
    st->s[st->len] = '\0';
}

static void str_addn(Str *st, const char *s, size_t n) {
    if (!s || n == 0) return;
    str_reserve(st, n);
    memcpy(st->s + st->len, s, n);
    st->len += n;
    st->s[st->len] = '\0';
}

static void str_addstr(Str *st, const char *s) {
    if (s) str_addn(st, s, strlen(s));
}

static void str_clear(Str *st) {
    st->len = 0;
    st->s[0] = '\0';
}

typedef struct {
    char **v;
    int n;
    int cap;
} Args;

static void args_init(Args *a) {
    a->cap = 8;
    a->n = 0;
    a->v = xmalloc(sizeof(char *) * a->cap);
    a->v[0] = NULL;
}

static void args_add(Args *a, char *s) {
    if (a->n + 1 >= a->cap) {
        a->cap *= 2;
        a->v = xrealloc(a->v, sizeof(char *) * a->cap);
    }
    a->v[a->n++] = s;
    a->v[a->n] = NULL;
}

static void args_add_copy(Args *a, const char *s) {
    args_add(a, xstrdup(s));
}

static void args_free(Args *a) {
    if (!a->v) return;
    for (int i = 0; i < a->n; i++) free(a->v[i]);
    free(a->v);
    a->v = NULL;
    a->n = a->cap = 0;
}

/* ------------------------------------------------------------------ */
/* Shell variables.                                                     */
/*                                                                      */
/* The original put every assignment straight into setenv(), which      */
/* exports it to every child process.  A shell variable is only in the  */
/* environment once it has been exported, so they live here and are     */
/* mirrored into the environment on export.                             */
/* ------------------------------------------------------------------ */

/*
 * A variable holds a sparse vector of elements.  items[i] is NULL when
 * that index has never been set, which is how bash arrays behave:
 *
 *   f=(1 2 3); unset f[1]; echo ${#f[@]}   ->  2
 *   ${!f[@]}                               ->  0 2
 *
 * A plain scalar is simply a variable with one element, so ${x} and
 * ${x[0]} name the same thing and nothing else has to know the
 * difference.
 */
typedef struct Var {
    char *name;
    char **items;
    int nitems;        /* one past the highest index ever set */
    int isarray;       /* assigned with ( ) or through a subscript */
    int exported;
    struct Var *next;
} Var;

static Var *variables = NULL;

static Var *var_find(const char *name) {
    for (Var *v = variables; v; v = v->next) {
        if (strcmp(v->name, name) == 0) return v;
    }
    return NULL;
}

static Var *var_make(const char *name) {
    Var *v = var_find(name);
    if (v) return v;

    v = xmalloc(sizeof(*v));
    v->name = xstrdup(name);
    v->items = NULL;
    v->nitems = 0;
    v->isarray = 0;
    /* a variable inherited from the environment stays exported */
    v->exported = getenv(name) != NULL;
    v->next = variables;
    variables = v;
    return v;
}

static void var_clear_items(Var *v) {
    for (int i = 0; i < v->nitems; i++) free(v->items[i]);
    free(v->items);
    v->items = NULL;
    v->nitems = 0;
}

/* bash does not put arrays in the environment, so neither do we */
static void var_sync_env(Var *v) {
    if (!v->exported) return;

    if (v->isarray) {
        unsetenv(v->name);
        return;
    }

    setenv(v->name, (v->nitems > 0 && v->items[0]) ? v->items[0] : "", 1);
}

/*
 * Elements are stored in a dense vector, so a very large index would try
 * to allocate a very large array: a[999999999]=x froze the shell.  bash
 * stores arrays as a list and has no practical limit; this caps the index
 * instead, which is the trade for the simpler storage.
 */
#define MAX_ARRAY_INDEX 65535

static void var_put(Var *v, int idx, const char *value) {
    if (idx < 0 || idx > MAX_ARRAY_INDEX) return;

    if (idx >= v->nitems) {
        v->items = xrealloc(v->items, sizeof(char *) * (idx + 1));
        for (int i = v->nitems; i <= idx; i++) v->items[i] = NULL;
        v->nitems = idx + 1;
    }

    free(v->items[idx]);
    v->items[idx] = value ? xstrdup(value) : NULL;
}

static const char *var_get(const char *name) {
    Var *v = var_find(name);
    if (v) return (v->nitems > 0 && v->items[0]) ? v->items[0] : NULL;
    return getenv(name);
}

/* element 0 only, leaving any other elements alone - this is what bash
   does for  a=(x y); a=z  which gives  z y  */
static void var_set(const char *name, const char *value) {
    Var *v = var_make(name);
    var_put(v, 0, value ? value : "");
    var_sync_env(v);
}

static void var_set_index(const char *name, int idx, const char *value) {
    Var *v = var_make(name);
    if (idx > 0) v->isarray = 1;
    var_put(v, idx, value ? value : "");
    var_sync_env(v);
}

static void var_set_array(const char *name, char **vals, int n) {
    Var *v = var_make(name);
    var_clear_items(v);
    v->isarray = 1;
    for (int i = 0; i < n; i++) var_put(v, i, vals[i]);
    var_sync_env(v);
}

static void var_append_array(const char *name, char **vals, int n) {
    Var *v = var_make(name);
    v->isarray = 1;
    int base = v->nitems;
    for (int i = 0; i < n; i++) var_put(v, base + i, vals[i]);
    var_sync_env(v);
}

static void var_append(const char *name, const char *value) {
    Var *v = var_make(name);

    const char *old = (v->nitems > 0 && v->items[0]) ? v->items[0] : "";
    size_t n = strlen(old) + strlen(value ? value : "") + 1;

    char *joined = xmalloc(n);
    strcpy(joined, old);
    strcat(joined, value ? value : "");

    var_put(v, 0, joined);
    free(joined);
    var_sync_env(v);
}

static const char *var_elem(const char *name, int idx) {
    Var *v = var_find(name);

    if (!v) {
        if (idx == 0) return getenv(name);
        return NULL;
    }

    if (idx < 0 || idx >= v->nitems) return NULL;
    return v->items[idx];
}

/* highest index that is actually set, or -1 */
static int var_top_index(const char *name) {
    Var *v = var_find(name);
    if (!v) return getenv(name) ? 0 : -1;
    for (int i = v->nitems - 1; i >= 0; i--) if (v->items[i]) return i;
    return -1;
}

static void var_unset_index(const char *name, int idx) {
    Var *v = var_find(name);
    if (!v || idx < 0 || idx >= v->nitems) return;

    free(v->items[idx]);
    v->items[idx] = NULL;
    var_sync_env(v);
}

static void var_export(const char *name) {
    Var *v = var_find(name);

    if (!v) {
        const char *e = getenv(name);
        v = var_make(name);
        if (v->nitems == 0) var_put(v, 0, e ? e : "");
    }

    v->exported = 1;
    var_sync_env(v);
}

static void var_unset(const char *name) {
    Var *prev = NULL;

    for (Var *v = variables; v; prev = v, v = v->next) {
        if (strcmp(v->name, name) == 0) {
            if (prev) prev->next = v->next;
            else variables = v->next;

            var_clear_items(v);
            free(v->name);
            free(v);
            break;
        }
    }

    unsetenv(name);
}

static void vars_free_all(void) {
    Var *v = variables;
    while (v) {
        Var *nx = v->next;
        var_clear_items(v);
        free(v->name);
        free(v);
        v = nx;
    }
    variables = NULL;
}

/*
 * Recognise an assignment word: NAME=, NAME+=, NAME[sub]= or NAME[sub]+=.
 * Returns 0 when the word is not an assignment.  Any output pointer may
 * be NULL if the caller only wants to know.  *sub and *name are owned by
 * the caller; *value points into the word.
 */
static int split_assign(const char *w, char **name, char **sub, int *append,
                        const char **value) {
    if (!w) return 0;
    if (!(isalpha((unsigned char)w[0]) || w[0] == '_')) return 0;

    int i = 1;
    while (w[i] && (isalnum((unsigned char)w[i]) || w[i] == '_')) i++;

    int nlen = i;
    char *sb = NULL;

    if (w[i] == '[') {
        int depth = 0;
        int start = i + 1;
        int j = i;

        while (w[j]) {
            if (w[j] == '[') depth++;
            else if (w[j] == ']') { depth--; if (depth == 0) break; }
            j++;
        }

        if (w[j] != ']') return 0;

        sb = xmalloc(j - start + 1);
        memcpy(sb, w + start, j - start);
        sb[j - start] = '\0';
        i = j + 1;
    }

    int ap = 0;
    if (w[i] == '+' && w[i + 1] == '=') { ap = 1; i += 2; }
    else if (w[i] == '=') i += 1;
    else { free(sb); return 0; }

    if (name) {
        char *nm = xmalloc(nlen + 1);
        memcpy(nm, w, nlen);
        nm[nlen] = '\0';
        *name = nm;
    }

    if (sub) *sub = sb;
    else free(sb);

    if (append) *append = ap;
    if (value) *value = w + i;
    return 1;
}

static int is_assign_word(const char *w) {
    return split_assign(w, NULL, NULL, NULL, NULL);
}

/* a full copy of a variable, so prefix assignments and `local` can put
   an array back exactly as it was */
typedef struct {
    char *name;
    char **items;
    int nitems;
    int isarray;
    int existed;
    int exported;
} VarSnap;

static void var_snapshot(const char *name, VarSnap *sn) {
    Var *v = var_find(name);
    const char *env = v ? NULL : getenv(name);

    sn->name = xstrdup(name);
    sn->items = NULL;
    sn->nitems = 0;
    sn->isarray = 0;
    sn->existed = 0;
    sn->exported = 0;

    if (v) {
        sn->existed = 1;
        sn->exported = v->exported;
        sn->isarray = v->isarray;
        sn->nitems = v->nitems;
        sn->items = xmalloc(sizeof(char *) * (v->nitems ? v->nitems : 1));
        for (int i = 0; i < v->nitems; i++) {
            sn->items[i] = v->items[i] ? xstrdup(v->items[i]) : NULL;
        }
    } else if (env) {
        sn->existed = 1;
        sn->exported = 1;
        sn->nitems = 1;
        sn->items = xmalloc(sizeof(char *));
        sn->items[0] = xstrdup(env);
    }
}

static void var_restore(VarSnap *sn) {
    var_unset(sn->name);

    if (!sn->existed) return;

    Var *v = var_make(sn->name);
    v->isarray = sn->isarray;
    for (int i = 0; i < sn->nitems; i++) var_put(v, i, sn->items[i]);

    if (sn->exported) { v->exported = 1; var_sync_env(v); }
}

static void var_snap_free(VarSnap *sn) {
    for (int i = 0; i < sn->nitems; i++) free(sn->items[i]);
    free(sn->items);
    free(sn->name);
    sn->items = NULL;
    sn->nitems = 0;
}

/* ------------------------------------------------------------------ */
/* Positional parameters and function frames.                           */
/* ------------------------------------------------------------------ */

typedef struct SavedVar {
    VarSnap snap;
    struct SavedVar *next;
} SavedVar;

typedef struct ArgsFrame {
    char **argv;      /* argv[0] is $0 / the function name; owned */
    int argc;
    SavedVar *locals;
    struct ArgsFrame *next;
} ArgsFrame;

static ArgsFrame *frames = NULL;

static void push_frame(char **argv, int argc) {
    ArgsFrame *f = xmalloc(sizeof(*f));

    f->argv = xmalloc(sizeof(char *) * (argc + 1));
    for (int i = 0; i < argc; i++) f->argv[i] = xstrdup(argv[i]);
    f->argv[argc] = NULL;

    f->argc = argc;
    f->locals = NULL;
    f->next = frames;
    frames = f;
}

static void pop_frame(void) {
    if (!frames) return;

    ArgsFrame *f = frames;
    frames = frames->next;

    SavedVar *s = f->locals;
    while (s) {
        SavedVar *nx = s->next;

        var_restore(&s->snap);
        var_snap_free(&s->snap);
        free(s);
        s = nx;
    }

    for (int i = 0; i < f->argc; i++) free(f->argv[i]);
    free(f->argv);
    free(f);
}

static char **cur_argv(void) {
    return frames->argv;
}

static int cur_argc(void) {
    return frames->argc;
}

static void frame_make_local(const char *name) {
    if (!frames || !frames->next) return;   /* not inside a function */

    for (SavedVar *s = frames->locals; s; s = s->next) {
        if (strcmp(s->snap.name, name) == 0) return;
    }

    SavedVar *s = xmalloc(sizeof(*s));
    var_snapshot(name, &s->snap);

    s->next = frames->locals;
    frames->locals = s;
}

/* ------------------------------------------------------------------ */
/* Pattern matching: used for globbing, case, and ${x#pat}.             */
/* A backslash in the pattern quotes the next character.                */
/* ------------------------------------------------------------------ */

static int glob_class(const char **pp, char c, int *ok) {
    const char *p = *pp;          /* just past '[' */
    int neg = 0;
    int match = 0;

    if (*p == '!' || *p == '^') { neg = 1; p++; }
    if (*p == ']') { if (c == ']') match = 1; p++; }

    while (*p && *p != ']') {
        if (p[0] == '\\' && p[1]) {
            if (c == p[1]) match = 1;
            p += 2;
            continue;
        }

        if (p[1] == '-' && p[2] && p[2] != ']') {
            unsigned char lo = (unsigned char)p[0];
            unsigned char hi = (unsigned char)p[2];
            if ((unsigned char)c >= lo && (unsigned char)c <= hi) match = 1;
            p += 3;
            continue;
        }

        if (*p == c) match = 1;
        p++;
    }

    if (*p != ']') { *ok = 0; return 0; }   /* unterminated: '[' is literal */

    *ok = 1;
    *pp = p + 1;
    return neg ? !match : match;
}

static int glob_match(const char *p, const char *s) {
    while (*p) {
        if (*p == '*') {
            while (*p == '*') p++;
            if (!*p) return 1;

            for (const char *t = s;; t++) {
                if (glob_match(p, t)) return 1;
                if (!*t) return 0;
            }
        }

        if (*p == '?') {
            if (!*s) return 0;
            p++; s++;
            continue;
        }

        if (*p == '[') {
            const char *q = p + 1;
            int ok = 0;
            int r = glob_class(&q, *s, &ok);

            if (!ok) {                      /* literal '[' */
                if (*s != '[') return 0;
                p++; s++;
                continue;
            }

            if (!*s || !r) return 0;
            p = q; s++;
            continue;
        }

        if (*p == '\\' && p[1]) p++;

        if (*p != *s) return 0;
        p++; s++;
    }

    return *s == '\0';
}

static int pattern_has_magic(const char *p) {
    for (int i = 0; p[i]; i++) {
        if (p[i] == '\\' && p[i + 1]) { i++; continue; }
        if (p[i] == '*' || p[i] == '?' || p[i] == '[') return 1;
    }
    return 0;
}

static char *pattern_unescape(const char *p) {
    Str out;
    str_init(&out);

    for (int i = 0; p[i]; i++) {
        if (p[i] == '\\' && p[i + 1]) {
            str_addch(&out, p[i + 1]);
            i++;
            continue;
        }
        str_addch(&out, p[i]);
    }

    return out.s;
}

static int str_cmp_qsort(const void *a, const void *b) {
    return strcmp(*(char * const *)a, *(char * const *)b);
}

/*
 * Expand one pathname pattern.  Returns the number of matches appended;
 * 0 means the caller should use the literal (unescaped) pattern, which is
 * what POSIX requires when nothing matches.
 */
static void glob_walk(const char *prefix, char **segs, int nseg, int idx,
                      Args *out) {
    if (idx >= nseg) return;

    char *seg = segs[idx];
    int last = (idx == nseg - 1);

    if (!pattern_has_magic(seg)) {
        char *lit = pattern_unescape(seg);

        Str path;
        str_init(&path);
        str_addstr(&path, prefix);
        str_addstr(&path, lit);

        if (last) {
            struct stat st;
            if (lstat(path.s, &st) == 0) args_add_copy(out, path.s);
        } else {
            str_addch(&path, '/');
            glob_walk(path.s, segs, nseg, idx + 1, out);
        }

        free(lit);
        free(path.s);
        return;
    }

    const char *dirname = prefix[0] ? prefix : "./";
    DIR *d = opendir(dirname);
    if (!d) return;

    Args names;
    args_init(&names);

    struct dirent *de;
    while ((de = readdir(d)) != NULL) {
        /* a leading dot must be matched explicitly */
        if (de->d_name[0] == '.' && seg[0] != '.') continue;
        if (strcmp(de->d_name, ".") == 0 || strcmp(de->d_name, "..") == 0) {
            if (seg[0] != '.') continue;
        }

        if (glob_match(seg, de->d_name)) args_add_copy(&names, de->d_name);
    }

    closedir(d);

    if (names.n > 1) qsort(names.v, names.n, sizeof(char *), str_cmp_qsort);

    for (int i = 0; i < names.n; i++) {
        Str path;
        str_init(&path);
        str_addstr(&path, prefix);
        str_addstr(&path, names.v[i]);

        if (last) {
            args_add_copy(out, path.s);
        } else {
            struct stat st;
            if (stat(path.s, &st) == 0 && S_ISDIR(st.st_mode)) {
                str_addch(&path, '/');
                glob_walk(path.s, segs, nseg, idx + 1, out);
            }
        }

        free(path.s);
    }

    args_free(&names);
}

static int glob_expand(const char *pattern, Args *out) {
    Args segs;
    args_init(&segs);

    const char *p = pattern;
    Str root;
    str_init(&root);

    while (*p == '/') { str_addch(&root, '/'); p++; }

    Str seg;
    str_init(&seg);

    for (;;) {
        if (*p == '\0' || *p == '/') {
            if (seg.len > 0) args_add_copy(&segs, seg.s);
            str_clear(&seg);

            if (*p == '\0') break;
            while (*p == '/') p++;
            continue;
        }

        if (*p == '\\' && p[1]) {
            str_addch(&seg, *p++);
            str_addch(&seg, *p++);
            continue;
        }

        str_addch(&seg, *p++);
    }

    int before = out->n;
    if (segs.n > 0) glob_walk(root.s, segs.v, segs.n, 0, out);
    int added = out->n - before;

    /* POSIX sorts the whole expansion of one word */
    if (added > 1) qsort(out->v + before, added, sizeof(char *), str_cmp_qsort);

    free(seg.s);
    free(root.s);
    args_free(&segs);
    return added;
}

/* ------------------------------------------------------------------ */
/* Lexer                                                                */
/* ------------------------------------------------------------------ */

typedef enum {
    T_WORD,
    T_IO_NUMBER,
    T_PIPE,
    T_AND,
    T_OR,
    T_SEMI,
    T_DSEMI,
    T_AMP,
    T_LESS,
    T_GREAT,
    T_DGREAT,
    T_GREATAND,
    T_LESSAND,
    T_DLESS,
    T_NEWLINE,
    T_LBRACE,
    T_RBRACE,
    T_LPAREN,
    T_RPAREN,
    T_END
} TType;

typedef struct {
    TType type;
    char *text;
    int fd;
    int quoted;
} Token;

typedef struct {
    Token *v;
    int n;
    int cap;
} TokVec;

static void tv_add(TokVec *tv, TType type, const char *text, int fd, int quoted) {
    if (tv->n == tv->cap) {
        tv->cap = tv->cap ? tv->cap * 2 : 32;
        tv->v = xrealloc(tv->v, tv->cap * sizeof(Token));
    }

    tv->v[tv->n].type = type;
    tv->v[tv->n].text = xstrdup(text);
    tv->v[tv->n].fd = fd;
    tv->v[tv->n].quoted = quoted;
    tv->n++;
}

/*
 * Copy a $(...), $((...)), ${...} or `...` construct into the word
 * verbatim, respecting nesting and quoting inside it, so that
 *   echo $(echo "a)b")
 * lexes as a single word.  Returns the index just past the construct.
 * Sets *incomplete if the input ends inside it.
 */
static int lex_copy_expansion(Str *raw, const char *s, int i, int *incomplete) {
    if (s[i] == '`') {
        str_addch(raw, s[i++]);

        while (s[i] && s[i] != '`') {
            if (s[i] == '\\' && s[i + 1]) {
                str_addch(raw, s[i]);
                str_addch(raw, s[i + 1]);
                i += 2;
                continue;
            }
            str_addch(raw, s[i++]);
        }

        if (s[i] == '`') str_addch(raw, s[i++]);
        else if (incomplete) *incomplete = 1;

        return i;
    }

    /* s[i] == '$' */
    str_addch(raw, s[i++]);

    if (s[i] == '{') {
        int depth = 0;

        do {
            if (s[i] == '{') depth++;
            else if (s[i] == '}') depth--;
            str_addch(raw, s[i++]);
        } while (s[i] && depth > 0);

        if (depth > 0 && incomplete) *incomplete = 1;
        return i;
    }

    if (s[i] == '(') {
        int depth = 0;
        int q = 0;                  /* 0 none, 1 single, 2 double */

        while (s[i]) {
            char c = s[i];

            if (q == 1) {
                str_addch(raw, c);
                i++;
                if (c == '\'') q = 0;
                continue;
            }

            if (c == '\\' && s[i + 1] && q != 1) {
                str_addch(raw, s[i]);
                str_addch(raw, s[i + 1]);
                i += 2;
                continue;
            }

            if (q == 2) {
                str_addch(raw, c);
                i++;
                if (c == '"') q = 0;
                continue;
            }

            if (c == '\'') { q = 1; str_addch(raw, c); i++; continue; }
            if (c == '"') { q = 2; str_addch(raw, c); i++; continue; }

            if (c == '(') depth++;
            else if (c == ')') depth--;

            str_addch(raw, c);
            i++;

            if (depth == 0) return i;
        }

        if (incomplete) *incomplete = 1;
        return i;
    }

    return i;
}

static int is_word_break(char c) {
    return c == '\0' || c == ' ' || c == '\t' || c == '\n' ||
           c == '|' || c == '&' || c == ';' ||
           c == '<' || c == '>' ||
           c == '(' || c == ')';
}

static void lex_word(TokVec *tv, const char *s, int *ip, int *incomplete) {
    int i = *ip;
    Str raw;
    str_init(&raw);
    int quoted = 0;

    while (s[i]) {
        if (s[i] == '\\') {
            if (s[i + 1] == '\n') {          /* line continuation */
                i += 2;
                continue;
            }

            quoted = 1;
            str_addch(&raw, s[i]);

            if (s[i + 1]) {
                str_addch(&raw, s[i + 1]);
                i += 2;
            } else {
                if (incomplete) *incomplete = 1;
                i++;
                break;
            }
            continue;
        }

        if (s[i] == '\'') {
            quoted = 1;
            str_addch(&raw, s[i++]);
            while (s[i] && s[i] != '\'') str_addch(&raw, s[i++]);

            if (s[i] == '\'') str_addch(&raw, s[i++]);
            else if (incomplete) *incomplete = 1;

            continue;
        }

        if (s[i] == '"') {
            quoted = 1;
            str_addch(&raw, s[i++]);

            while (s[i] && s[i] != '"') {
                if (s[i] == '\\' && s[i + 1]) {
                    if (s[i + 1] == '\n') { i += 2; continue; }
                    str_addch(&raw, s[i]);
                    str_addch(&raw, s[i + 1]);
                    i += 2;
                    continue;
                }

                if (s[i] == '$' || s[i] == '`') {
                    i = lex_copy_expansion(&raw, s, i, incomplete);
                    continue;
                }

                str_addch(&raw, s[i++]);
            }

            if (s[i] == '"') str_addch(&raw, s[i++]);
            else if (incomplete) *incomplete = 1;

            continue;
        }

        if (s[i] == '$' || s[i] == '`') {
            int before = i;
            i = lex_copy_expansion(&raw, s, i, incomplete);
            if (i == before) str_addch(&raw, s[i++]);
            continue;
        }

        if (is_word_break(s[i])) break;

        str_addch(&raw, s[i++]);
    }

    *ip = i;
    if (raw.len > 0) tv_add(tv, T_WORD, raw.s, 0, quoted);
    free(raw.s);
}

typedef struct {
    int tok;          /* index of the T_DLESS token to fill in */
    char *delim;
    int strip;        /* <<- : strip leading tabs */
    int quoted;       /* delimiter was quoted: no expansion in the body */
} PendingHD;

static Token *lex_program(const char *s, int *count, int *incomplete) {
    TokVec tv = {0};
    int i = 0;

    PendingHD pend[16];
    int npend = 0;

    if (incomplete) *incomplete = 0;

    while (s[i]) {
        while (s[i] == ' ' || s[i] == '\t') i++;

        if (s[i] == '\\' && s[i + 1] == '\n') { i += 2; continue; }
        if (!s[i]) break;

        if (s[i] == '\n') {
            tv_add(&tv, T_NEWLINE, "\n", 0, 0);
            i++;

            /* the bodies of any heredocs on the finished line start here */
            for (int k = 0; k < npend; k++) {
                Str body;
                str_init(&body);
                int found = 0;

                while (s[i]) {
                    int ls = i;
                    while (s[i] && s[i] != '\n') i++;

                    int le = i;
                    if (s[i] == '\n') i++;

                    int cs = ls;
                    if (pend[k].strip) while (cs < le && s[cs] == '\t') cs++;

                    int len = le - cs;
                    if ((int)strlen(pend[k].delim) == len &&
                        strncmp(s + cs, pend[k].delim, len) == 0) {
                        found = 1;
                        break;
                    }

                    str_addn(&body, s + cs, len);
                    str_addch(&body, '\n');
                }

                if (!found && incomplete) *incomplete = 1;

                free(tv.v[pend[k].tok].text);
                tv.v[pend[k].tok].text = xstrdup(body.s);
                tv.v[pend[k].tok].quoted = pend[k].quoted;

                free(body.s);
                free(pend[k].delim);
            }

            npend = 0;
            continue;
        }

        if (s[i] == '#') {
            while (s[i] && s[i] != '\n') i++;
            continue;
        }

        if (s[i] == '|') {
            if (s[i + 1] == '|') { tv_add(&tv, T_OR, "||", 0, 0); i += 2; }
            else { tv_add(&tv, T_PIPE, "|", 0, 0); i++; }
            continue;
        }

        if (s[i] == '&') {
            if (s[i + 1] == '&') { tv_add(&tv, T_AND, "&&", 0, 0); i += 2; }
            else { tv_add(&tv, T_AMP, "&", 0, 0); i++; }
            continue;
        }

        if (s[i] == ';') {
            if (s[i + 1] == ';') { tv_add(&tv, T_DSEMI, ";;", 0, 0); i += 2; }
            else { tv_add(&tv, T_SEMI, ";", 0, 0); i++; }
            continue;
        }

        if (s[i] == '<') {
            if (s[i + 1] == '<') {
                int strip = 0;
                i += 2;
                if (s[i] == '-') { strip = 1; i++; }

                while (s[i] == ' ' || s[i] == '\t') i++;

                /* read the delimiter word and note whether it was quoted */
                Str d;
                str_init(&d);
                int dq = 0;

                while (s[i] && !is_word_break(s[i])) {
                    if (s[i] == '\'' ) {
                        dq = 1; i++;
                        while (s[i] && s[i] != '\'') str_addch(&d, s[i++]);
                        if (s[i]) i++;
                        continue;
                    }
                    if (s[i] == '"') {
                        dq = 1; i++;
                        while (s[i] && s[i] != '"') str_addch(&d, s[i++]);
                        if (s[i]) i++;
                        continue;
                    }
                    if (s[i] == '\\' && s[i + 1]) {
                        dq = 1;
                        str_addch(&d, s[i + 1]);
                        i += 2;
                        continue;
                    }
                    str_addch(&d, s[i++]);
                }

                tv_add(&tv, T_DLESS, "", 0, 0);

                if (npend < 16) {
                    pend[npend].tok = tv.n - 1;
                    pend[npend].delim = xstrdup(d.s);
                    pend[npend].strip = strip;
                    pend[npend].quoted = dq;
                    npend++;
                }

                free(d.s);
                continue;
            }

            if (s[i + 1] == '&') { tv_add(&tv, T_LESSAND, "<&", 0, 0); i += 2; }
            else { tv_add(&tv, T_LESS, "<", 0, 0); i++; }
            continue;
        }

        if (s[i] == '>') {
            if (s[i + 1] == '>') { tv_add(&tv, T_DGREAT, ">>", 0, 0); i += 2; }
            else if (s[i + 1] == '&') { tv_add(&tv, T_GREATAND, ">&", 0, 0); i += 2; }
            else { tv_add(&tv, T_GREAT, ">", 0, 0); i++; }
            continue;
        }

        if (s[i] == '{') { tv_add(&tv, T_LBRACE, "{", 0, 0); i++; continue; }
        if (s[i] == '}') { tv_add(&tv, T_RBRACE, "}", 0, 0); i++; continue; }
        if (s[i] == '(') { tv_add(&tv, T_LPAREN, "(", 0, 0); i++; continue; }
        if (s[i] == ')') { tv_add(&tv, T_RPAREN, ")", 0, 0); i++; continue; }

        if (isdigit((unsigned char)s[i])) {
            int j = i;
            while (isdigit((unsigned char)s[j])) j++;

            if (s[j] == '<' || s[j] == '>') {
                char buf[32];
                int len = j - i;
                if (len > 31) len = 31;
                memcpy(buf, s + i, len);
                buf[len] = '\0';

                tv_add(&tv, T_IO_NUMBER, buf, atoi(buf), 0);
                i = j;
                continue;
            }
        }

        lex_word(&tv, s, &i, incomplete);
    }

    /* heredocs opened on the last line, with no trailing newline */
    for (int k = 0; k < npend; k++) {
        if (incomplete) *incomplete = 1;
        free(pend[k].delim);
    }

    tv_add(&tv, T_END, "", 0, 0);
    *count = tv.n;
    return tv.v;
}

/* ------------------------------------------------------------------ */
/* AST                                                                  */
/* ------------------------------------------------------------------ */

typedef struct Node Node;

typedef enum {
    N_LIST,
    N_SUBSHELL,
    N_SIMPLE,
    N_IF,
    N_WHILE,
    N_FOR,
    N_CASE,
    N_REDIR,
    N_FUNC
} NodeType;

struct Node {
    NodeType type;
    void *data;
};

typedef struct {
    int type;
    int fd;
    char *file;      /* filename, target fd, or heredoc body */
    int flags;       /* heredoc: 1 = delimiter was quoted */
} Redir;

/* NAME=(a b c) or NAME+=(a b c) sitting in the assignment prefix.
   `order` is how many prefix words came first, so the assignments are
   applied left to right the way they were written. */
typedef struct {
    char *name;
    int append;
    char **words;
    int nwords;
    int order;
} ArrAssign;

typedef struct {
    char **words;
    int nwords;
    Redir *redirs;
    int nredir;
    ArrAssign *arrs;
    int narr;
} Simple;

typedef struct {
    Node **cmds;
    int n;
    int bang;        /* leading '!' */
} Pipeline;

typedef struct {
    Pipeline **pipes;
    int n;
    int *ops;
} Andor;

typedef struct {
    Andor *andor;
    int bg;
} ListItem;

typedef struct {
    ListItem *items;
    int n;
} List;

typedef struct {
    List *cond;
    List *then;
    Node *else_node;
} If;

typedef struct {
    List *cond;
    List *body;
    int until;
} While;

typedef struct {
    char *var;
    char **words;
    int nwords;
    int use_args;
    List *body;
} For;

/* a compound command with redirections attached: while ... done > file */
typedef struct {
    Node *body;
    Redir *redirs;
    int nredir;
} RedirNode;

typedef struct {
    char **pats;
    int npat;
    List *body;
} CaseItem;

typedef struct {
    char *word;
    CaseItem *items;
    int n;
} Case;

typedef struct FuncDef {
    char *name;
    Node *body;
    struct FuncDef *next;
} FuncDef;

static FuncDef *functions = NULL;
static int func_installs = 0;

static FuncDef *find_function(const char *name) {
    for (FuncDef *f = functions; f; f = f->next) {
        if (strcmp(f->name, name) == 0) return f;
    }
    return NULL;
}

/*
 * The global table borrows the body from the AST that defined it, so any
 * program text that installs a function has its AST retained until exit
 * (see run_program_string).  The table owns only its own name and node.
 */
static void add_function(const char *name, Node *body) {
    FuncDef *f = find_function(name);

    if (f) {
        f->body = body;
    } else {
        f = xmalloc(sizeof(*f));
        f->name = xstrdup(name);
        f->body = body;
        f->next = functions;
        functions = f;
    }

    func_installs++;
}

static void functions_free_all(void) {
    FuncDef *f = functions;
    while (f) {
        FuncDef *nx = f->next;
        free(f->name);
        free(f);
        f = nx;
    }
    functions = NULL;
}

static Simple *new_simple(void) {
    Simple *s = xmalloc(sizeof(*s));
    /*
     * words is always a valid NULL-terminated vector.  It used to start
     * as NULL, so a command that is only a redirection ("> file", which
     * is how you truncate one) dereferenced a null pointer in
     * execute_simple before it ever looked at nwords.
     */
    s->words = xmalloc(sizeof(char *));
    s->words[0] = NULL;
    s->nwords = 0;
    s->arrs = NULL;
    s->narr = 0;
    s->redirs = NULL;
    s->nredir = 0;
    return s;
}

static void simple_add_word(Simple *s, const char *w) {
    s->words = xrealloc(s->words, sizeof(char *) * (s->nwords + 2));
    s->words[s->nwords++] = xstrdup(w);
    s->words[s->nwords] = NULL;
}

static void redir_add(Redir **rs, int *n, int type, int fd, const char *file,
                      int flags) {
    *rs = xrealloc(*rs, sizeof(Redir) * (*n + 1));
    (*rs)[*n].type = type;
    (*rs)[*n].fd = fd;
    (*rs)[*n].file = xstrdup(file);
    (*rs)[*n].flags = flags;
    (*n)++;
}

static void redirs_free(Redir *rs, int n) {
    for (int i = 0; i < n; i++) free(rs[i].file);
    free(rs);
}

static List *new_list(void) {
    List *l = xmalloc(sizeof(*l));
    l->items = NULL;
    l->n = 0;
    return l;
}

static void list_add(List *l, Andor *a, int bg) {
    l->items = xrealloc(l->items, sizeof(ListItem) * (l->n + 1));
    l->items[l->n].andor = a;
    l->items[l->n].bg = bg;
    l->n++;
}

static Pipeline *new_pipeline(void) {
    Pipeline *p = xmalloc(sizeof(*p));
    p->cmds = NULL;
    p->n = 0;
    p->bang = 0;
    return p;
}

static void pipeline_add(Pipeline *p, Node *c) {
    p->cmds = xrealloc(p->cmds, sizeof(Node *) * (p->n + 1));
    p->cmds[p->n++] = c;
}

static Andor *new_andor(void) {
    Andor *a = xmalloc(sizeof(*a));
    a->pipes = NULL;
    a->ops = NULL;
    a->n = 0;
    return a;
}

static void andor_add(Andor *a, Pipeline *p, int op) {
    a->pipes = xrealloc(a->pipes, sizeof(Pipeline *) * (a->n + 1));
    a->ops = xrealloc(a->ops, sizeof(int) * (a->n + 1));
    a->pipes[a->n] = p;
    a->ops[a->n] = op;
    a->n++;
}

static Node *new_node(NodeType type, void *data) {
    Node *n = xmalloc(sizeof(*n));
    n->type = type;
    n->data = data;
    return n;
}

static Node *new_simple_node(Simple *s) { return new_node(N_SIMPLE, s); }
static Node *new_list_node(List *l) { return new_node(N_LIST, l); }
static Node *new_subshell_node(List *l) { return new_node(N_SUBSHELL, l); }

static Node *new_if_node(List *cond, List *then, Node *else_node) {
    If *i = xmalloc(sizeof(*i));
    i->cond = cond;
    i->then = then;
    i->else_node = else_node;
    return new_node(N_IF, i);
}

static Node *new_while_node(List *cond, List *body, int until) {
    While *w = xmalloc(sizeof(*w));
    w->cond = cond;
    w->body = body;
    w->until = until;
    return new_node(N_WHILE, w);
}

static Node *new_func_node(char *name, Node *body) {
    FuncDef *f = xmalloc(sizeof(*f));
    f->name = name;
    f->body = body;
    f->next = NULL;
    return new_node(N_FUNC, f);
}

/* ---- freeing the tree ---- */

static void free_node(Node *n);

static void free_list_tree(List *l) {
    if (!l) return;

    for (int i = 0; i < l->n; i++) {
        Andor *a = l->items[i].andor;
        if (!a) continue;

        for (int j = 0; j < a->n; j++) {
            Pipeline *p = a->pipes[j];
            if (!p) continue;

            for (int k = 0; k < p->n; k++) free_node(p->cmds[k]);
            free(p->cmds);
            free(p);
        }

        free(a->pipes);
        free(a->ops);
        free(a);
    }

    free(l->items);
    free(l);
}

static void free_node(Node *n) {
    if (!n) return;

    switch (n->type) {
        case N_SIMPLE: {
            Simple *s = n->data;
            for (int i = 0; i < s->nwords; i++) free(s->words[i]);
            free(s->words);
            for (int i = 0; i < s->narr; i++) {
                free(s->arrs[i].name);
                for (int j = 0; j < s->arrs[i].nwords; j++) free(s->arrs[i].words[j]);
                free(s->arrs[i].words);
            }
            free(s->arrs);
            for (int i = 0; i < s->nredir; i++) free(s->redirs[i].file);
            free(s->redirs);
            free(s);
            break;
        }

        case N_LIST:
        case N_SUBSHELL:
            free_list_tree((List *)n->data);
            break;

        case N_IF: {
            If *i = n->data;
            free_list_tree(i->cond);
            free_list_tree(i->then);
            free_node(i->else_node);
            free(i);
            break;
        }

        case N_WHILE: {
            While *w = n->data;
            free_list_tree(w->cond);
            free_list_tree(w->body);
            free(w);
            break;
        }

        case N_FOR: {
            For *f = n->data;
            free(f->var);
            for (int i = 0; i < f->nwords; i++) free(f->words[i]);
            free(f->words);
            free_list_tree(f->body);
            free(f);
            break;
        }

        case N_CASE: {
            Case *c = n->data;
            free(c->word);
            for (int i = 0; i < c->n; i++) {
                for (int j = 0; j < c->items[i].npat; j++) {
                    free(c->items[i].pats[j]);
                }
                free(c->items[i].pats);
                free_list_tree(c->items[i].body);
            }
            free(c->items);
            free(c);
            break;
        }

        case N_REDIR: {
            RedirNode *r = n->data;
            free_node(r->body);
            redirs_free(r->redirs, r->nredir);
            free(r);
            break;
        }

        case N_FUNC: {
            FuncDef *f = n->data;
            free(f->name);
            free_node(f->body);
            free(f);
            break;
        }
    }

    free(n);
}

/* ------------------------------------------------------------------ */
/* Parser                                                               */
/* ------------------------------------------------------------------ */

typedef struct {
    Token *t;
    int n;
    int pos;
    int failed;
    int at_end;      /* the failure was "ran out of input" */
    int quiet;
} Parser;

static Token *peek(Parser *p) { return &p->t[p->pos]; }

static Token *peek_at(Parser *p, int off) {
    int idx = p->pos + off;
    if (idx >= p->n) idx = p->n - 1;
    return &p->t[idx];
}

static int peek_type(Parser *p) { return peek(p)->type; }

static void advance(Parser *p) {
    if (p->pos < p->n - 1) p->pos++;
}

static int is_word(Token *t, const char *s) {
    return t->type == T_WORD && !t->quoted && t->text && strcmp(t->text, s) == 0;
}

static void parse_error(Parser *p, const char *msg) {
    Token *t = peek(p);

    p->failed = 1;
    if (t->type == T_END) p->at_end = 1;

    if (!p->quiet) {
        fprintf(stderr, "minishell: syntax error: %s near '%s'\n",
                msg, t->text && t->text[0] ? t->text : "end of input");
    }
}

static void free_tokens(Token *t, int n) {
    for (int i = 0; i < n; i++) free(t[i].text);
    free(t);
}

static List *parse_list(Parser *p,
                        const char **stop_words, int nstop_words,
                        const TType *stop_types, int nstop_types);
static Node *parse_command(Parser *p);
static Andor *parse_andor(Parser *p);
static Pipeline *parse_pipeline(Parser *p);
static Node *parse_simple_command(Parser *p);

static int is_stop(Parser *p,
                   const char **words, int nwords,
                   const TType *types, int ntypes) {
    Token *t = peek(p);

    for (int i = 0; i < ntypes; i++) {
        if (t->type == types[i]) return 1;
    }

    if (t->type == T_WORD && !t->quoted && t->text) {
        for (int i = 0; i < nwords; i++) {
            if (strcmp(t->text, words[i]) == 0) return 1;
        }
    }

    return 0;
}

static void skip_separators(Parser *p) {
    while (peek_type(p) == T_SEMI || peek_type(p) == T_NEWLINE) advance(p);
}

static void skip_newlines(Parser *p) {
    while (peek_type(p) == T_NEWLINE) advance(p);
}

/*
 * Parse one redirection if the parser is sitting on one.
 * Returns 1 when a redirection was consumed, 0 when there was none,
 * and -1 on a syntax error.
 */
static int parse_redir(Parser *p, Redir **rs, int *n) {
    Token *t = peek(p);
    int pending_fd = -1;

    if (t->type == T_IO_NUMBER) {
        Token *nx = peek_at(p, 1);

        if (nx->type != T_LESS && nx->type != T_GREAT &&
            nx->type != T_DGREAT && nx->type != T_GREATAND &&
            nx->type != T_LESSAND && nx->type != T_DLESS) {
            return 0;
        }

        pending_fd = t->fd;
        advance(p);
        t = peek(p);
    }

    if (t->type == T_DLESS) {
        int fd = pending_fd != -1 ? pending_fd : 0;
        redir_add(rs, n, T_DLESS, fd, t->text, t->quoted);
        advance(p);
        return 1;
    }

    if (t->type == T_LESS || t->type == T_GREAT || t->type == T_DGREAT ||
        t->type == T_GREATAND || t->type == T_LESSAND) {
        int type = t->type;
        int fd = pending_fd != -1
                 ? pending_fd
                 : ((type == T_LESS || type == T_LESSAND) ? 0 : 1);

        advance(p);

        Token *f = peek(p);
        if (f->type != T_WORD && f->type != T_IO_NUMBER &&
            f->type != T_LBRACE && f->type != T_RBRACE) {
            parse_error(p, "missing redirection target");
            return -1;
        }

        redir_add(rs, n, type, fd, f->text, 0);
        advance(p);
        return 1;
    }

    return 0;
}

static void simple_add_array(Simple *s, char *name, int append,
                             char **words, int nwords, int order) {
    s->arrs = xrealloc(s->arrs, sizeof(ArrAssign) * (s->narr + 1));
    s->arrs[s->narr].name = name;
    s->arrs[s->narr].append = append;
    s->arrs[s->narr].words = words;
    s->arrs[s->narr].nwords = nwords;
    s->arrs[s->narr].order = order;
    s->narr++;
}

/*
 * NAME=(a b c) in the assignment prefix.  The lexer stops the word at the
 * '(' so this arrives as the word "NAME=" followed by T_LPAREN; a function
 * definition is already handled in parse_command, and a non-empty value
 * before the paren is not an array literal, so neither can be confused
 * with one.
 */
static int is_decl_word(const char *w) {
    return w && (strcmp(w, "local") == 0 || strcmp(w, "declare") == 0 ||
                 strcmp(w, "typeset") == 0);
}

static int parse_array_assign(Parser *p, Simple *s, int prefix) {
    Token *t = peek(p);

    /* also after a declaration builtin: local a=(1 2) */
    if (!prefix && !(s->nwords == 1 && is_decl_word(s->words[0]))) return 0;
    if (t->type != T_WORD || t->quoted) return 0;
    if (peek_at(p, 1)->type != T_LPAREN) return 0;

    char *name = NULL;
    char *sub = NULL;
    int append = 0;
    const char *value = NULL;

    if (!split_assign(t->text, &name, &sub, &append, &value)) return 0;

    if (sub || value[0] != '\0') {
        free(name);
        free(sub);
        return 0;
    }

    advance(p);   /* NAME= */
    advance(p);   /* (     */

    Args elems;
    args_init(&elems);

    for (;;) {
        skip_newlines(p);

        Token *e = peek(p);
        if (e->type == T_RPAREN || e->type == T_END) break;

        if (e->type == T_WORD || e->type == T_IO_NUMBER ||
            e->type == T_LBRACE || e->type == T_RBRACE) {
            args_add_copy(&elems, e->text);
            advance(p);
            continue;
        }

        break;
    }

    if (peek_type(p) != T_RPAREN) {
        parse_error(p, "expected ')' in array assignment");
        args_free(&elems);
        free(name);
        return -1;
    }

    advance(p);

    simple_add_array(s, name, append, elems.v, elems.n, s->nwords);
    return 1;
}

static Node *parse_simple_command(Parser *p) {
    Simple *s = new_simple();
    int any = 0;
    int prefix = 1;

    for (;;) {
        Token *t = peek(p);

        int a = parse_array_assign(p, s, prefix);
        if (a < 0) { free_node(new_simple_node(s)); return NULL; }
        if (a > 0) { any = 1; continue; }

        int r = parse_redir(p, &s->redirs, &s->nredir);
        if (r < 0) { free_node(new_simple_node(s)); return NULL; }
        if (r > 0) { any = 1; continue; }

        if (t->type == T_IO_NUMBER) {
            simple_add_word(s, t->text);
            advance(p);
            any = 1;
            continue;
        }

        /*
         * ')' is always an operator - the original accepted it as an
         * argument once the command already had a word, which swallowed
         * the closing paren of every subshell.  '}' is only a reserved
         * word at the start of a command, so it stays legal as an
         * argument.
         */
        if (t->type == T_WORD ||
            (any && (t->type == T_LBRACE || t->type == T_RBRACE))) {
            if (prefix && !(t->type == T_WORD && !t->quoted &&
                            is_assign_word(t->text))) {
                prefix = 0;
            }

            simple_add_word(s, t->text ? t->text : "");
            advance(p);
            any = 1;
            continue;
        }

        break;
    }

    if (!any) {
        free_node(new_simple_node(s));
        return NULL;
    }

    return new_simple_node(s);
}

static Node *parse_brace(Parser *p) {
    advance(p); /* { */

    TType stops[] = { T_RBRACE };
    List *l = parse_list(p, NULL, 0, stops, 1);
    if (!l) return NULL;

    if (peek_type(p) != T_RBRACE) {
        parse_error(p, "expected '}'");
        free_list_tree(l);
        return NULL;
    }

    advance(p);
    return new_list_node(l);
}

static Node *parse_subshell(Parser *p) {
    advance(p); /* ( */

    TType stops[] = { T_RPAREN };
    List *l = parse_list(p, NULL, 0, stops, 1);
    if (!l) return NULL;

    if (peek_type(p) != T_RPAREN) {
        parse_error(p, "expected ')'");
        free_list_tree(l);
        return NULL;
    }

    advance(p);
    return new_subshell_node(l);
}

static Node *parse_for(Parser *p) {
    advance(p); /* for */

    Token *vt = peek(p);
    if (vt->type != T_WORD || vt->quoted) {
        parse_error(p, "expected variable name after for");
        return NULL;
    }

    char *var = xstrdup(vt->text);
    advance(p);

    Args words;
    args_init(&words);
    int use_args = 0;

    skip_newlines(p);

    if (is_word(peek(p), "in")) {
        advance(p);

        for (;;) {
            if (peek_type(p) == T_SEMI || peek_type(p) == T_NEWLINE ||
                peek_type(p) == T_END) {
                break;
            }

            if (is_word(peek(p), "do")) break;

            Token *t = peek(p);
            if (t->type == T_WORD || t->type == T_IO_NUMBER ||
                t->type == T_LBRACE || t->type == T_RBRACE) {
                args_add_copy(&words, t->text);
                advance(p);
                continue;
            }

            break;
        }
    } else {
        use_args = 1;
    }

    skip_separators(p);

    if (!is_word(peek(p), "do")) {
        parse_error(p, "expected 'do' after for");
        free(var);
        args_free(&words);
        return NULL;
    }

    advance(p);

    const char *stop_done[] = { "done" };
    List *body = parse_list(p, stop_done, 1, NULL, 0);
    if (!body) { free(var); args_free(&words); return NULL; }

    if (!is_word(peek(p), "done")) {
        parse_error(p, "expected 'done'");
        free(var);
        args_free(&words);
        free_list_tree(body);
        return NULL;
    }

    advance(p);

    For *f = xmalloc(sizeof(*f));
    f->var = var;
    f->words = words.v;
    f->nwords = words.n;
    f->use_args = use_args;
    f->body = body;

    return new_node(N_FOR, f);
}

static Node *parse_while(Parser *p, int until) {
    advance(p); /* while / until */

    const char *stop_do[] = { "do" };
    List *cond = parse_list(p, stop_do, 1, NULL, 0);
    if (!cond) return NULL;

    if (!is_word(peek(p), "do")) {
        parse_error(p, "expected 'do' after condition");
        free_list_tree(cond);
        return NULL;
    }

    advance(p);

    const char *stop_done[] = { "done" };
    List *body = parse_list(p, stop_done, 1, NULL, 0);
    if (!body) { free_list_tree(cond); return NULL; }

    if (!is_word(peek(p), "done")) {
        parse_error(p, "expected 'done'");
        free_list_tree(cond);
        free_list_tree(body);
        return NULL;
    }

    advance(p);
    return new_while_node(cond, body, until);
}

static Node *parse_case(Parser *p) {
    advance(p); /* case */

    Token *wt = peek(p);
    if (wt->type != T_WORD && wt->type != T_IO_NUMBER) {
        parse_error(p, "expected word after case");
        return NULL;
    }

    Case *c = xmalloc(sizeof(*c));
    c->word = xstrdup(wt->text);
    c->items = NULL;
    c->n = 0;

    advance(p);
    skip_newlines(p);

    if (!is_word(peek(p), "in")) {
        parse_error(p, "expected 'in' after case word");
        free(c->word);
        free(c);
        return NULL;
    }

    advance(p);
    skip_newlines(p);

    while (!is_word(peek(p), "esac") && peek_type(p) != T_END) {
        if (peek_type(p) == T_LPAREN) advance(p);

        Args pats;
        args_init(&pats);

        for (;;) {
            Token *t = peek(p);

            if (t->type != T_WORD && t->type != T_IO_NUMBER &&
                t->type != T_LBRACE && t->type != T_RBRACE) {
                parse_error(p, "expected pattern in case");
                args_free(&pats);
                goto fail;
            }

            args_add_copy(&pats, t->text);
            advance(p);

            if (peek_type(p) == T_PIPE) { advance(p); continue; }
            break;
        }

        if (peek_type(p) != T_RPAREN) {
            parse_error(p, "expected ')' after case pattern");
            args_free(&pats);
            goto fail;
        }

        advance(p);

        const char *stop_esac[] = { "esac" };
        TType stops[] = { T_DSEMI };
        List *body = parse_list(p, stop_esac, 1, stops, 1);
        if (!body) { args_free(&pats); goto fail; }

        c->items = xrealloc(c->items, sizeof(CaseItem) * (c->n + 1));
        c->items[c->n].pats = pats.v;
        c->items[c->n].npat = pats.n;
        c->items[c->n].body = body;
        c->n++;

        if (peek_type(p) == T_DSEMI) advance(p);
        skip_newlines(p);
    }

    if (!is_word(peek(p), "esac")) {
        parse_error(p, "expected 'esac'");
        goto fail;
    }

    advance(p);
    return new_node(N_CASE, c);

fail:
    {
        Node tmp;
        tmp.type = N_CASE;
        tmp.data = c;
        /* free the partially built case without freeing the stack node */
        for (int i = 0; i < c->n; i++) {
            for (int j = 0; j < c->items[i].npat; j++) free(c->items[i].pats[j]);
            free(c->items[i].pats);
            free_list_tree(c->items[i].body);
        }
        free(c->items);
        free(c->word);
        free(c);
        (void)tmp;
    }
    return NULL;
}

static Node *parse_if(Parser *p) {
    advance(p); /* if */

    List **conds = NULL;
    List **thens = NULL;
    int n = 0;
    Node *else_node = NULL;

    for (;;) {
        const char *stop_then[] = { "then" };
        List *cond = parse_list(p, stop_then, 1, NULL, 0);
        if (!cond) goto fail;

        if (!is_word(peek(p), "then")) {
            parse_error(p, "expected 'then'");
            free_list_tree(cond);
            goto fail;
        }
        advance(p);

        const char *stop_body[] = { "else", "elif", "fi" };
        List *then = parse_list(p, stop_body, 3, NULL, 0);
        if (!then) { free_list_tree(cond); goto fail; }

        conds = xrealloc(conds, sizeof(List *) * (n + 1));
        thens = xrealloc(thens, sizeof(List *) * (n + 1));
        conds[n] = cond;
        thens[n] = then;
        n++;

        if (is_word(peek(p), "elif")) { advance(p); continue; }
        break;
    }

    if (is_word(peek(p), "else")) {
        advance(p);

        const char *stop_fi[] = { "fi" };
        List *else_list = parse_list(p, stop_fi, 1, NULL, 0);
        if (!else_list) goto fail;

        else_node = new_list_node(else_list);
    }

    if (!is_word(peek(p), "fi")) {
        parse_error(p, "expected 'fi'");
        goto fail;
    }

    advance(p);

    Node *result = NULL;
    for (int i = n - 1; i >= 0; i--) {
        result = new_if_node(conds[i], thens[i], else_node);
        else_node = result;
    }

    free(conds);
    free(thens);
    return result;

fail:
    for (int i = 0; i < n; i++) {
        free_list_tree(conds[i]);
        free_list_tree(thens[i]);
    }
    free(conds);
    free(thens);
    free_node(else_node);
    return NULL;
}

static Node *parse_function_keyword(Parser *p) {
    advance(p); /* function */

    Token *name = peek(p);
    if (name->type != T_WORD || name->quoted) {
        parse_error(p, "expected function name");
        return NULL;
    }

    char *fname = xstrdup(name->text);
    advance(p);

    if (peek_type(p) == T_LPAREN) {
        advance(p);
        if (peek_type(p) != T_RPAREN) {
            parse_error(p, "expected ')' in function definition");
            free(fname);
            return NULL;
        }
        advance(p);
    }

    skip_newlines(p);

    Node *body = parse_command(p);
    if (!body) { free(fname); return NULL; }

    return new_func_node(fname, body);
}

static Node *parse_function_paren(Parser *p) {
    Token *name = peek(p);
    char *fname = xstrdup(name->text);

    advance(p); /* name */
    advance(p); /* ( */
    advance(p); /* ) */

    skip_newlines(p);

    Node *body = parse_command(p);
    if (!body) { free(fname); return NULL; }

    return new_func_node(fname, body);
}

/*
 * Attach any trailing redirections to a compound command, so that
 *   while read l; do ...; done < file
 * feeds the whole loop.  The original only allowed redirections on a
 * simple command, which is why a read loop had nothing to read from.
 */
static Node *wrap_redirs(Parser *p, Node *body) {
    if (!body) return NULL;

    Redir *rs = NULL;
    int n = 0;

    for (;;) {
        int r = parse_redir(p, &rs, &n);
        if (r < 0) { free_node(body); redirs_free(rs, n); return NULL; }
        if (r == 0) break;
    }

    if (n == 0) return body;

    RedirNode *rn = xmalloc(sizeof(*rn));
    rn->body = body;
    rn->redirs = rs;
    rn->nredir = n;

    return new_node(N_REDIR, rn);
}

static Node *parse_command(Parser *p) {
    Token *t = peek(p);

    if (is_word(t, "function")) return parse_function_keyword(p);

    /*
     * name() { ... } is a function definition, but g=() is an empty array
     * literal - a function name cannot contain '=', so the assignment
     * test is what tells them apart.
     */
    if (t->type == T_WORD && !t->quoted && !is_assign_word(t->text)) {
        Token *n1 = peek_at(p, 1);
        Token *n2 = peek_at(p, 2);

        if (n1->type == T_LPAREN && n2->type == T_RPAREN) {
            return parse_function_paren(p);
        }
    }

    if (is_word(t, "if")) return wrap_redirs(p, parse_if(p));
    if (is_word(t, "while")) return wrap_redirs(p, parse_while(p, 0));
    if (is_word(t, "until")) return wrap_redirs(p, parse_while(p, 1));
    if (is_word(t, "for")) return wrap_redirs(p, parse_for(p));
    if (is_word(t, "case")) return wrap_redirs(p, parse_case(p));
    if (t->type == T_LBRACE) return wrap_redirs(p, parse_brace(p));
    if (t->type == T_LPAREN) return wrap_redirs(p, parse_subshell(p));

    return parse_simple_command(p);
}

static Pipeline *parse_pipeline(Parser *p) {
    Pipeline *pl = new_pipeline();

    while (is_word(peek(p), "!")) {
        pl->bang = !pl->bang;
        advance(p);
    }

    Node *c = parse_command(p);
    if (!c) { free(pl->cmds); free(pl); return NULL; }

    pipeline_add(pl, c);

    while (peek_type(p) == T_PIPE) {
        advance(p);
        skip_newlines(p);

        c = parse_command(p);
        if (!c) {
            for (int i = 0; i < pl->n; i++) free_node(pl->cmds[i]);
            free(pl->cmds);
            free(pl);
            return NULL;
        }

        pipeline_add(pl, c);
    }

    return pl;
}

static void free_pipeline_tree(Pipeline *p) {
    if (!p) return;
    for (int i = 0; i < p->n; i++) free_node(p->cmds[i]);
    free(p->cmds);
    free(p);
}

static Andor *parse_andor(Parser *p) {
    Pipeline *pl = parse_pipeline(p);
    if (!pl) return NULL;

    Andor *a = new_andor();
    andor_add(a, pl, 0);

    while (peek_type(p) == T_AND || peek_type(p) == T_OR) {
        int op = peek_type(p);
        advance(p);
        skip_newlines(p);

        pl = parse_pipeline(p);
        if (!pl) {
            for (int i = 0; i < a->n; i++) free_pipeline_tree(a->pipes[i]);
            free(a->pipes);
            free(a->ops);
            free(a);
            return NULL;
        }

        andor_add(a, pl, op);
    }

    return a;
}

static List *parse_list(Parser *p,
                        const char **stop_words, int nstop_words,
                        const TType *stop_types, int nstop_types) {
    List *l = new_list();

    for (;;) {
        skip_separators(p);

        if (peek_type(p) == T_END) break;
        if (is_stop(p, stop_words, nstop_words, stop_types, nstop_types)) break;

        Andor *a = parse_andor(p);
        if (!a) { free_list_tree(l); return NULL; }

        int bg = 0;
        if (peek_type(p) == T_AMP) {
            advance(p);
            bg = 1;
        }

        list_add(l, a, bg);
    }

    return l;
}

/* ------------------------------------------------------------------ */
/* Expansion                                                            */
/* ------------------------------------------------------------------ */

enum {
    EXP_WORD = 0,      /* full: quote removal, splitting, globbing */
    EXP_SCALAR,        /* one field, no splitting or globbing */
    EXP_HEREDOC,       /* only $ and ` are special */
    EXP_PATTERN        /* one field, quoted characters backslash-escaped */
};

typedef struct {
    Args *out;
    Str buf;
    Str msk;           /* 'Q' quoted, 'L' literal, 'S' from an unquoted expansion */
    int started;
    int hard;          /* the field exists even if it is empty */
    int at_null;       /* "$@" expanded to nothing */
    int mode;
} Exp;

static int run_program_string(const char *s);
static char *expand_scalar(const char *raw);
static long arith_eval(const char *expr, int *err);
static int assign_index(const char *name, const char *sub);

/*
 * ${var:offset:length} and ${a[@]:offset:length}.  A negative offset
 * counts back from the end and a negative length trims from the end,
 * the same as bash.  A missing length means "to the end".
 */
static int slice_bound(const char *text, long total, long dflt) {
    if (!text) return (int)dflt;

    char *expanded = expand_scalar(text);

    int err = 0;
    long v = arith_eval(expanded, &err);
    free(expanded);

    if (err) return (int)dflt;
    if (v < 0) v += total;
    return (int)v;
}

static char *slice_string(const char *val, const char *off, const char *len) {
    long total = (long)strlen(val);

    long start = slice_bound(off, total, 0);
    if (start < 0) start = 0;
    if (start > total) start = total;

    long count = len ? slice_bound(len, 0, total - start) : total - start;
    if (len && count < 0) count = (total - start) + count;
    if (count < 0) count = 0;
    if (start + count > total) count = total - start;

    char *out = xmalloc(count + 1);
    memcpy(out, val + start, count);
    out[count] = '\0';
    return out;
}

static void slice_args(Args *a, const char *off, const char *len) {
    if (!off) return;

    long total = a->n;

    long start = slice_bound(off, total, 0);
    if (start < 0) start = 0;
    if (start > total) start = total;

    long count = len ? slice_bound(len, 0, total - start) : total - start;
    if (len && count < 0) count = (total - start) + count;
    if (count < 0) count = 0;
    if (start + count > total) count = total - start;

    for (long k = 0; k < start; k++) free(a->v[k]);
    for (long k = start + count; k < total; k++) free(a->v[k]);

    for (long k = 0; k < count; k++) a->v[k] = a->v[start + k];

    a->n = (int)count;
    a->v[a->n] = NULL;
}

static void exp_init(Exp *e, Args *out, int mode) {
    e->out = out;
    str_init(&e->buf);
    str_init(&e->msk);
    e->started = 0;
    e->hard = 0;
    e->at_null = 0;
    e->mode = mode;
}

static void exp_done(Exp *e) {
    free(e->buf.s);
    free(e->msk.s);
}

static void exp_addch(Exp *e, char c, char m) {
    str_addch(&e->buf, c);
    str_addch(&e->msk, m);
    e->started = 1;
}

static void exp_addstr(Exp *e, const char *s, char m) {
    if (!s) return;
    for (int i = 0; s[i]; i++) exp_addch(e, s[i], m);
}

/* build a glob pattern from a field, escaping everything that was quoted */
static char *field_pattern(const char *buf, const char *msk, size_t len) {
    Str out;
    str_init(&out);

    for (size_t i = 0; i < len; i++) {
        char c = buf[i];

        if (msk[i] == 'Q' || c == '\\') str_addch(&out, '\\');
        str_addch(&out, c);
    }

    return out.s;
}

static int exp_emit_field(Exp *e, size_t start, size_t len) {
    char *pat = field_pattern(e->buf.s + start, e->msk.s + start, len);

    int added = 0;
    if (pattern_has_magic(pat)) added = glob_expand(pat, e->out);

    if (added == 0) {
        char *lit = pattern_unescape(pat);
        args_add_copy(e->out, lit);
        free(lit);
        added = 1;
    }

    free(pat);
    return added;
}

static int ifs_is_sep(char c, const char *ifs, int *ws) {
    if (!strchr(ifs, c)) return 0;
    *ws = (c == ' ' || c == '\t' || c == '\n');
    return 1;
}

static void exp_flush(Exp *e) {
    if (!e->started) {
        str_clear(&e->buf);
        str_clear(&e->msk);
        e->hard = 0;
        e->at_null = 0;
        return;
    }

    if (e->mode == EXP_SCALAR || e->mode == EXP_HEREDOC) {
        args_add_copy(e->out, e->buf.s);
    } else if (e->mode == EXP_PATTERN) {
        char *pat = field_pattern(e->buf.s, e->msk.s, e->buf.len);
        args_add(e->out, pat);
    } else {
        const char *ifs = var_get("IFS");
        if (!ifs) ifs = " \t\n";

        int nfields = 0;
        size_t i = 0;
        size_t len = e->buf.len;

        while (i < len) {
            int ws = 0;

            /* skip a run of splittable whitespace */
            while (i < len && e->msk.s[i] == 'S' &&
                   ifs_is_sep(e->buf.s[i], ifs, &ws) && ws) {
                i++;
            }

            /* a single non-whitespace IFS character delimits a field */
            if (i < len && e->msk.s[i] == 'S' &&
                ifs_is_sep(e->buf.s[i], ifs, &ws) && !ws) {
                args_add_copy(e->out, "");
                nfields++;
                i++;
                continue;
            }

            if (i >= len) break;

            size_t start = i;
            while (i < len) {
                if (e->msk.s[i] == 'S' && ifs_is_sep(e->buf.s[i], ifs, &ws)) break;
                i++;
            }

            nfields += exp_emit_field(e, start, i - start);

            /* consume one delimiter */
            if (i < len) {
                if (ifs_is_sep(e->buf.s[i], ifs, &ws) && !ws) i++;
            }
        }

        if (nfields == 0 && e->hard && !e->at_null) args_add_copy(e->out, "");
    }

    str_clear(&e->buf);
    str_clear(&e->msk);
    e->started = 0;
    e->hard = 0;
    e->at_null = 0;
}

/* run TEXT as a program and capture its standard output */
static char *command_substitute(const char *text) {
    int fds[2];

    cmdsub_count++;

    if (pipe(fds) < 0) {
        fprintf(stderr, "minishell: pipe: %s\n", strerror(errno));
        return xstrdup("");
    }

    pid_t pid = fork();
    if (pid < 0) {
        fprintf(stderr, "minishell: fork: %s\n", strerror(errno));
        close(fds[0]);
        close(fds[1]);
        return xstrdup("");
    }

    if (pid == 0) {
        close(fds[0]);
        if (dup2(fds[1], 1) < 0) _exit(1);
        close(fds[1]);

        signal(SIGINT, SIG_DFL);
        signal(SIGQUIT, SIG_DFL);

        interactive = 0;
        int st = run_program_string(text);

        fflush(NULL);
        _exit(shell_exit ? last_status : st);
    }

    close(fds[1]);

    Str out;
    str_init(&out);

    char buf[4096];
    ssize_t r;
    while ((r = read(fds[0], buf, sizeof(buf))) > 0) str_addn(&out, buf, (size_t)r);

    close(fds[0]);

    int st;
    while (waitpid(pid, &st, 0) < 0) {
        if (errno != EINTR) break;
    }

    if (WIFEXITED(st)) last_status = WEXITSTATUS(st);
    else if (WIFSIGNALED(st)) last_status = 128 + WTERMSIG(st);

    while (out.len > 0 && out.s[out.len - 1] == '\n') out.s[--out.len] = '\0';

    return out.s;
}

static void nounset_fail(const char *name) {
    fprintf(stderr, "minishell: %s: parameter not set\n", name);
    last_status = 2;
    if (!interactive) {
        shell_exit = 1;
        exit_requested = 1;
    }
}

/*
 * Expand one $... construct.  I is the index of the '$'.  Returns the index
 * just past the construct.  INQUOTE selects the mask, and changes how "$@"
 * behaves.
 */
static int expand_dollar(Exp *e, const char *s, int i, int inquote) {
    char m = inquote ? 'Q' : 'S';
    i++; /* skip $ */

    if (s[i] == '?') {
        char b[32];
        snprintf(b, sizeof(b), "%d", last_status);
        exp_addstr(e, b, m);
        return i + 1;
    }

    if (s[i] == '$') {
        char b[32];
        snprintf(b, sizeof(b), "%ld", (long)getpid());
        exp_addstr(e, b, m);
        return i + 1;
    }

    if (s[i] == '!') {
        char b[32];
        snprintf(b, sizeof(b), "%ld", (long)last_bg_pid);
        if (last_bg_pid) exp_addstr(e, b, m);
        return i + 1;
    }

    if (s[i] == '#') {
        char b[32];
        snprintf(b, sizeof(b), "%d", cur_argc() > 0 ? cur_argc() - 1 : 0);
        exp_addstr(e, b, m);
        return i + 1;
    }

    if (s[i] == '@') {
        char **av = cur_argv();
        int ac = cur_argc();

        if (inquote && e->mode == EXP_WORD) {
            /* one field per parameter */
            if (ac <= 1) {
                e->at_null = 1;
            } else {
                for (int j = 1; j < ac; j++) {
                    if (j > 1) exp_flush(e);
                    e->started = 1;
                    e->hard = 1;
                    exp_addstr(e, av[j], 'Q');
                }
            }
        } else {
            for (int j = 1; j < ac; j++) {
                if (j > 1) exp_addch(e, ' ', m);
                exp_addstr(e, av[j], m);
            }
        }

        return i + 1;
    }

    if (s[i] == '*') {
        const char *ifs = var_get("IFS");
        char sep = (ifs && ifs[0]) ? ifs[0] : ' ';
        if (!ifs) sep = ' ';

        char **av = cur_argv();
        int ac = cur_argc();

        for (int j = 1; j < ac; j++) {
            if (j > 1) exp_addch(e, inquote ? sep : ' ', m);
            exp_addstr(e, av[j], m);
        }

        return i + 1;
    }

    /* $(( arithmetic )) */
    if (s[i] == '(' && s[i + 1] == '(') {
        int depth = 0;
        int start = i + 2;
        int j = i;

        while (s[j]) {
            if (s[j] == '(') depth++;
            else if (s[j] == ')') { depth--; if (depth == 0) break; }
            j++;
        }

        /* j is at the ')' that closes the outer paren; inner ends at j-1 */
        int end = j > start && s[j - 1] == ')' ? j - 1 : j;

        char *raw = xmalloc(end - start + 1);
        memcpy(raw, s + start, end - start);
        raw[end - start] = '\0';

        char *expanded = expand_scalar(raw);

        int err = 0;
        long v = arith_eval(expanded, &err);

        if (err) {
            fprintf(stderr, "minishell: arithmetic: bad expression: %s\n", expanded);
            last_status = 1;
        }

        char b[32];
        snprintf(b, sizeof(b), "%ld", v);
        exp_addstr(e, b, m);

        free(expanded);
        free(raw);

        return s[j] ? j + 1 : j;
    }

    /* $( command ) */
    if (s[i] == '(') {
        int depth = 0;
        int q = 0;
        int start = i + 1;
        int j = i;

        while (s[j]) {
            char c = s[j];

            if (q == 1) { if (c == '\'') q = 0; j++; continue; }
            if (c == '\\' && s[j + 1] && q != 1) { j += 2; continue; }
            if (q == 2) { if (c == '"') q = 0; j++; continue; }
            if (c == '\'') { q = 1; j++; continue; }
            if (c == '"') { q = 2; j++; continue; }

            if (c == '(') depth++;
            else if (c == ')') { depth--; if (depth == 0) break; }

            j++;
        }

        char *raw = xmalloc(j - start + 1);
        memcpy(raw, s + start, j - start);
        raw[j - start] = '\0';

        char *val = command_substitute(raw);
        exp_addstr(e, val, m);
        if (val[0] == '\0') e->started = e->started;

        free(val);
        free(raw);

        return s[j] ? j + 1 : j;
    }

    /* ${...} */
    if (s[i] == '{') {
        i++;

        int nlen = 0;
        int hashlen = 0;
        int bang = 0;

        if (s[i] == '#' && s[i + 1] && s[i + 1] != '}') {
            hashlen = 1;
            i++;
        } else if (s[i] == '!' && s[i + 1] && s[i + 1] != '}') {
            bang = 1;
            i++;
        }

        int start = i;
        if (s[i] == '@' || s[i] == '*' || s[i] == '?' || s[i] == '#' ||
            s[i] == '$' || s[i] == '!') {
            i++;
        } else {
            while (s[i] && (isalnum((unsigned char)s[i]) || s[i] == '_')) i++;
        }
        nlen = i - start;

        char *name = xmalloc(nlen + 1);
        memcpy(name, s + start, nlen);
        name[nlen] = '\0';

        /* [subscript] */
        char *sub = NULL;
        if (s[i] == '[') {
            int depth = 0;
            int sstart = i + 1;
            int j = i;

            while (s[j]) {
                if (s[j] == '[') depth++;
                else if (s[j] == ']') { depth--; if (depth == 0) break; }
                j++;
            }

            if (s[j] == ']') {
                sub = xmalloc(j - sstart + 1);
                memcpy(sub, s + sstart, j - sstart);
                sub[j - sstart] = '\0';
                i = j + 1;
            }
        }

        /* :offset:length  -  not to be confused with :- := :+ :? */
        char *sl_off = NULL;
        char *sl_len = NULL;

        if (s[i] == ':' && s[i + 1] && !strchr("-=?+", s[i + 1])) {
            i++;
            int st2 = i;
            while (s[i] && s[i] != ':' && s[i] != '}') i++;

            sl_off = xmalloc(i - st2 + 1);
            memcpy(sl_off, s + st2, i - st2);
            sl_off[i - st2] = '\0';

            if (s[i] == ':') {
                i++;
                st2 = i;
                while (s[i] && s[i] != '}') i++;

                sl_len = xmalloc(i - st2 + 1);
                memcpy(sl_len, s + st2, i - st2);
                sl_len[i - st2] = '\0';
            }
        }

        /*
         * ${a[@]} / ${a[*]} / ${!a[@]} / ${#a[@]} - these produce a whole
         * list, so they are handled here and return; everything below
         * deals with a single value.
         */
        if (sub && (strcmp(sub, "@") == 0 || strcmp(sub, "*") == 0)) {
            int star = strcmp(sub, "*") == 0;

            Args items;
            args_init(&items);

            Var *av = var_find(name);
            if (av) {
                for (int k = 0; k < av->nitems; k++) {
                    if (!av->items[k]) continue;

                    if (bang) {
                        char b[32];
                        snprintf(b, sizeof(b), "%d", k);
                        args_add_copy(&items, b);
                    } else {
                        args_add_copy(&items, av->items[k]);
                    }
                }
            } else if (!bang) {
                const char *env = getenv(name);
                if (env) args_add_copy(&items, env);
            }

            slice_args(&items, sl_off, sl_len);

            if (hashlen) {
                char b[32];
                snprintf(b, sizeof(b), "%d", items.n);
                exp_addstr(e, b, m);
            } else if (star || !inquote || e->mode != EXP_WORD) {
                const char *ifs = var_get("IFS");
                char sep = ' ';
                if (star && inquote) sep = (ifs && ifs[0]) ? ifs[0] : (ifs ? '\0' : ' ');

                for (int k = 0; k < items.n; k++) {
                    if (k && sep) exp_addch(e, sep, m);
                    exp_addstr(e, items.v[k], m);
                }
            } else {
                if (items.n == 0) {
                    e->at_null = 1;
                } else {
                    for (int k = 0; k < items.n; k++) {
                        if (k) exp_flush(e);
                        e->started = 1;
                        e->hard = 1;
                        exp_addstr(e, items.v[k], 'Q');
                    }
                }
            }

            args_free(&items);
            free(sl_off);
            free(sl_len);
            free(sub);
            free(name);

            while (s[i] && s[i] != '}') i++;
            if (s[i] == '}') i++;
            return i;
        }

        const char *val = NULL;
        char numbuf[32];

        int all_digits = nlen > 0;
        for (int k = 0; k < nlen; k++) {
            if (!isdigit((unsigned char)name[k])) { all_digits = 0; break; }
        }

        if (sub) {
            int idx = assign_index(name, sub);
            val = idx < 0 ? NULL : var_elem(name, idx);
        } else if (all_digits) {
            int num = atoi(name);
            if (num < cur_argc()) val = cur_argv()[num];
        } else if (strcmp(name, "#") == 0) {
            snprintf(numbuf, sizeof(numbuf), "%d",
                     cur_argc() > 0 ? cur_argc() - 1 : 0);
            val = numbuf;
        } else if (strcmp(name, "?") == 0) {
            snprintf(numbuf, sizeof(numbuf), "%d", last_status);
            val = numbuf;
        } else if (strcmp(name, "$") == 0) {
            snprintf(numbuf, sizeof(numbuf), "%ld", (long)getpid());
            val = numbuf;
        } else {
            val = var_get(name);
        }

        /* ${!x} - the value of the variable that x names */
        if (bang && val) val = var_get(val);
        else if (bang) val = NULL;

        char *sliced = NULL;
        if (sl_off) {
            sliced = slice_string(val ? val : "", sl_off, sl_len);
            val = sliced;
        }

        /* collect the word after the operator, up to the matching '}' */
        char op = '\0';
        int colon = 0;
        char *arg = NULL;

        /*
         * strchr(str, '\0') returns a pointer to the terminator, not NULL,
         * so these tests must check for end of string first - otherwise
         * "${" and "${x:" walked off the end of the word.
         */
        if (s[i] == ':' && s[i + 1] && strchr("-=?+", s[i + 1])) {
            colon = 1;
            op = s[i + 1];
            i += 2;
        } else if (s[i] && strchr("-=?+#%", s[i])) {
            op = s[i];
            i++;
            if ((op == '#' || op == '%') && s[i] == op) { colon = 1; i++; }
        }

        if (op) {
            int depth = 1;
            int astart = i;

            while (s[i]) {
                if (s[i] == '{') depth++;
                else if (s[i] == '}') { depth--; if (depth == 0) break; }
                i++;
            }

            arg = xmalloc(i - astart + 1);
            memcpy(arg, s + astart, i - astart);
            arg[i - astart] = '\0';
        }

        while (s[i] && s[i] != '}') i++;
        if (s[i] == '}') i++;

        int unset_or_null = (!val || (colon && !*val));
        if (op == '#' || op == '%') unset_or_null = 0;

        if (hashlen) {
            char b[32];
            snprintf(b, sizeof(b), "%d", val ? (int)strlen(val) : 0);
            exp_addstr(e, b, m);
        } else if (op == '-' && unset_or_null) {
            char *d = expand_scalar(arg ? arg : "");
            exp_addstr(e, d, m);
            free(d);
        } else if (op == '=' && unset_or_null) {
            char *d = expand_scalar(arg ? arg : "");
            var_set(name, d);
            exp_addstr(e, d, m);
            free(d);
        } else if (op == '+') {
            if (!unset_or_null && val) {
                char *d = expand_scalar(arg ? arg : "");
                exp_addstr(e, d, m);
                free(d);
            }
        } else if (op == '?' && unset_or_null) {
            char *d = expand_scalar(arg ? arg : "");
            fprintf(stderr, "minishell: %s: %s\n", name,
                    d[0] ? d : "parameter not set");
            free(d);
            last_status = 1;
            if (!interactive) { shell_exit = 1; exit_requested = 1; }
        } else if (op == '#' || op == '%') {
            const char *v = val ? val : "";
            char *pat = expand_scalar(arg ? arg : "");
            size_t vlen = strlen(v);
            size_t best = 0;
            int found = 0;

            if (op == '#') {
                for (size_t k = 0; k <= vlen; k++) {
                    char save = ((char *)v)[k];
                    char *tmp = xmalloc(k + 1);
                    memcpy(tmp, v, k);
                    tmp[k] = '\0';
                    (void)save;

                    if (glob_match(pat, tmp)) {
                        if (!found || (colon ? k > best : k < best)) {
                            best = k;
                            found = 1;
                        }
                        if (!colon) { free(tmp); break; }
                    }
                    free(tmp);
                }
                exp_addstr(e, found ? v + best : v, m);
            } else {
                for (size_t k = 0; k <= vlen; k++) {
                    size_t cut = colon ? k : vlen - k;
                    if (glob_match(pat, v + cut)) {
                        best = cut;
                        found = 1;
                        break;
                    }
                }

                if (found) {
                    char *tmp = xmalloc(best + 1);
                    memcpy(tmp, v, best);
                    tmp[best] = '\0';
                    exp_addstr(e, tmp, m);
                    free(tmp);
                } else {
                    exp_addstr(e, v, m);
                }
            }

            free(pat);
        } else {
            if (!val && opt_nounset && !op) nounset_fail(name);
            if (val) exp_addstr(e, val, m);
        }

        free(arg);
        free(name);
        free(sub);
        free(sl_off);
        free(sl_len);
        free(sliced);
        return i;
    }

    if (isdigit((unsigned char)s[i])) {
        int n = 0;
        while (isdigit((unsigned char)s[i])) {
            n = n * 10 + (s[i] - '0');
            i++;
        }

        if (n < cur_argc()) exp_addstr(e, cur_argv()[n], m);
        return i;
    }

    if (isalpha((unsigned char)s[i]) || s[i] == '_') {
        int start = i;
        while (s[i] && (isalnum((unsigned char)s[i]) || s[i] == '_')) i++;

        int len = i - start;
        char *name = xmalloc(len + 1);
        memcpy(name, s + start, len);
        name[len] = '\0';

        const char *val = var_get(name);
        if (val) exp_addstr(e, val, m);
        else if (opt_nounset) nounset_fail(name);

        free(name);
        return i;
    }

    exp_addch(e, '$', inquote ? 'Q' : 'L');
    return i;
}

static int expand_backtick(Exp *e, const char *s, int i, int inquote) {
    char m = inquote ? 'Q' : 'S';
    i++; /* skip ` */

    Str body;
    str_init(&body);

    while (s[i] && s[i] != '`') {
        if (s[i] == '\\' && (s[i + 1] == '`' || s[i + 1] == '\\' ||
                             s[i + 1] == '$')) {
            str_addch(&body, s[i + 1]);
            i += 2;
            continue;
        }
        str_addch(&body, s[i++]);
    }

    if (s[i] == '`') i++;

    char *val = command_substitute(body.s);
    exp_addstr(e, val, m);

    free(val);
    free(body.s);
    return i;
}

static void expand_word(Exp *e, const char *raw) {
    int i = 0;

    if (e->mode == EXP_HEREDOC) {
        while (raw[i]) {
            if (raw[i] == '\\' &&
                (raw[i + 1] == '$' || raw[i + 1] == '`' || raw[i + 1] == '\\')) {
                exp_addch(e, raw[i + 1], 'Q');
                i += 2;
                continue;
            }

            if (raw[i] == '$') { i = expand_dollar(e, raw, i, 1); continue; }
            if (raw[i] == '`') { i = expand_backtick(e, raw, i, 1); continue; }

            exp_addch(e, raw[i++], 'L');
        }

        e->started = 1;
        return;
    }

    while (raw[i]) {
        if (raw[i] == '\\') {
            e->hard = 1;
            e->started = 1;

            if (raw[i + 1]) {
                exp_addch(e, raw[i + 1], 'Q');
                i += 2;
            } else {
                exp_addch(e, '\\', 'Q');
                i++;
            }
            continue;
        }

        if (raw[i] == '\'') {
            e->hard = 1;
            e->started = 1;
            i++;

            while (raw[i] && raw[i] != '\'') exp_addch(e, raw[i++], 'Q');
            if (raw[i] == '\'') i++;
            continue;
        }

        if (raw[i] == '"') {
            e->hard = 1;
            e->started = 1;
            i++;

            while (raw[i] && raw[i] != '"') {
                if (raw[i] == '\\' &&
                    (raw[i + 1] == '$' || raw[i + 1] == '"' ||
                     raw[i + 1] == '\\' || raw[i + 1] == '`')) {
                    exp_addch(e, raw[i + 1], 'Q');
                    i += 2;
                    continue;
                }

                if (raw[i] == '$') { i = expand_dollar(e, raw, i, 1); continue; }
                if (raw[i] == '`') { i = expand_backtick(e, raw, i, 1); continue; }

                exp_addch(e, raw[i++], 'Q');
            }

            if (raw[i] == '"') i++;
            continue;
        }

        if (raw[i] == '$') { i = expand_dollar(e, raw, i, 0); continue; }
        if (raw[i] == '`') { i = expand_backtick(e, raw, i, 0); continue; }

        exp_addch(e, raw[i++], 'L');
    }
}

/* ~ or ~/... at the start of a word */
static char *tilde_prefix(const char *raw, int *used) {
    *used = 0;
    if (raw[0] != '~') return NULL;
    if (raw[1] && raw[1] != '/') return NULL;

    const char *home = var_get("HOME");
    if (!home) return NULL;

    *used = 1;
    return xstrdup(home);
}

static void expand_into(Args *out, const char *raw, int mode) {
    Exp e;
    exp_init(&e, out, mode);

    if (mode != EXP_HEREDOC) {
        int used = 0;
        char *home = tilde_prefix(raw, &used);
        if (used) {
            exp_addstr(&e, home, 'Q');
            raw += 1;
        }
        free(home);
    }

    expand_word(&e, raw);
    exp_flush(&e);
    exp_done(&e);
}

static char *expand_scalar(const char *raw) {
    Args a;
    args_init(&a);
    expand_into(&a, raw, EXP_SCALAR);

    char *r = a.n > 0 ? xstrdup(a.v[0]) : xstrdup("");
    args_free(&a);
    return r;
}

static char *expand_heredoc(const char *raw) {
    Args a;
    args_init(&a);
    expand_into(&a, raw, EXP_HEREDOC);

    char *r = a.n > 0 ? xstrdup(a.v[0]) : xstrdup("");
    args_free(&a);
    return r;
}

static char *expand_pattern(const char *raw) {
    Args a;
    args_init(&a);
    expand_into(&a, raw, EXP_PATTERN);

    char *r = a.n > 0 ? xstrdup(a.v[0]) : xstrdup("");
    args_free(&a);
    return r;
}

static void expand_to_args(const char *raw, Args *args) {
    expand_into(args, raw, EXP_WORD);
}

/* ------------------------------------------------------------------ */
/* Arithmetic                                                           */
/* ------------------------------------------------------------------ */

typedef struct {
    const char *s;
    int i;
    int err;
} Arith;

static long ar_or(Arith *a);

static void ar_skip(Arith *a) {
    while (a->s[a->i] == ' ' || a->s[a->i] == '\t' || a->s[a->i] == '\n') a->i++;
}

static int ar_eat(Arith *a, const char *op) {
    ar_skip(a);
    size_t n = strlen(op);
    if (strncmp(a->s + a->i, op, n) == 0) {
        /* do not let "<" swallow the "<" of "<<" etc. */
        a->i += (int)n;
        return 1;
    }
    return 0;
}

static long ar_primary(Arith *a) {
    ar_skip(a);

    if (a->s[a->i] == '(') {
        a->i++;
        long v = ar_or(a);
        ar_skip(a);
        if (a->s[a->i] == ')') a->i++;
        else a->err = 1;
        return v;
    }

    if (a->s[a->i] == '-') { a->i++; return -ar_primary(a); }
    if (a->s[a->i] == '+') { a->i++; return ar_primary(a); }
    if (a->s[a->i] == '!') { a->i++; return !ar_primary(a); }
    if (a->s[a->i] == '~') { a->i++; return ~ar_primary(a); }

    if (isdigit((unsigned char)a->s[a->i])) {
        char *end = NULL;
        long v = strtol(a->s + a->i, &end, 0);
        a->i = (int)(end - a->s);
        return v;
    }

    if (isalpha((unsigned char)a->s[a->i]) || a->s[a->i] == '_') {
        int start = a->i;
        while (isalnum((unsigned char)a->s[a->i]) || a->s[a->i] == '_') a->i++;

        int len = a->i - start;
        char *name = xmalloc(len + 1);
        memcpy(name, a->s + start, len);
        name[len] = '\0';

        const char *val;

        /* a[expr] inside arithmetic, e.g. $(( total + counts[i] )) */
        if (a->s[a->i] == '[') {
            int depth = 0;
            int sstart = a->i + 1;
            int j = a->i;

            while (a->s[j]) {
                if (a->s[j] == '[') depth++;
                else if (a->s[j] == ']') { depth--; if (depth == 0) break; }
                j++;
            }

            if (a->s[j] != ']') { a->err = 1; free(name); return 0; }

            char *sb = xmalloc(j - sstart + 1);
            memcpy(sb, a->s + sstart, j - sstart);
            sb[j - sstart] = '\0';

            int err = 0;
            long idx = arith_eval(sb, &err);
            free(sb);

            a->i = j + 1;

            if (err) { a->err = 1; free(name); return 0; }
            if (idx < 0) idx = var_top_index(name) + 1 + idx;

            val = idx < 0 ? NULL : var_elem(name, (int)idx);
        } else {
            val = var_get(name);
        }

        free(name);

        if (!val || !*val) return 0;

        char *end = NULL;
        long v = strtol(val, &end, 0);
        if (end && *end) {
            /* the value is itself an expression */
            int err = 0;
            v = arith_eval(val, &err);
            if (err) a->err = 1;
        }
        return v;
    }

    a->err = 1;
    return 0;
}

static long ar_mul(Arith *a) {
    long v = ar_primary(a);

    for (;;) {
        ar_skip(a);
        char c = a->s[a->i];

        if (c == '*' ) { a->i++; v = v * ar_primary(a); continue; }
        if (c == '/') {
            a->i++;
            long d = ar_primary(a);
            if (d == 0) { a->err = 1; return 0; }
            v = v / d;
            continue;
        }
        if (c == '%') {
            a->i++;
            long d = ar_primary(a);
            if (d == 0) { a->err = 1; return 0; }
            v = v % d;
            continue;
        }
        break;
    }

    return v;
}

static long ar_add(Arith *a) {
    long v = ar_mul(a);

    for (;;) {
        ar_skip(a);
        char c = a->s[a->i];

        if (c == '+') { a->i++; v = v + ar_mul(a); continue; }
        if (c == '-') { a->i++; v = v - ar_mul(a); continue; }
        break;
    }

    return v;
}

static long ar_shift(Arith *a) {
    long v = ar_add(a);

    for (;;) {
        ar_skip(a);
        if (a->s[a->i] == '<' && a->s[a->i + 1] == '<') {
            a->i += 2; v = v << ar_add(a); continue;
        }
        if (a->s[a->i] == '>' && a->s[a->i + 1] == '>') {
            a->i += 2; v = v >> ar_add(a); continue;
        }
        break;
    }

    return v;
}

static long ar_rel(Arith *a) {
    long v = ar_shift(a);

    for (;;) {
        ar_skip(a);
        if (a->s[a->i] == '<' && a->s[a->i + 1] == '=') { a->i += 2; v = v <= ar_shift(a); continue; }
        if (a->s[a->i] == '>' && a->s[a->i + 1] == '=') { a->i += 2; v = v >= ar_shift(a); continue; }
        if (a->s[a->i] == '<' && a->s[a->i + 1] != '<') { a->i += 1; v = v < ar_shift(a); continue; }
        if (a->s[a->i] == '>' && a->s[a->i + 1] != '>') { a->i += 1; v = v > ar_shift(a); continue; }
        break;
    }

    return v;
}

static long ar_eq(Arith *a) {
    long v = ar_rel(a);

    for (;;) {
        if (ar_eat(a, "==")) { v = (v == ar_rel(a)); continue; }
        if (ar_eat(a, "!=")) { v = (v != ar_rel(a)); continue; }
        break;
    }

    return v;
}

static long ar_band(Arith *a) {
    long v = ar_eq(a);
    for (;;) {
        ar_skip(a);
        if (a->s[a->i] == '&' && a->s[a->i + 1] != '&') { a->i++; v = v & ar_eq(a); continue; }
        break;
    }
    return v;
}

static long ar_bxor(Arith *a) {
    long v = ar_band(a);
    for (;;) {
        ar_skip(a);
        if (a->s[a->i] == '^') { a->i++; v = v ^ ar_band(a); continue; }
        break;
    }
    return v;
}

static long ar_bor(Arith *a) {
    long v = ar_bxor(a);
    for (;;) {
        ar_skip(a);
        if (a->s[a->i] == '|' && a->s[a->i + 1] != '|') { a->i++; v = v | ar_bxor(a); continue; }
        break;
    }
    return v;
}

static long ar_and(Arith *a) {
    long v = ar_bor(a);
    for (;;) {
        if (ar_eat(a, "&&")) { long r = ar_bor(a); v = (v && r); continue; }
        break;
    }
    return v;
}

static long ar_or(Arith *a) {
    long v = ar_and(a);
    for (;;) {
        if (ar_eat(a, "||")) { long r = ar_and(a); v = (v || r); continue; }
        break;
    }
    return v;
}

static long arith_eval(const char *expr, int *err) {
    Arith a;
    a.s = expr;
    a.i = 0;
    a.err = 0;

    long v = ar_or(&a);
    ar_skip(&a);

    if (a.s[a.i] != '\0') a.err = 1;

    *err = a.err;
    return a.err ? 0 : v;
}

/* ------------------------------------------------------------------ */
/* Builtins                                                             */
/* ------------------------------------------------------------------ */

static int name_len_before_eq(const char *s) {
    if (!s) return 0;

    int i = 0;
    if (!(isalpha((unsigned char)s[i]) || s[i] == '_')) return 0;
    i++;

    while (s[i] && (isalnum((unsigned char)s[i]) || s[i] == '_')) i++;

    if (s[i] == '=') return i;
    return 0;
}

static int valid_name(const char *s) {
    if (!s || !s[0]) return 0;

    int i = 0;
    if (!(isalpha((unsigned char)s[i]) || s[i] == '_')) return 0;
    i++;

    while (s[i] && (isalnum((unsigned char)s[i]) || s[i] == '_')) i++;
    return s[i] == '\0';
}

static int builtin_cd(char **argv) {
    const char *dir = argv[1];

    if (!dir) dir = var_get("HOME");
    if (!dir) {
        fprintf(stderr, "cd: HOME not set\n");
        return 1;
    }

    if (strcmp(dir, "-") == 0) {
        dir = var_get("OLDPWD");
        if (!dir) {
            fprintf(stderr, "cd: OLDPWD not set\n");
            return 1;
        }
        printf("%s\n", dir);
    }

    char old[4096];
    if (!getcwd(old, sizeof(old))) old[0] = '\0';

    if (chdir(dir) != 0) {
        fprintf(stderr, "cd: %s: %s\n", dir, strerror(errno));
        return 1;
    }

    if (old[0]) { var_set("OLDPWD", old); var_export("OLDPWD"); }

    char cwd[4096];
    if (getcwd(cwd, sizeof(cwd))) { var_set("PWD", cwd); var_export("PWD"); }

    return 0;
}

static int builtin_pwd(char **argv) {
    (void)argv;

    char buf[4096];
    if (getcwd(buf, sizeof(buf))) {
        printf("%s\n", buf);
        return 0;
    }

    fprintf(stderr, "pwd: %s\n", strerror(errno));
    return 1;
}

static int builtin_echo(char **argv) {
    int i = 1;
    int newline = 1;

    if (argv[i] && strcmp(argv[i], "-n") == 0) {
        newline = 0;
        i++;
    }

    for (int j = i; argv[j]; j++) {
        if (j > i) putchar(' ');
        fputs(argv[j], stdout);
    }

    if (newline) putchar('\n');
    return 0;
}

static int builtin_export(char **argv) {
    if (!argv[1]) {
        for (Var *v = variables; v; v = v->next) {
            if (!v->exported) continue;
            if (v->isarray) {
                printf("export %s=(", v->name);
                for (int i = 0; i < v->nitems; i++) {
                    if (v->items[i]) printf("%s[%d]='%s'", i ? " " : "", i, v->items[i]);
                }
                printf(")\n");
            } else {
                printf("export %s='%s'\n", v->name,
                       (v->nitems > 0 && v->items[0]) ? v->items[0] : "");
            }
        }
        return 0;
    }

    for (int i = 1; argv[i]; i++) {
        int len = name_len_before_eq(argv[i]);

        if (len > 0) {
            char *name = xmalloc(len + 1);
            memcpy(name, argv[i], len);
            name[len] = '\0';

            var_set(name, argv[i] + len + 1);
            var_export(name);
            free(name);
        } else if (valid_name(argv[i])) {
            var_export(argv[i]);
        } else {
            fprintf(stderr, "export: `%s': not a valid identifier\n", argv[i]);
            return 1;
        }
    }

    return 0;
}

static int builtin_unset(char **argv) {
    for (int i = 1; argv[i]; i++) {
        /* unset a[1] removes that element and leaves the array sparse */
        char *br = strchr(argv[i], '[');
        if (br && argv[i][strlen(argv[i]) - 1] == ']') {
            size_t nlen = (size_t)(br - argv[i]);

            char *nm = xmalloc(nlen + 1);
            memcpy(nm, argv[i], nlen);
            nm[nlen] = '\0';

            if (!valid_name(nm)) {
                fprintf(stderr, "unset: `%s': not a valid identifier\n", argv[i]);
                free(nm);
                return 1;
            }

            size_t slen = strlen(br + 1) - 1;
            char *sb = xmalloc(slen + 1);
            memcpy(sb, br + 1, slen);
            sb[slen] = '\0';

            int idx = assign_index(nm, sb);
            if (idx >= 0) var_unset_index(nm, idx);

            free(sb);
            free(nm);
            continue;
        }

        if (valid_name(argv[i])) var_unset(argv[i]);
        else {
            fprintf(stderr, "unset: `%s': not a valid identifier\n", argv[i]);
            return 1;
        }
    }

    return 0;
}

static int test_file(const char *op, const char *path) {
    struct stat st;

    if (strcmp(op, "-f") == 0) return stat(path, &st) == 0 && S_ISREG(st.st_mode);
    if (strcmp(op, "-d") == 0) return stat(path, &st) == 0 && S_ISDIR(st.st_mode);
    if (strcmp(op, "-e") == 0) return access(path, F_OK) == 0;
    if (strcmp(op, "-r") == 0) return access(path, R_OK) == 0;
    if (strcmp(op, "-w") == 0) return access(path, W_OK) == 0;
    if (strcmp(op, "-x") == 0) return access(path, X_OK) == 0;
    if (strcmp(op, "-s") == 0) return stat(path, &st) == 0 && st.st_size > 0;
    if (strcmp(op, "-L") == 0 || strcmp(op, "-h") == 0) {
        return lstat(path, &st) == 0 && S_ISLNK(st.st_mode);
    }
    if (strcmp(op, "-p") == 0) return stat(path, &st) == 0 && S_ISFIFO(st.st_mode);
    if (strcmp(op, "-c") == 0) return stat(path, &st) == 0 && S_ISCHR(st.st_mode);
    if (strcmp(op, "-b") == 0) return stat(path, &st) == 0 && S_ISBLK(st.st_mode);

    return -1;
}

static int is_unary_file_op(const char *s) {
    static const char *ops[] = {
        "-f", "-d", "-e", "-r", "-w", "-x", "-s", "-L", "-h", "-p", "-c", "-b", NULL
    };
    for (int i = 0; ops[i]; i++) if (strcmp(s, ops[i]) == 0) return 1;
    return 0;
}

/*
 * test / [ - recursive descent so that !, -a and -o work.
 * Returns 1 for true, 0 for false, -1 for a usage error.
 */
typedef struct {
    char **a;
    int n;
    int i;
    int err;
} TestP;

static int test_or(TestP *t);

static int test_primary(TestP *t) {
    if (t->i >= t->n) { t->err = 1; return 0; }

    const char *w = t->a[t->i];

    if (strcmp(w, "!") == 0) {
        t->i++;
        return !test_primary(t);
    }

    if (strcmp(w, "(") == 0) {
        t->i++;
        int v = test_or(t);
        if (t->i >= t->n || strcmp(t->a[t->i], ")") != 0) { t->err = 1; return 0; }
        t->i++;
        return v;
    }

    /* binary operators need the operator to be the next word */
    if (t->i + 2 < t->n + 0 && t->i + 1 < t->n) {
        const char *op = t->a[t->i + 1];
        int isbin =
            strcmp(op, "=") == 0 || strcmp(op, "==") == 0 ||
            strcmp(op, "!=") == 0 || strcmp(op, "-eq") == 0 ||
            strcmp(op, "-ne") == 0 || strcmp(op, "-lt") == 0 ||
            strcmp(op, "-le") == 0 || strcmp(op, "-gt") == 0 ||
            strcmp(op, "-ge") == 0 || strcmp(op, "-nt") == 0 ||
            strcmp(op, "-ot") == 0;

        if (isbin && t->i + 2 < t->n) {
            const char *l = t->a[t->i];
            const char *r = t->a[t->i + 2];
            t->i += 3;

            if (strcmp(op, "=") == 0 || strcmp(op, "==") == 0) return strcmp(l, r) == 0;
            if (strcmp(op, "!=") == 0) return strcmp(l, r) != 0;

            if (strcmp(op, "-nt") == 0 || strcmp(op, "-ot") == 0) {
                struct stat sa, sb;
                if (stat(l, &sa) != 0 || stat(r, &sb) != 0) return 0;
                if (strcmp(op, "-nt") == 0) return sa.st_mtime > sb.st_mtime;
                return sa.st_mtime < sb.st_mtime;
            }

            char *le = NULL, *re = NULL;
            long li = strtol(l, &le, 10);
            long ri = strtol(r, &re, 10);

            if ((le && *le) || (re && *re)) {
                fprintf(stderr, "test: %s: integer expression expected\n",
                        (le && *le) ? l : r);
                t->err = 1;
                return 0;
            }

            if (strcmp(op, "-eq") == 0) return li == ri;
            if (strcmp(op, "-ne") == 0) return li != ri;
            if (strcmp(op, "-lt") == 0) return li < ri;
            if (strcmp(op, "-le") == 0) return li <= ri;
            if (strcmp(op, "-gt") == 0) return li > ri;
            return li >= ri;
        }
    }

    if (t->i + 1 < t->n) {
        if (strcmp(w, "-z") == 0) { int v = t->a[t->i + 1][0] == '\0'; t->i += 2; return v; }
        if (strcmp(w, "-n") == 0) { int v = t->a[t->i + 1][0] != '\0'; t->i += 2; return v; }
        if (strcmp(w, "-t") == 0) { int v = isatty(atoi(t->a[t->i + 1])); t->i += 2; return v; }

        if (is_unary_file_op(w)) {
            int v = test_file(w, t->a[t->i + 1]);
            t->i += 2;
            return v > 0;
        }
    }

    /* a bare word is true when it is non-empty */
    t->i++;
    return w[0] != '\0';
}

static int test_and(TestP *t) {
    int v = test_primary(t);

    while (t->i < t->n && strcmp(t->a[t->i], "-a") == 0) {
        t->i++;
        int r = test_primary(t);
        v = v && r;
    }

    return v;
}

static int test_or(TestP *t) {
    int v = test_and(t);

    while (t->i < t->n && strcmp(t->a[t->i], "-o") == 0) {
        t->i++;
        int r = test_and(t);
        v = v || r;
    }

    return v;
}

static int builtin_test(char **argv) {
    int argc = 0;
    while (argv[argc]) argc++;

    int end = argc;

    if (argv[0][0] == '[') {
        if (argc < 2 || strcmp(argv[argc - 1], "]") != 0) {
            fprintf(stderr, "[: missing ']'\n");
            return 2;
        }
        end = argc - 1;
    }

    TestP t;
    t.a = argv + 1;
    t.n = end - 1;
    t.i = 0;
    t.err = 0;

    if (t.n == 0) return 1;

    int v = test_or(&t);

    if (t.err || t.i != t.n) {
        if (!t.err) fprintf(stderr, "test: unexpected operand '%s'\n", t.a[t.i]);
        return 2;
    }

    return v ? 0 : 1;
}

static int builtin_read(char **argv) {
    int i = 1;
    int raw = 0;

    while (argv[i] && argv[i][0] == '-' && argv[i][1]) {
        if (strcmp(argv[i], "-r") == 0) { raw = 1; i++; continue; }
        break;
    }

    Str line;
    str_init(&line);

    int got = 0;
    char c;

    for (;;) {
        ssize_t r = read(0, &c, 1);
        if (r <= 0) break;

        got = 1;

        if (c == '\\' && !raw) {
            char nx;
            ssize_t r2 = read(0, &nx, 1);
            if (r2 <= 0) break;
            if (nx == '\n') continue;      /* line continuation */
            str_addch(&line, nx);
            continue;
        }

        if (c == '\n') break;
        str_addch(&line, c);
    }

    if (!got && line.len == 0) {
        /* still assign empty values so the caller sees no stale data */
        for (int j = i; argv[j]; j++) if (valid_name(argv[j])) var_set(argv[j], "");
        free(line.s);
        return 1;
    }

    const char *ifs = var_get("IFS");
    if (!ifs) ifs = " \t\n";

    int nvars = 0;
    for (int j = i; argv[j]; j++) nvars++;

    if (nvars == 0) {
        var_set("REPLY", line.s);
        free(line.s);
        return 0;
    }

    char *p = line.s;
    for (int j = 0; j < nvars; j++) {
        while (*p && strchr(ifs, *p) && (*p == ' ' || *p == '\t')) p++;

        if (j == nvars - 1) {
            char *endp = p + strlen(p);
            while (endp > p && strchr(ifs, endp[-1])) endp--;

            char save = *endp;
            *endp = '\0';
            var_set(argv[i + j], p);
            *endp = save;
            break;
        }

        char *start = p;
        while (*p && !strchr(ifs, *p)) p++;

        char save = *p;
        *p = '\0';
        var_set(argv[i + j], start);
        if (save) { *p = save; p++; }
    }

    free(line.s);
    return 0;
}

static int builtin_shift(char **argv) {
    int n = argv[1] ? atoi(argv[1]) : 1;
    if (n < 0) return 1;

    ArgsFrame *f = frames;
    if (n > f->argc - 1) return 1;

    for (int i = 1; i <= n; i++) free(f->argv[i]);

    for (int i = 1; i + n < f->argc; i++) f->argv[i] = f->argv[i + n];

    f->argc -= n;
    f->argv[f->argc] = NULL;
    return 0;
}

static int builtin_set(char **argv) {
    if (!argv[1]) {
        for (Var *v = variables; v; v = v->next) {
            if (v->isarray) {
                printf("%s=(", v->name);
                for (int i = 0; i < v->nitems; i++) {
                    if (v->items[i]) printf("%s[%d]=\"%s\"", i ? " " : "", i, v->items[i]);
                }
                printf(")\n");
            } else {
                printf("%s=%s\n", v->name,
                       (v->nitems > 0 && v->items[0]) ? v->items[0] : "");
            }
        }
        return 0;
    }

    int i = 1;

    while (argv[i] && (argv[i][0] == '-' || argv[i][0] == '+') && argv[i][1]) {
        int on = argv[i][0] == '-';

        if (strcmp(argv[i], "--") == 0) { i++; break; }

        for (int k = 1; argv[i][k]; k++) {
            switch (argv[i][k]) {
                case 'e': opt_errexit = on; break;
                case 'x': opt_xtrace = on; break;
                case 'u': opt_nounset = on; break;
                default:
                    fprintf(stderr, "set: -%c: unknown option\n", argv[i][k]);
                    return 2;
            }
        }

        i++;
    }

    if (!argv[i] && !(argv[1] && strcmp(argv[1], "--") == 0)) return 0;

    ArgsFrame *f = frames;

    char *zero = f->argv[0];
    for (int k = 1; k < f->argc; k++) free(f->argv[k]);

    int extra = 0;
    for (int k = i; argv[k]; k++) extra++;

    f->argv = xrealloc(f->argv, sizeof(char *) * (extra + 2));
    f->argv[0] = zero;

    for (int k = 0; k < extra; k++) f->argv[k + 1] = xstrdup(argv[i + k]);

    f->argc = extra + 1;
    f->argv[f->argc] = NULL;
    return 0;
}

static int printf_escape(const char *s, Str *out) {
    for (int i = 0; s[i]; i++) {
        if (s[i] != '\\') { str_addch(out, s[i]); continue; }

        i++;
        switch (s[i]) {
            case 'n': str_addch(out, '\n'); break;
            case 't': str_addch(out, '\t'); break;
            case 'r': str_addch(out, '\r'); break;
            case 'a': str_addch(out, '\a'); break;
            case 'b': str_addch(out, '\b'); break;
            case 'f': str_addch(out, '\f'); break;
            case 'v': str_addch(out, '\v'); break;
            case '\\': str_addch(out, '\\'); break;
            case '0': {
                int v = 0, k = 0;
                while (k < 3 && s[i + 1] >= '0' && s[i + 1] <= '7') {
                    v = v * 8 + (s[++i] - '0');
                    k++;
                }
                str_addch(out, (char)v);
                break;
            }
            case '\0': str_addch(out, '\\'); return 0;
            default: str_addch(out, '\\'); str_addch(out, s[i]); break;
        }
    }
    return 0;
}

static int builtin_printf(char **argv) {
    if (!argv[1]) {
        fprintf(stderr, "printf: usage: printf format [args]\n");
        return 2;
    }

    const char *fmt = argv[1];
    int argi = 2;
    int nargs = 0;
    while (argv[2 + nargs]) nargs++;

    Str out;
    str_init(&out);

    int pass = 0;

    do {
        int used = 0;

        for (int i = 0; fmt[i]; i++) {
            if (fmt[i] == '\\') {
                char two[3] = { fmt[i], fmt[i + 1], 0 };
                if (!fmt[i + 1]) { str_addch(&out, '\\'); break; }
                printf_escape(two, &out);
                i++;
                continue;
            }

            if (fmt[i] != '%') { str_addch(&out, fmt[i]); continue; }

            if (fmt[i + 1] == '%') { str_addch(&out, '%'); i++; continue; }

            /* copy the conversion spec */
            Str spec;
            str_init(&spec);
            str_addch(&spec, '%');
            i++;

            while (fmt[i] && strchr("-+ #0123456789.", fmt[i])) str_addch(&spec, fmt[i++]);

            char conv = fmt[i];
            if (!conv) { str_addstr(&out, spec.s); free(spec.s); break; }

            const char *arg = (argi < 2 + nargs) ? argv[argi] : "";
            if (argi < 2 + nargs) { argi++; used = 1; }

            char buf[512];

            if (conv == 's') {
                str_addch(&spec, 's');
                snprintf(buf, sizeof(buf), spec.s, arg);
                str_addstr(&out, buf);
            } else if (conv == 'd' || conv == 'i') {
                str_addstr(&spec, "ld");
                snprintf(buf, sizeof(buf), spec.s, strtol(arg, NULL, 10));
                str_addstr(&out, buf);
            } else if (conv == 'u' || conv == 'x' || conv == 'X' || conv == 'o') {
                char c2[3] = { 'l', conv, 0 };
                str_addstr(&spec, c2);
                snprintf(buf, sizeof(buf), spec.s, strtoul(arg, NULL, 10));
                str_addstr(&out, buf);
            } else if (conv == 'c') {
                str_addch(&out, arg[0]);
            } else {
                str_addstr(&out, spec.s);
                str_addch(&out, conv);
            }

            free(spec.s);
        }

        pass++;
        if (!used) break;
    } while (argi < 2 + nargs);

    fwrite(out.s, 1, out.len, stdout);
    free(out.s);
    return 0;
}

static int builtin_local(char **argv) {
    if (!frames || !frames->next) {
        fprintf(stderr, "local: can only be used in a function\n");
        return 1;
    }

    for (int i = 1; argv[i]; i++) {
        int len = name_len_before_eq(argv[i]);

        if (len > 0) {
            char *name = xmalloc(len + 1);
            memcpy(name, argv[i], len);
            name[len] = '\0';

            frame_make_local(name);
            var_set(name, argv[i] + len + 1);
            free(name);
        } else if (valid_name(argv[i])) {
            frame_make_local(argv[i]);
            var_set(argv[i], "");
        } else {
            fprintf(stderr, "local: `%s': not a valid identifier\n", argv[i]);
            return 1;
        }
    }

    return 0;
}

static char *read_all(FILE *fp);

static int builtin_source(char **argv) {
    if (!argv[1]) {
        fprintf(stderr, ".: filename argument required\n");
        return 2;
    }

    FILE *fp = fopen(argv[1], "r");
    if (!fp) {
        fprintf(stderr, ".: %s: %s\n", argv[1], strerror(errno));
        return 1;
    }

    char *src = read_all(fp);
    fclose(fp);

    int rc = run_program_string(src ? src : "");
    free(src);
    return rc;
}

static int builtin_eval(char **argv) {
    Str s;
    str_init(&s);

    for (int i = 1; argv[i]; i++) {
        if (i > 1) str_addch(&s, ' ');
        str_addstr(&s, argv[i]);
    }

    int rc = run_program_string(s.s);
    free(s.s);
    return rc;
}

static int builtin_wait(char **argv) {
    (void)argv;

    int st;
    while (waitpid(-1, &st, 0) > 0) { }

    return 0;
}

static int is_builtin(const char *s) {
    if (!s) return 0;

    static const char *names[] = {
        "cd", "pwd", "exit", "export", "unset", "echo", "true", "false",
        "test", "[", "break", "continue", "return", ":", "read", "shift",
        "set", "local", "printf", "eval", ".", "source", "wait", NULL
    };

    for (int i = 0; names[i]; i++) if (strcmp(s, names[i]) == 0) return 1;
    return 0;
}

static int run_builtin(char **argv) {
    if (!argv[0]) return 0;

    const char *c = argv[0];

    if (strcmp(c, ":") == 0) return 0;
    if (strcmp(c, "true") == 0) return 0;
    if (strcmp(c, "false") == 0) return 1;

    if (strcmp(c, "exit") == 0) {
        int st = argv[1] ? atoi(argv[1]) : last_status;
        shell_exit = 1;
        exit_requested = 1;
        last_status = st;
        return st;
    }

    if (strcmp(c, "cd") == 0) return builtin_cd(argv);
    if (strcmp(c, "pwd") == 0) return builtin_pwd(argv);
    if (strcmp(c, "echo") == 0) return builtin_echo(argv);
    if (strcmp(c, "export") == 0) return builtin_export(argv);
    if (strcmp(c, "unset") == 0) return builtin_unset(argv);
    if (strcmp(c, "test") == 0 || strcmp(c, "[") == 0) return builtin_test(argv);
    if (strcmp(c, "read") == 0) return builtin_read(argv);
    if (strcmp(c, "shift") == 0) return builtin_shift(argv);
    if (strcmp(c, "set") == 0) return builtin_set(argv);
    if (strcmp(c, "local") == 0) return builtin_local(argv);
    if (strcmp(c, "printf") == 0) return builtin_printf(argv);
    if (strcmp(c, "eval") == 0) return builtin_eval(argv);
    if (strcmp(c, ".") == 0 || strcmp(c, "source") == 0) return builtin_source(argv);
    if (strcmp(c, "wait") == 0) return builtin_wait(argv);

    if (strcmp(c, "break") == 0 || strcmp(c, "continue") == 0) {
        if (loop_depth == 0) {
            fprintf(stderr, "minishell: %s: only meaningful in a loop\n", c);
            return 0;
        }

        flow = (strcmp(c, "break") == 0) ? FLOW_BREAK : FLOW_CONTINUE;
        flow_count = argv[1] ? atoi(argv[1]) : 1;
        if (flow_count < 1) flow_count = 1;
        if (flow_count > loop_depth) flow_count = loop_depth;
        return 0;
    }

    if (strcmp(c, "return") == 0) {
        int st = argv[1] ? atoi(argv[1]) : last_status;
        return_status = st;
        last_status = st;
        flow = FLOW_RETURN;
        return st;
    }

    return 0;
}

/* ------------------------------------------------------------------ */
/* Redirection and execution                                            */
/* ------------------------------------------------------------------ */

typedef struct {
    char *name;
    char *sub;      /* raw subscript text, or NULL */
    int append;     /* += */
    char *value;    /* already expanded */
} Assign;

typedef VarSnap EnvBackup;

/*
 * Resolve a subscript to an index.  A negative index counts back from the
 * highest element that is set, which is what bash does for ${a[-1]}.
 * Returns -1 when the subscript is not usable.
 */
static int assign_index(const char *name, const char *sub) {
    char *text = expand_scalar(sub);

    int err = 0;
    long idx = arith_eval(text, &err);

    if (err) {
        fprintf(stderr, "minishell: %s: bad array subscript: %s\n", name, text);
        free(text);
        return -1;
    }

    free(text);

    if (idx < 0) idx = var_top_index(name) + 1 + idx;
    if (idx < 0) {
        fprintf(stderr, "minishell: %s: subscript out of range\n", name);
        return -1;
    }

    if (idx > MAX_ARRAY_INDEX) {
        fprintf(stderr, "minishell: %s: subscript %ld above the limit of %d\n",
                name, idx, MAX_ARRAY_INDEX);
        return -1;
    }

    return (int)idx;
}

static void assign_apply(Assign *a) {
    if (a->sub) {
        int idx = assign_index(a->name, a->sub);
        if (idx < 0) return;

        if (a->append) {
            const char *old = var_elem(a->name, idx);
            size_t n = strlen(old ? old : "") + strlen(a->value) + 1;

            char *joined = xmalloc(n);
            strcpy(joined, old ? old : "");
            strcat(joined, a->value);

            var_set_index(a->name, idx, joined);
            free(joined);
        } else {
            var_set_index(a->name, idx, a->value);
        }

        return;
    }

    if (a->append) var_append(a->name, a->value);
    else var_set(a->name, a->value);
}

/* NAME=(...) - each element word goes through full word expansion, so
   a=($(echo x y)) is two elements and a=(*.c) globs */
static void array_apply(ArrAssign *aa) {
    Args vals;
    args_init(&vals);

    for (int i = 0; i < aa->nwords; i++) expand_to_args(aa->words[i], &vals);

    if (aa->append) var_append_array(aa->name, vals.v, vals.n);
    else var_set_array(aa->name, vals.v, vals.n);

    args_free(&vals);
}

/* the prefix as written, left to right: plain assignments and NAME=(...)
   interleaved in source order */
static void assigns_apply_all(Assign *a, int n, ArrAssign *arrs, int narr) {
    for (int i = 0; i <= n; i++) {
        for (int k = 0; k < narr; k++) {
            if (arrs[k].order == i) array_apply(&arrs[k]);
        }
        if (i < n) assign_apply(&a[i]);
    }
}

static void apply_assigns_env(Assign *a, int n) {
    for (int i = 0; i < n; i++) {
        if (a[i].sub || a[i].append) { assign_apply(&a[i]); continue; }
        setenv(a[i].name, a[i].value, 1);
    }
}

static EnvBackup *save_and_set_assigns(Assign *a, int n,
                                       ArrAssign *arrs, int narr, int *nb_out) {
    int total = n + narr;
    EnvBackup *b = xmalloc(sizeof(EnvBackup) * (total ? total : 1));
    int nb = 0;

    for (int i = 0; i < n; i++) var_snapshot(a[i].name, &b[nb++]);

    /* only the ones in the assignment prefix are temporary; an array
       literal after `local` belongs to the command, not to the prefix */
    for (int i = 0; i < narr; i++) {
        if (arrs[i].order <= n) var_snapshot(arrs[i].name, &b[nb++]);
    }

    assigns_apply_all(a, n, arrs, narr);

    *nb_out = nb;
    return b;
}

static void restore_env_backups(EnvBackup *b, int nb) {
    if (!b) return;

    for (int i = nb - 1; i >= 0; i--) {
        var_restore(&b[i]);
        var_snap_free(&b[i]);
    }

    free(b);
}

static void free_assigns(Assign *a, int n) {
    if (!a) return;

    for (int i = 0; i < n; i++) {
        free(a[i].name);
        free(a[i].sub);
        free(a[i].value);
    }

    free(a);
}

typedef struct {
    int orig;
    int saved;
} FdBackup;

static void restore_redirs_current(FdBackup *b, int n) {
    if (!b) return;

    for (int i = n - 1; i >= 0; i--) {
        if (b[i].saved >= 0) {
            dup2(b[i].saved, b[i].orig);
            close(b[i].saved);
        } else {
            close(b[i].orig);
        }
    }

    free(b);
}

static int redir_flags(int type) {
    switch (type) {
        case T_LESS: return O_RDONLY;
        case T_DGREAT: return O_WRONLY | O_CREAT | O_APPEND;
        default: return O_WRONLY | O_CREAT | O_TRUNC;
    }
}

/* Feed a heredoc body to FD.  Returns 0 on success. */
static int heredoc_fd(const char *body, int target) {
    int fds[2];
    if (pipe(fds) < 0) return -1;

    size_t len = strlen(body);

    if (len < 32768) {
        ssize_t off = 0;
        while ((size_t)off < len) {
            ssize_t w = write(fds[1], body + off, len - off);
            if (w <= 0) break;
            off += w;
        }
        close(fds[1]);
    } else {
        pid_t pid = fork();
        if (pid < 0) { close(fds[0]); close(fds[1]); return -1; }

        if (pid == 0) {
            close(fds[0]);
            signal(SIGPIPE, SIG_DFL);

            size_t off = 0;
            while (off < len) {
                ssize_t w = write(fds[1], body + off, len - off);
                if (w <= 0) break;
                off += (size_t)w;
            }

            close(fds[1]);
            _exit(0);
        }

        close(fds[1]);
    }

    if (dup2(fds[0], target) < 0) { close(fds[0]); return -1; }
    close(fds[0]);
    return 0;
}

/*
 * open one redirection onto its target descriptor.
 * TEXT is the already-expanded filename, fd number, or heredoc body.
 */
static int open_redir(Redir *r, const char *text) {
    if (r->type == T_DLESS) return heredoc_fd(text, r->fd);

    if (r->type == T_GREATAND || r->type == T_LESSAND) {
        if (strcmp(text, "-") == 0) {
            close(r->fd);
            return 0;
        }

        char *end = NULL;
        long src = strtol(text, &end, 10);

        if (!end || *end) {
            fprintf(stderr, "minishell: %s: bad file descriptor\n", text);
            return -1;
        }

        if (dup2((int)src, r->fd) < 0) {
            fprintf(stderr, "minishell: %d: %s\n", (int)src, strerror(errno));
            return -1;
        }

        return 0;
    }

    int fd = open(text, redir_flags(r->type), 0644);
    if (fd < 0) {
        fprintf(stderr, "minishell: %s: %s\n", text, strerror(errno));
        return -1;
    }

    if (dup2(fd, r->fd) < 0) {
        fprintf(stderr, "minishell: dup2: %s\n", strerror(errno));
        close(fd);
        return -1;
    }

    if (fd != r->fd) close(fd);
    return 0;
}

/* expand each redirection target; heredoc bodies expand differently */
static char **expand_redir_files(Redir *rs, int n) {
    char **files = xmalloc(sizeof(char *) * (n ? n : 1));

    for (int i = 0; i < n; i++) {
        if (rs[i].type == T_DLESS) {
            files[i] = rs[i].flags ? xstrdup(rs[i].file)
                                   : expand_heredoc(rs[i].file);
        } else {
            files[i] = expand_scalar(rs[i].file);
        }
    }

    return files;
}

static void free_redir_files(char **files, int n) {
    for (int i = 0; i < n; i++) free(files[i]);
    free(files);
}

static int setup_redirs_files(Redir *rs, int n, char **files) {
    for (int i = 0; i < n; i++) {
        if (open_redir(&rs[i], files[i]) < 0) return 0;
    }
    return 1;
}

static int apply_redirs_current_files(Redir *rs, int nredir, char **files,
                                      FdBackup **backups, int *nbackup) {
    *backups = NULL;
    *nbackup = 0;

    if (nredir == 0) return 0;

    FdBackup *b = xmalloc(sizeof(FdBackup) * nredir);
    int nb = 0;

    for (int i = 0; i < nredir; i++) {
        Redir *r = &rs[i];

        int already = 0;
        for (int j = 0; j < nb; j++) {
            if (b[j].orig == r->fd) { already = 1; break; }
        }

        if (!already) {
            int saved = dup(r->fd);        /* -1 when the fd was not open */
            b[nb].orig = r->fd;
            b[nb].saved = saved;
            nb++;
        }

        if (open_redir(r, files[i]) < 0) {
            restore_redirs_current(b, nb);
            return -1;
        }
    }

    *backups = b;
    *nbackup = nb;
    return 0;
}

static int status_from_wait(int st) {
    if (WIFEXITED(st)) return WEXITSTATUS(st);
    if (WIFSIGNALED(st)) return 128 + WTERMSIG(st);
    return 1;
}

static int wait_for_pid(pid_t pid) {
    int st;

    while (waitpid(pid, &st, 0) < 0) {
        if (errno != EINTR) return 1;
    }

    return status_from_wait(st);
}

static void reap_jobs(void) {
    int st;
    while (waitpid(-1, &st, WNOHANG) > 0) { }
}

/* once something has asked the shell to stop, its status is final */
static void set_status(int s) {
    if (!exit_requested) last_status = s;
}

static int execute_node(Node *n);
static int execute_list(List *l);
static int execute_andor(Andor *a);
static int execute_pipeline(Pipeline *pl);
static int execute_simple(Simple *s);
static int execute_if(Node *n);
static int execute_while(Node *n);
static int execute_for(Node *n);
static int execute_case(Node *n);
static int execute_subshell(List *l);

static void xtrace(char **argv) {
    const char *ps4 = var_get("PS4");
    fprintf(stderr, "%s", ps4 ? ps4 : "+ ");

    for (int i = 0; argv[i]; i++) {
        if (i) fputc(' ', stderr);
        fputs(argv[i], stderr);
    }

    fputc('\n', stderr);
}

static int execute_simple(Simple *s) {
    int nassign = 0;
    long subs_before = cmdsub_count;

    while (s->words[nassign] && is_assign_word(s->words[nassign])) nassign++;

    Assign *assigns = xmalloc(sizeof(Assign) * (nassign ? nassign : 1));

    for (int i = 0; i < nassign; i++) {
        const char *value = NULL;

        split_assign(s->words[i], &assigns[i].name, &assigns[i].sub,
                     &assigns[i].append, &value);

        assigns[i].value = expand_scalar(value);
    }

    Args args;
    args_init(&args);

    for (int i = nassign; s->words[i]; i++) expand_to_args(s->words[i], &args);

    char **files = expand_redir_files(s->redirs, s->nredir);

    int status = 0;
    EnvBackup *eb = NULL;
    FdBackup *fb = NULL;
    int neb = 0;
    int nfb = 0;
    pid_t pid = 0;

    if (shell_exit) { status = last_status; goto cleanup; }

    if (opt_xtrace && args.n > 0) xtrace(args.v);

    if (args.n == 0) {
        assigns_apply_all(assigns, nassign, s->arrs, s->narr);

        /*
         * POSIX: a command with no command name but with a command
         * substitution exits with the status of the last substitution,
         * so X=$(false) leaves $? at 1.
         */
        if (cmdsub_count > subs_before) status = last_status;

        if (s->nredir > 0) {
            if (apply_redirs_current_files(s->redirs, s->nredir, files, &fb, &nfb) == 0) {
                restore_redirs_current(fb, nfb);
            } else {
                status = 1;
            }
        }

        goto cleanup;
    }

    FuncDef *f = find_function(args.v[0]);
    if (f) {
        int nprefix_arr = 0;
        for (int k = 0; k < s->narr; k++) if (s->arrs[k].order <= nassign) nprefix_arr++;

        if (nassign > 0 || nprefix_arr > 0)
            eb = save_and_set_assigns(assigns, nassign, s->arrs, s->narr, &neb);

        if (apply_redirs_current_files(s->redirs, s->nredir, files, &fb, &nfb) < 0) {
            if (eb) restore_env_backups(eb, neb);
            status = 1;
            goto cleanup;
        }

        if (func_depth >= MAX_FUNC_DEPTH) {
            fprintf(stderr, "minishell: %s: recursion too deep (limit %d)\n",
                    args.v[0], MAX_FUNC_DEPTH);
            status = 1;
            last_status = 1;

            if (fb) restore_redirs_current(fb, nfb);
            if (eb) restore_env_backups(eb, neb);
            goto cleanup;
        }

        int saved_loops = loop_depth;
        loop_depth = 0;

        func_depth++;
        push_frame(args.v, args.n);
        status = execute_node(f->body);
        pop_frame();
        func_depth--;

        loop_depth = saved_loops;

        if (flow == FLOW_RETURN) {
            flow = FLOW_NORMAL;
            status = return_status;
        }

        if (fb) restore_redirs_current(fb, nfb);
        if (eb) restore_env_backups(eb, neb);

        goto cleanup;
    }

    if (is_builtin(args.v[0])) {
        int nprefix_arr = 0;
        for (int k = 0; k < s->narr; k++) if (s->arrs[k].order <= nassign) nprefix_arr++;

        if (nassign > 0 || nprefix_arr > 0)
            eb = save_and_set_assigns(assigns, nassign, s->arrs, s->narr, &neb);

        if (apply_redirs_current_files(s->redirs, s->nredir, files, &fb, &nfb) < 0) {
            if (eb) restore_env_backups(eb, neb);
            status = 1;
            goto cleanup;
        }

        /*
         * local a=(1 2) - the array literal is not part of the assignment
         * prefix, so make the name local first and then assign it.
         */
        if (is_decl_word(args.v[0])) {
            for (int k = 0; k < s->narr; k++) {
                if (s->arrs[k].order == 0) continue;
                frame_make_local(s->arrs[k].name);
                array_apply(&s->arrs[k]);
            }
        }

        status = run_builtin(args.v);

        if (fb) restore_redirs_current(fb, nfb);
        if (eb) restore_env_backups(eb, neb);

        goto cleanup;
    }

    pid = fork();
    if (pid < 0) {
        perror("fork");
        status = 1;
    } else if (pid == 0) {
        signal(SIGINT, SIG_DFL);
        signal(SIGQUIT, SIG_DFL);

        apply_assigns_env(assigns, nassign);
        for (int i = 0; i < s->narr; i++) array_apply(&s->arrs[i]);

        if (!setup_redirs_files(s->redirs, s->nredir, files)) _exit(1);

        execvp(args.v[0], args.v);

        int code = (errno == ENOENT) ? 127 : 126;
        fprintf(stderr, "minishell: %s: %s\n", args.v[0], strerror(errno));
        fflush(NULL);
        _exit(code);
    } else {
        status = wait_for_pid(pid);
    }

cleanup:
    free_assigns(assigns, nassign);
    args_free(&args);
    free_redir_files(files, s->nredir);

    return status;
}

static int execute_redir(Node *n) {
    RedirNode *rn = n->data;

    char **files = expand_redir_files(rn->redirs, rn->nredir);

    FdBackup *fb = NULL;
    int nfb = 0;
    int status;

    if (apply_redirs_current_files(rn->redirs, rn->nredir, files,
                                   &fb, &nfb) < 0) {
        free_redir_files(files, rn->nredir);
        return 1;
    }

    status = execute_node(rn->body);

    restore_redirs_current(fb, nfb);
    free_redir_files(files, rn->nredir);

    return status;
}

static int execute_pipeline(Pipeline *pl) {
    if (!pl || pl->n == 0) return 0;

    int status;

    if (pl->n == 1) {
        status = execute_node(pl->cmds[0]);
        if (pl->bang) {
            status = status == 0 ? 1 : 0;
            flow = flow;      /* a negated pipeline still honours break/return */
        }
        return status;
    }

    pid_t *pids = xmalloc(sizeof(pid_t) * pl->n);
    int in_fd = 0;

    for (int i = 0; i < pl->n; i++) {
        int has_pipe = (i < pl->n - 1);
        int pipefd[2];

        if (has_pipe && pipe(pipefd) < 0) {
            perror("pipe");
            free(pids);
            return 1;
        }

        pid_t pid = fork();
        if (pid < 0) {
            perror("fork");
            if (has_pipe) { close(pipefd[0]); close(pipefd[1]); }
            free(pids);
            return 1;
        }

        if (pid == 0) {
            signal(SIGINT, SIG_DFL);
            signal(SIGQUIT, SIG_DFL);

            if (in_fd != 0) {
                if (dup2(in_fd, 0) < 0) _exit(1);
                close(in_fd);
            }

            if (has_pipe) {
                if (dup2(pipefd[1], 1) < 0) _exit(1);
                close(pipefd[0]);
                close(pipefd[1]);
            }

            int st = execute_node(pl->cmds[i]);
            fflush(NULL);
            _exit(st);
        }

        if (in_fd != 0) close(in_fd);

        if (has_pipe) {
            close(pipefd[1]);
            in_fd = pipefd[0];
        } else {
            in_fd = 0;
        }

        pids[i] = pid;
    }

    status = 0;
    for (int i = 0; i < pl->n; i++) {
        int st = wait_for_pid(pids[i]);
        if (i == pl->n - 1) status = st;
    }

    free(pids);

    if (pl->bang) status = status == 0 ? 1 : 0;
    return status;
}

static int execute_andor(Andor *a) {
    if (!a || a->n == 0) return 0;

    int status;

    if (a->n > 1) noerrexit++;
    status = execute_pipeline(a->pipes[0]);
    if (a->n > 1) noerrexit--;

    set_status(status);

    for (int i = 1; i < a->n; i++) {
        if (shell_exit || flow != FLOW_NORMAL) break;

        int op = a->ops[i];

        if ((op == T_AND && status == 0) || (op == T_OR && status != 0)) {
            if (i < a->n - 1) noerrexit++;
            status = execute_pipeline(a->pipes[i]);
            if (i < a->n - 1) noerrexit--;

            set_status(status);
        }
    }

    return status;
}

static int execute_list(List *l) {
    int status = 0;
    if (!l) return 0;

    for (int i = 0; i < l->n; i++) {
        if (shell_exit || flow != FLOW_NORMAL) break;

        reap_jobs();

        if (l->items[i].bg) {
            pid_t pid = fork();

            if (pid < 0) {
                perror("fork");
                status = 1;
                set_status(1);
            } else if (pid == 0) {
                signal(SIGINT, SIG_DFL);
                signal(SIGQUIT, SIG_DFL);

                int st = execute_andor(l->items[i].andor);
                fflush(NULL);
                _exit(st);
            } else {
                last_bg_pid = pid;
                status = 0;
                set_status(0);
            }
        } else {
            status = execute_andor(l->items[i].andor);
            set_status(status);

            if (opt_errexit && noerrexit == 0 && status != 0 &&
                flow == FLOW_NORMAL) {
                shell_exit = 1;
                exit_requested = 1;
                break;
            }
        }
    }

    return status;
}

static int execute_subshell(List *l) {
    pid_t pid = fork();

    if (pid < 0) {
        perror("fork");
        return 1;
    }

    if (pid == 0) {
        signal(SIGINT, SIG_DFL);
        signal(SIGQUIT, SIG_DFL);

        int st = execute_list(l);
        fflush(NULL);
        _exit(shell_exit ? last_status : st);
    }

    return wait_for_pid(pid);
}

static int execute_if(Node *n) {
    Node *cur = n;
    int status = 0;
    int executed = 0;

    while (cur && cur->type == N_IF) {
        If *i = cur->data;

        if (shell_exit || flow != FLOW_NORMAL) break;

        noerrexit++;
        int cs = execute_list(i->cond);
        noerrexit--;

        if (shell_exit || flow != FLOW_NORMAL) break;

        if (cs == 0) {
            status = execute_list(i->then);
            executed = 1;
            break;
        }

        cur = i->else_node;
    }

    if (!executed && cur && cur->type == N_LIST &&
        !shell_exit && flow == FLOW_NORMAL) {
        status = execute_list((List *)cur->data);
        executed = 1;
    }

    if (!executed) status = 0;
    return status;
}

/* returns 1 when the enclosing loop should stop */
static int loop_flow(void) {
    if (flow == FLOW_BREAK) {
        if (--flow_count <= 0) flow = FLOW_NORMAL;
        return 1;
    }

    if (flow == FLOW_CONTINUE) {
        if (--flow_count <= 0) { flow = FLOW_NORMAL; return 0; }
        return 1;
    }

    if (flow == FLOW_RETURN || shell_exit) return 1;
    return 0;
}

static int execute_while(Node *n) {
    While *w = n->data;
    int status = 0;

    loop_depth++;

    while (!shell_exit && flow == FLOW_NORMAL) {
        noerrexit++;
        int cs = execute_list(w->cond);
        noerrexit--;

        if (shell_exit || flow != FLOW_NORMAL) break;

        if (w->until ? (cs == 0) : (cs != 0)) break;

        status = execute_list(w->body);

        if (flow != FLOW_NORMAL || shell_exit) {
            if (loop_flow()) break;
        }
    }

    loop_depth--;
    return status;
}

static int execute_for(Node *n) {
    For *f = n->data;

    Args vals;
    args_init(&vals);

    if (f->use_args) {
        char **av = cur_argv();
        int ac = cur_argc();
        for (int i = 1; i < ac; i++) args_add_copy(&vals, av[i]);
    } else {
        for (int i = 0; i < f->nwords; i++) expand_to_args(f->words[i], &vals);
    }

    int status = 0;
    loop_depth++;

    for (int i = 0; i < vals.n; i++) {
        if (shell_exit || flow != FLOW_NORMAL) break;

        var_set(f->var, vals.v[i]);
        status = execute_list(f->body);

        if (flow != FLOW_NORMAL || shell_exit) {
            if (loop_flow()) break;
        }
    }

    loop_depth--;
    args_free(&vals);
    return status;
}

static int execute_case(Node *n) {
    Case *c = n->data;

    char *word = expand_scalar(c->word);
    int status = 0;

    for (int i = 0; i < c->n; i++) {
        for (int j = 0; j < c->items[i].npat; j++) {
            char *pat = expand_pattern(c->items[i].pats[j]);
            int hit = glob_match(pat, word);
            free(pat);

            if (hit) {
                status = execute_list(c->items[i].body);
                free(word);
                return status;
            }
        }
    }

    free(word);
    return status;
}

static int execute_node(Node *n) {
    if (!n) return 0;

    switch (n->type) {
        case N_SIMPLE: return execute_simple((Simple *)n->data);
        case N_LIST: return execute_list((List *)n->data);
        case N_SUBSHELL: return execute_subshell((List *)n->data);
        case N_IF: return execute_if(n);
        case N_WHILE: return execute_while(n);
        case N_FOR: return execute_for(n);
        case N_CASE: return execute_case(n);
        case N_REDIR: return execute_redir(n);

        case N_FUNC: {
            FuncDef *f = n->data;
            add_function(f->name, f->body);
            return 0;
        }
    }

    return 0;
}

/* ------------------------------------------------------------------ */
/* Program driver                                                       */
/* ------------------------------------------------------------------ */

/*
 * A function installed by this program text borrows its body from this
 * AST, so any text that defines a function is retained until exit and
 * everything else is freed immediately.  Freeing unconditionally would
 * leave the function table pointing at freed nodes.
 */
typedef struct Retained {
    Node *node;
    List *list;
    struct Retained *next;
} Retained;

static Retained *retained = NULL;

static void retain_list(List *l) {
    Retained *r = xmalloc(sizeof(*r));
    r->node = NULL;
    r->list = l;
    r->next = retained;
    retained = r;
}

static void retained_free_all(void) {
    Retained *r = retained;
    while (r) {
        Retained *nx = r->next;
        free_list_tree(r->list);
        free(r);
        r = nx;
    }
    retained = NULL;
}

static int run_program_string(const char *s) {
    int ntok = 0;
    int incomplete = 0;
    Token *toks = lex_program(s, &ntok, &incomplete);

    Parser p;
    p.t = toks;
    p.n = ntok;
    p.pos = 0;
    p.failed = 0;
    p.at_end = 0;
    p.quiet = 0;

    List *top = parse_list(&p, NULL, 0, NULL, 0);

    int rc = 0;

    if (incomplete) {
        /* unterminated quote, ${, $( or heredoc - refuse to guess */
        fprintf(stderr, "minishell: syntax error: unexpected end of input\n");
        free_list_tree(top);
        last_status = 2;
        rc = 2;
    } else if (!top) {
        last_status = 2;
        rc = 2;
    } else if (p.pos < p.n - 1 && peek_type(&p) != T_END) {
        parse_error(&p, "unexpected token");
        free_list_tree(top);
        last_status = 2;
        rc = 2;
    } else {
        int before = func_installs;

        rc = execute_list(top);

        /*
         * When something asked the shell to stop - exit, set -e, set -u,
         * ${x:?} - the status it stopped with is the shell's status.
         * Overwriting it here lost the failure and the script "succeeded".
         */
        if (exit_requested) rc = last_status;
        else last_status = rc;

        if (func_installs > before) retain_list(top);
        else free_list_tree(top);
    }

    if (flow != FLOW_NORMAL) flow = FLOW_NORMAL;

    free_tokens(toks, ntok);
    return rc;
}

/* is this text a complete command, or should the prompt ask for more? */
static int input_incomplete(const char *s) {
    int ntok = 0;
    int incomplete = 0;
    Token *toks = lex_program(s, &ntok, &incomplete);

    if (incomplete) { free_tokens(toks, ntok); return 1; }

    Parser p;
    p.t = toks;
    p.n = ntok;
    p.pos = 0;
    p.failed = 0;
    p.at_end = 0;
    p.quiet = 1;

    List *top = parse_list(&p, NULL, 0, NULL, 0);
    int more = (!top && p.at_end);

    free_list_tree(top);
    free_tokens(toks, ntok);
    return more;
}

static char *read_all(FILE *fp) {
    size_t cap = 8192;
    size_t len = 0;
    char *buf = xmalloc(cap);

    for (;;) {
        if (len + 4096 + 1 > cap) {
            cap *= 2;
            buf = xrealloc(buf, cap);
        }

        size_t r = fread(buf + len, 1, 4096, fp);
        if (r == 0) break;

        len += r;
    }

    buf[len] = '\0';
    return buf;
}

static void run_interactive(void) {
    char *line = NULL;
    size_t cap = 0;
    ssize_t len;

    signal(SIGINT, SIG_IGN);
    signal(SIGQUIT, SIG_IGN);

    Str acc;
    str_init(&acc);

    while (!shell_exit) {
        const char *ps = acc.len ? var_get("PS2") : var_get("PS1");
        if (!ps) ps = acc.len ? "> " : "minishell$ ";

        fprintf(stderr, "%s", ps);
        fflush(stderr);

        len = getline(&line, &cap, stdin);
        if (len == -1) break;

        if (len > 0 && line[len - 1] == '\n') line[--len] = '\0';
        if (len > 0 && line[len - 1] == '\r') line[--len] = '\0';

        if (acc.len == 0 && len == 0) continue;

        if (acc.len) str_addch(&acc, '\n');
        str_addstr(&acc, line);

        /* keep reading while the command is unfinished */
        if (input_incomplete(acc.s)) continue;

        reap_jobs();
        run_program_string(acc.s);
        str_clear(&acc);
    }

    if (acc.len) run_program_string(acc.s);

    free(acc.s);
    fprintf(stderr, "\n");
    free(line);
}

static void usage(void) {
    fprintf(stderr,
            "usage: minishell [-c command] [-x] [-e] [-u] [file [args...]]\n");
}

static void shell_cleanup(void) {
    while (frames) pop_frame();
    retained_free_all();
    functions_free_all();
    vars_free_all();
}

int main(int argc, char **argv) {
    setvbuf(stdout, NULL, _IONBF, 0);
    setvbuf(stderr, NULL, _IONBF, 0);

    /* seed the variable table from the environment lazily via var_get */
    char *base[2];
    base[0] = argv[0];
    base[1] = NULL;
    push_frame(base, 1);

    const char *cflag = NULL;
    int i = 1;

    for (; i < argc; i++) {
        if (argv[i][0] != '-' || argv[i][1] == '\0') break;

        if (strcmp(argv[i], "--") == 0) { i++; break; }

        if (strcmp(argv[i], "-c") == 0) {
            if (i + 1 >= argc) { usage(); shell_cleanup(); return 2; }
            cflag = argv[i + 1];
            i += 2;
            break;
        }

        if (strcmp(argv[i], "-s") == 0) { i++; break; }

        int bad = 0;
        for (int k = 1; argv[i][k]; k++) {
            switch (argv[i][k]) {
                case 'e': opt_errexit = 1; break;
                case 'x': opt_xtrace = 1; break;
                case 'u': opt_nounset = 1; break;
                default: bad = 1; break;
            }
        }

        if (bad) { usage(); shell_cleanup(); return 2; }
    }

    if (cflag) {
        /* minishell -c 'cmd' [$0 [$1 ...]] */
        Args pos;
        args_init(&pos);
        args_add_copy(&pos, i < argc ? argv[i] : argv[0]);
        for (int k = (i < argc ? i + 1 : argc); k < argc; k++) {
            args_add_copy(&pos, argv[k]);
        }

        pop_frame();
        push_frame(pos.v, pos.n);
        args_free(&pos);

        run_program_string(cflag);

        int rc = last_status;
        shell_cleanup();
        return rc;
    }

    if (i < argc) {
        FILE *fp = fopen(argv[i], "r");
        if (!fp) {
            fprintf(stderr, "minishell: %s: %s\n", argv[i], strerror(errno));
            shell_cleanup();
            return 127;
        }

        Args pos;
        args_init(&pos);
        for (int k = i; k < argc; k++) args_add_copy(&pos, argv[k]);

        pop_frame();
        push_frame(pos.v, pos.n);
        args_free(&pos);

        char *src = read_all(fp);
        fclose(fp);

        run_program_string(src ? src : "");
        free(src);

        int rc = last_status;
        shell_cleanup();
        return rc;
    }

    if (isatty(fileno(stdin))) {
        interactive = 1;
        run_interactive();

        int rc = last_status;
        shell_cleanup();
        return rc;
    }

    char *src = read_all(stdin);
    run_program_string(src ? src : "");
    free(src);

    int rc = last_status;
    shell_cleanup();
    return rc;
}
