#define _POSIX_C_SOURCE 200809L

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>
#include <ctype.h>
#include <signal.h>
#include <sys/wait.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <errno.h>

static int last_status = 0;
static int shell_exit = 0;
static char **g_argv;
static int g_argc;

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

static void str_addint(Str *st, long v) {
    char buf[32];
    snprintf(buf, sizeof(buf), "%ld", v);
    str_addstr(st, buf);
}

static int expand_var(const char *s, int i, Str *out) {
    i++; /* skip '$' */

    if (s[i] == '?') {
        str_addint(out, last_status);
        return i + 1;
    }

    if (s[i] == '$') {
        str_addint(out, (long)getpid());
        return i + 1;
    }

    if (s[i] == '#') {
        str_addint(out, g_argc > 0 ? g_argc - 1 : 0);
        return i + 1;
    }

    if (s[i] == '0') {
        str_addstr(out, g_argc > 0 ? g_argv[0] : "minishell");
        return i + 1;
    }

    if (s[i] == '{') {
        i++;
        int start = i;
        while (s[i] && (isalnum((unsigned char)s[i]) || s[i] == '_')) i++;
        int len = i - start;

        char *name = xmalloc(len + 1);
        memcpy(name, s + start, len);
        name[len] = '\0';

        const char *val = NULL;
        int all_digits = len > 0;
        for (int k = 0; k < len; k++) {
            if (!isdigit((unsigned char)name[k])) {
                all_digits = 0;
                break;
            }
        }

        if (all_digits) {
            int num = atoi(name);
            if (num < g_argc) val = g_argv[num];
        } else {
            val = getenv(name);
        }

        if (s[i] == ':' && s[i + 1] == '-') {
            i += 2;
            int dstart = i;
            while (s[i] && s[i] != '}') i++;
            int dlen = i - dstart;
            if (s[i] == '}') i++;

            if (!val || !*val) str_addn(out, s + dstart, dlen);
            else str_addstr(out, val);
        } else {
            while (s[i] && s[i] != '}') i++;
            if (s[i] == '}') i++;
            if (val) str_addstr(out, val);
        }

        free(name);
        return i;
    }

    if (isdigit((unsigned char)s[i])) {
        int n = 0;
        while (isdigit((unsigned char)s[i])) {
            n = n * 10 + (s[i] - '0');
            i++;
        }
        if (n < g_argc) str_addstr(out, g_argv[n]);
        return i;
    }

    if (isalpha((unsigned char)s[i]) || s[i] == '_') {
        int start = i;
        while (s[i] && (isalnum((unsigned char)s[i]) || s[i] == '_')) i++;
        int len = i - start;

        char *name = xmalloc(len + 1);
        memcpy(name, s + start, len);
        name[len] = '\0';

        const char *val = getenv(name);
        if (val) str_addstr(out, val);

        free(name);
        return i;
    }

    str_addch(out, '$');
    return i;
}

typedef enum {
    T_WORD,
    T_IO_NUMBER,
    T_PIPE,
    T_AND,
    T_OR,
    T_SEMI,
    T_AMP,
    T_LESS,
    T_GREAT,
    T_DGREAT,
    T_END
} TType;

typedef struct {
    TType type;
    char *text;
    int fd;
} Token;

typedef struct {
    Token *v;
    int n;
    int cap;
} TokVec;

static void tv_add(TokVec *tv, TType type, const char *text, int fd) {
    if (tv->n == tv->cap) {
        tv->cap = tv->cap ? tv->cap * 2 : 32;
        tv->v = xrealloc(tv->v, tv->cap * sizeof(Token));
    }
    tv->v[tv->n].type = type;
    tv->v[tv->n].text = text ? xstrdup(text) : NULL;
    tv->v[tv->n].fd = fd;
    tv->n++;
}

static void add_split_words(TokVec *tv, Str *st, int had_quote) {
    if (had_quote) {
        tv_add(tv, T_WORD, st->s, 0);
        return;
    }

    char *p = st->s;
    while (*p) {
        while (isspace((unsigned char)*p)) p++;
        if (!*p) break;

        char *start = p;
        while (*p && !isspace((unsigned char)*p)) p++;

        char c = *p;
        *p = '\0';
        tv_add(tv, T_WORD, start, 0);
        if (!c) break;
        *p = c;
        p++;
    }
}

static void lex_word(TokVec *tv, const char *s, int *ip) {
    int i = *ip;
    Str st;
    str_init(&st);
    int had_quote = 0;

    while (s[i]) {
        if (s[i] == '\\') {
            had_quote = 1;
            if (s[i + 1]) {
                str_addch(&st, s[i + 1]);
                i += 2;
            } else {
                i++;
                break;
            }
            continue;
        }

        if (s[i] == '\'') {
            had_quote = 1;
            i++;
            while (s[i] && s[i] != '\'') str_addch(&st, s[i++]);
            if (s[i] == '\'') i++;
            continue;
        }

        if (s[i] == '"') {
            had_quote = 1;
            i++;
            while (s[i] && s[i] != '"') {
                if (s[i] == '\\' &&
                    (s[i + 1] == '$' || s[i + 1] == 96 ||
                     s[i + 1] == '"' || s[i + 1] == '\\')) {
                    str_addch(&st, s[i + 1]);
                    i += 2;
                } else if (s[i] == '$') {
                    i = expand_var(s, i, &st);
                } else {
                    str_addch(&st, s[i++]);
                }
            }
            if (s[i] == '"') i++;
            continue;
        }

        if (s[i] == '$') {
            i = expand_var(s, i, &st);
            continue;
        }

        if (isspace((unsigned char)s[i]) ||
            s[i] == '|' || s[i] == '&' || s[i] == ';' ||
            s[i] == '<' || s[i] == '>') {
            break;
        }

        str_addch(&st, s[i++]);
    }

    *ip = i;
    if (st.len > 0 || had_quote) add_split_words(tv, &st, had_quote);
    free(st.s);
}

static Token *lex_line(const char *s, int *count) {
    TokVec tv = {0};
    int i = 0;

    while (s[i]) {
        while (s[i] == ' ' || s[i] == '\t') i++;
        if (!s[i] || s[i] == '\n') break;

        if (s[i] == '#') break;

        if (s[i] == '|') {
            if (s[i + 1] == '|') {
                tv_add(&tv, T_OR, "||", 0);
                i += 2;
            } else {
                tv_add(&tv, T_PIPE, "|", 0);
                i++;
            }
            continue;
        }

        if (s[i] == '&') {
            if (s[i + 1] == '&') {
                tv_add(&tv, T_AND, "&&", 0);
                i += 2;
            } else {
                tv_add(&tv, T_AMP, "&", 0);
                i++;
            }
            continue;
        }

        if (s[i] == ';') {
            tv_add(&tv, T_SEMI, ";", 0);
            i++;
            continue;
        }

        if (s[i] == '<') {
            tv_add(&tv, T_LESS, "<", 0);
            i++;
            continue;
        }

        if (s[i] == '>') {
            if (s[i + 1] == '>') {
                tv_add(&tv, T_DGREAT, ">>", 0);
                i += 2;
            } else {
                tv_add(&tv, T_GREAT, ">", 0);
                i++;
            }
            continue;
        }

        if (isdigit((unsigned char)s[i])) {
            int j = i;
            while (isdigit((unsigned char)s[j])) j++;

            if (s[j] == '<' || s[j] == '>') {
                char buf[32];
                int len = j - i;
                if (len > 31) len = 31;
                memcpy(buf, s + i, len);
                buf[len] = '\0';

                tv_add(&tv, T_IO_NUMBER, buf, atoi(buf));
                i = j;
                continue;
            }
        }

        lex_word(&tv, s, &i);
    }

    tv_add(&tv, T_END, "", 0);
    *count = tv.n;
    return tv.v;
}

typedef struct {
    int type;
    int fd;
    char *file;
} Redir;

typedef struct {
    char **argv;
    int argc;
    Redir *redirs;
    int nredir;
} Cmd;

typedef struct {
    Cmd **cmds;
    int n;
} Pipeline;

typedef struct {
    Pipeline **pipes;
    int n;
    int *ops;
} Andor;

typedef struct {
    Token *t;
    int n;
    int pos;
} Parser;

static Cmd *new_cmd(void) {
    Cmd *c = xmalloc(sizeof(*c));
    c->argv = NULL;
    c->argc = 0;
    c->redirs = NULL;
    c->nredir = 0;
    return c;
}

static void cmd_add_word(Cmd *c, const char *s) {
    c->argv = xrealloc(c->argv, sizeof(char *) * (c->argc + 2));
    c->argv[c->argc++] = xstrdup(s);
    c->argv[c->argc] = NULL;
}

static void cmd_add_redir(Cmd *c, int type, int fd, const char *file) {
    c->redirs = xrealloc(c->redirs, sizeof(Redir) * (c->nredir + 1));
    c->redirs[c->nredir].type = type;
    c->redirs[c->nredir].fd = fd;
    c->redirs[c->nredir].file = xstrdup(file);
    c->nredir++;
}

static void free_cmd(Cmd *c) {
    if (!c) return;

    if (c->argv) {
        for (int i = 0; i < c->argc; i++) free(c->argv[i]);
        free(c->argv);
    }

    if (c->redirs) {
        for (int i = 0; i < c->nredir; i++) free(c->redirs[i].file);
        free(c->redirs);
    }

    free(c);
}

static Pipeline *new_pipeline(void) {
    Pipeline *p = xmalloc(sizeof(*p));
    p->cmds = NULL;
    p->n = 0;
    return p;
}

static void pipeline_add(Pipeline *p, Cmd *c) {
    p->cmds = xrealloc(p->cmds, sizeof(Cmd *) * (p->n + 1));
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

static void free_tokens(Token *t, int n) {
    for (int i = 0; i < n; i++) free(t[i].text);
    free(t);
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
    while (waitpid(-1, &st, WNOHANG) > 0) {
        /* reap background children */
    }
}

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
    if (!s) return 0;

    int i = 0;
    if (!(isalpha((unsigned char)s[i]) || s[i] == '_')) return 0;
    i++;

    while (s[i] && (isalnum((unsigned char)s[i]) || s[i] == '_')) i++;
    return s[i] == '\0';
}

static int count_assignments(char **argv) {
    int n = 0;
    if (!argv) return 0;

    while (argv[n] && name_len_before_eq(argv[n]) > 0) n++;
    return n;
}

static void apply_assignments(char **argv, int nassign) {
    if (!argv) return;

    for (int i = 0; i < nassign; i++) {
        int len = name_len_before_eq(argv[i]);
        if (len <= 0) continue;

        char *name = xmalloc(len + 1);
        memcpy(name, argv[i], len);
        name[len] = '\0';

        setenv(name, argv[i] + len + 1, 1);
        free(name);
    }
}

typedef struct {
    char *name;
    char *old;
    int existed;
} EnvBackup;

static EnvBackup *save_and_set_assignments(char **argv, int nassign, int *nb_out) {
    EnvBackup *b = xmalloc(sizeof(EnvBackup) * (nassign ? nassign : 1));
    int nb = 0;

    for (int i = 0; i < nassign; i++) {
        int len = name_len_before_eq(argv[i]);
        if (len <= 0) continue;

        char *name = xmalloc(len + 1);
        memcpy(name, argv[i], len);
        name[len] = '\0';

        char *value = argv[i] + len + 1;
        char *old = getenv(name);

        b[nb].name = name;
        b[nb].existed = old ? 1 : 0;
        b[nb].old = old ? xstrdup(old) : NULL;

        setenv(name, value, 1);
        nb++;
    }

    *nb_out = nb;
    return b;
}

static void restore_env_backups(EnvBackup *b, int nb) {
    if (!b) return;

    for (int i = nb - 1; i >= 0; i--) {
        if (b[i].existed) setenv(b[i].name, b[i].old ? b[i].old : "", 1);
        else unsetenv(b[i].name);

        free(b[i].old);
        free(b[i].name);
    }

    free(b);
}

typedef struct {
    int orig;
    int saved;
} FdBackup;

static void restore_redirs_current(FdBackup *b, int n) {
    if (!b) return;

    for (int i = n - 1; i >= 0; i--) {
        dup2(b[i].saved, b[i].orig);
        close(b[i].saved);
    }

    free(b);
}

static int redir_flags(int type) {
    switch (type) {
        case T_LESS:
            return O_RDONLY;
        case T_DGREAT:
            return O_WRONLY | O_CREAT | O_APPEND;
        default:
            return O_WRONLY | O_CREAT | O_TRUNC;
    }
}

static int setup_redirs_child(Cmd *cmd) {
    for (int i = 0; i < cmd->nredir; i++) {
        Redir *r = &cmd->redirs[i];

        int fd = open(r->file, redir_flags(r->type), 0644);
        if (fd < 0) {
            fprintf(stderr, "minishell: %s: %s\n", r->file, strerror(errno));
            return 0;
        }

        if (dup2(fd, r->fd) < 0) {
            fprintf(stderr, "minishell: dup2: %s\n", strerror(errno));
            close(fd);
            return 0;
        }

        if (fd != r->fd) close(fd);
    }

    return 1;
}

static int apply_redirs_current(Cmd *cmd, FdBackup **backups, int *nbackup) {
    *backups = NULL;
    *nbackup = 0;

    if (cmd->nredir == 0) return 0;

    FdBackup *b = xmalloc(sizeof(FdBackup) * cmd->nredir);
    int nb = 0;

    for (int i = 0; i < cmd->nredir; i++) {
        Redir *r = &cmd->redirs[i];

        int already = 0;
        for (int j = 0; j < nb; j++) {
            if (b[j].orig == r->fd) {
                already = 1;
                break;
            }
        }

        if (!already) {
            int saved = dup(r->fd);
            if (saved < 0) {
                fprintf(stderr, "minishell: dup: %s\n", strerror(errno));
                restore_redirs_current(b, nb);
                return -1;
            }

            b[nb].orig = r->fd;
            b[nb].saved = saved;
            nb++;
        }

        int fd = open(r->file, redir_flags(r->type), 0644);
        if (fd < 0) {
            fprintf(stderr, "minishell: %s: %s\n", r->file, strerror(errno));
            restore_redirs_current(b, nb);
            return -1;
        }

        if (dup2(fd, r->fd) < 0) {
            fprintf(stderr, "minishell: dup2: %s\n", strerror(errno));
            close(fd);
            restore_redirs_current(b, nb);
            return -1;
        }

        if (fd != r->fd) close(fd);
    }

    *backups = b;
    *nbackup = nb;
    return 0;
}

static int builtin_cd(char **argv) {
    const char *dir = argv[1];

    if (!dir) dir = getenv("HOME");
    if (!dir) {
        fprintf(stderr, "cd: HOME not set\n");
        return 1;
    }

    if (strcmp(dir, "-") == 0) {
        dir = getenv("OLDPWD");
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

    if (old[0]) setenv("OLDPWD", old, 1);

    char cwd[4096];
    if (getcwd(cwd, sizeof(cwd))) setenv("PWD", cwd, 1);

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
    for (int i = 1; argv[i]; i++) {
        int len = name_len_before_eq(argv[i]);

        if (len > 0) {
            char *name = xmalloc(len + 1);
            memcpy(name, argv[i], len);
            name[len] = '\0';

            setenv(name, argv[i] + len + 1, 1);
            free(name);
        } else if (valid_name(argv[i])) {
            if (!getenv(argv[i])) setenv(argv[i], "", 1);
        } else {
            fprintf(stderr, "export: `%s': not a valid identifier\n", argv[i]);
            return 1;
        }
    }

    return 0;
}

static int builtin_unset(char **argv) {
    for (int i = 1; argv[i]; i++) {
        if (valid_name(argv[i])) unsetenv(argv[i]);
        else {
            fprintf(stderr, "unset: `%s': not a valid identifier\n", argv[i]);
            return 1;
        }
    }

    return 0;
}

static int is_builtin(const char *s) {
    if (!s) return 0;

    return strcmp(s, "cd") == 0 ||
           strcmp(s, "pwd") == 0 ||
           strcmp(s, "exit") == 0 ||
           strcmp(s, "export") == 0 ||
           strcmp(s, "unset") == 0 ||
           strcmp(s, "echo") == 0 ||
           strcmp(s, "true") == 0 ||
           strcmp(s, "false") == 0;
}

static int run_builtin(char **argv, int child) {
    if (!argv[0]) return 0;

    if (strcmp(argv[0], "exit") == 0) {
        int st = 0;
        if (argv[1]) st = atoi(argv[1]);

        if (child) _exit(st);

        shell_exit = 1;
        last_status = st;
        return st;
    }

    if (strcmp(argv[0], "cd") == 0) return builtin_cd(argv);
    if (strcmp(argv[0], "pwd") == 0) return builtin_pwd(argv);
    if (strcmp(argv[0], "echo") == 0) return builtin_echo(argv);
    if (strcmp(argv[0], "export") == 0) return builtin_export(argv);
    if (strcmp(argv[0], "unset") == 0) return builtin_unset(argv);
    if (strcmp(argv[0], "true") == 0) return 0;
    if (strcmp(argv[0], "false") == 0) return 1;

    return 0;
}

static int run_simple_child(Cmd *cmd) {
    int nassign = count_assignments(cmd->argv);
    apply_assignments(cmd->argv, nassign);

    if (!setup_redirs_child(cmd)) return 1;

    char **argv = cmd->argv ? cmd->argv + nassign : NULL;
    if (!argv || !argv[0]) return 0;

    if (is_builtin(argv[0])) return run_builtin(argv, 1);

    execvp(argv[0], argv);
    fprintf(stderr, "minishell: %s: %s\n", argv[0], strerror(errno));
    fflush(stderr);
    return 127;
}

static int run_simple_current(Cmd *cmd);
static int execute_pipeline(Pipeline *pl);
static int execute_andor(Andor *a);

static int run_simple_current(Cmd *cmd) {
    int nassign = count_assignments(cmd->argv);
    char **argv = cmd->argv ? cmd->argv + nassign : NULL;

    if (!argv || !argv[0]) {
        apply_assignments(cmd->argv, nassign);

        if (cmd->nredir > 0) {
            pid_t pid = fork();
            if (pid < 0) {
                perror("fork");
                return 1;
            }

            if (pid == 0) {
                _exit(setup_redirs_child(cmd) ? 0 : 1);
            }

            return wait_for_pid(pid);
        }

        return 0;
    }

    if (is_builtin(argv[0])) {
        EnvBackup *eb = NULL;
        int neb = 0;

        if (nassign > 0) eb = save_and_set_assignments(cmd->argv, nassign, &neb);

        FdBackup *fb = NULL;
        int nfb = 0;

        if (apply_redirs_current(cmd, &fb, &nfb) < 0) {
            if (eb) restore_env_backups(eb, neb);
            return 1;
        }

        int st = run_builtin(argv, 0);

        if (fb) restore_redirs_current(fb, nfb);
        if (eb) restore_env_backups(eb, neb);

        return st;
    }

    pid_t pid = fork();
    if (pid < 0) {
        perror("fork");
        return 1;
    }

    if (pid == 0) {
        signal(SIGINT, SIG_DFL);
        signal(SIGQUIT, SIG_DFL);

        apply_assignments(cmd->argv, nassign);

        if (!setup_redirs_child(cmd)) _exit(1);

        execvp(argv[0], argv);
        fprintf(stderr, "minishell: %s: %s\n", argv[0], strerror(errno));
        fflush(stderr);
        _exit(127);
    }

    return wait_for_pid(pid);
}

static int execute_pipeline(Pipeline *pl) {
    if (!pl || pl->n == 0) return 0;

    if (pl->n == 1) return run_simple_current(pl->cmds[0]);

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
            if (has_pipe) {
                close(pipefd[0]);
                close(pipefd[1]);
            }
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

            int st = run_simple_child(pl->cmds[i]);
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

    int status = 0;
    for (int i = 0; i < pl->n; i++) {
        int st = wait_for_pid(pids[i]);
        if (i == pl->n - 1) status = st;
    }

    free(pids);
    return status;
}

static int execute_andor(Andor *a) {
    if (!a || a->n == 0) return 0;

    int status = execute_pipeline(a->pipes[0]);

    for (int i = 1; i < a->n; i++) {
        if (shell_exit) break;

        int op = a->ops[i];

        if ((op == T_AND && status == 0) ||
            (op == T_OR && status != 0)) {
            status = execute_pipeline(a->pipes[i]);
        }
    }

    return status;
}

static Token *peek(Parser *p) {
    return &p->t[p->pos];
}

static int peek_type(Parser *p) {
    return p->t[p->pos].type;
}

static Token *peek_at(Parser *p, int off) {
    int idx = p->pos + off;
    if (idx >= p->n) idx = p->n - 1;
    return &p->t[idx];
}

static Cmd *parse_simple_command(Parser *p) {
    Cmd *c = new_cmd();
    int pending_fd = -1;
    int any = 0;

    for (;;) {
        Token *t = peek(p);

        if (t->type == T_IO_NUMBER) {
            Token *n = peek_at(p, 1);

            if (n->type == T_LESS || n->type == T_GREAT || n->type == T_DGREAT) {
                pending_fd = t->fd;
                p->pos++;
                continue;
            }

            cmd_add_word(c, t->text);
            p->pos++;
            any = 1;
            continue;
        }

        if (t->type == T_LESS || t->type == T_GREAT || t->type == T_DGREAT) {
            int type = t->type;
            int fd = pending_fd != -1 ? pending_fd : (type == T_LESS ? 0 : 1);
            pending_fd = -1;

            p->pos++;

            Token *f = peek(p);
            if (f->type != T_WORD && f->type != T_IO_NUMBER) {
                fprintf(stderr, "minishell: missing filename for redirection\n");
                free_cmd(c);
                return NULL;
            }

            p->pos++;
            cmd_add_redir(c, type, fd, f->text);
            any = 1;
            continue;
        }

        if (t->type == T_WORD) {
            cmd_add_word(c, t->text);
            p->pos++;
            any = 1;
            continue;
        }

        break;
    }

    if (!any) {
        free_cmd(c);
        return NULL;
    }

    return c;
}

static Pipeline *parse_pipeline(Parser *p) {
    Cmd *c = parse_simple_command(p);
    if (!c) return NULL;

    Pipeline *pl = new_pipeline();
    pipeline_add(pl, c);

    while (peek_type(p) == T_PIPE) {
        p->pos++;

        c = parse_simple_command(p);
        if (!c) return NULL;

        pipeline_add(pl, c);
    }

    return pl;
}

static Andor *parse_andor(Parser *p) {
    Pipeline *pl = parse_pipeline(p);
    if (!pl) return NULL;

    Andor *a = new_andor();
    andor_add(a, pl, 0);

    while (peek_type(p) == T_AND || peek_type(p) == T_OR) {
        int op = peek_type(p);
        p->pos++;

        pl = parse_pipeline(p);
        if (!pl) return NULL;

        andor_add(a, pl, op);
    }

    return a;
}

static int parse_execute_line(char *line) {
    int ntok = 0;
    Token *toks = lex_line(line, &ntok);

    Parser p = { toks, ntok, 0 };
    int rc = 0;

    while (peek_type(&p) != T_END) {
        while (peek_type(&p) == T_SEMI) p.pos++;

        if (peek_type(&p) == T_END) break;

        Andor *a = parse_andor(&p);
        if (!a) {
            last_status = 2;
            rc = 2;
            break;
        }

        int bg = 0;
        if (peek_type(&p) == T_AMP) {
            p.pos++;
            bg = 1;
        }

        if (bg) {
            pid_t pid = fork();

            if (pid < 0) {
                perror("fork");
                last_status = 1;
                rc = 1;
            } else if (pid == 0) {
                signal(SIGINT, SIG_DFL);
                signal(SIGQUIT, SIG_DFL);

                int st = execute_andor(a);
                fflush(NULL);
                _exit(st);
            } else {
                last_status = 0;
                rc = 0;
            }
        } else {
            last_status = execute_andor(a);
            rc = last_status;
        }

        if (shell_exit) break;

        if (peek_type(&p) == T_SEMI) p.pos++;
    }

    free_tokens(toks, ntok);
    return rc;
}

static void run_stream(FILE *fp, int interactive) {
    char *line = NULL;
    size_t cap = 0;
    ssize_t len;

    while (!shell_exit) {
        if (interactive) {
            fprintf(stderr, "minishell$ ");
            fflush(stderr);
        }

        len = getline(&line, &cap, fp);
        if (len == -1) break;

        if (len > 0 && line[len - 1] == '\n') line[--len] = '\0';
        if (len > 0 && line[len - 1] == '\r') line[--len] = '\0';

        if (len == 0) continue;

        reap_jobs();
        parse_execute_line(line);
    }

    if (interactive) fprintf(stderr, "\n");

    free(line);
}

int main(int argc, char **argv) {
    setvbuf(stdout, NULL, _IONBF, 0);
    setvbuf(stderr, NULL, _IONBF, 0);

    g_argv = argv;
    g_argc = argc;

    if (argc > 1) {
        FILE *fp = fopen(argv[1], "r");
        if (!fp) {
            fprintf(stderr, "minishell: %s: %s\n", argv[1], strerror(errno));
            return 1;
        }

        g_argc = argc - 1;
        g_argv = argv + 1;

        run_stream(fp, 0);
        fclose(fp);

        return last_status;
    }

    int interactive = isatty(fileno(stdin));

    if (interactive) {
        signal(SIGINT, SIG_IGN);
        signal(SIGQUIT, SIG_IGN);
    }

    run_stream(stdin, interactive);
    return last_status;
}