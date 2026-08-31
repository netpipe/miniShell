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

enum {
    FLOW_NORMAL = 0,
    FLOW_BREAK,
    FLOW_CONTINUE,
    FLOW_RETURN
};

static int flow = FLOW_NORMAL;
static int flow_count = 1;
static int return_status = 0;

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

static void lex_word(TokVec *tv, const char *s, int *ip) {
    int i = *ip;
    Str raw;
    str_init(&raw);
    int quoted = 0;

    while (s[i]) {
        if (s[i] == '\\') {
            quoted = 1;
            str_addch(&raw, s[i]);
            if (s[i + 1]) {
                str_addch(&raw, s[i + 1]);
                i += 2;
            } else {
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
            continue;
        }

        if (s[i] == '"') {
            quoted = 1;
            str_addch(&raw, s[i++]);
            while (s[i] && s[i] != '"') {
                if (s[i] == '\\' &&
                    (s[i + 1] == '$' || s[i + 1] == '"' ||
                     s[i + 1] == '\\' || s[i + 1] == 96)) {
                    str_addch(&raw, s[i]);
                    str_addch(&raw, s[i + 1]);
                    i += 2;
                } else {
                    str_addch(&raw, s[i++]);
                }
            }
            if (s[i] == '"') str_addch(&raw, s[i++]);
            continue;
        }

        if (s[i] == '$') {
            str_addch(&raw, s[i++]);
            if (s[i] == '{' || s[i] == '(' || s[i] == '[') {
                str_addch(&raw, s[i++]);
            }
            continue;
        }

        if (isspace((unsigned char)s[i]) ||
            s[i] == '|' || s[i] == '&' || s[i] == ';' ||
            s[i] == '<' || s[i] == '>' ||
            s[i] == '(' || s[i] == ')') {
            break;
        }

        str_addch(&raw, s[i++]);
    }

    *ip = i;
    if (raw.len > 0) tv_add(tv, T_WORD, raw.s, 0, quoted);
    free(raw.s);
}

static Token *lex_program(const char *s, int *count) {
    TokVec tv = {0};
    int i = 0;

    while (s[i]) {
        while (s[i] == ' ' || s[i] == '\t') i++;
        if (!s[i]) break;

        if (s[i] == '\n') {
            tv_add(&tv, T_NEWLINE, "\n", 0, 0);
            i++;
            continue;
        }

        if (s[i] == '#') {
            while (s[i] && s[i] != '\n') i++;
            continue;
        }

        if (s[i] == '|') {
            if (s[i + 1] == '|') {
                tv_add(&tv, T_OR, "||", 0, 0);
                i += 2;
            } else {
                tv_add(&tv, T_PIPE, "|", 0, 0);
                i++;
            }
            continue;
        }

        if (s[i] == '&') {
            if (s[i + 1] == '&') {
                tv_add(&tv, T_AND, "&&", 0, 0);
                i += 2;
            } else {
                tv_add(&tv, T_AMP, "&", 0, 0);
                i++;
            }
            continue;
        }

        if (s[i] == ';') {
            tv_add(&tv, T_SEMI, ";", 0, 0);
            i++;
            continue;
        }

        if (s[i] == '<') {
            tv_add(&tv, T_LESS, "<", 0, 0);
            i++;
            continue;
        }

        if (s[i] == '>') {
            if (s[i + 1] == '>') {
                tv_add(&tv, T_DGREAT, ">>", 0, 0);
                i += 2;
            } else {
                tv_add(&tv, T_GREAT, ">", 0, 0);
                i++;
            }
            continue;
        }

        if (s[i] == '{') {
            tv_add(&tv, T_LBRACE, "{", 0, 0);
            i++;
            continue;
        }

        if (s[i] == '}') {
            tv_add(&tv, T_RBRACE, "}", 0, 0);
            i++;
            continue;
        }

        if (s[i] == '(') {
            tv_add(&tv, T_LPAREN, "(", 0, 0);
            i++;
            continue;
        }

        if (s[i] == ')') {
            tv_add(&tv, T_RPAREN, ")", 0, 0);
            i++;
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

                tv_add(&tv, T_IO_NUMBER, buf, atoi(buf), 0);
                i = j;
                continue;
            }
        }

        lex_word(&tv, s, &i);
    }

    tv_add(&tv, T_END, "", 0, 0);
    *count = tv.n;
    return tv.v;
}

typedef struct Node Node;

typedef enum {
    N_LIST,
    N_SUBSHELL,
    N_SIMPLE,
    N_IF,
    N_WHILE,
    N_FOR,
    N_FUNC
} NodeType;

struct Node {
    NodeType type;
    void *data;
};

typedef struct {
    int type;
    int fd;
    char *file;
} Redir;

typedef struct {
    char **words;
    int nwords;
    Redir *redirs;
    int nredir;
} Simple;

typedef struct {
    Node **cmds;
    int n;
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
} While;

typedef struct {
    char *var;
    char **words;
    int nwords;
    int use_args;
    List *body;
} For;

typedef struct FuncDef {
    char *name;
    Node *body;
    struct FuncDef *next;
} FuncDef;

static FuncDef *functions = NULL;

static FuncDef *find_function(const char *name) {
    for (FuncDef *f = functions; f; f = f->next) {
        if (strcmp(f->name, name) == 0) return f;
    }
    return NULL;
}

static void add_function(FuncDef *def) {
    FuncDef *f = find_function(def->name);
    if (f) {
        f->body = def->body;
        return;
    }

    def->next = functions;
    functions = def;
}

typedef struct ArgsFrame {
    char **argv;
    int argc;
    struct ArgsFrame *next;
} ArgsFrame;

static ArgsFrame *frames = NULL;

static void push_frame(char **argv, int argc) {
    ArgsFrame *f = xmalloc(sizeof(*f));
    f->argv = argv;
    f->argc = argc;
    f->next = frames;
    frames = f;
}

static void pop_frame(void) {
    if (!frames) return;
    ArgsFrame *f = frames;
    frames = frames->next;
    free(f);
}

static char **cur_argv(void) {
    return frames ? frames->argv : g_argv;
}

static int cur_argc(void) {
    return frames ? frames->argc : g_argc;
}

static Simple *new_simple(void) {
    Simple *s = xmalloc(sizeof(*s));
    s->words = NULL;
    s->nwords = 0;
    s->redirs = NULL;
    s->nredir = 0;
    return s;
}

static void simple_add_word(Simple *s, const char *w) {
    s->words = xrealloc(s->words, sizeof(char *) * (s->nwords + 2));
    s->words[s->nwords++] = xstrdup(w);
    s->words[s->nwords] = NULL;
}

static void simple_add_redir(Simple *s, int type, int fd, const char *file) {
    s->redirs = xrealloc(s->redirs, sizeof(Redir) * (s->nredir + 1));
    s->redirs[s->nredir].type = type;
    s->redirs[s->nredir].fd = fd;
    s->redirs[s->nredir].file = xstrdup(file);
    s->nredir++;
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

static Node *new_simple_node(Simple *s) {
    return new_node(N_SIMPLE, s);
}

static Node *new_list_node(List *l) {
    return new_node(N_LIST, l);
}

static Node *new_subshell_node(List *l) {
    return new_node(N_SUBSHELL, l);
}

static Node *new_if_node(List *cond, List *then, Node *else_node) {
    If *i = xmalloc(sizeof(*i));
    i->cond = cond;
    i->then = then;
    i->else_node = else_node;
    return new_node(N_IF, i);
}

static Node *new_while_node(List *cond, List *body) {
    While *w = xmalloc(sizeof(*w));
    w->cond = cond;
    w->body = body;
    return new_node(N_WHILE, w);
}

static Node *new_func_node(char *name, Node *body) {
    FuncDef *f = xmalloc(sizeof(*f));
    f->name = name;
    f->body = body;
    f->next = NULL;
    return new_node(N_FUNC, f);
}

typedef struct {
    Token *t;
    int n;
    int pos;
} Parser;

static Token *peek(Parser *p) {
    return &p->t[p->pos];
}

static Token *peek_at(Parser *p, int off) {
    int idx = p->pos + off;
    if (idx >= p->n) idx = p->n - 1;
    return &p->t[idx];
}

static int peek_type(Parser *p) {
    return peek(p)->type;
}

static void advance(Parser *p) {
    if (p->pos < p->n - 1) p->pos++;
}

static int is_word(Token *t, const char *s) {
    return t->type == T_WORD && !t->quoted && t->text && strcmp(t->text, s) == 0;
}

static void parse_error(Parser *p, const char *msg) {
    Token *t = peek(p);
    fprintf(stderr, "minishell: syntax error: %s near '%s'\n",
            msg, t->text ? t->text : "?");
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
    while (peek_type(p) == T_SEMI || peek_type(p) == T_NEWLINE) {
        advance(p);
    }
}

static Node *parse_simple_command(Parser *p) {
    Simple *s = new_simple();
    int pending_fd = -1;
    int any = 0;

    for (;;) {
        Token *t = peek(p);

        if (t->type == T_IO_NUMBER) {
            Token *n = peek_at(p, 1);
            if (n->type == T_LESS || n->type == T_GREAT || n->type == T_DGREAT) {
                pending_fd = t->fd;
                advance(p);
                continue;
            }

            simple_add_word(s, t->text);
            advance(p);
            any = 1;
            continue;
        }

        if (t->type == T_LESS || t->type == T_GREAT || t->type == T_DGREAT) {
            int type = t->type;
            int fd = pending_fd != -1 ? pending_fd : (type == T_LESS ? 0 : 1);
            pending_fd = -1;

            advance(p);

            Token *f = peek(p);
            if (f->type != T_WORD &&
                f->type != T_IO_NUMBER &&
                f->type != T_LBRACE &&
                f->type != T_RBRACE &&
                f->type != T_LPAREN &&
                f->type != T_RPAREN) {
                parse_error(p, "missing redirection filename");
                return NULL;
            }

            simple_add_redir(s, type, fd, f->text);
            advance(p);
            any = 1;
            continue;
        }

        if (t->type == T_WORD ||
            (any && (t->type == T_LBRACE ||
                     t->type == T_RBRACE ||
                     t->type == T_LPAREN ||
                     t->type == T_RPAREN))) {
            simple_add_word(s, t->text ? t->text : "");
            advance(p);
            any = 1;
            continue;
        }

        break;
    }

    if (!any) return NULL;
    return new_simple_node(s);
}

static Node *parse_brace(Parser *p) {
    advance(p); /* { */

    TType stops[] = { T_RBRACE };
    List *l = parse_list(p, NULL, 0, stops, 1);
    if (!l) return NULL;

    if (peek_type(p) != T_RBRACE) {
        parse_error(p, "expected '}'");
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

    skip_separators(p);

    Args words;
    args_init(&words);
    int use_args = 0;

    if (is_word(peek(p), "in")) {
        advance(p);

        for (;;) {
            if (peek_type(p) == T_SEMI ||
                peek_type(p) == T_NEWLINE ||
                peek_type(p) == T_END) {
                break;
            }

            if (is_word(peek(p), "do")) break;

            Token *t = peek(p);
            if (t->type == T_WORD ||
                t->type == T_IO_NUMBER ||
                t->type == T_LBRACE ||
                t->type == T_RBRACE ||
                t->type == T_LPAREN ||
                t->type == T_RPAREN) {
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
        return NULL;
    }

    advance(p);

    const char *stop_done[] = { "done" };
    List *body = parse_list(p, stop_done, 1, NULL, 0);
    if (!body) return NULL;

    if (!is_word(peek(p), "done")) {
        parse_error(p, "expected 'done'");
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

static Node *parse_while(Parser *p) {
    advance(p); /* while */

    const char *stop_do[] = { "do" };
    List *cond = parse_list(p, stop_do, 1, NULL, 0);
    if (!cond) return NULL;

    if (!is_word(peek(p), "do")) {
        parse_error(p, "expected 'do' after while condition");
        return NULL;
    }

    advance(p);

    const char *stop_done[] = { "done" };
    List *body = parse_list(p, stop_done, 1, NULL, 0);
    if (!body) return NULL;

    if (!is_word(peek(p), "done")) {
        parse_error(p, "expected 'done'");
        return NULL;
    }

    advance(p);

    return new_while_node(cond, body);
}

static Node *parse_if(Parser *p) {
    advance(p); /* if */

    List **conds = NULL;
    List **thens = NULL;
    int n = 0;

    for (;;) {
        const char *stop_then[] = { "then" };
        List *cond = parse_list(p, stop_then, 1, NULL, 0);
        if (!cond) return NULL;

        if (!is_word(peek(p), "then")) {
            parse_error(p, "expected 'then'");
            return NULL;
        }
        advance(p);

        const char *stop_body[] = { "else", "elif", "fi" };
        List *then = parse_list(p, stop_body, 3, NULL, 0);
        if (!then) return NULL;

        conds = xrealloc(conds, sizeof(List *) * (n + 1));
        thens = xrealloc(thens, sizeof(List *) * (n + 1));
        conds[n] = cond;
        thens[n] = then;
        n++;

        if (is_word(peek(p), "elif")) {
            advance(p);
            continue;
        }

        break;
    }

    Node *else_node = NULL;

    if (is_word(peek(p), "else")) {
        advance(p);

        const char *stop_fi[] = { "fi" };
        List *else_list = parse_list(p, stop_fi, 1, NULL, 0);
        if (!else_list) return NULL;

        else_node = new_list_node(else_list);
    }

    if (!is_word(peek(p), "fi")) {
        parse_error(p, "expected 'fi'");
        return NULL;
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
            return NULL;
        }
        advance(p);
    }

    skip_separators(p);

    Node *body = parse_command(p);
    if (!body) return NULL;

    return new_func_node(fname, body);
}

static Node *parse_function_paren(Parser *p) {
    Token *name = peek(p);
    char *fname = xstrdup(name->text);

    advance(p); /* name */
    advance(p); /* ( */
    advance(p); /* ) */

    skip_separators(p);

    Node *body = parse_command(p);
    if (!body) return NULL;

    return new_func_node(fname, body);
}

static Node *parse_command(Parser *p) {
    Token *t = peek(p);

    if (is_word(t, "function")) {
        return parse_function_keyword(p);
    }

    if (t->type == T_WORD && !t->quoted) {
        Token *n1 = peek_at(p, 1);
        Token *n2 = peek_at(p, 2);

        if (n1->type == T_LPAREN && n2->type == T_RPAREN) {
            return parse_function_paren(p);
        }
    }

    if (is_word(t, "if")) return parse_if(p);
    if (is_word(t, "while")) return parse_while(p);
    if (is_word(t, "for")) return parse_for(p);
    if (t->type == T_LBRACE) return parse_brace(p);
    if (t->type == T_LPAREN) return parse_subshell(p);

    return parse_simple_command(p);
}

static Pipeline *parse_pipeline(Parser *p) {
    Node *c = parse_command(p);
    if (!c) return NULL;

    Pipeline *pl = new_pipeline();
    pipeline_add(pl, c);

    while (peek_type(p) == T_PIPE) {
        advance(p);

        c = parse_command(p);
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
        advance(p);

        pl = parse_pipeline(p);
        if (!pl) return NULL;

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
        if (!a) return NULL;

        int bg = 0;
        if (peek_type(p) == T_AMP) {
            advance(p);
            bg = 1;
        }

        list_add(l, a, bg);
    }

    return l;
}

static int expand_raw(const char *raw, Str *out, int *quoted);
static char *expand_scalar(const char *raw);
static int expand_var_runtime(const char *s, int i, Str *out);

static int expand_var_runtime(const char *s, int i, Str *out) {
    i++; /* skip $ */

    if (s[i] == '?') {
        str_addint(out, last_status);
        return i + 1;
    }

    if (s[i] == '$') {
        str_addint(out, (long)getpid());
        return i + 1;
    }

    if (s[i] == '#') {
        int c = cur_argc();
        str_addint(out, c > 0 ? c - 1 : 0);
        return i + 1;
    }

    if (s[i] == '@' || s[i] == '*') {
        char **av = cur_argv();
        int ac = cur_argc();

        for (int j = 1; j < ac; j++) {
            if (j > 1) str_addch(out, ' ');
            str_addstr(out, av[j]);
        }

        return i + 1;
    }

    if (s[i] == '0') {
        char **av = cur_argv();
        int ac = cur_argc();
        str_addstr(out, ac > 0 ? av[0] : "minishell");
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
            if (num < cur_argc()) val = cur_argv()[num];
        } else {
            val = getenv(name);
        }

        if (s[i] == ':' && s[i + 1] == '-') {
            i += 2;

            int dstart = i;
            while (s[i] && s[i] != '}') i++;
            int dlen = i - dstart;

            if (s[i] == '}') i++;

            if (!val || !*val) {
                char *d = xmalloc(dlen + 1);
                memcpy(d, s + dstart, dlen);
                d[dlen] = '\0';

                char *e = expand_scalar(d);
                str_addstr(out, e);

                free(e);
                free(d);
            } else {
                str_addstr(out, val);
            }
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

        if (n < cur_argc()) str_addstr(out, cur_argv()[n]);
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

static int expand_raw(const char *raw, Str *out, int *quoted) {
    int i = 0;
    *quoted = 0;

    while (raw[i]) {
        if (raw[i] == '\\') {
            *quoted = 1;
            if (raw[i + 1]) {
                str_addch(out, raw[i + 1]);
                i += 2;
            } else {
                str_addch(out, '\\');
                i++;
            }
            continue;
        }

        if (raw[i] == '\'') {
            *quoted = 1;
            i++;
            while (raw[i] && raw[i] != '\'') str_addch(out, raw[i++]);
            if (raw[i] == '\'') i++;
            continue;
        }

        if (raw[i] == '"') {
            *quoted = 1;
            i++;

            while (raw[i] && raw[i] != '"') {
                if (raw[i] == '\\' &&
                    (raw[i + 1] == '$' || raw[i + 1] == '"' ||
                     raw[i + 1] == '\\' || raw[i + 1] == 96)) {
                    str_addch(out, raw[i + 1]);
                    i += 2;
                } else if (raw[i] == '$') {
                    i = expand_var_runtime(raw, i, out);
                } else {
                    str_addch(out, raw[i++]);
                }
            }

            if (raw[i] == '"') i++;
            continue;
        }

        if (raw[i] == '$') {
            i = expand_var_runtime(raw, i, out);
            continue;
        }

        str_addch(out, raw[i++]);
    }

    return 0;
}

static char *expand_scalar(const char *raw) {
    Str st;
    str_init(&st);
    int q = 0;

    expand_raw(raw, &st, &q);
    return st.s;
}

static void expand_to_args(const char *raw, Args *args) {
    Str st;
    str_init(&st);

    int q = 0;
    expand_raw(raw, &st, &q);

    if (q) {
        args_add_copy(args, st.s);
    } else {
        char *p = st.s;

        while (*p) {
            while (isspace((unsigned char)*p)) p++;
            if (!*p) break;

            char *start = p;
            while (*p && !isspace((unsigned char)*p)) p++;

            char c = *p;
            *p = '\0';

            args_add_copy(args, start);

            if (!c) break;
            *p = c;
            p++;
        }
    }

    free(st.s);
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

static int builtin_test(char **argv) {
    int argc = 0;
    while (argv[argc]) argc++;

    int start = 1;
    int end = argc;

    if (argv[0][0] == '[') {
        if (argc < 2 || strcmp(argv[argc - 1], "]") != 0) return 2;
        end = argc - 1;
    }

    int n = end - start;
    char **a = argv + start;

    if (n == 0) return 1;

    if (n == 1) {
        if (strcmp(a[0], "-z") == 0 ||
            strcmp(a[0], "-n") == 0 ||
            strcmp(a[0], "-f") == 0 ||
            strcmp(a[0], "-d") == 0 ||
            strcmp(a[0], "-e") == 0) {
            return 1;
        }

        return a[0][0] ? 0 : 1;
    }

    if (n == 2) {
        if (strcmp(a[0], "-f") == 0) {
            struct stat st;
            return stat(a[1], &st) == 0 && S_ISREG(st.st_mode) ? 0 : 1;
        }

        if (strcmp(a[0], "-d") == 0) {
            struct stat st;
            return stat(a[1], &st) == 0 && S_ISDIR(st.st_mode) ? 0 : 1;
        }

        if (strcmp(a[0], "-e") == 0) {
            return access(a[1], F_OK) == 0 ? 0 : 1;
        }

        if (strcmp(a[0], "-z") == 0) {
            return a[1][0] ? 1 : 0;
        }

        if (strcmp(a[0], "-n") == 0) {
            return a[1][0] ? 0 : 1;
        }

        return 2;
    }

    if (n == 3) {
        const char *l = a[0];
        const char *op = a[1];
        const char *r = a[2];

        if (strcmp(op, "=") == 0 || strcmp(op, "==") == 0) {
            return strcmp(l, r) == 0 ? 0 : 1;
        }

        if (strcmp(op, "!=") == 0) {
            return strcmp(l, r) != 0 ? 0 : 1;
        }

        long li = strtol(l, NULL, 10);
        long ri = strtol(r, NULL, 10);

        if (strcmp(op, "-eq") == 0) return li == ri ? 0 : 1;
        if (strcmp(op, "-ne") == 0) return li != ri ? 0 : 1;
        if (strcmp(op, "-lt") == 0) return li < ri ? 0 : 1;
        if (strcmp(op, "-le") == 0) return li <= ri ? 0 : 1;
        if (strcmp(op, "-gt") == 0) return li > ri ? 0 : 1;
        if (strcmp(op, "-ge") == 0) return li >= ri ? 0 : 1;

        return 2;
    }

    return 2;
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
           strcmp(s, "false") == 0 ||
           strcmp(s, "test") == 0 ||
           strcmp(s, "[") == 0 ||
           strcmp(s, "break") == 0 ||
           strcmp(s, "continue") == 0 ||
           strcmp(s, "return") == 0;
}

static int run_builtin(char **argv) {
    if (!argv[0]) return 0;

    if (strcmp(argv[0], "exit") == 0) {
        int st = argv[1] ? atoi(argv[1]) : 0;
        shell_exit = 1;
        last_status = st;
        return st;
    }

    if (strcmp(argv[0], "cd") == 0) return builtin_cd(argv);
    if (strcmp(argv[0], "pwd") == 0) return builtin_pwd(argv);
    if (strcmp(argv[0], "echo") == 0) return builtin_echo(argv);
    if (strcmp(argv[0], "export") == 0) return builtin_export(argv);
    if (strcmp(argv[0], "unset") == 0) return builtin_unset(argv);
    if (strcmp(argv[0], "test") == 0 || strcmp(argv[0], "[") == 0) {
        return builtin_test(argv);
    }

    if (strcmp(argv[0], "true") == 0) return 0;
    if (strcmp(argv[0], "false") == 0) return 1;

    if (strcmp(argv[0], "break") == 0) {
        flow = FLOW_BREAK;
        flow_count = argv[1] ? atoi(argv[1]) : 1;
        if (flow_count < 1) flow_count = 1;
        return 0;
    }

    if (strcmp(argv[0], "continue") == 0) {
        flow = FLOW_CONTINUE;
        flow_count = argv[1] ? atoi(argv[1]) : 1;
        if (flow_count < 1) flow_count = 1;
        return 0;
    }

    if (strcmp(argv[0], "return") == 0) {
        int st = argv[1] ? atoi(argv[1]) : 0;
        return_status = st;
        last_status = st;
        flow = FLOW_RETURN;
        return st;
    }

    return 0;
}

typedef struct {
    char *name;
    char *value;
} Assign;

typedef struct {
    char *name;
    char *old;
    int existed;
} EnvBackup;

static void apply_assigns(Assign *a, int n) {
    for (int i = 0; i < n; i++) {
        setenv(a[i].name, a[i].value, 1);
    }
}

static EnvBackup *save_and_set_assigns(Assign *a, int n, int *nb_out) {
    EnvBackup *b = xmalloc(sizeof(EnvBackup) * (n ? n : 1));
    int nb = 0;

    for (int i = 0; i < n; i++) {
        char *old = getenv(a[i].name);

        b[nb].name = xstrdup(a[i].name);
        b[nb].existed = old ? 1 : 0;
        b[nb].old = old ? xstrdup(old) : NULL;

        setenv(a[i].name, a[i].value, 1);
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

static void free_assigns(Assign *a, int n) {
    if (!a) return;

    for (int i = 0; i < n; i++) {
        free(a[i].name);
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

static int setup_redirs_files(Simple *s, char **files) {
    for (int i = 0; i < s->nredir; i++) {
        Redir *r = &s->redirs[i];

        int fd = open(files[i], redir_flags(r->type), 0644);
        if (fd < 0) {
            fprintf(stderr, "minishell: %s: %s\n", files[i], strerror(errno));
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

static int apply_redirs_current_files(Simple *s, char **files,
                                      FdBackup **backups, int *nbackup) {
    *backups = NULL;
    *nbackup = 0;

    if (s->nredir == 0) return 0;

    FdBackup *b = xmalloc(sizeof(FdBackup) * s->nredir);
    int nb = 0;

    for (int i = 0; i < s->nredir; i++) {
        Redir *r = &s->redirs[i];

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

        int fd = open(files[i], redir_flags(r->type), 0644);
        if (fd < 0) {
            fprintf(stderr, "minishell: %s: %s\n", files[i], strerror(errno));
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

static int execute_node(Node *n);
static int execute_list(List *l);
static int execute_andor(Andor *a);
static int execute_pipeline(Pipeline *pl);
static int execute_simple(Simple *s);
static int execute_if(Node *n);
static int execute_while(Node *n);
static int execute_for(Node *n);
static int execute_subshell(List *l);

static int execute_simple(Simple *s) {
    int nassign = 0;

    while (s->words[nassign] &&
           name_len_before_eq(s->words[nassign]) > 0) {
        nassign++;
    }

    Assign *assigns = xmalloc(sizeof(Assign) * (nassign ? nassign : 1));

    for (int i = 0; i < nassign; i++) {
        int len = name_len_before_eq(s->words[i]);

        char *name = xmalloc(len + 1);
        memcpy(name, s->words[i], len);
        name[len] = '\0';

        char *value = expand_scalar(s->words[i] + len + 1);

        assigns[i].name = name;
        assigns[i].value = value;
    }

    Args args;
    args_init(&args);

    for (int i = nassign; s->words[i]; i++) {
        expand_to_args(s->words[i], &args);
    }

    char **files = xmalloc(sizeof(char *) * (s->nredir ? s->nredir : 1));
    for (int i = 0; i < s->nredir; i++) {
        files[i] = expand_scalar(s->redirs[i].file);
    }

    int status = 0;
    EnvBackup *eb = NULL;
    FdBackup *fb = NULL;
    int neb = 0;
    int nfb = 0;
    pid_t pid = 0;

    if (args.n == 0) {
        apply_assigns(assigns, nassign);

        if (s->nredir > 0) {
            if (apply_redirs_current_files(s, files, &fb, &nfb) == 0) {
                restore_redirs_current(fb, nfb);
                status = 0;
            } else {
                status = 1;
            }
        }

        goto cleanup;
    }

    FuncDef *f = find_function(args.v[0]);
    if (f) {
        if (nassign > 0) eb = save_and_set_assigns(assigns, nassign, &neb);

        if (apply_redirs_current_files(s, files, &fb, &nfb) < 0) {
            if (eb) restore_env_backups(eb, neb);
            status = 1;
            goto cleanup;
        }

        push_frame(args.v, args.n);
        status = execute_node(f->body);
        pop_frame();

        if (flow == FLOW_RETURN) {
            flow = FLOW_NORMAL;
            status = return_status;
        }

        if (fb) restore_redirs_current(fb, nfb);
        if (eb) restore_env_backups(eb, neb);

        goto cleanup;
    }

    if (is_builtin(args.v[0])) {
        if (nassign > 0) eb = save_and_set_assigns(assigns, nassign, &neb);

        if (apply_redirs_current_files(s, files, &fb, &nfb) < 0) {
            if (eb) restore_env_backups(eb, neb);
            status = 1;
            goto cleanup;
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

        apply_assigns(assigns, nassign);

        if (!setup_redirs_files(s, files)) _exit(1);

        execvp(args.v[0], args.v);
        fprintf(stderr, "minishell: %s: %s\n", args.v[0], strerror(errno));
        fflush(stderr);
        _exit(127);
    } else {
        status = wait_for_pid(pid);
    }

cleanup:
    free_assigns(assigns, nassign);
    args_free(&args);

    for (int i = 0; i < s->nredir; i++) free(files[i]);
    free(files);

    return status;
}

static int execute_pipeline(Pipeline *pl) {
    if (!pl || pl->n == 0) return 0;

    if (pl->n == 1) return execute_node(pl->cmds[0]);

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
    last_status = status;

    for (int i = 1; i < a->n; i++) {
        if (shell_exit || flow != FLOW_NORMAL) break;

        int op = a->ops[i];

        if ((op == T_AND && status == 0) ||
            (op == T_OR && status != 0)) {
            status = execute_pipeline(a->pipes[i]);
            last_status = status;
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
                last_status = 1;
            } else if (pid == 0) {
                signal(SIGINT, SIG_DFL);
                signal(SIGQUIT, SIG_DFL);

                int st = execute_andor(l->items[i].andor);
                fflush(NULL);
                _exit(st);
            } else {
                status = 0;
                last_status = 0;
            }
        } else {
            status = execute_andor(l->items[i].andor);
            last_status = status;
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
        _exit(st);
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

        int cs = execute_list(i->cond);

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

static int execute_while(Node *n) {
    While *w = n->data;
    int status = 0;

    while (!shell_exit && flow == FLOW_NORMAL) {
        int cs = execute_list(w->cond);

        if (shell_exit || flow != FLOW_NORMAL) break;
        if (cs != 0) break;

        status = execute_list(w->body);

        if (flow == FLOW_BREAK) {
            if (--flow_count == 0) {
                flow = FLOW_NORMAL;
                break;
            } else {
                break;
            }
        } else if (flow == FLOW_CONTINUE) {
            if (--flow_count == 0) {
                flow = FLOW_NORMAL;
                continue;
            } else {
                break;
            }
        } else if (flow == FLOW_RETURN || shell_exit) {
            break;
        }
    }

    return status;
}

static int execute_for(Node *n) {
    For *f = n->data;

    Args vals;
    args_init(&vals);

    if (f->use_args) {
        char **av = cur_argv();
        int ac = cur_argc();

        for (int i = 1; i < ac; i++) {
            args_add_copy(&vals, av[i]);
        }
    } else {
        for (int i = 0; i < f->nwords; i++) {
            expand_to_args(f->words[i], &vals);
        }
    }

    int status = 0;

    for (int i = 0; i < vals.n; i++) {
        if (shell_exit || flow != FLOW_NORMAL) break;

        setenv(f->var, vals.v[i], 1);

        status = execute_list(f->body);

        if (flow == FLOW_BREAK) {
            if (--flow_count == 0) {
                flow = FLOW_NORMAL;
                break;
            } else {
                break;
            }
        } else if (flow == FLOW_CONTINUE) {
            if (--flow_count == 0) {
                flow = FLOW_NORMAL;
                continue;
            } else {
                break;
            }
        } else if (flow == FLOW_RETURN || shell_exit) {
            break;
        }
    }

    args_free(&vals);
    return status;
}

static int execute_node(Node *n) {
    if (!n) return 0;

    switch (n->type) {
        case N_SIMPLE:
            return execute_simple((Simple *)n->data);

        case N_LIST:
            return execute_list((List *)n->data);

        case N_SUBSHELL:
            return execute_subshell((List *)n->data);

        case N_IF:
            return execute_if(n);

        case N_WHILE:
            return execute_while(n);

        case N_FOR:
            return execute_for(n);

        case N_FUNC:
            add_function((FuncDef *)n->data);
            return 0;
    }

    return 0;
}

static int run_program_string(const char *s) {
    int ntok = 0;
    Token *toks = lex_program(s, &ntok);

    Parser p;
    p.t = toks;
    p.n = ntok;
    p.pos = 0;

    List *top = parse_list(&p, NULL, 0, NULL, 0);

    int rc = 0;

    if (!top) {
        fprintf(stderr, "minishell: syntax error\n");
        last_status = 2;
        rc = 2;
    } else {
        rc = execute_list(top);
        last_status = rc;
    }

    if (flow != FLOW_NORMAL) flow = FLOW_NORMAL;

    free_tokens(toks, ntok);
    return rc;
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

    while (!shell_exit) {
        fprintf(stderr, "minishell$ ");
        fflush(stderr);

        len = getline(&line, &cap, stdin);
        if (len == -1) break;

        if (len > 0 && line[len - 1] == '\n') line[--len] = '\0';
        if (len > 0 && line[len - 1] == '\r') line[--len] = '\0';

        if (len == 0) continue;

        reap_jobs();
        run_program_string(line);
    }

    fprintf(stderr, "\n");
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

        char *src = read_all(fp);
        run_program_string(src ? src : "");

        free(src);
        fclose(fp);

        return last_status;
    }

    if (isatty(fileno(stdin))) {
        run_interactive();
        return last_status;
    }

    char *src = read_all(stdin);
    run_program_string(src ? src : "");
    free(src);

    return last_status;
}