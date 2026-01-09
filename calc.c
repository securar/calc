#include <assert.h>
#include <bits/types/struct_itimerspec.h>
#include <math.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include <readline/history.h>
#include <readline/readline.h>
#include <string.h>

#define exit_fatal(fmt, ...)                                                   \
    do {                                                                       \
        printf("[%s:%d] fatal: " fmt "\n", __FILE__, __LINE__, ##__VA_ARGS__); \
        exit(1);                                                               \
    } while (0)

#define check_alloc(ptr, size)                                 \
    do {                                                       \
        if (ptr == NULL) {                                     \
            exit_fatal("alocation of %zu bytes failed", size); \
        }                                                      \
    } while (0)

/// Max amount of parameters or arguments a function
/// declaration or function call can have
const size_t FN_MAX_PARAMS = 32;

const size_t RECURSION_LIMIT = 256;

const char EOF_CHAR = '\0';

// ************************************
//  ************* TOKENS *************
// ************************************

typedef enum {
    /* Basic tokens */
    TOK_NUMBER,
    TOK_IDENT,
    TOK_OPENPAR,
    TOK_CLOSEPAR,
    TOK_PLUS,
    TOK_MINUS,
    TOK_STAR,
    TOK_STARSTAR,
    TOK_SLASH,
    TOK_EQ,
    TOK_COLON,
    TOK_COMMA,
    TOK_DOLLAR,

    /* Special tokens */
    TOK_UNKNOWN,
    TOK_EOF,
} TokenType;

/// String representations of `TokenType` enum
/// indexed in the same way as integer values of enum
static const char* TOKEN_TO_STR[TOK_EOF + 1] = {
    "Number",
    "Ident",
    "OpenPar",
    "ClosePar",
    "Plus",
    "Minus",
    "Star",
    "Slash",
    "Eq",
    "Colon",
    "Comma",
    "Dollar",
    "Unknown",
    "Eof",
};

typedef struct {
    size_t start;
    size_t len;
} Span;

size_t span_end(Span span) {
    return span.start + span.len;
}

typedef struct {
    Span span;
    char* view;
    TokenType type;
} Token;

void print_token(char* prefix, Token* tok, char* suffix) {
    const char* as_str = TOKEN_TO_STR[tok->type];
    printf("%s%s(\"%.*s\")%s\n", prefix, as_str, (int)tok->span.len, tok->view, suffix);
}

/// Get token lexeme.
/// Size of the buffer should be at least token length + 1
void get_lexeme(char* view, char* buf, size_t size) {
    memcpy(buf, view, size);
    buf[size] = '\0';
}

// *****************************************
//  ************* DIAGNOSTICS *************
// *****************************************

/// Print as many `^` as token's length
void diagnose(char* input, Span span) {
    printf("    %s\n", input);
    printf("    ");
    for (size_t i = 0; i < span.start; i++) {
        putchar(' ');
    }
    for (size_t i = 0; i < span.len; i++) {
        putchar('^');
    }
    printf("\n");
}

// ******************************************
//  ************* TOKEN STREAM *************
// ******************************************

/// Dynamic array used to store stream of tokens produced by a lexer
typedef struct {
    size_t count;
    size_t capacity;
    Token* tokens;
} TokenStream;

/// Allocate new token stream. Caller is responsible for freeing the data
TokenStream ts_alloc(size_t capacity) {
    TokenStream ts = {0};
    assert(capacity > 0);

    ts.count = 0;
    ts.capacity = capacity;

    size_t size = capacity * sizeof(Token);
    Token* tokens = malloc(size);
    check_alloc(tokens, size);
    ts.tokens = tokens;
    return ts;
}

void ts_push(TokenStream* ts, Token tok) {
    if (ts->count >= ts->capacity) {
        size_t capacity = ts->capacity * 2;
        size_t size = capacity * sizeof(Token);

        Token* tokens = realloc(ts->tokens, size);
        check_alloc(tokens, size);
        ts->tokens = tokens;
        ts->capacity = capacity;
    }
    ts->tokens[ts->count++] = tok;
}

/// Get pointer to a token from stream at given index if any exists.
/// Otherwise return `NULL`
Token* ts_get(TokenStream* ts, size_t index) {
    if (index >= ts->count) {
        return NULL;
    }
    return &ts->tokens[index];
}

void ts_free(TokenStream* ts) {
    free(ts->tokens);
    ts->tokens = NULL;
    ts->count = 0;
    ts->capacity = 0;
}

// ***********************************
//  ************* LEXER *************
// ***********************************

typedef struct {
    char* input;
    size_t input_len;
    size_t pos;
    size_t errors_count;
} Lexer;

bool is_digit(char c) {
    return c >= '0' && c <= '9';
}

bool is_whitespace(char c) {
    return c == ' ' || c == '\n' || c == '\t' || c == '\r' || c == '\f' || c == '\v';
}

/// Check whether a character may start an identifier or not
bool is_ident_start(char c) {
    return isalpha(c) || c == '_';
}

/// Check whether a character may be present after the first character of an identifier
bool is_ident_continue(char c) {
    return is_ident_start(c) || is_digit(c);
}

#define emit_lexer_error(lex, span, message, ...) \
    do {                                          \
        printf("lexical error: %s\n", (message)); \
        diagnose(((Lexer*)lex)->input, (span));   \
        ((Lexer*)lex)->errors_count++;            \
    } while (0)

/// Move to the next character
char lex_bump(Lexer* lex) {
    if (lex->pos < lex->input_len) {
        return lex->input[lex->pos++];
    }
    return EOF_CHAR;
}

/// Peek next character without consuming it
char lex_peek(Lexer* lex) {
    size_t i = lex->pos;
    if (i < lex->input_len) {
        return lex->input[i];
    }
    return EOF_CHAR;
}

/// Eat characters until some non-digit character is encountered
void lex_eat_digits(Lexer* lex) {
    while (is_digit(lex_peek(lex))) {
        lex_bump(lex);
    }
}

/// Produce next token
Token lex_next_token(Lexer* lex) {
    size_t start = lex->pos;
    char* view = &lex->input[start];
    TokenType type;

    char consumed = lex_bump(lex);
    if (consumed == EOF_CHAR) {
        Span span = {
            .start = start,
            .len = 1,
        };
        Token tok = {
            .span = span,
            .view = view,
            .type = TOK_EOF,
        };
        return tok;
    }
    if (is_whitespace(consumed)) {
        while (is_whitespace(lex_peek(lex))) {
            lex_bump(lex);
        }
        return lex_next_token(lex);
    }

    switch (consumed) {
        case '+':
            type = TOK_PLUS;
            break;
        case '-':
            type = TOK_MINUS;
            break;
        case '*':
            if (lex_peek(lex) == '*') {
                lex_bump(lex);
                type = TOK_STARSTAR;
            }
            else {
                type = TOK_STAR;
            }
            break;
        case '/':
            type = TOK_SLASH;
            break;
        case '(':
            type = TOK_OPENPAR;
            break;
        case ')':
            type = TOK_CLOSEPAR;
            break;
        case '=':
            type = TOK_EQ;
            break;
        case ':':
            type = TOK_COLON;
            break;
        case ',':
            type = TOK_COMMA;
            break;
        case '$':
            type = TOK_DOLLAR;
            break;
        default:
            type = TOK_UNKNOWN;
            break;
    }
    if (consumed == '.' && is_digit(lex_peek(lex))) {
        lex_eat_digits(lex);
        type = TOK_NUMBER;
    }
    else if (is_digit(consumed)) {
        lex_eat_digits(lex);
        if (lex_peek(lex) == '.') {
            lex_bump(lex);
            lex_eat_digits(lex);
        }
        type = TOK_NUMBER;
    }
    else if (is_ident_start(consumed)) {
        while (is_ident_continue(lex_peek(lex))) {
            lex_bump(lex);
        }
        type = TOK_IDENT;
    }

    Span span = {
        .start = start,
        .len = lex->pos - start,
    };
    Token tok = {
        .span = span,
        .view = view,
        .type = type,
    };
    return tok;
}

// *********************************************
//  ************* AST AND OBJECTS *************
// *********************************************

/// Node type "tag" used to determine the type of the node
typedef enum {
    AST_NODE_GROUPING,
    AST_NODE_BIN,
    AST_NODE_UNARY,
    AST_NODE_LIT,
    AST_NODE_VAR_DEF,
    AST_NODE_VAR_ACCESS,
    AST_NODE_FN_DEF,
    AST_NODE_FN_CALL,
} AST_NodeType;

/// Syntax tree node used to represent expressions as trees
typedef struct AST_Node AST_Node;

typedef struct {
    Token* params;
    Token name;
    AST_Node* body;
    uint8_t arity;
    bool is_anon;
    char* orig_input;
} Func;

struct AST_Node {
    AST_NodeType type;

    union Expr {
        /// Parenthesized expression, e.g. `(2 + 2)`
        struct {
            AST_Node* node;
        } grouping;

        /// Binary expression, e.g. `a * b`
        struct {
            AST_Node* left;
            Token op;
            AST_Node* right;
        } bin;

        /// Unary expression, e.g. `-42`
        struct {
            Token op;
            AST_Node* right;
        } unary;

        /// Literal, e.g. `3.14`
        struct {
            double value;
        } lit;

        /// Variable definition, e.g. `foo = 1.0`
        struct {
            Token name;
            AST_Node* value;
        } var_def;

        /// Variable access, e.g. `x`
        struct {
            Token name;
        } var_access;

        /// Function definition, e.g. `$mul(a, b): a * b`
        /// or anonymous function: `$(x): x / 10`
        Func fn_def;

        /// Function call, e.g. `foo(2, 2)`
        struct {
            AST_Node** args;
            AST_Node* callee;
            uint8_t args_count;
        } fn_call;
    } as;

    Span span;
};

/// Allocate new node of the syntax tree.
/// Caller is responsible for freeing the data
AST_Node* ast_node_alloc() {
    size_t size = sizeof(AST_Node);
    AST_Node* node = malloc(size);
    check_alloc(node, size);
    return node;
}

void ast_node_free(AST_Node* node) {
    if (node == NULL) {
        return;
    }
    switch (node->type) {
        case AST_NODE_GROUPING: {
            ast_node_free(node->as.grouping.node);
            break;
        }
        case AST_NODE_BIN: {
            ast_node_free(node->as.bin.left);
            ast_node_free(node->as.bin.right);
            break;
        }
        case AST_NODE_UNARY: {
            ast_node_free(node->as.unary.right);
            break;
        }
        case AST_NODE_LIT: {
            break;
        }
        case AST_NODE_VAR_DEF: {
            ast_node_free(node->as.var_def.value);
            break;
        }
        case AST_NODE_VAR_ACCESS: {
            break;
        }
        case AST_NODE_FN_DEF: {
            free(node->as.fn_def.params);
            ast_node_free(node->as.fn_def.body);
            break;
        }
        case AST_NODE_FN_CALL: {
            for (size_t i = 0; i < node->as.fn_call.args_count; i++) {
                ast_node_free(node->as.fn_call.args[i]);
            }
            free(node->as.fn_call.args);
            ast_node_free(node->as.fn_call.callee);
            break;
        }
        default: {
            exit_fatal("unexpected syntax tree node");
        }
    }
    free(node);
}

AST_Node* ast_node_grouping(AST_Node* inner, Span span) {
    AST_Node* node = ast_node_alloc();
    node->type = AST_NODE_GROUPING;
    node->span = span;
    node->as.grouping.node = inner;
    return node;
}

AST_Node* ast_node_bin(AST_Node* left, Token op, AST_Node* right) {
    AST_Node* node = ast_node_alloc();
    node->type = AST_NODE_BIN;
    node->span = (Span){
        .start = left->span.start,
        .len = span_end(right->span) - left->span.start,
    };
    node->as.bin.left = left;
    node->as.bin.op = op;
    node->as.bin.right = right;
    return node;
}

AST_Node* ast_node_unary(Token op, AST_Node* right) {
    AST_Node* node = ast_node_alloc();
    node->type = AST_NODE_UNARY;
    node->span = (Span){
        .start = op.span.start,
        .len = span_end(right->span) - op.span.start,
    };
    node->as.unary.op = op;
    node->as.unary.right = right;
    return node;
}

AST_Node* ast_node_lit(double value, Span span) {
    AST_Node* node = ast_node_alloc();
    node->type = AST_NODE_LIT;
    node->span = span;
    node->as.lit.value = value;
    return node;
}

AST_Node* ast_node_var_def(Token name, AST_Node* value) {
    AST_Node* node = ast_node_alloc();
    node->type = AST_NODE_VAR_DEF;
    node->span = (Span){
        .start = name.span.start,
        .len = span_end(value->span) - name.span.start,
    };
    node->as.var_def.name = name;
    node->as.var_def.value = value;
    return node;
}

AST_Node* ast_node_var_access(Token name) {
    AST_Node* node = ast_node_alloc();
    node->type = AST_NODE_VAR_ACCESS;
    node->span = name.span;
    node->as.var_access.name = name;
    return node;
}

AST_Node* ast_node_fn_def(Func fn_def, Span span) {
    AST_Node* node = ast_node_alloc();
    node->type = AST_NODE_FN_DEF;
    node->span = span;
    node->as.fn_def = fn_def;
    return node;
}

AST_Node* ast_node_fn_call(AST_Node** args, AST_Node* callee, uint8_t args_count, Span span) {
    AST_Node* node = ast_node_alloc();
    node->type = AST_NODE_FN_CALL;
    node->span = span;
    node->as.fn_call.args = args;
    node->as.fn_call.callee = callee;
    node->as.fn_call.args_count = args_count;
    return node;
}

// ************************************
//  ************* PARSER *************
// ************************************

typedef struct {
    TokenStream ts;
    size_t pos;
    char* input;
    size_t errors_count;
} Parser;

/// Peek next token without consuming it
Token* parser_peek(Parser* p) {
    Token* tok = ts_get(&p->ts, p->pos);
    if (tok != NULL) {
        return tok;
    }
    // return previous (should be EOF)
    return &p->ts.tokens[p->pos - 1];
}

/// Peek second next token without consuming it
Token* parser_peek_second(Parser* p) {
    Token* tok = ts_get(&p->ts, p->pos + 1);
    if (tok != NULL) {
        return tok;
    }
    // return previous (should be EOF)
    return &p->ts.tokens[p->pos - 1];
}

/// Check whether next token matches expected type or not
bool parser_check(Parser* p, TokenType expected) {
    return parser_peek(p)->type == expected;
}

/// Check whether next token matches one of the expected types or not
bool parser_check_two(Parser* p, TokenType first, TokenType second) {
    TokenType peeked = parser_peek(p)->type;
    return peeked == first || peeked == second;
}

/// Move to the next token
Token parser_bump(Parser* p) {
    if (p->pos < p->ts.count) {
        p->pos++;
    }
    return p->ts.tokens[p->pos - 1];
}

#define emit_parser_error(p, message, ...)                    \
    do {                                                      \
        printf("syntax error: " message "\n", ##__VA_ARGS__); \
        diagnose((p)->input, parser_peek((p))->span);         \
        (p)->errors_count++;                                  \
    } while (0)

AST_Node* parse_expr(Parser* p);

AST_Node* parse_primary(Parser* p) {
    if (parser_check(p, TOK_NUMBER)) {
        Token number = parser_bump(p);

        char lexeme[number.span.len + 1];
        get_lexeme(number.view, lexeme, number.span.len);

        char* endptr;
        double value = strtod(lexeme, &endptr);

        if (endptr[0] != EOF_CHAR) {
            emit_parser_error(p, "failed to parse number");
            return NULL;
        }
        return ast_node_lit(value, number.span);
    }

    if (parser_check(p, TOK_IDENT)) {
        Token name = parser_bump(p);
        return ast_node_var_access(name);
    }

    if (parser_check(p, TOK_OPENPAR)) {
        Token openpar = parser_bump(p);
        AST_Node* inner = parse_expr(p);
        if (!parser_check(p, TOK_CLOSEPAR)) {
            emit_parser_error(p, "expected `)` after expression");
            return NULL;
        }
        Token closepar = parser_bump(p);
        Span span = {
            .start = openpar.span.start,
            .len = span_end(closepar.span) - openpar.span.start,
        };
        return ast_node_grouping(inner, span);
    }

    if (p->errors_count == 0) {
        emit_parser_error(p, "expected expression");
    }
    return NULL;
}

AST_Node* finish_fn_call(Parser* p, AST_Node* callee) {
    uint8_t args_count = 0;
    size_t capacity = 10;

    size_t size = sizeof(AST_Node*) * capacity;
    AST_Node** args = malloc(size);
    check_alloc(args, size);

    if (!parser_check(p, TOK_CLOSEPAR)) {
        TokenType last_consumed = TOK_UNKNOWN;
        do {
            AST_Node* arg = parse_expr(p);
            if (arg == NULL) {
                emit_parser_error(p, "expected function arguments");
                return NULL;
            }
            if (args_count > FN_MAX_PARAMS) {
                emit_parser_error(
                    p, "function cannot accept more that %zu arguments", FN_MAX_PARAMS
                );
            }
            if (args_count >= capacity) {
                capacity *= 2;
                size = sizeof(AST_Node*) * capacity;
                args = realloc(args, size);
                check_alloc(args, size);
            }
            args[args_count] = arg;
            args_count++;

            if (parser_check(p, TOK_CLOSEPAR)) {
                break;
            }
            if (!parser_check(p, TOK_COMMA)) {
                emit_parser_error(p, "expected `,` after argument");
                return NULL;
            }
            last_consumed = parser_bump(p).type;

        } while (last_consumed == TOK_COMMA);
    }
    if (!parser_check(p, TOK_CLOSEPAR)) {
        emit_parser_error(p, "expected `)` after function arguments");
        return NULL;
    }
    Token closepar = parser_bump(p);
    Span span = {
        .start = callee->span.start,
        .len = span_end(closepar.span) - callee->span.start,
    };
    return ast_node_fn_call(args, callee, args_count, span);
}

AST_Node* parse_fn_call(Parser* p) {
    AST_Node* callee = parse_primary(p);
    while (parser_check(p, TOK_OPENPAR)) {
        parser_bump(p);
        callee = finish_fn_call(p, callee);
    }
    return callee;
}

AST_Node* parse_power(Parser* p) {
    AST_Node* expr = parse_fn_call(p);

    if (parser_check(p, TOK_STARSTAR)) {
        Token op = parser_bump(p);
        AST_Node* right = parse_power(p);
        if (right == NULL) {
            return NULL;
        }
        return ast_node_bin(expr, op, right);
    }

    return expr;
}

AST_Node* parse_unary(Parser* p) {
    if (parser_check(p, TOK_MINUS)) {
        Token op = parser_bump(p);
        AST_Node* right = parse_unary(p);
        if (right == NULL) {
            return NULL;
        }
        return ast_node_unary(op, right);
    }

    return parse_power(p);
}

AST_Node* parse_factor(Parser* p) {
    AST_Node* left = parse_unary(p);

    while (parser_check_two(p, TOK_STAR, TOK_SLASH)) {
        Token op = parser_bump(p);
        AST_Node* right = parse_unary(p);
        if (right == NULL) {
            return NULL;
        }
        left = ast_node_bin(left, op, right);
    }

    return left;
}

AST_Node* parse_term(Parser* p) {
    AST_Node* left = parse_factor(p);

    while (parser_check_two(p, TOK_PLUS, TOK_MINUS)) {
        Token op = parser_bump(p);
        AST_Node* right = parse_factor(p);
        if (right == NULL) {
            return NULL;
        }
        left = ast_node_bin(left, op, right);
    }

    return left;
}

AST_Node* parse_var_def(Parser* p) {
    if (parser_check(p, TOK_IDENT) && parser_peek_second(p)->type == TOK_EQ) {
        Token name = parser_bump(p);
        parser_bump(p);

        AST_Node* value = parse_expr(p);
        if (value == NULL) {
            return NULL;
        }
        return ast_node_var_def(name, value);
    }
    return parse_term(p);
}

AST_Node* parse_fn_def(Parser* p) {
    if (parser_check(p, TOK_DOLLAR)) {
        Token dollar = parser_bump(p);

        Token name = {0};
        bool is_anon = true;

        if (parser_check(p, TOK_IDENT)) {
            name = parser_bump(p);
            is_anon = false;
        }

        if (!parser_check(p, TOK_OPENPAR)) {
            emit_parser_error(p, "expected `(` before function parameters");
            return NULL;
        }
        parser_bump(p);

        size_t capacity = 10;
        uint8_t arity = 0;
        size_t size = sizeof(Token) * capacity;
        Token* params = malloc(size);
        check_alloc(params, size);

        while (parser_check(p, TOK_IDENT)) {
            if (arity > FN_MAX_PARAMS) {
                emit_parser_error(
                    p, "function definition cannot have more that %zu parameters", FN_MAX_PARAMS
                );
                return NULL;
            }
            if (arity >= capacity) {
                capacity *= 2;
                size = sizeof(Token) * capacity;
                params = realloc(params, size);
                check_alloc(params, size);
            }
            params[arity] = parser_bump(p);
            arity++;

            if (parser_check(p, TOK_CLOSEPAR)) {
                break;
            }
            if (parser_check(p, TOK_COLON)) {
                emit_parser_error(p, "expected `)` before function body");
                return NULL;
            }
            if (!parser_check(p, TOK_COMMA)) {
                emit_parser_error(p, "expected `,` after parameter");
                return NULL;
            }
            // eat comma
            parser_bump(p);
        }

        if (!parser_check(p, TOK_CLOSEPAR)) {
            emit_parser_error(p, "expected closing `)`");
            return NULL;
        }
        parser_bump(p);

        if (!parser_check(p, TOK_COLON)) {
            emit_parser_error(p, "expected `:` before function body");
            return NULL;
        }
        parser_bump(p);

        AST_Node* body = parse_expr(p);
        if (body == NULL) {
            emit_parser_error(p, "expected function body");
            return NULL;
        }
        Span span = {
            .start = dollar.span.start,
            .len = span_end(body->span) - dollar.span.start,
        };
        Func fn_def = {
            .params = params,
            .name = name,
            .body = body,
            .arity = arity,
            .is_anon = is_anon,
            .orig_input = p->input,
        };
        return ast_node_fn_def(fn_def, span);
    }

    return parse_var_def(p);
}

AST_Node* parse_expr(Parser* p) {
    return parse_fn_def(p);
}

/// Parse token stream and produce syntax tree for it
AST_Node* parse(Parser* p) {
    AST_Node* parsed_expression = parse_expr(p);

    if (!parser_check(p, TOK_EOF) && p->errors_count == 0) {
        // report trailing tokens if there was no errors before
        Token first = parser_bump(p);
        Token last = first; // if there is no more tokens, then the
                            // first trailing is also the last one

        while (!parser_check(p, TOK_EOF)) {
            last = parser_bump(p);
        }

        Span span = {
            .start = first.span.start,
            .len = (last.span.start - first.span.start) + last.span.len,
        };
        printf("syntax error: unexpected trailing tokens\n");
        diagnose(p->input, span);
        p->errors_count++;
    }

    // return whatever we parsed
    return parsed_expression;
}

// *****************************************
//  ************* INTERPRETER *************
// *****************************************

void assert_node(AST_Node* node) {
    assert(
        node != NULL
        && "Empty nodes are error nodes.\n"
           "They should be handled before walking the AST"
    );
}

void print_indent(size_t depth) {
    for (size_t i = 0; i < depth; i++) {
        printf("    ");
    }
}

void print_node(AST_Node* node, size_t depth) {
    assert_node(node);

    switch (node->type) {
        case AST_NODE_GROUPING: {
            printf("Grouping {\n");

            print_indent(depth + 1);
            printf("expr = ");
            print_node(node->as.grouping.node, depth + 1);

            print_indent(depth);
            printf("},\n");
            return;
        }
        case AST_NODE_BIN: {
            printf("Binary {\n");

            AST_Node* left = node->as.bin.left;
            Token op = node->as.bin.op;
            AST_Node* right = node->as.bin.right;

            print_indent(depth + 1);
            printf("left = ");
            print_node(left, depth + 1);

            print_indent(depth + 1);
            print_token("op = ", &op, ",");

            print_indent(depth + 1);
            printf("right = ");
            print_node(right, depth + 1);

            print_indent(depth);
            printf("},\n");
            return;
        }
        case AST_NODE_UNARY: {
            printf("Unary {\n");

            Token op = node->as.unary.op;
            AST_Node* right = node->as.unary.right;

            print_indent(depth + 1);
            print_token("op = ", &op, ",");

            print_indent(depth + 1);
            printf("right = ");
            print_node(right, depth + 1);

            print_indent(depth);
            printf("},\n");
            return;
        }
        case AST_NODE_LIT: {
            printf("%f,\n", node->as.lit.value);
            return;
        }
        case AST_NODE_VAR_DEF: {
            printf("VarDef {\n");

            print_indent(depth + 1);
            print_token("name = ", &node->as.var_def.name, ",");

            print_indent(depth + 1);
            printf("value = ");
            print_node(node->as.var_def.value, depth + 1);

            print_indent(depth);
            printf("},\n");
            return;
        }
        case AST_NODE_VAR_ACCESS: {
            printf("VarAccess {\n");

            print_indent(depth + 1);
            print_token("name = ", &node->as.var_access.name, ",");

            print_indent(depth);
            printf("},\n");
            return;
        }
        case AST_NODE_FN_DEF: {
            printf("FnDef {\n");

            if (!node->as.fn_def.is_anon) {
                print_indent(depth + 1);
                print_token("name = ", &node->as.fn_def.name, ",");
            }

            print_indent(depth + 1);
            printf("params = [\n");
            for (size_t i = 0; i < node->as.fn_def.arity; i++) {
                Token param = node->as.fn_def.params[i];
                char lexeme[param.span.len + 1];
                get_lexeme(param.view, lexeme, param.span.len);

                print_indent(depth + 2);
                printf("%s,\n", lexeme);
            }
            print_indent(depth + 1);
            printf("],\n");

            print_indent(depth + 1);
            printf("arity = %d,\n", node->as.fn_def.arity);

            print_indent(depth + 1);
            printf("body = ");
            print_node(node->as.fn_def.body, depth + 1);

            print_indent(depth + 1);
            printf("is_anon = %d,\n", node->as.fn_def.is_anon);

            print_indent(depth);
            printf("},\n");
            return;
        }
        case AST_NODE_FN_CALL: {
            printf("FnCall {\n");

            print_indent(depth + 1);
            printf("callee = ");
            print_node(node->as.fn_call.callee, depth + 1);

            print_indent(depth + 1);
            printf("args = [\n");
            for (size_t i = 0; i < node->as.fn_call.args_count; i++) {
                AST_Node* arg = node->as.fn_call.args[i];
                if (arg == NULL) {
                    break;
                }
                print_indent(depth + 2);
                print_node(arg, depth + 2);
            }
            print_indent(depth + 1);
            printf("],\n");

            print_indent(depth);
            printf("},\n");
            return;
        }
        default:
            exit_fatal("Unexpected AST node type: %d", node->type);
            return;
    }
}

uint64_t fnv1a_hash(char* str) {
    static const uint64_t FNV_32_PRIME = 0x01000193;
    uint64_t hash = 0x811c9dc5;
    while (*str) {
        hash ^= (uint64_t)(*str);
        hash *= FNV_32_PRIME;
        str++;
    }
    return hash;
}

typedef enum {
    OBJ_NUMBER,
    OBJ_FN,
    OBJ_ERROR,
} ObjectType;

typedef struct {
    union {
        double number;
        Func fn;
    } as;

    ObjectType type;
} Object;

static const Object ERR_OBJECT = {
    .type = OBJ_ERROR,
};

Object object_number(double number) {
    Object obj;
    obj.as.number = number;
    obj.type = OBJ_NUMBER;
    return obj;
}

Object object_fn(Func fn) {
    Object obj;
    obj.as.fn = fn;
    obj.type = OBJ_FN;
    return obj;
}

typedef struct {
    uint64_t hash;
    Object value;
} Name;

typedef struct {
    Name* names;
    size_t count;
    size_t capacity;
} NameMap;

NameMap nm_alloc(size_t capacity) {
    NameMap nm = {0};
    assert(capacity > 0);

    nm.count = 0;
    nm.capacity = capacity;

    size_t size = capacity * sizeof(Name);
    Name* names = malloc(size);
    check_alloc(names, size);
    nm.names = names;
    return nm;
}

void nm_set(NameMap* nm, Name name) {
    if (nm->count >= nm->capacity) {
        size_t capacity = nm->capacity * 2;
        size_t size = capacity * sizeof(Name);

        Name* names = realloc(nm->names, size);
        check_alloc(names, size);
        nm->names = names;
        nm->capacity = capacity;
    }
    for (size_t i = 0; i < nm->count; i++) {
        if (nm->names[i].hash == name.hash) {
            nm->names[i] = name;
            return;
        }
    }
    nm->names[nm->count++] = name;
}

Object* nm_find(NameMap* nm, uint64_t hash) {
    for (size_t i = 0; i < nm->count; i++) {
        if (nm->names[i].hash == hash) {
            return &nm->names[i].value;
        }
    }
    return NULL;
}

void nm_free(NameMap* nm) {
    free(nm->names);
    nm->names = NULL;
    nm->count = 0;
    nm->capacity = 0;
}

typedef struct {
    NameMap* nm;
    char* input;
    size_t errors_count;
} Interp;

#define emit_interp_error(interp, span, message, ...)          \
    do {                                                       \
        printf("runtime error: " message "\n", ##__VA_ARGS__); \
        diagnose((interp)->input, (span));                     \
        (interp)->errors_count++;                              \
    } while (0)

char* format_object(Object object) {
    size_t size = 64;
    char* buf = malloc(size);
    check_alloc(buf, size);

    switch (object.type) {
        case OBJ_NUMBER: {
            snprintf(buf, size, "%.16g", object.as.number);
            return buf;
        }
        case OBJ_FN: {
            Func fn = object.as.fn;

            if (!fn.is_anon) {
                char name[fn.name.span.len + 1];
                get_lexeme(fn.name.view, name, fn.name.span.len);
                snprintf(buf, size, "<function '%s' at %p>", name, (void*)fn.params);
            }
            else {
                snprintf(buf, size, "<anonymous function at %p>", (void*)fn.params);
            }
            return buf;
        }
        case OBJ_ERROR: {
            snprintf(buf, size, "<error object>");
            return buf;
        }
        default: {
            exit_fatal("unexpected type of object: %d", object.type);
        }
    }
}

Object eval(Interp* interp, AST_Node* node, size_t recursion) {
    assert_node(node);

    if (interp->errors_count != 0) {
        return ERR_OBJECT;
    }
    if (recursion >= RECURSION_LIMIT) {
        emit_interp_error(interp, node->span, "recursion limit exceeded (%zu)", RECURSION_LIMIT);
        return ERR_OBJECT;
    }
    switch (node->type) {
        case AST_NODE_GROUPING: {
            return eval(interp, node->as.grouping.node, recursion);
        }
        case AST_NODE_BIN: {
            Object left_obj = eval(interp, node->as.bin.left, recursion);
            Object right_obj = eval(interp, node->as.bin.right, recursion);

            if (left_obj.type != OBJ_NUMBER || right_obj.type != OBJ_NUMBER) {
                if (left_obj.type != OBJ_ERROR || right_obj.type != OBJ_ERROR) {
                    emit_interp_error(
                        interp, node->span, "binary operations are supported only on numbers"
                    );
                    if (left_obj.type != OBJ_NUMBER) {
                        char* fmt = format_object(left_obj);
                        printf("note: this is a %s\n", fmt);
                        diagnose(interp->input, node->as.bin.left->span);
                        free(fmt);
                    }
                    if (right_obj.type != OBJ_NUMBER) {
                        char* fmt = format_object(right_obj);
                        printf("note: this is a %s\n", fmt);
                        diagnose(interp->input, node->as.bin.right->span);
                        free(fmt);
                    }
                }
                return ERR_OBJECT;
            }
            double left = left_obj.as.number;
            double right = right_obj.as.number;

            switch (node->as.bin.op.type) {
                case TOK_PLUS: {
                    return object_number(left + right);
                }
                case TOK_MINUS: {
                    return object_number(left - right);
                }
                case TOK_STAR: {
                    return object_number(left * right);
                }
                case TOK_STARSTAR: {
                    return object_number(pow(left, right));
                }
                case TOK_SLASH: {
                    return object_number(left / right);
                }
                default: {
                    emit_interp_error(interp, node->as.bin.op.span, "bad binary operator");
                    return ERR_OBJECT;
                }
            }
        }
        case AST_NODE_UNARY: {
            Object right_obj = eval(interp, node->as.unary.right, recursion);
            if (right_obj.type != OBJ_NUMBER) {
                if (right_obj.type != OBJ_ERROR) {
                    emit_interp_error(
                        interp, node->span, "unary operations are supported only on numbers"
                    );
                    char* fmt = format_object(right_obj);
                    printf("note: this is a %s\n", fmt);
                    diagnose(interp->input, node->as.unary.right->span);
                    free(fmt);
                }
                return ERR_OBJECT;
            }
            double right = right_obj.as.number;

            switch (node->as.unary.op.type) {
                case TOK_MINUS: {
                    return object_number(-right);
                }
                default: {
                    emit_interp_error(interp, node->as.bin.op.span, "bad unary operator");
                    return ERR_OBJECT;
                }
            }
        }
        case AST_NODE_LIT: {
            return object_number(node->as.lit.value);
        }
        case AST_NODE_VAR_DEF: {
            Token name_tok = node->as.var_def.name;
            char lexeme[name_tok.span.len + 1];
            get_lexeme(name_tok.view, lexeme, name_tok.span.len);

            Object value = eval(interp, node->as.var_def.value, recursion);
            Name name = {
                .hash = fnv1a_hash(lexeme),
                .value = value,
            };
            nm_set(interp->nm, name);
            return value;
        }
        case AST_NODE_VAR_ACCESS: {
            Token name_tok = node->as.var_access.name;
            char lexeme[name_tok.span.len + 1];
            get_lexeme(name_tok.view, lexeme, name_tok.span.len);

            Object* value = nm_find(interp->nm, fnv1a_hash(lexeme));
            if (value == NULL) {
                emit_interp_error(interp, name_tok.span, "\"%s\" is undefined", lexeme);
                return ERR_OBJECT;
            }
            return *value;
        }
        case AST_NODE_FN_DEF: {
            Func fn = node->as.fn_def;
            Object fn_obj = object_fn(fn);

            if (!fn.is_anon) {
                Token name_tok = fn.name;
                char lexeme[name_tok.span.len + 1];
                get_lexeme(name_tok.view, lexeme, name_tok.span.len);
                Name name = {
                    .hash = fnv1a_hash(lexeme),
                    .value = fn_obj,
                };
                nm_set(interp->nm, name);
            }
            return fn_obj;
        }
        case AST_NODE_FN_CALL: {
            Object callee_obj = eval(interp, node->as.fn_call.callee, recursion);
            if (callee_obj.type != OBJ_FN) {
                if (callee_obj.type == OBJ_ERROR) {
                    // error about callee was already reported
                    return ERR_OBJECT;
                }
                emit_interp_error(interp, node->as.fn_call.callee->span, "not a function");
                return ERR_OBJECT;
            }
            Func callee = callee_obj.as.fn;

            if (node->as.fn_call.args_count != callee.arity) {
                emit_interp_error(
                    interp,
                    node->span,
                    "function expected %d arguments, got %d",
                    callee.arity,
                    node->as.fn_call.args_count
                );
            }

            NameMap local_nm = nm_alloc(interp->nm->count + 1);
            // set existing global names
            for (size_t i = 0; i < interp->nm->count; i++) {
                nm_set(&local_nm, interp->nm->names[i]);
            }
            // set arguments only for function body
            for (size_t i = 0; i < node->as.fn_call.args_count; i++) {
                AST_Node* arg_node = node->as.fn_call.args[i];
                Object arg = eval(interp, arg_node, recursion);

                Token param = callee.params[i];
                char arg_name[param.span.len + 1];
                get_lexeme(param.view, arg_name, param.span.len);

                Name name = {
                    .hash = fnv1a_hash(arg_name),
                    .value = arg,
                };
                nm_set(&local_nm, name);
            }

            Interp local_interp = {
                .nm = &local_nm,
                .input = callee.orig_input,
                .errors_count = interp->errors_count,
            };
            Object result = eval(&local_interp, callee.body, recursion + 1);
            interp->errors_count += local_interp.errors_count;
            return result;
        }
        default: {
            exit_fatal("unexpected syntax tree node");
        }
    }
}

// **************************************************
//  ************* READ-EVAL-PRINT-LOOP *************
// **************************************************

AST_Node* handle_input(char* input, NameMap* nm) {
    Lexer lex = {
        .input = input,
        .input_len = strlen(input),
        .pos = 0,
    };
    TokenStream ts = ts_alloc(128);

    while (true) {
        Token tok = lex_next_token(&lex);
        ts_push(&ts, tok);

        if (tok.type == TOK_UNKNOWN) {
            emit_lexer_error(&lex, tok.span, "unknown token");
        }
        else if (tok.type == TOK_EOF) {
            break;
        }
    }
    if (lex.errors_count != 0) {
        ts_free(&ts);
        return NULL;
    }

    Parser parser = {
        .ts = ts,
        .pos = 0,
        .input = input,
    };
    AST_Node* root = parse(&parser);
    if (parser.errors_count == 0) {
        Interp interp = {
            .nm = nm,
            .input = input,
            .errors_count = 0,
        };
        Object result = eval(&interp, root, 0);

        if (interp.errors_count == 0) {
            char* fmt = format_object(result);
            printf("%s\n", fmt);
            free(fmt);
        }
    }

    ts_free(&ts);
    return root;
}

/// Accumulates all "roots" that were produced by parser during using of the program,
/// and clears them recursively before exiting
typedef struct {
    AST_Node** nodes;
    size_t count;
    size_t capacity;
} AST_Burden;

AST_Burden burden_alloc(size_t capacity) {
    AST_Burden burden = {0};
    assert(capacity > 0);

    burden.count = 0;
    burden.capacity = capacity;

    size_t size = capacity * sizeof(AST_Node*);
    AST_Node** nodes = malloc(size);
    check_alloc(nodes, size);
    burden.nodes = nodes;
    return burden;
}

void burden_push(AST_Burden* burden, AST_Node* node) {
    if (burden->count >= burden->capacity) {
        size_t capacity = burden->capacity * 2;
        size_t size = capacity * sizeof(AST_Node*);

        AST_Node** nodes = realloc(burden->nodes, size);
        check_alloc(nodes, size);
        burden->nodes = nodes;
        burden->capacity = capacity;
    }
    burden->nodes[burden->count++] = node;
}

void burden_free(AST_Burden* burden) {
    for (size_t i = 0; i < burden->count; i++) {
        ast_node_free(burden->nodes[i]);
    }
    free(burden->nodes);
    burden->nodes = NULL;
    burden->count = 0;
    burden->capacity = 0;
}

int main(void) {
    char* input;
    NameMap nm = nm_alloc(32);
    AST_Burden burden = burden_alloc(32);

    while ((input = readline("> ")) != NULL) {
        if (*input == EOF_CHAR) {
            continue;
        }
        if (strcmp("!exit", input) == 0) {
            break;
        }
        add_history(input);

        AST_Node* node = handle_input(input, &nm);
        if (node != NULL) {
            // accumulate node to free later
            burden_push(&burden, node);
        }
    }

    free(input);
    nm_free(&nm);
    burden_free(&burden);
}
