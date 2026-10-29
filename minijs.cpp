// minijs.cpp - a minimal terminal-based compiler + VM for a subset of JavaScript, in C++17
//
// Pipeline: Source -> Lexer -> Parser (AST) -> Semantic check + Codegen (bytecode) -> Stack VM
//
// Build:  g++ -O2 -std=c++17 -o minijs minijs.cpp
// Usage:  ./minijs <file.js> [--tokens] [--ast] [--bytecode] [--no-run]

#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <map>
#include <memory>
#include <set>
#include <sstream>
#include <string>
#include <vector>
using namespace std;

struct CompileError { string phase, msg; int line, col; };

/* ============================ Runtime values ============================ */
struct Value {
    enum T { UNDEF, NUL, NUM, BOOL, STR } t = UNDEF;
    double n = 0;   // number, or 0/1 for booleans
    string s;       // string payload
    static Value num(double d) { Value v; v.t = NUM; v.n = d; return v; }
    static Value boolean(bool b) { Value v; v.t = BOOL; v.n = b; return v; }
    static Value str(const string& x) { Value v; v.t = STR; v.s = x; return v; }
    static Value null() { Value v; v.t = NUL; return v; }
};

// JS-style number formatting: 5 -> "5", 0.1 -> "0.1", 1/0 -> "Infinity"
string numToStr(double d) {
    if (std::isnan(d)) return "NaN";
    if (std::isinf(d)) return d < 0 ? "-Infinity" : "Infinity";
    if (d == 0) return "0";
    char buf[64];
    if (d == std::floor(d) && std::fabs(d) < 1e21) { snprintf(buf, sizeof buf, "%.0f", d); return buf; }
    for (int p = 1; p <= 17; p++) {               // shortest representation that round-trips
        snprintf(buf, sizeof buf, "%.*g", p, d);
        if (strtod(buf, nullptr) == d) break;
    }
    return buf;
}
string toStr(const Value& v) {
    switch (v.t) {
        case Value::UNDEF: return "undefined";
        case Value::NUL: return "null";
        case Value::NUM: return numToStr(v.n);
        case Value::BOOL: return v.n ? "true" : "false";
        default: return v.s;
    }
}
double toNum(const Value& v) {
    switch (v.t) {
        case Value::UNDEF: return NAN;
        case Value::NUL: return 0;
        case Value::NUM: case Value::BOOL: return v.n;
        default: {
            if (v.s.empty()) return 0;
            char* end; double d = strtod(v.s.c_str(), &end);
            return *end == '\0' ? d : NAN;
        }
    }
}
bool truthy(const Value& v) {
    switch (v.t) {
        case Value::UNDEF: case Value::NUL: return false;
        case Value::NUM: return !(v.n == 0 || std::isnan(v.n));
        case Value::BOOL: return v.n != 0;
        default: return !v.s.empty();
    }
}
bool strictEq(const Value& a, const Value& b) {
    if (a.t != b.t) return false;
    switch (a.t) {
        case Value::UNDEF: case Value::NUL: return true;
        case Value::NUM: case Value::BOOL: return a.n == b.n;
        default: return a.s == b.s;
    }
}

/* ============================ 1. LEXER ============================ */
enum TT { T_NUM, T_STR, T_ID, T_KW, T_OP, T_EOF };
const char* TTN[] = {"num", "str", "id", "kw", "op", "eof"};
struct Token { TT type; string text; double num = 0; int line = 0, col = 0; };

static const set<string> KEYWORDS = {"let", "const", "var", "function", "return", "if", "else",
                                     "while", "for", "true", "false", "null"};
// longest operators first, so "===" is matched before "=="
static const vector<string> OPS = {"===", "!==", "==", "!=", "<=", ">=", "&&", "||", "++", "--",
                                   "+=", "-=", "*=", "/=", "+", "-", "*", "/", "%", "<", ">", "=",
                                   "!", "(", ")", "{", "}", ",", ";", "."};

vector<Token> lex(const string& src) {
    vector<Token> toks;
    size_t i = 0; int line = 1, col = 1;
    auto adv = [&](size_t n = 1) {
        for (size_t k = 0; k < n && i < src.size(); k++) {
            if (src[i] == '\n') { line++; col = 1; } else col++;
            i++;
        }
    };
    while (i < src.size()) {
        char c = src[i];
        if (isspace((unsigned char)c)) { adv(); continue; }
        if (c == '/' && i + 1 < src.size() && src[i + 1] == '/') {          // line comment
            while (i < src.size() && src[i] != '\n') adv();
            continue;
        }
        if (c == '/' && i + 1 < src.size() && src[i + 1] == '*') {          // block comment
            int sl = line, sc = col; adv(2);
            while (i < src.size() && !(src[i] == '*' && i + 1 < src.size() && src[i + 1] == '/')) adv();
            if (i >= src.size()) throw CompileError{"Lexical", "Unterminated comment", sl, sc};
            adv(2); continue;
        }
        Token t; t.line = line; t.col = col;
        if (isdigit((unsigned char)c)) {
            string s; int dots = 0;
            while (i < src.size() && (isdigit((unsigned char)src[i]) || src[i] == '.')) {
                if (src[i] == '.') dots++;
                s += src[i]; adv();
            }
            if (dots > 1) throw CompileError{"Lexical", "Malformed number '" + s + "'", t.line, t.col};
            t.type = T_NUM; t.text = s; t.num = strtod(s.c_str(), nullptr);
            toks.push_back(t); continue;
        }
        if (isalpha((unsigned char)c) || c == '_' || c == '$') {
            string s;
            while (i < src.size() && (isalnum((unsigned char)src[i]) || src[i] == '_' || src[i] == '$')) { s += src[i]; adv(); }
            t.type = KEYWORDS.count(s) ? T_KW : T_ID; t.text = s;
            toks.push_back(t); continue;
        }
        if (c == '"' || c == '\'') {
            char q = c; string s; adv();
            while (i < src.size() && src[i] != q && src[i] != '\n') {
                if (src[i] == '\\') {
                    adv();
                    if (i >= src.size()) break;
                    switch (src[i]) { case 'n': s += '\n'; break; case 't': s += '\t'; break; default: s += src[i]; }
                } else s += src[i];
                adv();
            }
            if (i >= src.size() || src[i] != q) throw CompileError{"Lexical", "Unterminated string", t.line, t.col};
            adv();
            t.type = T_STR; t.text = s;
            toks.push_back(t); continue;
        }
        bool matched = false;
        for (const string& o : OPS) {
            if (src.compare(i, o.size(), o) == 0) {
                adv(o.size()); t.type = T_OP; t.text = o; toks.push_back(t); matched = true; break;
            }
        }
        if (matched) continue;
        throw CompileError{"Lexical", string("Unexpected character '") + c + "'", line, col};
    }
    Token e; e.type = T_EOF; e.text = "<eof>"; e.line = line; e.col = col;
    toks.push_back(e);
    return toks;
}

/* ============================ 2. AST + PARSER ============================ */
enum Kind { K_PROGRAM, K_FUNC, K_BLOCK, K_VARDECL, K_DECL, K_IF, K_WHILE, K_FOR, K_RETURN,
            K_EXPRSTMT, K_LIT, K_ID, K_ASSIGN, K_BINARY, K_LOGICAL, K_UNARY, K_CALL };
const char* KN[] = {"Program", "Function", "Block", "VarDecl", "Decl", "If", "While", "For", "Return",
                    "ExprStmt", "Literal", "Id", "Assign", "Binary", "Logical", "Unary", "Call"};

struct Node;
using NP = unique_ptr<Node>;
struct Node {
    Kind kind;
    string str;              // name / operator / declaration kind
    Value v;                 // literal value
    vector<NP> ch;           // children (may contain nullptr for optional parts)
    vector<string> params;   // function parameters
    int line, col;
    Node(Kind k, int l = 0, int c = 0) : kind(k), line(l), col(c) {}
};
NP mk(Kind k, int l = 0, int c = 0) { return make_unique<Node>(k, l, c); }

/*
 * program    -> (function | statement)* EOF
 * statement  -> varDecl | if | while | for | return | block | exprStmt
 * assignment -> binary(0) [ ('='|'+='|...) assignment ]
 * binary     -> precedence climbing over LEVELS (|| lowest ... * / % highest)
 * unary      -> ('-'|'!'|'++'|'--') unary | postfix
 * postfix    -> call ['++'|'--']
 * call       -> primary ( '(' args ')' )*
 * primary    -> NUM | STR | true | false | null | ID | console.log | '(' expression ')'
 */
static const vector<vector<string>> LEVELS = {{"||"}, {"&&"}, {"===", "!==", "==", "!="},
                                               {"<", ">", "<=", ">="}, {"+", "-"}, {"*", "/", "%"}};

class Parser {
    vector<Token> t; size_t p = 0;
    Token& cur() { return t[p]; }
    bool is(const string& v) { auto& c = t[p]; return (c.type == T_OP || c.type == T_KW) && c.text == v; }
    bool eat(const string& v) { if (is(v)) { p++; return true; } return false; }
    [[noreturn]] void fail(const string& m) { throw CompileError{"Syntax", m, cur().line, cur().col}; }
    Token expect(const string& v) {
        if (!is(v)) fail("Expected '" + v + "' but found '" + cur().text + "'");
        return t[p++];
    }
    Token ident() {
        if (cur().type != T_ID) fail("Expected identifier but found '" + cur().text + "'");
        return t[p++];
    }
    bool isDeclKw() { return is("let") || is("const") || is("var"); }

public:
    explicit Parser(vector<Token> toks) : t(move(toks)) {}

    NP program() {
        auto n = mk(K_PROGRAM);
        while (cur().type != T_EOF) n->ch.push_back(is("function") ? funcDecl() : statement());
        return n;
    }
    NP funcDecl() {
        Token kw = expect("function"), name = ident();
        auto n = mk(K_FUNC, kw.line, kw.col); n->str = name.text;
        expect("(");
        if (!is(")")) { do n->params.push_back(ident().text); while (eat(",")); }
        expect(")");
        n->ch.push_back(block());
        return n;
    }
    NP block() {
        expect("{");
        auto n = mk(K_BLOCK);
        while (!is("}")) {
            if (cur().type == T_EOF) fail("Expected '}' before end of file");
            if (is("function")) fail("Nested functions are not supported in minijs");
            n->ch.push_back(statement());
        }
        expect("}");
        return n;
    }
    NP statement() {
        Token c = cur();
        if (isDeclKw()) return varDecl(true);
        if (is("{")) return block();
        if (eat("if")) {
            auto n = mk(K_IF, c.line, c.col);
            expect("("); n->ch.push_back(expression()); expect(")");
            n->ch.push_back(statement());
            n->ch.push_back(eat("else") ? statement() : nullptr);
            return n;
        }
        if (eat("while")) {
            auto n = mk(K_WHILE, c.line, c.col);
            expect("("); n->ch.push_back(expression()); expect(")");
            n->ch.push_back(statement());
            return n;
        }
        if (eat("for")) {
            auto n = mk(K_FOR, c.line, c.col);
            expect("(");
            NP init;
            if (isDeclKw()) init = varDecl(false);
            else if (!is(";")) { init = mk(K_EXPRSTMT); init->ch.push_back(expression()); }
            expect(";");
            NP test; if (!is(";")) test = expression();
            expect(";");
            NP upd; if (!is(")")) upd = expression();
            expect(")");
            n->ch.push_back(move(init)); n->ch.push_back(move(test)); n->ch.push_back(move(upd));
            n->ch.push_back(statement());
            return n;
        }
        if (eat("return")) {
            auto n = mk(K_RETURN, c.line, c.col);
            if (is(";") || is("}") || cur().type == T_EOF) n->ch.push_back(nullptr);
            else n->ch.push_back(expression());
            eat(";");
            return n;
        }
        auto n = mk(K_EXPRSTMT, c.line, c.col);
        n->ch.push_back(expression());
        eat(";");
        return n;
    }
    NP varDecl(bool semi) {
        Token kw = t[p++];
        auto n = mk(K_VARDECL, kw.line, kw.col); n->str = kw.text;
        do {
            Token id = ident();
            auto d = mk(K_DECL, id.line, id.col); d->str = id.text;
            d->ch.push_back(eat("=") ? expression() : nullptr);
            n->ch.push_back(move(d));
        } while (eat(","));
        if (semi) eat(";");
        return n;
    }
    NP expression() { return assignment(); }
    NP assignment() {
        NP left = binary(0);
        Token c = cur();
        if (c.type == T_OP && (c.text == "=" || c.text == "+=" || c.text == "-=" || c.text == "*=" || c.text == "/=")) {
            if (left->kind != K_ID) throw CompileError{"Syntax", "Invalid assignment target", c.line, c.col};
            p++;
            NP value = assignment();
            if (c.text != "=") {   // x += e   ==>   x = x + e
                auto bin = mk(K_BINARY, c.line, c.col); bin->str = string(1, c.text[0]);
                auto copy = mk(K_ID, left->line, left->col); copy->str = left->str;
                bin->ch.push_back(move(copy)); bin->ch.push_back(move(value));
                value = move(bin);
            }
            auto as = mk(K_ASSIGN, left->line, left->col); as->str = left->str;
            as->ch.push_back(move(value));
            return as;
        }
        return left;
    }
    NP binary(size_t level) {
        if (level == LEVELS.size()) return unary();
        NP left = binary(level + 1);
        for (;;) {
            bool match = false;
            if (cur().type == T_OP) for (auto& o : LEVELS[level]) if (cur().text == o) match = true;
            if (!match) break;
            Token o = t[p++];
            NP right = binary(level + 1);
            auto n = mk((o.text == "&&" || o.text == "||") ? K_LOGICAL : K_BINARY, o.line, o.col);
            n->str = o.text;
            n->ch.push_back(move(left)); n->ch.push_back(move(right));
            left = move(n);
        }
        return left;
    }
    NP unary() {
        Token c = cur();
        if (is("-") || is("!")) {
            p++;
            auto n = mk(K_UNARY, c.line, c.col); n->str = c.text; n->ch.push_back(unary());
            return n;
        }
        if (is("++") || is("--")) { p++; return incdec(unary(), c); }
        NP e = call();
        if (is("++") || is("--")) { Token o = t[p++]; return incdec(move(e), o); }
        return e;
    }
    // i++ / --i are desugared to  i = i + 1   (the expression's value is the NEW value)
    NP incdec(NP target, const Token& tok) {
        if (target->kind != K_ID)
            throw CompileError{"Syntax", "Invalid operand for '" + tok.text + "'", tok.line, tok.col};
        string name = target->str; int l = target->line, c = target->col;
        auto bin = mk(K_BINARY, tok.line, tok.col); bin->str = string(1, tok.text[0]);
        auto one = mk(K_LIT); one->v = Value::num(1);
        bin->ch.push_back(move(target)); bin->ch.push_back(move(one));
        auto as = mk(K_ASSIGN, l, c); as->str = name; as->ch.push_back(move(bin));
        return as;
    }
    NP call() {
        NP e = primary();
        while (is("(")) {
            Token open = t[p++];
            if (e->kind != K_ID) throw CompileError{"Syntax", "Only named functions can be called", open.line, open.col};
            auto n = mk(K_CALL, e->line, e->col); n->str = e->str;
            if (!is(")")) { do n->ch.push_back(expression()); while (eat(",")); }
            expect(")");
            e = move(n);
        }
        return e;
    }
    NP primary() {
        Token c = cur();
        if (c.type == T_NUM) { p++; auto n = mk(K_LIT); n->v = Value::num(c.num); return n; }
        if (c.type == T_STR) { p++; auto n = mk(K_LIT); n->v = Value::str(c.text); return n; }
        if (eat("true"))  { auto n = mk(K_LIT); n->v = Value::boolean(true); return n; }
        if (eat("false")) { auto n = mk(K_LIT); n->v = Value::boolean(false); return n; }
        if (eat("null"))  { auto n = mk(K_LIT); n->v = Value::null(); return n; }
        if (c.type == T_ID && c.text == "undefined") { p++; return mk(K_LIT); }   // Value() == undefined
        if (c.type == T_ID) {
            p++;
            auto n = mk(K_ID, c.line, c.col); n->str = c.text;
            if (c.text == "console") {
                expect(".");
                Token m = ident();
                if (m.text != "log") fail("Only 'console.log' is supported");
                n->str = "console.log";
            }
            return n;
        }
        if (eat("(")) { NP e = expression(); expect(")"); return e; }
        fail("Unexpected token '" + c.text + "'");
    }
};

/* ============ 3. SEMANTIC ANALYSIS + CODE GENERATION (bytecode) ============ */
enum Op { PUSH, LOAD, STORE, POP, DUP, NEG, NOT, ADD, SUB, MUL, DIV, MOD, LT, GT, LE, GE, EQ, NE,
          JMP, JF, JFK, JTK, CALL, RET, PRINT };
const char* OPN[] = {"PUSH", "LOAD", "STORE", "POP", "DUP", "NEG", "NOT", "ADD", "SUB", "MUL", "DIV", "MOD",
                     "LT", "GT", "LE", "GE", "EQ", "NE", "JMP", "JF", "JFK", "JTK", "CALL", "RET", "PRINT"};

struct Instr {
    Op op; int arg = 0; int argc = 0; Value k; string name;
};
struct Fn { string name; vector<Instr> code; int nslots = 0, nparams = 0; };

struct VarInfo { int slot; string kind; };

class Compiler {
    vector<Fn> fns;
    map<string, int> fnIndex, arity;          // function name -> index in fns / parameter count
    Fn cur;
    vector<map<string, VarInfo>> scopes;
    bool isMain = false;

    [[noreturn]] void err(const Node* n, const string& m) { throw CompileError{"Semantic", m, n->line, n->col}; }
    int emit(Op op, int arg = 0) { Instr i; i.op = op; i.arg = arg; cur.code.push_back(i); return (int)cur.code.size() - 1; }
    int here() { return (int)cur.code.size(); }
    void patch(int i) { cur.code[i].arg = here(); }
    void emitNamed(Op op, int arg, const string& name) { emit(op, arg); cur.code.back().name = name; }
    void emitPush(const Value& v) { emit(PUSH); cur.code.back().k = v; }

    VarInfo declare(const string& name, const string& kind, const Node* at) {
        auto& top = scopes.back();
        if (top.count(name)) err(at, "Variable '" + name + "' is already declared in this scope");
        VarInfo vi{cur.nslots++, kind};
        top[name] = vi;
        return vi;
    }
    VarInfo resolve(const string& name, const Node* at) {
        for (int i = (int)scopes.size() - 1; i >= 0; i--) {
            auto it = scopes[i].find(name);
            if (it != scopes[i].end()) return it->second;
        }
        err(at, "Variable '" + name + "' is not declared");
    }

    void compileFn(const string& name, const vector<string>& params, const vector<NP>& body, bool main, const Node* at) {
        cur = Fn(); cur.name = name; cur.nparams = (int)params.size();
        isMain = main; scopes.clear(); scopes.emplace_back();
        for (auto& p : params) declare(p, "let", at);
        for (auto& s : body) stmt(s.get());
        emitPush(Value());   // implicit "return undefined"
        emit(RET);
        fns.push_back(move(cur));
    }

    void stmt(const Node* s) {
        switch (s->kind) {
            case K_VARDECL:
                for (auto& d : s->ch) {
                    const Node* init = d->ch[0].get();
                    if (!init && s->str == "const") err(d.get(), "const '" + d->str + "' must be initialised");
                    if (init) expr(init); else emitPush(Value());
                    VarInfo vi = declare(d->str, s->str, d.get());   // declared AFTER its initialiser is compiled
                    emitNamed(STORE, vi.slot, d->str);
                }
                break;
            case K_EXPRSTMT: expr(s->ch[0].get()); emit(POP); break;
            case K_BLOCK:
                scopes.emplace_back();
                for (auto& x : s->ch) stmt(x.get());
                scopes.pop_back();
                break;
            case K_IF: {
                expr(s->ch[0].get());
                int jf = emit(JF);
                stmt(s->ch[1].get());
                if (s->ch[2]) { int j = emit(JMP); patch(jf); stmt(s->ch[2].get()); patch(j); }
                else patch(jf);
                break;
            }
            case K_WHILE: {
                int start = here();
                expr(s->ch[0].get());
                int jf = emit(JF);
                stmt(s->ch[1].get());
                emit(JMP, start);
                patch(jf);
                break;
            }
            case K_FOR: {
                scopes.emplace_back();
                if (s->ch[0]) stmt(s->ch[0].get());
                int start = here(), jf = -1;
                if (s->ch[1]) { expr(s->ch[1].get()); jf = emit(JF); }
                stmt(s->ch[3].get());
                if (s->ch[2]) { expr(s->ch[2].get()); emit(POP); }
                emit(JMP, start);
                if (jf >= 0) patch(jf);
                scopes.pop_back();
                break;
            }
            case K_RETURN:
                if (isMain) err(s, "'return' outside of a function");
                if (s->ch[0]) expr(s->ch[0].get()); else emitPush(Value());
                emit(RET);
                break;
            default: throw runtime_error("unknown statement");
        }
    }

    void expr(const Node* e) {
        switch (e->kind) {
            case K_LIT: emitPush(e->v); break;
            case K_ID:
                if (e->str == "console.log") err(e, "'console.log' must be called");
                emitNamed(LOAD, resolve(e->str, e).slot, e->str);
                break;
            case K_ASSIGN: {
                VarInfo vi = resolve(e->str, e);
                if (vi.kind == "const") err(e, "Cannot assign to const '" + e->str + "'");
                expr(e->ch[0].get());
                emit(DUP);
                emitNamed(STORE, vi.slot, e->str);
                break;
            }
            case K_BINARY: {
                const Node *l = e->ch[0].get(), *r = e->ch[1].get();
                // optimisation: constant folding for  number (op) number
                if (l->kind == K_LIT && r->kind == K_LIT && l->v.t == Value::NUM && r->v.t == Value::NUM &&
                    (e->str == "+" || e->str == "-" || e->str == "*" || e->str == "/" || e->str == "%")) {
                    double a = l->v.n, b = r->v.n, v = 0;
                    switch (e->str[0]) {
                        case '+': v = a + b; break; case '-': v = a - b; break; case '*': v = a * b; break;
                        case '/': v = a / b; break; default: v = std::fmod(a, b);
                    }
                    emitPush(Value::num(v));
                    break;
                }
                expr(l); expr(r);
                const string& o = e->str;
                emit(o == "+" ? ADD : o == "-" ? SUB : o == "*" ? MUL : o == "/" ? DIV : o == "%" ? MOD :
                     o == "<" ? LT : o == ">" ? GT : o == "<=" ? LE : o == ">=" ? GE :
                     (o == "===" || o == "==") ? EQ : NE);
                break;
            }
            case K_LOGICAL: {   // short-circuit: JFK/JTK keep the value if they jump, pop it otherwise
                expr(e->ch[0].get());
                int j = emit(e->str == "&&" ? JFK : JTK);
                expr(e->ch[1].get());
                patch(j);
                break;
            }
            case K_UNARY: expr(e->ch[0].get()); emit(e->str == "-" ? NEG : NOT); break;
            case K_CALL: {
                if (e->str == "console.log") {
                    for (auto& a : e->ch) expr(a.get());
                    emit(PRINT, (int)e->ch.size());
                    emitPush(Value());   // console.log evaluates to undefined
                    break;
                }
                if (!fnIndex.count(e->str)) err(e, "Function '" + e->str + "' is not defined");
                int want = arity[e->str];
                if (want != (int)e->ch.size())
                    err(e, "Function '" + e->str + "' expects " + to_string(want) + " argument(s), got " + to_string(e->ch.size()));
                for (auto& a : e->ch) expr(a.get());
                emit(CALL, fnIndex[e->str]);
                cur.code.back().argc = (int)e->ch.size();
                cur.code.back().name = e->str;
                break;
            }
            default: throw runtime_error("unknown expression");
        }
    }

public:
    vector<Fn> compile(const Node* prog) {
        int idx = 1;   // fns[0] is always "main"
        for (auto& s : prog->ch) if (s->kind == K_FUNC) {
            if (fnIndex.count(s->str) || s->str == "main") err(s.get(), "Function '" + s->str + "' already defined");
            fnIndex[s->str] = idx++;
            arity[s->str] = (int)s->params.size();
        }
        vector<NP> mainBody;   // top-level statements, compiled as the body of "main"
        // (non-owning view: we compile main by walking prog->ch directly)
        scopes.clear();
        cur = Fn(); cur.name = "main"; isMain = true; scopes.emplace_back();
        for (auto& s : prog->ch) if (s->kind != K_FUNC) stmt(s.get());
        emitPush(Value()); emit(RET);
        fns.push_back(move(cur));
        for (auto& s : prog->ch) if (s->kind == K_FUNC) {
            compileFn(s->str, s->params, s->ch[0]->ch, false, s.get());
        }
        return move(fns);
    }
};

/* ============================ 4. STACK VM ============================ */
void run(const vector<Fn>& fns) {
    struct Frame { int fn, ip; vector<Value> loc; };
    vector<Value> st;
    vector<Frame> frames;
    frames.push_back({0, 0, vector<Value>(fns[0].nslots)});
    long long steps = 0;
    auto rt = [](const string& m) { throw CompileError{"Runtime", m, 0, 0}; };
    auto pop = [&]() { Value v = move(st.back()); st.pop_back(); return v; };

    for (;;) {
        Frame& f = frames.back();
        const Instr& in = fns[f.fn].code[f.ip++];
        if (++steps > 30000000LL) rt("Step limit exceeded (possible infinite loop)");
        switch (in.op) {
            case PUSH: st.push_back(in.k); break;
            case LOAD: st.push_back(f.loc[in.arg]); break;
            case STORE: f.loc[in.arg] = pop(); break;
            case POP: st.pop_back(); break;
            case DUP: st.push_back(st.back()); break;
            case NEG: { Value a = pop(); st.push_back(Value::num(-toNum(a))); break; }
            case NOT: { Value a = pop(); st.push_back(Value::boolean(!truthy(a))); break; }
            case ADD: case SUB: case MUL: case DIV: case MOD:
            case LT: case GT: case LE: case GE: case EQ: case NE: {
                Value b = pop(), a = pop();
                switch (in.op) {
                    case ADD:
                        if (a.t == Value::STR || b.t == Value::STR) st.push_back(Value::str(toStr(a) + toStr(b)));
                        else st.push_back(Value::num(toNum(a) + toNum(b)));
                        break;
                    case SUB: st.push_back(Value::num(toNum(a) - toNum(b))); break;
                    case MUL: st.push_back(Value::num(toNum(a) * toNum(b))); break;
                    case DIV: st.push_back(Value::num(toNum(a) / toNum(b))); break;
                    case MOD: st.push_back(Value::num(std::fmod(toNum(a), toNum(b)))); break;
                    case EQ: st.push_back(Value::boolean(strictEq(a, b))); break;
                    case NE: st.push_back(Value::boolean(!strictEq(a, b))); break;
                    default: {
                        bool r;
                        if (a.t == Value::STR && b.t == Value::STR) {
                            int c = a.s.compare(b.s);
                            r = in.op == LT ? c < 0 : in.op == GT ? c > 0 : in.op == LE ? c <= 0 : c >= 0;
                        } else {
                            double x = toNum(a), y = toNum(b);
                            r = in.op == LT ? x < y : in.op == GT ? x > y : in.op == LE ? x <= y : x >= y;
                        }
                        st.push_back(Value::boolean(r));
                    }
                }
                break;
            }
            case JMP: f.ip = in.arg; break;
            case JF: { Value c = pop(); if (!truthy(c)) f.ip = in.arg; break; }
            case JFK: if (!truthy(st.back())) f.ip = in.arg; else st.pop_back(); break;
            case JTK: if (truthy(st.back())) f.ip = in.arg; else st.pop_back(); break;
            case CALL: {
                if (frames.size() > 10000) rt("Stack overflow (recursion too deep)");
                const Fn& callee = fns[in.arg];
                Frame nf{in.arg, 0, vector<Value>(callee.nslots)};
                for (int i = in.argc - 1; i >= 0; i--) nf.loc[i] = pop();   // args come off the stack in reverse
                frames.push_back(move(nf));                                   // 'f' is invalid after this line
                break;
            }
            case RET: {
                Value v = pop();
                if (frames.size() == 1) return;
                frames.pop_back();
                st.push_back(move(v));
                break;
            }
            case PRINT: {
                size_t base = st.size() - in.arg;
                string out;
                for (size_t i = base; i < st.size(); i++) { if (i > base) out += ' '; out += toStr(st[i]); }
                st.resize(base);
                cout << out << '\n';
                break;
            }
        }
    }
}

/* ============================ 5. CLI ============================ */
string reprValue(const Value& v) { return v.t == Value::STR ? "\"" + v.s + "\"" : toStr(v); }

void dumpTokens(const vector<Token>& toks) {
    cout << "--- TOKENS ---\n";
    for (auto& t : toks) {
        char buf[64]; snprintf(buf, sizeof buf, "%3d:%-3d %-4s ", t.line, t.col, TTN[t.type]);
        cout << buf << (t.type == T_STR ? "\"" + t.text + "\"" : t.text) << '\n';
    }
}
void dumpAst(const Node* n, int d) {
    if (!n) return;
    cout << string(d * 2, ' ') << KN[n->kind];
    if (!n->str.empty()) cout << " " << n->str;
    if (n->kind == K_LIT) cout << " " << reprValue(n->v);
    if (!n->params.empty()) { cout << " ("; for (size_t i = 0; i < n->params.size(); i++) cout << (i ? ", " : "") << n->params[i]; cout << ")"; }
    cout << '\n';
    for (auto& c : n->ch) dumpAst(c.get(), d + 1);
}
void dumpBytecode(const vector<Fn>& fns) {
    cout << "--- BYTECODE ---\n";
    for (auto& f : fns) {
        cout << "\nfunction " << f.name << "  (params=" << f.nparams << ", slots=" << f.nslots << ")\n";
        for (size_t n = 0; n < f.code.size(); n++) {
            const Instr& i = f.code[n];
            string a;
            switch (i.op) {
                case PUSH: a = reprValue(i.k); break;
                case LOAD: case STORE: case JMP: case JF: case JFK: case JTK: case PRINT: a = to_string(i.arg); break;
                case CALL: a = i.name + " argc=" + to_string(i.argc); break;
                default: break;
            }
            char buf[32]; snprintf(buf, sizeof buf, "  %3zu  %-6s ", n, OPN[i.op]);
            cout << buf << a;
            if ((i.op == LOAD || i.op == STORE) && !i.name.empty()) cout << "   ; " << i.name;
            cout << '\n';
        }
    }
    cout << '\n';
}
void report(const CompileError& e, const string& src, const string& file) {
    cerr << e.phase << " Error: " << e.msg;
    if (e.line) cerr << "  (" << file << ":" << e.line << ":" << e.col << ")";
    cerr << '\n';
    if (e.line) {
        istringstream in(src); string ln; int k = 0;
        while (getline(in, ln)) if (++k == e.line) {
            cerr << "  " << ln << "\n  " << string(max(0, e.col - 1), ' ') << "^\n";
            break;
        }
    }
}

int main(int argc, char** argv) {
    string file; bool fTok = false, fAst = false, fBc = false, fRun = true;
    for (int i = 1; i < argc; i++) {
        string a = argv[i];
        if (a == "--tokens") fTok = true;
        else if (a == "--ast") fAst = true;
        else if (a == "--bytecode") fBc = true;
        else if (a == "--no-run") fRun = false;
        else if (a.rfind("--", 0) != 0) file = a;
    }
    if (file.empty()) { cout << "Usage: ./minijs <file.js> [--tokens] [--ast] [--bytecode] [--no-run]\n"; return 1; }
    ifstream in(file);
    if (!in) { cerr << "Cannot read '" << file << "'\n"; return 1; }
    stringstream ss; ss << in.rdbuf();
    string src = ss.str();
    try {
        vector<Token> toks = lex(src);
        if (fTok) dumpTokens(toks);
        NP ast = Parser(toks).program();
        if (fAst) { cout << "--- AST ---\n"; dumpAst(ast.get(), 0); }
        vector<Fn> fns = Compiler().compile(ast.get());
        if (fBc) dumpBytecode(fns);
        if (fRun) run(fns);
    } catch (const CompileError& e) {
        cout.flush();
        report(e, src, file);
        return 1;
    }
    return 0;
}
