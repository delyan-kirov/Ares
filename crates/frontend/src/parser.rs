//! A Pratt (precedence-climbing) parser.
//!
//! Structure mirrors the grammar so the Rust call stack matches it, which keeps
//! error context meaningful:
//!
//! * `Parser::parse_expr` is the precedence-climbing core: it parses a prefix,
//!   then folds infix operators and juxtaposition (application) by binding power
//!   from `table`.
//! * `Parser::parse_primary` parses one atom then a left-associative postfix
//!   `.` chain (field access, tuple index, struct/variant literals,
//!   module-qualified names) that binds tighter than application.
//! * The control forms (`let`, `if`, `when`, `\`, `do`) are
//!   primaries, each with its own `parse_*` method.
//!
//! Nodes are built into the [`Ast`] stores as they are parsed (bottom-up), so a
//! parse method returns an [`Aol`] handle, not a reference. Names are interned to
//! [`StrId`]. Sugar (`;`, `|>`, `<|`, `::`, `[..]`) is preserved as explicit AST
//! nodes; [`crate::desugar`] removes it.
//!
//! Input: a [`Lexer`] over one module. Output: its [`Program`] in a shared
//! [`Ast`], plus every error, so one broken item does not hide the rest.
//!
//! Entry point: [`Parser::parse_program`].

pub mod data;
pub(crate) mod table;
#[cfg(test)]
mod tests;

use crate::lexer::data::{Kind, Token};
use crate::lexer::Lexer;
use utilities::{Aol, Line, Slice, Span, StrId};
use utilities::{Applicability, Code, Diagnostic, Edit, Result};

use crate::parser::data::*;

pub struct Parser<'a> {
    lex: Lexer<'a>,
    ast: Ast,
    /// The (read-only) source, so a token's lexeme is `src[token.span]`. Tokens
    /// themselves carry only spans; this is where they resolve.
    src: &'a str,
    /// End offset of the most recently consumed token, so a node's span can run
    /// from its first token's start to here.
    last_end: usize,
    /// Errors recovered from at item boundaries, in source order.
    errors: Vec<Diagnostic>,
    /// A `@ctx T ->` parameter read in the current signature. It is an error,
    /// raised once the body is parsed, so its fix can rewrite both.
    ctx_written: Option<CtxWritten>,
    /// The names a `let` or an applied lambda binds while an expression is
    /// read as a type, innermost last: `let u = {t, t} in u -> u` reads `u`
    /// as `{t, t}`.
    ty_env: Vec<(StrId, Aol<Ty>)>,
}

/// Where a signature wrote the reserved `@ctx T ->` parameter.
#[derive(Clone, Copy)]
struct CtxWritten {
    /// The `@ctx` keyword.
    kw: Token,
    /// The parameter's type, `T`.
    ty: Aol<Ty>,
    /// From the keyword to the end of `T`.
    span: Span,
}

/// Consume a token of an expected kind, or fail with an `UnexpectedToken`
/// diagnostic naming what was wanted. Evaluates to the consumed [`Token`].
macro_rules! expect {
    ($self:ident, $pat:pat, $what:expr) => {{
        let t = $self.peek()?;
        if !matches!(t.kind, $pat) {
            return Err($self.unexpected(&t, $what));
        }
        $self.bump()?
    }};
}

impl<'a> Parser<'a> {
    /// Build a parser that fills `ast`. Passing an existing [`Ast`] lets several
    /// modules of one compilation share stores, so a handle minted for one module
    /// resolves in every module (needed for cross-module type imports).
    pub fn new(lex: Lexer<'a>, ast: Ast) -> Parser<'a> {
        let src = lex.source();
        Parser {
            lex,
            ast,
            src,
            last_end: 0,
            errors: Vec::new(),
            ctx_written: None,
            ty_env: Vec::new(),
        }
    }

    /// The errors [`Parser::parse_program`] recovered from.
    pub fn take_errors(&mut self) -> Vec<Diagnostic> {
        std::mem::take(&mut self.errors)
    }

    /// Consume the parser, yielding the filled store bundle.
    pub fn into_ast(self) -> Ast {
        self.ast
    }

    // -- store + token helpers ----------------------------------------------

    fn expr(&mut self, e: Expr) -> Aol<Expr> {
        self.ast.exprs.create(e)
    }
    /// Record `node`'s source span as running from `start` to the end of the most
    /// recently consumed token, then return it (builder-style, for diagnostics).
    fn stamp(&mut self, start: usize, node: Aol<Expr>) -> Aol<Expr> {
        self.ast.expr_spans.insert(node, Span::new(start, self.last_end));
        node
    }
    /// Like [`stamp`](Self::stamp), for a `Ty` node.
    fn stamp_ty(&mut self, start: usize, node: Aol<Ty>) -> Aol<Ty> {
        self.ast.ty_spans.insert(node, Span::new(start, self.last_end));
        node
    }
    /// Like [`stamp`](Self::stamp), for a `Pattern` node.
    fn stamp_pat(&mut self, start: usize, node: Aol<Pattern>) -> Aol<Pattern> {
        self.ast.pat_spans.insert(node, Span::new(start, self.last_end));
        node
    }
    /// The start offset of the next token, marking where a node begins.
    fn here(&mut self) -> Result<usize> {
        Ok(self.peek()?.span.start)
    }
    fn ty(&mut self, t: Ty) -> Aol<Ty> {
        self.ast.tys.create(t)
    }
    fn pat(&mut self, p: Pattern) -> Aol<Pattern> {
        self.ast.pats.create(p)
    }
    /// A token's source lexeme, `src[t.span]`. The returned slice is tied to the
    /// source (`'a`), not to `&self`, so it can be handed straight to a `&mut
    /// self` method like [`intern`](Self::intern) without a borrow clash.
    fn text(&self, t: Token) -> &'a str {
        let src: &'a str = self.src;
        &src[t.span.start..t.span.end]
    }
    /// The identifier of an `@name` token, past the leading `@`.
    fn intrinsic_name(&self, t: Token) -> &'a str {
        debug_assert!(matches!(t.kind, Kind::At), "intrinsic_name on non-@ token");
        &self.text(t)[1..]
    }
    fn intern(&mut self, s: &str) -> StrId {
        StrId::intern(s)
    }
    /// Decode a `Kind::Str` token's literal (escapes and all) into interned
    /// bytes. Decoding is deferred to here so the lexer stays borrow-free. Used
    /// for non-interpolating strings (patterns, `@extern` operands).
    fn intern_str(&mut self, t: Token) -> Result<StrId> {
        let bytes = crate::lexer::decode_string(self.text(t), t.span.start, t.line)?;
        Ok(StrId::intern_bytes(&bytes))
    }
    /// A `Str` literal expression from raw decoded bytes.
    fn str_expr(&mut self, bytes: &[u8]) -> Aol<Expr> {
        let s = StrId::intern_bytes(bytes);
        self.expr(Expr::Str(s))
    }

    /// Build a string-literal expression, expanding `?(expr)` interpolations. `t`
    /// is the `Kind::Str` token. An interpolated literal is an [`Expr::Interp`]
    /// holding both of its readings: the `@Str` default `"a " ++ to_string e ++ " b"`,
    /// where a literal chunk seeds the `++` chain so the whole expression types as
    /// `Str` and each interpolant is stringified through `to_string` over its
    /// instance, and the builder chain over the blessed `@IInterp*` interfaces
    /// (see [`Self::interp_target`]). Braces are ordinary literal characters; `\?`
    /// is a literal `?`.
    fn build_string(&mut self, t: Token) -> Result<Aol<Expr>> {
        let raw = self.text(t);
        let bytes = raw.as_bytes();
        let inner = &bytes[1..bytes.len() - 1];
        let body_start = t.span.start + 1; // absolute offset of `inner[0]`

        let mut segs: Vec<Aol<Expr>> = Vec::new();
        let mut pieces: Vec<Vec<u8>> = Vec::new();
        let mut holes: Vec<Aol<Expr>> = Vec::new();
        let mut hole_srcs: Vec<&'a str> = Vec::new();
        let mut chunk: Vec<u8> = Vec::new();
        let mut interpolated = false;
        let mut i = 0;
        while i < inner.len() {
            match inner[i] {
                b'\\' => i = crate::lexer::decode_escape(inner, i, body_start, t.line, &mut chunk)?,
                b'?' if i + 1 < inner.len() && inner[i + 1] == b'(' => {
                    interpolated = true;
                    let seg = self.str_expr(&chunk);
                    segs.push(seg);
                    pieces.push(std::mem::take(&mut chunk));
                    // Balance the interpolant's `()` to find its close, skipping
                    // nested strings so their parens don't miscount.
                    let expr_start = i + 2; // past `?(`
                    let mut depth = 1usize;
                    let mut j = expr_start;
                    while j < inner.len() {
                        match inner[j] {
                            b'"' => {
                                j += 1;
                                while j < inner.len() && inner[j] != b'"' {
                                    j += if inner[j] == b'\\' { 2 } else { 1 };
                                }
                                j += 1; // past the closing quote
                            }
                            b'(' => {
                                depth += 1;
                                j += 1;
                            }
                            b')' => {
                                depth -= 1;
                                if depth == 0 {
                                    break;
                                }
                                j += 1;
                            }
                            _ => j += 1,
                        }
                    }
                    if depth != 0 {
                        let at = body_start + i;
                        return Err(Diagnostic::error(
                            Code::UnexpectedToken,
                            Span::new(at, at + 1),
                            t.line,
                            "string interpolation '?(' is not closed with ')'".to_string(),
                        ));
                    }
                    let full: &'a str = self.src;
                    let abs_start = body_start + expr_start;
                    let slice = &full[abs_start..body_start + j];
                    let e = self.parse_subexpr(slice, abs_start, t.line)?;
                    holes.push(e);
                    hole_srcs.push(slice.trim());
                    // `?(e)` stringifies via `to_string`, so an interpolant of any
                    // type with an `Ito_string` instance (base types ship one in the
                    // auto-imported `CORE`) reads as `Str`. The call
                    // inherits the interpolant's span so a resolution failure
                    // points at the interpolant, not a synthetic node.
                    let span = self.ast.expr_span(e).unwrap_or(t.span);
                    let to_string = self.intern("to_string");
                    let f = self.expr(Expr::Var {
                        module: None,
                        name: to_string,
                    });
                    let call = self.expr(Expr::App(f, e));
                    self.ast.expr_spans.insert(call, span);
                    segs.push(call);
                    i = j + 1; // past ')'
                }
                c => {
                    chunk.push(c);
                    i += 1;
                }
            }
        }
        let seg = self.str_expr(&chunk);
        segs.push(seg);

        if !interpolated {
            return Ok(segs.pop().expect("at least the whole-string chunk"));
        }
        pieces.push(chunk);
        let concat = self.intern("++");
        let mut acc = segs[0];
        for &rhs in &segs[1..] {
            acc = self.expr(Expr::BinOp {
                op: concat,
                lhs: acc,
                rhs,
            });
        }
        let target = self.interp_target(&pieces, &holes, t.span);
        let quoted = self.interp_quoted(&pieces, &hole_srcs, t.span);
        Ok(self.expr(Expr::Interp { default: acc, target, quoted }))
    }

    /// The `Template` reading of an interpolated string: the pieces as they
    /// are, and each hole's source as code, `@code "x"`, so the hole is never
    /// evaluated where the literal is.
    fn interp_quoted(&mut self, pieces: &[Vec<u8>], holes: &[&str], span: Span) -> Aol<Expr> {
        let pieces: Vec<Aol<Expr>> = pieces.iter().map(|p| self.str_expr(p)).collect();
        let code = self.intern("@code");
        let holes: Vec<Aol<Expr>> = holes
            .iter()
            .map(|src| {
                let f = self.expr(Expr::Var { module: None, name: code });
                let text = self.str_expr(src.as_bytes());
                self.expr(Expr::App(f, text))
            })
            .collect();
        let mut fields = Vec::new();
        for (name, items) in [("pieces", pieces), ("holes", holes)] {
            let items = self.ast.make_slice(items);
            let value = self.expr(Expr::List(items));
            self.ast.expr_spans.insert(value, span);
            fields.push(FieldInit::Named { name: self.intern(name), value });
        }
        let fields = self.ast.make_slice(fields);
        let out = self.expr(Expr::StructLit { ty: None, fields, spread: None });
        self.ast.expr_spans.insert(out, span);
        out
    }

    /// The builder reading of an interpolated string: each hole bound in order,
    /// then `@IInterp (\#b => ...)` appending every non-empty piece with
    /// `@IInterpText` and every hole with `@IInterpHole`. Binding the holes first
    /// keeps their effects outside the builder, in source order. The synthetic
    /// nodes take the literal's span, and a hole's call the hole's, so a missing
    /// instance points at the string or at the hole that needs it.
    fn interp_target(&mut self, pieces: &[Vec<u8>], holes: &[Aol<Expr>], span: Span) -> Aol<Expr> {
        debug_assert_eq!(pieces.len(), holes.len() + 1, "a piece on each side of every hole");
        let var = |p: &mut Self, name: &str, at: Span| {
            let name = p.intern(name);
            let v = p.expr(Expr::Var { module: None, name });
            p.ast.expr_spans.insert(v, at);
            v
        };
        let call2 = |p: &mut Self, head: &str, a: Aol<Expr>, b: Aol<Expr>, span: Span| {
            let f = var(p, head, span);
            let fa = p.expr(Expr::App(f, a));
            p.ast.expr_spans.insert(fa, span);
            let fab = p.expr(Expr::App(fa, b));
            p.ast.expr_spans.insert(fab, span);
            fab
        };
        let mut acc = var(self, "#b", span);
        for (k, piece) in pieces.iter().enumerate() {
            if !piece.is_empty() {
                let text = self.str_expr(piece);
                acc = call2(self, "@IInterpText", acc, text, span);
            }
            if let Some(&hole) = holes.get(k) {
                let at = self.ast.expr_span(hole).unwrap_or(span);
                let h = var(self, &format!("#h{k}"), at);
                acc = call2(self, "@IInterpHole", acc, h, at);
            }
        }
        let b = self.intern("#b");
        let param = self.pat(Pattern::Var(b));
        let params = self.ast.make_slice(vec![LamParam { pat: param, sig: None }]);
        let lam = self.expr(Expr::Lambda { params, body: acc });
        self.ast.expr_spans.insert(lam, span);
        let interp = var(self, "@IInterp", span);
        let mut out = self.expr(Expr::App(interp, lam));
        self.ast.expr_spans.insert(out, span);
        for (k, &hole) in holes.iter().enumerate().rev() {
            let name = self.intern(&format!("#h{k}"));
            let pat = self.pat(Pattern::Var(name));
            out = self.expr(Expr::Let { binding: Binding { pat, sig: None, value: hole }, body: out });
            self.ast.expr_spans.insert(out, span);
        }
        out
    }

    /// Parse a single expression from a sub-slice of the source (a string
    /// interpolant's `{...}` body), re-lexing it with absolute spans. Restores
    /// the outer token stream afterwards, even on error.
    fn parse_subexpr(&mut self, slice: &'a str, base: usize, line: Line) -> Result<Aol<Expr>> {
        let saved = std::mem::replace(&mut self.lex, Lexer::sub(slice, base, line));
        let saved_end = self.last_end;
        let out = self.parse_expr(0).and_then(|e| {
            if matches!(self.peek_kind()?, Kind::Eof) {
                Ok(e)
            } else {
                let t = self.peek()?;
                Err(self.unexpected(&t, "expected a single expression in the interpolation"))
            }
        });
        self.lex = saved;
        self.last_end = saved_end;
        out
    }
    /// Consume the next token and intern its text (the token is a checked word).
    fn bump_word(&mut self) -> Result<StrId> {
        let t = self.bump()?;
        Ok(self.intern(self.text(t)))
    }
    /// Expect a `Word` and intern it. Combines `expect!` + `intern` so the token
    /// is bound to a local first (a nested `self.intern(self.bump()?...)` would
    /// mutably borrow `self` twice in one expression).
    fn expect_word(&mut self, what: &str) -> Result<StrId> {
        let t = expect!(self, Kind::Word, what);
        Ok(self.intern(self.text(t)))
    }
    /// An effect-row label: a Capitalized `Word` (a user-declared effect like
    /// `Fail`) or an `@`-form builtin effect (`@IO`). The lexeme is interned as
    /// written, so `@IO` keeps its sigil ("@IO"), matching the `@`-type-con
    /// convention and staying distinct from any user effect.
    fn expect_effect_label(&mut self) -> Result<StrId> {
        let t = self.peek()?;
        if matches!(t.kind, Kind::Word | Kind::At) {
            self.bump()?;
            Ok(self.intern(self.text(t)))
        } else {
            Err(self.unexpected(&t, "expected an effect name"))
        }
    }
    /// Consume a lowercase-initial type variable name and intern it.
    fn expect_tyvar(&mut self, what: &str) -> Result<StrId> {
        let t = expect!(self, Kind::Word, what);
        if !self.text(t).starts_with(|c: char| c.is_ascii_lowercase()) {
            return Err(self.unexpected(&t, "a type variable must start with a lowercase letter"));
        }
        Ok(self.intern(self.text(t)))
    }
    /// Is the next token a lowercase name in an effect row not followed by
    /// its `>`: a variable of kind `@Effect` (`<l | e>`), not the row's tail?
    fn at_label_variable(&mut self) -> Result<bool> {
        let next = self.peek_at(1)?;
        Ok(!(matches!(next.kind, Kind::Op) && self.text(next).starts_with('>')))
    }
    /// Is the next token a lowercase-initial word, i.e. a type variable?
    fn at_tyvar(&mut self) -> Result<bool> {
        let t = self.peek()?;
        Ok(matches!(t.kind, Kind::Word) && self.text(t).starts_with(|c: char| c.is_ascii_lowercase()))
    }
    /// If `base` is a bare, unqualified variable, its interned name.
    fn bare_var_name(&self, base: Aol<Expr>) -> Option<StrId> {
        match self.ast.exprs.lookup(base) {
            Expr::Var { module: None, name } => Some(*name),
            _ => None,
        }
    }

    fn peek(&mut self) -> Result<Token> {
        self.lex.peek(0)
    }
    fn peek_at(&mut self, n: usize) -> Result<Token> {
        self.lex.peek(n)
    }
    fn peek_kind(&mut self) -> Result<Kind> {
        Ok(self.lex.peek(0)?.kind)
    }
    fn bump(&mut self) -> Result<Token> {
        let t = self.lex.next_token()?;
        self.last_end = t.span.end;
        Ok(t)
    }
    /// Consume the next token if it matches `pred`; report whether it did.
    fn eat(&mut self, pred: impl Fn(Kind) -> bool) -> Result<bool> {
        if pred(self.peek()?.kind) {
            self.bump()?;
            Ok(true)
        } else {
            Ok(false)
        }
    }
    /// How many names open a field group `a b c: T` at the cursor: the run of
    /// words a `:` ends, or 0 when the cursor is at no such run. The `:`
    /// decides, so `F a` followed by anything else stays an application.
    fn group_len(&mut self) -> Result<usize> {
        self.group_len_at(0)
    }
    /// [`Self::group_len`] from `from` tokens ahead.
    fn group_len_at(&mut self, from: usize) -> Result<usize> {
        let mut n = 0;
        while matches!(self.peek_kind_at(from + n)?, Kind::Word) {
            n += 1;
        }
        Ok(if n > 0 && matches!(self.peek_kind_at(from + n)?, Kind::Colon) { n } else { 0 })
    }
    /// The names of a field group `a b c: T` through its `:`, with the cursor
    /// on the first name and `n` from [`Self::group_len`], and the lexer mark
    /// of `T`. Each name parses `T` from that mark (see [`Self::group_type`]),
    /// so the fields share no node: the group is sugar for `a: T, b: T, c: T`.
    fn group_names(&mut self, n: usize) -> Result<(Vec<(Token, StrId)>, usize)> {
        let mut names = Vec::with_capacity(n);
        for _ in 0..n {
            let t = self.bump()?;
            names.push((t, self.intern(self.text(t))));
        }
        self.bump()?; // ':'
        Ok((names, self.lex.mark()))
    }
    /// Rewind to a field group's type, for the next name to parse it again.
    fn group_type(&mut self, mark: usize) {
        self.lex.reset(mark);
    }
    /// Is the next token the operator with lexeme `s`?
    /// The operand of a splice `!X`, with the cursor on the `!`. `!` binds like
    /// the other prefix operators in every position, so `!f a b` splices `f a b`
    /// and the operand ends before an infix operator, a `,`, `=>` or `>`.
    fn parse_splice_operand(&mut self) -> Result<Aol<Expr>> {
        self.bump()?; // '&'
        self.parse_expr(table::PREFIX)
    }
    fn at_splice(&mut self) -> Result<bool> {
        self.at_op(table::SPLICE)
    }
    /// `!` named as a function: a definition `$ (&)` or a section `(&)`.
    fn splice_not_a_function(&self, t: &Token) -> Diagnostic {
        Diagnostic::error(Code::UnexpectedToken, t.span, t.line, "`!` is a splice, not a function")
            .with_note("`!X` runs `X` at compile time and replaces itself with the result")
    }
    fn at_op(&mut self, s: &str) -> Result<bool> {
        let t = self.peek()?;
        Ok(matches!(t.kind, Kind::Op) && self.text(t) == s)
    }
    /// A `-` directly before a numeric literal: a negative literal pattern.
    fn at_negative_literal(&mut self) -> Result<bool> {
        Ok(self.at_op("-")? && matches!(self.peek_kind_at(1)?, Kind::Int(_) | Kind::Real(_)))
    }
    fn unexpected(&self, t: &Token, what: &str) -> Diagnostic {
        // Running into the next item (or the end) means this one stopped short:
        // the missing piece belongs right after its last token, not at the `$`.
        let cut = matches!(t.kind, Kind::Dollar | Kind::Eof) && self.last_end > 0;
        let span = if cut { Span::at(self.last_end) } else { t.span };
        let found = if cut && matches!(t.kind, Kind::Dollar) {
            "the next item".to_string()
        } else {
            describe(t, self.text(*t))
        };
        let d = Diagnostic::error(Code::UnexpectedToken, span, t.line, format!("{what}, found {found}"));
        let closer = what
            .strip_prefix("expected '")
            .and_then(|rest| rest.split_once('\''))
            .map(|(c, _)| c)
            .filter(|c| matches!(*c, ")" | "]" | "}" | "-#"));
        match closer {
            Some(c) => d.with_fix(
                format!("insert `{c}`"),
                vec![Edit::new(Span::at(self.last_end), c)],
                Applicability::MaybeIncorrect,
            ),
            None => d,
        }
    }

    /// A type name must start with a capital letter; a lowercase name in type
    /// position is a type variable. `tok` is the offending name token, for the
    /// error span.
    fn require_type_capital(&self, text: &str, tok: &Token) -> Result<()> {
        if text.starts_with(|c: char| c.is_ascii_uppercase()) {
            Ok(())
        } else {
            Err(self.unexpected(
                tok,
                "a type name must start with a capital letter (a lowercase name is a type variable)",
            ))
        }
    }

    /// A value or function name must start with a lowercase letter; a capitalized
    /// name is a type or constructor. Symbolic names (operators) are exempt.
    fn require_value_lowercase(&self, text: &str, tok: &Token) -> Result<()> {
        if text.starts_with(|c: char| c.is_ascii_uppercase()) {
            Err(self.unexpected(
                tok,
                "a value or function name must start with a lowercase letter (a capitalized name is a type or constructor)",
            ))
        } else {
            Ok(())
        }
    }

    // -- program + globals --------------------------------------------------

    /// Parse a whole compilation unit.
    pub fn parse_program(&mut self) -> Result<Program> {
        let head = expect!(self, Kind::Dollar, "expected '$ @mod' at the start of the file");
        let at = expect!(self, Kind::At, "expected '@mod' after '$' at the start of the file");
        if self.intrinsic_name(at) != "mod" {
            return Err(self.unexpected(&at, "expected '@mod' after '$' at the start of the file"));
        }
        let name = expect!(self, Kind::Word, "expected a module name after '@mod'");
        let module = self.intern(self.text(name));
        let header = Span::new(head.span.start, name.span.end);

        let mut items = Vec::new();
        let mut spans = Vec::new();
        let mut broken = Vec::new();
        loop {
            match self.peek_kind() {
                Ok(Kind::Eof) => break,
                Ok(_) => {}
                Err(d) => {
                    self.errors.push(d);
                    if !self.skip_to_next_item(self.last_end) {
                        break;
                    }
                    continue;
                }
            }
            let start = self.peek()?.span.start;
            let name = self.item_name_span();
            match self.parse_global() {
                Ok(item) => {
                    let full = Span::new(start, self.last_end);
                    items.push(item);
                    spans.push(ItemSpan { full, name });
                }
                Err(d) => {
                    if let Some(n) = name {
                        let text = &self.src[n.start..n.end];
                        if text.starts_with(|c: char| c.is_ascii_lowercase()) {
                            broken.push(self.intern(text));
                        }
                    }
                    self.errors.push(d);
                    if !self.skip_to_next_item(start + 1) {
                        break;
                    }
                }
            }
        }
        Ok(Program {
            module,
            header,
            items: self.ast.make_slice(items),
            spans: self.ast.make_slice(spans),
            broken: self.ast.make_slice(broken),
        })
    }

    /// The span of the name the item at the cursor (its `$`) defines: the word
    /// after `$`, or an `@`-named value (`@main`, `@build`, a CORE builtin).
    fn item_name_span(&mut self) -> Option<Span> {
        let t = self.peek_at(1).ok()?;
        let text = &self.src[t.span.start..t.span.end];
        match t.kind {
            Kind::Word => Some(t.span),
            Kind::At if matches!(text, "@main" | "@build") => Some(t.span),
            Kind::At if !crate::typing::types::is_blessed_interface(text)
                && matches!(self.peek_at(2).ok()?.kind, Kind::Colon) => Some(t.span),
            _ => None,
        }
    }

    /// Resume after a broken item: move the cursor to the next `$` at the start
    /// of a line past `from`, re-lexing from there so a lexical error inside the
    /// broken item is left behind too. Reports whether there is such an item.
    fn skip_to_next_item(&mut self, from: usize) -> bool {
        let src = self.src;
        let mut at = from.min(src.len());
        let next = loop {
            match src[at..].find('\n') {
                None => break None,
                Some(i) => {
                    let line = at + i + 1;
                    if src[line..].starts_with('$') {
                        break Some(line);
                    }
                    at = line;
                }
            }
        };
        let Some(off) = next else {
            self.lex = Lexer::sub("", src.len(), 0);
            return false;
        };
        let line = src[..off].bytes().filter(|&b| b == b'\n').count() as Line + 1;
        self.lex = Lexer::sub(&src[off..], off, line);
        self.last_end = off;
        true
    }

    fn parse_global(&mut self) -> Result<Item> {
        let dollar = expect!(
            self,
            Kind::Dollar,
            "expected a global declaration starting with '$'"
        );
        let t = self.peek()?;
        match t.kind {
            Kind::At => self.parse_directive(t),
            Kind::Op if self.text(t) == table::SPLICE => {
                let e = self.parse_splice_operand()?;
                Ok(Item::Run(e, Span::new(dollar.span.start, self.last_end)))
            }
            Kind::Word => self.parse_named_global(),
            Kind::LParen => self.parse_operator_global(),
            _ => Err(self.unexpected(&t, "expected a name or directive after '$'")),
        }
    }

    /// A `$ @...` directive: visibility, an import, or an `@`-named definition.
    fn parse_directive(&mut self, at: Token) -> Result<Item> {
        match self.intrinsic_name(at) {
            "import" => self.parse_import(),
            "private" => {
                self.bump()?;
                Ok(Item::Private)
            }
            "public" => Err(self.unexpected(
                &at,
                "there is no '@public': symbols are public by default. Use '$ @private' \
                 to hide the declarations below it",
            )),
            // The two `@`-names bound to a VALUE: `@main`, the program entry, and
            // `@build`, the compile-time entry, whose `@Code` result the driver adds
            // to this module. Both are ordinary definitions with a mandatory
            // signature; the compiler knows nothing about them but their names.
            which @ ("main" | "build") => {
                let at_tok = self.bump()?; // '@main' / '@build'
                let name = self.intern(self.text(at_tok));
                let want_sig = if which == "main" {
                    "expected ':' and a type for '@main'"
                } else {
                    "expected ':' and a type for '@build'"
                };
                expect!(self, Kind::Colon, want_sig);
                let sig = self.parse_signature()?;
                let body = self.parse_def_body()?;
                let body = self.bind_signature(sig, body);
                Ok(Item::Def {
                    name,
                    sig: Some(sig),
                    body,
                })
            }
            // A blessed interface TYPE (`$ @IRange : (b: @Type) -> (t: @Type) ->
            // @Type = @struct range: b -> b -> t,`). The compiler resolves a value
            // of it at the matching desugar site and projects its single field, so
            // the name is fixed and only CORE declares it; an implementation is an
            // ordinary value (`$ r : @IRange @Int (@Vec @Int) = .{ .range = ... }`).
            name if crate::typing::types::is_blessed_interface(&format!("@{name}")) => {
                let at_tok = self.bump()?; // the '@I...' token
                let iname = self.intern(self.text(at_tok));
                expect!(self, Kind::Colon, "expected ':' and a signature for the interface type");
                let sig = self.parse_signature()?;
                expect!(self, Kind::Eq, "expected '=' after the type signature");
                if !self.at_intrinsic("struct")? {
                    return Err(self.unexpected(
                        &at_tok,
                        "a blessed interface is declared as a one-field '@struct'",
                    ));
                }
                Ok(self.parse_type_decl(iname, sig)?.expect("at '@struct'"))
            }
            // A builtin declaration (`$ @iadd : t -> t -> t = @extern "ares"`): the
            // one other `@`-named value, and the checker allows it only in CORE.
            _ if matches!(self.peek_at(1)?.kind, Kind::Colon) => {
                let at_tok = self.bump()?;
                let name = self.intern(self.text(at_tok));
                self.bump()?; // ':'
                let sig = self.parse_signature()?;
                let body = self.parse_def_body()?;
                if !matches!(self.ast.expr(body), Expr::Builtin) {
                    return Err(self.unexpected(
                        &at_tok,
                        &format!(
                            "'{}' is a compiler intrinsic and is not extensible in user \
                             code; an '@'-named value is '@main', '@build', or a builtin \
                             defined as '@extern \"ares\"'",
                            self.text(at_tok)
                        ),
                    ));
                }
                Ok(Item::Def {
                    name,
                    sig: Some(sig),
                    body,
                })
            }
            other => Err(self.unexpected(
                &at,
                &format!(
                    "'@{other}' is a compiler intrinsic and is not extensible in user code; \
                     only '@main', '@build', builtins and the blessed interface types may \
                     be declared"
                ),
            )),
        }
    }

    /// `$ (op) : sig = body`: a definition bound under the symbolic operator name
    /// `op`. It becomes a plain [`Item::Def`], so it flows through the same
    /// collection, type-checking, and lowering as a `$ name` def and joins `op`'s
    /// name (a use like `a op b` then references it).
    fn parse_operator_global(&mut self) -> Result<Item> {
        self.bump()?; // '('
        let op_tok = expect!(self, Kind::Op, "expected an operator inside '( )'");
        if self.text(op_tok) == table::SPLICE {
            return Err(self.splice_not_a_function(&op_tok));
        }
        let op = self.intern(self.text(op_tok));
        expect!(self, Kind::RParen, "expected ')' after the operator");
        expect!(self, Kind::Colon, "expected ':' and a type for the operator");
        let sig = self.parse_signature()?;
        let body = self.parse_def_body()?;
        let body = self.bind_signature(sig, body);
        Ok(Item::Def {
            name: op,
            sig: Some(sig),
            body,
        })
    }

    /// `$ @import module` or `$ @import ALIAS = module`: one module per item.
    fn parse_import(&mut self) -> Result<Item> {
        self.bump()?; // '@import'
        let start = self.here()?;
        let first = self.parse_dotted_name()?;
        let span = Span::new(start, self.last_end);
        if !self.eat(|k| matches!(k, Kind::Eq))? {
            return Ok(Item::Import { module: first, alias: None, span });
        }
        let alias = match self.ast.slice(first) {
            [alias] if is_upper(self.ast.text(*alias)) => *alias,
            _ => {
                return Err(Diagnostic::error(
                    Code::BadModuleName,
                    span,
                    0,
                    "an import alias is a single capitalized name",
                )
                .with_help("write `$ @import ALIAS = MODULE`, e.g. `$ @import V = VEC`"))
            }
        };
        let start = self.here()?;
        let module = self.parse_dotted_name()?;
        let span = Span::new(start, self.last_end);
        Ok(Item::Import { module, alias: Some(alias), span })
    }

    fn parse_dotted_name(&mut self) -> Result<Slice<StrId>> {
        let first = expect!(self, Kind::Word, "expected a module name");
        let mut names = vec![self.intern(self.text(first))];
        while matches!(self.peek_kind()?, Kind::Dot) {
            self.bump()?;
            let part = expect!(self, Kind::Word, "expected a name after '.'");
            names.push(self.intern(self.text(part)));
        }
        Ok(self.ast.make_slice(names))
    }

    /// `$ name ...`: a value definition, or a struct/union/alias/effect type.
    fn parse_named_global(&mut self) -> Result<Item> {
        let name_tok = self.bump()?;
        let name = self.intern(self.text(name_tok));
        if !self.eat(|k| matches!(k, Kind::Colon))? {
            expect!(self, Kind::Eq, "expected ':' or '=' after the name");
            self.require_value_lowercase(self.text(name_tok), &name_tok)?;
            return Ok(Item::Def {
                name,
                sig: None,
                body: self.parse_expr(0)?,
            });
        }
        // A capitalized name with a signature defines a type: types are
        // expressions (#406), so `$ Frac : @Type 1 = {Integer, Pos}`. A body
        // starting `@struct` or `@union` declares one, its signature stating
        // the parameters: `$ Vec : (a: @Type) -> @Nat -> @Type = @union Nil:
        // {} -> Vec a 0, ...`. A signature ending in `@Effect` declares an
        // effect, its body the operations: `$ Fail : @Effect = fail : ...`.
        let sig = self.parse_signature()?;
        let effect = self.ends_in_effect(sig);
        if effect || self.at_type_decl()? {
            self.require_type_capital(self.text(name_tok), &name_tok)?;
        }
        if !effect {
            self.reject_field_list()?;
        }
        if is_upper(self.text(name_tok)) && (self.ctx_written.is_none() || effect) {
            expect!(self, Kind::Eq, "expected '=' after the type signature");
            if let Some(item) = self.parse_type_decl(name, sig)? {
                return Ok(item);
            }
            let body = self.parse_expr(0)?;
            let body = self.bind_signature(sig, body);
            if let Some(item) = self.type_function(name, sig, body)? {
                return Ok(item);
            }
            return Ok(Item::Def { name, sig: Some(sig), body });
        }
        let body = self.parse_def_body()?;
        let body = self.bind_signature(sig, body);
        if let Some(item) = self.type_function(name, sig, body)? {
            return Ok(item);
        }
        Ok(Item::Def {
            name,
            sig: Some(sig),
            body,
        })
    }

    /// Whether `= @struct` or `= @union` comes next.
    fn at_type_decl(&mut self) -> Result<bool> {
        if !matches!(self.peek_kind()?, Kind::Eq) {
            return Ok(false);
        }
        let t = self.peek_at(1)?;
        Ok(matches!(t.kind, Kind::At) && matches!(self.intrinsic_name(t), "struct" | "union"))
    }

    /// Whether a signature ends in `@Effect` after its arrows: the global
    /// declares an effect.
    fn ends_in_effect(&self, sig: Aol<Ty>) -> bool {
        let mut cod = sig;
        while let Ty::Arrow { to, .. } = self.ast.ty(cod) {
            cod = *to;
        }
        matches!(self.ast.ty(cod), Ty::Con { module: None, name } if name.as_str() == "@Effect")
    }

    /// A body `= name : Type, ...` is a list of operations, which only an
    /// effect has: expression ascription is written in parentheses.
    fn reject_field_list(&mut self) -> Result<()> {
        if !matches!(self.peek_kind()?, Kind::Eq) {
            return Ok(());
        }
        let word = self.peek_at(1)?;
        if self.group_len_at(1)? == 0 {
            return Ok(());
        }
        Err(Diagnostic::error(
            Code::UnexpectedToken,
            word.span,
            word.line,
            "a list of `name : Type` operations declares an effect".to_string(),
        )
        .with_note("an effect's signature ends in `@Effect`")
        .with_help("declare it as `$ Name : @Effect = op : Type, ...`"))
    }

    /// The body of a type declaration after `=`: `@struct [@extern "abi"]
    /// fields` or `@union [@extern "abi"] variants`, or an effect's
    /// operations when `sig` ends in `@Effect`, or `None` for any other body.
    /// `sig` states the parameters, each a named binder:
    /// `(a: @Type) -> (n: @Nat) -> @Type`. A union may
    /// go on with indices, binders its constructors' stated results do not pass
    /// through as themselves (the kernel's rule, #536).
    fn parse_type_decl(&mut self, name: StrId, sig: Aol<Ty>) -> Result<Option<Item>> {
        let at_tok = self.peek()?;
        let kw = if self.ends_in_effect(sig) {
            "effect"
        } else if matches!(at_tok.kind, Kind::At) && matches!(self.intrinsic_name(at_tok), "struct" | "union") {
            self.intrinsic_name(at_tok)
        } else {
            return Ok(None);
        };
        if let Some(f) = self.ast.ctx_params.get(sig).map(|fs| self.ast.slice(*fs)[0]) {
            let written = self.ast.ty_span(f.ty).map_or("@Type", |s| &self.src[s.start..s.end]);
            return Err(Diagnostic::error(
                Code::UnexpectedToken,
                f.span,
                at_tok.line,
                format!("a type declaration binds `{}` as a parameter, not in `@ctx`", f.name),
            )
            .with_help(format!("write it on the signature's arrows: `({}: {written}) -> ... -> @Type`", f.name)));
        }
        self.class_universe(sig, kw, &at_tok)?;
        if kw != "effect" {
            self.bump()?; // the keyword
        }
        let abi = if kw != "effect" && self.at_intrinsic("extern")? {
            self.bump()?; // '@extern'
            Some(self.expect_string("expected an ABI string after '@extern'")?)
        } else {
            None
        };
        let binders = self.decl_binders(sig, kw)?;
        let named = |n: usize| binders[..n].iter().map(|b| b.expect("checked by decl_binders")).collect::<Vec<_>>();
        let item = match kw {
            "struct" => {
                let (splices, fields) = self.parse_struct_body()?;
                let params = self.ast.make_slice(named(binders.len()));
                Item::Struct { name, sig, params, splices, fields, abi, c_union: false }
            }
            "union" if abi.is_some() => {
                let (splices, fields) = self.parse_struct_body()?;
                let params = self.ast.make_slice(named(binders.len()));
                Item::Struct { name, sig, params, splices, fields, abi, c_union: true }
            }
            "union" => {
                let (splices, variants) = self.parse_union_body()?;
                let uniform = self.uniform_params(name, &binders, self.ast.slice(variants));
                let params = self.ast.make_slice(named(uniform));
                Item::Union { name, sig, params, splices, variants }
            }
            _ => {
                let ops = self.parse_effect_body()?;
                let params = self.ast.make_slice(named(binders.len()));
                Item::Effect { name, sig, params, ops }
            }
        };
        Ok(Some(item))
    }

    /// A declaration whose signature ends in `@Class` is an interface: its
    /// values are instances, found by search. Only a `@struct` is one, and
    /// past the search it is a record, so its universe reads as `@Type`.
    fn class_universe(&mut self, sig: Aol<Ty>, kw: &str, at_tok: &Token) -> Result<()> {
        let mut cod = sig;
        while let Ty::Arrow { to, .. } = self.ast.ty(cod) {
            cod = *to;
        }
        if !matches!(self.ast.ty(cod), Ty::Con { module: None, name } if name.as_str() == "@Class") {
            return Ok(());
        }
        let abi = self.peek_at(1)?;
        if kw != "struct" || (matches!(abi.kind, Kind::At) && self.intrinsic_name(abi) == "extern") {
            let span = self.ast.ty_span(cod).unwrap_or(at_tok.span);
            return Err(Diagnostic::error(Code::UnexpectedToken, span, at_tok.line, "only a `@struct` is a `@Class`")
                .with_note("a class's values are records of operations, which instance search finds by type"));
        }
        let universe = self.intern("@Type");
        self.ast.replace_ty(cod, Ty::Con { module: None, name: universe });
        self.ast.classes.insert(sig, ());
        Ok(())
    }

    /// The binders of a type declaration's signature, one per arrow. A
    /// struct's and an effect's are all named; a union's unnamed ones must
    /// come last, as its indices.
    fn decl_binders(&mut self, sig: Aol<Ty>, kw: &str) -> Result<Vec<Option<StrId>>> {
        let mut binders = Vec::new();
        let mut cod = sig;
        while let Ty::Arrow { binder, effect, to, .. } = self.ast.ty(cod) {
            if effect.is_some() {
                return Err(self.decl_sig_error(cod, "a type declaration's signature carries no effect row"));
            }
            if binder.is_none() && kw != "union" {
                let what = if kw == "effect" { "an effect" } else { "a struct" };
                return Err(self.decl_sig_error(cod, &format!(
                    "{what} has no indices: name each parameter, as in `(a: @Type) -> @Type`"
                )));
            }
            if binder.is_some() && binders.last().is_some_and(Option::is_none) {
                return Err(self.decl_sig_error(cod, "a named parameter comes before the indices"));
            }
            binders.push(*binder);
            cod = *to;
        }
        Ok(binders)
    }

    fn decl_sig_error(&self, at: Aol<Ty>, msg: &str) -> Diagnostic {
        Diagnostic::error(Code::UnexpectedToken, self.ast.ty_span(at).unwrap_or(Span::at(0)), 0, msg.to_string())
    }

    /// How many leading binders of a union's signature are parameters: named,
    /// and passed through as themselves by every constructor's stated result,
    /// `Vec a ...`. The rest are indices, as in the kernel.
    fn uniform_params(&self, name: StrId, binders: &[Option<StrId>], variants: &[VariantDecl]) -> usize {
        let named = binders.iter().take_while(|b| b.is_some()).count();
        variants
            .iter()
            .filter_map(|v| v.result)
            .map(|result| {
                let mut args = Vec::new();
                let mut head = result;
                while let Ty::App(f, a) = self.ast.ty(head) {
                    args.push(*a);
                    head = *f;
                }
                if !matches!(self.ast.ty(head), Ty::Con { name: n, .. } if *n == name) {
                    return 0;
                }
                args.reverse();
                let passes = |(b, a): (&Option<StrId>, &Aol<Ty>)| {
                    matches!(self.ast.ty(*a), Ty::Var(v) | Ty::Con { module: None, name: v } if Some(*v) == *b)
                };
                binders[..named].iter().zip(&args).take_while(|&p| passes(p)).count()
            })
            .min()
            .unwrap_or(named)
    }

    /// A definition whose signature ends in `@Type` after pure arrows, with a
    /// lambda binding a lowercase name per arrow, is a
    /// type-level function (#535): its body read as a type is what the checker
    /// unfolds. Any other shape stays a definition.
    fn type_function(&mut self, name: StrId, sig: Aol<Ty>, body: Aol<Expr>) -> Result<Option<Item>> {
        if self.ast.ctx_params.get(sig).is_some() {
            return Ok(None);
        }
        let mut arity = 0;
        let mut cod = sig;
        while let Ty::Arrow { effect: None, to, .. } = self.ast.ty(cod) {
            arity += 1;
            cod = *to;
        }
        let universe = |t: &Ty| matches!(t, Ty::Con { module: None, name } if name.as_str() == "@Type");
        let is_type = match self.ast.ty(cod) {
            Ty::App(head, _) => universe(self.ast.ty(*head)),
            t => universe(t),
        };
        if !is_type {
            return Ok(None);
        }
        let mut params = Vec::new();
        let mut inner = body;
        while params.len() < arity {
            let Expr::Lambda { params: ps, body: b } = self.ast.expr(inner) else { return Ok(None) };
            for p in self.ast.slice(*ps) {
                match self.ast.pat(p.pat) {
                    Pattern::Var(v) if !is_upper(v.as_str()) => params.push(*v),
                    _ => return Ok(None),
                }
            }
            inner = *b;
        }
        if params.len() != arity {
            return Ok(None);
        }
        let ty = self.to_ty(inner)?;
        let params = self.ast.make_slice(params);
        Ok(Some(Item::Alias { name, params, ty, sig, body }))
    }

    /// Parse a definition's type signature. `@ctx {f: T, ...} ->` parameters may
    /// stand anywhere on its arrow spine. Their fields, with the place each was
    /// written, go in [`Ast::level_params`] (the `@l` ones) and
    /// [`Ast::ctx_params`] (the rest) under the returned signature, the arrows
    /// written between them. Which of the rest are instance fields the checker
    /// decides, from each field's type.
    fn parse_signature(&mut self) -> Result<Aol<Ty>> {
        let mut levels: Vec<UseField> = Vec::new();
        let mut ctx: Vec<UseField> = Vec::new();
        let mut params: Vec<(usize, Option<(StrId, Span)>, Aol<Ty>, Option<EffectRow>)> = Vec::new();
        let mut level_cond = None;
        self.ctx_written = None;
        let result = loop {
            if self.at_ctx()? && matches!(self.peek_kind_at(1)?, Kind::LBrace) {
                let leading = params.is_empty() && ctx.is_empty() && levels.is_empty();
                let cond = self.parse_ctx_fields(params.len() as u32, leading, &mut levels, &mut ctx)?;
                if cond.is_some() {
                    level_cond = cond;
                }
                self.binder_arrow("@ctx")?;
                continue;
            }
            if self.at_ctx()? {
                if self.ctx_written.is_some() {
                    return Err(self.ctx_reserved()?);
                }
                let kw = self.bump()?; // '@ctx'
                let e = self.parse_expr(table::ARROW.left + 1)?;
                let ty = self.to_ty(e)?;
                let span = Span::new(kw.span.start, self.last_end);
                expect!(self, Kind::Arrow, "expected '->' after the `@ctx` parameter");
                self.ctx_written = Some(CtxWritten { kw, ty, span });
                continue;
            }
            let at = self.here()?;
            let from = self.parse_expr(table::ARROW.left + 1)?;
            if !matches!(self.peek_kind()?, Kind::Arrow) {
                break self.to_ty(from)?;
            }
            self.bump()?; // '->'
            let effect = self.parse_effect_row_opt()?;
            self.expect_type_after_arrow()?;
            let (binder, from) = self.arrow_domain(from)?;
            params.push((at, binder, from, effect));
        };
        let mut to = result;
        for (at, binder, from, effect) in params.into_iter().rev() {
            to = self.arrow_ty(at, binder, from, effect, to);
        }
        self.record_ctx(to, levels, ctx, level_cond);
        Ok(to)
    }

    /// File a signature's `@ctx` levels and other fields under it.
    fn record_ctx(&mut self, sig: Aol<Ty>, levels: Vec<UseField>, ctx: Vec<UseField>, cond: Option<Aol<Expr>>) {
        if let Some(cond) = cond {
            self.ast.level_constraints.insert(sig, cond);
        }
        if !levels.is_empty() {
            let levels = self.ast.make_slice(levels);
            self.ast.level_params.insert(sig, levels);
        }
        if !ctx.is_empty() {
            let ctx = self.ast.make_slice(ctx);
            self.ast.ctx_params.insert(sig, ctx);
        }
    }

    /// The `->` after a `@ctx` parameter, which carries no effect row.
    fn binder_arrow(&mut self, binder: &str) -> Result<()> {
        let t = self.peek()?;
        if !matches!(t.kind, Kind::Arrow) {
            return Err(self.unexpected(&t, &format!("expected '->' after the `{binder}` parameter")));
        }
        self.bump()?; // '->'
        if self.parse_effect_row_opt()?.is_some() {
            return Err(Diagnostic::error(
                Code::UnexpectedToken,
                Span::new(t.span.start, self.last_end),
                t.line,
                format!("a `{binder}` parameter's arrow cannot carry an effect row"),
            )
            .with_note(format!("call sites never apply a `{binder}` parameter, so nothing can perform it")));
        }
        Ok(())
    }

    /// The `{name: Type, ...}` of a `@ctx` parameter, from its keyword. A field
    /// of type `@l` is a level, bound only by the signature's first `@ctx`
    /// ahead of every parameter (`leading`); a field whose type is no sort is
    /// an instance, found by search, and goes in `uses`; the others go in
    /// `ctx`. A name is unique across the signature's fields. The fields may
    /// end in `if cond`, the constraints on the levels, returned.
    fn parse_ctx_fields(
        &mut self,
        before: u32,
        leading: bool,
        levels: &mut Vec<UseField>,
        ctx: &mut Vec<UseField>,
    ) -> Result<Option<Aol<Expr>>> {
        self.bump()?; // '@ctx'
        self.bump()?; // '{'
        if matches!(self.peek_kind()?, Kind::RBrace) {
            let t = self.peek()?;
            return Err(self.unexpected(&t, "expected a `name: Type` field: a `@ctx` parameter names at least one"));
        }
        loop {
            let n = self.group_len()?;
            if n == 0 {
                self.expect_word("expected a `name: Type` field in the `@ctx` parameter")?;
                let at = self.peek()?;
                return Err(self
                    .unexpected(&at, "expected ':' after the `@ctx` field name")
                    .with_help("a `@ctx` field is named, as in `@ctx {t: @Type}`"));
            }
            let (names, mark) = self.group_names(n)?;
            for (t, name) in names {
                self.group_type(mark);
                self.parse_ctx_field(t, name, before, leading, levels, ctx)?;
            }
            if matches!(self.peek_kind()?, Kind::If) {
                let at = self.peek()?;
                if levels.is_empty() {
                    return Err(Diagnostic::error(Code::UnexpectedToken, at.span, at.line, "an `if` in a `@ctx` constrains its levels, and this one binds none")
                        .with_help("bind the levels it constrains, as in `@ctx {n: @l, m: @l if n < m}`"));
                }
                self.bump()?; // 'if'
                let cond = self.parse_expr(0)?;
                expect!(self, Kind::RBrace, "expected '}' after the `if` that ends the `@ctx` fields");
                return Ok(Some(cond));
            }
            if !self.eat(|k| matches!(k, Kind::Comma))? || matches!(self.peek_kind()?, Kind::RBrace) {
                break;
            }
        }
        expect!(self, Kind::RBrace, "expected '}' to close the `@ctx` parameter");
        Ok(None)
    }

    /// One `@ctx` field `name: T`, its name `t` read and the cursor on `T`:
    /// a level `@l` goes in `levels`, any other field in `ctx`.
    fn parse_ctx_field(
        &mut self,
        t: Token,
        name: StrId,
        before: u32,
        leading: bool,
        levels: &mut Vec<UseField>,
        ctx: &mut Vec<UseField>,
    ) -> Result<()> {
        // `@l if ...`: the `if` ends the fields, never an argument of `@l`.
        let ty = if self.at_intrinsic("l")? && matches!(self.peek_kind_at(1)?, Kind::If) {
            let at = self.peek()?;
            self.bump()?; // '@l'
            let name = self.intern("@l");
            let node = self.ty(Ty::Con { module: None, name });
            self.ast.ty_spans.insert(node, at.span);
            node
        } else {
            self.parse_type()?
        };
        let span = Span::new(t.span.start, self.last_end);
        if levels.iter().chain(ctx.iter()).any(|f| f.name == name) {
            return Err(Diagnostic::error(
                Code::DuplicateSymbol,
                t.span,
                t.line,
                format!("`{name}` is bound twice in this signature"),
            ));
        }
        let field = UseField { name, ty, before, span };
        match self.ast.ty(ty) {
            Ty::Con { module: None, name: k } if k.as_str() == "@l" => {
                if !leading {
                    return Err(Diagnostic::error(Code::UnexpectedToken, t.span, t.line, format!("the level `{name}` is bound after a parameter"))
                        .with_help("bind every level in the signature's first `@ctx`, ahead of its parameters"));
                }
                levels.push(field);
            }
            _ => ctx.push(field),
        }
        Ok(())
    }

    /// The `@ctx {..} ->` opening a constructor's or effect operation's type,
    /// binding the variables it uses beyond the declaration's parameters.
    /// Levels are the declaration's, so `@l` fields are an error here.
    fn parse_own_ctx(&mut self, what: &str) -> Result<Vec<UseField>> {
        if !(self.at_ctx()? && matches!(self.peek_kind_at(1)?, Kind::LBrace)) {
            return Ok(Vec::new());
        }
        let (mut levels, mut ctx) = (Vec::new(), Vec::new());
        self.parse_ctx_fields(0, true, &mut levels, &mut ctx)?;
        if let Some(l) = levels.first() {
            return Err(Diagnostic::error(Code::UnexpectedToken, l.span, 0, format!("{what} binds no level"))
                .with_help(format!("bind `{}` in the declaration's signature", l.name)));
        }
        self.binder_arrow("@ctx")?;
        Ok(ctx)
    }

    /// After `->` and its row: a type must follow.
    fn expect_type_after_arrow(&mut self) -> Result<()> {
        let t = self.peek()?;
        let prefix = matches!(t.kind, Kind::Op) && (self.text(t) == table::SPLICE || table::prefix(self.text(t)).is_some());
        if self.starts_operand(t.kind) || prefix || matches!(t.kind, Kind::Dot | Kind::Do) {
            return Ok(());
        }
        Err(self.unexpected(&t, "expected a type"))
    }

    /// The error for `@ctx`, which dependent types (#406) will give its own meaning.
    fn ctx_reserved(&mut self) -> Result<Diagnostic> {
        let t = self.peek()?;
        Ok(Self::ctx_reserved_at(&t)
            .with_help("an instance parameter is a named `@ctx` field: `@ctx {d: IOrd t} -> ...`, with `d` in scope in the body"))
    }

    fn ctx_reserved_at(kw: &Token) -> Diagnostic {
        Diagnostic::error(Code::UnexpectedToken, kw.span, kw.line, "a `@ctx` parameter is a record of named fields")
            .with_note("each field is solved by its sort: `@ctx {t: @Type, d: IOrd t}` unifies `t` and searches for `d`")
    }

    /// `= body` after a definition's signature. A `@ctx T ->` parameter in that
    /// signature is reported here, with the body in hand: the rewrite to
    /// `@ctx {d: T} ->` also drops the body's lambda parameter `d`, which the
    /// field now binds by name.
    fn parse_def_body(&mut self) -> Result<Aol<Expr>> {
        let Some(ctx) = self.ctx_written.take() else {
            expect!(self, Kind::Eq, "expected '=' after the type signature");
            return self.parse_expr(0);
        };
        let body = match self.eat(|k| matches!(k, Kind::Eq))? {
            true => self.parse_expr(0).ok(),
            false => None,
        };
        Err(match body {
            Some(body) => self.ctx_use_fix(ctx, body),
            None => self.ctx_use_help(Self::ctx_reserved_at(&ctx.kw), ctx.ty),
        })
    }

    /// The `@ctx` error with the edit to named fields: they are named after the
    /// lambda parameter that bound the context (a name, or a tuple of names for
    /// `@ctx {A, B}`), and that parameter is dropped from the body.
    fn ctx_use_fix(&self, ctx: CtxWritten, body: Aol<Expr>) -> Diagnostic {
        let d = Self::ctx_reserved_at(&ctx.kw);
        let Expr::Lambda { params, body: inner } = self.ast.expr(body) else {
            return self.ctx_use_help(d, ctx.ty);
        };
        let params = self.ast.slice(*params);
        let parts: Vec<Aol<Ty>> = match self.ast.ty(ctx.ty) {
            Ty::Tuple(tys) => self.ast.slice(*tys).to_vec(),
            _ => vec![ctx.ty],
        };
        let first = params[0];
        let names: Option<Vec<String>> = match (self.ast.pat(first.pat), parts.len()) {
            _ if first.sig.is_some() => None,
            (Pattern::Var(n), 1) => Some(vec![n.as_str().to_string()]),
            (Pattern::Wild, 1) => Some(vec!["d".to_string()]),
            (Pattern::Tuple(ps), k) if k > 1 && self.ast.slice(*ps).len() == k => self
                .ast
                .slice(*ps)
                .iter()
                .map(|p| match self.ast.pat(*p) {
                    Pattern::Var(n) => Some(n.as_str().to_string()),
                    _ => None,
                })
                .collect(),
            _ => None,
        };
        let texts: Option<Vec<&str>> = parts.iter().map(|t| self.ast.ty_span(*t).map(|s| &self.src[s.start..s.end])).collect();
        let (Some(names), Some(texts), Some(p0), Some(lam)) =
            (names, texts, self.ast.pat_span(first.pat), self.ast.expr_span(body))
        else {
            return self.ctx_use_help(d, ctx.ty);
        };
        let fields: Vec<String> = names.iter().zip(&texts).map(|(n, t)| format!("{n}: {t}")).collect();
        let drop = match (params.get(1).and_then(|p| self.ast.pat_span(p.pat)), self.ast.expr_span(*inner)) {
            (Some(p1), _) => Span::new(p0.start, p1.start),
            (None, Some(b)) => Span::new(lam.start, b.start),
            (None, None) => return self.ctx_use_help(d, ctx.ty),
        };
        let unnamed = matches!(self.ast.pat(first.pat), Pattern::Wild);
        d.with_fix(
            "name the instance in a `@ctx` field, in scope by name in the body",
            vec![Edit::new(ctx.span, format!("@ctx {{{}}}", fields.join(", "))), Edit::new(drop, "")],
            if unnamed { Applicability::MaybeIncorrect } else { Applicability::MachineApplicable },
        )
    }

    /// The `@ctx` error with prose help quoting the written type, for a body
    /// whose shape gives no field names.
    fn ctx_use_help(&self, d: Diagnostic, ty: Aol<Ty>) -> Diagnostic {
        let written = self.ast.ty_span(ty).map_or("IOrd t", |s| &self.src[s.start..s.end]);
        let fields = match self.ast.ty(ty) {
            Ty::Tuple(tys) => self
                .ast
                .slice(*tys)
                .iter()
                .enumerate()
                .map(|(i, t)| format!("d{i}: {}", self.ast.ty_span(*t).map_or("T", |s| &self.src[s.start..s.end])))
                .collect::<Vec<_>>()
                .join(", "),
            _ => format!("d: {written}"),
        };
        d.with_help(format!(
            "an instance parameter is a named `@ctx` field: `@ctx {{{fields}}} -> ...`, with each field in scope \
             by name in the body (drop the lambda parameter that bound `{written}`)"
        ))
    }

    /// The body of a definition, with the parameters its signature binds made
    /// explicit: the leading run of parameters that bind by name
    /// ([`Self::named_binding`]). The written lambdas bind the rest, left to
    /// right, so which parameter a lambda binds is read off the signature alone
    /// (#437). The instance fields are the checker's to bind, once it knows
    /// which `@ctx` fields they are.
    fn bind_signature(&mut self, sig: Aol<Ty>, body: Aol<Expr>) -> Aol<Expr> {
        if matches!(self.ast.expr(body), Expr::Extern { .. } | Expr::Builtin) {
            return body;
        }
        let mut cur = sig;
        let mut pats = Vec::new();
        while let &Ty::Arrow { from, to, .. } = self.ast.ty(cur) {
            let Some(pat) = self.named_binding(cur, from) else { break };
            pats.push(LamParam { pat, sig: None });
            cur = to;
        }
        let added = pats.len() as u32;
        let body = self.prepend_params(pats, body);
        if added > 0 {
            self.ast.sig_bound.insert(body, added);
        }
        body
    }

    /// The pattern a signature parameter binds by name, or `None` for a plain
    /// parameter, which a written lambda binds: `(x: A)` binds `x`, a closed
    /// record `{x: A, y: B}` its fields, and `{}` nothing.
    fn named_binding(&mut self, arrow: Aol<Ty>, from: Aol<Ty>) -> Option<Aol<Pattern>> {
        let binder = match self.ast.ty(arrow) {
            Ty::Arrow { binder, .. } => *binder,
            _ => None,
        };
        let (pat, span) = match (binder, self.ast.ty(from)) {
            (Some(name), _) => (Pattern::Var(name), self.ast.binder_spans.get(arrow).copied()),
            (_, Ty::Unit) => (Pattern::Wild, self.ast.ty_span(from)),
            (_, Ty::Record { fields, tail: None }) => {
                let names: Vec<FieldPat> = self.ast.slice(*fields).iter().map(|f| FieldPat::Shorthand(f.name)).collect();
                let fields = self.ast.make_slice(names);
                (Pattern::Record { fields, rest: None }, self.ast.ty_span(from))
            }
            _ => return None,
        };
        let node = self.pat(pat);
        if let Some(span) = span {
            self.ast.pat_spans.insert(node, span);
        }
        Some(node)
    }

    /// `body` with `params` bound ahead of its own lambda's parameters.
    fn prepend_params(&mut self, params: Vec<LamParam>, body: Aol<Expr>) -> Aol<Expr> {
        if params.is_empty() {
            return body;
        }
        let span = self.ast.expr_span(body);
        let node = match *self.ast.expr(body) {
            Expr::Lambda { params: own, body: inner } => {
                let mut all = params;
                all.extend_from_slice(self.ast.slice(own));
                let all = self.ast.make_slice(all);
                self.expr(Expr::Lambda { params: all, body: inner })
            }
            _ => {
                let params = self.ast.make_slice(params);
                self.expr(Expr::Lambda { params, body })
            }
        };
        if let Some(span) = span {
            self.ast.expr_spans.insert(node, span);
        }
        node
    }

    /// Is the next token the `@ctx` keyword?
    fn at_ctx(&mut self) -> Result<bool> {
        let t = self.peek()?;
        Ok(matches!(t.kind, Kind::At) && self.intrinsic_name(t) == "ctx")
    }

    /// Is the next token the `@name` intrinsic keyword?
    fn at_intrinsic(&mut self, name: &str) -> Result<bool> {
        let t = self.peek()?;
        Ok(matches!(t.kind, Kind::At) && self.intrinsic_name(t) == name)
    }


    /// An effect's body: its operations, or `{}` for none.
    fn parse_effect_body(&mut self) -> Result<Slice<FieldDecl>> {
        if matches!(self.peek_kind()?, Kind::LBrace) && matches!(self.peek_at(1)?.kind, Kind::RBrace) {
            self.bump()?;
            self.bump()?;
            return Ok(self.ast.make_slice(Vec::new()));
        }
        if !matches!(self.peek_kind()?, Kind::Word) {
            let t = self.peek()?;
            return Err(self.unexpected(&t, "expected an effect's operations, `name : Type, ...`, or `{}` for none"));
        }
        self.parse_effect_ops()
    }

    /// An effect's operations, `name : Type` like struct fields. A name must
    /// start lowercase: a handler arm `| Name x` would otherwise read as a value
    /// pattern rather than an operation clause.
    fn parse_effect_ops(&mut self) -> Result<Slice<FieldDecl>> {
        let mut ops = Vec::new();
        while matches!(self.peek_kind()?, Kind::Word) {
            let n = self.group_len()?;
            for i in 0..n.max(1) {
                let t = self.peek_at(i)?;
                if is_upper(self.text(t)) {
                    return Err(self.unexpected(&t, "an effect operation name must start lowercase"));
                }
            }
            if n == 0 {
                self.bump()?;
                let t = self.peek()?;
                return Err(self.unexpected(&t, "expected ':' after the operation name"));
            }
            let (names, mark) = self.group_names(n)?;
            for (_, name) in names {
                self.group_type(mark);
                let ctx = self.parse_own_ctx("an effect operation")?;
                let ty = self.parse_type()?;
                self.record_ctx(ty, Vec::new(), ctx, None);
                ops.push(FieldDecl { name, ty });
            }
            if !self.eat(|k| matches!(k, Kind::Comma))? {
                break;
            }
        }
        Ok(self.ast.make_slice(ops))
    }

    /// A struct body: comma-separated `name : Type` fields and `!X` splices
    /// of generated fields, freely interleaved.
    fn parse_struct_body(&mut self) -> Result<(Slice<EntrySplice>, Slice<FieldDecl>)> {
        let mut splices = Vec::new();
        let mut fields = Vec::new();
        loop {
            match self.peek_kind()? {
                _ if self.at_splice()? => splices.push(self.parse_entry_splice()?),
                Kind::Word => {
                    let n = self.group_len()?;
                    if n == 0 {
                        self.bump()?;
                        let t = self.peek()?;
                        return Err(self.unexpected(&t, "expected ':' after the field name"));
                    }
                    let (names, mark) = self.group_names(n)?;
                    for (_, name) in names {
                        self.group_type(mark);
                        let ty = self.parse_type()?;
                        fields.push(FieldDecl { name, ty });
                    }
                }
                _ => break,
            }
            if !self.eat(|k| matches!(k, Kind::Comma))? {
                break;
            }
        }
        Ok((self.ast.make_slice(splices), self.ast.make_slice(fields)))
    }

    fn parse_union_body(&mut self) -> Result<(Slice<EntrySplice>, Slice<VariantDecl>)> {
        let mut splices = Vec::new();
        let mut variants = Vec::new();
        loop {
            match self.peek_kind()? {
                _ if self.at_splice()? => splices.push(self.parse_entry_splice()?),
                Kind::Word => {
                    let tag_span = self.peek()?.span;
                    let tag = self.bump_word()?;
                    let (ctx, ctx_at, payload) = if self.eat(|k| matches!(k, Kind::Colon))? {
                        let at = self.here()?;
                        let ctx = self.parse_own_ctx("a constructor")?;
                        (ctx, Some(at), self.parse_payload()?)
                    } else {
                        (Vec::new(), None, Payload::None)
                    };
                    // `Tag: {fields} -> D a i`: an indexed family's constructor
                    // states its result. A bare payload's arrow is its own type.
                    let result = if !matches!(payload, Payload::Bare(_)) && matches!(self.peek_kind()?, Kind::Arrow) {
                        self.bump()?; // '->'
                        Some(self.parse_type()?)
                    } else {
                        None
                    };
                    if let (Some(f), None) = (ctx.first(), result) {
                        return Err(Diagnostic::error(
                            Code::UnexpectedToken,
                            tag_span,
                            0,
                            format!("constructor `{tag}` binds `{}` in `@ctx` but states no result", f.name),
                        )
                        .with_note("a constructor's own variables are those of the result it states, as in `Cons: @ctx {n: @Nat} -> {a, Vec a n} -> Vec a (n + 1)`")
                        .with_help("write the payload in braces and state the result: `{T} -> D a i`"));
                    }
                    let ctx = self.ast.make_slice(ctx);
                    variants.push(VariantDecl { tag, tag_span, ctx, ctx_at, payload, result });
                }
                _ => break,
            }
            if !self.eat(|k| matches!(k, Kind::Comma))? {
                break;
            }
        }
        Ok((self.ast.make_slice(splices), self.ast.make_slice(variants)))
    }

    /// An `!X` entry in a struct or union declaration. `X` ends at the entry's
    /// comma, and the entry's span is what the generated entries replace.
    fn parse_entry_splice(&mut self) -> Result<EntrySplice> {
        let start = self.here()?;
        let expr = self.parse_splice_operand()?;
        Ok(EntrySplice {
            expr,
            span: Span::new(start, self.last_end),
        })
    }

    fn parse_payload(&mut self) -> Result<Payload> {
        if !matches!(self.peek_kind()?, Kind::LBrace) {
            return Ok(Payload::Bare(self.parse_type()?));
        }
        self.bump()?; // '{'
        let mut fields = Vec::new();
        while !matches!(self.peek_kind()?, Kind::RBrace) {
            // Named fields are `a b : Type`; anything else is a positional type.
            let n = self.group_len()?;
            if n > 0 {
                let (names, mark) = self.group_names(n)?;
                for (_, name) in names {
                    self.group_type(mark);
                    let ty = self.parse_type()?;
                    fields.push(PayloadField {
                        name: Some(name),
                        ty,
                    });
                }
            } else {
                let ty = self.parse_type()?;
                fields.push(PayloadField { name: None, ty });
            }
            if !self.eat(|k| matches!(k, Kind::Comma))? {
                break;
            }
        }
        expect!(
            self,
            Kind::RBrace,
            "expected '}' to close the variant payload"
        );
        Ok(Payload::Fields(self.ast.make_slice(fields)))
    }

    fn peek_kind_at(&mut self, n: usize) -> Result<Kind> {
        Ok(self.lex.peek(n)?.kind)
    }

    // -- types --------------------------------------------------------------
    //
    // Types are expressions (#406): a type position parses an expression and
    // reads it as a [`Ty`], the view the checker elaborates. An expression no
    // `Ty` variant spells (a lambda, `a ~ b`, a projection) stays a term,
    // `Ty::Term`, which the kernel reads and the checker rejects.

    fn parse_type(&mut self) -> Result<Aol<Ty>> {
        if self.at_ctx()? && matches!(self.peek_kind_at(1)?, Kind::LBrace) {
            return Err(self.ctx_param_misplaced()?);
        }
        if self.at_ctx()? {
            return Err(self.ctx_reserved()?);
        }
        let e = self.parse_expr(0)?;
        self.to_ty(e)
    }

    /// One argument of an effect row entry, `<Chan @Int e>`: an atom read as a
    /// type.
    fn parse_type_arg(&mut self) -> Result<Aol<Ty>> {
        let e = self.parse_primary()?;
        self.to_ty(e)
    }

    fn starts_type_arg(&mut self) -> Result<bool> {
        // `@ctx` opens a signature's parameters, and a splice is a prefix
        // operator, so neither is an argument: `@Vec (!f a)`.
        if self.at_ctx()? || self.at_splice()? {
            return Ok(false);
        }
        Ok(matches!(
            self.peek_kind()?,
            Kind::Word | Kind::At | Kind::LParen | Kind::LBrace | Kind::Int(_)
        ))
    }

    /// `@ctx {d: T} ->` anywhere but on a definition's signature.
    fn ctx_param_misplaced(&mut self) -> Result<Diagnostic> {
        let at = self.peek()?;
        Ok(Diagnostic::error(
            Code::UnexpectedToken,
            at.span,
            at.line,
            "a `@ctx` parameter stands only on the arrows of a global's signature",
        )
        .with_note("or first in a constructor's or effect operation's type; not inside a parameter's type, an annotation, a local `let`'s type, or a field type"))
    }

    /// The function type `from -> to` an arrow builds in an expression. A
    /// domain that ascribes a bare name, `(x: A) -> B`, names the parameter.
    fn arrow_expr(
        &mut self,
        start: usize,
        from: Aol<Expr>,
        effect: Option<EffectRow>,
        to: Aol<Expr>,
    ) -> Result<Aol<Expr>> {
        let (binder, from) = self.arrow_domain(from)?;
        let to = self.to_ty(to)?;
        let ty = self.arrow_ty(start, binder, from, effect, to);
        let node = self.expr(Expr::Type(ty));
        Ok(self.stamp(start, node))
    }

    /// The parameter an arrow's domain names, if any, and its type.
    fn arrow_domain(&mut self, from: Aol<Expr>) -> Result<(Option<(StrId, Span)>, Aol<Ty>)> {
        if let Some((name, span, ty)) = self.named_param(from) {
            return Ok((Some((name, span)), ty));
        }
        Ok((None, self.to_ty(from)?))
    }

    /// `(x: A)`: an ascription of a bare lowercase name.
    fn named_param(&self, e: Aol<Expr>) -> Option<(StrId, Span, Aol<Ty>)> {
        let Expr::Ascribe { expr, ty } = self.ast.expr(e) else { return None };
        let Expr::Var { module: None, name } = self.ast.expr(*expr) else { return None };
        if is_upper(name.as_str()) || name.as_str().starts_with('@') {
            return None;
        }
        Some((*name, self.ast.expr_span(*expr)?, *ty))
    }

    fn arrow_ty(
        &mut self,
        start: usize,
        binder: Option<(StrId, Span)>,
        from: Aol<Ty>,
        effect: Option<EffectRow>,
        to: Aol<Ty>,
    ) -> Aol<Ty> {
        let node = self.ty(Ty::Arrow { binder: binder.map(|b| b.0), from, effect, to });
        if let Some((_, span)) = binder {
            self.ast.binder_spans.insert(node, span);
        }
        self.stamp_ty(start, node)
    }

    /// The type an expression in type position denotes. The checker's own
    /// forms keep their shape (names, applications, `@Tensor n T`, sizes,
    /// tuples, records, splices); any other expression is a `Ty::Term`.
    fn to_ty(&mut self, e: Aol<Expr>) -> Result<Aol<Ty>> {
        let span = self.ast.expr_span(e);
        if let Expr::Var { module: None, name } = self.ast.expr(e) {
            if let Some((_, ty)) = self.ty_env.iter().rev().find(|(n, _)| n == name) {
                return Ok(*ty);
            }
        }
        let node = match self.ast.expr(e).clone() {
            Expr::Type(ty) if self.ty_env.is_empty() => return Ok(ty),
            Expr::Type(ty) => return self.subst_ty(ty),
            // `let x = A in B` in a type: `B` with `x` read as `A`, when that
            // leaves a type; otherwise the term, for the kernel to read.
            Expr::Let { binding, body } if self.type_binder(binding.pat).is_some() => {
                let name = self.type_binder(binding.pat).unwrap();
                let value = self.to_ty(binding.value)?;
                let reduced = self.to_ty_under(&[(name, value)], body)?;
                if !self.holds_term(reduced) {
                    return Ok(reduced);
                }
                Ty::Term(e)
            }
            Expr::Var { module: None, name } if name.as_str() == "@Tensor" => {
                let span = span.unwrap_or(Span::at(0));
                return Err(Diagnostic::error(
                    Code::UnexpectedToken,
                    span,
                    0,
                    "a tensor type `@Tensor n T` stands only at the head of an application",
                )
                .with_help("parenthesize it: `(@Tensor n T)`"));
            }
            Expr::Var { module: None, name } if name.as_str() == "_" => Ty::Term(e),
            Expr::Var { module: None, name } => {
                if name.as_str().starts_with(|c: char| c.is_ascii_lowercase()) {
                    Ty::Var(name)
                } else {
                    Ty::Con { module: None, name }
                }
            }
            // `M.f`: a type-level function of module `M`.
            Expr::Var { module: Some(m), name } => Ty::Con { module: Some(m), name },
            // `M.T`: a qualified type reads as a variant of `M` with no payload.
            Expr::Variant { module: None, ty: Some(m), tag, fields } if self.ast.slice(fields).is_empty() => {
                Ty::Con { module: Some(m), name: tag }
            }
            Expr::App(..) => return self.app_ty(e),
            Expr::Int(n) if n >= 0 => Ty::Nat(n as u64),
            Expr::BinOp { op, lhs, rhs } if matches!(op.as_str(), "+" | "*") => {
                let (a, b) = (self.size_ty(lhs)?, self.size_ty(rhs)?);
                if op.as_str() == "+" { Ty::SizeAdd(a, b) } else { Ty::SizeMul(a, b) }
            }
            Expr::Unit => Ty::Unit,
            Expr::Tuple(items) => {
                let items = self.ast.slice(items).to_vec();
                let tys = items.into_iter().map(|t| self.to_ty(t)).collect::<Result<Vec<_>>>()?;
                Ty::Tuple(self.ast.make_slice(tys))
            }
            Expr::Splice(x) => Ty::MetaE(x),
            Expr::Ascribe { .. } if self.named_param(e).is_some() => {
                let (name, ..) = self.named_param(e).unwrap();
                let span = span.unwrap_or(Span::at(0));
                return Err(utilities::diag!(
                    Code::UnexpectedToken, span, 0,
                    "a named parameter `({name}: ...)` stands only before `->`";
                    help: "parenthesize the whole function type: `((x: A) -> B)`"
                ));
            }
            _ => Ty::Term(e),
        };
        let node = self.ty(node);
        if let Some(span) = span {
            self.ast.ty_spans.insert(node, span);
        }
        Ok(node)
    }

    /// `body` read as a type with each of `bound` naming its type.
    fn to_ty_under(&mut self, bound: &[(StrId, Aol<Ty>)], body: Aol<Expr>) -> Result<Aol<Ty>> {
        let depth = self.ty_env.len();
        self.ty_env.extend_from_slice(bound);
        let ty = self.to_ty(body);
        self.ty_env.truncate(depth);
        ty
    }

    /// `ty` with each name `ty_env` binds read as its type. A function type
    /// or record type is built as it is parsed, before an enclosing `let`
    /// is known, so its names are replaced here.
    fn subst_ty(&mut self, ty: Aol<Ty>) -> Result<Aol<Ty>> {
        let node = match self.ast.ty(ty).clone() {
            Ty::Var(name) => {
                let bound = self.ty_env.iter().rev().find(|(n, _)| *n == name);
                return Ok(bound.map_or(ty, |(_, t)| *t));
            }
            Ty::Term(e) => return self.to_ty(e),
            Ty::Con { .. } | Ty::Nat(_) | Ty::Unit | Ty::MetaE(_) => return Ok(ty),
            Ty::App(a, b) => Ty::App(self.subst_ty(a)?, self.subst_ty(b)?),
            Ty::SizeAdd(a, b) => Ty::SizeAdd(self.subst_ty(a)?, self.subst_ty(b)?),
            Ty::SizeMul(a, b) => Ty::SizeMul(self.subst_ty(a)?, self.subst_ty(b)?),
            Ty::Sized { size, elem } => Ty::Sized { size: self.subst_ty(size)?, elem: self.subst_ty(elem)? },
            Ty::Arrow { binder, from, effect, to } => {
                let from = self.subst_ty(from)?;
                let to = match binder {
                    Some(b) => {
                        let own = self.ty(Ty::Var(b));
                        self.ty_env.push((b, own));
                        let to = self.subst_ty(to);
                        self.ty_env.pop();
                        to?
                    }
                    None => self.subst_ty(to)?,
                };
                Ty::Arrow { binder, from, effect, to }
            }
            Ty::Tuple(items) => {
                let items = self.ast.slice(items).to_vec();
                let items = items.into_iter().map(|t| self.subst_ty(t)).collect::<Result<Vec<_>>>()?;
                Ty::Tuple(self.ast.make_slice(items))
            }
            Ty::Record { fields, tail } => {
                let fields = self.ast.slice(fields).to_vec();
                let fields = fields
                    .into_iter()
                    .map(|f| Ok(RecField { name: f.name, ty: self.subst_ty(f.ty)? }))
                    .collect::<Result<Vec<_>>>()?;
                Ty::Record { fields: self.ast.make_slice(fields), tail }
            }
        };
        let node = self.ty(node);
        if let Some(span) = self.ast.ty_span(ty) {
            self.ast.ty_spans.insert(node, span);
        }
        if let Some(&span) = self.ast.binder_spans.get(ty) {
            self.ast.binder_spans.insert(node, span);
        }
        Ok(node)
    }

    /// Whether `ty` keeps an expression inside it. A `let` or lambda whose
    /// body does is left as a term: its names are bound in that expression,
    /// which a type cannot substitute into.
    fn holds_term(&self, ty: Aol<Ty>) -> bool {
        match self.ast.ty(ty) {
            Ty::Term(_) | Ty::MetaE(_) => true,
            Ty::Con { .. } | Ty::Var(_) | Ty::Nat(_) | Ty::Unit => false,
            Ty::App(a, b) | Ty::SizeAdd(a, b) | Ty::SizeMul(a, b) => self.holds_term(*a) || self.holds_term(*b),
            Ty::Sized { size, elem } => self.holds_term(*size) || self.holds_term(*elem),
            Ty::Arrow { from, to, .. } => self.holds_term(*from) || self.holds_term(*to),
            Ty::Tuple(items) => self.ast.slice(*items).iter().any(|t| self.holds_term(*t)),
            Ty::Record { fields, .. } => self.ast.slice(*fields).iter().any(|f| self.holds_term(f.ty)),
        }
    }

    /// The name a `let` or lambda binds in a type: one lowercase variable.
    fn type_binder(&self, pat: Aol<Pattern>) -> Option<StrId> {
        match self.ast.pat(pat) {
            Pattern::Var(v) if !is_upper(v.as_str()) => Some(*v),
            _ => None,
        }
    }

    /// An application in type position: `@Tensor n T` at its head is a sized
    /// tensor, a lambda at its head is applied by binding its parameters, and
    /// any other head is applied to its arguments one at a time.
    fn app_ty(&mut self, e: Aol<Expr>) -> Result<Aol<Ty>> {
        let mut args = Vec::new();
        let mut head = e;
        while let Expr::App(f, a) = *self.ast.expr(head) {
            args.push(a);
            head = f;
        }
        args.reverse();
        let start = self.ast.expr_span(e).map_or(0, |s| s.start);
        let tensor = matches!(self.ast.expr(head), Expr::Var { module: None, name } if name.as_str() == "@Tensor");
        if let Expr::Lambda { params, body } = *self.ast.expr(head) {
            let names: Option<Vec<StrId>> = self.ast.slice(params).iter().map(|p| self.type_binder(p.pat)).collect();
            if let Some(names) = names.filter(|n| n.len() <= args.len()) {
                let mut bound = Vec::new();
                for (name, &arg) in names.into_iter().zip(&args) {
                    bound.push((name, self.to_ty(arg)?));
                }
                let mut ty = self.to_ty_under(&bound, body)?;
                if !self.holds_term(ty) {
                    for &arg in &args[bound.len()..] {
                        let a = self.to_ty(arg)?;
                        ty = self.ty(Ty::App(ty, a));
                    }
                    return Ok(ty);
                }
            }
        }
        let (mut ty, rest) = if tensor {
            if args.len() < 2 {
                let span = self.ast.expr_span(e).unwrap_or(Span::at(0));
                return Err(Diagnostic::error(Code::UnexpectedToken, span, 0, "expected a type: `@Tensor n T` takes a size and an element type"));
            }
            let size = self.size_ty(args[0])?;
            let elem = self.to_ty(args[1])?;
            let node = self.ty(Ty::Sized { size, elem });
            (node, &args[2..])
        } else {
            (self.to_ty(head)?, &args[..])
        };
        let mut end = self.ast.ty_span(ty).map_or(start, |s| s.end);
        if tensor {
            end = self.ast.expr_span(args[1]).map_or(end, |s| s.end);
            self.ast.ty_spans.insert(ty, Span::new(start, end));
        }
        for &arg in rest {
            let a = self.to_ty(arg)?;
            end = self.ast.expr_span(arg).map_or(end, |s| s.end);
            ty = self.ty(Ty::App(ty, a));
            self.ast.ty_spans.insert(ty, Span::new(start, end));
        }
        Ok(ty)
    }

    /// A tensor size: any expression, which the checker evaluates (#535).
    fn size_ty(&mut self, e: Aol<Expr>) -> Result<Aol<Ty>> {
        self.to_ty(e)
    }

    /// The fields of a record type, `{x: A, y: B}` or open `{x: A | r}`, with
    /// the cursor on the first field name (the `{` consumed).
    fn parse_record_type(&mut self, start: usize) -> Result<Aol<Expr>> {
        let mut fields = Vec::new();
        let mut tail = None;
        loop {
            let n = self.group_len()?;
            if n == 0 {
                self.expect_word("expected a record field name")?;
                let t = self.peek()?;
                return Err(self.unexpected(&t, "expected ':' after the field name"));
            }
            let (names, mark) = self.group_names(n)?;
            for (_, name) in names {
                self.group_type(mark);
                let ty = self.parse_type()?;
                fields.push(RecField { name, ty });
            }
            // `{ x: A, y: B | r }`: `| r` opens the record with a row variable.
            if self.at_op("|")? {
                self.bump()?;
                tail = Some(self.expect_tyvar("expected a row variable after '|'")?);
                break;
            }
            if !self.eat(|k| matches!(k, Kind::Comma))? || matches!(self.peek_kind()?, Kind::RBrace) {
                break;
            }
        }
        expect!(self, Kind::RBrace, "expected '}' to close the record type");
        let fields = self.ast.make_slice(fields);
        let ty = self.ty(Ty::Record { fields, tail });
        let ty = self.stamp_ty(start, ty);
        let node = self.expr(Expr::Type(ty));
        Ok(self.stamp(start, node))
    }

    /// An optional effect row right after `->`: `<>`, `<e>`, `<A, B>`,
    /// `<A, B | e>`, or `<| e>`. Effect names are Capitalized (user effects) or
    /// `@`-form (builtin effects like `@IO`); a lowercase name after `|`, or
    /// alone, is the row-polymorphic tail variable, and one among the entries
    /// (`<l, A | e>`) a variable of kind `@Effect`, which takes no
    /// arguments. An entry may be a splice `<!X, @IO>`; what each name
    /// denotes is the checker's call.
    fn parse_effect_row_opt(&mut self) -> Result<Option<EffectRow>> {
        if self.at_op("<>")? {
            self.bump()?;
            return Ok(Some(EffectRow {
                entries: self.ast.make_slice(Vec::new()),
                tail: None,
                tail_span: None,
            }));
        }
        if self.at_op("<|")? {
            self.bump()?;
            let at = self.here()?;
            let tail = self.expect_tyvar("expected a type variable in the effect row")?;
            let tail_span = Some(Span::new(at, self.last_end));
            self.expect_op(">", "expected '>' to close the effect row")?;
            return Ok(Some(EffectRow {
                entries: self.ast.make_slice(Vec::new()),
                tail: Some(tail),
                tail_span,
            }));
        }
        if !self.at_op("<")? {
            return Ok(None);
        }
        self.bump()?; // '<'
        if self.at_tyvar()? && !self.at_label_variable()? {
            let at = self.here()?;
            let tail = self.expect_tyvar("expected a type variable in the effect row")?;
            let tail_span = Some(Span::new(at, self.last_end));
            self.expect_op(">", "expected '>' to close the effect row")?;
            return Ok(Some(EffectRow {
                entries: self.ast.make_slice(Vec::new()),
                tail: Some(tail),
                tail_span,
            }));
        }
        let mut entries = Vec::new();
        loop {
            let start = self.here()?;
            // `!X`: the operand binds tighter than a comparison, so it ends before
            // the `,` or the closing `>`.
            if self.at_splice()? {
                let e = self.parse_splice_operand()?;
                entries.push(RowEntry {
                    name: self.intern(table::SPLICE),
                    args: self.ast.make_slice(Vec::new()),
                    span: Span::new(start, self.last_end),
                    meta: Some(e),
                });
                if !self.eat(|k| matches!(k, Kind::Comma))? {
                    break;
                }
                continue;
            }
            let name = self.expect_effect_label()?;
            let mut args = Vec::new();
            if name.as_str().starts_with(|c: char| c.is_ascii_lowercase()) && self.starts_type_arg()? {
                let t = self.peek()?;
                return Err(self.unexpected(&t, "an effect variable takes no arguments: it stands for a whole effect"));
            }
            while self.starts_type_arg()? {
                args.push(self.parse_type_arg()?);
            }
            let args = self.ast.make_slice(args);
            entries.push(RowEntry {
                name,
                args,
                span: Span::new(start, self.last_end),
                meta: None,
            });
            if !self.eat(|k| matches!(k, Kind::Comma))? {
                break;
            }
        }
        let (tail, tail_span) = if self.at_op("|")? {
            self.bump()?;
            let at = self.here()?;
            let tail = self.expect_tyvar("expected a type variable after '|'")?;
            (Some(tail), Some(Span::new(at, self.last_end)))
        } else {
            (None, None)
        };
        self.expect_op(">", "expected '>' to close the effect row")?;
        Ok(Some(EffectRow {
            entries: self.ast.make_slice(entries),
            tail,
            tail_span,
        }))
    }

    fn expect_op(&mut self, s: &str, what: &str) -> Result<()> {
        if self.at_op(s)? {
            self.bump()?;
            Ok(())
        } else {
            let t = self.peek()?;
            Err(self.unexpected(&t, what))
        }
    }

    // -- expressions: the Pratt core ----------------------------------------

    fn parse_expr(&mut self, min_bp: u8) -> Result<Aol<Expr>> {
        let start = self.here()?;
        let mut lhs = self.parse_prefix()?;
        loop {
            let t = self.peek()?;
            match t.kind {
                Kind::Op => match table::infix(self.text(t)) {
                    // Infix, but binds looser than the caller's floor: stop and
                    // let the outer level fold it.
                    Some(bp) if bp.left < min_bp => break,
                    // Not infix at all. A grammatical delimiter (`|`, `<>`)
                    // legitimately ends the expression; anything else is an
                    // operator with no infix meaning here, reported at its own
                    // span rather than surfacing as a confusing error elsewhere.
                    None => {
                        if table::ends_expr(self.text(t)) {
                            break;
                        }
                        return Err(self.unexpected(&t, "expected an infix operator"));
                    }
                    Some(bp) => {
                        let lexeme = self.text(t).to_string();
                        self.bump()?;
                        let rhs = self.parse_expr(bp.right)?;
                        let node = self.binop_expr(&lexeme, lhs, rhs);
                        lhs = self.stamp(start, node);
                    }
                },
                // A function type: types are expressions (#406).
                Kind::Arrow => {
                    if table::ARROW.left < min_bp {
                        break;
                    }
                    self.bump()?; // '->'
                    let effect = self.parse_effect_row_opt()?;
                    self.expect_type_after_arrow()?;
                    let to = self.parse_expr(table::ARROW.right)?;
                    lhs = self.arrow_expr(start, lhs, effect, to)?;
                }
                _ if self.starts_operand(t.kind) => {
                    if table::APP.left < min_bp {
                        break;
                    }
                    let rhs = self.parse_expr(table::APP.right)?;
                    let node = self.expr(Expr::App(lhs, rhs));
                    lhs = self.stamp(start, node);
                }
                _ => break,
            }
        }
        Ok(lhs)
    }

    /// Tokens that can begin an operand, so juxtaposition means application.
    /// `do` is deliberately excluded (a `do` block is never an argument).
    fn starts_operand(&self, k: Kind) -> bool {
        matches!(
            k,
            Kind::Int(_)
                | Kind::Real(_)
                | Kind::Imaginary(_)
                | Kind::Str
                | Kind::Word
                | Kind::LParen
                | Kind::Let
                | Kind::If
                | Kind::Lambda
                | Kind::LBrace
                | Kind::LBrack
                | Kind::At
        )
    }

    /// `lhs op rhs`. `&&`/`||` are short-circuit, so they become a lazy `if`
    /// rather than a call, and `<|>` becomes the lambda that composes its operands;
    /// every other operator keeps its [`Expr::BinOp`] node.
    fn binop_expr(&mut self, lexeme: &str, lhs: Aol<Expr>, rhs: Aol<Expr>) -> Aol<Expr> {
        match lexeme {
            "&&" => {
                let alt = self.expr(Expr::Bool(false));
                self.expr(Expr::If { cond: lhs, then: rhs, alt })
            }
            "||" => {
                let then = self.expr(Expr::Bool(true));
                self.expr(Expr::If { cond: lhs, then, alt: rhs })
            }
            // Composition becomes the lambda it means, `\x => f (g x)`, so the
            // composed function's effect row is inferred as the UNION of the two
            // rows (a definition with one signature could only share one row, and a
            // row union is not expressible), and a context-bearing operand
            // (`to_string <|> f`) resolves as the head of an ordinary application.
            "<|>" => {
                let x = self.intern("#x");
                let arg = self.expr(Expr::Var { module: None, name: x });
                let inner = self.expr(Expr::App(rhs, arg));
                let body = self.expr(Expr::App(lhs, inner));
                let param = self.pat(Pattern::Var(x));
                let params = self.ast.make_slice(vec![LamParam { pat: param, sig: None }]);
                self.expr(Expr::Lambda { params, body })
            }
            _ => {
                let op = self.intern(lexeme);
                self.expr(Expr::BinOp { op, lhs, rhs })
            }
        }
    }

    fn parse_prefix(&mut self) -> Result<Aol<Expr>> {
        let t = self.peek()?;
        if self.at_splice()? {
            let start = t.span.start;
            let operand = self.parse_splice_operand()?;
            let node = self.expr(Expr::Splice(operand));
            return Ok(self.stamp(start, node));
        }
        if let Kind::Op = t.kind {
            if let Some(name) = table::prefix(self.text(t)) {
                let start = t.span.start;
                self.bump()?;
                let op = self.intern(name);
                let operand = self.parse_expr(table::PREFIX)?;
                let node = self.expr(Expr::UnOp { op, operand });
                return Ok(self.stamp(start, node));
            }
        }
        self.parse_primary()
    }

    /// One atom followed by a left-associative postfix `.` chain.
    fn parse_primary(&mut self) -> Result<Aol<Expr>> {
        let start = self.here()?;
        let lit = self.peek()?;
        let mut base = self.parse_atom()?;
        if matches!(lit.kind, Kind::Int(_) | Kind::Real(_)) && matches!(self.peek_kind()?, Kind::Dot)
        {
            return Err(self.dot_after_number(lit)?);
        }
        while matches!(self.peek_kind()?, Kind::Dot) {
            self.bump()?; // '.'
            base = self.parse_postfix(base)?;
            base = self.stamp(start, base);
        }
        Ok(base)
    }

    /// A `.` after the number literal `lit`. A number has no fields, so this is
    /// either an unfinished decimal (`2.`, which would otherwise read the next
    /// number as a tuple index: `1. 2.2` is `(1).2.2`) or a stray dot.
    fn dot_after_number(&mut self, lit: Token) -> Result<Diagnostic> {
        let dot = self.peek()?;
        let digits = self.text(lit);
        if matches!(lit.kind, Kind::Int(_)) && dot.span.start == lit.span.end {
            let span = Span::new(lit.span.start, dot.span.end);
            return Ok(utilities::diag!(
                Code::NumberParsingFailure, span, lit.line,
                "unfinished decimal literal `{digits}.`"
            )
            .with_fix(
                format!("write the fractional part: `{digits}.0`"),
                vec![Edit::new(span, format!("{digits}.0"))],
                Applicability::MachineApplicable,
            ));
        }
        Ok(utilities::diag!(
            Code::UnexpectedToken, dot.span, dot.line,
            "a number has no fields, so a `.` cannot follow `{digits}`"
        ))
    }

    fn parse_atom(&mut self) -> Result<Aol<Expr>> {
        let start = self.here()?;
        let node = self.parse_atom_inner()?;
        Ok(self.stamp(start, node))
    }

    fn parse_atom_inner(&mut self) -> Result<Aol<Expr>> {
        let t = self.peek()?;
        match t.kind {
            Kind::Int(v) => {
                self.bump()?;
                Ok(self.expr(Expr::Int(v)))
            }
            Kind::Real(v) => {
                self.bump()?;
                Ok(self.expr(Expr::Real(v)))
            }
            // `1.2i` desugars to the `@IImagLit` interface, the way `.[..]` desugars
            // to `@IIndex`: the compiler carries no complex type of its own, and
            // whatever the resolved instance builds is what `1.2i` means.
            Kind::Imaginary(v) => {
                self.bump()?;
                let hook = self.intern("@IImagLit");
                let f = self.expr(Expr::Var { module: None, name: hook });
                let arg = self.expr(Expr::Real(v));
                Ok(self.expr(Expr::App(f, arg)))
            }
            Kind::Str => {
                self.bump()?;
                self.build_string(t)
            }
            Kind::Word => {
                self.bump()?;
                let name = self.intern(self.text(t));
                Ok(self.expr(Expr::Var { module: None, name }))
            }
            Kind::LParen if self.at_operator_ref()? => self.parse_operator_ref(),
            Kind::LParen => self.parse_group(),
            Kind::Let => self.parse_let(),
            Kind::If => self.parse_if(),
            Kind::Do => self.parse_handle(),
            Kind::Lambda => self.parse_lambda(),
            Kind::LBrack => self.parse_list(),
            Kind::At => self.parse_at_term(),
            Kind::LBrace => self.parse_brace_expr(),
            Kind::Dot => self.parse_leading_dot(),
            _ => Err(self.unexpected(&t, "expected an expression")),
        }
    }

    /// The postfix action after a `.`: struct literal, tuple index, variant
    /// constructor, module-qualified variable, or field access.
    fn parse_postfix(&mut self, base: Aol<Expr>) -> Result<Aol<Expr>> {
        let ahead = self.peek()?;
        match ahead.kind {
            Kind::LBrace => {
                let ty = self.expect_bare_type_name(base, &ahead, "a struct literal")?;
                self.parse_struct_lit(Some(ty))
            }
            Kind::Int(_) | Kind::Real(_) => {
                let tok = self.bump()?;
                Ok(self.tuple_indices(base, tok))
            }
            // `recv.[i]` / `recv.[i, j, ...]`: an all-index access desugars to the
            // `@IIndex` interface, so tensors, maps, and user types share the
            // surface; a comma-list nests. A `p ... q` slot is an INCLUSIVE range
            // slice of the leading axis (`@tensor_slice`).
            Kind::LBrack => {
                self.bump()?; // '['
                let mut slots: Vec<SliceSlot> = Vec::new();
                loop {
                    // A leading `..` (two `Dot`s, not the `...` range token) is a full
                    // axis; otherwise an expression, optionally `lo ... hi` for a range.
                    if matches!(self.peek_kind()?, Kind::Dot)
                        && matches!(self.peek_kind_at(1)?, Kind::Dot)
                    {
                        self.bump()?;
                        self.bump()?;
                        slots.push(SliceSlot::Full);
                    } else {
                        let lo = self.parse_expr(0)?;
                        if matches!(self.peek_kind()?, Kind::Ellipsis) {
                            self.bump()?;
                            let hi = self.parse_expr(0)?;
                            slots.push(SliceSlot::Range(lo, hi));
                        } else {
                            slots.push(SliceSlot::Index(lo));
                        }
                    }
                    if !self.eat(|k| matches!(k, Kind::Comma))? {
                        break;
                    }
                }
                expect!(self, Kind::RBrack, "expected ']' to close the index");
                // An all-index access desugars to the `@IIndex` interface (so
                // tensors, maps, and user types share `.[..]`); if any slot keeps an
                // axis (a range or `..`), it is a tensor slice whose result shape the
                // checker computes from the receiver.
                if slots.iter().all(|s| matches!(s, SliceSlot::Index(_))) {
                    // The synthetic head carries the whole access's span, because
                    // that is where a failure to resolve its instance is reported.
                    let start = self.ast.expr_span(base).map_or(ahead.span.start, |s| s.start);
                    let mut recv = base;
                    for s in slots {
                        let SliceSlot::Index(idx) = s else { unreachable!() };
                        let index_fn = self.intern("@IIndex");
                        let f = self.expr(Expr::Var { module: None, name: index_fn });
                        let f = self.stamp(start, f);
                        let f = self.expr(Expr::App(f, recv));
                        recv = self.expr(Expr::App(f, idx));
                    }
                    Ok(recv)
                } else {
                    let slots = self.ast.make_slice(slots);
                    Ok(self.expr(Expr::Slice { recv: base, slots }))
                }
            }
            Kind::Word if is_upper(self.text(ahead)) => {
                // A builtin type's constructor, such as the kernel's
                // `@Nat.Succ.{ n }`.
                let builtin = self.bare_var_name(base).filter(|n| self.ast.text(*n).strip_prefix('@').is_some_and(is_upper));
                let ty = match builtin {
                    Some(name) => name,
                    None => self.expect_bare_type_name(base, &ahead, "a variant constructor")?,
                };
                self.bump()?; // the tag / type name
                let ahead_name = self.intern(self.text(ahead));
                // `Module.Type.Tag`: another uppercase `.Name` follows.
                let qualifies = matches!(self.peek_kind()?, Kind::Dot)
                    && matches!(self.peek_kind_at(1)?, Kind::Word)
                    && {
                        let t1 = self.peek_at(1)?;
                        is_upper(self.text(t1))
                    };
                if qualifies {
                    self.bump()?; // '.'
                    let tag = self.bump_word()?;
                    self.parse_variant_lit(Some(ty), Some(ahead_name), tag)
                } else {
                    self.parse_variant_lit(None, Some(ty), ahead_name)
                }
            }
            Kind::Word => {
                // `Module.name`: uppercase base, lowercase member -> qualified var.
                if let Some(name) = self.bare_var_name(base) {
                    if is_upper(self.ast.text(name)) {
                        self.bump()?;
                        let member = self.intern(self.text(ahead));
                        return Ok(self.expr(Expr::Var {
                            module: Some(name),
                            name: member,
                        }));
                    }
                }
                self.bump()?;
                let name = self.intern(self.text(ahead));
                Ok(self.expr(Expr::Field { record: base, name }))
            }
            _ => Err(self.unexpected(&ahead, "expected a field name, tag, or '{' after '.'")),
        }
    }

    /// A `:` where a closing delimiter was due: the writer tried to annotate an
    /// element in place. Ascription lives in a group, so say where to put it.
    /// Returns `None` when the next token is something else, leaving the ordinary
    /// "expected X" error to speak for itself.
    fn stray_annotation(&mut self, what: &str, hint: &str) -> Result<Option<Diagnostic>> {
        if !matches!(self.peek_kind()?, Kind::Colon) {
            return Ok(None);
        }
        let t = self.peek()?;
        Ok(Some(self.unexpected(&t, what).with_help(hint.to_string())))
    }

    /// Require that `base` is a bare, uppercase-initial type name and return it.
    /// `at` is the token after the `.` (the `{` or the tag); the error spans the
    /// base, whose span `parse_atom` always stamps, through that token.
    fn expect_bare_type_name(&self, base: Aol<Expr>, at: &Token, what: &str) -> Result<StrId> {
        if let Some(name) = self.bare_var_name(base) {
            if is_upper(self.ast.text(name)) {
                return Ok(name);
            }
        }
        let span = match self.ast.expr_span(base) {
            Some(s) => Span::new(s.start, at.span.end),
            None => at.span,
        };
        let Some(head) = self.spine_head_name(base) else {
            return Err(Diagnostic::error(
                Code::UnexpectedToken,
                span,
                at.line,
                format!("{what} must be qualified with an uppercase type name"),
            )
            .with_help("write `Type.{ ... }`"));
        };
        let head = self.ast.text(head);
        if !is_upper(head) {
            return Err(Diagnostic::error(
                Code::UnexpectedToken,
                span,
                at.line,
                format!(
                    "{what} must be qualified with an uppercase type name, and `{head}` names \
                     a value, not a type"
                ),
            ));
        }
        // `(List @Int32).Cons`: a type applied to its arguments, which is how a
        // reader asks for a constructor at a fixed instantiation. Ares infers
        // those arguments instead, so an ascription is where the types go.
        Err(Diagnostic::error(
            Code::UnexpectedToken,
            span,
            at.line,
            format!("{what} is qualified by a bare type name, not by a type applied to arguments"),
        )
        .with_note("the type arguments are inferred")
        .with_help(format!(
            "drop them here and ascribe the whole expression instead, as in `(e : {head} @Int32)`"
        )))
    }

    /// The head of an application spine, when it is a bare unqualified name:
    /// `List` for `List @Int32 @Str`, and for a bare `List` itself.
    fn spine_head_name(&self, base: Aol<Expr>) -> Option<StrId> {
        let mut head = base;
        while let Expr::App(f, _) = self.ast.exprs.lookup(head) {
            head = *f;
        }
        self.bare_var_name(head)
    }

    /// Split a `.0` / `.0.1` index token into nested field accesses.
    fn tuple_indices(&mut self, base: Aol<Expr>, tok: Token) -> Aol<Expr> {
        let mut record = base;
        for part in self.text(tok).split('.') {
            debug_assert!(
                !part.is_empty() && part.bytes().all(|b| b.is_ascii_digit()),
                "a tuple index token is dot-separated digit runs"
            );
            let name = self.intern(part);
            record = self.expr(Expr::Field { record, name });
        }
        record
    }

    /// Whether the upcoming `(` opens an operator reference `(op)` rather than a
    /// group. The parens must hold exactly one operator token, so `(a + b)` and
    /// `(-1)` stay groups.
    fn at_operator_ref(&mut self) -> Result<bool> {
        Ok(matches!(self.peek_kind_at(1)?, Kind::Op)
            && matches!(self.peek_kind_at(2)?, Kind::RParen))
    }

    /// `(op)` in expression position: the operator as a first-class function,
    /// the same binding `$ (op) : ... = ...` defines. Application and context
    /// resolution then treat it like any other function reference.
    fn parse_operator_ref(&mut self) -> Result<Aol<Expr>> {
        self.bump()?; // '('
        let op_tok = self.bump()?;
        let lexeme = self.text(op_tok);
        self.bump()?; // ')'
        if table::ends_expr(lexeme) {
            return Err(Diagnostic::error(
                Code::UnexpectedToken,
                op_tok.span,
                op_tok.line,
                format!("`{lexeme}` is a grammatical delimiter, not a function"),
            ));
        }
        // A rewritten operator that names a global instead (`(<|>)` is `compose`):
        // the reference is that binding, so the function form carries a written,
        // effect-polymorphic type rather than an inferred (pure) eta-expansion.
        if let Some(global) = table::infix_global(lexeme) {
            let name = self.intern(global);
            return Ok(self.expr(Expr::Var { module: None, name }));
        }
        // Any other operator the parser or lowering rewrites has no global of its
        // own, so the reference eta-expands and goes back through that same rewrite.
        if table::desugared(lexeme) {
            return Ok(self.eta_operator(lexeme));
        }
        // A prefix-only operator names its global by role (`!` is `not`), since no
        // binary form of the lexeme exists.
        let name = match table::infix(lexeme) {
            Some(_) => self.intern(lexeme),
            None if lexeme == table::SPLICE => return Err(self.splice_not_a_function(&op_tok)),
            None => {
                let prefix = table::prefix(lexeme)
                    .ok_or_else(|| self.unexpected(&op_tok, "expected an operator"))?;
                self.intern(prefix)
            }
        };
        Ok(self.expr(Expr::Var { module: None, name }))
    }

    /// `\l r => l op r`, the function form of an operator whose infix use is
    /// desugared rather than lowered to a call. The binder names carry a `#`, a
    /// comment character, so they cannot collide with a source name.
    fn eta_operator(&mut self, lexeme: &str) -> Aol<Expr> {
        let l = self.intern("#l");
        let r = self.intern("#r");
        let lhs = self.expr(Expr::Var { module: None, name: l });
        let rhs = self.expr(Expr::Var { module: None, name: r });
        let body = self.binop_expr(lexeme, lhs, rhs);
        let lp = self.pat(Pattern::Var(l));
        let rp = self.pat(Pattern::Var(r));
        let params = self.ast.make_slice(vec![
            LamParam { pat: lp, sig: None },
            LamParam { pat: rp, sig: None },
        ]);
        self.expr(Expr::Lambda { params, body })
    }

    fn parse_group(&mut self) -> Result<Aol<Expr>> {
        self.bump()?; // '('
        let e = self.parse_expr(0)?;
        // A trailing `: T` ascribes the group's type, e.g. `([] : List Int)`. The
        // colon is otherwise free inside a group, so this is unambiguous.
        let e = if self.eat(|k| matches!(k, Kind::Colon))? {
            let ty = self.parse_type()?;
            self.expr(Expr::Ascribe { expr: e, ty })
        } else {
            e
        };
        expect!(self, Kind::RParen, "expected ')' to close the group");
        Ok(e)
    }

    /// `{}` unit or `{a, b, ...}` tuple.
    fn parse_brace_expr(&mut self) -> Result<Aol<Expr>> {
        let start = self.here()?;
        self.bump()?; // '{'
        if self.eat(|k| matches!(k, Kind::RBrace))? {
            return Ok(self.expr(Expr::Unit));
        }
        // An anonymous record literal starts with a `.field =` entry or a `..base`
        // extension; anything else (including a `.Tag` variant element) is a tuple.
        let is_record = matches!(self.peek_kind()?, Kind::Dot)
            && (matches!(self.peek_kind_at(1)?, Kind::Dot)
                || (matches!(self.peek_kind_at(1)?, Kind::Word)
                    && matches!(self.peek_kind_at(2)?, Kind::Eq)));
        if is_record {
            return self.parse_record_expr();
        }
        if self.group_len()? > 0 {
            return self.parse_record_type(start);
        }
        let mut elems = Vec::new();
        loop {
            elems.push(self.parse_expr(0)?);
            if !self.eat(|k| matches!(k, Kind::Comma))? || matches!(self.peek_kind()?, Kind::RBrace)
            {
                break;
            }
        }
        if self.at_op("|")? {
            let t = self.peek()?;
            return Err(self.unexpected(&t, "expected '}' to close the tuple").with_help(
                "`| base` updates a record, so the fields before it are named, as in \
                 `{ .x = 1 | base }`; a tuple has no update form"
                    .to_string(),
            ));
        }
        expect!(self, Kind::RBrace, "expected '}' to close the tuple");
        let elems = self.ast.make_slice(elems);
        Ok(self.expr(Expr::Tuple(elems)))
    }

    /// A record value body (the `{` is already consumed): `.field = e` entries,
    /// ending in either a `..base` extension (the listed fields stacked on top of
    /// `base`'s row, mirroring the `..rest` pattern) or a `| base` update.
    fn parse_record_expr(&mut self) -> Result<Aol<Expr>> {
        let mut fields = Vec::new();
        let mut extend = None;
        let mut update = None;
        loop {
            if matches!(self.peek_kind()?, Kind::Dot) && matches!(self.peek_kind_at(1)?, Kind::Dot) {
                self.bump()?;
                self.bump()?;
                extend = Some(self.parse_expr(0)?);
                break;
            }
            fields.push(self.parse_field_init()?);
            if self.at_op("|")? {
                self.bump()?;
                update = Some(self.parse_expr(0)?);
                break;
            }
            if !self.eat(|k| matches!(k, Kind::Comma))? || matches!(self.peek_kind()?, Kind::RBrace)
            {
                break;
            }
        }
        expect!(self, Kind::RBrace, "expected '}' to close the record");
        let fields = self.ast.make_slice(fields);
        Ok(self.expr(Expr::Record {
            fields,
            extend,
            update,
        }))
    }

    /// A leading-dot atom: bare struct literal `.{...}` or bare variant `.Tag`.
    fn parse_leading_dot(&mut self) -> Result<Aol<Expr>> {
        self.bump()?; // '.'
        if matches!(self.peek_kind()?, Kind::LBrace) {
            return self.parse_struct_lit(None);
        }
        let tag = expect!(
            self,
            Kind::Word,
            "expected '{' or a variant tag after a leading '.'"
        );
        if !is_upper(self.text(tag)) {
            return Err(self.unexpected(&tag, "a variant tag must start uppercase"));
        }
        let tag = self.intern(self.text(tag));
        self.parse_variant_lit(None, None, tag)
    }

    /// A struct literal body `{ .field = e, ..., | base }`. Assumes the next token
    /// is `{`. The optional trailing `| base` is a record update: the listed fields
    /// override, the rest come from `base` (an expression of the same struct type).
    /// A bare `{ | base }` clones `base`.
    fn parse_struct_lit(&mut self, ty: Option<StrId>) -> Result<Aol<Expr>> {
        expect!(
            self,
            Kind::LBrace,
            "expected '{' to open the struct literal"
        );
        let mut fields = Vec::new();
        let mut spread = None;
        while !matches!(self.peek_kind()?, Kind::RBrace) {
            if self.at_op("|")? {
                self.bump()?;
                spread = Some(self.parse_expr(0)?);
                break; // the update base is always the final entry
            }
            fields.push(self.parse_field_init()?);
            if self.at_op("|")? {
                self.bump()?;
                spread = Some(self.parse_expr(0)?);
                break;
            }
            if !self.eat(|k| matches!(k, Kind::Comma))? {
                break;
            }
        }
        expect!(
            self,
            Kind::RBrace,
            "expected '}' to close the struct literal"
        );
        let fields = self.ast.make_slice(fields);
        Ok(self.expr(Expr::StructLit { ty, fields, spread }))
    }

    /// A variant constructor with an optional `.{ payload }`.
    fn parse_variant_lit(
        &mut self,
        module: Option<StrId>,
        ty: Option<StrId>,
        tag: StrId,
    ) -> Result<Aol<Expr>> {
        let mut fields = Vec::new();
        if matches!(self.peek_kind()?, Kind::Dot) && matches!(self.peek_kind_at(1)?, Kind::LBrace) {
            self.bump()?; // '.'
            self.bump()?; // '{'
            while !matches!(self.peek_kind()?, Kind::RBrace) {
                fields.push(self.parse_field_init()?);
                if !self.eat(|k| matches!(k, Kind::Comma))? {
                    break;
                }
            }
            if let Some(d) = self.stray_annotation(
                "expected '}' to close the variant payload",
                "ascribe a payload field in a group, `.Cons.{ (1 : @Int32), rest }`, or the \
                 whole value, `(.Cons.{ .. } : List @Int32)`",
            )? {
                return Err(d);
            }
            expect!(
                self,
                Kind::RBrace,
                "expected '}' to close the variant payload"
            );
        }
        let fields = self.ast.make_slice(fields);
        Ok(self.expr(Expr::Variant {
            module,
            ty,
            tag,
            fields,
        }))
    }

    fn parse_field_init(&mut self) -> Result<FieldInit> {
        // A named field is `.field = e` (lowercase field name). A positional
        // value may itself be a leading-dot literal (`.Tag`, `.{ ... }`), which
        // starts with `.` too, so only a lowercase `.name` is a named field.
        let named = matches!(self.peek_kind()?, Kind::Dot)
            && matches!(self.peek_kind_at(1)?, Kind::Word)
            && {
                let t1 = self.peek_at(1)?;
                !is_upper(self.text(t1))
            };
        if named {
            self.bump()?; // '.'
            let name = self.bump_word()?;
            expect!(self, Kind::Eq, "expected '=' after the field name");
            let value = self.parse_expr(0)?;
            Ok(FieldInit::Named { name, value })
        } else {
            Ok(FieldInit::Positional(self.parse_expr(0)?))
        }
    }

    fn parse_list(&mut self) -> Result<Aol<Expr>> {
        self.bump()?; // '['
        if matches!(self.peek_kind()?, Kind::RBrack) {
            self.bump()?;
            let elems = self.ast.make_slice(Vec::new());
            return Ok(self.expr(Expr::List(elems)));
        }
        let first = self.parse_expr(0)?;
        // The inclusive range builder `[lo ... hi]`. A TYPE-DIRECTED literal
        // (`Expr::Range`): the checker resolves it to a sized tensor `@Tensor n T` or, by
        // default, a `List Int`. It is not desugared here so the target stays open.
        if matches!(self.peek_kind()?, Kind::Ellipsis) {
            self.bump()?; // '...'
            let hi = if matches!(self.peek_kind()?, Kind::RBrack) {
                None
            } else {
                Some(self.parse_expr(0)?)
            };
            expect!(self, Kind::RBrack, "expected ']' to close the range");
            return Ok(self.expr(Expr::Range { lo: first, hi }));
        }
        let mut elems = vec![first];
        if self.eat(|k| matches!(k, Kind::Comma))? {
            while !matches!(self.peek_kind()?, Kind::RBrack) {
                elems.push(self.parse_expr(0)?);
                if !self.eat(|k| matches!(k, Kind::Comma))? {
                    break;
                }
            }
        }
        if let Some(d) = self.stray_annotation(
            "expected ']' to close the list",
            "ascribe an element in a group, `[(1 : @Int32), 2, 3]`, or the whole literal and \
             its sequence type, `([1, 2, 3] : List @Int32)`",
        )? {
            return Err(d);
        }
        expect!(self, Kind::RBrack, "expected ']' to close the list");
        let elems = self.ast.make_slice(elems);
        Ok(self.expr(Expr::List(elems)))
    }

    /// An `@`-intrinsic in expression position: `@Array`, `@extern`.
    fn parse_at_term(&mut self) -> Result<Aol<Expr>> {
        let at = self.peek()?;
        match self.intrinsic_name(at) {
            // `x |> @absurd`, the empty match: a lambda over a match with no arms,
            // so exhaustiveness accepts it only when `x`'s type is uninhabited.
            "absurd" => {
                self.bump()?;
                let arms = self.ast.make_slice(Vec::new());
                Ok(self.match_lambda(arms, 1))
            }
            "ctx" if matches!(self.peek_kind_at(1)?, Kind::LBrace) && matches!(self.peek_kind_at(2)?, Kind::Dot) => {
                self.parse_ctx_arg()
            }
            "ctx" if matches!(self.peek_kind_at(1)?, Kind::LBrace) && matches!(self.peek_kind_at(2)?, Kind::RBrace) => {
                let t = self.peek_at(2)?;
                Err(self.unexpected(&t, "expected a `.field = value`: a `@ctx` argument supplies at least one field"))
            }
            "ctx" if matches!(self.peek_kind_at(1)?, Kind::LBrace) && self.group_len_at(2)? > 0 =>
            {
                Err(self.ctx_param_misplaced()?)
            }
            "ctx" => {
                let t = self.peek()?;
                Err(Self::ctx_reserved_at(&t).with_help(
                    "an explicit instance is passed by its `@ctx` field's name: `f @ctx {.d = value} ...`",
                ))
            }
            "Array" if matches!(self.peek_kind_at(1)?, Kind::Dot) => self.parse_array(),
            "extern" => self.parse_extern(),
            // Any other lowercase `@name` is a reference to a compiler intrinsic
            // (`@tensor_create`, `@tensor_index`, `@vec_get`, ...), usable as a value
            // function value. The `@` sigil marks it as a primitive, not a library fn.
            // A base type (`@Int32`) parses the same way, so a misplaced one reaches
            // the checker's diagnostics rather than a bare parse error.
            // Any other `@name` is a compiler intrinsic (`@vec_get`), a builtin
            // type or effect (`@Int32`, `@IO`), or a primitive of the dependent
            // core (`@Type`, `@refl`): types are expressions, so each parses as
            // a name, and the checker decides where it may stand.
            _ => {
                self.bump()?;
                let name = self.intern(self.text(at));
                Ok(self.expr(Expr::Var { module: None, name }))
            }
        }
    }

    /// `@ctx {.t = @Int, .d = rev_ord, ...}`: values for some of the callee's
    /// `@ctx` fields, by name, each the expression written. The checker
    /// elaborates it by its field's sort: a level, a type, a size, an effect,
    /// an instance or a proof.
    fn parse_ctx_arg(&mut self) -> Result<Aol<Expr>> {
        let start = self.here()?;
        self.bump()?; // '@ctx'
        self.bump()?; // '{'
        let mut inits = Vec::new();
        loop {
            expect!(self, Kind::Dot, "expected a `.field = value`");
            let name = self.expect_word("expected a field name after '.'")?;
            expect!(self, Kind::Eq, "expected '=' after the field name");
            let value = self.parse_expr(0)?;
            inits.push(FieldInit::Named { name, value });
            if !self.eat(|k| matches!(k, Kind::Comma))? || matches!(self.peek_kind()?, Kind::RBrace) {
                break;
            }
        }
        expect!(self, Kind::RBrace, "expected '}' to close the `@ctx` argument");
        let inits = self.ast.make_slice(inits);
        let node = self.expr(Expr::CtxArg(inits));
        Ok(self.stamp(start, node))
    }

    /// `@Array.{ n }` or `@Array.{ .field = n }`.
    fn parse_array(&mut self) -> Result<Aol<Expr>> {
        self.bump()?; // '@Array'
        expect!(self, Kind::Dot, "expected '.{' after '@Array'");
        expect!(self, Kind::LBrace, "expected '{' after '@Array.'");
        if matches!(self.peek_kind()?, Kind::Dot) {
            self.bump()?; // '.'
            expect!(self, Kind::Word, "expected a field name after '.'");
            expect!(self, Kind::Eq, "expected '=' after the field name");
        }
        let size = self.parse_expr(0)?;
        self.eat(|k| matches!(k, Kind::Comma))?;
        expect!(
            self,
            Kind::RBrace,
            "expected '}' to close the array literal"
        );
        Ok(self.expr(Expr::Array { size }))
    }

    /// `@extern "abi" "symbol" "lib"`, `@extern "ares"` for a runtime builtin, or
    /// `@extern "load"` for a load from C memory.
    fn parse_extern(&mut self) -> Result<Aol<Expr>> {
        self.bump()?; // '@extern'
        let abi = self.expect_string("expected an ABI string after '@extern'")?;
        if self.ast.bytes(abi) == BUILTIN_ABI.as_bytes() {
            return Ok(self.expr(Expr::Builtin));
        }
        if self.ast.bytes(abi) == LOAD_ABI.as_bytes() {
            let none = StrId::intern("");
            return Ok(self.expr(Expr::Extern { abi, symbol: none, lib: none }));
        }
        let symbol = self.expect_string("expected a symbol string")?;
        let lib = self.expect_string("expected a library string")?;
        Ok(self.expr(Expr::Extern { abi, symbol, lib }))
    }

    fn expect_string(&mut self, what: &str) -> Result<StrId> {
        let t = self.peek()?;
        if let Kind::Str = t.kind {
            self.bump()?;
            Ok(self.intern_str(t)?)
        } else {
            Err(self.unexpected(&t, what))
        }
    }

    // -- control forms ------------------------------------------------------

    fn parse_let(&mut self) -> Result<Aol<Expr>> {
        self.bump()?; // 'let'
        let pat = self.parse_pattern()?;
        // Any pattern may carry the annotation, as a lambda parameter does: the
        // type describes the whole binding, not one of its binders.
        let sig = if self.eat(|k| matches!(k, Kind::Colon))? {
            Some(self.parse_type()?)
        } else {
            None
        };
        expect!(self, Kind::Eq, "expected '=' in the 'let' binding");
        let value = self.parse_expr(0)?;
        expect!(self, Kind::In, "expected 'in' after the 'let' binding");
        let body = self.parse_expr(0)?;
        Ok(self.expr(Expr::Let { binding: Binding { pat, sig, value }, body }))
    }

    fn parse_if(&mut self) -> Result<Aol<Expr>> {
        self.bump()?; // 'if'
        let cond = self.parse_expr(0)?;
        expect!(self, Kind::FatArrow, "expected '=>' after the 'if' condition");
        let then = self.parse_expr(0)?;
        expect!(self, Kind::Else, "expected 'else' in the 'if' expression");
        let alt = self.parse_expr(0)?;
        Ok(self.expr(Expr::If { cond, then, alt }))
    }

    /// One `| p1 | p2 if guard => body` arm, shared by a multi-arm lambda and a
    /// handler's value arms. Each alternative lists one pattern per argument,
    /// `| p, q => e`, and becomes one tuple pattern when there are several.
    /// Returns the arm with its arity, which every alternative shares.
    /// See Note [Multi-argument arms].
    fn parse_arm(&mut self) -> Result<(Arm, usize)> {
        let mut patterns = Vec::new();
        let mut arity = None;
        while self.at_op("|")? {
            self.bump()?; // '|'
            let start = self.here()?;
            let mut columns = vec![self.parse_pattern()?];
            while self.eat(|k| matches!(k, Kind::Comma))? {
                columns.push(self.parse_pattern()?);
            }
            let span = Span::new(start, self.last_end);
            match arity {
                None => arity = Some(columns.len()),
                Some(n) if n != columns.len() => return Err(arity_mismatch("alternative", span, n, columns.len())),
                Some(_) => {}
            }
            patterns.push(match columns.as_slice() {
                [one] => *one,
                _ => {
                    let items = self.ast.make_slice(columns);
                    let tuple = self.pat(Pattern::Tuple(items));
                    self.ast.pat_spans.insert(tuple, span);
                    tuple
                }
            });
        }
        let guard = if matches!(self.peek_kind()?, Kind::If) {
            self.bump()?;
            Some(self.parse_expr(0)?)
        } else {
            None
        };
        // No `: T` here, unlike `let` and a lambda parameter: the scrutinee's
        // type already fixes every arm's pattern, so there is nothing to pin.
        let t = self.peek()?;
        if matches!(t.kind, Kind::Word) {
            return Err(self
                .unexpected(&t, "expected '=>' after the match pattern")
                .with_help("separate the patterns of several arguments with `,`, as in `| a, b => ...`"));
        }
        expect!(self, Kind::FatArrow, "expected '=>' after the match pattern");
        let body = self.parse_expr(0)?;
        let patterns = self.ast.make_slice(patterns);
        let arm = Arm {
            patterns,
            guard,
            body,
        };
        Ok((arm, arity.expect("an arm starts with '|'")))
    }

    /// Whether the next tokens open a handler operation clause, `| op x` or
    /// `| Eff.op x`, rather than a value arm. A pattern never juxtaposes two
    /// names, and a qualified pattern's second segment is an uppercase tag, so
    /// the two shapes cannot collide.
    fn at_op_clause(&mut self) -> Result<bool> {
        if !self.at_op("|")? || !matches!(self.peek_kind_at(1)?, Kind::Word) {
            return Ok(false);
        }
        let first = self.peek_at(1)?;
        if !is_upper(self.text(first)) {
            return Ok(matches!(self.peek_kind_at(2)?, Kind::Word));
        }
        if !matches!(self.peek_kind_at(2)?, Kind::Dot) || !matches!(self.peek_kind_at(3)?, Kind::Word) {
            return Ok(false);
        }
        let op = self.peek_at(3)?;
        Ok(!is_upper(self.text(op)))
    }

    /// `\p1 p2 => body`. Parameters are juxtaposed pattern atoms. An annotated
    /// parameter is always parenthesized, `\(i: @Int) (j: @Float32) => ...`,
    /// even a lone one, so its type ends at `)`: a lowercase name in a type is
    /// a type variable, and a bare annotation would swallow the next parameter
    /// as its argument.
    fn parse_lambda(&mut self) -> Result<Aol<Expr>> {
        self.bump()?; // '\'
        if self.at_op("|")? {
            return self.parse_arms_lambda();
        }
        let mut params = vec![self.lambda_param(true)?];
        while !self.eat(|k| matches!(k, Kind::FatArrow))? {
            params.push(self.lambda_param(false)?);
        }
        let body = self.parse_expr(0)?;
        let params = self.ast.make_slice(params);
        Ok(self.expr(Expr::Lambda { params, body }))
    }

    /// One juxtaposed lambda parameter. A splice would take the parameters after
    /// it as its operand's arguments (`\!f a b =>`), and `\.Tag .{ x } =>` would
    /// read either as one parameter with its payload or as two, so a splice is
    /// parenthesized and only the first parameter may start with `.`.
    fn lambda_param(&mut self, first: bool) -> Result<LamParam> {
        let t = self.peek()?;
        if self.at_splice()? {
            return Err(Diagnostic::error(
                Code::UnexpectedToken,
                t.span,
                t.line,
                "a splice as a lambda parameter is parenthesized",
            )
            .with_help("write `(!f a)`"));
        }
        if !first && matches!(t.kind, Kind::Dot) {
            return Err(Diagnostic::error(
                Code::UnexpectedToken,
                t.span,
                t.line,
                "only a lambda's first parameter may start with `.`",
            )
            .with_help("parenthesize it: `(.Tag)`"));
        }
        self.parse_lambda_param()
    }

    // Note [Multi-argument arms]
    //
    // `\ | p1, ..., pn => e` is a lambda of n curried arguments whose arms match
    // all of them at once, like Lean's `fun | a, b => e`. The comma separates
    // arguments and never builds a tuple: `| { a, b } => e` is one argument, a
    // tuple. Every alternative of every arm lists the same number of patterns,
    // and that number is the arity.
    //
    // The parser lowers it to `\#arg0 ... #argn => <match { #arg0, ... } with
    // the arms>`, each pattern list a tuple pattern, so the checker,
    // exhaustiveness and both backends see an ordinary match. `arity` on the
    // match records the shape: coverage shows a missing case as `0, []` rather
    // than `{ 0, [] }`, and match compilation reads the parameters directly
    // instead of building the tuple. See Note [Tuple scrutinees].
    //
    // A dependent elaborator will match the parameters as a telescope instead,
    // since a later argument's type may depend on an earlier one.

    /// `\ | p => a | q => b`: a lambda matching its arguments against the arms,
    /// top to bottom, one argument per comma-separated pattern. The arms end at
    /// a handler's next operation clause. See Note [Multi-argument arms].
    fn parse_arms_lambda(&mut self) -> Result<Aol<Expr>> {
        // The first arm is never a handler's operation clause: a lambda needs
        // an arm, so `\ | a b => e` is a malformed arm, not a clause.
        let (first, arity) = self.parse_arm()?;
        let mut arms = vec![first];
        while self.at_op("|")? && !self.at_op_clause()? {
            let start = self.here()?;
            let (arm, n) = self.parse_arm()?;
            if n != arity {
                return Err(arity_mismatch("arm", Span::new(start, self.last_end), arity, n));
            }
            arms.push(arm);
        }
        let arms = self.ast.make_slice(arms);
        Ok(self.match_lambda(arms, arity))
    }

    /// `\#arg0 ... => <match { #arg0, ... } with arms>`, the lambda a multi-arm
    /// lambda and `@absurd` (no arms, arity 1) both are. A lone argument is
    /// matched as itself, not as a one-element tuple.
    fn match_lambda(&mut self, arms: Slice<Arm>, arity: usize) -> Aol<Expr> {
        let names: Vec<StrId> = match arity {
            1 => vec![self.intern("#arg")],
            _ => (0..arity).map(|i| self.intern(&format!("#arg{i}"))).collect(),
        };
        let vars: Vec<Aol<Expr>> = names.iter().map(|&name| self.expr(Expr::Var { module: None, name })).collect();
        let scrut = match vars.as_slice() {
            [one] => *one,
            _ => {
                let items = self.ast.make_slice(vars);
                self.expr(Expr::Tuple(items))
            }
        };
        let arity = u32::try_from(arity).expect("an arm's pattern count fits u32");
        let body = self.expr(Expr::Match { scrut, arms, arity });
        let params: Vec<LamParam> = names
            .into_iter()
            .map(|name| LamParam {
                pat: self.pat(Pattern::Var(name)),
                sig: None,
            })
            .collect();
        let params = self.ast.make_slice(params);
        self.expr(Expr::Lambda { params, body })
    }

    /// One lambda parameter: a pattern atom, or `(pat)` / `(pat: T)`.
    fn parse_lambda_param(&mut self) -> Result<LamParam> {
        if !self.eat(|k| matches!(k, Kind::LParen))? {
            let pat = self.parse_pattern_atom()?;
            return Ok(LamParam { pat, sig: None });
        }
        let pat = self.parse_pattern()?;
        let sig = if self.eat(|k| matches!(k, Kind::Colon))? {
            Some(self.parse_type()?)
        } else {
            None
        };
        expect!(self, Kind::RParen, "expected ')' after the lambda parameter");
        Ok(LamParam { pat, sig })
    }

    fn parse_handle(&mut self) -> Result<Aol<Expr>> {
        self.bump()?; // 'do'
        let body = self.parse_expr(0)?;
        if !matches!(self.peek_kind()?, Kind::Is) {
            return Ok(self.expr(Expr::Handle {
                body,
                handler: None,
            }));
        }
        self.bump()?; // 'is'
        let continuation = self.expect_word("expected a continuation name after 'is'")?;
        let start = self.here()?;
        let mut clauses = Vec::new();
        let mut value_arms = Vec::new();
        while self.at_op("|")? {
            if !self.at_op_clause()? {
                let start = self.here()?;
                let (arm, arity) = self.parse_arm()?;
                if arity != 1 {
                    return Err(Diagnostic::error(
                        Code::UnexpectedToken,
                        Span::new(start, self.last_end),
                        0,
                        format!("a handler's value arm matches one value, but this arm has {arity} patterns"),
                    )
                    .with_help("match the value's parts with one pattern, as in `| { a, b } => ...`"));
                }
                value_arms.push(arm);
                continue;
            }
            self.bump()?; // '|'
            let first = self.expect_word("expected an operation name in the handler clause")?;
            let (effect, op) = if matches!(self.peek_kind()?, Kind::Dot) {
                self.bump()?;
                let op = self.expect_word("expected an operation after '.'")?;
                (Some(first), op)
            } else {
                (None, first)
            };
            let arg = self.expect_word("expected the operation's argument binder")?;
            expect!(self, Kind::FatArrow, "expected '=>' in the handler clause");
            let body = self.parse_expr(0)?;
            clauses.push(Clause {
                effect,
                op,
                arg,
                body,
            });
        }
        let value = self.value_clause(start, value_arms);
        let handler = Box::new(Handler {
            continuation,
            clauses: self.ast.make_slice(clauses),
            value,
        });
        Ok(self.expr(Expr::Handle {
            body,
            handler: Some(handler),
        }))
    }

    /// Fold a handler's value arms into its return clause. A lone unguarded
    /// binder or `_` binds the value directly; anything else matches on a fresh
    /// binder, exactly as a multi-arm lambda would.
    fn value_clause(&mut self, start: usize, arms: Vec<Arm>) -> Option<(StrId, Aol<Expr>)> {
        if let [arm] = arms.as_slice() {
            let pats = self.ast.slice(arm.patterns);
            if arm.guard.is_none() && pats.len() == 1 {
                match self.ast.pats.lookup(pats[0]) {
                    Pattern::Var(name) => return Some((*name, arm.body)),
                    Pattern::Wild => return Some((self.intern("_"), arm.body)),
                    _ => {}
                }
            }
        }
        if arms.is_empty() {
            return None;
        }
        let name = self.intern("%ret");
        let scrut = self.expr(Expr::Var { module: None, name });
        let arms = self.ast.make_slice(arms);
        let node = self.expr(Expr::Match { scrut, arms, arity: 1 });
        Some((name, self.stamp(start, node)))
    }

    // -- patterns -----------------------------------------------------------

    fn parse_pattern(&mut self) -> Result<Aol<Pattern>> {
        let start = self.here()?;
        let node = self.parse_pattern_unstamped()?;
        Ok(self.stamp_pat(start, node))
    }

    fn parse_pattern_unstamped(&mut self) -> Result<Aol<Pattern>> {
        let atom = self.parse_pattern_atom()?;
        if self.at_op("::")? || self.at_op("++")? {
            let op = self.peek()?;
            let cons = self.at_op("::")?;
            self.bump()?;
            let right = self.parse_pattern()?; // right-associative
            let left = if cons {
                let one = self.ast.make_slice([atom]);
                let piece = self.pat(Pattern::List(one));
                if let Some(span) = self.ast.pat_span(atom) {
                    self.ast.pat_spans.insert(piece, span);
                }
                piece
            } else {
                atom
            };
            return self.concat_pattern(left, right, &op);
        }
        // `lo ... hi`: an inclusive numeric range, or `lo ...`: an open range (no
        // upper bound). Both bounds are numeric literals.
        if matches!(self.peek_kind()?, Kind::Ellipsis) {
            if !matches!(self.ast.pats.lookup(atom), Pattern::Int(_) | Pattern::Real(_)) {
                let t = self.peek()?;
                return Err(self.unexpected(&t, "a range '...' needs a numeric literal on its left"));
            }
            self.bump()?; // '...'
            let hi = if matches!(self.peek_kind()?, Kind::Int(_) | Kind::Real(_))
                || self.at_negative_literal()?
            {
                Some(self.parse_pattern_atom()?)
            } else {
                None
            };
            return Ok(self.pat(Pattern::Range { lo: atom, hi }));
        }
        Ok(atom)
    }

    /// A pattern as a `++` chain: its fixed pieces before the variable-length
    /// part, that part, and the fixed pieces after it.
    fn pattern_chain(&self, p: Aol<Pattern>) -> (Vec<Aol<Pattern>>, Option<Aol<Pattern>>, Vec<Aol<Pattern>>) {
        match self.ast.pats.lookup(p) {
            Pattern::Str(_) | Pattern::List(_) => (vec![p], None, Vec::new()),
            Pattern::Concat { pre, mid, suf } => {
                (self.ast.slice(*pre).to_vec(), *mid, self.ast.slice(*suf).to_vec())
            }
            _ => (Vec::new(), Some(p), Vec::new()),
        }
    }

    /// `left ++ right` as one chain. A pattern can only split a sequence at
    /// points fixed by the pieces' lengths, so at most one part may be
    /// variable-length.
    fn concat_pattern(&mut self, left: Aol<Pattern>, right: Aol<Pattern>, op: &Token) -> Result<Aol<Pattern>> {
        let (lp, lm, ls) = self.pattern_chain(left);
        let (rp, rm, rs) = self.pattern_chain(right);
        let (pre, mid, suf) = match (lm, rm) {
            (Some(a), Some(b)) => {
                let mut d = Diagnostic::error(
                    Code::UnexpectedToken,
                    op.span,
                    op.line,
                    "a `++` pattern can have only one part of unknown length",
                );
                for p in [a, b] {
                    if let Some(span) = self.ast.pat_span(p) {
                        d = d.with_label(span, "this matches any length");
                    }
                }
                return Err(d.with_help(
                    "there is more than one way to split the sequence between them; keep one \
                     variable part and match the rest in the arm body or a guard"
                        .to_string(),
                ));
            }
            (Some(m), None) => (lp, Some(m), [ls, rp, rs].concat()),
            (None, m) => ([lp, ls, rp].concat(), m, rs),
        };
        let pre = self.merge_pieces(pre);
        let suf = self.merge_pieces(suf);
        if mid.is_none() && pre.len() == 1 {
            return Ok(pre[0]);
        }
        let pre = self.ast.make_slice(pre);
        let suf = self.ast.make_slice(suf);
        Ok(self.pat(Pattern::Concat { pre, mid, suf }))
    }

    /// Merge adjacent pieces of one kind: `"a" ++ "b"` is `"ab"`, `[1] ++ [2]`
    /// is `[1, 2]`.
    fn merge_pieces(&mut self, pieces: Vec<Aol<Pattern>>) -> Vec<Aol<Pattern>> {
        let mut out: Vec<Aol<Pattern>> = Vec::new();
        for p in pieces {
            let merged = match (out.last().map(|q| self.ast.pats.lookup(*q).clone()), self.ast.pats.lookup(p).clone()) {
                (Some(Pattern::Str(a)), Pattern::Str(b)) => {
                    let bytes = [self.ast.bytes(a), self.ast.bytes(b)].concat();
                    let s = StrId::intern_bytes(&bytes);
                    Some(self.pat(Pattern::Str(s)))
                }
                (Some(Pattern::List(a)), Pattern::List(b)) => {
                    let elems = [self.ast.slice(a), self.ast.slice(b)].concat();
                    let elems = self.ast.make_slice(elems);
                    Some(self.pat(Pattern::List(elems)))
                }
                _ => None,
            };
            match merged {
                Some(m) => {
                    let first = self.ast.pat_span(*out.last().expect("merged with a piece"));
                    if let (Some(a), Some(b)) = (first, self.ast.pat_span(p)) {
                        self.ast.pat_spans.insert(m, Span::new(a.start, b.end));
                    }
                    *out.last_mut().expect("merged with a piece") = m;
                }
                None => out.push(p),
            }
        }
        out
    }

    fn parse_pattern_atom(&mut self) -> Result<Aol<Pattern>> {
        let start = self.here()?;
        let node = self.parse_pattern_atom_unstamped()?;
        Ok(self.stamp_pat(start, node))
    }

    fn parse_pattern_atom_unstamped(&mut self) -> Result<Aol<Pattern>> {
        let t = self.peek()?;
        if self.at_negative_literal()? {
            self.bump()?; // '-'
            let n = self.peek()?;
            self.bump()?;
            return Ok(match n.kind {
                Kind::Int(v) => self.pat(Pattern::Int(v.wrapping_neg())),
                Kind::Real(v) => self.pat(Pattern::Real(-v)),
                _ => unreachable!("at_negative_literal saw a number"),
            });
        }
        match t.kind {
            Kind::Int(v) => {
                self.bump()?;
                Ok(self.pat(Pattern::Int(v)))
            }
            Kind::Real(v) => {
                self.bump()?;
                Ok(self.pat(Pattern::Real(v)))
            }
            // An imaginary literal builds its value through a hook, and a pattern
            // holds no application, so it has no pattern form.
            Kind::Imaginary(_) => Err(Diagnostic::error(
                Code::UnexpectedToken,
                t.span,
                t.line,
                "an imaginary literal is not a pattern; match the fields \
                 (`Cpx.{re, im}`) or compare with `==` in a guard"
                    .to_string(),
            )),
            Kind::Str => {
                self.bump()?;
                let s = self.intern_str(t)?;
                Ok(self.pat(Pattern::Str(s)))
            }
            Kind::Word if self.text(t) == "_" => {
                self.bump()?;
                Ok(self.pat(Pattern::Wild))
            }
            Kind::Word if is_upper(self.text(t)) => self.parse_qualified_pattern(),
            Kind::Word => {
                self.bump()?;
                let name = self.intern(self.text(t));
                Ok(self.pat(Pattern::Var(name)))
            }
            // `!X`: the operand binds tighter than `::` and `++`, so it ends
            // before them and before the `=>`, `|` or `,` that follow a pattern.
            Kind::Op if self.text(t) == table::SPLICE => {
                let e = self.parse_splice_operand()?;
                Ok(self.pat(Pattern::MetaE(e)))
            }
            Kind::At => {
                self.bump()?;
                let other = self.intrinsic_name(t);
                Err(self.unexpected(&t, &format!("'@{other}' is not a pattern")))
            }
            Kind::LBrack => self.parse_list_pattern(),
            Kind::LBrace => self.parse_tuple_pattern(),
            Kind::Dot => {
                self.bump()?; // '.'
                let tag = expect!(self, Kind::Word, "expected a variant tag after '.'");
                if !is_upper(self.text(tag)) {
                    return Err(self.unexpected(&tag, "a variant tag must start uppercase"));
                }
                let tag = self.intern(self.text(tag));
                let fields = self.parse_pattern_payload()?;
                Ok(self.pat(Pattern::Variant {
                    module: None,
                    ty: None,
                    tag,
                    fields,
                }))
            }
            _ => Err(self.unexpected(&t, "expected a pattern")),
        }
    }

    /// An uppercase-led pattern: `Type.{ ... }` struct, `Type.Tag`, or
    /// `Module.Type.Tag`, each with an optional `.{ ... }` payload.
    fn parse_qualified_pattern(&mut self) -> Result<Aol<Pattern>> {
        let head = self.bump_word()?;
        expect!(
            self,
            Kind::Dot,
            "expected '.' after the type name in a pattern"
        );
        if matches!(self.peek_kind()?, Kind::LBrace) {
            let fields = self.parse_field_pats()?;
            return Ok(self.pat(Pattern::Struct { ty: head, fields }));
        }
        let second = expect!(self, Kind::Word, "expected a variant tag after '.'");
        let second_name = self.intern(self.text(second));
        // `Module.Type.Tag`
        let qualifies = matches!(self.peek_kind()?, Kind::Dot)
            && matches!(self.peek_kind_at(1)?, Kind::Word)
            && {
                let t1 = self.peek_at(1)?;
                is_upper(self.text(t1))
            };
        if qualifies {
            self.bump()?; // '.'
            let tag = self.bump_word()?;
            let fields = self.parse_pattern_payload()?;
            Ok(self.pat(Pattern::Variant {
                module: Some(head),
                ty: Some(second_name),
                tag,
                fields,
            }))
        } else {
            let fields = self.parse_pattern_payload()?;
            Ok(self.pat(Pattern::Variant {
                module: None,
                ty: Some(head),
                tag: second_name,
                fields,
            }))
        }
    }

    fn parse_pattern_payload(&mut self) -> Result<Slice<FieldPat>> {
        if matches!(self.peek_kind()?, Kind::Dot) && matches!(self.peek_kind_at(1)?, Kind::LBrace) {
            self.bump()?; // '.'
            self.parse_field_pats()
        } else {
            Ok(self.ast.make_slice(Vec::new()))
        }
    }

    /// A `{ field-patterns }` body. Assumes the next token is `{`.
    fn parse_field_pats(&mut self) -> Result<Slice<FieldPat>> {
        expect!(
            self,
            Kind::LBrace,
            "expected '{' to open the field patterns"
        );
        let mut fields = Vec::new();
        while !matches!(self.peek_kind()?, Kind::RBrace) {
            if matches!(self.peek_kind()?, Kind::Dot) {
                self.bump()?; // '.'
                let name = self.expect_word("expected a field name after '.'")?;
                if self.eat(|k| matches!(k, Kind::Eq))? {
                    let pat = self.parse_pattern()?;
                    fields.push(FieldPat::Named { name, pat });
                } else {
                    fields.push(FieldPat::Shorthand(name));
                }
            } else {
                fields.push(FieldPat::Positional(self.parse_pattern()?));
            }
            if !self.eat(|k| matches!(k, Kind::Comma))? {
                break;
            }
        }
        expect!(
            self,
            Kind::RBrace,
            "expected '}' to close the field patterns"
        );
        Ok(self.ast.make_slice(fields))
    }

    fn parse_list_pattern(&mut self) -> Result<Aol<Pattern>> {
        self.bump()?; // '['
        let mut elems = Vec::new();
        while !matches!(self.peek_kind()?, Kind::RBrack) {
            elems.push(self.parse_pattern()?);
            if !self.eat(|k| matches!(k, Kind::Comma))? {
                break;
            }
        }
        expect!(self, Kind::RBrack, "expected ']' to close the list pattern");
        let elems = self.ast.make_slice(elems);
        Ok(self.pat(Pattern::List(elems)))
    }

    fn parse_rest_pattern(&mut self, what: &str) -> Result<Aol<Pattern>> {
        if matches!(self.peek_kind()?, Kind::RBrace | Kind::RBrack | Kind::Comma) {
            let t = self.peek()?;
            return Err(self.unexpected(&t, "expected a pattern after '..'").with_help(format!(
                "write `.._` to ignore the remaining {what}, or `..rest` to bind them"
            )));
        }
        self.parse_pattern()
    }

    fn parse_tuple_pattern(&mut self) -> Result<Aol<Pattern>> {
        self.bump()?; // '{'
        // A record pattern starts with a `.field` entry (or `..rest`); anything
        // else is a positional tuple pattern.
        if matches!(self.peek_kind()?, Kind::Dot) {
            return self.parse_record_pattern();
        }
        let mut elems = Vec::new();
        loop {
            elems.push(self.parse_pattern()?);
            if !self.eat(|k| matches!(k, Kind::Comma))? || matches!(self.peek_kind()?, Kind::RBrace)
            {
                break;
            }
        }
        if let Some(d) = self.stray_annotation(
            "expected '}' to close the tuple pattern",
            "a pattern carries no types, so annotate the binding instead, as in \
             `let {a, b} : {@Int32, @Int32} = ...` or `\\({a, b}: {@Int32, @Int32}) => ...`",
        )? {
            return Err(d);
        }
        expect!(
            self,
            Kind::RBrace,
            "expected '}' to close the tuple pattern"
        );
        let elems = self.ast.make_slice(elems);
        Ok(self.pat(Pattern::Tuple(elems)))
    }

    /// A record pattern body (the `{` is consumed): `.field = pat` / `.field`
    /// entries, and an optional trailing `..rest` (`..name` binds, `.._` discards).
    fn parse_record_pattern(&mut self) -> Result<Aol<Pattern>> {
        let mut fields = Vec::new();
        let mut rest = None;
        loop {
            // `..rest`: two dots then a binder.
            if matches!(self.peek_kind()?, Kind::Dot) && matches!(self.peek_kind_at(1)?, Kind::Dot) {
                self.bump()?;
                self.bump()?;
                rest = Some(self.parse_rest_pattern("fields")?);
                break;
            }
            expect!(self, Kind::Dot, "expected '.field' in a record pattern");
            let name = self.expect_word("expected a field name after '.'")?;
            if self.eat(|k| matches!(k, Kind::Eq))? {
                let pat = self.parse_pattern()?;
                fields.push(FieldPat::Named { name, pat });
            } else {
                fields.push(FieldPat::Shorthand(name));
            }
            if !self.eat(|k| matches!(k, Kind::Comma))? || matches!(self.peek_kind()?, Kind::RBrace)
            {
                break;
            }
        }
        expect!(self, Kind::RBrace, "expected '}' to close the record pattern");
        let fields = self.ast.make_slice(fields);
        Ok(self.pat(Pattern::Record { fields, rest }))
    }
}

// -- free helpers ------------------------------------------------------------

fn is_upper(name: &str) -> bool {
    name.as_bytes()
        .first()
        .is_some_and(|b| b.is_ascii_uppercase())
}

/// A short human description of a token for diagnostics. `text` is the token's
/// source lexeme (`source[t.span]`), resolved by the caller.
fn describe(t: &Token, text: &str) -> String {
    match t.kind {
        Kind::Eof => "end of input".to_string(),
        _ => format!("'{text}'"),
    }
}

/// An arm, or an alternative of one (`what`), whose pattern count differs from
/// the ones before it. See Note [Multi-argument arms].
fn arity_mismatch(what: &str, span: Span, expected: usize, found: usize) -> Diagnostic {
    let patterns = |n: usize| if n == 1 { "1 pattern".to_string() } else { format!("{n} patterns") };
    utilities::diag!(
        Code::UnexpectedToken, span, 0,
        "this {what} has {}, but the {what}s before it have {}", patterns(found), patterns(expected);
        note: "a multi-arm lambda takes one argument per comma-separated pattern, the same in every arm";
        help: "to match a tuple as one argument, write `{{ a, b }}`"
    )
}
