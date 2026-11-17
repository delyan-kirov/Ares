//! The kernel's input: an Ares module, parsed by the frontend's parser and
//! lowered to named, unresolved [`Raw`] terms.
//!
//! A script is an ordinary module. Types are expressions (#406), so kernel
//! tests read like the programs the frontend will one day elaborate:
//!
//! ```text
//! $ @mod ID
//! $ id : @ctx {u: @l} -> (t: @Type u) -> t -> t = \x => x
//! $ two : @Type 1 -> @Type 1 = id @ctx {.u = 2} (@Type 1 -> @Type 1) (\a => a)
//! ```
//!
//! A signature's leading named parameters are bound by the signature, as in
//! every Ares definition (#437): `id`'s body binds only `x`. Every other
//! argument is explicit except levels, which a reference to a
//! level-polymorphic global supplies with `@ctx {.u = l}`. The checker infers
//! left-out levels and an argument written `_` from the types around the
//! application (see `check::spine`).
//!
//! A global whose body is `@axiom` is an axiom. An inductive type is a union:
//! `$ Nat : @union = Zero: {}, Succ: Nat` in `@Type 1`, or with its parameters,
//! indices and universe stated, `$ Vec : (a: @Type 1) -> Nat -> @Type 1 =
//! @union Nil: {} -> Vec a Nat.Zero, Cons: {m: Nat, h: a, t: Vec a m} -> Vec a
//! Nat.Succ.{ m }`. A constructor is the global `D.Tag`, written `D.Tag.{
//! fields }` or `.Tag.{ fields }` with its parameters inferred. Primitive
//! forms are `@name` applied to a fixed number of arguments, read from the
//! [`PRIMITIVES`] table; `x |> @absurd` eliminates a proof of `@Bottom`.
//! `{a, b}` is a pair, or the type of pairs where a type is expected, and
//! `{x: A, y: B x}` a dependent pair type; `.0` and `.1` project.
//!
//! Input: source text. Output: [`Item`]s of named, unresolved [`Raw`] terms.
//!
//! Entry point: [`parse_script`].

use frontend::{Ast, Expr, FieldInit, Item as AstItem, LamParam, Pattern, Payload, Ty};
use utilities::{Aol, Code, Diagnostic, Result, Span};

use crate::term::Name;

// ## Raw terms

#[derive(Clone, Debug)]
pub struct Raw {
    pub kind: RawKind,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum RawKind {
    /// A name, with the level arguments of `name @ctx {.u = l}`.
    Var(Name, Vec<LevelArg>),
    Sort(RawLevel),
    Pi(Name, Box<Raw>, Box<Raw>),
    /// `\x => body` or `\(x: A) => body`, one binder per node.
    Lam(Name, Option<Box<Raw>>, Box<Raw>),
    App(Box<Raw>, Box<Raw>),
    Let(Name, Option<Box<Raw>>, Box<Raw>, Box<Raw>),
    /// `(e : T)`.
    Ann(Box<Raw>, Box<Raw>),
    Prim(Primitive, Vec<Raw>),
    /// `{x: A, y: B}`, a dependent pair type.
    Sigma(Name, Box<Raw>, Box<Raw>),
    /// `{a, b}`: a pair checked against a pair type, otherwise the type of
    /// pairs `{A, B}`.
    Tuple(Box<Raw>, Box<Raw>),
    /// `e.0`, `e.1`.
    Fst(Box<Raw>),
    Snd(Box<Raw>),
    /// `a ~ b`.
    Eq(Box<Raw>, Box<Raw>),
    /// `D.Tag.{ fields }` or `.Tag.{ fields }`: a constructor applied to its
    /// fields, positional or `.name = e`, its parameters inferred.
    Ctor {
        data: Option<Name>,
        tag: Name,
        fields: Vec<(Option<Name>, Raw)>,
    },
    /// `_`, an argument the checker infers.
    Hole,
}

#[derive(Clone, Debug)]
pub struct LevelArg {
    pub name: Name,
    pub level: RawLevel,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum RawLevel {
    Num(u32),
    Name(Name, Span),
    Plus(Box<RawLevel>, u32),
    Max(Box<RawLevel>, Box<RawLevel>),
    IMax(Box<RawLevel>, Box<RawLevel>),
}

/// A primitive form `@name arg ...`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Primitive {
    Top,
    Tt,
    Bottom,
    /// `x |> @absurd`, from a proof `x` of `@Bottom`, at the type expected.
    /// Its first argument is that type, a `_` the checker fills.
    Absurd,
    /// `@Eq A a b`, the equality with its type given.
    Eq,
    Refl,
    /// `@transp t B u t2 e`: from `u : B t` and `e : t ~ t2`, a proof of
    /// `B t2` (transport into a proposition).
    Transp,
    Cast,
    /// `@Quot A R rr rs rt`: `A` quotiented by `R`, with proofs that `R` is
    /// reflexive, symmetric and transitive.
    Quot,
    QIn,
    /// `@qelim P f resp q`.
    QElim,
}

/// Every primitive's spelling and argument count. `@absurd` is not here: in
/// Ares it is the empty match, `x |> @absurd`.
pub const PRIMITIVES: &[(&str, Primitive, usize)] = &[
    ("@Top", Primitive::Top, 0),
    ("@tt", Primitive::Tt, 0),
    ("@Bottom", Primitive::Bottom, 0),
    ("@Eq", Primitive::Eq, 3),
    ("@refl", Primitive::Refl, 1),
    ("@transp", Primitive::Transp, 5),
    ("@cast", Primitive::Cast, 4),
    ("@Quot", Primitive::Quot, 5),
    ("@qin", Primitive::QIn, 1),
    ("@qelim", Primitive::QElim, 4),
];

#[derive(Clone, Debug)]
pub struct Item {
    pub name: Name,
    pub span: Span,
    pub level_params: Vec<(Name, Span)>,
    pub ty: Raw,
    pub body: ItemBody,
}

#[derive(Clone, Debug)]
pub enum ItemBody {
    Definition(Raw),
    /// `= @axiom`.
    Axiom,
    /// `@union Tag: fields, ...`.
    Data(Vec<RawConstructor>),
}

#[derive(Clone, Debug)]
pub struct RawConstructor {
    /// The tag; the constructor is the global `D.Tag`.
    pub name: Name,
    pub span: Span,
    /// Each field's name (`_` when unnamed) and type.
    pub fields: Vec<(Name, Raw)>,
    /// The stated result type, `-> D params indices`, which an indexed
    /// family's constructors need.
    pub result: Option<Raw>,
}

/// The 1-based line of a byte offset.
pub fn line_of(src: &str, offset: usize) -> u32 {
    1 + src[..offset.min(src.len())].bytes().filter(|b| *b == b'\n').count() as u32
}

pub fn error(src: &str, code: Code, span: Span, msg: impl Into<String>) -> Diagnostic {
    Diagnostic::error(code, span, line_of(src, span.start), msg)
}

// ## Lowering

/// Parse an Ares module and lower its items to the kernel's input.
pub fn parse_script(src: &str) -> Result<Vec<Item>> {
    let parsed = frontend::parse(src)?;
    let lower = Lower { src, ast: &parsed.ast };
    let items = parsed.ast.slice(parsed.program.items);
    let spans = parsed.ast.slice(parsed.program.spans);
    items.iter().zip(spans).map(|(item, at)| lower.item(item, at.name.unwrap_or(at.full))).collect()
}

struct Lower<'a> {
    src: &'a str,
    ast: &'a Ast,
}

fn raw(kind: RawKind, span: Span) -> Raw {
    Raw { kind, span }
}

impl Lower<'_> {
    fn error(&self, span: Span, msg: impl Into<String>) -> Diagnostic {
        error(self.src, Code::Unsupported, span, msg)
    }

    fn ty_span(&self, ty: Aol<Ty>) -> Span {
        self.ast.ty_span(ty).unwrap_or(Span::at(0))
    }

    fn expr_span(&self, e: Aol<Expr>) -> Span {
        self.ast.expr_span(e).unwrap_or(Span::at(0))
    }

    fn item(&self, item: &AstItem, span: Span) -> Result<Item> {
        match item {
            AstItem::Def { name, sig: Some(sig), body, .. } => {
                if self.ast.use_params.get(*sig).is_some() {
                    return Err(self.error(span, "a kernel global takes no `@use` parameter"));
                }
                let body = match self.ast.expr(*body) {
                    Expr::Var { module: None, name } if name.as_str() == "@axiom" => ItemBody::Axiom,
                    _ => ItemBody::Definition(self.expr(*body)?),
                };
                Ok(Item {
                    name: name.as_str().into(),
                    span,
                    level_params: self.level_params(*sig),
                    ty: self.ty(*sig)?,
                    body,
                })
            }
            AstItem::Def { name, sig: None, .. } => {
                Err(self.error(span, format!("a kernel global needs its type: `$ {name} : T = ...`")))
            }
            AstItem::Union { name, sig, params, variants, splices } => {
                if !self.ast.slice(*splices).is_empty() {
                    return Err(self.error(span, "a kernel union is written out, without `&` entries"));
                }
                let (ty, level_params) = match sig {
                    Some(sig) => (self.ty(*sig)?, self.level_params(*sig)),
                    None => (self.classic_union_type(self.ast.slice(*params), span), Vec::new()),
                };
                let ctors = self.ast.slice(*variants).iter().map(|v| self.constructor(v, span)).collect::<Result<_>>()?;
                Ok(Item { name: name.as_str().into(), span, level_params, ty, body: ItemBody::Data(ctors) })
            }
            _ => Err(self.error(
                span,
                "a kernel script holds definitions (`$ x : T = e`, `= @axiom`) and unions, nothing else",
            )),
        }
    }

    fn level_params(&self, sig: Aol<Ty>) -> Vec<(Name, Span)> {
        let Some(levels) = self.ast.level_params.get(sig) else { return Vec::new() };
        self.ast.slice(*levels).iter().map(|l| (l.name.as_str().into(), l.span)).collect()
    }

    /// `$ D : @union a b = ...`: each parameter in `@Type 1`, and so the type.
    fn classic_union_type(&self, params: &[utilities::StrId], span: Span) -> Raw {
        let ty1 = || raw(RawKind::Sort(RawLevel::Num(1)), span);
        params.iter().rev().fold(ty1(), |cod, p| raw(RawKind::Pi(p.as_str().into(), Box::new(ty1()), Box::new(cod)), span))
    }

    fn constructor(&self, v: &frontend::VariantDecl, item_span: Span) -> Result<RawConstructor> {
        let mut fields = Vec::new();
        match &v.payload {
            Payload::None => {}
            Payload::Bare(ty) => fields.push(("_".into(), self.ty(*ty)?)),
            Payload::Fields(fs) => {
                for f in self.ast.slice(*fs) {
                    let name: Name = f.name.map_or("_".into(), |n| n.as_str().into());
                    fields.push((name, self.ty(f.ty)?));
                }
            }
        }
        let span = fields.first().map_or(item_span, |(_, r): &(Name, Raw)| r.span);
        let result = v.result.map(|r| self.ty(r)).transpose()?;
        Ok(RawConstructor { name: v.tag.as_str().into(), span, fields, result })
    }

    // ### Types

    fn ty(&self, ty: Aol<Ty>) -> Result<Raw> {
        let span = self.ty_span(ty);
        let kind = match self.ast.ty(ty) {
            Ty::Term(e) => return self.expr(*e),
            Ty::Con { module: None, name } | Ty::Var(name) => return self.name(name.as_str(), span),
            Ty::Con { module: Some(m), name } => RawKind::Var(format!("{m}.{name}").into(), Vec::new()),
            Ty::App(..) => return self.ty_spine(ty),
            Ty::Arrow { binder, from, effect, to } => {
                if effect.is_some() {
                    return Err(self.error(span, "a kernel function type carries no effect row"));
                }
                let name: Name = binder.map_or("_".into(), |b| b.as_str().into());
                RawKind::Pi(name, Box::new(self.ty(*from)?), Box::new(self.ty(*to)?))
            }
            Ty::Tuple(items) => {
                let items: Vec<Raw> = self.ast.slice(*items).iter().map(|t| self.ty(*t)).collect::<Result<_>>()?;
                return self.tuple(items, span);
            }
            Ty::Record { fields, tail: None } => {
                let fields = self.ast.slice(*fields);
                let mut fields: Vec<(Name, Raw)> =
                    fields.iter().map(|f| Ok((f.name.as_str().into(), self.ty(f.ty)?))).collect::<Result<_>>()?;
                let Some((_, mut acc)) = fields.pop() else { unreachable!("a record type has a field") };
                if fields.is_empty() {
                    return Err(self.error(span, "a dependent pair type has two fields or more"));
                }
                for (name, dom) in fields.into_iter().rev() {
                    acc = raw(RawKind::Sigma(name, Box::new(dom), Box::new(acc)), span);
                }
                return Ok(acc);
            }
            Ty::Nat(_) | Ty::SizeAdd(..) | Ty::SizeMul(..) => {
                return Err(self.error(span, "a number stands only for a level, as in `@Type 1`"))
            }
            Ty::Record { .. } | Ty::Unit | Ty::Sized { .. } | Ty::MetaE(_) => {
                return Err(self.error(span, "not a type of the kernel"))
            }
        };
        Ok(raw(kind, span))
    }

    fn ty_spine(&self, ty: Aol<Ty>) -> Result<Raw> {
        let mut args = Vec::new();
        let mut head = ty;
        while let Ty::App(f, a) = self.ast.ty(head) {
            args.push(Arg::Ty(*a));
            head = *f;
        }
        args.reverse();
        let head = match self.ast.ty(head) {
            Ty::Con { module: None, name } | Ty::Var(name) => Head::Name(*name, self.ty_span(head)),
            Ty::Con { module: Some(m), name } => Head::Name(utilities::StrId::intern(&format!("{m}.{name}")), self.ty_span(head)),
            _ => Head::Raw(self.ty(head)?),
        };
        self.spine(head, args, self.ty_span(ty))
    }

    // ### Terms

    fn expr(&self, e: Aol<Expr>) -> Result<Raw> {
        let span = self.expr_span(e);
        let kind = match self.ast.expr(e) {
            Expr::Type(ty) => return self.ty(*ty),
            Expr::Var { module: None, name } => return self.name(name.as_str(), span),
            Expr::Var { module: Some(m), name } => RawKind::Var(format!("{m}.{name}").into(), Vec::new()),
            Expr::App(..) => {
                let mut args = Vec::new();
                let mut head = e;
                while let Expr::App(f, a) = self.ast.expr(head) {
                    args.push(Arg::Expr(*a));
                    head = *f;
                }
                args.reverse();
                let head = match self.ast.expr(head) {
                    Expr::Var { module: None, name } => Head::Name(*name, self.expr_span(head)),
                    Expr::Var { module: Some(m), name } => {
                        Head::Name(utilities::StrId::intern(&format!("{m}.{name}")), self.expr_span(head))
                    }
                    _ => Head::Raw(self.expr(head)?),
                };
                return self.spine(head, args, span);
            }
            Expr::BinOp { op, lhs, rhs } => match op.as_str() {
                "~" => RawKind::Eq(Box::new(self.expr(*lhs)?), Box::new(self.expr(*rhs)?)),
                "|>" => return self.apply(*rhs, *lhs, span),
                "<|" => return self.apply(*lhs, *rhs, span),
                other => return Err(self.error(span, format!("`{other}` is not an operator of the kernel"))),
            },
            Expr::Lambda { params, body } => return self.lambda(self.ast.slice(*params), *body, span),
            Expr::Let { binding, body } => {
                let name = self.binder(binding.pat)?;
                let ann = binding.sig.map(|t| self.ty(t).map(Box::new)).transpose()?;
                RawKind::Let(name, ann, Box::new(self.expr(binding.value)?), Box::new(self.expr(*body)?))
            }
            Expr::Ascribe { expr, ty } => RawKind::Ann(Box::new(self.expr(*expr)?), Box::new(self.ty(*ty)?)),
            Expr::Tuple(items) => {
                let items: Vec<Raw> = self.ast.slice(*items).iter().map(|t| self.expr(*t)).collect::<Result<_>>()?;
                return self.tuple(items, span);
            }
            Expr::Field { record, name } => match name.as_str() {
                "0" => RawKind::Fst(Box::new(self.expr(*record)?)),
                "1" => RawKind::Snd(Box::new(self.expr(*record)?)),
                _ => return Err(self.error(span, "a pair projects by position, `.0` or `.1`")),
            },
            Expr::Variant { module: None, ty, tag, fields } => {
                let fields = self
                    .ast
                    .slice(*fields)
                    .iter()
                    .map(|f| match f {
                        FieldInit::Named { name, value } => Ok((Some(name.as_str().into()), self.expr(*value)?)),
                        FieldInit::Positional(value) => Ok((None, self.expr(*value)?)),
                    })
                    .collect::<Result<_>>()?;
                RawKind::Ctor { data: ty.map(|t| t.as_str().into()), tag: tag.as_str().into(), fields }
            }
            Expr::Int(_) => return Err(self.error(span, "a number stands only for a level, as in `@Type 1`")),
            _ => return Err(self.error(span, "not a term of the kernel")),
        };
        Ok(raw(kind, span))
    }

    /// `f x` written with a pipe. `x |> @absurd` is the primitive itself, at
    /// the type expected.
    fn apply(&self, f: Aol<Expr>, x: Aol<Expr>, span: Span) -> Result<Raw> {
        if self.is_absurd(f) {
            let proof = self.expr(x)?;
            return Ok(raw(RawKind::Prim(Primitive::Absurd, vec![raw(RawKind::Hole, span), proof]), span));
        }
        Ok(raw(RawKind::App(Box::new(self.expr(f)?), Box::new(self.expr(x)?)), span))
    }

    /// `@absurd`: the parser reads it as the lambda over an empty match.
    fn is_absurd(&self, e: Aol<Expr>) -> bool {
        matches!(self.ast.expr(e), Expr::Lambda { body, .. }
            if matches!(self.ast.expr(*body), Expr::Match { arms, .. } if self.ast.slice(*arms).is_empty()))
    }

    /// A name standing alone: a variable, a global, `_`, or a primitive
    /// with no arguments.
    fn name(&self, name: &str, span: Span) -> Result<Raw> {
        if name == "_" {
            return Ok(raw(RawKind::Hole, span));
        }
        if name.starts_with('@') {
            return self.spine(Head::Name(utilities::StrId::intern(name), span), Vec::new(), span);
        }
        Ok(raw(RawKind::Var(name.into(), Vec::new()), span))
    }

    fn tuple(&self, mut items: Vec<Raw>, span: Span) -> Result<Raw> {
        if items.len() < 2 {
            return Err(self.error(span, "a pair has two components"));
        }
        let mut acc = items.pop().expect("two components");
        while let Some(item) = items.pop() {
            acc = raw(RawKind::Tuple(Box::new(item), Box::new(acc)), span);
        }
        Ok(acc)
    }

    fn binder(&self, pat: Aol<Pattern>) -> Result<Name> {
        match self.ast.pat(pat) {
            Pattern::Var(name) => Ok(name.as_str().into()),
            Pattern::Wild => Ok("_".into()),
            _ => Err(self.error(self.ast.pat_span(pat).unwrap_or(Span::at(0)), "a kernel binder is a name or `_`")),
        }
    }

    fn lambda(&self, params: &[LamParam], body: Aol<Expr>, span: Span) -> Result<Raw> {
        // `@absurd`, the empty match: `\#arg => @absurd _ #arg`.
        let body = match self.ast.expr(body) {
            Expr::Match { scrut, arms, .. } if self.ast.slice(*arms).is_empty() => {
                let proof = self.expr(*scrut)?;
                raw(RawKind::Prim(Primitive::Absurd, vec![raw(RawKind::Hole, span), proof]), span)
            }
            Expr::Match { .. } => {
                return Err(self.error(span, "a kernel term eliminates with a recursor, `D.elim`, not a match"))
            }
            _ => self.expr(body)?,
        };
        params.iter().rev().try_fold(body, |body, p| {
            let name = self.binder(p.pat)?;
            let ann = p.sig.map(|t| self.ty(t).map(Box::new)).transpose()?;
            Ok(raw(RawKind::Lam(name, ann, Box::new(body)), span))
        })
    }

    /// An application: a primitive or `@Type` at its head takes its own
    /// arguments, and a `@ctx {.u = l}` argument gives the head its levels.
    fn spine(&self, head: Head, args: Vec<Arg>, span: Span) -> Result<Raw> {
        let mut levels = Vec::new();
        let mut rest = Vec::new();
        for arg in args {
            let term = match arg {
                Arg::Expr(a) => Some(a),
                Arg::Ty(t) => match self.ast.ty(t) {
                    Ty::Term(e) => Some(*e),
                    _ => None,
                },
            };
            match term.map(|e| self.ast.expr(e)) {
                Some(Expr::CtxArg(inits)) => levels.extend(self.level_args(*inits)?),
                _ => rest.push(arg),
            }
        }
        let mut rest = rest.into_iter();
        let mut acc = match head {
            Head::Raw(r) => r,
            Head::Name(name, name_span) => {
                let text = name.as_str();
                if text == "@Type" {
                    let Some(level) = rest.next() else {
                        return Err(self.error(span, "`@Type` takes a level: `@Type 1`, `@Type (u + 1)`"));
                    };
                    raw(RawKind::Sort(self.level(level)?), span)
                } else if let Some(&(_, prim, arity)) = PRIMITIVES.iter().find(|(w, ..)| *w == text) {
                    let args: Vec<Raw> = rest.by_ref().take(arity).map(|a| self.arg(a)).collect::<Result<_>>()?;
                    if args.len() < arity {
                        return Err(self.error(span, format!("`{text}` takes {arity} argument(s)")));
                    }
                    raw(RawKind::Prim(prim, args), span)
                } else if text.starts_with('@') {
                    return Err(error(self.src, Code::UnknownSymbol, name_span, format!("unknown primitive `{text}`")));
                } else if text == "_" {
                    raw(RawKind::Hole, name_span)
                } else {
                    raw(RawKind::Var(text.into(), levels.split_off(0)), name_span)
                }
            }
        };
        if let Some(l) = levels.first() {
            return Err(self.error(l.span, "only a global takes `@ctx` levels"));
        }
        for a in rest {
            let a = self.arg(a)?;
            let end = a.span.end.max(acc.span.end);
            let start = acc.span.start.min(a.span.start);
            acc = raw(RawKind::App(Box::new(acc), Box::new(a)), Span::new(start, end));
        }
        Ok(acc)
    }

    fn arg(&self, a: Arg) -> Result<Raw> {
        match a {
            Arg::Expr(e) => self.expr(e),
            Arg::Ty(t) => self.ty(t),
        }
    }

    // ### Levels

    fn level_args(&self, inits: utilities::Slice<FieldInit>) -> Result<Vec<LevelArg>> {
        self.ast
            .slice(inits)
            .iter()
            .map(|init| {
                let FieldInit::Named { name, value } = init else { unreachable!("the parser names level arguments") };
                Ok(LevelArg { name: name.as_str().into(), level: self.level(Arg::Expr(*value))?, span: self.expr_span(*value) })
            })
            .collect()
    }

    /// A level: a number, a level name, `l + n`, `@max a b` or `@imax a b`.
    fn level(&self, a: Arg) -> Result<RawLevel> {
        let bad = |span| self.error(span, "expected a level: a number, a level name, `l + n`, `@max a b` or `@imax a b`");
        match a {
            Arg::Expr(e) => {
                let span = self.expr_span(e);
                match self.ast.expr(e) {
                    Expr::Type(t) => self.level(Arg::Ty(*t)),
                    Expr::Int(n) => u32::try_from(*n).map(RawLevel::Num).map_err(|_| bad(span)),
                    Expr::Var { module: None, name } if !name.as_str().starts_with('@') => Ok(RawLevel::Name(name.as_str().into(), span)),
                    Expr::BinOp { op, lhs, rhs } if op.as_str() == "+" => match self.ast.expr(*rhs) {
                        Expr::Int(n) => Ok(RawLevel::Plus(Box::new(self.level(Arg::Expr(*lhs))?), u32::try_from(*n).map_err(|_| bad(span))?)),
                        _ => Err(bad(span)),
                    },
                    Expr::App(f, b) => match self.ast.expr(*f) {
                        Expr::App(m, a) => self.max(*m, Arg::Expr(*a), Arg::Expr(*b), span),
                        _ => Err(bad(span)),
                    },
                    _ => Err(bad(span)),
                }
            }
            Arg::Ty(t) => {
                let span = self.ty_span(t);
                match self.ast.ty(t) {
                    Ty::Term(e) => self.level(Arg::Expr(*e)),
                    Ty::Nat(n) => u32::try_from(*n).map(RawLevel::Num).map_err(|_| bad(span)),
                    Ty::Var(name) => Ok(RawLevel::Name(name.as_str().into(), span)),
                    Ty::SizeAdd(l, n) => match self.ast.ty(*n) {
                        Ty::Nat(n) => Ok(RawLevel::Plus(Box::new(self.level(Arg::Ty(*l))?), u32::try_from(*n).map_err(|_| bad(span))?)),
                        _ => Err(bad(span)),
                    },
                    Ty::App(f, b) => match self.ast.ty(*f) {
                        Ty::App(m, a) => match self.ast.ty(*m) {
                            Ty::Con { module: None, name } => self.max_named(name.as_str(), Arg::Ty(*a), Arg::Ty(*b), span),
                            _ => Err(bad(span)),
                        },
                        _ => Err(bad(span)),
                    },
                    _ => Err(bad(span)),
                }
            }
        }
    }

    fn max(&self, m: Aol<Expr>, a: Arg, b: Arg, span: Span) -> Result<RawLevel> {
        match self.ast.expr(m) {
            Expr::Var { module: None, name } => self.max_named(name.as_str(), a, b, span),
            _ => Err(self.error(span, "expected a level")),
        }
    }

    fn max_named(&self, name: &str, a: Arg, b: Arg, span: Span) -> Result<RawLevel> {
        let (a, b) = (Box::new(self.level(a)?), Box::new(self.level(b)?));
        match name {
            "@max" => Ok(RawLevel::Max(a, b)),
            "@imax" => Ok(RawLevel::IMax(a, b)),
            _ => Err(self.error(span, "expected a level: `@max a b` or `@imax a b`")),
        }
    }
}

/// An application's head: a name, which may be a primitive, or any term.
enum Head {
    Name(utilities::StrId, Span),
    Raw(Raw),
}

/// An argument, from an expression or a type position.
#[derive(Clone, Copy)]
enum Arg {
    Expr(Aol<Expr>),
    Ty(Aol<Ty>),
}
