//! The kernel's type checker: bidirectional elaboration of script syntax into
//! core terms.
//!
//! The algorithm is bidirectional type checking (Pierce and Turner, "Local
//! type inference", TOPLAS 2000; Dunfield and Krishnaswami, "Bidirectional
//! typing", CSUR 2021) over normalisation-by-evaluation values, in the shape
//! of Coquand's checker for dependent types. `check` pushes an
//! expected type into lambdas; `infer` synthesises a type at
//! variables, applications and annotations, and a synthesised type fits an
//! expected one when the two are convertible. Names are resolved as they are
//! checked, so the output is a de Bruijn [`Term`].
//!
//! Each global is checked in order and added to the [`Signature`]: its level
//! parameters first, then its type, then its body against that type.
//!
//! Input: a script. Output: the signature of its globals, with their proofs
//! kept so [`crate::recheck()`] can check it again, or the first error.
//!
//! Entry point: [`check_script`].

use std::rc::Rc;

use utilities::error::closest;
use utilities::{Code, Diagnostic, Result, Span};

use crate::conversion::ConversionChecker;
use crate::level::Level;
use crate::nbe::{apply, eval, fst, global_type, quote, BindingVal, Closure, Env, Lvl, Neutral, QuotVal, Val};
use crate::observational::{cast, eq, native_pi, relation_type};
use crate::inductive::{constructor_type, ford, projection_type, recursive_shape, recursor_type};
use crate::signature::{ConstructorDecl, DataDecl, DataId, Global, GlobalId, GlobalKind, Param, Signature};
use crate::syntax::{error, parse_script, Item, ItemBody, LevelArg, Primitive, Raw, RawConstructor, RawKind, RawLevel};
use crate::term::{mentions, mentions_global, Binding, Name, Term, TermDisplay};

/// Check every global of a script, after the prelude's.
pub fn check_script(src: &str) -> Result<Signature> {
    let mut sig = Signature::new();
    crate::prelude::load(&mut sig, |sig, item| {
        let mut checker = Checker { src: crate::prelude::SOURCE, sig: std::mem::take(sig) };
        let checked = checker.check_item(item);
        *sig = checker.sig;
        checked
    });
    let mut checker = Checker { src, sig };
    for item in parse_script(src)? {
        checker.check_item(&item)?;
    }
    Ok(checker.sig)
}

struct Checker<'s> {
    src: &'s str,
    sig: Signature,
}

/// The variables in scope, outermost first: their names and types, and the
/// environment that evaluates a term in that scope.
struct Context {
    names: Vec<Name>,
    types: Vec<Val>,
    env: Env,
    level_names: Vec<Name>,
}

impl Context {
    fn new(level_names: Vec<Name>) -> Context {
        Context {
            names: Vec::new(),
            types: Vec::new(),
            env: Env::new(),
            level_names,
        }
    }

    fn depth(&self) -> Lvl {
        self.types.len() as Lvl
    }

    /// Bind a variable of type `ty` with no value.
    fn bind(&mut self, name: Name, ty: Val) {
        self.env = self.env.extend(Val::var(self.depth()));
        self.names.push(name);
        self.types.push(ty);
    }

    /// Bind a variable of type `ty` that stands for `val`.
    fn define(&mut self, name: Name, ty: Val, val: Val) {
        self.env = self.env.extend(val);
        self.names.push(name);
        self.types.push(ty);
    }
}

// ## Globals

impl Checker<'_> {
    fn error(&self, code: Code, span: Span, msg: impl Into<String>) -> Diagnostic {
        error(self.src, code, span, msg)
    }

    fn check_item(&mut self, item: &Item) -> Result<()> {
        if self.sig.lookup(&item.name).is_some_and(|id| !self.sig.is_prelude(id)) {
            return Err(self.error(Code::DuplicateSymbol, item.span, format!("`{}` is already defined", item.name)));
        }
        let mut level_names: Vec<Name> = Vec::new();
        for (name, span) in &item.level_params {
            if level_names.contains(name) {
                return Err(self.error(Code::DuplicateSymbol, *span, format!("level `{name}` is bound twice")));
            }
            level_names.push(name.clone());
        }
        if let ItemBody::Data(ctors) = &item.body {
            return self.check_data(item, level_names, ctors);
        }
        let mut ctx = Context::new(level_names.clone());
        let (ty, _) = self.check_type(&mut ctx, &item.ty)?;
        let kind = match &item.body {
            ItemBody::Definition(body) => {
                let expected = eval(&self.sig, &ctx.env, &ty);
                GlobalKind::Definition(Rc::new(self.check(&mut ctx, body, &expected)?))
            }
            ItemBody::Axiom => GlobalKind::Axiom,
            ItemBody::Data(_) => unreachable!("handled above"),
        };
        self.sig.add(Global {
            name: item.name.clone(),
            level_params: level_names,
            ty: Rc::new(ty),
            kind,
        });
        Ok(())
    }
}

// ## Inductive declarations

impl Checker<'_> {
    /// Reject a name a declaration would introduce twice.
    fn fresh_global(&self, name: &str, span: Span, taken: &[Name]) -> Result<()> {
        if self.sig.lookup(name).is_some_and(|id| !self.sig.is_prelude(id)) || taken.iter().any(|t| &**t == name) {
            return Err(self.error(Code::DuplicateSymbol, span, format!("`{name}` is already defined")));
        }
        Ok(())
    }

    // Rule [Data-Form]
    fn check_data(&mut self, item: &Item, level_names: Vec<Name>, ctors: &[RawConstructor]) -> Result<()> {
        let mut ctx = Context::new(level_names.clone());
        let (ty, _) = self.check_type(&mut ctx, &item.ty)?;
        let mut params = Vec::new();
        let mut result = &ty;
        while let Term::Pi(b) = result {
            params.push(Param {
                name: b.name.clone(),
                ty: b.dom.clone(),
                level: b.dom_level.clone(),
            });
            result = &b.cod;
        }
        let Term::Sort(level) = result.clone() else {
            return Err(self.error(
                Code::Unsupported,
                item.ty.span,
                "an inductive type's signature must end in `@Type l` after its parameters and indices",
            ));
        };
        if !level.is_nonzero() {
            return Err(self.error(
                Code::Unsupported,
                item.ty.span,
                "inductive propositions are not supported: the type must be in `@Type l` with `l >= 1`",
            ));
        }
        let uniform = uniform_params(&params, ctors);
        for (i, index) in params[uniform..].iter().enumerate() {
            if (0..i as u32).any(|v| mentions(&index.ty, v)) {
                return Err(self.error(
                    Code::Unsupported,
                    item.ty.span,
                    format!("the type of index `{}` may depend on the parameters, not on earlier indices", index.name),
                ));
            }
            if !index.level.is_nonzero() {
                return Err(self.error(
                    Code::Unsupported,
                    item.ty.span,
                    format!("index `{}` must be data, in `@Type l` with `l >= 1`, not a proof", index.name),
                ));
            }
        }
        let recursor_name: Name = format!("{}.elim", item.name).into();
        let mut taken = vec![item.name.clone(), recursor_name.clone()];
        // Constructor `Tag` of `D` is the global `D.Tag`.
        let ctor_name = |c: &RawConstructor| -> Name { format!("{}.{}", item.name, c.name).into() };
        for c in ctors {
            self.fresh_global(&ctor_name(c), c.span, &taken)?;
            taken.push(ctor_name(c));
        }
        // `D.eq_Tag_f` for field `f` of constructor `Tag`, or `D.eq_Tag_argN`
        // for the unnamed `N`th field.
        let projection_name = |c: &RawConstructor, j: usize| -> Name {
            match &*c.fields[j].0 {
                "_" => format!("{}.eq_{}_arg{}", item.name, c.name, j + 1).into(),
                field => format!("{}.eq_{}_{field}", item.name, c.name).into(),
            }
        };
        let has_params = matches!(ty, Term::Pi(_));
        for c in ctors.iter().filter(|_| has_params) {
            for j in 0..c.fields.len() {
                let name = projection_name(c, j);
                self.fresh_global(&name, c.span, &taken)?;
                taken.push(name);
            }
        }
        self.fresh_global(&recursor_name, item.span, &[])?;

        let data = self.sig.add_data(DataDecl {
            global: self.sig.next_global(),
            params,
            uniform,
            level: level.clone(),
            constructors: Vec::new(),
            projections: Vec::new(),
            recursor: GlobalId::MAX,
        });
        self.sig.add(Global {
            name: item.name.clone(),
            level_params: level_names.clone(),
            ty: Rc::new(ty),
            kind: GlobalKind::Data(data),
        });
        for (index, c) in ctors.iter().enumerate() {
            let mut decl = self.check_constructor(data, &level_names, &level, c)?;
            decl.global = self.sig.next_global();
            self.sig.data_mut(data).constructors.push(decl);
            let ty = constructor_type(self.sig.data(data), level_names.len(), index);
            self.sig.add(Global {
                name: ctor_name(c),
                level_params: level_names.clone(),
                ty: Rc::new(ty),
                kind: GlobalKind::Constructor(data, index),
            });
        }
        // A type without parameters is equal only to itself, so its
        // projections would say nothing.
        for (index, c) in ctors.iter().enumerate().filter(|_| has_params) {
            for j in 0..c.fields.len() {
                let ty = projection_type(self.sig.data(data), level_names.len(), index, j);
                let id = self.sig.next_global();
                self.sig.data_mut(data).projections.push(id);
                self.sig.add(Global {
                    name: projection_name(c, j),
                    level_params: level_names.clone(),
                    ty: Rc::new(ty),
                    kind: GlobalKind::Projection(data, index, j),
                });
            }
        }

        let mut recursor_levels = level_names.clone();
        let mut motive: Name = "m".into();
        while recursor_levels.contains(&motive) {
            motive = format!("{motive}2").into();
        }
        recursor_levels.push(motive);
        let ty = recursor_type(self.sig.data(data), level_names.len());
        self.sig.data_mut(data).recursor = self.sig.next_global();
        self.sig.add(Global {
            name: recursor_name,
            level_params: recursor_levels,
            ty: Rc::new(ty),
            kind: GlobalKind::Recursor(data),
        });
        Ok(())
    }

    fn check_constructor(&self, data: DataId, level_names: &[Name], level: &Level, c: &RawConstructor) -> Result<ConstructorDecl> {
        let decl = self.sig.data(data);
        let (np, u) = (decl.params.len(), decl.uniform);
        let data_name = &self.sig.global(decl.global).name;
        // The fields see the uniform parameters only; the indices are what the
        // constructor's result fixes.
        let mut ctx = Context::new(level_names.to_vec());
        for p in &decl.params[..u] {
            let ty = self.eval(&ctx, &p.ty);
            ctx.bind(p.name.clone(), ty);
        }
        let mut surface = Vec::new();
        let mut recursive = Vec::new();
        for (i, (name, raw)) in c.fields.iter().enumerate() {
            // An unnamed field gets a positional name, for printing the
            // recursor's type.
            let name: Name = if &**name == "_" { format!("f{i}").into() } else { name.clone() };
            let (ty, field_level) = self.check_type(&mut ctx, raw)?;
            if !field_level.leq(level) {
                return Err(self.error(
                    Code::TypeMismatch,
                    raw.span,
                    format!("this field is too large for the type's universe `{}`", self.show(&ctx, &Val::Sort(level.clone()))),
                ));
            }
            let ty_val = self.eval(&ctx, &ty);
            // Rule [Positivity-Restricted]
            // See Note [Strict positivity, restricted].
            let is_self = is_recursive_field(&ty, decl.global, np, u, (u + i) as u32);
            if !is_self && mentions_global(&ty, decl.global) {
                return Err(self.error(
                    Code::Unsupported,
                    raw.span,
                    format!("`{data_name}` may only occur as the result of a field's type, applied to its own parameters"),
                ));
            }
            surface.push(Param {
                name: name.clone(),
                ty: Rc::new(ty),
                level: field_level,
            });
            recursive.push(is_self);
            ctx.bind(name, ty_val);
        }
        let indices: Vec<Rc<Term>> = match &c.result {
            None if u < np => {
                return Err(self.error(
                    Code::Unsupported,
                    c.span,
                    format!("a constructor of the indexed family `{data_name}` must state its result: `{}: {{fields}} -> {data_name} ...`", c.name),
                ));
            }
            None => Vec::new(),
            Some(raw) => {
                let (ty, _) = self.check_type(&mut ctx, raw)?;
                let ty_val = self.eval(&ctx, &ty);
                // The indices as written when the result is `D` applied
                // directly, so they keep their proofs; read back otherwise.
                let written = spine(&ty);
                let ty_val = ty_val.force(&self.sig).clone();
                let indices: Vec<Rc<Term>> = match &ty_val {
                    Val::Data(_) if is_data_at_own_params(&ty_val, data, np, u) && written.len() == np && head(&ty) == Some(decl.global) => {
                        written[u..].iter().map(|y| Rc::new((*y).clone())).collect()
                    }
                    Val::Data(d) if is_data_at_own_params(&ty_val, data, np, u) => {
                        d.params[u..].iter().map(|y| Rc::new(quote(&self.sig, ctx.depth(), y))).collect()
                    }
                    _ => {
                        return Err(self.error(
                            Code::TypeMismatch,
                            raw.span,
                            format!("a constructor's result must be `{data_name}` at its own parameters"),
                        ));
                    }
                };
                if indices.iter().any(|y| mentions_global(y, decl.global)) {
                    return Err(self.error(Code::Unsupported, raw.span, format!("an index may not mention `{data_name}`")));
                }
                indices
            }
        };

        let (fields, recursive) = ford(decl, &surface, recursive, &indices);
        Ok(ConstructorDecl {
            name: c.name.clone(),
            global: GlobalId::MAX,
            fields,
            recursive,
            surface,
            indices,
        })
    }
}

/// `(x y: A) -> R x y -> @cast (P (@qin x)) (P (@qin y)) _ (f x) ~ f y`: the
/// method `f` sends related representatives to equal results.
pub(crate) fn respect_type(quot: Rc<QuotVal>, p: Val, f: Val, level: Level) -> Val {
    let outer = quot.clone();
    native_pi("x", outer.carrier.clone(), outer.level.clone(), Level::Zero, move |_, x| {
        let (quot, p, f, level) = (quot.clone(), p.clone(), f.clone(), level.clone());
        native_pi("y", quot.carrier.clone(), quot.level.clone(), Level::Zero, move |sig, y| {
            let related = apply(sig, apply(sig, quot.relation.clone(), x.clone()), y.clone());
            let px = apply(sig, p.clone(), Val::QIn(Rc::new(x.clone())));
            let py = apply(sig, p.clone(), Val::QIn(Rc::new(y.clone())));
            let moved = cast(sig, px, py.clone(), Val::Irrelevant, apply(sig, f.clone(), x.clone()));
            let goal = eq(sig, level.clone(), py, moved, apply(sig, f.clone(), y));
            native_pi("_", related, Level::Zero, Level::Zero, move |_, _| goal.clone())
        })
    })
}

/// The types of the proofs that `r` is an equivalence on `a : @Type level`:
/// `(x: A) -> R x x`, `(x y: A) -> R x y -> R y x` and
/// `(x y z: A) -> R x y -> R y z -> R x z`.
pub(crate) fn equivalence_laws(a: &Val, r: &Val, level: &Level) -> [Val; 3] {
    let r0 = r.clone();
    let rel = Rc::new(move |sig: &Signature, x: Val, y: Val| apply(sig, apply(sig, r0.clone(), x), y));

    let r1 = rel.clone();
    let reflexive = native_pi("x", a.clone(), level.clone(), Level::Zero, move |sig, x| r1(sig, x.clone(), x));

    let (a2, l2, r2) = (a.clone(), level.clone(), rel.clone());
    let symmetric = native_pi("x", a.clone(), level.clone(), Level::Zero, move |_, x| {
        let r2 = r2.clone();
        native_pi("y", a2.clone(), l2.clone(), Level::Zero, move |sig, y| {
            let forward = r2(sig, x.clone(), y.clone());
            let back = r2(sig, y, x.clone());
            native_pi("_", forward, Level::Zero, Level::Zero, move |_, _| back.clone())
        })
    });

    let (a3, l3, rel3) = (a.clone(), level.clone(), rel);
    let transitive = native_pi("x", a.clone(), level.clone(), Level::Zero, move |_, x| {
        let (a3, l3, rel3) = (a3.clone(), l3.clone(), rel3.clone());
        native_pi("y", a3.clone(), l3.clone(), Level::Zero, move |_, y| {
            let (x, rel3) = (x.clone(), rel3.clone());
            native_pi("z", a3.clone(), l3.clone(), Level::Zero, move |sig, z| {
                let (xy, yz, xz) = (rel3(sig, x.clone(), y.clone()), rel3(sig, y.clone(), z.clone()), rel3(sig, x.clone(), z));
                native_pi("_", xy, Level::Zero, Level::Zero, move |_, _| {
                    let xz = xz.clone();
                    native_pi("_", yz.clone(), Level::Zero, Level::Zero, move |_, _| xz.clone())
                })
            })
        })
    });
    [reflexive, symmetric, transitive]
}

/// The global at the head of an application spine, if it is one.
pub(crate) fn head(t: &Term) -> Option<GlobalId> {
    let mut t = t;
    while let Term::App(f, _) = t {
        t = f;
    }
    match t {
        Term::Global(id, _) => Some(*id),
        _ => None,
    }
}

/// `ty` is `D p0 ... pn` with each `pi` the parameter variable at level `i`.
/// `ty` is `D` applied to its own uniform parameters (the first `uniform`
/// of `params`), at any indices.
pub(crate) fn is_data_at_own_params(ty: &Val, data: DataId, params: usize, uniform: usize) -> bool {
    let Val::Data(d) = ty else { return false };
    let own = |(i, p): (usize, &Val)| matches!(p, Val::Neutral(n) if matches!(**n, Neutral::Var(l) if l as usize == i));
    d.data == data && d.params.len() == params && d.params[..uniform].iter().enumerate().all(own)
}

// Rule [Positivity-Branching]
/// Whether a field's type `ty`, over the uniform parameters and the fields
/// before it (`depth` binders in all), is a recursive occurrence of the
/// inductive type `global`: `(a_1: A_1) -> ... -> (a_k: A_k) -> D params ys`,
/// with the uniform parameters passed through as themselves and `D` in no
/// `A_i` and no index `y`. The check is syntactic, so it agrees with what
/// the recursor's generator reads off the field.
pub(crate) fn is_recursive_field(ty: &Term, global: GlobalId, params: usize, uniform: usize, depth: u32) -> bool {
    let (binders, body) = recursive_shape(ty);
    let k = binders.len() as u32;
    let args = spine(body);
    let own = |(p, a): (usize, &&Term)| matches!(a, Term::Var(v) if *v == depth + k - 1 - p as u32);
    head(body) == Some(global)
        && args.len() == params
        && args[..uniform].iter().enumerate().all(own)
        && !args[uniform..].iter().any(|a| mentions_global(a, global))
        && !binders.iter().any(|b| mentions_global(&b.dom, global))
}

/// The arguments of an application spine.
pub(crate) fn spine(t: &Term) -> Vec<&Term> {
    let mut args = Vec::new();
    let mut t = t;
    while let Term::App(f, a) = t {
        args.push(&**a);
        t = f;
    }
    args.reverse();
    args
}

/// How many leading binders of an inductive type's signature are uniform
/// parameters: every constructor's stated result passes them through as
/// themselves. The rest are indices.
fn uniform_params(params: &[Param], ctors: &[RawConstructor]) -> usize {
    let raw_spine = |r: &Raw| {
        let mut args = Vec::new();
        let mut r = r;
        while let RawKind::App(f, a) = &r.kind {
            args.push((**a).clone());
            r = f;
        }
        args.reverse();
        args
    };
    ctors
        .iter()
        .map(|c| match &c.result {
            None => params.len(),
            Some(result) => {
                let args = raw_spine(result);
                let passes = |(p, a): &(&Param, &Raw)| {
                    let shadowed = c.fields.iter().any(|(f, _)| *f == p.name);
                    !shadowed && matches!(&a.kind, RawKind::Var(n, levels) if *n == p.name && levels.is_empty())
                };
                params.iter().zip(&args).take_while(passes).count()
            }
        })
        .min()
        .unwrap_or(params.len())
}

// Note [Strict positivity, restricted]
//
// An inductive type may appear in its own constructors only where its
// recursor can recurse: as the result of a field's type,
// `(a: A) -> D params ys`, with exactly the declaration's parameters and
// with `D` neither in the domains `A` nor in the indices `ys`. With no Pi in
// front this is a whole field `D params ys`; with one it is an infinitely
// branching node, whose induction hypothesis is a function
// `(a: A) -> P ys (f a)`. Strict positivity proper also allows nested
// occurrences such as `List (D params)`; they need a nested recursor or a
// translation to a mutual family, and are rejected for now (#467). Anything
// that is not positive must be rejected for consistency: a negative
// occurrence gives a fixpoint combinator.

// ## Bidirectional checking

impl Checker<'_> {
    fn conversion<'a>(&'a self, ctx: &'a mut Context) -> ConversionChecker<'a> {
        ConversionChecker {
            sig: &self.sig,
            types: &mut ctx.types,
        }
    }

    fn eval(&self, ctx: &Context, t: &Term) -> Val {
        eval(&self.sig, &ctx.env, t)
    }

    fn show(&self, ctx: &Context, v: &Val) -> String {
        let term = quote(&self.sig, ctx.depth(), v);
        TermDisplay {
            sig: &self.sig,
            names: &ctx.names,
            level_names: &ctx.level_names,
            term: &term,
        }
        .to_string()
    }

    /// Types print folded; a note gives the head of each unfolded, its
    /// arguments still folded, when that reads differently.
    /// See Note [Glued evaluation].
    fn mismatch(&self, ctx: &Context, span: Span, expected: &Val, found: &Val) -> Diagnostic {
        let (shown_expected, shown_found) = (self.show(ctx, expected), self.show(ctx, found));
        let unfolded = |v: &Val, shown: &str| Some(self.show(ctx, v.force(&self.sig))).filter(|head| head != shown);
        let (head_expected, head_found) = (unfolded(expected, &shown_expected), unfolded(found, &shown_found));
        if matches!(expected.force(&self.sig), Val::Bottom) && head_expected.is_some() {
            return self
                .error(Code::TypeMismatch, span, "this claim is false")
                .with_note(format!("the claim `{shown_expected}` computes to `@Bottom`"))
                .with_note(format!("found a proof of `{shown_found}`"));
        }
        let mut d = self.error(Code::TypeMismatch, span, format!("expected `{shown_expected}`, found `{shown_found}`"));
        if let Some(head) = head_expected {
            d = d.with_note(format!("the expected type computes to `{head}`"));
        }
        if let Some(head) = head_found {
            d = d.with_note(format!("the found type computes to `{head}`"));
        }
        d
    }

    /// Run `k` with `name: ty` in scope.
    fn under<R>(&self, ctx: &mut Context, name: &Name, ty: Val, k: impl FnOnce(&Self, &mut Context) -> R) -> R {
        let env = ctx.env.clone();
        ctx.bind(name.clone(), ty);
        let r = k(self, ctx);
        ctx.names.pop();
        ctx.types.pop();
        ctx.env = env;
        r
    }

    /// Elaborate `raw` as a type, returning its sort.
    fn check_type(&self, ctx: &mut Context, raw: &Raw) -> Result<(Term, Level)> {
        let (t, ty) = self.infer(ctx, raw)?;
        match ty.force(&self.sig).clone() {
            Val::Sort(l) => Ok((t, l)),
            _ if self.is_bool(ctx, &ty) => Ok((self.reflect(t), Level::Zero)),
            other => Err(self.error(
                Code::TypeMismatch,
                raw.span,
                format!("expected a type, found a value of type `{}`", self.show(ctx, &other)),
            )),
        }
    }

    /// Whether `ty` is the prelude's `Bool`.
    fn is_bool(&self, ctx: &mut Context, ty: &Val) -> bool {
        let Some(builtins) = self.sig.builtins() else { return false };
        let bool = eval(&self.sig, &Env::new(), &Term::Global(builtins.bool, Rc::new([])));
        self.conversion(ctx).conv_type(ty, &bool)
    }

    // Rule [Bool-Reflection]
    /// The proposition a boolean `b` stands for where a type is expected,
    /// `b ~ true`. See Note [Booleans as propositions].
    fn reflect(&self, b: Term) -> Term {
        let builtins = self.sig.builtins().expect("only a script, after the prelude, has a boolean in a type");
        let global = |id| Rc::new(Term::Global(id, Rc::new([])));
        Term::Eq(Level::constant(1), global(builtins.bool), Rc::new(b), global(builtins.true_value))
    }

    // Algorithm [Bidirectional checking]
    fn check(&self, ctx: &mut Context, raw: &Raw, expected: &Val) -> Result<Term> {
        let term = self.check_relevant(ctx, raw, expected)?;
        // Rule [Proof-Witness]
        // See Note [Proofs evaluate to an irrelevant witness].
        if self.conversion(ctx).is_proposition(expected) && !matches!(term, Term::Proof(_)) {
            return Ok(Term::Proof(Rc::new(term)));
        }
        Ok(term)
    }

    fn check_relevant(&self, ctx: &mut Context, raw: &Raw, expected: &Val) -> Result<Term> {
        match (&raw.kind, expected.force(&self.sig)) {
            // Rule [Fun]
            (RawKind::Lam(name, ann, body), Val::Pi(pi)) => {
                let dom = match ann {
                    Some(ann) => {
                        let (t, _) = self.check_type(ctx, ann)?;
                        let given = self.eval(ctx, &t);
                        if !self.conversion(ctx).conv_type(&given, &pi.dom) {
                            return Err(self.mismatch(ctx, ann.span, &pi.dom, &given));
                        }
                        Some(Rc::new(t))
                    }
                    None => None,
                };
                let body = self.under(ctx, name, pi.dom.clone(), |c, ctx| {
                    let cod = pi.cod.apply(&c.sig, Val::var(ctx.depth() - 1));
                    c.check(ctx, body, &cod)
                })?;
                Ok(Term::Lam(name.clone(), dom, Rc::new(body)))
            }
            (RawKind::Ctor { .. }, _) => {
                let spine = self.constructor_spine(raw)?;
                self.check_relevant(ctx, &spine, expected)
            }
            // Rule [Sigma-Pair]
            (RawKind::Tuple(a, b), Val::Sigma(sigma)) => {
                let a = self.check(ctx, a, &sigma.dom)?;
                let cod = sigma.cod.apply(&self.sig, self.eval(ctx, &a));
                let b = self.check(ctx, b, &cod)?;
                Ok(Term::Pair(Rc::new(a), Rc::new(b)))
            }
            // `x |> @absurd`: at the type expected.
            (RawKind::Prim(Primitive::Absurd, args), _) if matches!(args[0].kind, RawKind::Hole) => {
                let proof = self.check(ctx, &args[1], &Val::Bottom)?;
                let ty = quote(&self.sig, ctx.depth(), expected);
                Ok(Term::Absurd(Rc::new(ty), Rc::new(proof)))
            }
            // Rule [Quot-Intro]
            (RawKind::Prim(Primitive::QIn, args), Val::Quot(q)) => {
                let a = self.check(ctx, &args[0], &q.carrier)?;
                Ok(Term::QIn(Rc::new(a)))
            }
            // Rule [Let]
            (RawKind::Let(name, ann, val, body), _) => {
                let (ty, val) = self.let_binding(ctx, ann.as_deref(), val)?;
                let (ty_val, val_val) = (self.eval(ctx, &ty), self.eval(ctx, &val));
                let env = ctx.env.clone();
                ctx.define(name.clone(), ty_val, val_val);
                let body = self.check(ctx, body, expected);
                ctx.names.pop();
                ctx.types.pop();
                ctx.env = env;
                Ok(Term::Let(name.clone(), Rc::new(ty), Rc::new(val), Rc::new(body?)))
            }
            _ if self.is_open_spine(ctx, raw) => Ok(self.spine(ctx, raw, Some(expected))?.0),
            _ => {
                let (t, found) = self.infer(ctx, raw)?;
                if self.conversion(ctx).conv_type(&found, expected) {
                    Ok(t)
                } else if matches!(expected.force(&self.sig), Val::Sort(_)) && self.is_bool(ctx, &found) {
                    if self.conversion(ctx).conv_type(&Val::Sort(Level::Zero), expected) {
                        Ok(self.reflect(t))
                    } else {
                        Err(self.mismatch(ctx, raw.span, expected, &Val::Sort(Level::Zero)))
                    }
                } else {
                    Err(self.mismatch(ctx, raw.span, expected, &found))
                }
            }
        }
    }

    fn infer(&self, ctx: &mut Context, raw: &Raw) -> Result<(Term, Val)> {
        if self.is_open_spine(ctx, raw) {
            return self.spine(ctx, raw, None);
        }
        match &raw.kind {
            RawKind::Nat(n) => {
                let builtins = self.sig.builtins().expect("the prelude declares no numeral");
                let nat = eval(&self.sig, &Env::new(), &Term::Global(builtins.nat, Rc::new([])));
                Ok((crate::prelude::numeral(builtins, *n), nat))
            }
            RawKind::Hole => Err(self.error(
                Code::TypeAnnotationRequired,
                raw.span,
                "cannot infer this `_`: it stands only for an argument of an application whose type fixes it",
            )),
            RawKind::Var(name, level_args) => self.infer_var(ctx, raw.span, name, level_args),
            // Rule [Univ]
            RawKind::Sort(l) => {
                let l = self.level(ctx, l)?;
                Ok((Term::Sort(l.clone()), Val::Sort(l.succ())))
            }
            // Rule [Pi-Form]
            RawKind::Pi(name, dom, cod) => {
                let binding = self.binding(ctx, name, dom, cod)?;
                let sort = Level::imax(&binding.dom_level, &binding.cod_level);
                Ok((Term::Pi(Rc::new(binding)), Val::Sort(sort)))
            }
            // Rule [Sigma-Form]
            RawKind::Sigma(name, dom, cod) => {
                let binding = self.binding(ctx, name, dom, cod)?;
                let sort = Level::max(&binding.dom_level, &binding.cod_level);
                Ok((Term::Sigma(Rc::new(binding)), Val::Sort(sort)))
            }
            // A pair whose type is not given is the type of pairs, `{A, B}`.
            RawKind::Tuple(a, b) => {
                let binding = self.binding(ctx, &"_".into(), a, b)?;
                let sort = Level::max(&binding.dom_level, &binding.cod_level);
                Ok((Term::Sigma(Rc::new(binding)), Val::Sort(sort)))
            }
            RawKind::Ctor { .. } => {
                let spine = self.constructor_spine(raw)?;
                self.infer(ctx, &spine)
            }
            RawKind::Fst(e) | RawKind::Snd(e) => {
                let (t, ty) = self.infer(ctx, e)?;
                let Val::Sigma(sigma) = ty.force(&self.sig) else {
                    return Err(self.error(
                        Code::TypeMismatch,
                        e.span,
                        format!("projected from a value of type `{}`, which is not a pair", self.show(ctx, &ty)),
                    ));
                };
                let t = Rc::new(t);
                if matches!(raw.kind, RawKind::Fst(_)) {
                    Ok((Term::Fst(t), sigma.dom.clone()))
                } else {
                    let first = fst(&self.sig, self.eval(ctx, &t));
                    Ok((Term::Snd(t), sigma.cod.apply(&self.sig, first)))
                }
            }
            RawKind::Lam(name, Some(ann), body) => {
                let (dom, dom_level) = self.check_type(ctx, ann)?;
                let dom_val = self.eval(ctx, &dom);
                let (body, cod, cod_level) = self.under(ctx, name, dom_val.clone(), |c, ctx| {
                    let (body, cod) = c.infer(ctx, body)?;
                    let level = c.conversion(ctx).sort_of(&cod);
                    Ok::<_, Diagnostic>((body, quote(&c.sig, ctx.depth(), &cod), level))
                })?;
                let Some(cod_level) = cod_level else {
                    return Err(self.error(Code::TypeAnnotationRequired, raw.span, "cannot infer the sort of this lambda's result"));
                };
                let ty = Val::Pi(Rc::new(BindingVal {
                    name: name.clone(),
                    dom: dom_val,
                    cod: Closure::Term(ctx.env.clone(), Rc::new(cod)),
                    dom_level,
                    cod_level,
                }));
                Ok((Term::Lam(name.clone(), Some(Rc::new(dom)), Rc::new(body)), ty))
            }
            RawKind::Lam(name, None, _) => Err(self.error(
                Code::TypeAnnotationRequired,
                raw.span,
                format!("cannot infer the type of `{name}`; annotate it as `\\({name}: T) => ...`"),
            )),
            // Rule [App]
            RawKind::App(f, a) => {
                let (f_term, f_ty) = self.infer(ctx, f)?;
                let Val::Pi(pi) = f_ty.force(&self.sig) else {
                    return Err(self.error(
                        Code::TypeMismatch,
                        f.span,
                        format!("applied a value of type `{}`, which is not a function", self.show(ctx, &f_ty)),
                    ));
                };
                let a_term = self.check(ctx, a, &pi.dom)?;
                let ty = pi.cod.apply(&self.sig, self.eval(ctx, &a_term));
                Ok((Term::app(f_term, a_term), ty))
            }
            RawKind::Let(name, ann, val, body) => {
                let (ty, val) = self.let_binding(ctx, ann.as_deref(), val)?;
                let (ty_val, val_val) = (self.eval(ctx, &ty), self.eval(ctx, &val));
                let env = ctx.env.clone();
                ctx.define(name.clone(), ty_val, val_val);
                let body = self.infer(ctx, body);
                ctx.names.pop();
                ctx.types.pop();
                ctx.env = env;
                let (body, body_ty) = body?;
                Ok((Term::Let(name.clone(), Rc::new(ty), Rc::new(val), Rc::new(body)), body_ty))
            }
            RawKind::Ann(e, ty) => {
                let (ty, _) = self.check_type(ctx, ty)?;
                let ty_val = self.eval(ctx, &ty);
                let e = self.check(ctx, e, &ty_val)?;
                Ok((Term::Ann(Rc::new(e), Rc::new(ty)), ty_val))
            }
            RawKind::Prim(prim, args) => self.infer_primitive(ctx, *prim, args),
            // Rule [Eq-Form]
            RawKind::Eq(a, b) => {
                let (a, ty) = self.infer(ctx, a)?;
                let level = self.sort_of(ctx, &ty, raw.span)?;
                self.relevant(ctx, &ty, &level, raw.span)?;
                let b = self.check(ctx, b, &ty)?;
                let ty = quote(&self.sig, ctx.depth(), &ty);
                Ok((Term::Eq(level, Rc::new(ty), Rc::new(a), Rc::new(b)), Val::Sort(Level::Zero)))
            }
        }
    }

    /// The sort of a type a term was inferred to have.
    fn sort_of(&self, ctx: &mut Context, ty: &Val, span: Span) -> Result<Level> {
        match self.conversion(ctx).sort_of(ty) {
            Some(level) => Ok(level),
            None => Err(self.error(
                Code::TypeAnnotationRequired,
                span,
                format!("cannot tell which universe `{}` lives in", self.show(ctx, ty)),
            )),
        }
    }

    /// Equality is formed only at a type that is not a proposition: two
    /// proofs are already equal by conversion.
    /// See Note [Equality is not formed at a proposition].
    fn relevant(&self, ctx: &mut Context, ty: &Val, level: &Level, span: Span) -> Result<()> {
        if !level.is_zero() {
            return Ok(());
        }
        Err(self.error(
            Code::TypeMismatch,
            span,
            format!("equality is not formed at the proposition `{}`", self.show(ctx, ty)),
        ))
    }

    /// The domain and codomain of a Pi or Sigma type.
    fn binding(&self, ctx: &mut Context, name: &Name, dom: &Raw, cod: &Raw) -> Result<Binding> {
        let (dom, dom_level) = self.check_type(ctx, dom)?;
        let dom_val = self.eval(ctx, &dom);
        let (cod, cod_level) = self.under(ctx, name, dom_val, |c, ctx| c.check_type(ctx, cod))?;
        Ok(Binding {
            name: name.clone(),
            dom: Rc::new(dom),
            cod: Rc::new(cod),
            dom_level,
            cod_level,
        })
    }

    fn infer_primitive(&self, ctx: &mut Context, prim: Primitive, args: &[Raw]) -> Result<(Term, Val)> {
        let proposition = Val::Sort(Level::Zero);
        Ok(match prim {
            // Rule [Top]
            Primitive::Top => (Term::Top, proposition),
            Primitive::Tt => (Term::Tt, Val::Top),
            // Rule [Bottom]
            Primitive::Bottom => (Term::Bottom, proposition),
            Primitive::Absurd => {
                let (ty, _) = self.check_type(ctx, &args[0])?;
                let proof = self.check(ctx, &args[1], &Val::Bottom)?;
                let ty_val = self.eval(ctx, &ty);
                (Term::Absurd(Rc::new(ty), Rc::new(proof)), ty_val)
            }
            // Rule [Eq-Form]
            Primitive::Eq => {
                let (ty, level) = self.check_type(ctx, &args[0])?;
                let ty_val = self.eval(ctx, &ty);
                self.relevant(ctx, &ty_val, &level, args[0].span)?;
                let a = self.check(ctx, &args[1], &ty_val)?;
                let b = self.check(ctx, &args[2], &ty_val)?;
                (Term::Eq(level, Rc::new(ty), Rc::new(a), Rc::new(b)), proposition)
            }
            // Rule [Refl]
            Primitive::Refl => {
                let (a, ty) = self.infer(ctx, &args[0])?;
                let level = self.sort_of(ctx, &ty, args[0].span)?;
                self.relevant(ctx, &ty, &level, args[0].span)?;
                let a_val = self.eval(ctx, &a);
                (Term::Refl(Rc::new(a)), eq(&self.sig, level, ty, a_val.clone(), a_val))
            }
            // Rule [Transport]
            Primitive::Transp => {
                let (t, ty) = self.infer(ctx, &args[0])?;
                let level = self.sort_of(ctx, &ty, args[0].span)?;
                self.relevant(ctx, &ty, &level, args[0].span)?;
                let motive_ty = Val::Pi(Rc::new(BindingVal {
                    name: "_".into(),
                    dom: ty.clone(),
                    cod: Closure::Native(Rc::new(|_, _| Val::Sort(Level::Zero))),
                    dom_level: level.clone(),
                    cod_level: Level::constant(1),
                }));
                let motive = self.check(ctx, &args[1], &motive_ty)?;
                let motive_val = self.eval(ctx, &motive);
                let t_val = self.eval(ctx, &t);
                let proof = self.check(ctx, &args[2], &apply(&self.sig, motive_val.clone(), t_val.clone()))?;
                let t2 = self.check(ctx, &args[3], &ty)?;
                let t2_val = self.eval(ctx, &t2);
                let e = self.check(ctx, &args[4], &eq(&self.sig, level, ty, t_val, t2_val.clone()))?;
                let term = Term::Transp(Rc::new([t, motive, proof, t2, e].map(Rc::new)));
                (term, apply(&self.sig, motive_val, t2_val))
            }
            // Rule [Cast]
            Primitive::Cast => {
                let (from, level) = self.check_type(ctx, &args[0])?;
                let universe = Val::Sort(level.clone());
                let to = self.check(ctx, &args[1], &universe)?;
                let (from_val, to_val) = (self.eval(ctx, &from), self.eval(ctx, &to));
                let along = eq(&self.sig, level.succ(), universe, from_val.clone(), to_val.clone());
                let proof = self.check(ctx, &args[2], &along)?;
                let value = self.check(ctx, &args[3], &from_val)?;
                let term = Term::Cast(Rc::new(from), Rc::new(to), Rc::new(proof), Rc::new(value));
                (term, to_val)
            }
            Primitive::Quot => self.infer_quotient(ctx, args)?,
            Primitive::QIn => {
                return Err(self.error(
                    Code::TypeAnnotationRequired,
                    args[0].span,
                    "cannot infer which quotient this class belongs to; annotate it as `(@qin a : Q)`",
                ))
            }
            Primitive::QElim => self.infer_quotient_elim(ctx, args)?,
        })
    }

    // Rule [Quot-Form]
    fn infer_quotient(&self, ctx: &mut Context, args: &[Raw]) -> Result<(Term, Val)> {
        let (carrier, level) = self.check_type(ctx, &args[0])?;
        if !level.is_nonzero() {
            return Err(self.error(Code::Unsupported, args[0].span, "only data can be quotiented, not a proposition"));
        }
        let a = self.eval(ctx, &carrier);
        let relation = self.check(ctx, &args[1], &relation_type(a.clone(), level.clone()))?;
        let r = self.eval(ctx, &relation);
        let [reflexive, symmetric, transitive] = equivalence_laws(&a, &r, &level);
        let proofs = [
            self.check(ctx, &args[2], &reflexive)?,
            self.check(ctx, &args[3], &symmetric)?,
            self.check(ctx, &args[4], &transitive)?,
        ];

        let term = Term::Quot(Rc::new(carrier), Rc::new(relation), level.clone(), Rc::new(proofs.map(Rc::new)));
        Ok((term, Val::Sort(level)))
    }

    // Rule [Quot-Elim]
    fn infer_quotient_elim(&self, ctx: &mut Context, args: &[Raw]) -> Result<(Term, Val)> {
        let (q, q_ty) = self.infer(ctx, &args[3])?;
        let Val::Quot(quot) = q_ty.force(&self.sig) else {
            return Err(self.error(
                Code::TypeMismatch,
                args[3].span,
                format!("eliminated a value of type `{}`, which is not a quotient", self.show(ctx, &q_ty)),
            ));
        };
        let (motive, level) = self.infer_motive(ctx, &args[0], &q_ty, &quot.level)?;
        let p = self.eval(ctx, &motive);

        // (x: A) -> P (@qin x)
        let p1 = p.clone();
        let method_ty = native_pi("x", quot.carrier.clone(), quot.level.clone(), level.clone(), move |sig, x| {
            apply(sig, p1.clone(), Val::QIn(Rc::new(x)))
        });
        let method = self.check(ctx, &args[1], &method_ty)?;
        let f = self.eval(ctx, &method);

        // (x y: A) -> R x y -> @cast (P (@qin x)) (P (@qin y)) _ (f x) ~ f y
        let respects = respect_type(quot.clone(), p.clone(), f.clone(), level.clone());
        let respect = self.check(ctx, &args[2], &respects)?;

        let ty = apply(&self.sig, p, self.eval(ctx, &q));
        Ok((Term::QElim(Rc::new(motive), Rc::new(method), Rc::new(respect), level, Rc::new(q)), ty))
    }

    /// A motive `P : dom -> @Type m`, with its sort `m`. A lambda is checked
    /// against the domain and its body's sort read off; anything else must
    /// have a Pi type over `dom`.
    fn infer_motive(&self, ctx: &mut Context, raw: &Raw, dom: &Val, dom_level: &Level) -> Result<(Term, Level)> {
        if let RawKind::Lam(name, ann, body) = &raw.kind {
            let written = match ann {
                Some(ann) => {
                    let (t, _) = self.check_type(ctx, ann)?;
                    let given = self.eval(ctx, &t);
                    if !self.conversion(ctx).conv_type(&given, dom) {
                        return Err(self.mismatch(ctx, ann.span, dom, &given));
                    }
                    Some(Rc::new(t))
                }
                None => None,
            };
            let (body, level) = self.under(ctx, name, dom.clone(), |c, ctx| c.check_type(ctx, body))?;
            return Ok((Term::Lam(name.clone(), written, Rc::new(body)), level));
        }
        let (t, ty) = self.infer(ctx, raw)?;
        if let Val::Pi(pi) = ty.force(&self.sig) {
            let cod = pi.cod.apply(&self.sig, Val::var(ctx.depth()));
            if let Val::Sort(level) = cod.force(&self.sig).clone() {
                if self.conversion(ctx).conv_type(&pi.dom, dom) {
                    return Ok((t, level));
                }
            }
        }
        let expected = native_pi("_", dom.clone(), dom_level.clone(), Level::constant(1), |_, _| Val::Sort(Level::Zero));
        Err(self.error(
            Code::TypeMismatch,
            raw.span,
            format!("expected a motive over `{}`, found `{}`", self.show(ctx, dom), self.show(ctx, &ty)),
        )
        .with_note(format!("a motive has a type like `{}`", self.show(ctx, &expected))))
    }

    /// The type and value of `let x: ann = val`.
    fn let_binding(&self, ctx: &mut Context, ann: Option<&Raw>, val: &Raw) -> Result<(Term, Term)> {
        match ann {
            Some(ann) => {
                let (ty, _) = self.check_type(ctx, ann)?;
                let ty_val = self.eval(ctx, &ty);
                Ok((ty, self.check(ctx, val, &ty_val)?))
            }
            None => {
                let (val, ty) = self.infer(ctx, val)?;
                Ok((quote(&self.sig, ctx.depth(), &ty), val))
            }
        }
    }

    /// `D.Tag.{ fields }` as the application it stands for: the global
    /// `D.Tag` applied to `_` for each uniform parameter of `D`, which the
    /// spine infers, then to the fields in order. `.Tag` names the one
    /// constructor so tagged.
    fn constructor_spine(&self, raw: &Raw) -> Result<Raw> {
        let RawKind::Ctor { data, tag, fields } = &raw.kind else { unreachable!("a constructor") };
        let is_ctor = |id: &GlobalId| matches!(self.sig.global(*id).kind, GlobalKind::Constructor(..));
        let id = match data {
            Some(d) => self.sig.lookup(&format!("{d}.{tag}")).filter(is_ctor).ok_or_else(|| {
                self.error(Code::UnknownSymbol, raw.span, format!("`{d}` has no constructor `{tag}`"))
            })?,
            None => {
                let suffix = format!(".{tag}");
                let mut found: Vec<GlobalId> = (0..self.sig.len() as GlobalId)
                    .filter(|id| is_ctor(id) && self.sig.global(*id).name.ends_with(&suffix))
                    .collect();
                // The script's own constructors come before the prelude's.
                if found.iter().any(|id| !self.sig.is_prelude(*id)) {
                    found.retain(|id| !self.sig.is_prelude(*id));
                }
                match found.as_slice() {
                    [id] => *id,
                    [] => return Err(self.error(Code::UnknownSymbol, raw.span, format!("no constructor is tagged `{tag}`"))),
                    [a, b, ..] => {
                        return Err(self.error(
                            Code::AmbiguousName,
                            raw.span,
                            format!("`.{tag}` names both `{}` and `{}`; write the type, as in `{}`", self.sig.global(*a).name, self.sig.global(*b).name, self.sig.global(*a).name),
                        ))
                    }
                }
            }
        };
        let GlobalKind::Constructor(data_id, index) = self.sig.global(id).kind else { unreachable!("a constructor") };
        let decl = self.sig.data(data_id);
        let surface = &decl.constructors[index].surface;
        let name = &self.sig.global(id).name;
        if fields.len() != surface.len() {
            return Err(self.error(
                Code::TypeMismatch,
                raw.span,
                format!("`{name}` has {} field(s), given {}", surface.len(), fields.len()),
            ));
        }
        let mut ordered: Vec<Option<&Raw>> = vec![None; surface.len()];
        for (i, (field, value)) in fields.iter().enumerate() {
            let at = match field {
                None => i,
                Some(f) => surface.iter().position(|p| p.name == *f).ok_or_else(|| {
                    self.error(Code::UnknownSymbol, value.span, format!("`{name}` has no field `{f}`"))
                })?,
            };
            if ordered[at].replace(value).is_some() {
                return Err(self.error(Code::DuplicateSymbol, value.span, format!("field `{}` of `{name}` is given twice", surface[at].name)));
            }
        }
        let span = raw.span;
        let head = Raw { kind: RawKind::Var(name.clone(), Vec::new()), span };
        let holes = (0..decl.uniform).map(|_| Raw { kind: RawKind::Hole, span });
        let args = holes.chain(ordered.into_iter().map(|f| f.expect("every field is given").clone()));
        Ok(args.fold(head, |f, a| Raw { kind: RawKind::App(Box::new(f), Box::new(a)), span }))
    }

    fn infer_var(&self, ctx: &mut Context, span: Span, name: &Name, level_args: &[LevelArg]) -> Result<(Term, Val)> {
        if let Some(level) = ctx.names.iter().rposition(|n| n == name) {
            if let Some(arg) = level_args.first() {
                return Err(self.error(Code::TypeMismatch, arg.span, format!("`{name}` is a local variable and takes no levels")));
            }
            let ix = ctx.depth() - 1 - level as Lvl;
            return Ok((Term::Var(ix), ctx.types[level].clone()));
        }
        let Some(id) = self.sig.lookup(name) else {
            let locals = ctx.names.iter().map(|n| &**n);
            let mut err = self.error(Code::UnknownSymbol, span, format!("unknown name `{name}`"));
            if let Some(near) = closest(name, locals.chain(self.sig.visible_names())) {
                err = err.with_help(format!("did you mean `{near}`?"));
            }
            return Err(err);
        };
        // A global with a level left out is an open spine, which infers it.
        let levels = self.level_args(ctx, name, id, level_args)?;
        // Rule [Level-Polymorphism]
        let levels: Rc<[Level]> = levels.into_iter().map(|l| l.expect("every level is given")).collect();
        let ty = global_type(&self.sig, id, levels.clone());
        Ok((Term::Global(id, levels), ty))
    }

    /// The levels `@ctx {.u = l}` gives global `id`, by parameter, `None`
    /// where left out.
    fn level_args(&self, ctx: &Context, name: &str, id: GlobalId, level_args: &[LevelArg]) -> Result<Vec<Option<Level>>> {
        let params = &self.sig.global(id).level_params;
        let mut levels: Vec<Option<Level>> = vec![None; params.len()];
        for arg in level_args {
            let Some(i) = params.iter().position(|p| *p == arg.name) else {
                return Err(self.error(Code::UnknownSymbol, arg.span, format!("`{name}` has no level `{}`", arg.name)));
            };
            if levels[i].is_some() {
                return Err(self.error(Code::DuplicateSymbol, arg.span, format!("level `{}` is given twice", arg.name)));
            }
            levels[i] = Some(self.level(ctx, &arg.level)?);
        }
        Ok(levels)
    }

    fn level(&self, ctx: &Context, raw: &RawLevel) -> Result<Level> {
        Ok(match raw {
            RawLevel::Num(n) => Level::constant(*n),
            RawLevel::Name(name, span) => match ctx.level_names.iter().position(|n| n == name) {
                Some(i) => Level::Param(i as u32),
                None => {
                    let mut err = self.error(Code::UnknownSymbol, *span, format!("unknown level `{name}`"));
                    if let Some(near) = closest(name, ctx.level_names.iter().map(|n| &**n)) {
                        err = err.with_help(format!("did you mean `{near}`?"));
                    }
                    return Err(err);
                }
            },
            RawLevel::Plus(l, n) => (0..*n).fold(self.level(ctx, l)?, |l, _| l.succ()),
            RawLevel::Max(a, b) => Level::max(&self.level(ctx, a)?, &self.level(ctx, b)?),
            RawLevel::IMax(a, b) => Level::imax(&self.level(ctx, a)?, &self.level(ctx, b)?),
        })
    }
}

// Note [Booleans as propositions]
//
// A boolean where a type is expected is the proposition `b ~ true`, as in
// SSReflect, where `is_true b` is the coercion from `bool` to `Prop`, and as
// the frontend reads it (#539). The checker writes the equality out, so the
// elaborated term is an ordinary `Eq` at the prelude's `Bool` and the
// re-check and the computation rules never see a boolean in a type: the rule
// is notation over Eq-Form. A comparison computes by the recursors of the
// prelude's `@Nat`, so `3 < 10` is `true ~ true`, which is `@Top`, and
// `30 < 10` is `false ~ true`, which is `@Bottom`. With a variable,
// `n < 10 ~ true` is stuck until `n` is known, and a proof of it is a
// hypothesis, or an induction over `n` (See Rule [Data-Elim]).
// Only the prelude's `Bool` is read so: a script's own boolean type is
// data, not notation.

// Note [Equality is not formed at a proposition]
//
// TT^obs and CC^obs form `t ~ u` only at a type in a relevant universe (PT22
// and PT23 Fig. 2, Eq-Form), and so do `@refl` and `@transp`: two proofs are
// equal by conversion, so the equality would say nothing. A type whose
// universe is a level parameter that may be `0` is allowed, and its equality
// stays stuck until the level is known. Equality still meets proofs inside
// data, as the second component of a pair or a field of a constructor; there
// it is `{}`, as for a Box type.
// See Rule [Eq-Box].

mod spine;

#[cfg(test)]
pub(crate) mod tests;
