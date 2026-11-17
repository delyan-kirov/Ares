//! Re-checking a signature from its core terms alone.
//!
//! The elaborator in [`crate::check`] reads script syntax, resolves names and
//! builds the [`Signature`]. This module checks the result again without any
//! of that: every global's type is a type, every definition's body has its
//! type, and every inductive declaration is well formed and its generated
//! globals are the ones its declaration gives. It shares the evaluator, the
//! conversion checker and the computation rules with the elaborator (they
//! are the theory), but not the elaborator's own code.
//!
//! The terms carry what checking needs: proofs are kept (wrapped in
//! [`Term::Proof`] where the elaborator checked them against a proposition,
//! and never evaluated), a lambda in a position that infers its type keeps
//! its domain, and an annotation stays a [`Term::Ann`]. A read-back
//! [`Term::Irrelevant`] carries no proof and is rejected, except where a
//! term only records something the checker computes itself (the type of an
//! equality or of a `let` whose value infers its own), which is compared by
//! conversion instead of checked.
//! See Note [Proofs evaluate to an irrelevant witness].
//!
//! Input: a signature. Output: nothing, or the first global that fails.
//!
//! Entry point: [`recheck`].

use std::fmt;
use std::rc::Rc;

use crate::check::{equivalence_laws, is_recursive_field, respect_type};
use crate::conversion::ConversionChecker;
use crate::inductive::{constructor_type, ford, projection_type, recursor_type};
use crate::level::Level;
use crate::nbe::{apply, eval, fst, global_type, quote, BindingVal, Closure, Env, Lvl, Val};
use crate::observational::{eq, native_pi, relation_type};
use crate::signature::{DataId, GlobalId, GlobalKind, Param, Signature};
use crate::term::{mentions, mentions_global, rename, Binding, Name, Term, TermDisplay};

/// Why a global failed to re-check.
#[derive(Debug)]
pub struct RecheckError {
    pub global: String,
    pub message: String,
}

impl fmt::Display for RecheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "`{}`: {}", self.global, self.message)
    }
}

type Result<T> = std::result::Result<T, String>;

/// Re-check every global of `sig`, in order.
pub fn recheck(sig: &Signature) -> std::result::Result<(), RecheckError> {
    for id in 0..sig.len() as GlobalId {
        let checker = Rechecker { sig, current: id };
        checker.global(id).map_err(|message| RecheckError {
            global: sig.global(id).name.to_string(),
            message,
        })?;
    }
    Ok(())
}

struct Rechecker<'s> {
    sig: &'s Signature,
    /// The global being re-checked: it may name only the globals before it.
    current: GlobalId,
}

/// The variables in scope, outermost first.
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

    fn bind(&mut self, name: Name, ty: Val) {
        self.env = self.env.extend(Val::var(self.depth()));
        self.names.push(name);
        self.types.push(ty);
    }
}

/// Whether a term synthesises its type: a lambda without its domain, a pair
/// and a class need one pushed in.
fn inferable(t: &Term) -> bool {
    match t {
        Term::Lam(_, None, _) | Term::Pair(..) | Term::QIn(_) => false,
        Term::Lam(_, Some(_), body) | Term::Let(_, _, _, body) | Term::Proof(body) => inferable(body),
        _ => true,
    }
}

/// Whether `l` names only the first `count` level parameters.
fn level_in_scope(l: &Level, count: usize) -> bool {
    match l {
        Level::Zero => true,
        Level::Succ(l) => level_in_scope(l, count),
        Level::Max(a, b) | Level::IMax(a, b) => level_in_scope(a, count) && level_in_scope(b, count),
        Level::Param(p) => (*p as usize) < count,
    }
}

fn same_params(a: &[Param], b: &[Param]) -> bool {
    a.len() == b.len() && a.iter().zip(b).all(|(x, y)| x.name == y.name && x.ty == y.ty && x.level.equal(&y.level))
}

// ## Globals

impl Rechecker<'_> {
    fn global(&self, id: GlobalId) -> Result<()> {
        let global = self.sig.global(id);
        let mut ctx = Context::new(global.level_params.clone());
        match &global.kind {
            GlobalKind::Definition(body) => {
                self.check_type(&mut ctx, &global.ty)?;
                let expected = self.eval(&ctx, &global.ty);
                self.check(&mut ctx, body, &expected)
            }
            GlobalKind::Axiom => self.check_type(&mut ctx, &global.ty).map(|_| ()),
            GlobalKind::Data(data) => self.data(&mut ctx, id, *data),
            GlobalKind::Constructor(data, index) => self.constructor(&mut ctx, id, *data, *index),
            GlobalKind::Recursor(data) => {
                let decl = self.sig.data(*data);
                let former = self.former(id, *data)?;
                if decl.recursor != id || global.level_params.len() != former + 1 {
                    return Err("is not the recursor its declaration names".into());
                }
                self.generated(&global.ty, recursor_type(decl, former))
            }
            GlobalKind::Projection(data, index, field) => {
                let decl = self.sig.data(*data);
                let former = self.former(id, *data)?;
                let fields = decl.constructors.get(*index).map_or(0, |c| c.fields.len());
                if decl.params.is_empty() || *field >= fields || global.level_params.len() != former {
                    return Err("is not a projection its declaration has".into());
                }
                self.generated(&global.ty, projection_type(decl, former, *index, *field))
            }
        }
    }

    /// The number of level parameters of `data`'s type former, which must
    /// come before global `id`.
    fn former(&self, id: GlobalId, data: DataId) -> Result<usize> {
        let decl = self.sig.data(data);
        if decl.global >= id || !matches!(self.sig.global(decl.global).kind, GlobalKind::Data(d) if d == data) {
            return Err("belongs to an inductive type declared after it".into());
        }
        Ok(self.sig.global(decl.global).level_params.len())
    }

    /// A generated global's type must be the one its declaration gives.
    fn generated(&self, stored: &Term, expected: Term) -> Result<()> {
        if *stored != expected {
            return Err("has a type its declaration does not give".into());
        }
        Ok(())
    }

    // Rule [Data-Form]
    fn data(&self, ctx: &mut Context, id: GlobalId, data: DataId) -> Result<()> {
        let decl = self.sig.data(data);
        let global = self.sig.global(id);
        if decl.global != id {
            return Err("is not the type former its declaration names".into());
        }
        self.check_type(ctx, &global.ty)?;
        let mut params = Vec::new();
        let mut result = &*global.ty;
        while let Term::Pi(b) = result {
            params.push(Param {
                name: b.name.clone(),
                ty: b.dom.clone(),
                level: b.dom_level.clone(),
            });
            result = &b.cod;
        }
        if !matches!(result, Term::Sort(l) if l.equal(&decl.level)) || !same_params(&params, &decl.params) {
            return Err("has a type that is not its declaration's parameters and sort".into());
        }
        if !decl.level.is_nonzero() {
            return Err("is an inductive proposition".into());
        }
        if decl.uniform > params.len() {
            return Err("has more uniform parameters than parameters".into());
        }
        for (i, index) in params[decl.uniform..].iter().enumerate() {
            if (0..i as u32).any(|v| mentions(&index.ty, v)) || !index.level.is_nonzero() {
                return Err(format!("has an index `{}` that depends on an earlier index or is a proof", index.name));
            }
        }
        for (index, c) in decl.constructors.iter().enumerate() {
            let owned = (c.global as usize) < self.sig.len() && matches!(self.sig.global(c.global).kind, GlobalKind::Constructor(d, i) if d == data && i == index);
            if !owned {
                return Err(format!("has a constructor `{}` that is not its global", c.name));
            }
        }
        let recursor = decl.recursor;
        if (recursor as usize) >= self.sig.len() || !matches!(self.sig.global(recursor).kind, GlobalKind::Recursor(d) if d == data) {
            return Err("has no recursor".into());
        }
        Ok(())
    }

    fn constructor(&self, ctx: &mut Context, id: GlobalId, data: DataId, index: usize) -> Result<()> {
        let decl = self.sig.data(data);
        let former = self.former(id, data)?;
        let Some(ctor) = decl.constructors.get(index) else {
            return Err("is a constructor its declaration does not have".into());
        };
        if ctor.global != id || self.sig.global(id).level_params.len() != former {
            return Err("is not the constructor its declaration names".into());
        }
        let (np, u) = (decl.params.len(), decl.uniform);
        for p in &decl.params[..u] {
            let ty = self.eval(ctx, &p.ty);
            ctx.bind(p.name.clone(), ty);
        }
        let mut recursive = Vec::new();
        for (f, field) in ctor.surface.iter().enumerate() {
            let level = self.check_type(ctx, &field.ty)?;
            if !level.equal(&field.level) || !level.leq(&decl.level) {
                return Err(format!("has a field `{}` too large for its type's universe", field.name));
            }
            let ty = self.eval(ctx, &field.ty);
            // Rule [Positivity-Restricted]
            // See Note [Strict positivity, restricted].
            let is_self = is_recursive_field(&field.ty, decl.global, np, u, (u + f) as u32);
            if !is_self && mentions_global(&field.ty, decl.global) {
                return Err(format!("has a field `{}` where its type occurs other than as a field's result", field.name));
            }
            recursive.push(is_self);
            ctx.bind(field.name.clone(), ty);
        }
        if ctor.indices.len() != np - u {
            return Err("states the wrong number of indices".into());
        }
        let nf = ctor.surface.len() as u32;
        for (i, y) in ctor.indices.iter().enumerate() {
            // The index's type mentions only the uniform parameters, so it
            // moves past the earlier indices and over the fields.
            let i32_ = i as u32;
            let ty = rename(&decl.params[u + i].ty, 0, &|v| v - i32_ + nf);
            let ty = self.eval(ctx, &ty);
            self.check(ctx, y, &ty)?;
        }
        let (fields, recursive) = ford(decl, &ctor.surface, recursive, &ctor.indices);
        if !same_params(&fields, &ctor.fields) || recursive != ctor.recursive {
            return Err("has forded fields its written fields do not give".into());
        }
        self.generated(&self.sig.global(id).ty, constructor_type(decl, former, index))
    }
}

// ## Terms

impl Rechecker<'_> {
    fn conversion<'a>(&'a self, ctx: &'a mut Context) -> ConversionChecker<'a> {
        ConversionChecker {
            sig: self.sig,
            types: &mut ctx.types,
        }
    }

    fn eval(&self, ctx: &Context, t: &Term) -> Val {
        eval(self.sig, &ctx.env, t)
    }

    fn show(&self, ctx: &Context, v: &Val) -> String {
        let term = quote(self.sig, ctx.depth(), v);
        TermDisplay {
            sig: self.sig,
            names: &ctx.names,
            level_names: &ctx.level_names,
            term: &term,
        }
        .to_string()
    }

    /// Types print folded, each followed by its head unfolded when that reads
    /// differently. See Note [Glued evaluation].
    fn mismatch(&self, ctx: &Context, expected: &Val, found: &Val) -> String {
        let shown = |v: &Val| {
            let (folded, head) = (self.show(ctx, v), self.show(ctx, v.force(self.sig)));
            if folded == head {
                format!("`{folded}`")
            } else {
                format!("`{folded}` (which computes to `{head}`)")
            }
        };
        format!("expected {}, found {}", shown(expected), shown(found))
    }

    fn level(&self, ctx: &Context, l: &Level) -> Result<()> {
        if !level_in_scope(l, ctx.level_names.len()) {
            return Err("names a level parameter it does not have".into());
        }
        Ok(())
    }

    fn under<R>(&self, ctx: &mut Context, name: &Name, ty: Val, k: impl FnOnce(&Self, &mut Context) -> R) -> R {
        let env = ctx.env.clone();
        ctx.bind(name.clone(), ty);
        let r = k(self, ctx);
        ctx.names.pop();
        ctx.types.pop();
        ctx.env = env;
        r
    }

    fn check_type(&self, ctx: &mut Context, t: &Term) -> Result<Level> {
        match self.infer(ctx, t)?.force(self.sig).clone() {
            Val::Sort(l) => Ok(l),
            other => Err(format!("expected a type, found a value of type `{}`", self.show(ctx, &other))),
        }
    }

    // Algorithm [Bidirectional checking]
    fn check(&self, ctx: &mut Context, t: &Term, expected: &Val) -> Result<()> {
        match (t, expected.force(self.sig)) {
            // Rule [Proof-Witness]
            (Term::Proof(p), _) => {
                if !self.conversion(ctx).is_proposition(expected) {
                    return Err(format!("a proof stands where `{}`, which is not a proposition, is expected", self.show(ctx, expected)));
                }
                self.check(ctx, p, expected)
            }
            (Term::Lam(name, dom, body), Val::Pi(pi)) => {
                if let Some(dom) = dom {
                    self.check_type(ctx, dom)?;
                    let given = self.eval(ctx, dom);
                    if !self.conversion(ctx).conv_type(&given, &pi.dom) {
                        return Err(self.mismatch(ctx, &pi.dom, &given));
                    }
                }
                self.under(ctx, name, pi.dom.clone(), |c, ctx| {
                    let cod = pi.cod.apply(c.sig, Val::var(ctx.depth() - 1));
                    c.check(ctx, body, &cod)
                })
            }
            (Term::Pair(a, b), Val::Sigma(sigma)) => {
                self.check(ctx, a, &sigma.dom)?;
                let cod = sigma.cod.apply(self.sig, self.eval(ctx, a));
                self.check(ctx, b, &cod)
            }
            (Term::QIn(a), Val::Quot(q)) => self.check(ctx, a, &q.carrier),
            (Term::Let(name, ty, val, body), _) => {
                let ty = self.let_type(ctx, ty, val)?;
                let val = self.eval(ctx, val);
                self.define(ctx, name, ty, val, |c, ctx| c.check(ctx, body, expected))
            }
            (Term::Lam(..) | Term::Pair(..) | Term::QIn(_), _) => {
                Err(format!("a lambda, pair or class stands where `{}` is expected", self.show(ctx, expected)))
            }
            _ => {
                let found = self.infer(ctx, t)?;
                if self.conversion(ctx).conv_type(&found, expected) {
                    Ok(())
                } else {
                    Err(self.mismatch(ctx, expected, &found))
                }
            }
        }
    }

    fn define<R>(&self, ctx: &mut Context, name: &Name, ty: Val, val: Val, k: impl FnOnce(&Self, &mut Context) -> R) -> R {
        let env = ctx.env.clone();
        ctx.env = ctx.env.extend(val);
        ctx.names.push(name.clone());
        ctx.types.push(ty);
        let r = k(self, ctx);
        ctx.names.pop();
        ctx.types.pop();
        ctx.env = env;
        r
    }

    /// The type of `let x: ty = val`. A value that infers its type is
    /// compared with `ty` by conversion (the elaborator may have read `ty`
    /// back from that type); otherwise `ty` was written and is checked.
    fn let_type(&self, ctx: &mut Context, ty: &Term, val: &Term) -> Result<Val> {
        if inferable(val) {
            let found = self.infer(ctx, val)?;
            let written = self.eval(ctx, ty);
            if !self.conversion(ctx).conv_type(&found, &written) {
                return Err(self.mismatch(ctx, &written, &found));
            }
            return Ok(found);
        }
        self.check_type(ctx, ty)?;
        let ty = self.eval(ctx, ty);
        self.check(ctx, val, &ty)?;
        Ok(ty)
    }

    /// The sort of `ty`, which must not be a proposition: equality is not
    /// formed at one.
    /// See Note [Equality is not formed at a proposition].
    fn relevant_sort(&self, ctx: &mut Context, ty: &Val) -> Result<Level> {
        let Some(level) = self.conversion(ctx).sort_of(ty) else {
            return Err(format!("cannot tell which universe `{}` lives in", self.show(ctx, ty)));
        };
        if level.is_zero() {
            return Err(format!("equality is not formed at the proposition `{}`", self.show(ctx, ty)));
        }
        Ok(level)
    }

    fn binding(&self, ctx: &mut Context, b: &Binding) -> Result<()> {
        self.level(ctx, &b.dom_level)?;
        self.level(ctx, &b.cod_level)?;
        let dom = self.check_type(ctx, &b.dom)?;
        let dom_val = self.eval(ctx, &b.dom);
        let cod = self.under(ctx, &b.name, dom_val, |c, ctx| c.check_type(ctx, &b.cod))?;
        if !dom.equal(&b.dom_level) || !cod.equal(&b.cod_level) {
            return Err(format!("records the wrong sorts for the sides of a binder over `{}`", b.name));
        }
        Ok(())
    }

    fn infer(&self, ctx: &mut Context, t: &Term) -> Result<Val> {
        match t {
            Term::Var(ix) => match (ctx.depth() as usize).checked_sub(*ix as usize + 1) {
                Some(level) => Ok(ctx.types[level].clone()),
                None => Err(format!("variable #{ix} is not in scope")),
            },
            Term::Global(id, levels) => {
                if *id >= self.current {
                    return Err(format!("names global #{id}, which is not declared before it"));
                }
                if levels.len() != self.sig.global(*id).level_params.len() {
                    return Err(format!("instantiates `{}` at the wrong number of levels", self.sig.global(*id).name));
                }
                for l in levels.iter() {
                    self.level(ctx, l)?;
                }
                Ok(global_type(self.sig, *id, levels.clone()))
            }
            Term::Sort(l) => {
                self.level(ctx, l)?;
                Ok(Val::Sort(l.succ()))
            }
            Term::Pi(b) => {
                self.binding(ctx, b)?;
                Ok(Val::Sort(Level::imax(&b.dom_level, &b.cod_level)))
            }
            Term::Sigma(b) => {
                self.binding(ctx, b)?;
                Ok(Val::Sort(Level::max(&b.dom_level, &b.cod_level)))
            }
            Term::Lam(name, Some(dom), body) => {
                let dom_level = self.check_type(ctx, dom)?;
                let dom_val = self.eval(ctx, dom);
                let (cod, cod_level) = self.under(ctx, name, dom_val.clone(), |c, ctx| {
                    let cod = c.infer(ctx, body)?;
                    let level = c.conversion(ctx).sort_of(&cod);
                    Ok::<_, String>((quote(c.sig, ctx.depth(), &cod), level))
                })?;
                let Some(cod_level) = cod_level else {
                    return Err("cannot tell the sort of a lambda's result".into());
                };
                Ok(Val::Pi(Rc::new(BindingVal {
                    name: name.clone(),
                    dom: dom_val,
                    cod: Closure::Term(ctx.env.clone(), Rc::new(cod)),
                    dom_level,
                    cod_level,
                })))
            }
            Term::Lam(..) | Term::Pair(..) | Term::QIn(_) => Err("cannot infer the type of a lambda, pair or class".into()),
            Term::App(f, a) => {
                let f_ty = self.infer(ctx, f)?;
                let Val::Pi(pi) = f_ty.force(self.sig) else {
                    return Err(format!("applies a value of type `{}`, which is not a function", self.show(ctx, &f_ty)));
                };
                self.check(ctx, a, &pi.dom)?;
                Ok(pi.cod.apply(self.sig, self.eval(ctx, a)))
            }
            Term::Let(name, ty, val, body) => {
                let ty = self.let_type(ctx, ty, val)?;
                let val = self.eval(ctx, val);
                self.define(ctx, name, ty, val, |c, ctx| c.infer(ctx, body))
            }
            Term::Fst(e) | Term::Snd(e) => {
                let ty = self.infer(ctx, e)?;
                let Val::Sigma(sigma) = ty.force(self.sig) else {
                    return Err(format!("projects from a value of type `{}`, which is not a pair", self.show(ctx, &ty)));
                };
                if matches!(t, Term::Fst(_)) {
                    Ok(sigma.dom.clone())
                } else {
                    Ok(sigma.cod.apply(self.sig, fst(self.sig, self.eval(ctx, e))))
                }
            }
            Term::Top | Term::Bottom => Ok(Val::Sort(Level::Zero)),
            Term::Tt => Ok(Val::Top),
            Term::Absurd(ty, e) => {
                self.check_type(ctx, ty)?;
                self.check(ctx, e, &Val::Bottom)?;
                Ok(self.eval(ctx, ty))
            }
            Term::Eq(level, ty, a, b) => {
                self.level(ctx, level)?;
                let ty_val = if inferable(a) {
                    let found = self.infer(ctx, a)?;
                    let written = self.eval(ctx, ty);
                    if !self.conversion(ctx).conv_type(&found, &written) {
                        return Err(self.mismatch(ctx, &written, &found));
                    }
                    found
                } else {
                    self.check_type(ctx, ty)?;
                    let ty_val = self.eval(ctx, ty);
                    self.check(ctx, a, &ty_val)?;
                    ty_val
                };
                if !self.relevant_sort(ctx, &ty_val)?.equal(level) {
                    return Err("records the wrong sort for an equality's type".into());
                }
                self.check(ctx, b, &ty_val)?;
                Ok(Val::Sort(Level::Zero))
            }
            Term::Refl(a) => {
                let ty = self.infer(ctx, a)?;
                let level = self.relevant_sort(ctx, &ty)?;
                let a = self.eval(ctx, a);
                Ok(eq(self.sig, level, ty, a.clone(), a))
            }
            Term::Transp(args) => {
                let [t, motive, proof, t2, e] = &**args;
                let ty = self.infer(ctx, t)?;
                let level = self.relevant_sort(ctx, &ty)?;
                let motive_ty = native_pi("_", ty.clone(), level.clone(), Level::constant(1), |_, _| Val::Sort(Level::Zero));
                self.check(ctx, motive, &motive_ty)?;
                let motive = self.eval(ctx, motive);
                let t = self.eval(ctx, t);
                self.check(ctx, proof, &apply(self.sig, motive.clone(), t.clone()))?;
                self.check(ctx, t2, &ty)?;
                let t2 = self.eval(ctx, t2);
                self.check(ctx, e, &eq(self.sig, level, ty, t, t2.clone()))?;
                Ok(apply(self.sig, motive, t2))
            }
            Term::Cast(from, to, proof, value) => {
                let level = self.check_type(ctx, from)?;
                let universe = Val::Sort(level.clone());
                self.check(ctx, to, &universe)?;
                let (from, to) = (self.eval(ctx, from), self.eval(ctx, to));
                self.check(ctx, proof, &eq(self.sig, level.succ(), universe, from.clone(), to.clone()))?;
                self.check(ctx, value, &from)?;
                Ok(to)
            }
            Term::Quot(carrier, relation, level, proofs) => {
                self.level(ctx, level)?;
                if !self.check_type(ctx, carrier)?.equal(level) || !level.is_nonzero() {
                    return Err("quotients a proposition, or records the wrong sort for its carrier".into());
                }
                let a = self.eval(ctx, carrier);
                self.check(ctx, relation, &relation_type(a.clone(), level.clone()))?;
                let r = self.eval(ctx, relation);
                for (proof, law) in proofs.iter().zip(equivalence_laws(&a, &r, level)) {
                    self.check(ctx, proof, &law)?;
                }
                Ok(Val::Sort(level.clone()))
            }
            Term::QElim(motive, method, respect, level, q) => {
                self.level(ctx, level)?;
                let q_ty = self.infer(ctx, q)?;
                let Val::Quot(quot) = q_ty.force(self.sig) else {
                    return Err(format!("eliminates a value of type `{}`, which is not a quotient", self.show(ctx, &q_ty)));
                };
                let sort = level.clone();
                let motive_ty = native_pi("_", q_ty.clone(), quot.level.clone(), level.succ(), move |_, _| Val::Sort(sort.clone()));
                self.check(ctx, motive, &motive_ty)?;
                let p = self.eval(ctx, motive);
                let p1 = p.clone();
                let method_ty = native_pi("x", quot.carrier.clone(), quot.level.clone(), level.clone(), move |sig, x| {
                    apply(sig, p1.clone(), Val::QIn(Rc::new(x)))
                });
                self.check(ctx, method, &method_ty)?;
                let f = self.eval(ctx, method);
                self.check(ctx, respect, &respect_type(quot.clone(), p.clone(), f, level.clone()))?;
                Ok(apply(self.sig, p, self.eval(ctx, q)))
            }
            Term::Ann(e, ty) => {
                self.check_type(ctx, ty)?;
                let ty = self.eval(ctx, ty);
                self.check(ctx, e, &ty)?;
                Ok(ty)
            }
            Term::Proof(p) => {
                let ty = self.infer(ctx, p)?;
                if !self.conversion(ctx).is_proposition(&ty) {
                    return Err(format!("a proof has type `{}`, which is not a proposition", self.show(ctx, &ty)));
                }
                Ok(ty)
            }
            Term::Irrelevant => Err("contains an erased proof, which cannot be re-checked".into()),
        }
    }
}

#[cfg(test)]
mod tests;
