//! Normalisation by evaluation: terms evaluate to values in weak head normal
//! form, and values read back to terms.
//!
//! The algorithm is normalisation by evaluation (Berger and Schwichtenberg,
//! "An inverse of the evaluation functional for typed lambda-calculus", LICS
//! 1991), in the untyped, environment-machine form of Coquand's type checker
//! ("An algorithm for type-checking dependent types", SCP 1996). A binder's
//! body is a [`Closure`]: the term and the environment it was evaluated in,
//! or a Rust function when a computation rule builds the binder itself. A
//! variable that is not bound to a value is a de Bruijn *level* (0 is the
//! outermost binder), so values never need shifting. Elimination of a
//! variable is a [`Neutral`].
//!
//! [`eval`] substitutes the level arguments of the global being evaluated as
//! it goes, so a value's levels are always closed over the parameters of the
//! global being checked.
//!
//! A definition is not unfolded where it is evaluated: its application is a
//! [`Val::Unfold`], which keeps the global and its arguments and computes the
//! unfolding on demand ([`Val::force`]).
//! See Note [Glued evaluation].
//!
//! Input: a term and an environment. Output: its value; [`quote`] reads a
//! value back to a term at a context depth, keeping definitions folded, and
//! [`quote_unfolded`] reads it back to its normal form.
//!
//! Entry points: [`eval`], [`apply`], [`quote`], [`quote_unfolded`].

use std::cell::OnceCell;
use std::rc::Rc;

use crate::inductive::{canonical, constructor_value, data_value, numeral_value, recursor_value, ConstructorVal, DataVal, RecursorArgs};
use crate::level::Level;
use crate::observational::{cast, eq};
use crate::signature::{Computed, GlobalId, GlobalKind, Signature};
use crate::term::{Binding, Index, Name, Term};

/// A de Bruijn level: the number of binders outside a variable's own.
pub type Lvl = u32;

// ## Values

#[derive(Clone)]
pub enum Val {
    Neutral(Rc<Neutral>),
    Sort(Level),
    Pi(Rc<BindingVal>),
    Lam(Name, Closure),
    Sigma(Rc<BindingVal>),
    Pair(Rc<(Val, Val)>),
    Top,
    Tt,
    Bottom,
    Data(Rc<DataVal>),
    Constructor(Rc<ConstructorVal>),
    /// Any proof. See Note [Proofs evaluate to an irrelevant witness].
    Irrelevant,
    Quot(Rc<QuotVal>),
    QIn(Rc<Val>),
    /// A definition applied to arguments, not yet unfolded.
    Unfold(Rc<Unfold>),
    /// A numeral of the prelude's `@Nat`, its constructor chain unexpanded.
    /// See Rule [Nat-Literal].
    Nat(u64),
}

/// A definition applied to zero or more arguments, with its unfolding
/// computed the first time it is needed.
/// See Note [Glued evaluation].
pub struct Unfold {
    pub global: GlobalId,
    pub levels: Rc<[Level]>,
    /// The application this one extends and its last argument, or `None` for
    /// the definition itself.
    pub applied: Option<(Rc<Unfold>, Val)>,
    unfolded: OnceCell<Val>,
}

impl Unfold {
    fn new(global: GlobalId, levels: Rc<[Level]>, applied: Option<(Rc<Unfold>, Val)>) -> Unfold {
        Unfold {
            global,
            levels,
            applied,
            unfolded: OnceCell::new(),
        }
    }

    /// The value with the definition unfolded, which may itself be another
    /// definition's application.
    pub fn unfolded(&self, sig: &Signature) -> &Val {
        self.unfolded.get_or_init(|| match &self.applied {
            None => {
                let GlobalKind::Definition(body) = &sig.global(self.global).kind else {
                    unreachable!("only a definition is glued")
                };
                eval(sig, &Env::with_levels(self.levels.clone()), body)
            }
            Some((f, a)) => match self.computed(sig) {
                Some(v) => v,
                None => apply(sig, f.unfolded(sig).clone(), a.clone()),
            },
        })
    }

    // Rule [Nat-Literal]
    /// An arithmetic global of the prelude applied to numerals: its value,
    /// computed on the numbers. See Note [Numerals compute on numbers].
    fn computed(&self, sig: &Signature) -> Option<Val> {
        let builtins = sig.builtins()?;
        let op = builtins.arithmetic(self.global)?;
        let args = self.spine();
        if args.len() != op.arity() {
            return None;
        }
        let numbers: Vec<u64> = args.iter().map(|a| numeral_value(sig, a)).collect::<Option<_>>()?;
        Some(match op.compute(&numbers)? {
            Computed::Nat(n) => Val::Nat(n),
            Computed::Bool(b) => eval_global(sig, if b { builtins.true_ctor } else { builtins.false_ctor }, Rc::new([])),
        })
    }

    /// The arguments, first to last.
    pub fn spine(&self) -> Vec<Val> {
        let mut args = Vec::new();
        let mut at = self;
        while let Some((f, a)) = &at.applied {
            args.push(a.clone());
            at = f;
        }
        args.reverse();
        args
    }
}

/// A quotient type: a carrier in `@Type level` and an equivalence relation.
pub struct QuotVal {
    pub carrier: Val,
    pub relation: Val,
    pub level: Level,
}

/// A Pi or Sigma type's value, with the sorts of both sides.
pub struct BindingVal {
    pub name: Name,
    pub dom: Val,
    pub cod: Closure,
    pub dom_level: Level,
    pub cod_level: Level,
}

/// An elimination stuck on a variable or an axiom.
pub enum Neutral {
    Var(Lvl),
    Axiom(GlobalId, Rc<[Level]>),
    App(Rc<Neutral>, Val),
    Fst(Rc<Neutral>),
    Snd(Rc<Neutral>),
    /// `@absurd ty proof`, stuck because no proof of `@Bottom` is canonical.
    Absurd(Val, Val),
    /// A recursor stuck on its major premise.
    Recursor(Rc<RecursorArgs>, Rc<Neutral>),
    /// An equality whose type or sides have no head its rules know.
    Eq { level: Level, ty: Val, a: Val, b: Val },
    /// A cast between types whose heads differ or are neutral.
    Cast { from: Val, to: Val, proof: Val, value: Val },
    /// A quotient eliminator stuck on its argument.
    QElim { motive: Val, method: Val, level: Level, quotient: Rc<Neutral> },
}

/// A binder's body, waiting for the value of its variable.
#[derive(Clone)]
pub enum Closure {
    Term(Env, Rc<Term>),
    Native(Rc<dyn Fn(&Signature, Val) -> Val>),
}

impl Closure {
    pub fn apply(&self, sig: &Signature, arg: Val) -> Val {
        match self {
            Closure::Term(env, body) => eval(sig, &env.extend(arg), body),
            Closure::Native(f) => f(sig, arg),
        }
    }
}

impl Val {
    pub fn var(level: Lvl) -> Val {
        Val::Neutral(Rc::new(Neutral::Var(level)))
    }

    pub fn neutral(n: Neutral) -> Val {
        Val::Neutral(Rc::new(n))
    }

    /// The value with every definition at its head unfolded: what the rules
    /// that look at a value's head see.
    pub fn force(&self, sig: &Signature) -> &Val {
        match self {
            Val::Unfold(u) => u.unfolded(sig).force(sig),
            v => v,
        }
    }
}

// ## Environments

/// The values of the bound variables, innermost first, and the level
/// arguments of the global being evaluated (`None` while checking a global,
/// whose parameters stay parameters).
#[derive(Clone, Default)]
pub struct Env {
    values: Option<Rc<EnvNode>>,
    levels: Option<Rc<[Level]>>,
}

struct EnvNode {
    head: Val,
    tail: Option<Rc<EnvNode>>,
}

impl Env {
    pub fn new() -> Env {
        Env::default()
    }

    pub fn with_levels(levels: Rc<[Level]>) -> Env {
        Env {
            values: None,
            levels: Some(levels),
        }
    }

    pub fn extend(&self, v: Val) -> Env {
        Env {
            values: Some(Rc::new(EnvNode {
                head: v,
                tail: self.values.clone(),
            })),
            levels: self.levels.clone(),
        }
    }

    fn lookup(&self, ix: Index) -> Val {
        let mut node = self.values.as_deref();
        for _ in 0..ix {
            node = node.expect("de Bruijn index out of scope").tail.as_deref();
        }
        node.expect("de Bruijn index out of scope").head.clone()
    }

    fn level(&self, l: &Level) -> Level {
        match &self.levels {
            Some(args) => l.instantiate(args),
            None => l.clone(),
        }
    }
}

// ## Evaluation

// Algorithm [Normalisation by evaluation]
pub fn eval(sig: &Signature, env: &Env, t: &Term) -> Val {
    match t {
        Term::Var(ix) => env.lookup(*ix),
        Term::Global(id, levels) => {
            let levels: Rc<[Level]> = levels.iter().map(|l| env.level(l)).collect();
            eval_global(sig, *id, levels)
        }
        Term::Sort(l) => Val::Sort(env.level(l)),
        Term::Pi(b) => Val::Pi(Rc::new(eval_binding(sig, env, b))),
        Term::Lam(name, _, body) => Val::Lam(name.clone(), Closure::Term(env.clone(), body.clone())),
        Term::App(f, a) => apply(sig, eval(sig, env, f), eval(sig, env, a)),
        // Rule [Let]
        Term::Let(_, _, val, body) => eval(sig, &env.extend(eval(sig, env, val)), body),
        Term::Sigma(b) => Val::Sigma(Rc::new(eval_binding(sig, env, b))),
        Term::Pair(a, b) => Val::Pair(Rc::new((eval(sig, env, a), eval(sig, env, b)))),
        Term::Fst(e) => fst(sig, eval(sig, env, e)),
        Term::Snd(e) => snd(sig, eval(sig, env, e)),
        Term::Top => Val::Top,
        Term::Tt => Val::Tt,
        Term::Bottom => Val::Bottom,
        Term::Absurd(ty, e) => Val::neutral(Neutral::Absurd(eval(sig, env, ty), eval(sig, env, e))),
        Term::Eq(level, ty, a, b) => eq(sig, env.level(level), eval(sig, env, ty), eval(sig, env, a), eval(sig, env, b)),
        Term::Cast(from, to, proof, value) => {
            let (from, to) = (eval(sig, env, from), eval(sig, env, to));
            cast(sig, from, to, eval(sig, env, proof), eval(sig, env, value))
        }
        // Rule [Proof-Witness]
        // See Note [Proofs evaluate to an irrelevant witness].
        Term::Proof(_) | Term::Refl(_) | Term::Transp(_) | Term::Irrelevant => Val::Irrelevant,
        Term::Ann(e, _) => eval(sig, env, e),
        Term::Quot(a, r, level, _) => Val::Quot(Rc::new(QuotVal {
            carrier: eval(sig, env, a),
            relation: eval(sig, env, r),
            level: env.level(level),
        })),
        Term::QIn(a) => Val::QIn(Rc::new(eval(sig, env, a))),
        Term::QElim(p, f, _, level, q) => {
            let (motive, method) = (eval(sig, env, p), eval(sig, env, f));
            qelim(sig, motive, method, env.level(level), eval(sig, env, q))
        }
        Term::Nat(_, n) => Val::Nat(*n),
    }
}

fn eval_binding(sig: &Signature, env: &Env, b: &Binding) -> BindingVal {
    BindingVal {
        name: b.name.clone(),
        dom: eval(sig, env, &b.dom),
        cod: Closure::Term(env.clone(), b.cod.clone()),
        dom_level: env.level(&b.dom_level),
        cod_level: env.level(&b.cod_level),
    }
}

/// A global's value at the given levels.
pub fn eval_global(sig: &Signature, id: GlobalId, levels: Rc<[Level]>) -> Val {
    let global = sig.global(id);
    assert_eq!(global.level_params.len(), levels.len(), "`{}` instantiated at the wrong number of levels", global.name);
    match &global.kind {
        // Algorithm [Glued evaluation]
        GlobalKind::Definition(_) => Val::Unfold(Rc::new(Unfold::new(id, levels, None))),
        GlobalKind::Axiom => Val::neutral(Neutral::Axiom(id, levels)),
        GlobalKind::Data(data) => data_value(sig, *data, levels),
        GlobalKind::Constructor(data, index) => constructor_value(sig, *data, *index, levels),
        GlobalKind::Recursor(data) => recursor_value(sig, *data, levels),
        GlobalKind::Projection(..) => Val::Irrelevant,
    }
}

/// A global's type at the given levels.
pub fn global_type(sig: &Signature, id: GlobalId, levels: Rc<[Level]>) -> Val {
    eval(sig, &Env::with_levels(levels), &sig.global(id).ty)
}

pub fn apply(sig: &Signature, f: Val, a: Val) -> Val {
    match f {
        // Rule [Beta]
        Val::Lam(_, body) => body.apply(sig, a),
        Val::Neutral(n) => Val::neutral(Neutral::App(n, a)),
        Val::Irrelevant => Val::Irrelevant,
        Val::Unfold(u) => {
            let (global, levels) = (u.global, u.levels.clone());
            Val::Unfold(Rc::new(Unfold::new(global, levels, Some((u, a)))))
        }
        _ => unreachable!("applied a non-function: the checker let an ill-typed term through"),
    }
}

/// `@qelim motive method q`: the method on a class's representative.
pub fn qelim(sig: &Signature, motive: Val, method: Val, level: Level, q: Val) -> Val {
    match q {
        // Rule [Quot-Beta]
        Val::QIn(a) => apply(sig, method, (*a).clone()),
        Val::Neutral(n) => Val::neutral(Neutral::QElim { motive, method, level, quotient: n }),
        Val::Unfold(u) => qelim(sig, motive, method, level, u.unfolded(sig).clone()),
        _ => unreachable!("eliminated a non-quotient: the checker let an ill-typed term through"),
    }
}

// Rule [Sigma-Pair]
pub fn fst(sig: &Signature, p: Val) -> Val {
    match p {
        Val::Pair(pair) => pair.0.clone(),
        Val::Neutral(n) => Val::neutral(Neutral::Fst(n)),
        Val::Irrelevant => Val::Irrelevant,
        Val::Unfold(u) => fst(sig, u.unfolded(sig).clone()),
        _ => unreachable!("projected from a non-pair: the checker let an ill-typed term through"),
    }
}

pub fn snd(sig: &Signature, p: Val) -> Val {
    match p {
        Val::Pair(pair) => pair.1.clone(),
        Val::Neutral(n) => Val::neutral(Neutral::Snd(n)),
        Val::Irrelevant => Val::Irrelevant,
        Val::Unfold(u) => snd(sig, u.unfolded(sig).clone()),
        _ => unreachable!("projected from a non-pair: the checker let an ill-typed term through"),
    }
}

// ## Read-back

/// Read a value back to a term in a context of `depth` variables, with the
/// definitions it applies folded, as they were written.
pub fn quote(sig: &Signature, depth: Lvl, v: &Val) -> Term {
    read_back(sig, Unfolding::Folded, depth, v)
}

/// Read a value back to its normal form, every definition unfolded.
pub fn quote_unfolded(sig: &Signature, depth: Lvl, v: &Val) -> Term {
    read_back(sig, Unfolding::Unfolded, depth, v)
}

#[derive(Clone, Copy, PartialEq)]
enum Unfolding {
    Folded,
    Unfolded,
}

fn read_back(sig: &Signature, mode: Unfolding, depth: Lvl, v: &Val) -> Term {
    let quote = |sig, depth, v| read_back(sig, mode, depth, v);
    let quote_spine = |sig, depth, head, args: &[Val]| quote_spine(sig, mode, depth, head, args);
    match v {
        Val::Unfold(u) => match mode {
            Unfolding::Folded => quote_spine(sig, depth, Term::Global(u.global, u.levels.clone()), &u.spine()),
            Unfolding::Unfolded => quote(sig, depth, u.unfolded(sig)),
        },
        Val::Neutral(n) => quote_neutral(sig, mode, depth, n),
        Val::Sort(l) => Term::Sort(l.clone()),
        Val::Pi(p) => Term::Pi(Rc::new(quote_binding(sig, mode, depth, p))),
        Val::Lam(name, body) => Term::Lam(name.clone(), None, Rc::new(read_back_closure(sig, mode, depth, body))),
        Val::Sigma(p) => Term::Sigma(Rc::new(quote_binding(sig, mode, depth, p))),
        Val::Pair(pair) => Term::Pair(Rc::new(quote(sig, depth, &pair.0)), Rc::new(quote(sig, depth, &pair.1))),
        Val::Top => Term::Top,
        Val::Tt => Term::Tt,
        Val::Bottom => Term::Bottom,
        Val::Irrelevant => Term::Irrelevant,
        Val::Quot(q) => {
            let proofs = Rc::new([(); 3].map(|_| Rc::new(Term::Irrelevant)));
            Term::Quot(Rc::new(quote(sig, depth, &q.carrier)), Rc::new(quote(sig, depth, &q.relation)), q.level.clone(), proofs)
        }
        Val::QIn(a) => Term::QIn(Rc::new(quote(sig, depth, a))),
        Val::Nat(n) => Term::Nat(sig.builtins().expect("only a script, after the prelude, has a numeral").nat, *n),
        Val::Data(d) => {
            let head = Term::Global(sig.data(d.data).global, d.levels.clone());
            quote_spine(sig, depth, head, &d.params)
        }
        Val::Constructor(c) => {
            // The constructor as written: the uniform parameters and its
            // fields, at the indices it states, cast to the value's own
            // indices when they differ.
            // See Note [Indexed families are forded].
            let decl = sig.data(c.data);
            let ctor = &decl.constructors[c.index];
            let (u, nf) = (decl.uniform, ctor.surface.len());
            let head = Term::Global(ctor.global, c.levels.clone());
            let written = quote_spine(sig, depth, quote_spine(sig, depth, head, &c.params[..u]), &c.fields[..nf]);
            if u == decl.params.len() {
                return written;
            }
            let own = canonical(sig, c.data, c.index, c.levels.clone(), c.params[..u].to_vec(), c.fields[..nf].to_vec());
            let at = |params: &[Val]| quote_spine(sig, depth, Term::Global(decl.global, c.levels.clone()), params);
            let (from, to) = (at(&own.params), at(&c.params));
            if from == to {
                written
            } else {
                Term::Cast(Rc::new(from), Rc::new(to), Rc::new(Term::Irrelevant), Rc::new(written))
            }
        }
    }
}

fn quote_spine(sig: &Signature, mode: Unfolding, depth: Lvl, head: Term, args: &[Val]) -> Term {
    args.iter().fold(head, |f, a| Term::app(f, read_back(sig, mode, depth, a)))
}

fn quote_binding(sig: &Signature, mode: Unfolding, depth: Lvl, p: &BindingVal) -> Binding {
    Binding {
        name: p.name.clone(),
        dom: Rc::new(read_back(sig, mode, depth, &p.dom)),
        cod: Rc::new(read_back_closure(sig, mode, depth, &p.cod)),
        dom_level: p.dom_level.clone(),
        cod_level: p.cod_level.clone(),
    }
}

/// Read a closure back to its body, under one more binder.
pub fn quote_closure(sig: &Signature, depth: Lvl, c: &Closure) -> Term {
    read_back_closure(sig, Unfolding::Folded, depth, c)
}

fn read_back_closure(sig: &Signature, mode: Unfolding, depth: Lvl, c: &Closure) -> Term {
    read_back(sig, mode, depth + 1, &c.apply(sig, Val::var(depth)))
}

fn quote_neutral(sig: &Signature, mode: Unfolding, depth: Lvl, n: &Neutral) -> Term {
    let quote = |sig, depth, v| read_back(sig, mode, depth, v);
    let quote_spine = |sig, depth, head, args: &[Val]| quote_spine(sig, mode, depth, head, args);
    let quote_neutral = |sig, depth, n| quote_neutral(sig, mode, depth, n);
    match n {
        Neutral::Var(level) => {
            assert!(*level < depth, "variable level {level} escapes a context of depth {depth}");
            Term::Var(depth - 1 - level)
        }
        Neutral::Axiom(id, levels) => Term::Global(*id, levels.clone()),
        Neutral::App(f, a) => Term::app(quote_neutral(sig, depth, f), quote(sig, depth, a)),
        Neutral::Fst(p) => Term::Fst(Rc::new(quote_neutral(sig, depth, p))),
        Neutral::Snd(p) => Term::Snd(Rc::new(quote_neutral(sig, depth, p))),
        Neutral::Absurd(ty, e) => Term::Absurd(Rc::new(quote(sig, depth, ty)), Rc::new(quote(sig, depth, e))),
        Neutral::Recursor(rec, major) => {
            let head = Term::Global(sig.data(rec.data).recursor, rec.levels.clone());
            Term::app(quote_spine(sig, depth, head, &rec.args), quote_neutral(sig, depth, major))
        }
        Neutral::Eq { level, ty, a, b } => {
            let q = |v| Rc::new(quote(sig, depth, v));
            Term::Eq(level.clone(), q(ty), q(a), q(b))
        }
        Neutral::Cast { from, to, proof, value } => {
            let q = |v| Rc::new(quote(sig, depth, v));
            Term::Cast(q(from), q(to), q(proof), q(value))
        }
        Neutral::QElim { motive, method, level, quotient } => {
            let q = |v| Rc::new(quote(sig, depth, v));
            Term::QElim(q(motive), q(method), Rc::new(Term::Irrelevant), level.clone(), Rc::new(quote_neutral(sig, depth, quotient)))
        }
    }
}

// Note [Glued evaluation]
//
// A definition evaluates to a `Val::Unfold`: the global, its arguments, and
// its unfolding, computed the first time a rule looks at the head
// (`Val::force`). Applying it extends the spine; every other elimination
// forces it. This is smalltt's glued evaluation, for top-level definitions
// only.
//
// The two sides serve two readers. Read-back for printing and for elaborated
// terms takes the folded side, so an error shows `is_zero x.1` where the user
// wrote it, not the recursor it unfolds to. `quote_unfolded` takes the other
// side, for normal forms. Conversion first compares two applications of one
// definition at equal levels by their arguments, along the definition's
// type, and unfolds only when that fails: a no from the arguments is not a
// no, because a definition need not be injective. A stuck equality or cast
// keeps its sides as written, so it prints folded too.
//
// No rule changes: unfolding is the definition's own equation, applied later,
// and equal arguments give equal applications by congruence.
// See Algorithm [Glued evaluation].

// Note [Numerals compute on numbers]
//
// A numeral of the prelude's `@Nat` is the value `Val::Nat(n)`, not a chain
// of `n` constructors, as Lean keeps its `Nat` literals. It stands for that
// chain, and every rule that looks at a constructor sees it one step at a
// time: the recursor runs `n` steps up from `0` (`inductive::iota`),
// conversion and Eq-Ctor expand a numeral only against a constructor, and a
// constructor of `@Nat` over a numeral is a numeral again. Two numerals
// compare by their numbers, and a cast of one is itself, since `@Nat` has no
// parameters.
//
// The prelude's `+`, `-`, `*`, `<`, `==`, `@Nat.pred` and `@Nat.is_zero`,
// applied to numerals (or `@Nat.Succ` over one), give the numeral or boolean
// their definitions compute, without unfolding them (`Unfold::computed`).
// That is the value the
// definitions reach by Data-Iota, so no new equation holds; what changes is
// the cost, which no longer grows with the numbers. A result that does not
// fit 64 bits unfolds by the definition instead.
//
// What still walks the chain: a recursor on a numeral, and arithmetic with
// one side a variable, such as `n + 500`, which builds 500 constructors
// around `n`; comparing two such values recurses once per constructor, so
// that depth is bounded by the stack, as any deep term is.
// See Rule [Nat-Literal].
