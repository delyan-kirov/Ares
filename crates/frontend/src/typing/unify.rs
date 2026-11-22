//! The unifier behind type inference: a union-find over type variables with
//! level-based generalization.
//!
//! The algorithm is Hindley-Milner unification with Rémy's levels, from Didier
//! Rémy, "Extension of ML type system with a sorted equational theory on types"
//! (INRIA RR-1766, 1992). Each variable is `Unbound` at some
//! [`Level`], `Linked` to another type once unified, or
//! `Generic` once generalized. Entering a global's definition bumps the
//! current level; leaving it, any variable still unbound at a deeper level is
//! safe to quantify. The occurs check lowers levels as it walks, which is what
//! keeps that sound. See Note [Rémy levels].
//!
//! Unification compares weak head normal forms (`Unifier::whnf`): variable
//! links followed, glued aliases unfolded, and a size evaluated to its
//! polynomial. Two theories ride on top of plain structural unification, each in
//! its own module: [`rows`] (scoped-label rows for records and effects) and
//! [`sizes`] (the `Nat` kind of tensor sizes, compared as polynomials).
//! [`booleans`] folds the booleans a proposition compares before they meet.
//!
//! Input: pairs of [`Type`]s to make equal. Output: the variable bindings, or a
//! mismatch diagnostic. Every mutation is logged, so [`Unifier::save`] and
//! [`Unifier::restore`] can try a unification and take it back.
//!
//! Entry points: [`Unifier::unify`], [`Unifier::generalize`],
//! [`Unifier::instantiate`].

pub mod booleans;
pub mod levels;
pub mod rows;
pub mod sizes;

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use utilities::{Code, Diagnostic, Result, Span, StrId};

use crate::typing::types::{display, Level, LevelView, Type, TypeNode, Types, VarId};

/// The state of one unification variable.
#[derive(Clone, Debug)]
enum VarState {
    Unbound { level: Level },
    Linked(Type),
    Generic,
}

/// The mutable inference state shared across a whole program check.
pub struct Unifier {
    /// Every type node, and the interner for constructor and label names. Shared
    /// by every module's checker in one compilation: a `Type` is a handle into
    /// this store, so a type crossing a module boundary must address the same one.
    pub types: Rc<Types>,
    vars: Vec<VarState>,
    level: Level,
    /// Record-row schemes of the declared structs, by name: `(parameter vars in
    /// declaration order, the row)`. Lets a nominal struct unify with a structural
    /// record row (the hybrid bridge): passing a struct where an open row
    /// `{ x | r }` is expected. A generic struct instance `App(Con("Box"), Int)`
    /// bridges by substituting its arguments for the parameter vars.
    struct_rows: std::collections::HashMap<StrId, (Vec<VarId>, Type)>,
    /// Variables of the `Nat` kind (a size in `@Tensor n T`). A `Nat` variable unifies
    /// only with another `Nat` variable or a `TypeNode::Nat`; kind mismatches are
    /// rejected in [`Unifier::bind`]. Snapshotted by save/restore so a rolled-back
    /// trial cannot leave a stale id that a reused var slot would inherit.
    nat_vars: HashSet<VarId>,
    /// Variables introduced by an integer literal, which refuse to become a
    /// float. See Note [Integer literals never become floats].
    int_vars: HashSet<VarId>,
    /// The undo log behind [`Unifier::save`] / [`Unifier::restore`].
    trail: Vec<Undo>,
    /// Set while [`Unifier::unify_expected`] runs: its first operand is the type
    /// found, not the one expected, so a mismatch names them the other way round.
    found_first: bool,
    /// Variables a variable-to-variable unification links the other way round:
    /// the other variable is bound to one of these, never this one to it (see
    /// [`Unifier::keeping`]).
    keep: HashSet<VarId>,
    /// Size equations waiting for a binding to make them patterns, `None` once
    /// solved. See Note [Size patterns].
    postponed: Vec<Option<sizes::Postponed>>,
    /// Set while [`Unifier::wake`] runs, so a binding it makes does not wake
    /// the equations again from inside.
    waking: bool,
    /// The level each type variable bound with a universe stands at.
    /// See Note [Level constraints].
    var_levels: HashMap<VarId, Type>,
    /// Level constraints waiting for their definition to settle them.
    level_le: Vec<levels::LevelLe>,
    /// Level constraints over generalised variables, copied at each
    /// instantiation, and their index by variable.
    scheme_le: Vec<levels::LevelLe>,
    scheme_le_by_var: HashMap<VarId, Vec<usize>>,
    /// The universe of each declared struct, union and effect as a function
    /// of its parameters' levels. See Note [Declaration levels].
    pub decl_levels: HashMap<StrId, levels::DeclLevel>,
}

/// A type in weak head normal form, as conversion compares it. See
/// [`Unifier::whnf`].
enum Whnf {
    /// A size, evaluated: the `Nat` case of normalisation.
    Size(sizes::Poly),
    /// A universe level, which [`Unifier::unify_level`] compares by normal form.
    Level,
    /// Any other type: its head node.
    Node(TypeNode),
}

/// One reversible mutation, recorded so [`Unifier::restore`] can rewind a trial.
enum Undo {
    /// Put this var slot back to the value it held.
    Var(VarId, VarState),
    /// Drop this id from the `Nat`-kinded set again.
    NatVar(VarId),
    /// Drop this id from the integer-literal set again.
    IntVar(VarId),
    /// Drop the last postponed size equation again.
    Postponed,
    /// Put this postponed size equation back, unsolved.
    Woken(usize, sizes::Postponed),
    /// Forget this type variable's level again.
    VarLevel(VarId),
    /// Drop the last waiting level constraint again.
    LevelLe,
}

/// A checkpoint of the [`Unifier`] state, taken by [`Unifier::save`] and rewound by
/// [`Unifier::restore`]. A mark into the undo trail, not a copy of the var store:
/// a trial unification takes one per candidate, and copying the store made that
/// cost grow with every variable the program had introduced so far.
pub struct Save {
    trail: usize,
    vars: usize,
    level: Level,
}

// ## Variables and levels

impl Unifier {
    pub fn new(types: Rc<Types>) -> Unifier {
        Unifier {
            types,
            vars: Vec::new(),
            level: 0,
            struct_rows: std::collections::HashMap::new(),
            nat_vars: HashSet::new(),
            int_vars: HashSet::new(),
            trail: Vec::new(),
            found_first: false,
            keep: HashSet::new(),
            postponed: Vec::new(),
            waking: false,
            var_levels: HashMap::new(),
            level_le: Vec::new(),
            scheme_le: Vec::new(),
            scheme_le_by_var: HashMap::new(),
            decl_levels: HashMap::new(),
        }
    }

    /// Run `f` with the variables of `keep` bound last: where one meets another
    /// variable, that one is linked to it. Unifying with an instance this way
    /// leaves a signature's variables unbound (they belong to the caller), so a
    /// generic instance fits a requirement that mentions them.
    pub fn keeping<T>(&mut self, keep: &HashSet<VarId>, f: impl FnOnce(&mut Unifier) -> T) -> T {
        let outer = std::mem::replace(&mut self.keep, keep.clone());
        let out = f(self);
        self.keep = outer;
        out
    }

    // Note [Rémy levels]
    //
    // Generalizing a global means quantifying the variables of its type that do
    // not occur in the environment. Scanning the environment for them at every
    // global is quadratic. Rémy's levels make it a comparison instead: the
    // unifier keeps a current level, bumped on entering a global (or a group of
    // mutually recursive globals) and dropped on leaving it, and every fresh
    // variable records the level it was born at. A local `let` is not
    // generalized. See Note [Local lets are monomorphic].
    //
    // A variable can only escape into the environment by being unified with a
    // type that mentions an outer variable. So binding a variable at level `l`
    // to a type clamps every unbound variable in that type to at most `l`
    // (`occurs_and_adjust`, fused with the occurs check). After the right-hand
    // side, a variable still deeper than the current level is reachable only
    // from the binding being generalized, and `generalize` quantifies exactly
    // those.
    //
    // Two things lean on this. A failed definition unwinds to the level it
    // started at (`unwind_level`), so the next one starts clean. And a variable
    // a pending instance or overload requirement still constrains is held back
    // (`generalize_except`), the monomorphism restriction: it must stay a
    // unification variable until the requirement pins it.

    /// Enter a deeper definition; variables created here become generalizable
    /// once [`Unifier::leave_level`] runs. See Note [Rémy levels].
    pub fn enter_level(&mut self) {
        self.level += 1;
    }

    /// The current generalization level, saved before a definition so a failed
    /// check can be unwound to it ([`Unifier::unwind_level`]).
    pub fn level(&self) -> Level {
        self.level
    }

    pub fn unwind_level(&mut self, level: Level) {
        assert!(level <= self.level, "unwinding to a deeper level");
        self.level = level;
    }

    pub fn leave_level(&mut self) {
        debug_assert!(self.level > 0, "leave_level without a matching enter_level");
        self.level -= 1;
    }

    /// Overwrite a var slot, recording the old value so a trial can be rewound.
    fn set_var(&mut self, id: VarId, v: VarState) {
        let old = std::mem::replace(&mut self.vars[id as usize], v);
        self.trail.push(Undo::Var(id, old));
    }

    // Note [Integer literals never become floats]
    //
    // An integer literal's type is a fresh variable, so that `1` can be any
    // integer width the context asks for. It may not become a float: `1 + 2.0`
    // and `x : @Float64 = 1` are errors, and `1.0` is how a float is spelled.
    // A silent int-to-float reading hides a mistake as often as it saves a
    // keystroke, and a literal that is sometimes exact and sometimes rounded is
    // worse than one rule.
    //
    // The restriction lives in the unifier, not the checker, because it must
    // hold wherever unification reaches. The literal's variable goes into
    // `int_vars`. Binding it to a float constructor fails (`check_kind`), and
    // binding it to another variable marks that one too, so the restriction
    // follows the chain: in `1 + x`, `x` cannot become a float either. A
    // literal nothing constrains defaults to `@Int` at the definition boundary
    // (`Checker::default_numerics`), never to a float.

    /// Mark a variable as an integer literal's, so it refuses to become a float.
    /// See Note [Integer literals never become floats].
    pub fn mark_int_literal(&mut self, ty: Type) {
        if let TypeNode::Var(id) = self.types.node(ty) {
            if self.int_vars.insert(id) {
                self.trail.push(Undo::IntVar(id));
            }
        }
    }

    fn is_int_var(&self, id: VarId) -> bool {
        self.int_vars.contains(&id)
    }

    /// A fresh unbound variable at the current level.
    pub fn fresh(&mut self) -> Type {
        let id = self.vars.len() as VarId;
        self.vars.push(VarState::Unbound { level: self.level });
        self.types.add(TypeNode::Var(id))
    }

    /// A fresh already-`Generic` (quantified) variable. Used to construct the
    /// polymorphic types of built-ins, which are instantiated at each use.
    pub fn fresh_generic(&mut self) -> Type {
        let id = self.vars.len() as VarId;
        self.vars.push(VarState::Generic);
        self.types.add(TypeNode::Var(id))
    }

    /// A fresh variable that does not borrow `self` twice (used inside closures).
    fn fresh_raw(&mut self) -> Type {
        let id = self.vars.len() as VarId;
        self.vars.push(VarState::Unbound { level: self.level });
        self.types.add(TypeNode::Var(id))
    }
}

// ## Checkpoints

impl Unifier {
    /// Snapshot the whole variable store for trial unification. Restoring undoes
    /// every binding made since the snapshot, so a failed trial leaves
    /// no trace. (A clone of the store is simplest and fine at these sizes; a
    /// change trail would be the optimization.)
    pub fn save(&self) -> Save {
        Save {
            trail: self.trail.len(),
            vars: self.vars.len(),
            level: self.level,
        }
    }

    /// Rewind every mutation made since `save`. Undoing in reverse order matters:
    /// one slot may have been written more than once.
    pub fn restore(&mut self, save: Save) {
        while self.trail.len() > save.trail {
            match self.trail.pop().expect("length checked") {
                Undo::Var(id, old) => self.vars[id as usize] = old,
                Undo::NatVar(id) => {
                    self.nat_vars.remove(&id);
                }
                Undo::IntVar(id) => {
                    self.int_vars.remove(&id);
                }
                Undo::Postponed => {
                    self.postponed.pop();
                }
                Undo::Woken(i, c) => self.postponed[i] = Some(c),
                Undo::VarLevel(id) => {
                    self.var_levels.remove(&id);
                }
                Undo::LevelLe => {
                    self.level_le.pop();
                }
            }
        }
        self.vars.truncate(save.vars);
        self.level = save.level;
    }
}

// ## Resolution

impl Unifier {
    /// Follow variable links and glued aliases until the head is neither: the
    /// weak head normal form. See Note [Glued aliases].
    pub fn resolve(&self, ty: Type) -> Type {
        match self.types.node_raw(ty) {
            TypeNode::Var(id) => match self.vars[id as usize] {
                VarState::Linked(inner) => self.resolve(inner),
                _ => ty,
            },
            TypeNode::Alias(_, _, body) => self.resolve(body),
            _ => ty,
        }
    }

    /// The glued alias `ty` is, after following variable links: its name,
    /// arguments and unfolding.
    pub fn glued(&self, ty: Type) -> Option<(StrId, Vec<Type>, Type)> {
        match self.types.node_raw(ty) {
            TypeNode::Var(id) => match self.vars[id as usize] {
                VarState::Linked(inner) => self.glued(inner),
                _ => None,
            },
            TypeNode::Alias(name, args, body) => Some((name, self.types.items(args), body)),
            _ => None,
        }
    }

    /// Whether a variable is still unbound (not linked to another type). Context
    /// resolution asks this to tell a candidate that READS a type from one that
    /// would decide it.
    pub fn is_free(&self, id: VarId) -> bool {
        !matches!(self.vars[id as usize], VarState::Linked(_))
    }

    /// The node a type resolves to: [`Unifier::resolve`] then a store read. What
    /// almost every caller wants, since they match on the head constructor.
    pub fn head(&self, ty: Type) -> TypeNode {
        self.types.node(self.resolve(ty))
    }

    /// The weak head normal form unification compares: [`Unifier::resolve`],
    /// then a size (a `Nat` literal, a `+`/`*`, or a `Nat`-kinded variable)
    /// evaluated to its polynomial, so `n * 1` and `n` are the same size before
    /// either is taken for a variable to bind.
    fn whnf(&self, ty: Type) -> Whnf {
        match self.head(ty) {
            TypeNode::Nat(_) | TypeNode::NatAdd(..) | TypeNode::NatMul(..) => {
                Whnf::Size(self.normalize_size(ty))
            }
            TypeNode::Var(id) if self.is_nat_var(id) => Whnf::Size(self.normalize_size(ty)),
            TypeNode::Level(_) | TypeNode::LevelAdd(..) | TypeNode::LevelMax(..) => Whnf::Level,
            node => Whnf::Node(node),
        }
    }

    /// Fully resolve a type, replacing every linked variable throughout ("zonk").
    pub fn zonk(&self, ty: Type) -> Type {
        if let Some((name, args, body)) = self.glued(ty) {
            let args = args.into_iter().map(|a| self.zonk(a)).collect();
            return self.types.alias(name, args, self.zonk(body));
        }
        match self.head(ty) {
            TypeNode::App(head, arg) => {
                let (h, a) = (self.zonk(head), self.zonk(arg));
                self.types.app(h, a)
            }
            TypeNode::NatAdd(a, b) => {
                let (x, y) = (self.zonk(a), self.zonk(b));
                self.types.add(TypeNode::NatAdd(x, y))
            }
            TypeNode::NatMul(a, b) => {
                let (x, y) = (self.zonk(a), self.zonk(b));
                self.types.add(TypeNode::NatMul(x, y))
            }
            TypeNode::Level(_) | TypeNode::LevelAdd(..) | TypeNode::LevelMax(..) => {
                self.level_of_nf(&self.normalize_level(ty))
            }
            TypeNode::Arrow(from, to, eff) => {
                let (f, t, e) = (self.zonk(from), self.zonk(to), self.zonk(eff));
                self.types.arrow_eff(f, t, e)
            }
            TypeNode::Tuple(items) => {
                let items = self.types.items(items).to_vec();
                let zonked: Vec<Type> = items.into_iter().map(|t| self.zonk(t)).collect();
                self.types.tuple(zonked)
            }
            TypeNode::RowExtend(label, args, rest) => {
                let (a, r) = (self.zonk(args), self.zonk(rest));
                self.types.add(TypeNode::RowExtend(label, a, r))
            }
            TypeNode::Record(row) => {
                let r = self.zonk(row);
                self.types.record(r)
            }
            TypeNode::RowField(label, ty, rest) => {
                let (f, r) = (self.zonk(ty), self.zonk(rest));
                self.types.add(TypeNode::RowField(label, f, r))
            }
            // Var (unbound/generic), Con, or RowEmpty: already its own resolution.
            _ => self.resolve(ty),
        }
    }
}

// ## Unification

impl Unifier {
    /// Unify the type `found` of an expression with the type `expected` of its
    /// position. A mismatch says "expected E, found F" the right way round, and
    /// when it lies inside a larger type, a note shows both whole types.
    pub fn unify_expected(&mut self, found: Type, expected: Type, where_: &str) -> Result<()> {
        self.expected_by(found, expected, where_, Unifier::unify)
    }

    /// [`Self::unify_expected`], but a function may be used where one with more
    /// effects is expected (see [`Self::subsume`]).
    pub fn subsume_expected(&mut self, found: Type, expected: Type, where_: &str) -> Result<()> {
        self.expected_by(found, expected, where_, Unifier::subsume)
    }

    fn expected_by(
        &mut self,
        found: Type,
        expected: Type,
        where_: &str,
        relate: fn(&mut Unifier, Type, Type, &str) -> Result<()>,
    ) -> Result<()> {
        let saved = std::mem::replace(&mut self.found_first, true);
        let r = relate(self, found, expected, where_);
        self.found_first = saved;
        r.map_err(|d| {
            if d.root().code != Code::TypeMismatch {
                return d;
            }
            let (e, f) = (self.show(expected), self.show(found));
            let msg = &d.root().msg;
            let whole_is_news = (msg.contains(", found ") || msg.starts_with("size mismatch"))
                && !msg.ends_with(&format!("expected {e}, found {f}"))
                && !matches!(self.head(expected), TypeNode::Var(_))
                && !matches!(self.head(found), TypeNode::Var(_));
            if !whole_is_news {
                return d;
            }
            d.with_note(format!("expected type `{e}`\n         found type `{f}`"))
        })
    }

    /// Unify two types, mutating variables in place. `where_` names the context
    /// for diagnostics.
    pub fn unify(&mut self, a: Type, b: Type, where_: &str) -> Result<()> {
        let (written_a, written_b) = (a, b);
        let a = self.resolve(a);
        let b = self.resolve(b);
        if a == self.types.error() || b == self.types.error() {
            return Ok(());
        }
        if self.bool_op(a).is_some() || self.bool_op(b).is_some() {
            let (fa, fb) = (self.fold_bool(a), self.fold_bool(b));
            if fa.is_some() || fb.is_some() {
                return self.unify(fa.unwrap_or(a), fb.unwrap_or(b), where_);
            }
        }
        let (na, nb) = match (self.whnf(a), self.whnf(b)) {
            (Whnf::Size(pa), Whnf::Size(pb)) => return self.unify_size(pa, pb, a, b, where_),
            (Whnf::Size(_), Whnf::Node(TypeNode::Var(j))) => return self.bind(j, a),
            (Whnf::Node(TypeNode::Var(i)), Whnf::Size(_)) => return self.bind(i, b),
            (Whnf::Size(_), Whnf::Node(_)) => return Err(self.kind_mismatch(self.found_first)),
            (Whnf::Node(_), Whnf::Size(_)) => return Err(self.kind_mismatch(!self.found_first)),
            // A variable against a level is a level atom, so `u = u + 0` and
            // `u = @max u v` are level equations, not occurs failures.
            (Whnf::Level, Whnf::Level) | (Whnf::Level, Whnf::Node(TypeNode::Var(_))) | (Whnf::Node(TypeNode::Var(_)), Whnf::Level) => {
                return self.unify_level(a, b, where_)
            }
            (Whnf::Level, _) | (_, Whnf::Level) => return Err(self.mismatch(written_a, written_b, where_)),
            (Whnf::Node(na), Whnf::Node(nb)) => (na, nb),
        };
        match (na, nb) {
            (TypeNode::Var(i), TypeNode::Var(j)) if i == j => Ok(()),
            (TypeNode::Var(i), TypeNode::Var(j)) if self.keep.contains(&i) && !self.keep.contains(&j) => {
                self.bind(j, a)
            }
            (TypeNode::Var(i), _) => self.bind(i, b),
            (_, TypeNode::Var(j)) => self.bind(j, a),
            (TypeNode::Con(x), TypeNode::Con(y)) if x == y => Ok(()),
            (TypeNode::Arrow(a1, a2, ae), TypeNode::Arrow(b1, b2, be)) => {
                self.unify(a1, b1, where_)?;
                self.unify(a2, b2, where_)?;
                self.unify(ae, be, where_)
            }
            (TypeNode::App(a1, a2), TypeNode::App(b1, b2)) => {
                self.unify(a1, b1, where_)?;
                self.unify(a2, b2, where_)
            }
            (TypeNode::Tuple(xs), TypeNode::Tuple(ys)) if xs.len() == ys.len() => {
                let pairs: Vec<(Type, Type)> = self
                    .types
                    .items(xs)
                    .iter()
                    .copied()
                    .zip(self.types.items(ys).iter().copied())
                    .collect();
                for (x, y) in pairs {
                    self.unify(x, y, where_)?;
                }
                Ok(())
            }
            (TypeNode::RowEmpty, TypeNode::RowEmpty) => Ok(()),
            (TypeNode::RowExtend(..), _) | (_, TypeNode::RowExtend(..)) => {
                self.unify_row(a, b, where_)
            }
            (TypeNode::Record(ra), TypeNode::Record(rb)) => self.unify_record(ra, rb, where_),
            (TypeNode::RowField(..), _) | (_, TypeNode::RowField(..)) => {
                self.unify_record_row(a, b, where_)
            }
            // The hybrid bridge: a nominal struct (bare `Con` or a generic instance
            // `App..(Con)`) satisfies a structural record row by expanding to its
            // row, with its type arguments substituted for the struct's parameters.
            _ => match self.struct_row_bridge(a, b, where_) {
                Some(r) => r,
                None => Err(self.mismatch(written_a, written_b, where_)),
            },
        }
    }

    /// Require a value of type `found` to be usable at type `expected`. Two
    /// arrows relate by effect subsumption: the found function's row must be a
    /// subrow of the expected one, contravariantly in parameters and covariantly
    /// in results. Everything else unifies.
    pub fn subsume(&mut self, found: Type, expected: Type, where_: &str) -> Result<()> {
        match (self.head(found), self.head(expected)) {
            (TypeNode::Arrow(fp, fr, fe), TypeNode::Arrow(ep, er, ee)) => {
                self.subsume(ep, fp, where_)?;
                self.subsume(fr, er, where_)?;
                self.subrow(fe, ee, where_)
            }
            _ => self.unify(found, expected, where_),
        }
    }

    /// Point an unbound variable `id` at `ty` after the occurs/level check.
    fn bind(&mut self, id: VarId, ty: Type) -> Result<()> {
        let level = match self.vars[id as usize] {
            VarState::Unbound { level } => level,
            _ => {
                debug_assert!(false, "bind called on a non-unbound variable");
                return Ok(());
            }
        };
        self.check_kind(id, ty)?;
        self.occurs_and_adjust(id, level, ty)?;
        self.bind_level(id, ty)?;
        self.set_var(id, VarState::Linked(ty));
        self.wake()
    }

    /// The occurs check, fused with the level-lowering that generalization
    /// relies on: fail if `id` appears in `ty`, and clamp every unbound variable
    /// inside `ty` to at most `level`.
    fn occurs_and_adjust(&mut self, id: VarId, level: Level, ty: Type) -> Result<()> {
        match self.head(ty) {
            TypeNode::Var(other) => {
                if other == id {
                    return Err(Diagnostic::error(
                        Code::TypeCycle,
                        Span::at(0),
                        0,
                        "cannot construct an infinite type (a variable occurs in its own binding)",
                    ));
                }
                if let VarState::Unbound { level: other_level } = self.vars[other as usize] {
                    if other_level > level {
                        self.set_var(other, VarState::Unbound { level });
                    }
                }
                Ok(())
            }
            TypeNode::Con(_) | TypeNode::Nat(_) | TypeNode::Level(_) | TypeNode::RowEmpty => Ok(()),
            TypeNode::Alias(..) => unreachable!("`head` looks through aliases"),
            TypeNode::App(head, arg) => {
                self.occurs_and_adjust(id, level, head)?;
                self.occurs_and_adjust(id, level, arg)
            }
            TypeNode::LevelAdd(l, _) => self.occurs_and_adjust(id, level, l),
            TypeNode::NatAdd(a, b) | TypeNode::NatMul(a, b) | TypeNode::LevelMax(a, b) => {
                self.occurs_and_adjust(id, level, a)?;
                self.occurs_and_adjust(id, level, b)
            }
            TypeNode::Arrow(from, to, eff) => {
                self.occurs_and_adjust(id, level, from)?;
                self.occurs_and_adjust(id, level, to)?;
                self.occurs_and_adjust(id, level, eff)
            }
            TypeNode::Tuple(items) => {
                for item in self.types.items(items).to_vec() {
                    self.occurs_and_adjust(id, level, item)?;
                }
                Ok(())
            }
            TypeNode::RowExtend(_, args, rest) => {
                self.occurs_and_adjust(id, level, args)?;
                self.occurs_and_adjust(id, level, rest)
            }
            TypeNode::Record(row) => self.occurs_and_adjust(id, level, row),
            TypeNode::RowField(_, ty, rest) => {
                self.occurs_and_adjust(id, level, ty)?;
                self.occurs_and_adjust(id, level, rest)
            }
        }
    }

    fn mismatch(&self, a: Type, b: Type, where_: &str) -> Diagnostic {
        let (a, b) = if self.found_first { (b, a) } else { (a, b) };
        Diagnostic::error(
            Code::TypeMismatch,
            Span::at(0),
            0,
            format!(
                "type mismatch {where_}: expected {}, found {}",
                self.show(a),
                self.show(b)
            ),
        )
    }
}

// ## Generalization and instantiation

impl Unifier {
    /// Generalize a type: every unbound variable deeper than the current level
    /// becomes `Generic` (quantified). Run after leaving a `let` binding's level.
    pub fn generalize(&mut self, ty: Type) {
        self.generalize_except(ty, &HashSet::new());
    }

    /// Generalize as [`Unifier::generalize`], but leave any variable in `mono`
    /// ungeneralized. This is the monomorphism restriction: a variable still
    /// constrained by an unresolved requirement must stay a unification variable so
    /// a later use can pin it, rather than becoming spuriously polymorphic.
    pub fn generalize_except(&mut self, ty: Type, mono: &HashSet<VarId>) {
        self.generalize_rec(ty, mono);
        self.attach_generic_constraints();
    }

    fn generalize_rec(&mut self, ty: Type, mono: &HashSet<VarId>) {
        match self.head(ty) {
            TypeNode::Var(id) => {
                if mono.contains(&id) {
                    return;
                }
                if let VarState::Unbound { level } = self.vars[id as usize] {
                    if level > self.level {
                        self.set_var(id, VarState::Generic);
                        if let Some(l) = self.var_level(id) {
                            self.generalize_rec(l, mono);
                        }
                    }
                }
            }
            TypeNode::App(head, arg) => {
                self.generalize_rec(head, mono);
                self.generalize_rec(arg, mono);
            }
            TypeNode::NatAdd(a, b) | TypeNode::NatMul(a, b) | TypeNode::LevelMax(a, b) => {
                self.generalize_rec(a, mono);
                self.generalize_rec(b, mono);
            }
            TypeNode::LevelAdd(l, _) => self.generalize_rec(l, mono),
            TypeNode::Arrow(from, to, eff) => {
                self.generalize_rec(from, mono);
                self.generalize_rec(to, mono);
                self.generalize_rec(eff, mono);
            }
            TypeNode::Tuple(items) => {
                for t in self.types.items(items).to_vec() {
                    self.generalize_rec(t, mono);
                }
            }
            TypeNode::RowExtend(_, args, rest) => {
                self.generalize_rec(args, mono);
                self.generalize_rec(rest, mono);
            }
            TypeNode::Record(row) => self.generalize_rec(row, mono),
            TypeNode::RowField(_, ty, rest) => {
                self.generalize_rec(ty, mono);
                self.generalize_rec(rest, mono);
            }
            TypeNode::Con(_) | TypeNode::Nat(_) | TypeNode::Level(_) | TypeNode::RowEmpty => {}
            TypeNode::Alias(..) => unreachable!("`head` looks through aliases"),
        }
    }

    /// Collect the unbound variables reachable from `ty` (after resolution) into
    /// `out`. Used to protect a pending requirement's variables from generalization.
    pub fn collect_vars(&self, ty: Type, out: &mut HashSet<VarId>) {
        match self.head(ty) {
            TypeNode::Var(id) => {
                out.insert(id);
            }
            TypeNode::App(head, arg) => {
                self.collect_vars(head, out);
                self.collect_vars(arg, out);
            }
            TypeNode::NatAdd(a, b) | TypeNode::NatMul(a, b) | TypeNode::LevelMax(a, b) => {
                self.collect_vars(a, out);
                self.collect_vars(b, out);
            }
            TypeNode::LevelAdd(l, _) => self.collect_vars(l, out),
            TypeNode::Arrow(from, to, eff) => {
                self.collect_vars(from, out);
                self.collect_vars(to, out);
                self.collect_vars(eff, out);
            }
            TypeNode::Tuple(items) => {
                for t in self.types.items(items) {
                    self.collect_vars(t, out);
                }
            }
            TypeNode::RowExtend(_, args, rest) => {
                self.collect_vars(args, out);
                self.collect_vars(rest, out);
            }
            TypeNode::Record(row) => self.collect_vars(row, out),
            TypeNode::RowField(_, ty, rest) => {
                self.collect_vars(ty, out);
                self.collect_vars(rest, out);
            }
            TypeNode::Con(_) | TypeNode::Nat(_) | TypeNode::Level(_) | TypeNode::RowEmpty => {}
            TypeNode::Alias(..) => unreachable!("`head` looks through aliases"),
        }
    }

    /// Instantiate a (possibly polymorphic) type: replace each `Generic` variable
    /// with a fresh unbound variable, consistently within this one call.
    pub fn instantiate(&mut self, ty: Type) -> Type {
        let mut mapping = HashMap::new();
        let t = self.instantiate_with(ty, &mut mapping);
        self.emit_scheme_constraints(&mut mapping);
        t
    }

    /// Instantiate an effect operation's scheme for a handler clause. The
    /// effect's parameters (the label's arguments) and the row tail are fresh
    /// variables as usual; every other variable is the operation's own, chosen
    /// by each performer, so the clause sees it as an opaque type of its own (a
    /// rigid variable, unique to this clause): it can pass such a value along,
    /// but not make one up. `op` names the operation in it.
    pub fn instantiate_for_handler(&mut self, scheme: Type, op: &str) -> Type {
        let mut mapping = HashMap::new();
        if let TypeNode::Arrow(from, to, eff) = self.head(scheme) {
            let mut shared = HashSet::new();
            self.collect_vars(eff, &mut shared);
            let mut order = Vec::new();
            self.vars_in_order(from, &mut order);
            self.vars_in_order(to, &mut order);
            let own: Vec<VarId> = order
                .into_iter()
                .filter(|id| !shared.contains(id) && matches!(self.vars[*id as usize], VarState::Generic))
                .collect();
            for (i, id) in own.into_iter().enumerate() {
                let letter = (b'a' + (i % 26) as u8) as char;
                let rigid = self.types.rigid(&format!("`{letter}` of `{op}`"));
                mapping.insert(id, rigid);
            }
        }
        self.instantiate_with(scheme, &mut mapping)
    }

    /// Replace each `Generic` variable of `tys` with a rigid type, the same one
    /// wherever it occurs, as the body of the definition that generalized it saw
    /// it. `name` is how each rigid type displays.
    pub fn rigid_generics(&mut self, tys: &[Type], name: &str) -> Vec<Type> {
        let mut vars = HashSet::new();
        for t in tys {
            self.collect_vars(*t, &mut vars);
        }
        let mut mapping = HashMap::new();
        for id in vars {
            if matches!(self.vars[id as usize], VarState::Generic) {
                mapping.insert(id, self.types.rigid(name));
            }
        }
        tys.iter().map(|t| self.instantiate_with(*t, &mut mapping)).collect()
    }

    /// The variables of `ty` in order of first appearance, each once.
    fn vars_in_order(&self, ty: Type, out: &mut Vec<VarId>) {
        let mut set = HashSet::new();
        self.collect_vars(ty, &mut set);
        let mut found: Vec<VarId> = set.into_iter().filter(|id| !out.contains(id)).collect();
        found.sort_unstable();
        out.extend(found);
    }

    /// Instantiate several types that share generalized variables with ONE fresh
    /// mapping, so a `Generic` common to two of them maps to the same fresh var.
    /// Used to instantiate an instance's exposed type together with the context it
    /// requires (an `Ito_string (Box t)` instance and its `Ito_string t` share `t`).
    pub fn instantiate_bundle(&mut self, tys: &[Type]) -> Vec<Type> {
        let mut mapping = HashMap::new();
        let out = tys.to_vec().into_iter().map(|t| self.instantiate_with(t, &mut mapping)).collect();
        self.emit_scheme_constraints(&mut mapping);
        out
    }

    pub(super) fn instantiate_with(&mut self, ty: Type, mapping: &mut HashMap<VarId, Type>) -> Type {
        if let Some((name, args, body)) = self.glued(ty) {
            let args = args.into_iter().map(|a| self.instantiate_with(a, mapping)).collect();
            let body = self.instantiate_with(body, mapping);
            return self.types.alias(name, args, body);
        }
        match self.head(ty) {
            TypeNode::Var(id) => match self.vars[id as usize] {
                VarState::Generic => {
                    if let Some(t) = mapping.get(&id) {
                        return *t;
                    }
                    let fresh = self.fresh_raw();
                    // A refreshed size variable stays `Nat`-kinded.
                    if self.is_nat_var(id) {
                        if let TypeNode::Var(fid) = self.types.node(fresh) {
                            self.mark_nat(fid);
                        }
                    }
                    mapping.insert(id, fresh);
                    if let Some(l) = self.var_level(id) {
                        let l = self.instantiate_with(l, mapping);
                        self.set_var_level(fresh, l);
                    }
                    fresh
                }
                _ => self.types.add(TypeNode::Var(id)),
            },
            TypeNode::App(head, arg) => {
                let (h, a) = (
                    self.instantiate_with(head, mapping),
                    self.instantiate_with(arg, mapping),
                );
                self.types.app(h, a)
            }
            TypeNode::NatAdd(a, b) => {
                let (x, y) = (
                    self.instantiate_with(a, mapping),
                    self.instantiate_with(b, mapping),
                );
                self.types.add(TypeNode::NatAdd(x, y))
            }
            TypeNode::NatMul(a, b) => {
                let (x, y) = (
                    self.instantiate_with(a, mapping),
                    self.instantiate_with(b, mapping),
                );
                self.types.add(TypeNode::NatMul(x, y))
            }
            TypeNode::LevelMax(a, b) => {
                let (x, y) = (
                    self.instantiate_with(a, mapping),
                    self.instantiate_with(b, mapping),
                );
                self.types.add(TypeNode::LevelMax(x, y))
            }
            TypeNode::LevelAdd(l, n) => {
                let l = self.instantiate_with(l, mapping);
                self.types.add(TypeNode::LevelAdd(l, n))
            }
            TypeNode::Arrow(from, to, eff) => {
                let (f, t, e) = (
                    self.instantiate_with(from, mapping),
                    self.instantiate_with(to, mapping),
                    self.instantiate_with(eff, mapping),
                );
                self.types.arrow_eff(f, t, e)
            }
            TypeNode::Tuple(items) => {
                let items = self.types.items(items).to_vec();
                let mapped: Vec<Type> = items
                    .into_iter()
                    .map(|t| self.instantiate_with(t, mapping))
                    .collect();
                self.types.tuple(mapped)
            }
            TypeNode::RowExtend(label, args, rest) => {
                let a = self.instantiate_with(args, mapping);
                let r = self.instantiate_with(rest, mapping);
                self.types.add(TypeNode::RowExtend(label, a, r))
            }
            TypeNode::Record(row) => {
                let r = self.instantiate_with(row, mapping);
                self.types.record(r)
            }
            TypeNode::RowField(label, ty, rest) => {
                let (f, r) = (
                    self.instantiate_with(ty, mapping),
                    self.instantiate_with(rest, mapping),
                );
                self.types.add(TypeNode::RowField(label, f, r))
            }
            // Con or RowEmpty: already its own instance.
            _ => self.resolve(ty),
        }
    }
}

// ## Display

impl Unifier {
    /// Render a type with variables named `` `a ``, `` `b ``, ... in order.
    pub fn show(&self, ty: Type) -> String {
        self.show_all(&[ty]).pop().expect("one rendering")
    }

    /// Render several types under ONE variable naming, so a context requirement and
    /// the signature it belongs to agree on their variable names.
    pub fn show_all(&self, tys: &[Type]) -> Vec<String> {
        self.show_all_named(tys, HashMap::new())
    }

    /// [`Self::show_all`] with some variables named already, as a signature
    /// binds them; the rest take the letters those names leave free.
    pub fn show_all_named(&self, tys: &[Type], mut names: HashMap<VarId, String>) -> Vec<String> {
        let taken: HashSet<String> = names.values().cloned().collect();
        let named: HashSet<VarId> = names.keys().copied().collect();
        let of = |id: VarId| self.var_level(id).map(|l| self.zonk(l));
        let levels = LevelView { of: &of, named: &named };
        let mut next = 0u32;
        let mut namer = |id: VarId| {
            names
                .entry(id)
                .or_insert_with(|| loop {
                    // Type variables display lowercase (`a`), matching the source
                    // syntax where a lowercase name in type position is a variable.
                    let name = ((b'a' + (next % 26) as u8) as char).to_string();
                    next += 1;
                    if !taken.contains(&name) {
                        break name;
                    }
                })
                .clone()
        };
        tys.iter()
            .map(|t| {
                let zonked = self.zonk(*t);
                display(&self.types, zonked, &mut namer, &levels)
            })
            .collect()
    }
}

/// Whether a type-constructor name is one of the float types, which an integer
/// literal may not become.
pub(super) fn is_float_name(name: &str) -> bool {
    matches!(name, "@Float64" | "@Float32")
}
