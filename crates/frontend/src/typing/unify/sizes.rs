//! Sizes: the `Nat` kind of tensor axes, and their equality.
//!
//! A tensor type `@Tensor n T` carries its size `n` as a type of kind `Nat`: a literal,
//! a `Nat` variable, or a `+`/`*` of sizes. Two sizes are equal when their
//! normal forms are: `normalize_size` turns a size into a polynomial
//! over Z/2^64 (a sum of coefficient-times-monomial terms, like terms combined,
//! sorted), and structural equality of polynomials decides the rest.
//! Evaluating a size is the `Nat` case of `Unifier::whnf`, so sizes are
//! compared by the same normaliser as every other type.
//!
//! A size is inferred by pattern unification: once equal terms cancel, a side
//! that is a lone unbound variable binds it, and an equation with no unique
//! solution yet is postponed until a later binding makes it one.
//! See Note [Size patterns].
//!
//! This module also keeps the kind discipline (a `Nat` variable binds only a
//! size).
//!
//! Entry points: [`Unifier::fresh_nat`], [`Unifier::nat_value`],
//! [`Unifier::unsolved_size`]; plain [`Unifier::unify`] comes here when both
//! normal forms are sizes.

use utilities::{Code, Diagnostic, Result, Span};

use super::{is_float_name, Undo, Unifier, VarState, Whnf};
use crate::typing::types::{Type, TypeNode, VarId};


// ## Nat variables

impl Unifier {
    /// A fresh unbound variable of the `Nat` kind (a tensor size).
    pub fn fresh_nat(&mut self) -> Type {
        let ty = self.fresh();
        if let TypeNode::Var(id) = self.types.node(ty) {
            self.mark_nat(id);
        }
        ty
    }

    /// A fresh `Generic` `Nat` variable, for the scheme of a size-polymorphic
    /// built-in (instantiated, staying Nat-kinded, at each use).
    pub fn fresh_generic_nat(&mut self) -> Type {
        let ty = self.fresh_generic();
        if let TypeNode::Var(id) = self.types.node(ty) {
            self.mark_nat(id);
        }
        ty
    }

    /// Whether `ty` is a variable of kind `@Nat`.
    pub fn is_size_var(&self, ty: Type) -> bool {
        match self.types.node(self.resolve(ty)) {
            TypeNode::Var(id) => self.is_nat_var(id),
            _ => false,
        }
    }

    pub(super) fn is_nat_var(&self, id: VarId) -> bool {
        self.nat_vars.contains(&id)
    }

    /// Mark a variable `Nat`-kinded, recording it if this is the first time.
    pub(super) fn mark_nat(&mut self, id: VarId) {
        if self.nat_vars.insert(id) {
            self.trail.push(Undo::NatVar(id));
        }
    }

    /// Mark the variables of a size `ty` as `@Nat`, for a position that wants one.
    pub fn mark_size(&mut self, ty: Type) {
        self.note_nat(ty);
    }

    /// Mark every variable in a size expression (a `Nat` position) as `Nat`-kinded.
    pub(super) fn note_nat(&mut self, ty: Type) {
        match self.head(ty) {
            TypeNode::Var(id) => {
                self.mark_nat(id);
            }
            TypeNode::NatAdd(a, b) | TypeNode::NatMul(a, b) => {
                self.note_nat(a);
                self.note_nat(b);
            }
            _ => {}
        }
    }

    /// Walk a type and mark every tensor-size variable as `Nat`. Kind is not carried
    /// in a `TypeNode::Var`, so a scheme imported across modules (fresh plain generics)
    /// must be re-annotated from its structure, else a size var unifies as a type.
    pub fn note_tensor_sizes(&mut self, ty: Type) {
        match self.head(ty) {
            TypeNode::App(head, elem) => {
                if let Some((size, _elem)) = self.tensor_spine(ty) {
                    self.note_nat(size);
                }
                self.note_tensor_sizes(head);
                self.note_tensor_sizes(elem);
            }
            TypeNode::Arrow(from, to, eff) => {
                self.note_tensor_sizes(from);
                self.note_tensor_sizes(to);
                self.note_tensor_sizes(eff);
            }
            TypeNode::Tuple(items) => {
                for t in self.types.items(items).to_vec() {
                    self.note_tensor_sizes(t);
                }
            }
            TypeNode::Record(row) => self.note_tensor_sizes(row),
            TypeNode::RowField(_, t, rest) => {
                self.note_tensor_sizes(t);
                self.note_tensor_sizes(rest);
            }
            _ => {}
        }
    }

    /// A `Nat`-kinded variable may bind only to a `Nat` literal or another
    /// `Nat`-kinded variable; a `Type` variable may not bind to a `Nat`. Binding a
    /// `Nat` variable to a plain variable makes that variable `Nat` too.
    pub(super) fn check_kind(&mut self, id: VarId, ty: Type) -> Result<()> {
        let want_nat = self.is_nat_var(id);
        match self.head(ty) {
            TypeNode::Nat(_) | TypeNode::NatAdd(..) | TypeNode::NatMul(..) => {
                if !want_nat {
                    return Err(self.kind_mismatch(true));
                }
            }
            TypeNode::Var(other) => {
                let other_nat = self.is_nat_var(other);
                if want_nat && !other_nat {
                    self.mark_nat(other);
                } else if !want_nat && other_nat {
                    self.mark_nat(id);
                }
                // The integer-literal restriction travels with the chain, so
                // `1 + x` keeps `x` from being a float too.
                if self.is_int_var(id) {
                    let ty = self.types.add(TypeNode::Var(other));
                    self.mark_int_literal(ty);
                }
            }
            TypeNode::Con(name) if self.is_int_var(id) && is_float_name(self.types.name(name)) => {
                return Err(Diagnostic::error(
                    Code::TypeMismatch,
                    Span::at(0),
                    0,
                    format!("an integer literal cannot be a `{}`", self.types.name(name)),
                )
                .with_note("an integer literal never becomes a float")
                .with_help("write a float literal instead (`1.0`, not `1`)"));
            }
            _ => {
                if want_nat {
                    return Err(self.kind_mismatch(false));
                }
            }
        }
        Ok(())
    }

    pub(super) fn kind_mismatch(&self, found_nat: bool) -> Diagnostic {
        let msg = if found_nat {
            "kind mismatch: a size (`Nat`) where a type was expected"
        } else {
            "kind mismatch: a type where a size (`Nat`) was expected"
        };
        Diagnostic::error(Code::TypeMismatch, Span::at(0), 0, msg)
    }
}

// ## Tensors

impl Unifier {
    /// Peel one axis of a sized-tensor type `@tensor size elem` into its size and
    /// element.
    pub fn tensor_spine(&self, ty: Type) -> Option<(Type, Type)> {
        if let TypeNode::App(head, elem) = self.head(ty) {
            if let TypeNode::App(con, size) = self.head(head) {
                if matches!(self.head(con), TypeNode::Con(n) if self.types.name(n) == "@tensor") {
                    return Some((size, elem));
                }
            }
        }
        None
    }
}

// ## Size equality

impl Unifier {
    // Note [Size patterns]
    //
    // A size equation `a = b` is solved the way pattern unification solves a
    // metavariable: only when the solution is unique. The unbound variables of
    // a size are its metavariables; a `Generic` one is a parameter of the
    // signature being checked and stays rigid.
    //
    // Both sides are evaluated to polynomials and the common part is cancelled
    // (`n + 1 = 5` becomes `n = 4`, `3n = n + m` becomes `2n = m`). Cancelling is
    // sound in any additive group, so in Z/2^64 too. What is left is a pattern
    // when one side is a lone metavariable that does not occur in the other,
    // and then the other side is its unique solution. With no metavariable left
    // the sizes differ.
    //
    // Anything else (`n + m = 5`, `2n = 6`) has many solutions or none we can
    // write, so it is postponed, not refused. Every later binding wakes the
    // postponed equations, since solving `n` may turn `n + m = 5` into a pattern
    // (`Unifier::wake`). One still postponed when its definition is checked is
    // an error (`Unifier::unsolved_size`). Solving `2n = 6` would need division,
    // and in Z/2^64 it has two solutions; `n + 1 = m` needs subtraction, which a
    // size cannot spell. Both are left to an annotation.

    /// Unify two sizes `a` and `b`, evaluated to the polynomials `pa` and `pb`.
    /// See Note [Size patterns].
    pub(super) fn unify_size(&mut self, pa: Poly, pb: Poly, a: Type, b: Type, where_: &str) -> Result<()> {
        match self.size_step(&pa, &pb, a, b) {
            Step::Equal => Ok(()),
            Step::Bind(v, t) => self.bind(v, t),
            Step::Postpone => {
                self.postponed.push(Some(Postponed { a, b, where_: where_.to_string() }));
                self.trail.push(Undo::Postponed);
                Ok(())
            }
            Step::Differ => Err(self.size_mismatch(a, b, where_)),
        }
    }

    /// What the size equation `a = b` (as polynomials `pa`, `pb`) calls for now.
    fn size_step(&self, pa: &Poly, pb: &Poly, a: Type, b: Type) -> Step {
        if pa == pb {
            return Step::Equal;
        }
        let (l, r) = cancel(pa, pb);
        let meta = |p: &Poly, other: &Poly| {
            lone_var(p).filter(|&v| self.is_unbound(v) && !poly_has_var(other, v))
        };
        // The solution is the other side as written when nothing was cancelled
        // from it, so a message shows the size the user wrote.
        let value = |side: &Poly, whole: &Poly, written: Type| match side == whole {
            true => written,
            false => self.reify(side),
        };
        match (meta(&l, &r), meta(&r, &l)) {
            // A kept variable is bound last (see `Unifier::keeping`).
            (Some(v), Some(w)) if self.keep.contains(&v) && !self.keep.contains(&w) => {
                Step::Bind(w, value(&l, pa, a))
            }
            (Some(v), _) => Step::Bind(v, value(&r, pb, b)),
            (None, Some(w)) => Step::Bind(w, value(&l, pa, a)),
            (None, None) if self.has_meta(&l) || self.has_meta(&r) => Step::Postpone,
            (None, None) => Step::Differ,
        }
    }

    fn is_unbound(&self, v: VarId) -> bool {
        matches!(self.vars[v as usize], VarState::Unbound { .. })
    }

    fn has_meta(&self, p: &Poly) -> bool {
        p.iter().any(|(_, m)| m.iter().any(|&v| self.is_unbound(v)))
    }

    /// A polynomial as a size: `Nat`, `Var`, and `+`/`*` of them.
    fn reify(&self, p: &Poly) -> Type {
        let term = |(c, m): &(u64, Vec<VarId>)| {
            let vars = m.iter().map(|&v| self.types.var(v));
            let product = vars.reduce(|x, y| self.types.add(TypeNode::NatMul(x, y)));
            match (product, *c) {
                (None, c) => self.types.nat(c),
                (Some(t), 1) => t,
                (Some(t), c) => self.types.add(TypeNode::NatMul(self.types.nat(c), t)),
            }
        };
        p.iter()
            .map(term)
            .reduce(|x, y| self.types.add(TypeNode::NatAdd(x, y)))
            .unwrap_or_else(|| self.types.nat(0))
    }

    fn size_mismatch(&self, a: Type, b: Type, where_: &str) -> Diagnostic {
        let (a, b) = if self.found_first { (b, a) } else { (a, b) };
        let shown = self.show_all(&[a, b]);
        Diagnostic::error(
            Code::TypeMismatch,
            Span::at(0),
            0,
            format!("size mismatch {where_}: expected `{}`, found `{}`", shown[0], shown[1]),
        )
    }

    /// Retry the postponed size equations after a binding, until none moves.
    /// A binding one of them makes wakes nothing itself: this loop sees it.
    /// Postponed row equations wake the same way. See Note [Size patterns].
    /// See Note [Effect label variables].
    pub(super) fn wake(&mut self) -> Result<()> {
        if self.waking || (self.postponed.iter().all(Option::is_none) && !self.rows_postponed()) {
            return Ok(());
        }
        self.waking = true;
        let r = self.wake_sizes_and_rows();
        self.waking = false;
        r
    }

    fn wake_sizes_and_rows(&mut self) -> Result<()> {
        loop {
            self.wake_all()?;
            if !self.wake_rows()? {
                return Ok(());
            }
        }
    }

    fn wake_all(&mut self) -> Result<()> {
        loop {
            let mut progress = false;
            for i in 0..self.postponed.len() {
                let Some(c) = self.postponed[i].clone() else { continue };
                let (pa, pb) = (self.normalize_size(c.a), self.normalize_size(c.b));
                let step = self.size_step(&pa, &pb, c.a, c.b);
                if let Step::Postpone = step {
                    continue;
                }
                self.postponed[i] = None;
                self.trail.push(Undo::Woken(i, c.clone()));
                progress = true;
                match step {
                    Step::Equal | Step::Postpone => {}
                    Step::Bind(v, t) => self.bind(v, t)?,
                    Step::Differ => return Err(self.size_mismatch(c.a, c.b, &c.where_)),
                }
            }
            if !progress {
                return Ok(());
            }
        }
    }

    /// The first size equation still postponed, as an error, after dropping
    /// them all. Run where a definition is done: what is left has no unique
    /// solution. See Note [Size patterns].
    pub fn unsolved_size(&mut self) -> Option<Diagnostic> {
        let mut first = None;
        for i in 0..self.postponed.len() {
            if let Some(c) = self.postponed[i].take() {
                self.trail.push(Undo::Woken(i, c.clone()));
                first.get_or_insert(c);
            }
        }
        let c = first?;
        let shown = self.show_all(&[c.a, c.b]);
        Some(
            Diagnostic::error(
                Code::TypeMismatch,
                Span::at(0),
                0,
                format!("cannot solve the size equation `{} = {}` {}", shown[0], shown[1], c.where_),
            )
            .with_note("a size is inferred only when one side is a single unknown once equal terms cancel")
            .with_help("write the sizes in a type annotation"),
        )
    }

    /// The variables the postponed size equations mention, which must stay
    /// unification variables until they are solved.
    pub fn postponed_vars(&self, out: &mut std::collections::HashSet<VarId>) {
        for c in self.postponed.iter().flatten() {
            self.collect_vars(c.a, out);
            self.collect_vars(c.b, out);
        }
    }

    /// A size's value when it has no variables left (`2 + 3` is 5).
    pub fn nat_value(&self, ty: Type) -> Option<u64> {
        match self.whnf(ty) {
            Whnf::Size(p) => match p.as_slice() {
                [] => Some(0),
                [(k, vars)] if vars.is_empty() => Some(*k),
                _ => None,
            },
            Whnf::Node(_) | Whnf::Level => None,
        }
    }

    /// Normalize a size to a canonical polynomial over Z/2^64: a sorted list of
    /// `(coefficient, sorted variable monomial)` terms, like terms combined, zero
    /// terms dropped. Bound variables are followed, so equality is decidable and
    /// `n + m` and `m + n` share a normal form.
    /// A size as a sum of `(coefficient, variables multiplied)` terms, each
    /// variable as a type.
    pub fn size_poly(&self, ty: Type) -> Vec<(u64, Vec<Type>)> {
        self.normalize_size(ty)
            .into_iter()
            .map(|(k, vars)| (k, vars.into_iter().map(|v| self.types.add(TypeNode::Var(v))).collect()))
            .collect()
    }

    pub(super) fn normalize_size(&self, ty: Type) -> Poly {
        match self.head(ty) {
            TypeNode::Nat(k) => canon(vec![(k, vec![])]),
            TypeNode::Var(id) => vec![(1, vec![id])],
            TypeNode::NatAdd(a, b) => {
                let mut t = self.normalize_size(a);
                t.extend(self.normalize_size(b));
                canon(t)
            }
            TypeNode::NatMul(a, b) => poly_mul(&self.normalize_size(a), &self.normalize_size(b)),
            _ => Vec::new(),
        }
    }
}

/// A size normalized to a polynomial over Z/2^64: `(coefficient, sorted variable
/// monomial)` terms, canonical (like terms combined, zeros dropped, sorted), so
/// structural equality decides size equality (`n + m` and `m + n` share a form).
pub(super) type Poly = Vec<(u64, Vec<VarId>)>;

/// A size equation that is not a pattern yet (`n + m = 5`), kept until a
/// binding elsewhere makes it one. See Note [Size patterns].
#[derive(Clone)]
pub(super) struct Postponed {
    a: Type,
    b: Type,
    where_: String,
}

/// What a size equation calls for. See [`Unifier::size_step`].
enum Step {
    Equal,
    Bind(VarId, Type),
    Postpone,
    Differ,
}

/// Cancel the common part of two canonical polynomials: what is left of each
/// side, with positive coefficients and no monomial on both.
fn cancel(a: &Poly, b: &Poly) -> (Poly, Poly) {
    let (mut l, mut r) = (Vec::new(), Vec::new());
    let (mut i, mut j) = (0, 0);
    loop {
        match (a.get(i), b.get(j)) {
            (Some((ca, ma)), Some((cb, mb))) if ma == mb => {
                if ca > cb {
                    l.push((ca - cb, ma.clone()));
                } else if cb > ca {
                    r.push((cb - ca, mb.clone()));
                }
                i += 1;
                j += 1;
            }
            (Some(x), Some(y)) if x.1 < y.1 => {
                l.push(x.clone());
                i += 1;
            }
            (Some(x), None) => {
                l.push(x.clone());
                i += 1;
            }
            (_, Some(y)) => {
                r.push(y.clone());
                j += 1;
            }
            (None, None) => return (l, r),
        }
    }
}

/// Canonicalize: sort each monomial, combine like terms (wrapping add), drop zeros.
fn canon(mut terms: Poly) -> Poly {
    for (_, m) in terms.iter_mut() {
        m.sort_unstable();
    }
    terms.sort_by(|a, b| a.1.cmp(&b.1));
    let mut out: Poly = Vec::new();
    for (c, m) in terms {
        match out.last_mut() {
            Some(last) if last.1 == m => last.0 = last.0.wrapping_add(c),
            _ => out.push((c, m)),
        }
    }
    out.retain(|(c, _)| *c != 0);
    out
}

fn poly_mul(a: &Poly, b: &Poly) -> Poly {
    let mut terms: Poly = Vec::new();
    for (ca, ma) in a {
        for (cb, mb) in b {
            let mut m = ma.clone();
            m.extend(mb.iter().copied());
            terms.push((ca.wrapping_mul(*cb), m));
        }
    }
    canon(terms)
}

/// The single variable of a bare-variable polynomial `1*v`, else None.
fn lone_var(p: &Poly) -> Option<VarId> {
    match p.as_slice() {
        [(1, m)] if m.len() == 1 => Some(m[0]),
        _ => None,
    }
}

fn poly_has_var(p: &Poly, v: VarId) -> bool {
    p.iter().any(|(_, m)| m.contains(&v))
}

