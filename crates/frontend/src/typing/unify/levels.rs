//! Universe levels: the `n` of `@Type n`, and their equality.
//!
//! A level is a constant, a level variable, `l + n`, or `@max a b`. Every
//! level has a normal form `max(c, v1 + k1, ..., vn + kn)`: a constant and at
//! most one offset per variable, sorted by variable. Two levels are equal when
//! their normal forms are. A level variable stands for a level of 1 or more
//! (#538: `@Type 0` holds propositions, and only an explicit `n >= 0` opts a
//! variable into it), so a constant no larger than every variable term is
//! dropped: `@max 1 u` is `u`. See Note [Universe levels].
//!
//! Evaluating a level is the level case of `Unifier::whnf`, so levels are
//! compared by the same normaliser as every other type.
//!
//! Entry points: [`Unifier::fresh_universe`], [`Unifier::level_leq`]; plain
//! [`Unifier::unify`] comes here when both normal forms are levels.

use utilities::{Code, Diagnostic, Result, Span};

use std::collections::{HashMap, HashSet};

use super::{Undo, Unifier, VarState};
use crate::typing::types::{Type, TypeNode, VarId};

// Note [Universe levels]
//
// The checker keeps universes as types: `@Type l` is `App(Con @Type, l)`,
// with `l` a level term. A bare `@Type` in a written type is `@Type v` for a
// fresh level variable `v`, which a definition's scheme generalises like any
// other variable, so each use of a definition picks its own levels.
//
// Levels form their own kind beside types and sizes. They are compared by
// normal form (`LevelNf`), as sizes are by polynomial: `@max u (u + 1)` and
// `u + 1` are one level. A lone variable on one side binds to the other
// side, and `v + k` against a constant `c > k` binds `v` to `c - k`; any
// other equation of different normal forms is a mismatch.

/// A level in normal form: `max(konst, v + k, ...)`, one term per variable,
/// sorted by variable.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct LevelNf {
    pub konst: u32,
    pub vars: Vec<(VarId, u32)>,
}

impl LevelNf {
    fn constant(konst: u32) -> LevelNf {
        LevelNf { konst, vars: Vec::new() }
    }

    fn shift(mut self, n: u32) -> LevelNf {
        self.konst += n;
        for (_, k) in &mut self.vars {
            *k += n;
        }
        self.tidy()
    }

    fn max(mut self, other: LevelNf) -> LevelNf {
        self.konst = self.konst.max(other.konst);
        for (v, k) in other.vars {
            match self.vars.iter_mut().find(|(w, _)| *w == v) {
                Some((_, j)) => *j = (*j).max(k),
                None => self.vars.push((v, k)),
            }
        }
        self.vars.sort_unstable();
        self.tidy()
    }

    /// Drop a constant every variable term already reaches: each variable is
    /// at least 1, so `v + k` is at least `k + 1`.
    fn tidy(mut self) -> LevelNf {
        if self.vars.iter().any(|(_, k)| self.konst <= k + 1) {
            self.konst = 0;
        }
        self
    }

    /// The level's value when it has no variable.
    pub fn ground(&self) -> Option<u32> {
        self.vars.is_empty().then_some(self.konst)
    }
}

impl Unifier {
    /// The universe `@Type v` for a fresh level variable `v`: what a bare
    /// `@Type` stands for.
    pub fn fresh_universe(&mut self) -> Type {
        let level = self.fresh();
        self.types.universe(level)
    }

    /// The normal form of a level. An unbound variable is an atom.
    pub fn normalize_level(&self, ty: Type) -> LevelNf {
        match self.head(ty) {
            TypeNode::Level(n) => LevelNf::constant(n),
            TypeNode::LevelAdd(l, n) => self.normalize_level(l).shift(n),
            TypeNode::LevelMax(a, b) => self.normalize_level(a).max(self.normalize_level(b)),
            TypeNode::Var(v) => LevelNf { konst: 0, vars: vec![(v, 0)] },
            other => unreachable!("normalize_level on a non-level: {other:?}"),
        }
    }

    /// The level term of a normal form.
    pub fn level_of_nf(&self, nf: &LevelNf) -> Type {
        let mut terms = Vec::new();
        if nf.konst > 0 || nf.vars.is_empty() {
            terms.push(self.types.add(TypeNode::Level(nf.konst)));
        }
        for &(v, k) in &nf.vars {
            let var = self.types.add(TypeNode::Var(v));
            terms.push(if k == 0 { var } else { self.types.add(TypeNode::LevelAdd(var, k)) });
        }
        terms
            .into_iter()
            .reduce(|a, b| self.types.add(TypeNode::LevelMax(a, b)))
            .expect("a level has a term")
    }

    /// Unify two levels by normal form. See Note [Universe levels].
    pub(super) fn unify_level(&mut self, a: Type, b: Type, where_: &str) -> Result<()> {
        let (na, nb) = (self.normalize_level(a), self.normalize_level(b));
        if na == nb {
            return Ok(());
        }
        for (lone, other, other_ty) in [(&na, &nb, b), (&nb, &na, a)] {
            match (lone.konst, lone.vars.as_slice()) {
                (0, &[(v, 0)]) if !other.vars.iter().any(|(w, _)| *w == v) => {
                    return self.bind(v, other_ty);
                }
                (0, &[(v, k)]) => {
                    if let Some(c) = other.ground().filter(|c| *c > k) {
                        let level = self.types.add(TypeNode::Level(c - k));
                        return self.bind(v, level);
                    }
                }
                _ => {}
            }
        }
        // An equation unification cannot solve, `@max u v = @max x y`, holds
        // when each side is at most the other; the definition settles both.
        if !(na.vars.is_empty() && nb.vars.is_empty()) {
            self.constrain_level(a, b, None);
            self.constrain_level(b, a, None);
            return Ok(());
        }
        let (expected, found) = if self.found_first { (b, a) } else { (a, b) };
        Err(Diagnostic::error(
            Code::TypeMismatch,
            Span::at(0),
            0,
            format!("universe level mismatch {where_}: expected {}, found {}", self.show(expected), self.show(found)),
        ))
    }

    /// Whether `a <= b` for every value of the variables (each at least 1).
    pub fn level_leq(&self, a: &LevelNf, b: &LevelNf) -> bool {
        let konst_ok = a.konst <= b.konst || b.vars.iter().any(|(_, k)| a.konst <= k + 1);
        konst_ok && a.vars.iter().all(|(v, k)| b.vars.iter().any(|(w, j)| v == w && k <= j))
    }
}

// ## Level constraints
//
// Note [Level constraints]
//
// Universes are not cumulative, as in the kernel (#487) and CC^obs: a type
// lives in exactly one universe, so `@Int` is in `@Type 1` and `@Type 1` in
// `@Type 2`, and nowhere else. A type used as a value, `@Int` in `f @Int`,
// has the type `@Type (level @Int)`. A type variable bound by
// `@ctx {t: @Type u}` or `(t: @Type u)` carries its level `u`, and binding
// it to a type `X` equates `level(X)` with `u`. What a bare `@Type` gives
// instead is polymorphism: its level is a fresh variable each use chooses.
//
// Most level equations are solved by unification.
// See Note [Universe levels].
// One it cannot solve, `@max u v = @max x y`, waits as two constraints, each
// side at most the other, in `level_le`. Each definition settles its own
// when it is checked (`settle_levels`): a constraint that holds for every value of
// its variables is dropped, a level variable the definition's type does not
// mention takes its least solution, and a constraint left false, or a set
// with no solution, is an error at that definition. What remains mentions
// the definition's own level variables: generalising them moves it into
// `scheme_le`, and instantiating the scheme emits a copy, so a use is
// checked against the levels the definition needs.

/// A pending `lhs <= rhs` between two levels, with where it came from.
#[derive(Clone, Copy, Debug)]
pub struct LevelLe {
    pub lhs: Type,
    pub rhs: Type,
    pub span: Option<Span>,
}

impl Unifier {
    /// The level a type variable stands at, if it was bound with one.
    pub fn var_level(&self, id: VarId) -> Option<Type> {
        self.var_levels.get(&id).copied()
    }

    /// Record that the type variable `ty` ranges over `@Type level`.
    pub fn set_var_level(&mut self, ty: Type, level: Type) {
        if let TypeNode::Var(id) = self.head(ty) {
            if self.var_levels.insert(id, level).is_none() {
                self.trail.push(Undo::VarLevel(id));
            }
        }
    }

    /// Require `lhs <= rhs`. See Note [Level constraints].
    pub fn constrain_level(&mut self, lhs: Type, rhs: Type, span: Option<Span>) {
        self.level_le.push(LevelLe { lhs, rhs, span });
        self.trail.push(Undo::LevelLe);
    }

    /// How many constraints wait, to settle those a definition adds.
    pub fn level_mark(&self) -> usize {
        self.level_le.len()
    }

    /// The level of the universe `ty` lives in: 1 for a data type, `l + 1`
    /// for `@Type l`, the largest of the parts for a function, tuple or
    /// record, and a variable's own level (a fresh one, from now on its own,
    /// when it has none).
    pub fn level_of(&mut self, ty: Type) -> Type {
        let one = self.types.add(TypeNode::Level(1));
        let ty = self.resolve(ty);
        if let Some(l) = self.types.universe_level(ty) {
            return self.types.add(TypeNode::LevelAdd(l, 1));
        }
        let parts: Vec<Type> = match self.types.node(ty) {
            TypeNode::Var(id) if self.is_nat_var(id) => return one,
            TypeNode::Var(id) => {
                if let Some(l) = self.var_level(id) {
                    return l;
                }
                let l = self.fresh();
                self.set_var_level(ty, l);
                return l;
            }
            TypeNode::App(..) => {
                let mut parts = Vec::new();
                let mut cur = ty;
                while let TypeNode::App(head, arg) = self.types.node(self.resolve(cur)) {
                    if !self.is_size(arg) {
                        parts.push(arg);
                    }
                    cur = head;
                }
                parts
            }
            TypeNode::Arrow(from, to, _) => vec![from, to],
            TypeNode::Tuple(items) => self.types.items(items).to_vec(),
            TypeNode::Record(row) => {
                let mut parts = Vec::new();
                let mut cur = row;
                while let TypeNode::RowField(_, t, rest) = self.head(cur) {
                    parts.push(t);
                    cur = rest;
                }
                parts
            }
            _ => return one,
        };
        let levels: Vec<Type> = parts.into_iter().map(|p| self.level_of(p)).collect();
        levels.into_iter().fold(one, |acc, l| self.types.add(TypeNode::LevelMax(acc, l)))
    }

    fn is_size(&self, ty: Type) -> bool {
        match self.head(ty) {
            TypeNode::Nat(_) | TypeNode::NatAdd(..) | TypeNode::NatMul(..) => true,
            TypeNode::Var(id) => self.is_nat_var(id),
            _ => false,
        }
    }

    /// A binding `id := ty` of a type variable with a level puts `ty` at
    /// that level. See Note [Level constraints].
    pub(super) fn bind_level(&mut self, id: VarId, ty: Type) -> Result<()> {
        let Some(level) = self.var_level(id) else { return Ok(()) };
        match self.head(ty) {
            TypeNode::Var(other) if self.var_level(other).is_none() && !self.is_nat_var(other) => {
                let other = self.types.add(TypeNode::Var(other));
                self.set_var_level(other, level);
                Ok(())
            }
            _ => {
                let own = self.level_of(ty);
                self.unify(level, own, "in the universe of a type variable")
            }
        }
    }

    /// Every variable `ty` mentions, with the levels of its type variables.
    pub fn vars_with_levels(&self, ty: Type, out: &mut HashSet<VarId>) {
        let mut found = HashSet::new();
        self.collect_vars(ty, &mut found);
        for id in found {
            if out.insert(id) {
                if let Some(l) = self.var_level(id) {
                    self.vars_with_levels(l, out);
                }
            }
        }
    }

    /// Drop the constraints added since `mark`, once settled for a
    /// declaration that has no scheme to keep them. Settling happens between
    /// definitions, never inside a trial, so it leaves no undo entry.
    pub fn forget_levels(&mut self, mark: usize) {
        self.level_le.truncate(mark);
    }

    /// Settle the constraints added since `mark`, for a definition whose
    /// types mention the variables `keep`. See Note [Level constraints]. The
    /// error is the constraint that cannot hold, shown as `(lhs, rhs)`.
    pub fn settle_levels(&mut self, mark: usize, keep: &HashSet<VarId>) -> std::result::Result<(), (LevelLe, String, String)> {
        loop {
            self.drop_provable(mark);
            if !self.solve_internal(mark, keep) {
                break;
            }
        }
        for c in self.level_le[mark..].to_vec() {
            let (l, r) = (self.normalize_level(c.lhs), self.normalize_level(c.rhs));
            if l.ground().is_some() && r.ground().is_some() && !self.level_leq(&l, &r) {
                return Err((c, self.show(c.lhs), self.show(c.rhs)));
            }
        }
        if let Some(c) = self.unsatisfiable(mark) {
            return Err((c, self.show(c.lhs), self.show(c.rhs)));
        }
        Ok(())
    }

    fn drop_provable(&mut self, mark: usize) {
        let kept: Vec<LevelLe> = self.level_le[mark..]
            .iter()
            .copied()
            .filter(|c| !self.level_leq(&self.normalize_level(c.lhs), &self.normalize_level(c.rhs)))
            .collect();
        self.level_le.truncate(mark);
        self.level_le.extend(kept);
    }

    /// Give each variable the definition's types do not mention its least
    /// solution: the largest of the levels below it, or 1. Only a variable
    /// that stands alone on every right side it appears on is solved.
    /// Whether one was.
    fn solve_internal(&mut self, mark: usize, keep: &HashSet<VarId>) -> bool {
        let cs: Vec<(LevelNf, LevelNf, LevelLe)> = self.level_le[mark..]
            .iter()
            .map(|c| (self.normalize_level(c.lhs), self.normalize_level(c.rhs), *c))
            .collect();
        let mut candidates: Vec<VarId> = cs.iter().flat_map(|(l, r, _)| l.vars.iter().chain(&r.vars).map(|(v, _)| *v)).collect();
        candidates.sort_unstable();
        candidates.dedup();
        for v in candidates {
            if keep.contains(&v) || !matches!(self.vars[v as usize], VarState::Unbound { level } if level >= self.level) {
                continue;
            }
            let lone = |r: &LevelNf| r.konst == 0 && r.vars == [(v, 0)];
            let on_right: Vec<&(LevelNf, LevelNf, LevelLe)> = cs.iter().filter(|(_, r, _)| r.vars.iter().any(|(w, _)| *w == v)).collect();
            if on_right.iter().any(|(l, r, _)| !lone(r) || l.vars.iter().any(|(w, _)| *w == v)) {
                continue;
            }
            let least = on_right.iter().fold(LevelNf { konst: 1, vars: Vec::new() }, |acc, (l, _, _)| acc.max(l.clone()));
            let term = self.level_of_nf(&least);
            if self.bind(v, term).is_ok() {
                return true;
            }
        }
        false
    }

    /// A constraint of the set added since `mark` that no values of its
    /// variables satisfy, found by raising variables from 1 until every
    /// constraint holds or one keeps climbing.
    fn unsatisfiable(&self, mark: usize) -> Option<LevelLe> {
        let cs: Vec<(LevelNf, LevelNf, LevelLe)> = self.level_le[mark..]
            .iter()
            .map(|c| (self.normalize_level(c.lhs), self.normalize_level(c.rhs), *c))
            .collect();
        let mut value: HashMap<VarId, u64> = HashMap::new();
        let eval = |nf: &LevelNf, value: &HashMap<VarId, u64>| {
            nf.vars.iter().map(|(v, k)| value.get(v).copied().unwrap_or(1) + *k as u64).fold(nf.konst as u64, u64::max)
        };
        let rounds = (cs.len() + 1) * (cs.len() + 2) + 2;
        for _ in 0..rounds {
            let mut changed = false;
            for (l, r, c) in &cs {
                let (lv, rv) = (eval(l, &value), eval(r, &value));
                if lv <= rv {
                    continue;
                }
                let Some((v, k)) = r.vars.iter().max_by_key(|(v, k)| value.get(v).copied().unwrap_or(1) + *k as u64) else {
                    return Some(*c);
                };
                value.insert(*v, lv - *k as u64);
                changed = true;
            }
            if !changed {
                return None;
            }
        }
        cs.iter().find(|(l, r, _)| eval(l, &value) > eval(r, &value)).map(|(_, _, c)| *c)
    }

    /// Move each waiting constraint whose variables are all generalised into
    /// the schemes' store, indexed by those variables.
    pub(super) fn attach_generic_constraints(&mut self) {
        let mut i = 0;
        while i < self.level_le.len() {
            let c = self.level_le[i];
            let mut vars = HashSet::new();
            self.collect_vars(c.lhs, &mut vars);
            self.collect_vars(c.rhs, &mut vars);
            if vars.is_empty() || !vars.iter().all(|v| matches!(self.vars[*v as usize], VarState::Generic)) {
                i += 1;
                continue;
            }
            self.level_le.remove(i);
            let at = self.scheme_le.len();
            self.scheme_le.push(c);
            for v in vars {
                self.scheme_le_by_var.entry(v).or_default().push(at);
            }
        }
    }

    /// Emit a copy of each scheme constraint whose variables `mapping`
    /// instantiated. See Note [Level constraints].
    pub(super) fn emit_scheme_constraints(&mut self, mapping: &mut HashMap<VarId, Type>) {
        let mut seen: Vec<usize> = mapping.keys().filter_map(|v| self.scheme_le_by_var.get(v)).flatten().copied().collect();
        seen.sort_unstable();
        seen.dedup();
        for i in seen {
            let c = self.scheme_le[i];
            let mut vars = HashSet::new();
            self.collect_vars(c.lhs, &mut vars);
            self.collect_vars(c.rhs, &mut vars);
            if !vars.iter().all(|v| mapping.contains_key(v)) {
                continue;
            }
            let (lhs, rhs) = (self.instantiate_with(c.lhs, mapping), self.instantiate_with(c.rhs, mapping));
            self.constrain_level(lhs, rhs, c.span);
        }
    }

    /// The scheme constraints whose variables `map` all covers, as
    /// `(lhs, rhs, span)`: those an imported scheme brings along.
    pub fn scheme_constraints_over(&self, map: &HashMap<VarId, Type>) -> Vec<(Type, Type, Option<Span>)> {
        let mut found: Vec<usize> = map.keys().filter_map(|v| self.scheme_le_by_var.get(v)).flatten().copied().collect();
        found.sort_unstable();
        found.dedup();
        found
            .into_iter()
            .map(|i| self.scheme_le[i])
            .filter(|c| {
                let mut vars = HashSet::new();
                self.collect_vars(c.lhs, &mut vars);
                self.collect_vars(c.rhs, &mut vars);
                vars.iter().all(|v| map.contains_key(v))
            })
            .map(|c| (c.lhs, c.rhs, c.span))
            .collect()
    }

    /// Keep `lhs <= rhs` over generalised variables with their scheme.
    pub fn add_scheme_constraint(&mut self, lhs: Type, rhs: Type, span: Option<Span>) {
        let mut vars = HashSet::new();
        self.collect_vars(lhs, &mut vars);
        self.collect_vars(rhs, &mut vars);
        let at = self.scheme_le.len();
        self.scheme_le.push(LevelLe { lhs, rhs, span });
        for v in vars {
            self.scheme_le_by_var.entry(v).or_default().push(at);
        }
    }
}
