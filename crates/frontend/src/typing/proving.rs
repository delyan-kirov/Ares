//! Proposition fields of `@ctx`, and the hypotheses that prove them (#540).
//!
//! A `@ctx` field whose type is a proposition (`ok: i < n`) is proved at each
//! use, not searched for: by evaluation, or from the hypotheses in scope
//! there. A proof is erased, so the field travels in the instance bundle as
//! `{}`. See Note [Proving propositions].
//!
//! Entry points: [`Checker::prove`] (a field at a use), [`Checker::branch_fact`]
//! and [`Checker::arm_facts`] (what a branch establishes),
//! [`Checker::hypotheses_in_scope`].

use super::propositions::Static;
use super::*;
use crate::parser::data::Arm;
use crate::typing::types::BoolOp;

// Note [Proving propositions]
//
// A proposition field is a goal at each use of the definition that declares
// it, solved at the enclosing definition's boundary with the other `@ctx`
// fields, once inference has pinned the sizes it compares. The solver is
// deliberately small (automation is #549):
//
// - Evaluation: the goal's two sides unify, after folding the booleans in
//   them (`2 < 5` is `true`), without binding any variable.
// - Hypotheses: the binders in scope whose type is a proposition (the
//   definition's own proof fields, a proof parameter or `let`), and the facts
//   of the branches around the use: `c ~ true` in the then-branch of
//   `if c`, `c ~ false` in its else-branch, `s ~ k` in the arm `k` of a match
//   on `s`, the negation of the earlier literal arms in a catch-all one, and
//   `g ~ true` under a guard `if g`. Each counts only when the checker
//   evaluates its condition, so a branch on a run-time value adds nothing
//   (propositions over run-time values are #594).
//
// A hypothesis is read as literals: a boolean `b ~ true` splits at `&&`, a
// `b ~ false` at `||`, and `not` flips a literal. An equation of a size
// variable `n ~ e` is used by substituting `e` for `n` in the goal. The goal
// is then split the same way (`&&` needs both sides, `||` either), and each
// literal left must fold to its value or be a hypothesis. Contradictory
// hypotheses (`c` and `not c`, or one that folds to its opposite) prove
// anything, so a branch that cannot run needs no proof.

/// A proposition read as a literal: a boolean with the value it has, or an
/// equation between two values of another sort.
#[derive(Clone, Copy, Debug)]
enum Literal {
    Bool(Type, bool),
    Eq(Type, Type),
}

impl<'a> Checker<'a> {
    /// Whether `ty` is a proposition `a ~ b`, an alias of one included.
    pub(super) fn is_prop(&self, ty: Type) -> bool {
        self.unifier.types.prop_eq_sides(self.unifier.resolve(ty)).is_some()
    }

    /// The hypotheses in scope: the binders whose type is a proposition, the
    /// components of a bundle of contexts that are, and the branch facts.
    pub(super) fn hypotheses_in_scope(&self) -> Vec<Type> {
        let mut out = Vec::new();
        for scope in &self.scopes[1..] {
            for &t in scope.values() {
                let z = self.unifier.zonk(t);
                match self.unifier.types.node(z) {
                    TypeNode::Tuple(items) => {
                        out.extend(self.unifier.types.items(items).iter().copied().filter(|&p| self.is_prop(p)));
                    }
                    _ if self.is_prop(z) => out.push(z),
                    _ => {}
                }
            }
        }
        out.extend(self.hypotheses.iter().copied());
        out
    }

    /// Run `f` with `facts` assumed.
    pub(super) fn assuming<T>(&mut self, facts: impl IntoIterator<Item = Type>, f: impl FnOnce(&mut Self) -> T) -> T {
        let depth = self.hypotheses.len();
        self.hypotheses.extend(facts);
        let out = f(self);
        self.hypotheses.truncate(depth);
        out
    }

    /// The value `e` has for the checker, when it evaluates it: a size or a
    /// boolean built from the sizes in scope.
    fn static_value(&mut self, e: Aol<Expr>) -> Option<Static> {
        if !self.is_static_value(e) {
            return None;
        }
        let tvars = self.scoped_tvars.clone();
        let save = self.unifier.save();
        match self.static_of(e, &tvars, &[]) {
            Ok(s @ (Static::Size(_) | Static::Bool(_))) => Some(s),
            _ => {
                self.unifier.restore(save);
                None
            }
        }
    }

    /// The fact the branch of `if cond` taken when `cond` is `value`
    /// establishes, `cond ~ value`.
    // Rule [Frontend-Branch-Hypothesis]
    pub(super) fn branch_fact(&mut self, cond: Aol<Expr>, value: bool) -> Option<Type> {
        let Some(Static::Bool(b)) = self.static_value(cond) else { return None };
        let v = self.unifier.types.bool_lit(value);
        Some(self.unifier.types.prop_eq(b, v))
    }

    /// Remember the value a match lambda `f` applied on the spot to `x`
    /// matches, so its arms learn which value each matched.
    pub(super) fn note_piped_match(&mut self, f: Aol<Expr>, x: Aol<Expr>) {
        let Expr::Lambda { params, body } = *self.node(f) else { return };
        let [param] = self.ast.slice(params) else { return };
        let (&Pattern::Var(arg), Expr::Match { scrut, .. }) = (self.pnode(param.pat), self.node(body)) else { return };
        if !matches!(self.node(*scrut), Expr::Var { module: None, name } if *name == arg) {
            return;
        }
        if let Some(s) = self.static_value(x) {
            self.match_scruts.insert(body, s);
        }
    }

    /// The facts each arm of the match `m` on `scrut` establishes: `s ~ k`
    /// for a literal arm `k`, the negations of the earlier unguarded literal
    /// arms for a catch-all one, and `g ~ true` for a guard `if g`.
    // Rule [Frontend-Branch-Hypothesis]
    pub(super) fn arm_facts(&mut self, m: Aol<Expr>, scrut: Aol<Expr>, arms: Slice<Arm>) -> Vec<Vec<Type>> {
        let arms = self.ast.slice(arms).to_vec();
        let matched = match self.match_scruts.get(&m) {
            Some(&s) => Some(s),
            None => self.static_value(scrut),
        };
        let mut missed: Vec<Type> = Vec::new();
        let mut out = Vec::with_capacity(arms.len());
        for arm in arms {
            let mut facts = Vec::new();
            if let (Some(s), [p]) = (matched, self.ast.slice(arm.patterns)) {
                match (s, self.literal_of(*p, s)) {
                    (_, Some(k)) => {
                        let fact = self.unifier.types.prop_eq(s.ty(), k);
                        facts.push(fact);
                        if arm.guard.is_none() {
                            missed.push(self.differs(s, k));
                        }
                    }
                    _ if matches!(self.pnode(*p), Pattern::Wild | Pattern::Var(_)) => facts.extend(missed.iter().copied()),
                    _ => {}
                }
            }
            if let Some(g) = arm.guard {
                facts.extend(self.branch_fact(g, true));
            }
            out.push(facts);
        }
        out
    }

    /// The value a literal pattern `p` stands for, matched against `s`: a
    /// number against a size, `.True`/`.False` against a boolean.
    fn literal_of(&self, p: Aol<Pattern>, s: Static) -> Option<Type> {
        match (self.pnode(p), s) {
            (&Pattern::Int(k), Static::Size(_)) if k >= 0 => Some(self.unifier.types.nat(k as u64)),
            (&Pattern::Variant { tag, fields, .. }, Static::Bool(_)) if self.ast.slice(fields).is_empty() => match tag.as_str() {
                "True" => Some(self.unifier.types.bool_lit(true)),
                "False" => Some(self.unifier.types.bool_lit(false)),
                _ => None,
            },
            _ => None,
        }
    }

    /// The fact that `s` is not `k`.
    fn differs(&self, s: Static, k: Type) -> Type {
        let types = &self.unifier.types;
        let (b, v) = match s {
            Static::Bool(b) => (b, types.bool_op(BoolOp::Not, &[k])),
            _ => (types.bool_op(BoolOp::Eq, &[s.ty(), k]), types.bool_lit(false)),
        };
        types.prop_eq(b, v)
    }

    /// Prove the proposition field `field` of `fname`, `goal`, from the
    /// hypotheses of the use being resolved. See Note [Proving propositions].
    // Rule [Frontend-Prop-Field]
    pub(super) fn prove(&mut self, fname: StrId, field: Option<StrId>, goal: Type, rigid: &HashSet<VarId>) -> Result<CtxVal> {
        let goal = self.unifier.zonk(goal);
        let hyps: Vec<Type> = self.proving.1.iter().map(|&h| self.unifier.zonk(h)).collect();
        let mut facts = Vec::new();
        for &h in &hyps {
            facts.extend(self.literals(h));
        }
        let sub = self.equations(&facts);
        let subst = |this: &Self, t: Type| if sub.is_empty() { t } else { this.unifier.subst_vars(t, &sub) };
        let facts: Vec<Literal> = facts
            .into_iter()
            .map(|l| match l {
                Literal::Bool(b, v) => Literal::Bool(subst(self, b), v),
                Literal::Eq(a, b) => Literal::Eq(subst(self, a), subst(self, b)),
            })
            .collect();
        let (a, b) = self.unifier.types.prop_eq_sides(self.unifier.resolve(goal)).expect("a proposition");
        let (a, b) = (subst(self, a), subst(self, b));
        if self.same(a, b) || self.contradictory(&facts) || self.proves(&facts, a, b) {
            return Ok(CtxVal::Proof);
        }
        Err(self.unproved(fname, field, goal, subst(self, goal), &hyps, rigid))
    }

    /// `goal` read as literals, a boolean split at `&&` (or at `||` when it
    /// is false) and through `not`.
    fn literals(&self, prop: Type) -> Vec<Literal> {
        let Some((a, b)) = self.unifier.types.prop_eq_sides(self.unifier.resolve(prop)) else { return Vec::new() };
        let mut out = Vec::new();
        match (self.bool_value(a), self.bool_value(b)) {
            (_, Some(v)) => self.bool_literals(a, v, &mut out),
            (Some(v), None) => self.bool_literals(b, v, &mut out),
            (None, None) => out.push(Literal::Eq(a, b)),
        }
        out
    }

    fn bool_literals(&self, b: Type, v: bool, out: &mut Vec<Literal>) {
        let b = self.unifier.fold_bool(b).unwrap_or(b);
        match self.unifier.bool_op(b) {
            Some((BoolOp::Not, x)) => self.bool_literals(x[0], !v, out),
            Some((BoolOp::And, x)) if v => x.iter().for_each(|&y| self.bool_literals(y, true, out)),
            Some((BoolOp::Or, x)) if !v => x.iter().for_each(|&y| self.bool_literals(y, false, out)),
            _ => out.push(Literal::Bool(b, v)),
        }
    }

    /// The constant a boolean folds to.
    fn bool_value(&self, b: Type) -> Option<bool> {
        let b = self.unifier.fold_bool(b).unwrap_or(b);
        self.unifier.bool_const(b)
    }

    /// The equations among `facts` that name a size variable on one side,
    /// as a substitution for it.
    fn equations(&self, facts: &[Literal]) -> HashMap<VarId, Type> {
        let mut sub = HashMap::new();
        for l in facts {
            let Literal::Eq(a, b) = *l else { continue };
            for (x, e) in [(a, b), (b, a)] {
                if let TypeNode::Var(v) = self.unifier.types.node(self.unifier.resolve(x)) {
                    if self.unifier.is_size(x) && !sub.contains_key(&v) {
                        sub.insert(v, e);
                        break;
                    }
                }
            }
        }
        sub
    }

    /// Whether `facts` prove `a ~ b`: split a boolean side by its
    /// connectives, and find each literal left among the facts.
    fn proves(&mut self, facts: &[Literal], a: Type, b: Type) -> bool {
        match (self.bool_value(a), self.bool_value(b)) {
            (_, Some(v)) => self.proves_bool(facts, a, v),
            (Some(v), None) => self.proves_bool(facts, b, v),
            (None, None) => facts.iter().any(|l| match *l {
                Literal::Eq(x, y) => (self.same(x, a) && self.same(y, b)) || (self.same(x, b) && self.same(y, a)),
                Literal::Bool(..) => false,
            }),
        }
    }

    fn proves_bool(&mut self, facts: &[Literal], b: Type, v: bool) -> bool {
        let b = self.unifier.fold_bool(b).unwrap_or(b);
        if let Some(c) = self.unifier.bool_const(b) {
            return c == v;
        }
        match self.unifier.bool_op(b) {
            Some((BoolOp::Not, x)) => self.proves_bool(facts, x[0], !v),
            Some((op @ (BoolOp::And | BoolOp::Or), x)) => {
                let (l, r) = (self.proves_bool(facts, x[0], v), self.proves_bool(facts, x[1], v));
                if (op == BoolOp::And) == v { l && r } else { l || r }
            }
            _ => facts.iter().any(|l| matches!(*l, Literal::Bool(h, w) if w == v && self.same(h, b))),
        }
    }

    /// Whether some fact folds to its opposite, or two facts give one
    /// boolean both values.
    fn contradictory(&mut self, facts: &[Literal]) -> bool {
        for (i, l) in facts.iter().enumerate() {
            let Literal::Bool(b, v) = *l else { continue };
            if self.bool_value(b) == Some(!v) {
                return true;
            }
            if facts[i + 1..].iter().any(|m| matches!(*m, Literal::Bool(c, w) if w != v && self.same(b, c))) {
                return true;
            }
        }
        false
    }

    /// Whether two values are one by conversion, binding no variable.
    fn same(&mut self, a: Type, b: Type) -> bool {
        let mut closed = HashSet::new();
        self.unifier.collect_vars(a, &mut closed);
        self.unifier.collect_vars(b, &mut closed);
        let save = self.unifier.save();
        let ok = self.unifier.unify(a, b, "proving a proposition").is_ok() && self.keeps_open(&closed);
        self.unifier.restore(save);
        ok
    }

    /// A proposition field the hypotheses do not prove: the goal, what it
    /// computes to, and the hypotheses tried.
    fn unproved(&self, fname: StrId, field: Option<StrId>, goal: Type, reduced: Type, hyps: &[Type], rigid: &HashSet<VarId>) -> Diagnostic {
        let fold = |t: Type| self.unifier.fold_bool(t).unwrap_or(t);
        // A boolean standing for `b ~ true` computes to what `b` does.
        let reduced = match self.unifier.types.prop_eq_sides(self.unifier.resolve(reduced)) {
            Some((a, b)) if self.unifier.bool_const(b) == Some(true) && self.unifier.bool_const(fold(a)).is_some() => fold(a),
            Some((a, b)) => self.unifier.types.prop_eq(fold(a), fold(b)),
            None => reduced,
        };
        let names = self.proving.0.map(|d| self.sig_names(d)).unwrap_or_default();
        let mut shown = self.unifier.show_all_named(&[goal, reduced], names.clone());
        let (goal_s, reduced_s) = (shown.remove(0), shown.remove(0));
        let what = match field {
            Some(f) => format!("the `@ctx` field `{f}` of `{fname}`"),
            None => format!("a `@ctx` field of `{fname}`"),
        };
        let mut d = diag!(
            Code::TypeMismatch, Span::at(0), 0,
            "cannot prove `{goal_s}`, {what}"
        );
        if reduced_s != goal_s {
            d = d.with_note(format!("it computes to `{reduced_s}`"));
        }
        let mut open = HashSet::new();
        self.unifier.collect_vars(goal, &mut open);
        if open.iter().any(|v| self.unifier.is_free(*v) && !rigid.contains(v) && !names.contains_key(v)) {
            d = d.with_note("a value it compares is not determined here");
        }
        d = match hyps {
            [] => d.with_note("no hypothesis is in scope"),
            _ => {
                let shown: Vec<String> = self.unifier.show_all_named(hyps, names).into_iter().map(|h| format!("`{h}`")).collect();
                d.with_note(format!("hypotheses in scope: {}", shown.join(", ")))
            }
        };
        // A goal over no variable is decided: a test would only take the
        // branch that cannot run.
        if open.is_empty() {
            return d;
        }
        let field = field.map_or("field".to_string(), |f| f.as_str().to_string());
        d.with_help(format!(
            "test it first, as in `if {goal_s} => ... else ...`, or pass a proof as `@ctx {{.{field} = ...}}`"
        ))
    }
}
