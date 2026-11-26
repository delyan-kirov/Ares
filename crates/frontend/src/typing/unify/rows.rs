//! Row unification: records and effect rows as scoped-label rows.
//!
//! The algorithm is Leijen's, from "Extensible records with scoped labels" (TFP
//! 2005). A row is a chain of labelled entries ending in the empty row or a row
//! variable. To unify `l : t | r` with a row `s`, `rewrite_row` digs
//! `l` out of `s` (binding `s`'s tail to a fresh row with `l` added when the
//! label is absent and the tail is open), unifies the two `t`s, and unifies what
//! remains. Duplicate labels are kept, in order, which is what makes the labels
//! "scoped".
//!
//! Records use the same machinery over [`TypeNode::RowField`]; a nominal struct
//! meets a record row through its declared row. Effect rows add subsumption:
//! [`Unifier::subrow`] checks that one effect row's labels all appear in
//! another. See Note [Nominal struct / record row bridge].
//!
//! Entry points: [`Unifier::subrow`], [`Unifier::record_field`]; plain
//! [`Unifier::unify`] dispatches here for rows and records.


use utilities::{Code, Diagnostic, Result, Span, StrId};

use super::{Undo, Unifier, VarState};
use crate::typing::types::{Type, TypeNode, VarId, ERROR_CON};


// ## Records

impl Unifier {
    /// Register the structs' record-row schemes for the nominal-struct / record-row
    /// unification bridge (see the `struct_rows` map).
    pub fn set_struct_rows(&mut self, rows: std::collections::HashMap<StrId, (Vec<VarId>, Type)>) {
        self.struct_rows = rows;
    }

    /// Look up field `label` in a record type, growing an open tail to include it.
    pub fn record_field(&mut self, record: Type, label: impl Into<StrId>, where_: &str) -> Result<Type> {
        match self.head(record) {
            TypeNode::Record(row) => Ok(self.rewrite_field(row, label.into(), where_)?.0),
            _ => Ok(self.fresh()),
        }
    }

    // Note [Nominal struct / record row bridge]
    //
    // Ares has both nominal structs (`$ P : @Type = @struct x: @Int, y: @Int`) and
    // structural records (`{ x: @Int | r }`, a row). A function written against
    // a row should accept any struct with those fields, so a struct has to meet
    // a row somewhere, without the two kinds of type becoming one.
    //
    // They meet in unification and only there. Every struct registers its
    // fields as a closed row, quantified over the struct's parameters
    // (`Checker::register_struct_rows` into `struct_rows`). When unification
    // finds a record on one side and a struct type (a bare constructor or an
    // applied one) on the other, it instantiates that row with the struct's
    // arguments and unifies it with the record. Structs never unify with each
    // other this way: `P` and `Q` with the same fields stay different types. The
    // bridge is one-way per use, so nothing records that `P` "is" a record.

    /// If one side is a record row and the other a struct type (bare `Con` or an
    /// applied `App..(Con)`), unify the record against the struct's registered row
    /// with the struct's type arguments substituted for its parameters. Returns
    /// `None` when neither side bridges, so the caller reports a plain mismatch.
    /// See Note [Nominal struct / record row bridge].
    pub(super) fn struct_row_bridge(&mut self, a: Type, b: Type, where_: &str) -> Option<Result<()>> {
        let (spine, rec) = match (self.types.node(a), self.types.node(b)) {
            (TypeNode::Record(r), _) => (b, r),
            (_, TypeNode::Record(r)) => (a, r),
            _ => return None,
        };
        let mut args = Vec::new();
        let mut cur = spine;
        loop {
            match self.head(cur) {
                TypeNode::App(head, arg) => {
                    args.push(arg);
                    cur = head;
                }
                TypeNode::Con(name) => {
                    let (params, row) = self.struct_rows.get(&name)?.clone();
                    args.reverse();
                    let mut sub = std::collections::HashMap::new();
                    for (id, arg) in params.iter().zip(args.iter()) {
                        sub.insert(*id, *arg);
                    }
                    let row = self.subst_vars(row, &sub);
                    return Some(self.unify_record_row(row, rec, where_));
                }
                _ => return None,
            }
        }
    }

    /// A copy of `ty` with each variable in `sub` replaced by its mapped type. Used
    /// to instantiate a struct-row scheme's parameters at a bridge site; the stored
    /// scheme is never mutated, so each use is independent.
    pub(crate) fn subst_vars(&self, ty: Type, sub: &std::collections::HashMap<VarId, Type>) -> Type {
        match self.head(ty) {
            TypeNode::Var(id) => match sub.get(&id) {
                Some(t) => *t,
                None => self.types.add(TypeNode::Var(id)),
            },
            TypeNode::App(head, arg) => {
                let (h, a) = (self.subst_vars(head, sub), self.subst_vars(arg, sub));
                self.types.app(h, a)
            }
            TypeNode::NatAdd(a, b) => {
                let (x, y) = (self.subst_vars(a, sub), self.subst_vars(b, sub));
                self.types.add(TypeNode::NatAdd(x, y))
            }
            TypeNode::NatMul(a, b) => {
                let (x, y) = (self.subst_vars(a, sub), self.subst_vars(b, sub));
                self.types.add(TypeNode::NatMul(x, y))
            }
            TypeNode::LevelMax(a, b) => {
                let (x, y) = (self.subst_vars(a, sub), self.subst_vars(b, sub));
                self.types.add(TypeNode::LevelMax(x, y))
            }
            TypeNode::LevelAdd(l, n) => {
                let l = self.subst_vars(l, sub);
                self.types.add(TypeNode::LevelAdd(l, n))
            }
            TypeNode::Arrow(from, to, eff) => {
                let (f, t, e) = (
                    self.subst_vars(from, sub),
                    self.subst_vars(to, sub),
                    self.subst_vars(eff, sub),
                );
                self.types.arrow_eff(f, t, e)
            }
            TypeNode::Tuple(items) => {
                let items = self.types.items(items).to_vec();
                let mapped: Vec<Type> = items.into_iter().map(|t| self.subst_vars(t, sub)).collect();
                self.types.tuple(mapped)
            }
            TypeNode::RowExtend(label, args, rest) => {
                let (l, a, r) = (self.subst_vars(label, sub), self.subst_vars(args, sub), self.subst_vars(rest, sub));
                self.types.add(TypeNode::RowExtend(l, a, r))
            }
            TypeNode::Record(row) => {
                let r = self.subst_vars(row, sub);
                self.types.record(r)
            }
            TypeNode::RowField(label, fty, rest) => {
                let (f, r) = (self.subst_vars(fty, sub), self.subst_vars(rest, sub));
                self.types.add(TypeNode::RowField(label, f, r))
            }
            _ => self.resolve(ty), // Con or RowEmpty
        }
    }

    /// Unify two record types by unifying their rows.
    pub(super) fn unify_record(&mut self, a: Type, b: Type, where_: &str) -> Result<()> {
        self.unify_record_row(a, b, where_)
    }

    /// Unify two record rows (Leijen scoped-label discipline, plus field types):
    /// bring the head field of one row to the head of the other, unify the field
    /// types, then unify the tails. An open tail (a row variable) grows to accept a
    /// missing field, which is where row polymorphism comes from.
    pub(super) fn unify_record_row(&mut self, a: Type, b: Type, where_: &str) -> Result<()> {
        let a = self.resolve(a);
        let b = self.resolve(b);
        match (self.types.node(a), self.types.node(b)) {
            (TypeNode::RowEmpty, TypeNode::RowEmpty) => Ok(()),
            (TypeNode::Var(i), TypeNode::Var(j)) if i == j => Ok(()),
            (TypeNode::Var(i), _) => self.bind(i, b),
            (_, TypeNode::Var(j)) => self.bind(j, a),
            (TypeNode::RowField(label, fty, a_rest), _) => {
                let (b_fty, b_rest) = self.rewrite_field(b, label, where_)?;
                self.unify(fty, b_fty, where_)?;
                self.unify_record_row(a_rest, b_rest, where_)
            }
            // The other side ran out of fields but this one still wants `label`.
            (TypeNode::RowEmpty, TypeNode::RowField(label, ..)) => Err(self.field_missing(label, where_)),
            _ => Err(self.mismatch(a, b, where_)),
        }
    }

    /// Bring an occurrence of field `label` to the head of record `row`, returning
    /// its field type and the remaining row. An open tail grows to include the
    /// field (fresh field type); a closed row lacking it is a type error.
    pub(super) fn rewrite_field(&mut self, row: Type, label: StrId, where_: &str) -> Result<(Type, Type)> {
        match self.head(row) {
            TypeNode::RowField(l, fty, rest) => {
                if l == label {
                    Ok((fty, rest))
                } else {
                    let (found, deeper) = self.rewrite_field(rest, label, where_)?;
                    let rebuilt = self.types.add(TypeNode::RowField(l, fty, deeper));
                    Ok((found, rebuilt))
                }
            }
            TypeNode::Var(id) => {
                let fty = self.fresh();
                let tail = self.fresh();
                let ext = self.types.row_field(label, fty, tail);
                self.bind(id, ext)?;
                Ok((fty, tail))
            }
            _ => Err(self.field_missing(label, where_)),
        }
    }

    pub(super) fn field_missing(&self, label: StrId, where_: &str) -> Diagnostic {
        Diagnostic::error(
            Code::TypeMismatch,
            Span::at(0),
            0,
            format!("record has no field `{label}` {where_}"),
        )
    }
}


// ## Effect rows

// Note [Effect label variables]
//
// A row label is an effect, of kind `@Effect`, or a variable of that kind
// standing for one: `@ctx {l: @Effect, e: @Row} -> ... -> <l | e> a` (#585).
// A label variable stands for a whole effect, arguments included, so each one
// is elaborated with an arguments variable of its own that every occurrence
// shares; solving `l` to `State` unifies those with `State`'s.
//
// Unifying `<l | e>` with `<A, B | r>` has more than one solution (`l` is `A`,
// or `B`, or an effect of `r`), so a row equation is solved only while each
// step has one answer. Digging a label out of a row walks its entries: a
// label equal to the one sought matches, one surely different is skipped, and
// an unsolved label variable on either side, not the same variable, makes the
// step ambiguous. The equation is then postponed, and a later binding of one
// of its variables wakes it, as a size equation that is not a pattern waits.
// See Note [Size patterns].
// Two cases still have one answer and are solved at once: a label variable
// sought in a bare row variable extends that variable, and a closed row with
// one place left pins it: `l` sought in `<A>` is `A`, and `A` sought in
// `<B, l>` makes `l` be `A`. An equation still postponed when its definition
// is checked is an error that asks for the effect to be named,
// `f @ctx {.l = State}`.
//
// Inside the body of a definition, the label variables its signature binds
// are rigid (`rigid_labels`): an effect of the body's own, different from
// every other label, and never solved.

/// A row label as row unification compares it: an effect's name, or a label
/// variable.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum LabelKey {
    Name(StrId),
    Var(VarId),
}

/// A row equation waiting for a label variable.
/// See Note [Effect label variables].
#[derive(Clone)]
pub(crate) struct RowPostponed {
    a: Type,
    b: Type,
    /// `a` is a subrow of `b`, not equal to it.
    sub: bool,
    /// The variables whose binding may decide it: the label variables and
    /// open tails of both rows.
    vars: Vec<VarId>,
    where_: String,
}

impl Unifier {
    /// A fresh label variable, of kind `@Effect`.
    pub fn fresh_label(&mut self) -> Type {
        let t = self.fresh();
        if let TypeNode::Var(id) = self.types.node(t) {
            self.mark_label(id);
        }
        t
    }

    pub fn mark_label(&mut self, id: VarId) {
        if self.label_vars.insert(id) {
            self.trail.push(Undo::LabelVar(id));
        }
    }

    /// The arguments of the effect label variable `label` stands for, the
    /// same variable at every occurrence.
    pub fn label_args(&mut self, label: Type) -> Type {
        let TypeNode::Var(id) = self.head(label) else { return self.types.row_empty() };
        if let Some(&a) = self.label_args.get(&id) {
            return a;
        }
        let a = self.fresh();
        self.set_label_args(label, a);
        a
    }

    /// Give the label variable `label` the arguments variable `args`.
    pub fn set_label_args(&mut self, label: Type, args: Type) {
        if let TypeNode::Var(id) = self.head(label) {
            if self.label_args.insert(id, args).is_none() {
                self.trail.push(Undo::LabelArgs(id));
            }
        }
    }

    /// Unify the label variables at the same places of `a` and `b`, two
    /// elaborations of one signature, so that unifying them leaves no row
    /// equation between two unsolved label variables to wait.
    pub fn pair_labels(&mut self, a: Type, b: Type) -> Result<()> {
        match (self.head(a), self.head(b)) {
            (TypeNode::RowExtend(la, aa, ra), TypeNode::RowExtend(lb, ab, rb)) => {
                if self.is_label(la) && self.is_label(lb) && self.resolve(la) != self.resolve(lb) {
                    self.unify(aa, ab, "against the signature")?;
                    self.unify(la, lb, "against the signature")?;
                }
                self.pair_labels(ra, rb)
            }
            (TypeNode::Arrow(fa, ta, ea), TypeNode::Arrow(fb, tb, eb)) => {
                self.pair_labels(fa, fb)?;
                self.pair_labels(ta, tb)?;
                self.pair_labels(ea, eb)
            }
            (TypeNode::App(ha, xa), TypeNode::App(hb, xb)) => {
                self.pair_labels(ha, hb)?;
                self.pair_labels(xa, xb)
            }
            (TypeNode::Tuple(xs), TypeNode::Tuple(ys)) => {
                let (xs, ys) = (self.types.items(xs).to_vec(), self.types.items(ys).to_vec());
                for (x, y) in xs.into_iter().zip(ys) {
                    self.pair_labels(x, y)?;
                }
                Ok(())
            }
            (TypeNode::Record(ra), TypeNode::Record(rb)) => self.pair_labels(ra, rb),
            (TypeNode::RowField(_, ta, ra), TypeNode::RowField(_, tb, rb)) => {
                self.pair_labels(ta, tb)?;
                self.pair_labels(ra, rb)
            }
            _ => Ok(()),
        }
    }

    pub fn is_label_var(&self, id: VarId) -> bool {
        self.label_vars.contains(&id)
    }

    /// Whether `ty` is (resolves to) a label variable.
    pub fn is_label(&self, ty: Type) -> bool {
        matches!(self.head(ty), TypeNode::Var(id) if self.is_label_var(id))
    }

    /// Make the label variables among `labels` rigid, as a body sees those of
    /// its own signature, until [`Unifier::release_labels`]. Each shows by
    /// the name the signature gives it.
    pub fn hold_labels(&mut self, labels: impl IntoIterator<Item = (StrId, Type)>) {
        for (name, l) in labels {
            if let TypeNode::Var(id) = self.head(l) {
                if self.is_label_var(id) {
                    self.rigid_labels.insert(id, name);
                }
            }
        }
    }

    pub fn release_labels(&mut self) {
        self.rigid_labels.clear();
    }

    /// The key of a row label, and whether it is an unsolved label variable
    /// unification may still choose.
    fn label_key(&self, label: Type) -> (LabelKey, bool) {
        match self.head(label) {
            TypeNode::Var(id) => {
                let flexible = matches!(self.vars[id as usize], VarState::Unbound { .. }) && !self.rigid_labels.contains_key(&id);
                (LabelKey::Var(id), flexible)
            }
            TypeNode::Con(name) => (LabelKey::Name(name), false),
            _ => (LabelKey::Name(StrId::intern(ERROR_CON)), false),
        }
    }

    /// A label variable stands only for an effect or another label variable.
    pub(super) fn check_label_kind(&mut self, id: VarId, ty: Type) -> Result<()> {
        match self.head(ty) {
            TypeNode::Var(other) => {
                if self.is_label_var(id) {
                    self.mark_label(other);
                } else if self.is_label_var(other) {
                    self.mark_label(id);
                }
                Ok(())
            }
            TypeNode::Con(_) => Ok(()),
            _ if self.is_label_var(id) => Err(Diagnostic::error(
                Code::TypeMismatch,
                Span::at(0),
                0,
                format!("`{}` is a type, not an effect", self.show(ty)),
            )),
            _ => Ok(()),
        }
    }

    /// Unify two effect rows, at least one a `<label | rest>` extension (Leijen's
    /// scoped-label discipline): pull the head label of the extension out of the
    /// other row, then unify the remaining tails.
    pub(super) fn unify_row(&mut self, a: Type, b: Type, where_: &str) -> Result<()> {
        // Normalize so `a` is the extension we decompose.
        let (a, b) = if matches!(self.types.node(a), TypeNode::RowExtend(..)) {
            (a, b)
        } else {
            (b, a)
        };
        let TypeNode::RowExtend(label, a_args, a_rest) = self.types.node(a) else {
            unreachable!("unify_row without a row extension")
        };
        match self.rewrite_row(b, label, a_args, where_)? {
            Some(b_rest) => self.unify(a_rest, b_rest, where_),
            None => {
                self.postpone_row(a, b, false, where_);
                Ok(())
            }
        }
    }

    /// Bring an occurrence of effect `label` to the head of `row`, unify its
    /// arguments with `args`, and return the row that remains once it is
    /// removed. An open tail (a row variable) grows to accept the label. A closed
    /// row lacking the label is the unhandled-effect error. `None` when a label
    /// variable leaves more than one way to do it.
    /// See Note [Effect label variables].
    // Rule [Frontend-Effect-Label-Var]
    pub(super) fn rewrite_row(&mut self, row: Type, label: Type, args: Type, where_: &str) -> Result<Option<Type>> {
        let (want, flexible) = self.label_key(label);
        match self.head(row) {
            TypeNode::RowExtend(l, l_args, rest) => {
                let (have, have_flexible) = self.label_key(l);
                if have == want {
                    self.unify_effect_args(label, args, l_args, where_)?;
                    return Ok(Some(rest));
                }
                // The arguments first: binding a label variable reads them for
                // its level. See Note [Label variable levels].
                if flexible && !have_flexible && matches!(self.head(rest), TypeNode::RowEmpty) {
                    let LabelKey::Var(id) = want else { unreachable!("a flexible label is a variable") };
                    self.unify_effect_args(label, args, l_args, where_)?;
                    self.bind(id, l)?;
                    return Ok(Some(rest));
                }
                if have_flexible && !flexible && matches!(self.head(rest), TypeNode::RowEmpty) {
                    let LabelKey::Var(id) = have else { unreachable!("a flexible label is a variable") };
                    self.unify_effect_args(label, args, l_args, where_)?;
                    self.bind(id, label)?;
                    return Ok(Some(rest));
                }
                if flexible || have_flexible {
                    return Ok(None);
                }
                Ok(self
                    .rewrite_row(rest, label, args, where_)?
                    .map(|deeper| self.types.add(TypeNode::RowExtend(l, l_args, deeper))))
            }
            TypeNode::Var(id) => {
                let tail = self.fresh();
                let ext = self.types.add(TypeNode::RowExtend(label, args, tail));
                self.bind(id, ext)?;
                Ok(Some(tail))
            }
            _ => Err(self.effect_not_handled(label, where_)),
        }
    }

    /// Effect subsumption: require `sub` to be a subrow of `super_`. Every effect
    /// the callee performs (`sub`) must be permitted by the ambient (`super_`).
    pub fn subrow(&mut self, sub: Type, super_: Type, where_: &str) -> Result<()> {
        match self.head(sub) {
            TypeNode::RowEmpty => Ok(()),
            TypeNode::Var(_) => self.unify(sub, super_, where_),
            TypeNode::RowExtend(label, args, rest) => match self.rewrite_row(super_, label, args, where_)? {
                Some(super_rest) => self.subrow(rest, super_rest, where_),
                None => {
                    self.postpone_row(sub, super_, true, where_);
                    Ok(())
                }
            },
            _ => self.unify(sub, super_, where_),
        }
    }

    fn postpone_row(&mut self, a: Type, b: Type, sub: bool, where_: &str) {
        let mut vars = Vec::new();
        self.row_vars(a, &mut vars);
        self.row_vars(b, &mut vars);
        self.row_postponed.push(Some(RowPostponed { a, b, sub, vars, where_: where_.to_string() }));
        self.trail.push(Undo::RowPostponed);
    }

    /// The label variables and the open tail of `row`.
    fn row_vars(&self, row: Type, out: &mut Vec<VarId>) {
        let mut cur = row;
        loop {
            match self.head(cur) {
                TypeNode::RowExtend(l, _, rest) => {
                    if let TypeNode::Var(id) = self.head(l) {
                        out.push(id);
                    }
                    cur = rest;
                }
                TypeNode::Var(id) => {
                    out.push(id);
                    return;
                }
                _ => return,
            }
        }
    }

    /// Retry each postponed row equation one of whose variables has been
    /// bound since. Whether any was retried.
    pub(super) fn wake_rows(&mut self) -> Result<bool> {
        let mut progress = false;
        for i in 0..self.row_postponed.len() {
            let Some(c) = self.row_postponed[i].clone() else { continue };
            if c.vars.iter().all(|&v| self.is_free(v)) {
                continue;
            }
            self.row_postponed[i] = None;
            self.trail.push(Undo::RowWoken(i, c.clone()));
            progress = true;
            match c.sub {
                true => self.subrow(c.a, c.b, &c.where_)?,
                false => self.unify(c.a, c.b, &c.where_)?,
            }
        }
        Ok(progress)
    }

    pub(super) fn rows_postponed(&self) -> bool {
        self.row_postponed.iter().any(Option::is_some)
    }

    /// The first row equation still postponed, as an error, after dropping
    /// them all. Run where a definition is done: what is left has more than
    /// one solution. See Note [Effect label variables].
    pub fn unsolved_row(&mut self) -> Option<Diagnostic> {
        let mut first = None;
        for i in 0..self.row_postponed.len() {
            if let Some(c) = self.row_postponed[i].take() {
                self.trail.push(Undo::RowWoken(i, c.clone()));
                first.get_or_insert(c);
            }
        }
        let c = first?;
        let shown = self.show_all(&[c.a, c.b]);
        Some(
            Diagnostic::error(
                Code::TypeAnnotationRequired,
                Span::at(0),
                0,
                format!("cannot tell which effect stands for a label variable in `{}` and `{}` {}", shown[0], shown[1], c.where_),
            )
            .with_note("an effect variable is solved only when exactly one effect of the other row can be it")
            .with_help("name the effect where the function is used, as in `f @ctx {.l = State}`"),
        )
    }

    /// The variables the postponed row equations mention, which must stay
    /// unification variables until they are solved.
    pub fn row_postponed_vars(&self, out: &mut std::collections::HashSet<VarId>) {
        for c in self.row_postponed.iter().flatten() {
            self.collect_vars(c.a, out);
            self.collect_vars(c.b, out);
        }
    }

    /// Unify the type arguments of two occurrences of one effect label. Unknown
    /// arguments (`RowEmpty`, a label written where its effect is not visible)
    /// match any.
    pub(super) fn unify_effect_args(&mut self, label: Type, a: Type, b: Type, where_: &str) -> Result<()> {
        let (a, b) = (self.resolve(a), self.resolve(b));
        if matches!(self.types.node(a), TypeNode::RowEmpty)
            || matches!(self.types.node(b), TypeNode::RowEmpty)
        {
            return Ok(());
        }
        self.unify(a, b, where_).map_err(|d| {
            let note = format!(
                "effect `{}` is used here at `{}` and at `{}`; one handler serves one instance",
                self.show(label),
                self.show_args(a),
                self.show_args(b)
            );
            d.with_note(note)
        })
    }

    /// An effect's type arguments, space-separated as written in a row.
    pub(super) fn show_args(&self, args: Type) -> String {
        match self.types.node(args) {
            TypeNode::Tuple(items) => self
                .types
                .items(items)
                .into_iter()
                .map(|t| self.show(t))
                .collect::<Vec<_>>()
                .join(" "),
            _ => self.show(args),
        }
    }

    pub(super) fn effect_not_handled(&self, label: Type, where_: &str) -> Diagnostic {
        Diagnostic::error(
            Code::TypeMismatch,
            Span::at(0),
            0,
            format!("effect `{}` is performed but not handled {where_}", self.show(label)),
        )
    }
}
