//! Propositions: `a ~ b`, booleans used as types, and the proofs `@refl`,
//! `@transp` and `@cast` (#539).
//!
//! A proposition compares two values the checker evaluates while it checks
//! a type: sizes, types, and booleans built from comparisons of sizes. Such a
//! value is a [`Static`], read off an expression by [`Checker::static_of`].
//! See Note [Propositions]. A `Bool` where a type is expected
//! is the proposition `b ~ true`, so `(n: @Nat) -> n < 4 -> T` takes a proof
//! that `n < 4` computes to `true`. A `let` stays transparent: after
//! `let n = 3`, `n` is the size `3` in a proposition, and after
//! `let t = @Int`, an annotation `(x: t)` is `(x: @Int)`.
//!
//! Proofs are erased: `@refl a` and `@transp ...` lower to `{}`, and
//! `@cast A B e x` to `x`.
//!
//! Entry points: [`Checker::proposition_of`] (a proposition written in a
//! type), [`Checker::proof_form`] (a proof in a term), [`Checker::let_static`].

use super::*;

/// A value a proposition compares, evaluated: a size, a boolean, a type, or
/// a `_` not known yet.
#[derive(Clone, Copy, Debug)]
pub(super) enum Static {
    Size(Type),
    Bool(Type),
    Type(Type),
    Unknown(Type),
}

impl Static {
    pub(super) fn ty(self) -> Type {
        match self {
            Static::Size(t) | Static::Bool(t) | Static::Type(t) | Static::Unknown(t) => t,
        }
    }

    fn sort(self) -> &'static str {
        match self {
            Static::Size(_) => "a size",
            Static::Bool(_) => "a boolean",
            Static::Type(_) => "a type",
            Static::Unknown(_) => "unknown",
        }
    }
}

/// The proof forms the checker knows, by the name at the head of a call.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum ProofForm {
    /// `@refl a : a ~ a`.
    Refl,
    /// `@transp t B u t2 e : B t2`, from `u : B t` and `e : t ~ t2`.
    Transp,
    /// `@cast A B e x : B`, from `e : A ~ B` and `x : A`.
    Cast,
}

impl ProofForm {
    fn arity(self) -> usize {
        match self {
            ProofForm::Refl => 1,
            ProofForm::Transp => 5,
            ProofForm::Cast => 4,
        }
    }

    fn name(self) -> &'static str {
        match self {
            ProofForm::Refl => "@refl",
            ProofForm::Transp => "@transp",
            ProofForm::Cast => "@cast",
        }
    }
}

/// The comparison operators, each spelled through `<` and `==` as CORE
/// defines them: the operands in order, swapped or not, and whether the
/// result is negated.
fn comparison(op: &str) -> Option<(BoolOp, bool, bool)> {
    Some(match op {
        "<" => (BoolOp::Lt, false, false),
        ">" => (BoolOp::Lt, true, false),
        "<=" => (BoolOp::Lt, true, true),
        ">=" => (BoolOp::Lt, false, true),
        "==" => (BoolOp::Eq, false, false),
        "!=" => (BoolOp::Eq, false, true),
        _ => return None,
    })
}

impl<'a> Checker<'a> {
    /// Whether `e`, standing where a type is expected, is a proposition or a
    /// boolean: `a ~ b`, a comparison, `not`, `&&`, `||` or a constant.
    pub(super) fn is_proposition_shaped(&self, e: Aol<Expr>) -> bool {
        match self.node(e) {
            Expr::BinOp { op, .. } => op.as_str() == "~" || comparison(op.as_str()).is_some(),
            Expr::App(f, _) => matches!(self.node(*f), Expr::Var { module: None, name } if name.as_str() == "not"),
            Expr::If { then, alt, .. } => {
                matches!(self.node(*alt), Expr::Bool(false)) || matches!(self.node(*then), Expr::Bool(true))
            }
            Expr::Bool(_) => true,
            Expr::Var { module: None, name } => matches!(name.as_str(), "true" | "false"),
            Expr::Let { body, .. } => self.is_proposition_shaped(*body),
            _ => false,
        }
    }

    /// The type a proposition written in a type stands for: `a ~ b` itself,
    /// and a boolean `b` as `b ~ true`.
    pub(super) fn proposition_of(&mut self, e: Aol<Expr>, tvars: &HashMap<StrId, Type>) -> Result<Type> {
        let s = self.static_of(e, tvars, &[])?;
        self.as_proposition(s, self.ast.expr_span(e))
    }

    /// `not b` written in a type, which reads as a type application.
    pub(super) fn negation_of(&mut self, ty: Aol<Ty>, tvars: &HashMap<StrId, Type>) -> Result<Type> {
        let s = self.static_of_ty(ty, tvars)?;
        self.as_proposition(s, self.ast.ty_span(ty))
    }

    /// Whether `ty` is `not b` written in a type.
    pub(super) fn is_negation(&self, ty: Aol<Ty>, tvars: &HashMap<StrId, Type>) -> bool {
        matches!(self.tnode(ty), Ty::App(head, _)
            if matches!(self.tnode(*head), Ty::Var(n) if n.as_str() == "not" && !tvars.contains_key(n)))
    }

    /// A value standing where a type is expected: a type as itself, and a
    /// boolean `b` as `b ~ true`.
    pub(super) fn as_proposition(&mut self, s: Static, span: Option<Span>) -> Result<Type> {
        match s {
            // Rule [Frontend-Bool-Reflection]
            Static::Bool(b) => {
                let t = self.unifier.types.bool_lit(true);
                Ok(self.unifier.types.prop_eq(b, t))
            }
            Static::Type(t) | Static::Unknown(t) => Ok(t),
            Static::Size(_) => Err(diag!(
                Code::TypeMismatch, span.unwrap_or(Span::at(0)), 0,
                "a size stands where a type is expected"
            )),
        }
    }

    /// A value written in type syntax: the parser reads `not b` and the
    /// names in it as types.
    fn static_of_ty(&mut self, ty: Aol<Ty>, tvars: &HashMap<StrId, Type>) -> Result<Static> {
        match *self.tnode(ty) {
            Ty::Term(e) => self.static_of(e, tvars, &[]),
            Ty::Nat(n) => Ok(Static::Size(self.unifier.types.nat(n))),
            Ty::Var(name) if tvars.contains_key(&name) && self.unifier.is_size(tvars[&name]) => Ok(Static::Size(tvars[&name])),
            Ty::Var(name) if !tvars.contains_key(&name) && matches!(name.as_str(), ty::TRUE | ty::FALSE) => {
                Ok(Static::Bool(self.unifier.types.bool_lit(name.as_str() == ty::TRUE)))
            }
            Ty::App(_, x) if self.is_negation(ty, tvars) => {
                match self.static_of_ty(x, tvars)? {
                    Static::Bool(b) | Static::Unknown(b) => Ok(Static::Bool(self.unifier.types.bool_op(BoolOp::Not, &[b]))),
                    s => Err(diag!(
                        Code::TypeMismatch, self.ast.ty_span(x).unwrap_or(Span::at(0)), 0,
                        "expected a boolean in a type, found {}", s.sort()
                    )),
                }
            }
            _ => {
                let mut tvars = tvars.clone();
                Ok(Static::Type(self.ty_of_ast(ty, &mut tvars)))
            }
        }
    }

    /// Evaluate `e` as a value a proposition compares. `tvars` are the type
    /// and size variables in scope, `env` the binders of a `@transp` motive.
    pub(super) fn static_of(&mut self, e: Aol<Expr>, tvars: &HashMap<StrId, Type>, env: &[(StrId, Static)]) -> Result<Static> {
        let span = self.ast.expr_span(e);
        let at = span.unwrap_or(Span::at(0));
        match *self.node(e) {
            Expr::BinOp { op, lhs, rhs } if op.as_str() == "~" => {
                let (a, b) = (self.static_of(lhs, tvars, env)?, self.static_of(rhs, tvars, env)?);
                self.same_sort(a, b, at)?;
                // Rule [Frontend-Eq-Form]
                Ok(Static::Type(self.unifier.types.prop_eq(a.ty(), b.ty())))
            }
            Expr::BinOp { op, lhs, rhs } if comparison(op.as_str()).is_some() => {
                let (bop, swap, negate) = comparison(op.as_str()).expect("guarded");
                let (a, b) = (self.static_of(lhs, tvars, env)?, self.static_of(rhs, tvars, env)?);
                let (a, b) = if swap { (b, a) } else { (a, b) };
                let cmp = match (a, b) {
                    (Static::Size(_) | Static::Unknown(_), Static::Size(_) | Static::Unknown(_)) => {
                        for s in [a, b] {
                            self.unifier.mark_size(s.ty());
                        }
                        self.unifier.types.bool_op(bop, &[a.ty(), b.ty()])
                    }
                    (Static::Bool(x), Static::Bool(y)) if bop == BoolOp::Eq => self.bool_eq(x, y),
                    _ => {
                        return Err(dependent_only(
                            span,
                            &format!("a comparison of {} and {} in a type", a.sort(), b.sort()),
                        )
                        .with_note("a type compares sizes, and booleans with `==` and `!=`"))
                    }
                };
                Ok(Static::Bool(if negate { self.unifier.types.bool_op(BoolOp::Not, &[cmp]) } else { cmp }))
            }
            Expr::BinOp { op, lhs, rhs } if matches!(op.as_str(), "+" | "*") => {
                let (a, b) = (self.static_size(lhs, tvars, env)?, self.static_size(rhs, tvars, env)?);
                let node = if op.as_str() == "+" { TypeNode::NatAdd(a, b) } else { TypeNode::NatMul(a, b) };
                Ok(Static::Size(self.unifier.types.add(node)))
            }
            Expr::Int(n) if n >= 0 => Ok(Static::Size(self.unifier.types.nat(n as u64))),
            Expr::Bool(b) => Ok(Static::Bool(self.unifier.types.bool_lit(b))),
            Expr::App(f, x) if matches!(self.node(f), Expr::Var { module: None, name } if name.as_str() == "not") => {
                let x = self.static_bool(x, tvars, env)?;
                Ok(Static::Bool(self.unifier.types.bool_op(BoolOp::Not, &[x])))
            }
            Expr::If { cond, then, alt } if matches!(self.node(alt), Expr::Bool(false)) => {
                let (a, b) = (self.static_bool(cond, tvars, env)?, self.static_bool(then, tvars, env)?);
                Ok(Static::Bool(self.unifier.types.bool_op(BoolOp::And, &[a, b])))
            }
            Expr::If { cond, then, alt } if matches!(self.node(then), Expr::Bool(true)) => {
                let (a, b) = (self.static_bool(cond, tvars, env)?, self.static_bool(alt, tvars, env)?);
                Ok(Static::Bool(self.unifier.types.bool_op(BoolOp::Or, &[a, b])))
            }
            Expr::Var { module: None, name } => self.static_name(name, e, tvars, env),
            // Rule [Frontend-Let-Transparent]
            Expr::Let { binding, body } => {
                let Pattern::Var(x) = *self.pnode(binding.pat) else { return Err(not_evaluated(span)) };
                let value = self.static_of(binding.value, tvars, env)?;
                let mut inner = env.to_vec();
                inner.push((x, value));
                let mut tvars = tvars.clone();
                tvars.remove(&x);
                self.static_of(body, &tvars, &inner)
            }
            Expr::Type(t) => {
                let mut tvars = tvars.clone();
                Ok(Static::Type(self.ty_reporting(t, &mut tvars, None)))
            }
            Expr::App(..) => self.static_type_app(e, tvars, env),
            _ => Err(not_evaluated(span)),
        }
    }

    /// A name in a proposition: a binder of the motive, a variable of the
    /// signature, a local whose value the checker knows, a `@Nat` constant,
    /// a boolean constant or a type.
    fn static_name(&mut self, name: StrId, e: Aol<Expr>, tvars: &HashMap<StrId, Type>, env: &[(StrId, Static)]) -> Result<Static> {
        let span = self.ast.expr_span(e);
        if let Some((_, s)) = env.iter().rev().find(|(n, _)| *n == name) {
            return Ok(*s);
        }
        if name.as_str() == "_" {
            return Ok(Static::Unknown(self.unifier.fresh()));
        }
        if let Some(s) = self.let_bound(name, tvars) {
            return Ok(s);
        }
        if let Some(&t) = tvars.get(&name) {
            if self.level_names.contains(&t) {
                return Err(diag!(
                    Code::TypeMismatch, span.unwrap_or(Span::at(0)), 0,
                    "`{name}` is a level, which stands only in a universe"
                ));
            }
            return Ok(match self.unifier.is_size(t) {
                true => Static::Size(t),
                false => Static::Type(t),
            });
        }
        if let Some(t) = self.lookup_local(name) {
            if let Some(size) = self.size_of_req(t) {
                return Ok(Static::Size(size));
            }
            if let Some(&s) = self.let_statics.get(&t) {
                return Ok(s);
            }
            return Err(dependent_only(span, "a run-time value in a type")
                .with_note(format!("the checker evaluates what a type compares, and `{name}` is known only at run time")));
        }
        if self.nat_consts.contains_key(&name) {
            let mut visiting = Vec::new();
            return match self.size_of_expr(e, &mut visiting) {
                Ok(t) => Ok(Static::Size(t)),
                Err(_) => Err(not_evaluated(span)),
            };
        }
        match name.as_str() {
            ty::TRUE => return Ok(Static::Bool(self.unifier.types.bool_lit(true))),
            ty::FALSE => return Ok(Static::Bool(self.unifier.types.bool_lit(false))),
            _ => {}
        }
        if name.as_str() == ty::UNIVERSE || name.as_str() == "@Tensor" || self.is_known_type(name) {
            return self.static_type_app(e, tvars, env);
        }
        Err(not_evaluated(span))
    }

    /// A type written as a term in a proposition: a type name, `@Type n`, or
    /// a type or type-level function applied to types and sizes.
    fn static_type_app(&mut self, e: Aol<Expr>, tvars: &HashMap<StrId, Type>, env: &[(StrId, Static)]) -> Result<Static> {
        let span = self.ast.expr_span(e);
        let mut args = Vec::new();
        let mut head = e;
        while let Expr::App(f, x) = *self.node(head) {
            args.push(x);
            head = f;
        }
        args.reverse();
        let Expr::Var { module: None, name } = *self.node(head) else { return Err(not_evaluated(span)) };
        if name.as_str() == ty::UNIVERSE {
            return match args.as_slice() {
                [] => Ok(Static::Type(self.unifier.fresh_universe())),
                [n] => match *self.node(*n) {
                    Expr::Int(n) if (0..=u32::MAX as i64).contains(&n) => {
                        let level = self.unifier.types.add(TypeNode::Level(n as u32));
                        Ok(Static::Type(self.unifier.types.universe(level)))
                    }
                    _ => Err(dependent_only(span, "a level other than a number in a proposition")),
                },
                _ => Err(not_evaluated(span)),
            };
        }
        if name.as_str() == "@Tensor" {
            let [size, elem] = args.as_slice() else { return Err(not_evaluated(span)) };
            let size = self.static_size(*size, tvars, env)?;
            let elem = self.static_of(*elem, tvars, env)?.ty();
            return Ok(Static::Type(tensor_type(&self.unifier.types, size, elem)));
        }
        if !self.is_known_type(name) {
            return Err(not_evaluated(span));
        }
        let mut values = Vec::with_capacity(args.len());
        for a in &args {
            values.push(self.static_of(*a, tvars, env)?.ty());
        }
        if let Some((params, body)) = self.aliases.get(&name).cloned() {
            if params.len() == values.len() {
                let mut sub: HashMap<StrId, Type> = params.iter().copied().zip(values.iter().copied()).collect();
                let expanded = self.ty_of_ast(body, &mut sub);
                return Ok(Static::Type(self.unifier.types.alias(name, values, expanded)));
            }
            return Err(dependent_only(span, "a type-level function applied to too few arguments in a proposition"));
        }
        let applied = values.into_iter().fold(self.unifier.types.con(name), |f, x| self.unifier.types.app(f, x));
        Ok(Static::Type(applied))
    }

    fn static_size(&mut self, e: Aol<Expr>, tvars: &HashMap<StrId, Type>, env: &[(StrId, Static)]) -> Result<Type> {
        match self.static_of(e, tvars, env)? {
            Static::Size(t) => Ok(t),
            Static::Unknown(t) => {
                self.unifier.mark_size(t);
                Ok(t)
            }
            s => Err(diag!(
                Code::TypeMismatch, self.ast.expr_span(e).unwrap_or(Span::at(0)), 0,
                "expected a size in a type, found {}", s.sort()
            )),
        }
    }

    fn static_bool(&mut self, e: Aol<Expr>, tvars: &HashMap<StrId, Type>, env: &[(StrId, Static)]) -> Result<Type> {
        match self.static_of(e, tvars, env)? {
            Static::Bool(t) | Static::Unknown(t) => Ok(t),
            s => Err(diag!(
                Code::TypeMismatch, self.ast.expr_span(e).unwrap_or(Span::at(0)), 0,
                "expected a boolean in a type, found {}", s.sort()
            )),
        }
    }

    /// `x == y` of two booleans, as `(x && y) || (not x && not y)`.
    fn bool_eq(&self, x: Type, y: Type) -> Type {
        let types = &self.unifier.types;
        let both = types.bool_op(BoolOp::And, &[x, y]);
        let (nx, ny) = (types.bool_op(BoolOp::Not, &[x]), types.bool_op(BoolOp::Not, &[y]));
        let neither = types.bool_op(BoolOp::And, &[nx, ny]);
        types.bool_op(BoolOp::Or, &[both, neither])
    }

    /// The two sides of `a ~ b` compare values of one kind; two types also
    /// share a universe.
    fn same_sort(&mut self, a: Static, b: Static, at: Span) -> Result<()> {
        match (a, b) {
            (Static::Unknown(_), _) | (_, Static::Unknown(_)) => Ok(()),
            (Static::Size(_), Static::Size(_)) | (Static::Bool(_), Static::Bool(_)) => Ok(()),
            (Static::Type(x), Static::Type(y)) => {
                let (lx, ly) = (self.unifier.level_of(x), self.unifier.level_of(y));
                self.unifier.unify(lx, ly, "between the sides of `~`").map_err(|d| d.fill_span(at))
            }
            _ => Err(diag!(
                Code::TypeMismatch, at, 0,
                "the sides of `~` are {} and {}", a.sort(), b.sort();
                note: "`a ~ b` compares two values of one type"
            )),
        }
    }

    /// The local `name`, if a binder in the body binds it.
    pub(super) fn lookup_local(&self, name: StrId) -> Option<Type> {
        self.scopes[1..].iter().rev().find_map(|s| s.get(&name).copied())
    }

    /// The value of the `let`-bound local `name` that a type mentions, when
    /// the checker knows it and the type itself binds no `name` of its own
    /// (`tvars` beyond the enclosing signature's).
    // Rule [Frontend-Let-Transparent]
    pub(super) fn let_bound(&self, name: StrId, tvars: &HashMap<StrId, Type>) -> Option<Static> {
        if tvars.get(&name).is_some_and(|t| self.scoped_tvars.get(&name) != Some(t)) {
            return None;
        }
        self.lookup_local(name).and_then(|t| self.let_statics.get(&t).copied())
    }

    /// Remember the value of `let name = value` for the types in its body,
    /// keyed by the local's type `local`, when it is a value the checker
    /// evaluates: a size, a boolean or a type. See Note [Propositions].
    // Rule [Frontend-Let-Transparent]
    pub(super) fn let_static(&mut self, value: Aol<Expr>, local: Type) {
        if !self.is_static_value(value) {
            return;
        }
        let tvars = self.scoped_tvars.clone();
        let save = self.unifier.save();
        match self.static_of(value, &tvars, &[]) {
            Ok(s @ (Static::Size(_) | Static::Bool(_) | Static::Type(_))) => {
                self.let_statics.insert(local, s);
            }
            _ => self.unifier.restore(save),
        }
    }

    /// Whether `e` is built only from what a proposition evaluates: numbers,
    /// `+`, `*`, comparisons, `not`, `&&`, `||`, boolean constants, types
    /// and names whose values the checker knows.
    pub(super) fn is_static_value(&self, e: Aol<Expr>) -> bool {
        match self.node(e) {
            Expr::Int(n) => *n >= 0,
            Expr::Bool(_) | Expr::Type(_) => true,
            Expr::BinOp { op, lhs, rhs } => {
                (matches!(op.as_str(), "+" | "*") || comparison(op.as_str()).is_some())
                    && self.is_static_value(*lhs)
                    && self.is_static_value(*rhs)
            }
            Expr::App(f, x) if matches!(self.node(*f), Expr::Var { module: None, name } if name.as_str() == "not") => {
                self.is_static_value(*x)
            }
            Expr::App(f, x) => self.is_type_head(*f) && self.is_static_value(*x),
            Expr::If { cond, then, alt } => {
                (matches!(self.node(*alt), Expr::Bool(false)) || matches!(self.node(*then), Expr::Bool(true)))
                    && [*cond, *then, *alt].iter().all(|x| self.is_static_value(*x))
            }
            Expr::Var { module: None, name } => match self.lookup_local(*name) {
                Some(t) => self.size_of_req(t).is_some() || self.let_statics.contains_key(&t),
                None => matches!(name.as_str(), "true" | "false") || self.is_type_head(e),
            },
            _ => false,
        }
    }

    /// Whether `e` is a type, or a type-level function applied to some of
    /// its arguments: the head of the spine names a type, `@Tensor` or
    /// `@Type`.
    fn is_type_head(&self, e: Aol<Expr>) -> bool {
        match self.node(e) {
            Expr::App(f, x) => self.is_type_head(*f) && self.is_static_value(*x),
            Expr::Var { module: None, name } => {
                self.lookup_local(*name).is_none()
                    && (name.as_str() == ty::UNIVERSE || name.as_str() == "@Tensor" || self.is_known_type(*name))
            }
            _ => false,
        }
    }

    /// The proof form a call `head args` makes, if any. `@cast` with one
    /// argument is the integer cast.
    pub(super) fn proof_head(&self, head: Aol<Expr>, args: usize) -> Option<ProofForm> {
        let Expr::Var { module: None, name } = self.node(head) else { return None };
        if self.lookup_local(*name).is_some() {
            return None;
        }
        match name.as_str() {
            "@refl" => Some(ProofForm::Refl),
            "@transp" => Some(ProofForm::Transp),
            "@cast" if args == ProofForm::Cast.arity() => Some(ProofForm::Cast),
            _ => None,
        }
    }

    /// The proof form a whole call `e` makes, with its arguments.
    pub(super) fn proof_call(&self, e: Aol<Expr>) -> Option<(ProofForm, Vec<Aol<Expr>>)> {
        let mut args = Vec::new();
        let mut head = e;
        while let Expr::App(f, x) = self.node(head) {
            args.push(*x);
            head = *f;
        }
        args.reverse();
        self.proof_head(head, args.len()).map(|form| (form, args))
    }

    /// Check a proof form `e` applied to `args`, against `expected` when it is
    /// known. Each is erased: the call lowers to `{}`, or `@cast`'s to its
    /// value.
    pub(super) fn proof_form(&mut self, e: Aol<Expr>, form: ProofForm, args: &[Aol<Expr>], expected: Option<Type>) -> Result<Type> {
        let at = self.ast.expr_span(e).unwrap_or(Span::at(0));
        if args.len() != form.arity() {
            let usage = match form {
                ProofForm::Refl => "`@refl a` proves `a ~ a`",
                ProofForm::Transp => "`@transp t B u t2 e` moves a proof `u` of `B t` along `e : t ~ t2`",
                ProofForm::Cast => "`@cast A B e x` moves `x : A` to `B` along `e : A ~ B`",
            };
            return Err(diag!(
                Code::TypeMismatch, at, 0,
                "`{}` takes {} argument(s), found {}", form.name(), form.arity(), args.len();
                note: "{usage}"
            ));
        }
        let tvars = self.scoped_tvars.clone();
        let result = match form {
            // Rule [Frontend-Refl]
            ProofForm::Refl => {
                let a = self.static_of(args[0], &tvars, &[])?.ty();
                self.type_terms.insert(e);
                let proved = self.unifier.types.prop_eq(a, a);
                if let Some(expected) = expected {
                    self.refl_against(proved, expected, at)?;
                }
                proved
            }
            // Rule [Frontend-Transport]
            ProofForm::Transp => {
                let (t, motive, u, t2, eq) = (args[0], args[1], args[2], args[3], args[4]);
                let (from, to) = (self.static_of(t, &tvars, &[])?, self.static_of(t2, &tvars, &[])?);
                self.same_sort(from, to, at)?;
                let along = self.unifier.types.prop_eq(from.ty(), to.ty());
                self.check(eq, along)?;
                let before = self.motive_at(motive, from, &tvars)?;
                let after = self.motive_at(motive, to, &tvars)?;
                self.check(u, before)?;
                self.type_terms.insert(e);
                after
            }
            // Rule [Frontend-Cast]
            ProofForm::Cast => {
                let (a, b, eq, x) = (args[0], args[1], args[2], args[3]);
                let (from, to) = (self.static_of(a, &tvars, &[])?, self.static_of(b, &tvars, &[])?);
                for (s, side) in [(from, a), (to, b)] {
                    if !matches!(s, Static::Type(_) | Static::Unknown(_)) {
                        return Err(diag!(
                            Code::TypeMismatch, self.ast.expr_span(side).unwrap_or(at), 0,
                            "`@cast` moves a value between types, but this is {}", s.sort()
                        ));
                    }
                }
                self.same_sort(from, to, at)?;
                let along = self.unifier.types.prop_eq(from.ty(), to.ty());
                self.check(eq, along)?;
                self.check(x, from.ty())?;
                self.proof_casts.insert(e, x);
                to.ty()
            }
        };
        Ok(result)
    }

    /// `B v` for a motive `B`: a lambda `\z => P` of one variable whose body
    /// is a proposition, the body with `z` standing for `v`; or a type-level
    /// function returning a proposition, applied to all its arguments but the
    /// last, and then to `v`.
    fn motive_at(&mut self, motive: Aol<Expr>, v: Static, tvars: &HashMap<StrId, Type>) -> Result<Type> {
        let at = self.ast.expr_span(motive).unwrap_or(Span::at(0));
        let shown = match *self.node(motive) {
            Expr::Lambda { params, body } => {
                let params = self.ast.slice(params);
                let [param] = params else {
                    return Err(diag!(Code::TypeMismatch, at, 0, "a `@transp` motive binds one variable, `\\z => ...`"));
                };
                let Pattern::Var(z) = *self.pnode(param.pat) else {
                    return Err(diag!(Code::TypeMismatch, at, 0, "a `@transp` motive binds one variable, `\\z => ...`"));
                };
                let mut tvars = tvars.clone();
                if let Static::Type(t) | Static::Size(t) = v {
                    tvars.insert(z, t);
                }
                self.static_of(body, &tvars, &[(z, v)])?
            }
            _ => self.named_motive_at(motive, v, tvars)?,
        };
        let prop = match shown {
            Static::Bool(b) => {
                let t = self.unifier.types.bool_lit(true);
                self.unifier.types.prop_eq(b, t)
            }
            Static::Type(t) | Static::Unknown(t) => t,
            Static::Size(_) => return Err(diag!(Code::TypeMismatch, at, 0, "a `@transp` motive returns a proposition, not a size")),
        };
        let level = self.unifier.level_of(prop);
        if self.unifier.normalize_level(level).ground() != Some(0) {
            return Err(diag!(
                Code::TypeMismatch, at, 0,
                "a `@transp` motive returns a proposition, but this one returns `{}`", self.show_in_def(&[prop])[0];
                help: "move a value of a type along an equality with `@cast A B e x`"
            ));
        }
        Ok(prop)
    }

    /// `F a.. v` for a motive `F a..` naming a type-level function (`Pos`,
    /// `Lt 0`) that takes one argument more than it is given.
    fn named_motive_at(&mut self, motive: Aol<Expr>, v: Static, tvars: &HashMap<StrId, Type>) -> Result<Static> {
        let span = self.ast.expr_span(motive);
        let at = span.unwrap_or(Span::at(0));
        let mut args = Vec::new();
        let mut head = motive;
        while let Expr::App(f, x) = *self.node(head) {
            args.push(x);
            head = f;
        }
        args.reverse();
        let named = match *self.node(head) {
            Expr::Var { module: None, name } if self.lookup_local(name).is_none() => Some(name),
            _ => None,
        };
        let Some((name, (params, body))) = named.and_then(|n| self.aliases.get(&n).cloned().map(|a| (n, a))) else {
            return Err(dependent_only(span, "a `@transp` motive other than a lambda `\\z => ...` or a type-level function")
                .with_note("a motive names a global returning a proposition, as `$ Pos : (n: @Nat) -> @Type 0 = 0 < n`"));
        };
        if params.len() != args.len() + 1 {
            return Err(diag!(
                Code::TypeMismatch, at, 0,
                "a `@transp` motive takes one argument, but `{name}` applied to {} argument(s) does not",
                args.len();
                note: "`{name}` takes {} argument(s)", params.len();
                note: "a motive is a type-level function applied to all its arguments but the last"
            ));
        }
        let mut values = Vec::with_capacity(params.len());
        for a in &args {
            values.push(self.static_of(*a, tvars, &[])?.ty());
        }
        values.push(v.ty());
        let mut sub: HashMap<StrId, Type> = params.iter().copied().zip(values.iter().copied()).collect();
        let expanded = self.ty_of_ast(body, &mut sub);
        Ok(Static::Type(self.unifier.types.alias(name, values, expanded)))
    }

    /// Check that `@refl`'s `a ~ a` is the proposition `expected`, saying
    /// which sides differ when it is not.
    fn refl_against(&mut self, proved: Type, expected: Type, at: Span) -> Result<()> {
        let resolved = self.unifier.resolve(expected);
        let Some((l, r)) = self.unifier.types.prop_eq_sides(resolved) else {
            return self.unifier.unify_expected(proved, expected, "against the expected type").map_err(|d| d.fill_span(at));
        };
        let (a, _) = self.unifier.types.prop_eq_sides(proved).expect("built as `a ~ a`");
        let save = self.unifier.save();
        if self.unifier.unify(l, a, "in `@refl`").and_then(|_| self.unifier.unify(r, a, "in `@refl`")).is_ok() {
            return Ok(());
        }
        self.unifier.restore(save);
        let folded: Vec<Option<Type>> = [l, r].iter().map(|&side| self.unifier.fold_bool(side)).collect();
        let shown = self.show_in_def(&[l, r, folded[0].unwrap_or(l), folded[1].unwrap_or(r)]);
        let mut d = diag!(
            Code::TypeMismatch, at, 0,
            "`@refl` proves a value equal to itself, but `{}` and `{}` do not compute to one value", shown[0], shown[1];
            note: "the checker compares the two sides by evaluation, so sides equal only by a lemma need a proof that uses it"
        );
        for i in 0..2 {
            if folded[i].is_some() {
                d = d.with_note(format!("`{}` computes to `{}`", shown[i], shown[i + 2]));
            }
        }
        Err(d)
    }

    /// Show types with the variables of the signature being checked by
    /// their names.
    pub(super) fn show_in_def(&self, tys: &[Type]) -> Vec<String> {
        let names = self.checking_def.map(|d| self.sig_names(d)).unwrap_or_default();
        self.unifier.show_all_named(tys, names)
    }
}

/// Why an expression in a proposition is rejected: it is not a value the
/// checker evaluates.
fn not_evaluated(span: Option<Span>) -> Diagnostic {
    dependent_only(span, "a value other than sizes, booleans and types in a proposition")
        .with_note("a proposition compares sizes (`n + 1`), booleans (`n < 4`) and types (`@Int`)")
}
