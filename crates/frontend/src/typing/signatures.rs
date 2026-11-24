//! Written types: turning type syntax into [`Type`]s.
//!
//! [`Checker::ty_of_ast`] elaborates a type expression from a signature, a
//! field or an alias body. It validates names (an unknown or hidden type is an
//! error with a fix), checks arities, expands aliases, turns `<...>` effect rows
//! into row types, and turns tensor shapes into sizes.
//!
//! Entry point: [`Checker::ty_of_ast`].

use super::*;
use super::unify::levels::ParamLevel;

// ## Binding type variables

/// How elaborating a type treats a lowercase name no binder in scope binds.
/// Either way it stands as a fresh variable, so every look at one signature
/// agrees; only the look that owns the signature reports it.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum FreeNames {
    Bind,
    Report,
}

/// A name found unbound while elaborating a type in [`FreeNames::Report`].
pub(super) struct Unbound {
    name: StrId,
    span: Option<Span>,
    ty: Type,
    row: bool,
}

impl<'a> Checker<'a> {
    /// The variables a signature's `@ctx` fields bind, by name, each fresh and of
    /// its field's kind.
    pub(super) fn sig_tvars(&mut self, sig: Aol<Ty>) -> HashMap<StrId, Type> {
        let mut tvars = self.level_tvars(sig);
        let Some(fields) = self.ast.ctx_params.get(sig).copied() else { return tvars };
        for f in self.ast.slice(fields).to_vec() {
            let t = match self.kind_of_ast(f.ty) {
                Some(ParamKind::Nat) => self.unifier.fresh_nat(),
                Some(ParamKind::Type) => self.leveled_var(f.ty, &tvars),
                Some(ParamKind::Row) => self.unifier.fresh(),
                None => continue,
            };
            tvars.insert(f.name, t);
        }
        tvars
    }

    /// The levels a signature's leading `@ctx {u: @l}` binds, each a fresh
    /// level variable, by name. See Note [Level parameters].
    // Rule [Frontend-Level-Polymorphism]
    pub(super) fn level_tvars(&mut self, sig: Aol<Ty>) -> HashMap<StrId, Type> {
        let mut tvars = HashMap::new();
        let Some(levels) = self.ast.level_params.get(sig).copied() else { return tvars };
        for f in self.ast.slice(levels).to_vec() {
            let l = self.unifier.fresh();
            self.level_names.insert(l);
            tvars.insert(f.name, l);
        }
        tvars
    }

    /// A fresh type variable ranging over the universe `universe` (`@Type`,
    /// `@Type n` or `@Type u` for a level `tvars` binds).
    /// See Note [Level constraints].
    pub(super) fn leveled_var(&mut self, universe: Aol<Ty>, tvars: &HashMap<StrId, Type>) -> Type {
        let t = self.unifier.fresh();
        let u = self.ty_of_ast(universe, &mut tvars.clone());
        if let Some(l) = self.unifier.types.universe_level(self.unifier.resolve(u)) {
            self.unifier.set_var_level(t, l);
        }
        t
    }

    /// The type of the type `ty` used as a value: the one universe it lives
    /// in. See Note [Level constraints].
    // Rule [Frontend-Univ]
    pub(super) fn universe_holding(&mut self, ty: Type) -> Type {
        let own = self.unifier.level_of(ty);
        self.unifier.types.universe(own)
    }

    /// The variable `name` stands for: the one `tvars` binds, else a fresh one
    /// of `kind`, recorded as unbound when reporting.
    fn free_name(&mut self, name: StrId, span: Option<Span>, tvars: &mut HashMap<StrId, Type>, kind: ParamKind) -> Type {
        if let Some(&t) = tvars.get(&name) {
            if let Some(u) = self.unbound.iter_mut().find(|u| u.name == name) {
                if span.is_some_and(|s| u.span.is_none_or(|w| s.start < w.start)) {
                    u.span = span;
                }
            }
            return t;
        }
        let t = match kind {
            ParamKind::Nat => self.unifier.fresh_nat(),
            _ => self.unifier.fresh(),
        };
        tvars.insert(name, t);
        if self.free_names == FreeNames::Report {
            self.unbound.push(Unbound { name, span, ty: t, row: kind == ParamKind::Row });
        }
        t
    }

    /// Elaborate `ty` reporting the names nothing binds: `sig` is the
    /// signature it is, whose `@ctx` the fix extends, or `None` for an
    /// annotation inside a body.
    pub(super) fn ty_reporting(&mut self, ty: Aol<Ty>, tvars: &mut HashMap<StrId, Type>, sig: Option<Aol<Ty>>) -> Type {
        let saved = std::mem::replace(&mut self.free_names, FreeNames::Report);
        let t = self.ty_of_ast(ty, tvars);
        self.free_names = saved;
        self.mark_sizes(t);
        self.report_unbound(sig);
        if let Some(sig) = sig {
            self.check_ctx_kinds(sig, tvars);
        }
        t
    }

    /// Mark the variables `ty` uses as sizes `@Nat`: tensor sizes, a declared
    /// type's `@Nat` arguments, and the operands of `+` and `*`.
    fn mark_sizes(&mut self, ty: Type) {
        self.unifier.note_tensor_sizes(ty);
        self.mark_param_sizes(ty);
    }

    fn mark_param_sizes(&mut self, ty: Type) {
        let ty = self.unifier.resolve(ty);
        match self.unifier.types.node(ty) {
            TypeNode::App(..) => {
                let mut args = Vec::new();
                let mut head = ty;
                while let TypeNode::App(h, a) = self.unifier.types.node(self.unifier.resolve(head)) {
                    args.push(a);
                    head = h;
                }
                args.reverse();
                if let TypeNode::Con(name) = self.unifier.types.node(self.unifier.resolve(head)) {
                    for (kind, &a) in self.param_kinds(name).unwrap_or_default().iter().zip(&args) {
                        if *kind == ParamKind::Nat {
                            self.unifier.mark_size(a);
                        }
                    }
                }
                for a in args {
                    self.mark_param_sizes(a);
                }
            }
            TypeNode::NatAdd(a, b) | TypeNode::NatMul(a, b) => {
                self.unifier.mark_size(a);
                self.unifier.mark_size(b);
            }
            TypeNode::Arrow(from, to, _) => {
                self.mark_param_sizes(from);
                self.mark_param_sizes(to);
            }
            TypeNode::Tuple(items) => {
                for t in self.unifier.types.items(items).to_vec() {
                    self.mark_param_sizes(t);
                }
            }
            TypeNode::Record(row) => self.mark_param_sizes(row),
            TypeNode::RowField(_, t, rest) => {
                self.mark_param_sizes(t);
                self.mark_param_sizes(rest);
            }
            _ => {}
        }
    }

    /// A `@ctx {n: @Type}` field the signature uses as a size is a `@Nat`.
    fn check_ctx_kinds(&mut self, sig: Aol<Ty>, tvars: &HashMap<StrId, Type>) {
        let Some(fields) = self.ast.ctx_params.get(sig).copied() else { return };
        for f in self.ast.slice(fields).to_vec() {
            let used_as_size = tvars.get(&f.name).is_some_and(|t| self.unifier.is_size_var(*t));
            if self.kind_of_ast(f.ty) != Some(ParamKind::Type) || !used_as_size {
                continue;
            }
            let written = self.ast.ty_span(f.ty).unwrap_or(f.span);
            self.errors.push(
                diag!(
                    Code::TypeMismatch, f.span, 0,
                    "`{}` is a `@Type`, but the signature uses it as a size", f.name;
                    note: "a size is a `@Nat`"
                )
                .with_fix(format!("make `{}` a `@Nat`", f.name), vec![Edit::new(written, "@Nat")], Applicability::MachineApplicable),
            );
        }
    }

    /// The error for the names found unbound, with the fix that binds them in
    /// the signature's leading `@ctx`.
    pub(super) fn report_unbound(&mut self, sig: Option<Aol<Ty>>) {
        let mut unbound = std::mem::take(&mut self.unbound);
        unbound.sort_by_key(|u| u.span.map_or(usize::MAX, |s| s.start));
        if unbound.is_empty() {
            return;
        }
        let names: Vec<(StrId, Option<Span>, ParamKind)> = unbound
            .iter()
            .map(|u| {
                let kind = match (u.row, self.unifier.is_size_var(u.ty)) {
                    (true, _) => ParamKind::Row,
                    (false, true) => ParamKind::Nat,
                    (false, false) => ParamKind::Type,
                };
                (u.name, u.span, kind)
            })
            .collect();
        let fields = ctx_fields(&names);
        let binder = match sig {
            Some(s) => Binder::Signature(self.ctx_insertion(s, &fields)),
            None => Binder::Body,
        };
        let d = unbound_names(&names, binder);
        self.errors.push(d);
    }

    /// The edit adding `fields` to the `@ctx` that opens `sig`, or a new one
    /// in front of it.
    fn ctx_insertion(&self, sig: Aol<Ty>, fields: &[String]) -> Option<Edit> {
        let mut bound: Vec<UseField> = Vec::new();
        for map in [&self.ast.level_params, &self.ast.ctx_params] {
            if let Some(fs) = map.get(sig) {
                bound.extend(self.ast.slice(*fs).iter().copied());
            }
        }
        if let Some(fs) = self.ast.use_params.get(sig) {
            bound.extend(self.ast.slice(*fs).iter().copied());
        }
        let leading = bound.iter().filter(|f| f.before == 0).map(|f| f.span.end).max();
        match leading {
            Some(end) => Some(Edit::new(Span::at(end), format!(", {}", fields.join(", ")))),
            None => {
                let start = self.ast.ty_span(sig)?.start;
                Some(Edit::new(Span::at(start), format!("@ctx {{{}}} -> ", fields.join(", "))))
            }
        }
    }

    /// Check that each `@ctx` field of signature `sig` that unification solves
    /// binds a type, a size or a row.
    pub(super) fn check_ctx_fields(&mut self, sig: Aol<Ty>) {
        let Some(fields) = self.ast.ctx_params.get(sig).copied() else { return };
        for f in self.ast.slice(fields).to_vec() {
            if self.kind_of_ast(f.ty).is_some() {
                continue;
            }
            if self.is_effect_kind(f.ty) {
                self.errors.push(label_variable(Some(f.span)));
                continue;
            }
            self.errors.push(dependent_only(Some(f.span), "a `@ctx` field of this sort"));
        }
    }
}

// ## Type names

impl<'a> Checker<'a> {
    /// Is `name` a usable type: a built-in base type, or a struct/union/alias
    /// declared here or imported? A bare name that is none of these is a typo (a
    /// type variable is a lowercase name).
    pub(super) fn unknown_type(&self, name: StrId) -> Diagnostic {
        let d = diag!(Code::TypeUnbound, Span::at(0), 0, "unknown type `{name}`");
        let known = self
            .structs
            .keys()
            .chain(self.unions.keys())
            .chain(self.aliases.keys())
            .map(|k| k.as_str())
            .chain(BASE_TYPES.iter().copied());
        match utilities::error::closest(name.as_str(), known) {
            Some(n) => d.with_fix(
                format!("did you mean `{n}`?"),
                vec![Edit::new(Span::at(0), n)],
                Applicability::MaybeIncorrect,
            ),
            None => d.with_note(
                "a type variable is written as a lowercase name; a capitalized type must be declared",
            ),
        }
    }

    /// Record `name` as one of this module's own types, displacing a hidden
    /// one of the same name an import brought in.
    pub(super) fn claim_type_name(&mut self, name: StrId) {
        self.type_home.insert(name, self.module_name);
        let aliased = self.alias_types.remove(&name).is_some();
        if self.hidden_types.remove(&name).is_some() || aliased {
            self.structs.remove(&name);
            self.unions.remove(&name);
            self.aliases.remove(&name);
        }
    }

    /// A type this module wrote naming a hidden type: one only an import's
    /// declarations reach. Deferred like the other type-name errors.
    pub(super) fn check_hidden_type(&mut self, ty: Aol<Ty>, name: StrId) {
        if let (Some(owners), true) = (self.ambiguous_imports.get(&name), self.imported_types.contains_key(&name)) {
            let qualified = matches!(self.tnode(ty), Ty::Con { module: Some(_), .. });
            if qualified || self.foreign_tys.contains(&ty) || self.unknown_type.is_some() {
                return;
            }
            let list = owners.iter().map(|m| format!("`{m}.{name}`")).collect::<Vec<_>>().join(" or ");
            let mut d = diag!(
                Code::AmbiguousName, Span::at(0), 0,
                "`{name}` is imported from more than one module";
                note: "types and values share one namespace: a type is a global of type `@Type`";
                help: "qualify it as {list}"
            );
            if let Some(span) = self.ast.ty_span(ty) {
                d = d.fill_span(span);
            }
            self.unknown_type = Some(d);
            return;
        }
        if let Some(&alias) = self.alias_types.get(&name) {
            let qualified = matches!(self.tnode(ty), Ty::Con { module: Some(_), .. });
            if qualified || self.foreign_tys.contains(&ty) || self.unknown_type.is_some() {
                return;
            }
            let mut d = diag!(
                Code::TypeUnbound, Span::at(0), 0,
                "type `{name}` is imported qualified-only";
                note: "`$ @import {alias} = {}` brings in no bare names", self.alias_modules[&alias]
            );
            if let Some(span) = self.ast.ty_span(ty) {
                d = d.fill_span(span).with_fix(
                    format!("write `{alias}.{name}`"),
                    vec![Edit::new(span, format!("{alias}.{name}"))],
                    Applicability::MachineApplicable,
                );
            }
            self.unknown_type = Some(d);
            return;
        }
        let Some(&home) = self.hidden_types.get(&name) else {
            return;
        };
        if self.foreign_tys.contains(&ty) || self.unknown_type.is_some() {
            return;
        }
        let mut d = diag!(Code::TypeUnbound, Span::at(0), 0, "type `{name}` is not imported");
        d = self.with_import_fix(d, home.as_str());
        if let Some(span) = self.ast.ty_span(ty) {
            d = d.fill_span(span);
        }
        self.unknown_type = Some(d);
    }

    /// `Type.Tag` naming a type an aliased-only import brought in, without the
    /// alias. A bare `.Tag` is fine: the expected type picks the union.
    pub(super) fn unqualified_alias_ctor(&self, module: Option<StrId>, ty: Option<StrId>, tag: StrId) -> Option<Diagnostic> {
        let ty = ty?;
        let alias = *self.alias_types.get(&ty)?;
        if module.is_some() {
            return None;
        }
        Some(diag!(
            Code::TypeUnbound, Span::at(0), 0,
            "type `{ty}` is imported qualified-only";
            note: "`$ @import {alias} = {}` brings in no bare names", self.alias_modules[&alias];
            help: "write `{alias}.{ty}.{tag}`"
        ))
    }

    /// `A.B` in a literal or pattern, read as struct `B` when `A` qualifies
    /// imported names (a module or an import alias) rather than naming a union
    /// (#449). A name means one thing in a scope, so this never competes with
    /// the union reading.
    pub(super) fn module_struct(&self, module: Option<StrId>, ty: Option<StrId>, tag: StrId) -> Option<StrId> {
        let qualifier = ty?;
        let is_module = self.module_scopes.contains(&qualifier) || qualifier == self.module_name;
        (module.is_none() && is_module && !self.unions.contains_key(&qualifier) && self.structs.contains_key(&tag))
            .then_some(tag)
    }

    /// Whether a lowercase name in a type means a global rather than a type
    /// variable: a type-level function.
    pub(super) fn is_type_global(&self, name: StrId) -> bool {
        self.aliases.contains_key(&name) || self.nat_consts.contains_key(&name)
    }

    /// The size a `@Nat` constant unfolds to, glued to its name so errors
    /// show it as written. Only what conversion can decide unfolds: a literal,
    /// another constant, and `+`/`*` of them. See Note [Glued aliases].
    fn nat_const(&mut self, name: StrId, span: Option<Span>) -> Type {
        let body = self.nat_consts[&name];
        let mut visiting = vec![name];
        let value = match self.size_of_expr(body, &mut visiting) {
            Ok(v) => v,
            Err(what) => {
                let d = match what {
                    SizeError::Cycle => diag!(
                        Code::TypeCycle, span.unwrap_or(Span::at(0)), 0,
                        "the size `{name}` unfolds to itself"
                    ),
                    SizeError::Term(at) => dependent_only(self.ast.expr_span(at).or(span), UNEVALUATED_SIZE)
                        .with_note(format!("`{name}` stands in a type, so the checker evaluates its definition")),
                };
                self.defer_type_error(d);
                return self.unifier.fresh_nat();
            }
        };
        self.unifier.types.alias(name, Vec::new(), value)
    }

    /// Evaluate a `@Nat` constant's body to a size.
    pub(super) fn size_of_expr(&mut self, e: Aol<Expr>, visiting: &mut Vec<StrId>) -> std::result::Result<Type, SizeError> {
        match self.node(e) {
            Expr::Int(n) if *n >= 0 => Ok(self.unifier.types.add(TypeNode::Nat(*n as u64))),
            Expr::Var { module: None, name } if self.nat_consts.contains_key(name) => {
                let name = *name;
                if visiting.contains(&name) {
                    return Err(SizeError::Cycle);
                }
                visiting.push(name);
                let v = self.size_of_expr(self.nat_consts[&name], visiting)?;
                visiting.pop();
                Ok(v)
            }
            // A `@Nat` field or `(n: @Nat)` parameter in scope holds its size.
            Expr::Var { module: None, name } if self.lookup(*name).and_then(|t| self.size_of_req(t)).is_some() => {
                let t = self.lookup(*name).expect("looked up");
                Ok(self.size_of_req(t).expect("a size field"))
            }
            Expr::BinOp { op, lhs, rhs } if matches!(op.as_str(), "+" | "*") => {
                let (add, lhs, rhs) = (op.as_str() == "+", *lhs, *rhs);
                let (a, b) = (self.size_of_expr(lhs, visiting)?, self.size_of_expr(rhs, visiting)?);
                Ok(self.unifier.types.add(if add { TypeNode::NatAdd(a, b) } else { TypeNode::NatMul(a, b) }))
            }
            _ => Err(SizeError::Term(e)),
        }
    }

    pub(super) fn is_known_type(&self, name: StrId) -> bool {
        is_base_type(name.as_str())
            || self.structs.contains_key(&name)
            || self.unions.contains_key(&name)
            || self.aliases.contains_key(&name)
    }

    /// The type of a type written in term position: its kind. A declared type
    /// takes `@Nat` for each parameter it uses as a size and `@Type` for the
    /// rest; a base type takes its element type. `None` when `name` is not a
    /// type.
    pub(super) fn type_kind(&mut self, name: StrId) -> Option<Type> {
        let kinds = self.param_kinds(name)?;
        // A data type lives in the universe of its largest parameter, and at
        // level 1 without one.
        let froms: Vec<Type> = kinds
            .iter()
            .map(|k| match k {
                ParamKind::Type => self.unifier.fresh_universe(),
                ParamKind::Nat => self.unifier.types.con(ty::NAT),
                ParamKind::Row => self.unifier.types.con(StrId::intern("@Row")),
            })
            .collect();
        let one = self.unifier.types.add(TypeNode::Level(1));
        let result = froms
            .iter()
            .filter_map(|f| self.unifier.types.universe_level(*f))
            .fold(one, |acc, l| self.unifier.types.add(TypeNode::LevelMax(acc, l)));
        let mut kind = self.unifier.types.universe(result);
        for (k, from) in kinds.iter().zip(froms).rev() {
            let from = match k {
                ParamKind::Type => from,
                ParamKind::Nat => self.unifier.types.con(ty::NAT),
                ParamKind::Row => self.unifier.types.con(StrId::intern("@Row")),
            };
            kind = self.unifier.types.arrow(from, kind);
        }
        Some(kind)
    }

    /// Why an expression in type position that did not reduce to a type is
    /// rejected. Choosing a type by a value (`if`, a match) is a large
    /// elimination, which needs the kernel; any other expression is a value.
    fn not_a_type(&self, ty: Aol<Ty>, e: Aol<Expr>) -> Diagnostic {
        let span = self.ast.ty_span(ty);
        let d = match self.ast.expr(e) {
            Expr::If { .. } | Expr::Match { .. } => return dependent_only(span, "a type chosen by a value"),
            Expr::Lambda { .. } => diag!(
                Code::TypeMismatch, Span::at(0), 0,
                "a function stands where a type is expected";
                help: "apply it to its arguments, or name it as a type-level function `$ f : @Type -> @Type = \\t => ...`"
            ),
            Expr::List(items) if self.ast.slice(*items).len() == 1 => {
                let size = match self.ast.expr(self.ast.slice(*items)[0]) {
                    Expr::Int(n) => n.to_string(),
                    _ => "n".to_string(),
                };
                diag!(
                    Code::TypeMismatch, Span::at(0), 0,
                    "a list stands where a type is expected";
                    help: "a sized tensor is written `@Tensor {size} T`"
                )
            }
            _ => diag!(
                Code::TypeMismatch, Span::at(0), 0,
                "a value stands where a type is expected";
                note: "a type is a type name, a type-level function applied to its arguments, or a size"
            ),
        };
        match span {
            Some(s) => d.fill_span(s),
            None => d,
        }
    }

    /// The type parameters a user-declared type constructor takes, if `name` is
    /// a struct, union, or alias (the ones whose arity we track).
    pub(super) fn type_params(&self, name: StrId) -> Option<&[StrId]> {
        self.structs
            .get(&name)
            .map(|i| i.params.as_slice())
            .or_else(|| self.unions.get(&name).map(|i| i.params.as_slice()))
            .or_else(|| self.aliases.get(&name).map(|(p, _)| p.as_slice()))
    }

    /// Flag a type constructor applied to the wrong number of arguments
    /// (`Weirdtype Int Int Int` for a two-parameter `Weirdtype`). Under-application
    /// is flagged only when `exact`: there are no higher-kinded parameters, so a
    /// struct or union is only ever a type once fully applied, but an alias may be
    /// left under-applied (its missing parameters become fresh variables).
    /// Deferred like other type-name errors.
    pub(super) fn check_type_arity(&mut self, ty: Aol<Ty>, exact: bool) {
        let mut count = 0;
        let mut cur = ty;
        while let Ty::App(h, _) = self.tnode(cur) {
            count += 1;
            cur = *h;
        }
        if let Ty::Con { name, .. } | Ty::Var(name) = self.tnode(cur) {
            let name = *name;
            if let Some(params) = self.type_params(name) {
                let arity = params.len();
                if count < arity && exact && self.unknown_type.is_none() {
                    let mut d = diag!(
                        Code::TypeMismatch, Span::at(0), 0,
                        "type `{name}` takes {arity} parameter(s) but {count} {} given",
                        if count == 1 { "was" } else { "were" };
                        note: "a type constructor is a type only once it is applied to every parameter";
                        help: "write `{name} {}`, with a type for each parameter",
                            params.iter().map(|p| p.as_str()).collect::<Vec<_>>().join(" ")
                    );
                    if let Some(span) = self.ast.ty_span(ty) {
                        d = d.fill_span(span);
                    }
                    self.unknown_type = Some(d);
                }
                if count > arity && self.unknown_type.is_none() {
                    let mut d = diag!(
                        Code::TypeMismatch, Span::at(0), 0,
                        "type `{name}` takes {arity} parameter(s) but {count} were given"
                    );
                    if let Some(span) = self.ast.ty_span(ty) {
                        d = d.fill_span(span);
                    }
                    self.unknown_type = Some(d);
                }
            }
        }
    }

    /// If `ty` is an alias applied to zero or more arguments, expand it: bind the
    /// alias's parameters to the arguments (a fresh variable for any not supplied,
    /// so an under-applied alias stays polymorphic, as for structs) and elaborate
    /// the body under that binding. Returns None when the spine head is not an alias.
    pub(super) fn try_expand_alias(&mut self, ty: Aol<Ty>, tvars: &mut HashMap<StrId, Type>) -> Option<Type> {
        let mut args = Vec::new();
        let mut cur = ty;
        while let Ty::App(h, a) = self.tnode(cur) {
            args.push(*a);
            cur = *h;
        }
        // A lowercase name is a global in scope before it is a type variable,
        // unless the type already binds it (a parameter, or a variable met
        // earlier in the same signature).
        let name = match self.tnode(cur) {
            Ty::Con { name, .. } => *name,
            Ty::Var(name) if !tvars.contains_key(name) => *name,
            _ => return None,
        };
        let (params, body) = self.aliases.get(&name)?.clone();
        self.check_hidden_type(cur, name);
        args.reverse();
        self.check_type_arity(ty, false);
        let mut sub: HashMap<StrId, Type> = HashMap::new();
        let mut written = Vec::new();
        let levels = self.alias_param_levels.get(&name).cloned().unwrap_or_default();
        for (i, p) in params.iter().enumerate() {
            let t = match args.get(i) {
                Some(&a) => self.ty_of_ast(a, tvars),
                None => self.unifier.fresh(),
            };
            if let Some(Some(n)) = levels.get(i) {
                let own = self.unifier.level_of(t);
                let at = self.unifier.types.add(TypeNode::Level(*n));
                if let Err(d) = self.unifier.unify(at, own, "in a type argument") {
                    let span = args.get(i).and_then(|a| self.ast.ty_span(*a)).unwrap_or(Span::at(0));
                    self.universe_errors.push(d.fill_span(span));
                }
            }
            if i < args.len() {
                written.push(t);
            }
            sub.insert(*p, t);
        }
        // An argument is elaborated before the body shows where it lands, so a
        // variable passed to a size parameter (`Matrix m n a`) is marked `Nat` here.
        let expanded = self.ty_of_ast(body, &mut sub);
        self.unifier.note_tensor_sizes(expanded);
        if args.len() != params.len() {
            return Some(expanded);
        }
        Some(self.unifier.types.alias(name, written, expanded))
    }

    /// Keep the first type error met while elaborating a type, reported once the
    /// definition is checked (see `unknown_type`).
    pub(super) fn defer_type_error(&mut self, d: Diagnostic) {
        if self.unknown_type.is_none() {
            self.unknown_type = Some(d);
        }
    }
}

// ## Effect rows

impl<'a> Checker<'a> {
    /// Elaborate an effect row: each entry's label extended onto the tail. The
    /// tail is the written one together with one per `!X` entry still waiting to
    /// be spliced (all one row variable), or the closed row when there is none.
    /// Each label is an effect, of kind `@Effect`; a `foreign` row, one an
    /// import's declarations wrote, may name effects this module does not see.
    pub(super) fn row_of_ast(
        &mut self,
        entries: Slice<RowEntry>,
        tail: Option<StrId>,
        span: Option<Span>,
        foreign: bool,
        tvars: &mut HashMap<StrId, Type>,
    ) -> Type {
        let ast = self.ast;
        let mut labels: Vec<(StrId, Type)> = Vec::new();
        let mut tails: Vec<Type> = Vec::new();
        if let Some(t) = tail {
            let v = self.free_name(t, span, tvars, ParamKind::Row);
            tails.push(v);
        }
        for entry in ast.slice(entries) {
            // `<!X>`: the labels are unknown until the driver splices them, so
            // the entry stands as an open tail.
            if let Some(expr) = entry.meta {
                self.meta_splice_operand(expr);
                tails.push(self.unifier.fresh());
                continue;
            }
            let name = entry.name;
            if self.aliases.contains_key(&name) {
                self.defer_type_error(diag!(
                    Code::TypeMismatch, entry.span, 0,
                    "type alias `{name}` is not an effect";
                    help: "an effect row names effects; a set of them is a `@Code` global \
                           spliced as `<!name>`"
                ));
                continue;
            }
            if !foreign {
                if let Some(d) = self.not_an_effect(name, entry.span) {
                    self.defer_type_error(d);
                    continue;
                }
            }
            let args = self.effect_label_args(name, ast.slice(entry.args), entry.span, tvars);
            labels.push((name, args));
        }
        let mut row = match tails.split_first() {
            None => self.unifier.types.row_empty(),
            Some((&first, rest)) => {
                for &other in rest {
                    if let Err(d) = self.unifier.unify(first, other, "in an effect row") {
                        self.defer_type_error(d);
                    }
                }
                first
            }
        };
        for &(label, args) in labels.iter().rev() {
            row = self.unifier.types.row_extend_args(label, args, row);
        }
        row
    }

    /// Why the row label `name` is not an effect: it is a type, or nothing
    /// declared here or imported. `None` for an effect.
    fn not_an_effect(&self, name: StrId, span: Span) -> Option<Diagnostic> {
        let own = self.effect_self.is_some_and(|(e, _)| e == name);
        if own || self.effect_arity.contains_key(&name) || BUILTIN_EFFECTS.contains(&name.as_str()) {
            return None;
        }
        if self.is_known_type(name) {
            return Some(diag!(
                Code::TypeMismatch, span, 0,
                "`{name}` is a type, not an effect";
                note: "an effect row holds effects, whose kind is `@Effect`, not `@Type`"
            ));
        }
        let d = diag!(Code::TypeUnbound, span, 0, "unknown effect `{name}`");
        let known = self.effect_arity.keys().map(|k| k.as_str()).chain(BUILTIN_EFFECTS.iter().copied());
        Some(match utilities::error::closest(name.as_str(), known) {
            Some(n) => d.with_fix(format!("did you mean `{n}`?"), vec![Edit::new(span, n)], Applicability::MaybeIncorrect),
            None => d.with_note("an effect is declared `$ Name : @Effect = op : Type, ...` here or in an imported module"),
        })
    }

    /// The type arguments of effect label `name` written with `args`. Omitted
    /// arguments of a parameterized effect are fresh variables, except inside
    /// that effect's own declaration, where they are its parameters. A label
    /// whose effect is not visible here keeps what was written, or matches any
    /// arguments when nothing was.
    pub(super) fn effect_label_args(
        &mut self,
        name: StrId,
        args: &[Aol<Ty>],
        span: Span,
        tvars: &mut HashMap<StrId, Type>,
    ) -> Type {
        if args.is_empty() {
            if let Some((own, own_args)) = self.effect_self {
                if own == name {
                    return own_args;
                }
            }
        }
        let arity = self.effect_arity.get(&name).copied();
        match arity {
            Some(0) if !args.is_empty() => self.defer_type_error(diag!(
                Code::TypeMismatch, span, 0,
                "effect `{name}` takes no parameters";
                note: "only an effect declared with parameters is applied in a row"
            )),
            Some(n) if !args.is_empty() && args.len() != n => self.defer_type_error(diag!(
                Code::TypeMismatch, span, 0,
                "effect `{name}` takes {n} parameter(s) but {} were given", args.len();
                help: "write all of them, or none to leave them to inference"
            )),
            _ => {}
        }
        let tys: Vec<Type> = if args.is_empty() {
            (0..arity.unwrap_or(0)).map(|_| self.unifier.fresh()).collect()
        } else {
            args.iter().map(|&a| self.ty_of_ast(a, tvars)).collect()
        };
        if tys.is_empty() {
            self.unifier.types.row_empty()
        } else {
            self.unifier.types.tuple(tys)
        }
    }

    /// Check the operand of a type or row splice `!X` under the `<@Meta>`
    /// ambient against `@Code`, so a string literal there is a quotation. See
    /// `Ty::MetaE` in `ty_of_ast`. The operand is its own boundary, as a `$ !`
    /// directive is: what it plans (a quotation's hole instances) resolves here,
    /// apart from the requirements of any definition it sits in.
    pub(super) fn meta_splice_operand(&mut self, expr: Aol<Expr>) {
        let ambient = self.meta_ambient();
        let saved = std::mem::replace(&mut self.ambient, ambient);
        let sites = self.deferred_sites.clone();
        let outer = (std::mem::take(&mut self.pending), std::mem::take(&mut self.ctx_pending));
        let code = self.unifier.types.con("@Code");
        let _ = self
            .check(expr, code)
            .and_then(|_| self.solve_pending())
            .and_then(|_| self.resolve_pending_ctx());
        (self.pending, self.ctx_pending) = outer;
        self.deferred_sites = sites;
        self.ambient = saved;
    }
}

// ## Elaboration

impl<'a> Checker<'a> {
    /// Elaborate a tensor size: a `Nat` literal, or a (Nat-kinded) size variable
    /// bound by name in `tvars` so `@Tensor n T -> @Tensor n U` shares the one size.
    pub(super) fn size_ty_of_ast(&mut self, ty: Aol<Ty>, tvars: &mut HashMap<StrId, Type>) -> Type {
        match self.tnode(ty) {
            Ty::Nat(n) => self.unifier.types.add(TypeNode::Nat(*n)),
            Ty::Var(name) if !tvars.contains_key(name) && self.nat_consts.contains_key(name) => {
                let name = *name;
                self.nat_const(name, self.ast.ty_span(ty))
            }
            Ty::Var(name) => {
                let name = *name;
                self.free_name(name, self.ast.ty_span(ty), tvars, ParamKind::Nat)
            }
            Ty::SizeAdd(a, b) => {
                let (a, b) = (*a, *b);
                let (x, y) = (
                    self.size_ty_of_ast(a, tvars),
                    self.size_ty_of_ast(b, tvars),
                );
                self.unifier.types.add(TypeNode::NatAdd(x, y))
            }
            Ty::SizeMul(a, b) => {
                let (a, b) = (*a, *b);
                let (x, y) = (
                    self.size_ty_of_ast(a, tvars),
                    self.size_ty_of_ast(b, tvars),
                );
                self.unifier.types.add(TypeNode::NatMul(x, y))
            }
            Ty::Term(e) if is_wildcard(self.ast, *e) => {
                let t = self.unifier.fresh_nat();
                self.wildcards.push((self.ast.ty_span(ty).unwrap_or(Span::at(0)), t));
                t
            }
            // Anything else conversion cannot evaluate: a call (`f n`), `-`.
            Ty::Term(_) | Ty::App(..) => {
                self.defer_type_error(dependent_only(self.ast.ty_span(ty), UNEVALUATED_SIZE));
                self.unifier.fresh_nat()
            }
            _ => self.ty_of_ast(ty, tvars),
        }
    }

    /// The value of an `Int` literal expression, else `None` (used to read the
    /// compile-time bounds of a range that builds a sized tensor).
    pub(super) fn int_literal(&self, e: Aol<Expr>) -> Option<i64> {
        match self.node(e) {
            Expr::Int(n) => Some(*n),
            _ => None,
        }
    }

    /// Peel one axis of a sized-tensor type `@tensor size elem` into
    /// `(size, elem)`.
    pub(super) fn tensor_parts(&self, ty: Type) -> Option<(Type, Type)> {
        self.unifier.tensor_spine(ty)
    }

    /// An application spine whose arity the caller has already checked: the
    /// partial applications inside it (`Pair @Int` in `Pair @Int @Str`) are not
    /// types of their own, so they are not checked again.
    pub(super) fn spine_of_ast(&mut self, ty: Aol<Ty>, tvars: &mut HashMap<StrId, Type>) -> Type {
        match self.tnode(ty) {
            Ty::App(head, arg) => {
                let (head, arg) = (*head, *arg);
                let h = self.spine_of_ast(head, tvars);
                let a = self.ty_of_ast(arg, tvars);
                self.unifier.types.app(h, a)
            }
            Ty::Con { .. } => self.con_of_ast(ty),
            _ => self.ty_of_ast(ty, tvars),
        }
    }

    /// A written application of a declared type puts each argument at the
    /// level its parameter takes. See Note [Declaration levels].
    fn check_decl_args(&mut self, ty: Aol<Ty>, applied: Type) {
        let mut written = Vec::new();
        let mut cur = ty;
        while let Ty::App(h, a) = self.tnode(cur) {
            written.push(*a);
            cur = *h;
        }
        written.reverse();
        let Ty::Con { name, .. } = self.tnode(cur) else { return };
        let Some(decl) = self.unifier.decl_levels.get(name).cloned() else { return };
        let mut args = Vec::new();
        let mut t = applied;
        while let TypeNode::App(h, a) = self.unifier.types.node(t) {
            args.push(a);
            t = h;
        }
        args.reverse();
        for ((param, &arg), &at) in decl.params.iter().zip(&args).zip(&written) {
            let span = self.ast.ty_span(at).unwrap_or(Span::at(0));
            match *param {
                ParamLevel::Stated(n) => {
                    let own = self.unifier.level_of(arg);
                    let level = self.unifier.types.add(TypeNode::Level(n));
                    if let Err(d) = self.unifier.unify(level, own, "in a type argument") {
                        self.universe_errors.push(d.fill_span(span));
                    }
                }
                ParamLevel::Free { at_most: Some(m) } => {
                    let own = self.unifier.level_of(arg);
                    let level = self.unifier.types.add(TypeNode::Level(m));
                    self.unifier.constrain_level(own, level, Some(span));
                }
                ParamLevel::Like(i) => {
                    if let Some(&first) = args.get(i) {
                        let (own, other) = (self.unifier.level_of(arg), self.unifier.level_of(first));
                        if let Err(d) = self.unifier.unify(other, own, "in a type argument") {
                            self.universe_errors.push(d.fill_span(span));
                        }
                    }
                }
                ParamLevel::Free { at_most: None } | ParamLevel::Other => {}
            }
        }
    }

    /// `(x: A) -> B` whose result names `x`: a dependent function type, which
    /// needs the elaborator of #406. Until then `x` in `B` is a type variable.
    fn dependent_arrow(&mut self, arrow: Aol<Ty>, binder: StrId, to: Aol<Ty>) {
        let Some(at) = self.ast.ty_mention(to, binder) else { return };
        if self.unknown_type.is_some() {
            return;
        }
        let name_span = self.ast.binder_spans.get(arrow).copied().unwrap_or(Span::at(0));
        let span = self.ast.ty_span(at).unwrap_or(name_span);
        self.unknown_type = Some(
            diag!(
                Code::UnexpectedToken, span, 0,
                "the result type names the parameter `{binder}`, which needs dependent types";
                note: "a function type whose result depends on its argument comes with \
                       dependent types (#406); until then `{binder}` here is a type variable";
                help: "rename the parameter, or the type variable if that is what you meant"
            )
            .with_label(name_span, "the parameter"),
        );
    }

    pub(super) fn con_of_ast(&mut self, ty: Aol<Ty>) -> Type {
        let Ty::Con { name, .. } = self.tnode(ty) else {
            unreachable!("con_of_ast on a non-constructor");
        };
        let name = *name;
        if !self.is_known_type(name) && self.unknown_type.is_none() {
            let mut d = match self.effect_arity.contains_key(&name) || BUILTIN_EFFECTS.contains(&name.as_str()) {
                true => diag!(
                    Code::TypeMismatch, Span::at(0), 0,
                    "`{name}` is an effect, not a type";
                    note: "an effect has kind `@Effect` and labels an effect row, as in `A -> <{name}> B`"
                ),
                false => self.unknown_type(name),
            };
            if let Some(span) = self.ast.ty_span(ty) {
                d = d.fill_span(span);
            }
            self.unknown_type = Some(d);
        }
        self.check_hidden_type(ty, name);
        self.unifier.types.con(name)
    }

    /// Elaborate the level of `@Type l`: a number, a level `tvars` binds, a
    /// level plus a number, or `@max a b`. See Note [Level parameters].
    fn level_of_ast(&mut self, ty: Aol<Ty>, tvars: &HashMap<StrId, Type>) -> Type {
        let is_max = |c: &Self, t: Aol<Ty>| matches!(c.tnode(t), Ty::Con { module: None, name } if name.as_str() == "@max");
        match self.tnode(ty) {
            Ty::Nat(n) => match u32::try_from(*n) {
                Ok(n) => self.unifier.types.add(TypeNode::Level(n)),
                Err(_) => {
                    self.defer_type_error(diag!(
                        Code::TypeMismatch, self.ty_span_or_none(ty), 0,
                        "the level {n} is too large";
                        note: "a level is below 2^32"
                    ));
                    self.unifier.fresh()
                }
            },
            Ty::Var(name) => {
                let name = *name;
                match tvars.get(&name) {
                    Some(&l) if self.level_names.contains(&l) => l,
                    _ => {
                        let d = self.unbound_level(name, self.ty_span_or_none(ty), tvars);
                        self.defer_type_error(d);
                        self.unifier.fresh()
                    }
                }
            }
            Ty::SizeAdd(l, k) => {
                let (l, k) = (*l, *k);
                let l = self.level_of_ast(l, tvars);
                match self.tnode(k) {
                    Ty::Nat(k) if u32::try_from(*k).is_ok() => self.unifier.types.add(TypeNode::LevelAdd(l, *k as u32)),
                    _ => {
                        self.defer_type_error(diag!(
                            Code::TypeMismatch, self.ty_span_or_none(ty), 0,
                            "a level is a number, a level name, `l + n` or `@max a b`"
                        ));
                        self.unifier.fresh()
                    }
                }
            }
            Ty::App(f, b) if matches!(self.tnode(*f), Ty::App(m, _) if is_max(self, *m)) => {
                let (f, b) = (*f, *b);
                let Ty::App(_, a) = *self.tnode(f) else { unreachable!("matched above") };
                let (a, b) = (self.level_of_ast(a, tvars), self.level_of_ast(b, tvars));
                self.unifier.types.add(TypeNode::LevelMax(a, b))
            }
            _ => {
                self.defer_type_error(diag!(
                    Code::TypeMismatch, self.ty_span_or_none(ty), 0,
                    "a level is a number, a level name, `l + n` or `@max a b`"
                ));
                self.unifier.fresh()
            }
        }
    }

    /// The level `ty` writes, as in `@Type ty`.
    pub(super) fn level_of_ty(&mut self, ty: Aol<Ty>, tvars: &HashMap<StrId, Type>) -> Type {
        self.level_of_ast(ty, tvars)
    }

    /// `name` stands where a level does, and no `@ctx {name: @l}` binds it.
    pub(super) fn unbound_level(&self, name: StrId, span: Span, tvars: &HashMap<StrId, Type>) -> Diagnostic {
        let known: Vec<&str> = tvars.iter().filter(|(_, t)| self.level_names.contains(t)).map(|(n, _)| n.as_str()).collect();
        let mut d = diag!(
            Code::TypeUnbound, span, 0,
            "the level `{name}` is not bound";
            note: "a level is bound in the signature's first `@ctx`, as in `@ctx {{{name}: @l}} -> ...`"
        );
        if let Some(c) = utilities::error::closest(name.as_str(), known.iter().copied()) {
            d = d.with_help(format!("did you mean `{c}`?"));
        }
        d
    }

    pub(super) fn ty_of_ast(&mut self, ty: Aol<Ty>, tvars: &mut HashMap<StrId, Type>) -> Type {
        // An alias at the head of an application spine expands first, so `MapInt Bool`
        // substitutes into `Map Int Bool` rather than forming `App(alias, Bool)`.
        if let Some(t) = self.try_expand_alias(ty, tvars) {
            return t;
        }
        match self.tnode(ty) {
            // A bare `@Type` is a universe at a fresh level, which the
            // definition's scheme generalises. See Note [Universe levels].
            Ty::Con { module: None, name } if name.as_str() == ty::UNIVERSE => self.unifier.fresh_universe(),
            Ty::App(head, level) if matches!(self.tnode(*head), Ty::Con { module: None, name } if name.as_str() == ty::UNIVERSE) => {
                let level = self.level_of_ast(*level, tvars);
                self.unifier.types.universe(level)
            }
            Ty::Con { .. } => {
                self.check_type_arity(ty, true);
                self.con_of_ast(ty)
            }
            Ty::Var(name) if !tvars.contains_key(name) && self.nat_consts.contains_key(name) => {
                let name = *name;
                self.nat_const(name, self.ast.ty_span(ty))
            }
            Ty::Var(name) if tvars.get(name).is_some_and(|t| self.level_names.contains(t)) => {
                let name = *name;
                self.defer_type_error(diag!(
                    Code::TypeMismatch, self.ty_span_or_none(ty), 0,
                    "`{name}` is a level, which stands only in a universe";
                    help: "write `@Type {name}` for the universe at level `{name}`"
                ));
                self.unifier.fresh()
            }
            Ty::Var(name) => {
                let name = *name;
                self.free_name(name, self.ast.ty_span(ty), tvars, ParamKind::Type)
            }
            Ty::App(head, size) if matches!(self.tnode(*head), Ty::Con { module: None, name } if *name == SIZE_OF) => {
                let size = self.size_ty_of_ast(*size, tvars);
                let head = self.unifier.types.con(StrId::intern(SIZE_OF));
                self.unifier.types.app(head, size)
            }
            Ty::App(..) => {
                self.check_type_arity(ty, true);
                let applied = self.spine_of_ast(ty, tvars);
                self.check_decl_args(ty, applied);
                applied
            }
            // `!X` in type position: infer `X` (so its calls/overloads resolve
            // for lowering) and require it to build `@Code`; the spliced-in type is
            // unknown until the driver's expand loop runs `X`, so it stands as a
            // fresh variable here. Only reachable in a lenient (pre-expansion)
            // round; the final strict compile sees the substituted concrete type.
            //
            // Signatures are elaborated before any global is in scope, so every
            // name the operand mentions takes the lenient branch here even though
            // lowering resolves it. Those are not deferred sites: holding the
            // operand back for them would hold it forever.
            Ty::MetaE(expr) => {
                let expr = *expr;
                self.meta_splice_operand(expr);
                self.unifier.fresh()
            }
            Ty::Nat(n) => self.unifier.types.add(TypeNode::Nat(*n)),
            // A size expression written in type position (only well-formed inside a
            // `[..]`); elaborate it as a size so kind-checking flags any misuse.
            Ty::SizeAdd(..) | Ty::SizeMul(..) => self.size_ty_of_ast(ty, tvars),
            Ty::Sized { size, elem } => {
                let (size, elem) = (*size, *elem);
                let size_ty = self.size_ty_of_ast(size, tvars);
                let elem_ty = self.ty_of_ast(elem, tvars);
                tensor_type(&self.unifier.types, size_ty, elem_ty)
            }
            // `_`: a type left to elaboration, a fresh variable whatever uses it
            // solves.
            Ty::Term(e) if is_wildcard(self.ast, *e) => {
                let t = self.unifier.fresh();
                self.wildcards.push((self.ast.ty_span(ty).unwrap_or(Span::at(0)), t));
                t
            }
            Ty::Term(e) => {
                if self.unknown_type.is_none() {
                    self.unknown_type = Some(self.not_a_type(ty, *e));
                }
                self.unifier.fresh()
            }
            Ty::Arrow { from, effect, to, binder } => {
                let (from, to, binder) = (*from, *to, *binder);
                // `(t: @Type) -> B` and `(n: @Nat) -> B`: `B` may name the
                // parameter, whose argument fixes it at each call.
                let singleton = match (binder, self.kind_of_ast(from)) {
                    (Some(name), Some(kind @ (ParamKind::Type | ParamKind::Nat))) => {
                        let v = match kind {
                            ParamKind::Nat => self.unifier.fresh_nat(),
                            _ => self.leveled_var(from, tvars),
                        };
                        tvars.insert(name, v);
                        let head = if kind == ParamKind::Nat { SIZE_OF } else { ty::TYPE_OF };
                        let head = self.unifier.types.con(StrId::intern(head));
                        Some(self.unifier.types.app(head, v))
                    }
                    (Some(name), _) => {
                        self.dependent_arrow(ty, name, to);
                        tvars.entry(name).or_insert_with(|| self.unifier.fresh());
                        None
                    }
                    (None, _) => None,
                };
                // An unannotated arrow is pure.
                let eff = match effect {
                    Some(row) => {
                        let foreign = self.foreign_tys.contains(&ty);
                        self.row_of_ast(row.entries, row.tail, row.tail_span, foreign, tvars)
                    }
                    None => self.unifier.types.row_empty(),
                };
                let f = match singleton {
                    Some(s) => s,
                    None => self.ty_of_ast(from, tvars),
                };
                let t = self.ty_of_ast(to, tvars);
                self.unifier.types.arrow_eff(f, t, eff)
            }
            Ty::Unit => self.unifier.types.con(ty::UNIT),
            Ty::Tuple(items) => {
                let items = self.ast.slice(*items);
                let mapped: Vec<Type> =
                    items.iter().map(|t| self.ty_of_ast(*t, tvars)).collect();
                self.unifier.types.tuple(mapped)
            }
            Ty::Record { fields, tail } => {
                // A record type: `{ x: A | r }` is open (row variable tail), `{ x: A,
                // y: B }` is closed (empty tail). Records are real, name-keyed types;
                // positional/scalar values promote to them at call sites.
                let rest = match tail {
                    Some(tvar) => {
                        let tvar = *tvar;
                        self.free_name(tvar, self.ast.ty_span(ty), tvars, ParamKind::Row)
                    }
                    None => self.unifier.types.row_empty(),
                };
                let decls: Vec<_> = self.ast.slice(*fields).to_vec();
                let mut row = rest;
                for f in decls.iter().rev() {
                    let fty = self.ty_of_ast(f.ty, tvars);
                    row = self.unifier.types.row_field(f.name, fty, row);
                }
                self.unifier.types.record(row)
            }
        }
    }
}

/// What conversion evaluates in a size is literals, size variables, `@Nat`
/// constants, `+` and `*`; anything else waits for the elaborator of #406.
const UNEVALUATED_SIZE: &str = "a size other than literals, size variables, `@Nat` constants, `+` and `*`";

/// Why a `@Nat` constant does not unfold to a size.
pub(super) enum SizeError {
    Cycle,
    /// A subterm conversion cannot evaluate (a call, a negative literal).
    Term(Aol<Expr>),
}

/// The `name: @Kind` fields that bind `names` in a `@ctx`.
pub(super) fn ctx_fields(names: &[(StrId, Option<Span>, ParamKind)]) -> Vec<String> {
    names.iter().map(|(n, _, k)| format!("{n}: {}", k.written())).collect()
}

/// What binds the names an [`unbound_names`] error reports, with the edit
/// that binds them there if one can be made.
pub(super) enum Binder {
    /// A global's or effect operation's signature, whose leading `@ctx` takes them.
    Signature(Option<Edit>),
    /// A constructor's `@ctx`.
    Constructor(Option<Edit>),
    /// An annotation inside a body: the enclosing definition's signature.
    Body,
}

/// The error for type variables nothing binds, `names` in order of first use,
/// each with the kind its uses give.
pub(super) fn unbound_names(names: &[(StrId, Option<Span>, ParamKind)], binder: Binder) -> Diagnostic {
    let fields = ctx_fields(names);
    let quoted: Vec<String> = names.iter().map(|(n, _, _)| format!("`{n}`")).collect();
    let (shown, verb) = match quoted.as_slice() {
        [one] => (one.clone(), "is"),
        [init @ .., last] => (format!("{} and {last}", init.join(", ")), "are"),
        [] => unreachable!("at least one unbound name"),
    };
    let first = names[0].1.unwrap_or(Span::at(0));
    let note = match binder {
        Binder::Constructor(_) => {
            "a constructor binds its own variables in `@ctx`, as in `Cons: @ctx {n: @Nat} -> {a, Vec a n} -> Vec a (n + 1)`"
        }
        _ => "a signature binds its type variables in `@ctx`, as in `@ctx {t: @Type} -> t -> t`",
    };
    let mut d = Diagnostic::error(Code::TypeUnbound, first, 0, format!("{shown} {verb} not bound")).with_note(note);
    for (_, span, _) in &names[1..] {
        if let Some(span) = span {
            d = d.with_label(*span, "");
        }
    }
    let (whose, edit) = match binder {
        Binder::Signature(edit) => ("signature", edit),
        Binder::Constructor(edit) => ("constructor", edit),
        Binder::Body => {
            return d.with_help(format!(
                "bind {shown} in the enclosing definition's `@ctx`, or write `_` for a type left to inference"
            ))
        }
    };
    let fix = format!("bind {shown} in the {whose}'s `@ctx`");
    match edit {
        Some(edit) => d.with_fix(fix, vec![edit], Applicability::MachineApplicable),
        None => d.with_help(format!("{fix}: `@ctx {{{}}} -> ...`", fields.join(", "))),
    }
}
