//! Type declarations: structs, unions, aliases and effects.
//!
//! [`Checker::register_types`] records every declaration before any body is
//! checked, so definitions may refer to types declared later. It records which
//! types still wait on `!` entry splices, rejects alias cycles, computes which constructor slots
//! are lazy, and registers each struct's record row for the nominal-to-row
//! bridge. The lookups below answer the questions inference asks of a
//! declaration: a struct's fields, a variant's payload, a tag's union.
//!
//! Entry points: [`Checker::register_types`], [`Checker::register_effects`].

use super::*;
use super::signatures::{ctx_fields, unbound_names, Binder};

// ## Type parameters

impl<'a> Checker<'a> {
    /// A type's parameter list is exactly what its signature binds. Every
    /// type variable used in the body must be declared (an undeclared one is an
    /// error: parameters are mandatory, never inferred). A declared parameter that
    /// appears nowhere is allowed (a phantom). `kind` is the keyword, for the error.
    pub(super) fn resolve_type_params(
        &self,
        kind: &str,
        name: StrId,
        declared: &[utilities::StrId],
        collected: Vec<(StrId, Span)>,
    ) -> Result<Vec<StrId>> {
        let declared: Vec<StrId> = declared.to_vec();
        for (v, span) in &collected {
            if !declared.contains(v) {
                return Err(undeclared_param(kind, name, v, &declared).fill_span(*span));
            }
        }
        Ok(declared)
    }

    /// A declared type's recorded span, or the no-location sentinel.
    pub(super) fn ty_span_or_none(&self, ty: Aol<Ty>) -> Span {
        self.ast.ty_span(ty).unwrap_or(Span::at(0))
    }

    /// Every type variable used across `tys`, each paired with the span of the
    /// type it was found in, so an undeclared one carets that field or payload
    /// rather than the whole declaration.
    pub(super) fn tyvars_with_spans(&self, tys: impl IntoIterator<Item = Aol<Ty>>) -> Vec<(StrId, Span)> {
        let mut out: Vec<(StrId, Span)> = Vec::new();
        for ty in tys {
            let mut vs = Vec::new();
            collect_tyvars(self.ast, ty, &mut vs);
            let span = self.ty_span_or_none(ty);
            for v in vs {
                // A lowercase name may be a global instead: it needs no declaring.
                if self.is_type_global(v) {
                    continue;
                }
                if !out.iter().any(|(n, _)| *n == v) {
                    out.push((v, span));
                }
            }
        }
        out
    }
}

// ## Kinds

impl<'a> Checker<'a> {
    /// What each binder of a type declaration's signature ranges over; the
    /// signature ends in `@Type`.
    /// A parameter of any other type, `(b: Bool)`, makes the type depend on
    /// a value, which needs the kernel.
    pub(super) fn decl_kinds(&self, sig: Aol<Ty>) -> Result<Vec<ParamKind>> {
        let mut kinds = Vec::new();
        let mut cur = sig;
        while let Ty::Arrow { from, to, .. } = self.ast.ty(cur) {
            let Some(kind) = self.kind_of_ast(*from) else {
                return Err(dependent_only(self.ast.ty_span(*from), "a type parameter that is a value"));
            };
            kinds.push(kind);
            cur = *to;
        }
        let universe = |t: &Ty| matches!(t, Ty::Con { module: None, name } if name.as_str() == "@Type");
        let ends_in_universe = match self.ast.ty(cur) {
            Ty::App(head, _) => universe(self.ast.ty(*head)),
            t => universe(t),
        };
        if !ends_in_universe {
            return Err(diag!(
                Code::TypeMismatch, self.ty_span_or_none(cur), 0,
                "a type declaration's signature ends in `@Type`";
                help: "state the parameters and then the universe, as in `(a: @Type) -> @Type`"
            ));
        }
        Ok(kinds)
    }

    /// The kind a binder's written type gives it: `@Type` (or `@Type n`),
    /// `@Nat` or `@Row`. `None` for any other type, whose binder is a value.
    pub(super) fn kind_of_ast(&self, ty: Aol<Ty>) -> Option<ParamKind> {
        let named = |t: &Ty, n: &str| matches!(t, Ty::Con { module: None, name } if name.as_str() == n);
        match self.ast.ty(ty) {
            t if named(t, "@Type") => Some(ParamKind::Type),
            Ty::App(head, _) if named(self.ast.ty(*head), "@Type") => Some(ParamKind::Type),
            t if named(t, "@Nat") => Some(ParamKind::Nat),
            t if named(t, "@Row") => Some(ParamKind::Row),
            _ => None,
        }
    }

    /// The names of a type declaration's binders, an unnamed index called
    /// `i1`, `i2`, ... by its position.
    pub(super) fn decl_binder_names(&self, sig: Aol<Ty>) -> Vec<StrId> {
        let mut names = Vec::new();
        let mut cur = sig;
        while let Ty::Arrow { binder, to, .. } = self.ast.ty(cur) {
            names.push(binder.unwrap_or_else(|| StrId::intern(&format!("i{}", names.len() + 1))));
            cur = *to;
        }
        names
    }

    /// A constructor's stated result builds its own union, applied to every
    /// parameter and index: `Cons: @ctx {n: @Nat} -> {a, Vec a n} -> Vec a (n + 1)`.
    fn check_variant_result(&self, union: StrId, tag: StrId, result: Aol<Ty>, arity: usize) -> Result<()> {
        let mut args = 0;
        let mut head = result;
        while let Ty::App(f, _) = self.ast.ty(head) {
            args += 1;
            head = *f;
        }
        let span = self.ty_span_or_none(result);
        if !matches!(self.ast.ty(head), Ty::Con { name, .. } if *name == union) {
            return Err(diag!(
                Code::TypeMismatch, span, 0,
                "the constructor `{tag}` states a result that is not `{union}`";
                note: "a constructor builds a value of its own union"
            ));
        }
        if args != arity {
            return Err(diag!(
                Code::TypeMismatch, span, 0,
                "type `{union}` takes {arity} parameter(s) and indices but {args} {} given",
                if args == 1 { "was" } else { "were" }
            ));
        }
        Ok(())
    }

    /// What the parameters of the type `name` range over, if it is one whose
    /// parameters are known.
    pub(super) fn param_kinds(&self, name: StrId) -> Option<Vec<ParamKind>> {
        if let Some(info) = self.structs.get(&name) {
            return Some(info.kinds.clone());
        }
        if let Some(info) = self.unions.get(&name) {
            return Some(info.kinds.clone());
        }
        if let Some((params, body)) = self.aliases.get(&name) {
            let mut sizes = Vec::new();
            collect_size_vars(self.ast, *body, false, &mut sizes);
            return Some(params.iter().map(|p| if sizes.contains(p) { ParamKind::Nat } else { ParamKind::Type }).collect());
        }
        if is_base_type(name.as_str()) {
            let arity = usize::from(matches!(name.as_str(), "@Vec" | "@Future" | "@Chan" | "@TVar"));
            return Some(vec![ParamKind::Type; arity]);
        }
        None
    }

    /// Check that each type declared in this module uses its parameters as
    /// what they range over: a `@Nat` one as a size, a `@Row` one as a row
    /// tail or an effect's row argument, a `@Type` one as a type. A
    /// constructor's or operation's own variables are bound by its `@ctx`,
    /// which says what each ranges over.
    pub(super) fn check_decl_kinds(&mut self, program: &Program) -> Result<()> {
        for item in self.ast.slice(program.items) {
            let (name, members): (StrId, Vec<Aol<Ty>>) = match item {
                Item::Struct { name, fields, .. } => (*name, self.ast.slice(*fields).iter().map(|f| f.ty).collect()),
                Item::Effect { name, ops, .. } => (*name, self.ast.slice(*ops).iter().map(|f| f.ty).collect()),
                Item::Union { name, .. } => (*name, Vec::new()),
                _ => continue,
            };
            let (params, kinds): (Vec<StrId>, Vec<ParamKind>) = match item {
                Item::Effect { params, .. } => (self.ast.slice(*params).to_vec(), self.effect_kinds[&name].clone()),
                Item::Struct { .. } => {
                    let info = &self.structs[&name];
                    (info.params.clone(), info.kinds.clone())
                }
                _ => {
                    let info = &self.unions[&name];
                    (info.params[..info.uniform].to_vec(), info.kinds[..info.uniform].to_vec())
                }
            };
            let env: HashMap<StrId, ParamKind> = params.into_iter().zip(kinds).collect();
            for ty in members {
                let mut env = env.clone();
                self.bind_own_ctx(self.ast.ctx_params.get(ty).copied(), &mut env);
                self.check_kind(ty, Some(ParamKind::Type), &mut env)?;
            }
            let Item::Union { variants: decls, .. } = item else { continue };
            let info = self.unions[&name].clone();
            let uniform = &info.params[..info.uniform];
            let mut owns = Vec::new();
            for (v, decl) in info.variants.iter().zip(self.ast.slice(*decls)) {
                self.check_own_ctx(name, v.tag, uniform, Some(decl.ctx))?;
                let mut env = env.clone();
                let ctx = self.ast.slice(decl.ctx).to_vec();
                self.bind_own_ctx(Some(decl.ctx), &mut env);
                if let Some(result) = v.result {
                    self.check_kind(result, Some(ParamKind::Type), &mut env)?;
                }
                for (_, ty) in &v.payload {
                    self.check_kind(*ty, Some(ParamKind::Type), &mut env)?;
                }
                let mut own: Vec<(StrId, ParamKind)> =
                    ctx.iter().filter_map(|f| self.kind_of_ast(f.ty).map(|k| (f.name, k))).collect();
                if v.result.is_some() {
                    let mut uses = Vec::new();
                    v.payload.iter().for_each(|(_, t)| collect_tyvar_uses(self.ast, *t, &mut uses));
                    v.result.iter().for_each(|r| collect_tyvar_uses(self.ast, *r, &mut uses));
                    let unbound: Vec<(StrId, Option<Span>, ParamKind)> = uses
                        .into_iter()
                        .filter(|(x, _)| !uniform.contains(x) && !own.iter().any(|(o, _)| o == x))
                        .filter_map(|(x, span)| env.get(&x).map(|k| (x, span, *k)))
                        .collect();
                    if !unbound.is_empty() {
                        let fields = ctx_fields(&unbound).join(", ");
                        let edit = match (ctx.last(), decl.ctx_at) {
                            (Some(last), _) => Some(Edit::new(Span::at(last.span.end), format!(", {fields}"))),
                            (None, Some(at)) => Some(Edit::new(Span::at(at), format!("@ctx {{{fields}}} -> "))),
                            (None, None) => None,
                        };
                        self.errors.push(unbound_names(&unbound, Binder::Constructor(edit)));
                        own.extend(unbound.into_iter().map(|(x, _, k)| (x, k)));
                    }
                }
                owns.push(own);
            }
            let info = self.unions.get_mut(&name).expect("registered above");
            for (v, own) in info.variants.iter_mut().zip(owns) {
                v.own = own;
            }
        }
        Ok(())
    }

    /// Give each field of a constructor's or operation's `@ctx` the kind it
    /// declares.
    fn bind_own_ctx(&self, ctx: Option<Slice<UseField>>, env: &mut HashMap<StrId, ParamKind>) {
        for f in ctx.map(|c| self.ast.slice(c).to_vec()).unwrap_or_default() {
            if let Some(k) = self.kind_of_ast(f.ty) {
                env.insert(f.name, k);
            }
        }
    }

    /// Check a constructor's or operation's `@ctx` (`member` of `decl`) binds
    /// only variables of its own, each a type, a size or a row.
    pub(super) fn check_own_ctx(&self, decl: StrId, member: StrId, params: &[StrId], ctx: Option<Slice<UseField>>) -> Result<()> {
        for f in ctx.map(|c| self.ast.slice(c).to_vec()).unwrap_or_default() {
            if params.contains(&f.name) {
                return Err(diag!(
                    Code::DuplicateSymbol, f.span, 0,
                    "`{}` is a parameter of `{decl}`, which `{member}`'s `@ctx` cannot bind again", f.name;
                    help: "drop `{}` from the `@ctx`: `{member}` sees `{decl}`'s parameters", f.name
                ));
            }
            if self.kind_of_ast(f.ty).is_none() {
                return Err(diag!(
                    Code::TypeMismatch, f.span, 0,
                    "`@ctx` field `{}` of `{member}` is not a type, a size or a row", f.name;
                    note: "`@ctx` binds what unification solves: `@Type`, `@Nat` or `@Row`"
                ));
            }
        }
        Ok(())
    }

    /// Check `ty` stands where a `want` is expected (`None`: unknown, as an
    /// argument of a type-level function or a variable).
    fn check_kind(&self, ty: Aol<Ty>, want: Option<ParamKind>, env: &mut HashMap<StrId, ParamKind>) -> Result<()> {
        let want_type = Some(ParamKind::Type);
        match self.ast.ty(ty) {
            Ty::Var(v) if env.contains_key(v) || !self.is_type_global(*v) => {
                let Some(want) = want else { return Ok(()) };
                let have = *env.entry(*v).or_insert(want);
                if have != want {
                    return Err(diag!(
                        Code::TypeMismatch, self.ty_span_or_none(ty), 0,
                        "`{v}` is a `{}`, but it stands where a `{}` is expected", have.written(), want.written();
                        help: "declare `{v}` as a `{}` if that is what it ranges over", want.written()
                    ));
                }
            }
            Ty::App(..) => {
                let mut args = Vec::new();
                let mut head = ty;
                while let Ty::App(f, a) = self.ast.ty(head) {
                    args.push(*a);
                    head = *f;
                }
                args.reverse();
                let kinds = match self.ast.ty(head) {
                    Ty::Con { name, .. } | Ty::Var(name) if !env.contains_key(name) => self.param_kinds(*name),
                    _ => None,
                };
                for (i, a) in args.into_iter().enumerate() {
                    let want = match &kinds {
                        Some(ks) => ks.get(i).copied(),
                        None => None,
                    };
                    self.check_kind(a, want, env)?;
                }
            }
            Ty::Sized { size, elem } => {
                self.check_kind(*size, Some(ParamKind::Nat), env)?;
                self.check_kind(*elem, want_type, env)?;
            }
            Ty::SizeAdd(a, b) | Ty::SizeMul(a, b) => {
                self.check_kind(*a, Some(ParamKind::Nat), env)?;
                self.check_kind(*b, Some(ParamKind::Nat), env)?;
            }
            Ty::Arrow { from, effect, to, .. } => {
                self.check_kind(*from, want_type, env)?;
                self.check_kind(*to, want_type, env)?;
                if let Some(row) = effect {
                    for entry in self.ast.slice(row.entries) {
                        let kinds = self.effect_kinds.get(&entry.name);
                        for (i, a) in self.ast.slice(entry.args).iter().enumerate() {
                            self.check_kind(*a, kinds.and_then(|ks| ks.get(i).copied()), env)?;
                        }
                    }
                    if let Some(tail) = row.tail {
                        self.check_tail(tail, ty, env)?;
                    }
                }
            }
            Ty::Tuple(items) => {
                for t in self.ast.slice(*items) {
                    self.check_kind(*t, want_type, env)?;
                }
            }
            Ty::Record { fields, tail } => {
                for f in self.ast.slice(*fields) {
                    self.check_kind(f.ty, want_type, env)?;
                }
                if let Some(tail) = tail {
                    self.check_tail(*tail, ty, env)?;
                }
            }
            _ => {}
        }
        Ok(())
    }

    /// A row tail `| e` is a `@Row`.
    fn check_tail(&self, tail: StrId, at: Aol<Ty>, env: &mut HashMap<StrId, ParamKind>) -> Result<()> {
        let have = *env.entry(tail).or_insert(ParamKind::Row);
        if have != ParamKind::Row {
            return Err(diag!(
                Code::TypeMismatch, self.ty_span_or_none(at), 0,
                "`{tail}` is a `{}`, but it stands where a `@Row` is expected", have.written();
                help: "declare `{tail}` as a `@Row` if that is what it ranges over"
            ));
        }
        Ok(())
    }
}

// ## Registration

impl<'a> Checker<'a> {
    pub(super) fn register_types(&mut self, program: &Program) -> Result<()> {
        self.reject_dependent_defs(program)?;
        self.reject_declared_wildcards(program)?;
        for item in self.ast.slice(program.items) {
            if let Item::Def { name, sig: Some(sig), ctx: None, body } = item {
                if matches!(self.ast.ty(*sig), Ty::Con { module: None, name } if name.as_str() == "@Nat") {
                    self.nat_consts.insert(*name, *body);
                }
            }
        }
        for item in self.ast.slice(program.items).iter() {
            match item {
                Item::Struct {
                    name,
                    sig,
                    params,
                    splices,
                    fields,
                    abi,
                    c_union,
                } => {
                    let kinds = self.decl_kinds(*sig)?;
                    let (params, splices, fields) = (
                        self.ast.slice(*params),
                        self.ast.slice(*splices),
                        self.ast.slice(*fields),
                    );
                    let collected = self.tyvars_with_spans(fields.iter().map(|f| f.ty));
                    let name = *name;
                    // A blessed interface is the compiler's own: CORE declares it, and
                    // exactly one field, because a desugar site projects that field
                    // without knowing its name.
                    if is_blessed_interface(name.as_str()) {
                        let at = fields
                            .first()
                            .map_or(Span::at(0), |f| self.ty_span_or_none(f.ty));
                        if self.module_name != "CORE" {
                            return Err(diag!(
                                Code::TypeMismatch, at, 0,
                                "`{name}` is a blessed interface and only CORE may declare it";
                                help: "implement it instead: a value of the applied type \
                                       (`$ r : @IRange @Int Span = .{{ .range = ... }}`)"
                            ));
                        }
                        if fields.len() != 1 {
                            return Err(diag!(
                                Code::TypeMismatch, at, 0,
                                "the blessed interface `{name}` must have exactly one field, \
                                 not {}", fields.len()
                            ));
                        }
                    }
                    let params = self.resolve_type_params("struct", name, params, collected)?;
                    for (i, f) in fields.iter().enumerate() {
                        if fields[..i].iter().any(|g| g.name == f.name) {
                            return Err(dup_member(name, f.name, "field").fill_span(self.ty_span_or_none(f.ty)));
                        }
                    }
                    let fields = fields.iter().map(|f| (f.name, f.ty)).collect();
                    let crepr = abi.is_some();
                    self.claim_type_name(name);
                    self.structs.insert(
                        name,
                        StructInfo {
                            params,
                            kinds,
                            fields,
                            crepr,
                            c_union: *c_union,
                        },
                    );
                    self.own_type_names.push(name);
                    self.pend_entry_splices(name, splices);
                }
                Item::Union {
                    name,
                    sig,
                    params,
                    splices,
                    variants,
                } => {
                    let kinds = self.decl_kinds(*sig)?;
                    let binders = self.decl_binder_names(*sig);
                    let uniform = params.len();
                    let (params, splices, variants) = (
                        self.ast.slice(*params),
                        self.ast.slice(*splices),
                        self.ast.slice(*variants),
                    );
                    let mut payload_tys = Vec::new();
                    let mut vs = Vec::with_capacity(variants.len());
                    for (i, v) in variants.iter().enumerate() {
                        let payload = payload_fields(self.ast, &v.payload);
                        let at = v.tag_span;
                        if variants[..i].iter().any(|w| w.tag == v.tag) {
                            return Err(dup_member(*name, v.tag, "variant").fill_span(at));
                        }
                        match v.result {
                            Some(result) => self.check_variant_result(*name, v.tag, result, binders.len())?,
                            None if binders.len() > uniform => {
                                return Err(unstated_result(*name, v.tag, &binders[..uniform]).fill_span(at));
                            }
                            // A constructor's own variables are bound by the
                            // result it states; the others' must be parameters.
                            None => payload_tys.extend(payload.iter().map(|(_, ty)| *ty)),
                        }
                        vs.push(VariantSig {
                            tag: v.tag,
                            payload,
                            result: v.result,
                            own: Vec::new(),
                        });
                    }
                    let collected = self.tyvars_with_spans(payload_tys);
                    let name = *name;
                    self.resolve_type_params("union", name, params, collected)?;
                    self.claim_type_name(name);
                    self.unions.insert(
                        name,
                        UnionInfo {
                            params: binders,
                            kinds,
                            uniform,
                            variants: vs,
                        },
                    );
                    self.own_type_names.push(name);
                    self.pend_entry_splices(name, splices);
                }
                Item::Alias { name, params, ty, sig, .. } => {
                    self.check_type_function_sig(*sig)?;
                    let params = self.ast.slice(*params);
                    let collected = self.tyvars_with_spans([*ty]);
                    let name = *name;
                    let params = self.resolve_type_params("alias", name, params, collected)?;
                    self.claim_type_name(name);
                    let levels = self.sig_param_levels(*sig);
                    self.alias_param_levels.insert(name, levels);
                    self.aliases.insert(name, (params, *ty));
                    self.own_type_names.push(name);
                }
                _ => {}
            }
        }
        self.check_alias_cycles()?;
        self.compute_lazy_slots();
        Ok(())
    }

    /// The constant level of each parameter of a type-level function's
    /// signature: `Some(n)` for `@Type n`, `None` for anything else.
    fn sig_param_levels(&self, sig: Aol<Ty>) -> Vec<Option<u32>> {
        let mut out = Vec::new();
        let mut cur = sig;
        while let Ty::Arrow { from, to, .. } = self.ast.ty(cur) {
            out.push(match self.ast.ty(*from) {
                Ty::App(head, n) if matches!(self.ast.ty(*head), Ty::Con { module: None, name } if name.as_str() == "@Type") => {
                    match self.ast.ty(*n) {
                        Ty::Nat(n) => u32::try_from(*n).ok(),
                        _ => None,
                    }
                }
                _ => None,
            });
            cur = *to;
        }
        out
    }

    /// Check each type-level function's body lives in the universe its
    /// signature states: `$ T : @Type 1 = @Type 1` does not. Its parameters
    /// stand at the levels the signature gives them.
    pub(super) fn check_alias_levels(&mut self, program: &Program) -> Result<()> {
        let items = self.ast.slice(program.items);
        let spans = self.ast.slice(program.spans);
        for (item, at) in items.iter().zip(spans) {
            let Item::Alias { params, ty, sig, .. } = item else { continue };
            let (params, ty, sig) = (self.ast.slice(*params).to_vec(), *ty, *sig);
            self.unifier.enter_level();
            let mark = self.unifier.level_mark();
            let saved = self.unknown_type.take();
            let mut tvars = HashMap::new();
            let mut cur = sig;
            let mut i = 0;
            while let Ty::Arrow { from, to, .. } = self.ast.ty(cur) {
                let (from, to) = (*from, *to);
                if let Some(p) = params.get(i) {
                    let v = match self.kind_of_ast(from) {
                        Some(ParamKind::Nat) => self.unifier.fresh_nat(),
                        _ => self.leveled_var(from),
                    };
                    tvars.insert(*p, v);
                }
                i += 1;
                cur = to;
            }
            let result = self.ty_of_ast(cur, &mut HashMap::new());
            let body = self.ty_of_ast(ty, &mut tvars);
            self.unknown_type = saved;
            let span = self.ast.ty_span(ty).or(at.name).unwrap_or(at.full);
            let equated = match self.unifier.types.universe_level(self.unifier.resolve(result)) {
                Some(r) => {
                    let own = self.unifier.level_of(body);
                    self.unifier.unify(r, own, "in the body of a type")
                }
                None => Ok(()),
            };
            let settled = self.unifier.settle_levels(mark, &HashSet::new());
            self.unifier.forget_levels(mark);
            self.unifier.leave_level();
            if let Some(d) = self.universe_errors.drain(..).next() {
                return Err(d);
            }
            equated.map_err(|d| d.fill_span(span))?;
            if let Err((c, lhs, rhs)) = settled {
                return Err(universe_error(c.span.unwrap_or(span), &lhs, &rhs));
            }
        }
        Ok(())
    }

    /// A type-level function's parameters are types or sizes, and it returns
    /// a type of data: `@Type -> @Nat -> @Type`. Anything else is a family
    /// indexed by values, or a universe level, which only the kernel checks.
    fn check_type_function_sig(&self, sig: Aol<Ty>) -> Result<()> {
        let is_con = |t: Aol<Ty>, want: &str| matches!(self.ast.ty(t), Ty::Con { module: None, name } if name.as_str() == want);
        let mut cur = sig;
        while let Ty::Arrow { from, to, .. } = self.ast.ty(cur) {
            if self.kind_of_ast(*from) != Some(ParamKind::Type) && !is_con(*from, "@Nat") {
                return Err(dependent_only(self.ast.ty_span(*from), "a type indexed by a value other than a size"));
            }
            cur = *to;
        }
        if self.kind_of_ast(cur) != Some(ParamKind::Type) {
            return Err(dependent_only(self.ast.ty_span(cur), "a type-level function returning something other than a type"));
        }
        Ok(())
    }

    /// A `_` stands where a definition's body can solve it. A type
    /// declaration has no body, so its types are written out; so is the
    /// signature of a foreign or builtin definition, and of one with `@use`
    /// parameters, which every use elaborates again.
    fn reject_declared_wildcards(&self, program: &Program) -> Result<()> {
        let ast = self.ast;
        for item in ast.slice(program.items) {
            let (tys, what): (Vec<Aol<Ty>>, &str) = match item {
                Item::Struct { fields, .. } => (ast.slice(*fields).iter().map(|f| f.ty).collect(), "a type declaration"),
                Item::Union { variants, .. } => (
                    ast.slice(*variants).iter().flat_map(|v| payload_fields(ast, &v.payload)).map(|(_, t)| t).collect(),
                    "a type declaration",
                ),
                Item::Effect { ops, .. } => (ast.slice(*ops).iter().map(|f| f.ty).collect(), "an effect declaration"),
                Item::Alias { ty, .. } => (vec![*ty], "a type-level function"),
                Item::Def { sig: Some(sig), body, .. } if matches!(ast.expr(*body), Expr::Extern { .. } | Expr::Builtin) => {
                    (vec![*sig], "a foreign or builtin signature")
                }
                Item::Def { sig: Some(sig), ctx: Some(_), .. } => (vec![*sig], "a signature with `@use` parameters"),
                _ => continue,
            };
            if let Some(span) = tys.into_iter().find_map(|t| first_wildcard(ast, t)) {
                return Err(diag!(
                    Code::TypeAnnotationRequired, span, 0,
                    "{what} writes its types out, so it cannot leave one to elaboration with `_`";
                    note: "`_` stands in a definition's signature or an annotation inside a body, which the body solves"
                ));
            }
        }
        Ok(())
    }

    /// Whether a signature ends in a universe after its arrows.
    fn returns_type(&self, sig: Aol<Ty>) -> bool {
        let mut cur = sig;
        while let Ty::Arrow { to, .. } = self.ast.ty(cur) {
            cur = *to;
        }
        if let Ty::App(head, _) = self.ast.ty(cur) {
            cur = *head;
        }
        matches!(self.ast.ty(cur), Ty::Con { module: None, name } if name.as_str() == "@Type")
    }

    /// A definition the checker cannot take yet (#406): a type-level function
    /// whose lambda leaves parameters unbound, or one whose signature binds
    /// levels. A capitalized value is only a warning: capitalization is a
    /// convention.
    fn reject_dependent_defs(&mut self, program: &Program) -> Result<()> {
        let items = self.ast.slice(program.items);
        let spans = self.ast.slice(program.spans);
        for (item, at) in items.iter().zip(spans) {
            let Item::Def { name, sig, .. } = item else { continue };
            let span = at.name.unwrap_or(at.full);
            if sig.is_some_and(|s| self.returns_type(s)) {
                return Err(diag!(
                    Code::Unsupported, span, 0,
                    "a type-level function binds every parameter with its lambda";
                    help: "write `\\a b => ...`, one name per arrow of the signature"
                ));
            }
            if name.as_str().starts_with(|c: char| c.is_ascii_uppercase()) {
                self.warnings.push(diag!(
                    Code::CapitalizedValue, span, 0,
                    "a value's name is lowercase by convention; a capitalized name reads as a type";
                    help: "rename `{name}` to `{}`", lower_first(name.as_str())
                ));
            }
            if let Some(levels) = sig.and_then(|s| self.ast.level_params.get(s)) {
                let span = self.ast.slice(*levels).first().map_or(span, |l| l.span);
                return Err(dependent_only(Some(span), "a level parameter"));
            }
        }
        Ok(())
    }

    /// Record that `name` still holds `!` entry splices, whose operands are
    /// checked once the globals are in scope (`check_program`). Until the expand loop splices them in, the type is
    /// incomplete: reflecting on it faults, and a lenient round holds back the
    /// globals that fail against it (see [`Checker::awaits_splices`]).
    fn pend_entry_splices(&mut self, name: StrId, splices: &[EntrySplice]) {
        if splices.is_empty() {
            return;
        }
        self.pending_types.insert(name);
        self.entry_splices.extend(splices.iter().map(|s| s.expr));
    }

    /// Reject an alias that reaches itself through aliases alone (`T = T`, or
    /// `A = B` with `B = A`). A struct or union in the chain is nominal and stops
    /// the expansion, but an alias is expanded in place and would never finish.
    pub(super) fn check_alias_cycles(&self) -> Result<()> {
        fn visit<'a>(
            checker: &Checker<'a>,
            name: StrId,
            path: &mut Vec<StrId>,
            done: &mut HashSet<StrId>,
        ) -> Result<()> {
            if done.contains(&name) {
                return Ok(());
            }
            let Some((_, body)) = checker.aliases.get(&name) else {
                return Ok(());
            };
            if let Some(at) = path.iter().position(|n| *n == name) {
                let mut chain: Vec<&str> = path[at..].iter().map(|n| n.as_str()).collect();
                chain.push(name.as_str());
                let span = checker.ast.ty_span(*body).unwrap_or_else(|| Span::at(0));
                return Err(diag!(
                    Code::TypeCycle, span, 0,
                    "type `{name}` unfolds to itself";
                    note: "{}", chain.join(" -> ");
                    help: "a type-level function only unfolds; make one of them a `@struct` or `@union`"
                ));
            }
            path.push(name);
            let mut cons = Vec::new();
            collect_tycons(checker.ast, *body, &mut cons);
            for c in cons {
                visit(checker, c, path, done)?;
            }
            path.pop();
            done.insert(name);
            Ok(())
        }
        let mut names: Vec<StrId> = self.aliases.keys().copied().collect();
        names.sort_unstable_by_key(|n| n.as_str());
        let mut done = HashSet::new();
        for name in names {
            visit(self, name, &mut Vec::new(), &mut done)?;
        }
        Ok(())
    }

    /// If `name` is a parameterless alias whose body is a bare type constructor,
    /// the constructor it aliases (`Quaternion` -> `Vector4`), else None. Used to
    /// see through aliases when deciding whether a C-repr field is representable.
    pub(super) fn nullary_alias_target(&self, name: StrId) -> Option<StrId> {
        let (params, body) = self.aliases.get(&name)?;
        if !params.is_empty() {
            return None;
        }
        match self.tnode(*body) {
            Ty::Con { name, .. } => Some(*name),
            _ => None,
        }
    }

    /// Register every declared effect's operations. An operation `op : Arg -> Res`
    /// becomes a value: bound unqualified when a single effect declares that name,
    /// or an overload when several do (resolved by result type at the use site);
    /// always reachable qualified as `Effect.op`. Its `Arg -> Res` scheme is also
    /// kept per effect for handler-clause typing.
    /// Build the record row of every struct and hand them to the unifier, so a
    /// nominal struct can unify with a structural record row (the hybrid bridge).
    /// Each row is a scheme: its parameters become fresh vars (recorded in
    /// declaration order), so a generic struct instance `Box Int` bridges by
    /// substituting its type arguments for those parameter vars per use.
    pub(super) fn register_struct_rows(&mut self) {
        let decls: Vec<(StrId, Vec<StrId>, Vec<(StrId, Aol<Ty>)>)> = self
            .structs
            .iter()
            .map(|(name, info)| (*name, info.params.clone(), info.fields.clone()))
            .collect();
        let mut rows = HashMap::new();
        for (name, params, fields) in decls {
            let mut tvars = HashMap::new();
            // A fresh var per parameter, in order, so App arguments line up with
            // them at bridge time (a phantom param still gets a slot, unused).
            let param_ids: Vec<VarId> = params
                .iter()
                .map(|p| {
                    let v = self.unifier.fresh();
                    let id = match self.unifier.types.node(v) {
                        TypeNode::Var(id) => id,
                        _ => unreachable!("fresh() returns a variable"),
                    };
                    tvars.insert(*p, v);
                    id
                })
                .collect();
            let mut row = self.unifier.types.row_empty();
            for (fname, fty) in fields.iter().rev() {
                let f = self.ty_of_ast(*fty, &mut tvars);
                row = self.unifier.types.row_field(*fname, f, row);
            }
            rows.insert(name, (param_ids, row));
        }
        self.unifier.set_struct_rows(rows);
    }

    // Note [Lazy constructor slots]
    //
    // Ares is call-by-value, but a recursive data type built strictly could
    // never describe an infinite or very long structure without building all of
    // it first. So a constructor slot is lazy exactly when its type can lead
    // back to the type that owns it: `Cons`'s tail, a tree's children. Every
    // other slot is strict.
    //
    // Laziness belongs to the slot, not to the expression that fills it, so it
    // holds however the value is built. The checker decides it per declaration
    // (`compute_lazy_slots`, into `Resolved::lazy_slots`), and desugaring wraps
    // each value placed in a lazy slot in a lambda passed to `@delay`. The
    // engines force the suspension when the value is scrutinised and overwrite
    // the cell with the result, so the work happens once and only if it is
    // needed.
    //
    // A C-repr struct is excluded: its runtime value is a flat C struct, and a
    // suspension cannot cross the `@extern` boundary.

    /// Decide which slots hold their value lazily.
    /// See Note [Lazy constructor slots].
    pub(super) fn compute_lazy_slots(&mut self) {
        let mut mentions: HashMap<StrId, Vec<StrId>> = HashMap::new();
        let mut slot_types: Vec<(StrId, Option<StrId>, Vec<Aol<Ty>>)> = Vec::new();
        for (name, info) in &self.structs {
            if info.crepr {
                continue;
            }
            slot_types.push((*name, None, info.fields.iter().map(|(_, t)| *t).collect()));
        }
        for (name, info) in &self.unions {
            for v in &info.variants {
                slot_types.push((*name, Some(v.tag), v.payload.iter().map(|(_, t)| *t).collect()));
            }
        }
        // An alias is transparent here: a slot typed through one still reaches
        // whatever the alias expands to.
        for (name, (_, ty)) in &self.aliases {
            let mut cons = Vec::new();
            collect_tycons(self.ast, *ty, &mut cons);
            mentions.entry(*name).or_default().extend(cons);
        }
        for (owner, _, tys) in &slot_types {
            let entry = mentions.entry(*owner).or_default();
            for ty in tys {
                let mut cons = Vec::new();
                collect_tycons(self.ast, *ty, &mut cons);
                for c in cons {
                    if !entry.contains(&c) {
                        entry.push(c);
                    }
                }
            }
        }
        // Transitive closure of "mentions", so a slot typed `B` counts as
        // recursive when `B` leads back to the owner through any chain.
        let mut reach: HashMap<StrId, HashSet<StrId>> =
            mentions.iter().map(|(k, v)| (*k, v.iter().copied().collect())).collect();
        loop {
            let mut changed = false;
            let keys: Vec<StrId> = reach.keys().copied().collect();
            for k in keys {
                let grown: HashSet<StrId> = reach[&k]
                    .iter()
                    .filter_map(|t| reach.get(t))
                    .flatten()
                    .copied()
                    .collect();
                let entry = reach.get_mut(&k).expect("key came from this map");
                let before = entry.len();
                entry.extend(grown);
                changed |= entry.len() != before;
            }
            if !changed {
                break;
            }
        }
        let leads_back = |c: StrId, owner: StrId| {
            c == owner || reach.get(&c).is_some_and(|r| r.contains(&owner))
        };
        for (owner, tag, tys) in &slot_types {
            let flags: Vec<bool> = tys
                .iter()
                .map(|ty| {
                    let mut cons = Vec::new();
                    collect_tycons(self.ast, *ty, &mut cons);
                    cons.into_iter().any(|c| leads_back(c, *owner))
                })
                .collect();
            if flags.iter().any(|f| *f) {
                let home = self.type_home.get(owner).copied().unwrap_or(self.module_name);
                self.lazy_slots.insert((home, *owner, *tag), flags);
            }
        }
    }
}

// ## Effects

impl<'a> Checker<'a> {
    pub(super) fn register_effects(&mut self, program: &Program) -> Result<()> {
        let items = self.ast.slice(program.items);
        for item in items.iter() {
            if let Item::Effect { name, sig, params, .. } = item {
                let n = self.ast.slice(*params).len();
                self.effect_arity.insert(*name, n);
                let kinds = self.decl_kinds(*sig)?;
                self.effect_kinds.insert(*name, kinds);
            }
        }
        let mut per_op: HashMap<StrId, Vec<Type>> = HashMap::new();
        for item in items.iter() {
            let Item::Effect { name, params, ops, .. } = item else {
                continue;
            };
            let effect = *name;
            let params: Vec<StrId> = self.ast.slice(*params).to_vec();
            let mut op_schemes = HashMap::new();
            for op in self.ast.slice(*ops).iter() {
                let op_name = op.name;
                self.check_own_ctx(effect, op_name, &params, self.ast.ctx_params.get(op.ty).copied())?;
                self.check_ctx_fields(op_name, op.ty);
                let scheme = self.op_scheme(effect, &params, op.ty)?;
                op_schemes.insert(op_name, scheme);
                per_op.entry(op_name).or_default().push(scheme);
                self.qualified
                    .entry(effect)
                    .or_default()
                    .insert(op_name, vec![scheme]);
            }
            self.effect_ops.insert(effect, op_schemes);
            self.own_effects.push(effect);
        }
        for (op_name, mut schemes) in per_op {
            // A bare operation of this module's own effect shadows an imported
            // global of its name, as this module's own definition would (CORE's
            // `get` does not capture a `get` operation).
            self.global_ctx.remove(&op_name);
            self.ctx_sigs.remove(&op_name);
            self.value_module.remove(&op_name);
            self.ambiguous_imports.remove(&op_name);
            if schemes.len() == 1 {
                self.bind(op_name, schemes.pop().expect("one scheme"));
            } else {
                self.overloads
                    .entry(op_name)
                    .or_default()
                    .extend(schemes.into_iter().map(Cand::local));
            }
        }
        Ok(())
    }

    /// An operation's scheme: its written type, with the outermost arrow's
    /// latent effect `<effect params | mu>` (mu a fresh row variable), so
    /// performing it forces `effect` into the ambient, fits any ambient already
    /// containing more effects, and ties `params` to the handler's instance. The
    /// type may also use variables of its own, chosen anew at each use, like
    /// `throw : @Str -> a`. One handler serves every use, so its clause sees
    /// each of them as an opaque type (see `instantiate_for_handler`): it can
    /// pass such a value along, but cannot make one up or inspect it, which
    /// keeps it from answering one use's type to another (#290).
    pub(super) fn op_scheme(
        &mut self,
        effect: StrId,
        params: &[StrId],
        sig: Aol<Ty>,
    ) -> Result<Type> {
        self.unifier.enter_level();
        let mut tvars = self.sig_tvars(sig);
        let param_tys: Vec<Type> = params
            .iter()
            .map(|p| {
                let v = self.unifier.fresh();
                tvars.insert(*p, v);
                v
            })
            .collect();
        let args = if param_tys.is_empty() {
            self.unifier.types.row_empty()
        } else {
            self.unifier.types.tuple(param_tys)
        };
        let saved = self.effect_self.replace((effect, args));
        let ty = self.ty_reporting(sig, &mut tvars, Some(sig));
        self.effect_self = saved;
        let ty = match self.unifier.types.node(ty) {
            TypeNode::Arrow(from, to, _) => {
                let mu = self.unifier.fresh();
                let eff = self.unifier.types.row_extend_args(effect, args, mu);
                self.unifier.types.arrow_eff(from, to, eff)
            }
            _ => ty,
        };
        self.unifier.leave_level();
        self.unifier.generalize(ty);
        Ok(self.unifier.zonk(ty))
    }

    /// The effect a handler clause discharges: its explicit qualifier, or the
    /// unique effect declaring a bare operation (ambiguous / unknown -> `None`,
    /// left to dynamic dispatch).
    pub(super) fn op_owner(&self, effect: Option<StrId>, op: StrId) -> Option<StrId> {
        if let Some(e) = effect {
            return Some(e);
        }
        for table in [&self.effect_ops, &self.imported_effect_ops] {
            let mut found = None;
            for (eff, ops) in table {
                if ops.contains_key(&op) {
                    if found.is_some() {
                        return None;
                    }
                    found = Some(*eff);
                }
            }
            if found.is_some() {
                return found;
            }
        }
        None
    }

    /// The `Arg -> Res` scheme of an operation named in a handler clause, resolved
    /// by its explicit effect or, for a bare name, by the unique effect declaring
    /// it.
    pub(super) fn resolve_op_ty(&self, effect: Option<StrId>, op: StrId) -> Option<Type> {
        let owner = self.op_owner(effect, op)?;
        [&self.effect_ops, &self.imported_effect_ops]
            .into_iter()
            .find_map(|table| table.get(&owner).and_then(|ops| ops.get(&op)).copied())
    }
}

// ## Lookups

impl<'a> Checker<'a> {
    /// The result type and payload of `union`'s constructor `tag`, its
    /// parameters fresh. A constructor that states its result builds that, its
    /// own variables fresh too. In a pattern (`opaque`) the result's indices
    /// are left free instead, and the constructor's own variables come back
    /// with the rest: matching learns nothing about them until dependent
    /// matching (#543), so the caller keeps them apart from every other type.
    pub(super) fn variant_sig(&mut self, union: StrId, tag: StrId, opaque: bool) -> Option<(Type, VariantPayload, Vec<(StrId, Type)>)> {
        let info = self.unions.get(&union)?.clone();
        let pos = info.variants.iter().position(|v| v.tag == tag)?;
        let (mut args, mut subst) = self.instantiate_params(&info.params[..info.uniform], &info.kinds[..info.uniform]);
        let variant = &info.variants[pos];
        let mut own = Vec::new();
        for &(name, kind) in &variant.own {
            let v = self.fresh_of(kind);
            subst.insert(name, v);
            own.push((name, v));
        }
        let result = match variant.result {
            Some(result) if !opaque => self.ty_of_ast(result, &mut subst),
            Some(_) => {
                args.extend(info.kinds[info.uniform..].iter().map(|k| self.fresh_of(*k)));
                applied(&self.unifier.types, union, &args)
            }
            None => applied(&self.unifier.types, union, &args),
        };
        let payload = variant
            .payload
            .clone()
            .into_iter()
            .map(|(name, ast_ty)| (name, self.ty_of_ast(ast_ty, &mut subst)))
            .collect();
        Some((result, payload, own))
    }

    /// The union an unqualified tag (`.Missing`) names: this module's own first,
    /// then an imported module's, then the prelude's, so a library type never
    /// takes a tag from the code using it. Ties go to the smaller name, so the
    /// choice does not depend on hash order.
    pub(super) fn find_union_by_tag(&self, tag: StrId) -> Option<StrId> {
        let prelude = StrId::intern("CORE");
        let rank = |name: &StrId| match self.type_home.get(name).copied() {
            Some(m) if m == self.module_name => 0,
            Some(m) if m == prelude => 2,
            _ => 1,
        };
        self.unions
            .iter()
            .filter(|(_, info)| info.variants.iter().any(|v| v.tag == tag))
            .map(|(name, _)| *name)
            .min_by_key(|name| (rank(name), name.as_str()))
    }

    /// The union an unqualified tag names where a value of type `expected` is
    /// wanted: the expected union itself when it has the tag, else as
    /// [`Self::find_union_by_tag`].
    pub(super) fn find_union_for(&self, tag: StrId, expected: Type) -> Option<StrId> {
        let head = self.ctx_head(self.unifier.zonk(expected));
        head.filter(|h| self.unions.get(h).is_some_and(|u| u.variants.iter().any(|v| v.tag == tag)))
            .or_else(|| self.find_union_by_tag(tag))
    }

    /// The type of field `name` in a record value: through the row for a structural
    /// record (open tail grows to include it), or the declared field for a struct.
    pub(super) fn field_type_of(&mut self, base: Type, name: StrId) -> Result<Type> {
        if let TypeNode::Record(_) = self.unifier.head(base) {
            return self
                .unifier
                .record_field(base, name, "in a record update");
        }
        for (fname, fty) in self.record_fields_of(base)? {
            if fname == name {
                return Ok(fty);
            }
        }
        Err(diag!(
            Code::TypeMismatch, Span::at(0), 0,
            "record update sets `{name}`, which the base record does not have"
        ))
    }

    /// The record row of a value (the inner row of a structural record, possibly
    /// open; or a struct's closed row), for stacking fields onto it.
    pub(super) fn record_row_of(&mut self, base: Type) -> Result<Type> {
        if let TypeNode::Record(row) = self.unifier.head(base) {
            return Ok(row);
        }
        let fields = self.record_fields_of(base)?;
        Ok(fields
            .into_iter()
            .rev()
            .fold(self.unifier.types.row_empty(), |rest, (n, t)| self.unifier.types.row_field(n, t, rest)))
    }

    /// Whether `ty` is a record-shaped target: a structural record row, or a
    /// The nominal struct name `ty` resolves to (possibly applied), if any.
    pub(super) fn struct_name_of(&self, ty: Type) -> Option<StrId> {
        let (head, _) = self.spine(ty);
        if let TypeNode::Con(n) = self.unifier.types.node(head) {
            if let Some((k, _)) = self.structs.get_key_value(&n) {
                return Some(*k);
            }
        }
        None
    }

    /// The union `ty`'s head names, if it is a (possibly applied) declared union that
    /// has a variant `tag`. Lets a BARE `.Tag` resolve type-directedly against the
    /// expected type, so two unions sharing a constructor name (e.g. a user list and
    /// the builtin `List`, both with `Cons`/`Nil`) do not collide.
    pub(super) fn union_head_with_tag(&self, ty: Type, tag: StrId) -> Option<StrId> {
        let (head, _) = self.spine(ty);
        let TypeNode::Con(n) = self.unifier.types.node(head) else {
            return None;
        };
        let (k, info) = self.unions.get_key_value(&n)?;
        info.variants.iter().any(|v| v.tag == tag).then_some(*k)
    }

    /// Whether `ty` is a declared union with no variants, so no value has it.
    pub(super) fn is_variantless_union(&self, ty: Type) -> bool {
        let (head, _) = self.spine(ty);
        let TypeNode::Con(n) = self.unifier.types.node(head) else {
            return false;
        };
        self.unions.get(&n).is_some_and(|u| u.variants.is_empty())
    }

    /// The `(label, type)` fields of a record value: a structural [`TypeNode::Record`]
    /// (its closed row) or a nominal struct (its declared fields, instantiated).
    pub(super) fn record_fields_of(&mut self, ty: Type) -> Result<Vec<(StrId, Type)>> {
        if let TypeNode::Record(row) = self.unifier.head(ty) {
            let mut out = Vec::new();
            let mut cur = row;
            loop {
                match self.unifier.head(cur) {
                    TypeNode::RowField(l, fty, rest) => {
                        out.push((l, fty));
                        cur = rest;
                    }
                    TypeNode::RowEmpty => return Ok(out),
                    _ => {
                        return Err(diag!(
                            Code::TypeMismatch, Span::at(0), 0,
                            "cannot use a record with an unknown (open) row here"
                        ))
                    }
                }
            }
        }
        let (head, args) = self.spine(ty);
        if let TypeNode::Con(name) = self.unifier.types.node(head) {
            if let Some(info) = self.structs.get(&name).cloned() {
                let mut subst = subst_from_args(&info.params, &args, &mut self.unifier);
                return Ok(info
                    .fields
                    .iter()
                    .map(|(n, fty)| (*n, self.ty_of_ast(*fty, &mut subst)))
                    .collect());
            }
        }
        Err(diag!(
            Code::TypeMismatch, Span::at(0), 0,
            "expected a record or struct value here"
        ))
    }

    pub(super) fn resolve_struct_by_fields(&self, fields: &[FieldInit]) -> Option<(StrId, StructInfo)> {
        let mut names = Vec::with_capacity(fields.len());
        for f in fields {
            match f {
                FieldInit::Named { name, .. } => names.push(*name),
                FieldInit::Positional(_) => return None,
            }
        }
        self.structs.iter().find_map(|(sname, info)| {
            let same = info.fields.len() == names.len()
                && names
                    .iter()
                    .all(|n| info.fields.iter().any(|(f, _)| f == n));
            same.then(|| (*sname, info.clone()))
        })
    }

    pub(super) fn struct_field_ty(
        &mut self,
        info: &StructInfo,
        subst: &mut HashMap<StrId, Type>,
        name: Option<StrId>,
        index: usize,
    ) -> Option<Type> {
        let ast_ty = match name {
            Some(name) => info
                .fields
                .iter()
                .find(|(n, _)| *n == name)
                .map(|(_, t)| *t),
            None => info.fields.get(index).map(|(_, t)| *t),
        }?;
        Some(self.ty_of_ast(ast_ty, subst))
    }

    /// A fresh variable for each parameter, a size variable for a `@Nat` one.
    pub(super) fn instantiate_params(&mut self, params: &[StrId], kinds: &[ParamKind]) -> (Vec<Type>, HashMap<StrId, Type>) {
        let mut subst = HashMap::new();
        let mut args = Vec::with_capacity(params.len());
        for (p, kind) in params.iter().zip(kinds) {
            let v = self.fresh_of(*kind);
            subst.insert(*p, v);
            args.push(v);
        }
        (args, subst)
    }

    /// A fresh variable ranging over `kind`.
    pub(super) fn fresh_of(&mut self, kind: ParamKind) -> Type {
        match kind {
            ParamKind::Nat => self.unifier.fresh_nat(),
            ParamKind::Type | ParamKind::Row => self.unifier.fresh(),
        }
    }

    pub(super) fn spine(&self, ty: Type) -> (Type, Vec<Type>) {
        let mut args = Vec::new();
        let mut cur = self.unifier.resolve(ty);
        while let TypeNode::App(head, arg) = self.unifier.types.node(cur) {
            args.push(self.unifier.resolve(arg));
            cur = self.unifier.resolve(head);
        }
        args.reverse();
        (cur, args)
    }
}

pub(super) fn applied(types: &Types, name: StrId, args: &[Type]) -> Type {
    let mut acc = types.con(name);
    for a in args {
        acc = types.app(acc, *a);
    }
    acc
}

pub(super) fn subst_from_args(
    params: &[StrId],
    args: &[Type],
    eng: &mut Unifier,
) -> HashMap<StrId, Type> {
    let mut subst = HashMap::new();
    for (i, p) in params.iter().enumerate() {
        let a = args.get(i).cloned().unwrap_or_else(|| eng.fresh());
        subst.insert(*p, a);
    }
    subst
}

/// The type variables of `ty` in order of first use, each with where that use
/// is written (for a row tail, the record it ends).
pub(super) fn collect_tyvar_uses(ast: &Ast, ty: Aol<Ty>, out: &mut Vec<(StrId, Option<Span>)>) {
    let mut push = |name: StrId| {
        if !out.iter().any(|(n, _)| *n == name) {
            out.push((name, ast.ty_span(ty)));
        }
    };
    match ast.ty(ty) {
        Ty::Var(name) => push(*name),
        Ty::Record { fields, tail } => {
            let tail = *tail;
            ast.slice(*fields).iter().for_each(|f| collect_tyvar_uses(ast, f.ty, out));
            if let Some(t) = tail {
                if !out.iter().any(|(n, _)| *n == t) {
                    out.push((t, ast.ty_span(ty)));
                }
            }
        }
        Ty::App(a, b) | Ty::Arrow { from: a, to: b, .. } | Ty::Sized { size: a, elem: b, .. } | Ty::SizeAdd(a, b) | Ty::SizeMul(a, b) => {
            collect_tyvar_uses(ast, *a, out);
            collect_tyvar_uses(ast, *b, out);
        }
        Ty::Tuple(items) => ast.slice(*items).iter().for_each(|t| collect_tyvar_uses(ast, *t, out)),
        Ty::Con { .. } | Ty::Nat(_) | Ty::Unit | Ty::MetaE(..) | Ty::Term(_) => {}
    }
}

pub(super) fn collect_tyvars(ast: &Ast, ty: Aol<Ty>, out: &mut Vec<StrId>) {
    match ast.ty(ty) {
        Ty::Var(name) => {
            let name = *name;
            if !out.contains(&name) {
                out.push(name);
            }
        }
        Ty::App(a, b) => {
            collect_tyvars(ast, *a, out);
            collect_tyvars(ast, *b, out);
        }
        Ty::Arrow { from, to, .. } => {
            collect_tyvars(ast, *from, out);
            collect_tyvars(ast, *to, out);
        }
        Ty::Tuple(items) => ast.slice(*items).iter().for_each(|t| collect_tyvars(ast, *t, out)),
        Ty::Record { fields, tail } => {
            ast.slice(*fields).iter().for_each(|f| collect_tyvars(ast, f.ty, out));
            if let Some(t) = tail {
                let name = *t;
                if !out.contains(&name) {
                    out.push(name);
                }
            }
        }
        Ty::Sized { size, elem, .. } => {
            collect_tyvars(ast, *size, out);
            collect_tyvars(ast, *elem, out);
        }
        Ty::SizeAdd(a, b) | Ty::SizeMul(a, b) => {
            collect_tyvars(ast, *a, out);
            collect_tyvars(ast, *b, out);
        }
        // A `!X` type splice contributes no type variables: its type is unknown
        // until the driver expands it, after which this node no longer exists.
        Ty::Con { .. } | Ty::Nat(_) | Ty::Unit | Ty::MetaE(..) | Ty::Term(_) => {}
    }
}

/// Collect the type variables `ty` uses as sizes: in the size of a
/// `@Tensor n T`, or under `+` and `*`. They are the parameters of kind `@Nat`.
pub(super) fn collect_size_vars(ast: &Ast, ty: Aol<Ty>, in_size: bool, out: &mut Vec<StrId>) {
    match ast.ty(ty) {
        Ty::Var(name) if in_size && !out.contains(name) => out.push(*name),
        Ty::App(a, b) | Ty::Arrow { from: a, to: b, .. } => {
            collect_size_vars(ast, *a, in_size, out);
            collect_size_vars(ast, *b, in_size, out);
        }
        Ty::Tuple(items) => ast.slice(*items).iter().for_each(|t| collect_size_vars(ast, *t, in_size, out)),
        Ty::Record { fields, .. } => ast.slice(*fields).iter().for_each(|f| collect_size_vars(ast, f.ty, in_size, out)),
        Ty::Sized { size, elem } => {
            collect_size_vars(ast, *size, true, out);
            collect_size_vars(ast, *elem, in_size, out);
        }
        Ty::SizeAdd(a, b) | Ty::SizeMul(a, b) => {
            collect_size_vars(ast, *a, true, out);
            collect_size_vars(ast, *b, true, out);
        }
        _ => {}
    }
}

/// Collect the type-constructor names `ty` mentions in a STRICT position: one
/// that must be built to build a value of `ty`. Used for the type dependency
/// graph behind the lazy-slot decision.
///
/// An arrow is not descended into. A function is already a suspension, so a
/// recursive occurrence behind one (`Susp: { @Int, {} -> Task }`) costs nothing
/// at construction and must stay a plain function: thunking it again would leave
/// callers applying a thunk. A type variable contributes nothing either, since a
/// parameter cannot make its owner recursive on its own.
pub(super) fn collect_tycons(ast: &Ast, ty: Aol<Ty>, out: &mut Vec<StrId>) {
    match ast.ty(ty) {
        Ty::Con { name, .. } => {
            let name = *name;
            if !out.contains(&name) {
                out.push(name);
            }
        }
        Ty::App(a, b) | Ty::SizeAdd(a, b) | Ty::SizeMul(a, b) => {
            collect_tycons(ast, *a, out);
            collect_tycons(ast, *b, out);
        }
        Ty::Sized { size, elem, .. } => {
            collect_tycons(ast, *size, out);
            collect_tycons(ast, *elem, out);
        }
        Ty::Tuple(items) => ast.slice(*items).iter().for_each(|t| collect_tycons(ast, *t, out)),
        Ty::Record { fields, .. } => {
            ast.slice(*fields).iter().for_each(|f| collect_tycons(ast, f.ty, out))
        }
        Ty::Arrow { .. } | Ty::Var(_) | Ty::Nat(_) | Ty::Unit | Ty::MetaE(..) | Ty::Term(_) => {}
    }
}

/// Normalize a variant payload into `(optional-name, type-handle)` pairs.
pub(crate) fn payload_fields(ast: &Ast, p: &Payload) -> Vec<(Option<StrId>, Aol<Ty>)> {
    match p {
        Payload::None => vec![],
        Payload::Bare(ty) => vec![(None, *ty)],
        Payload::Fields(fs) => ast
            .slice(*fs)
            .iter()
            .map(|f| (f.name, f.ty))
            .collect(),
    }
}

/// A type that declares a `{kind}` (`"field"`/`"variant"`) twice, by hand or
/// through a `!` entry splice.
pub(super) fn dup_member(ty: impl Display, member: impl Display, kind: &str) -> Diagnostic {
    diag!(
        Code::DuplicateSymbol, Span::at(0), 0,
        "type `{ty}` declares the {kind} `{member}` twice"
    )
}

/// A type declaration uses a type variable it does not declare. Parameters are
/// mandatory, so this reports the fix: bind `v` in the signature.
pub(super) fn undeclared_param(kind: &str, name: StrId, v: &StrId, declared: &[StrId]) -> Diagnostic {
    let how = format!("`{name}` uses the type variable `{v}`");
    let msg = if declared.is_empty() {
        format!("{how}, but `{name}` declares no type parameters")
    } else {
        format!(
            "{how}, which is not one of `{name}`'s declared parameters `{}`",
            declared.iter().map(|d| d.as_str()).collect::<Vec<_>>().join(" ")
        )
    };
    let help = if kind == "alias" {
        let params: String = declared.iter().map(|d| format!("{d} ")).collect();
        format!("bind it with the lambda, `\\{params}{v} => ...`, and add an `@Type ->` to the signature")
    } else {
        format!("bind it in the signature, `({v}: @Type) -> ... -> @Type = @{kind} ...`")
    };
    Diagnostic::error(Code::TypeUnbound, Span::at(0), 0, msg)
        .with_note("type parameters are mandatory")
        .with_help(help)
}

/// A constructor of an indexed union with no stated result.
fn unstated_result(union: StrId, tag: StrId, params: &[StrId]) -> Diagnostic {
    let params: String = params.iter().map(|p| format!(" {p}")).collect();
    diag!(
        Code::TypeMismatch, Span::at(0), 0,
        "`{union}` has indices, so its constructor `{tag}` states its result";
        help: "write the result after the payload, `{tag}: {{...}} -> {union}{params} ...`"
    )
}

/// `name` with its first letter lowercased.
fn lower_first(name: &str) -> String {
    let mut cs = name.chars();
    cs.next().map_or_else(String::new, |c| c.to_ascii_lowercase().to_string() + cs.as_str())
}
