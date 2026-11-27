//! Context instance resolution.
//!
//! A definition whose signature's `@ctx` has instance fields, those whose type
//! is a `@Class`, takes them as one argument, implicitly. At each use the checker plans the requirement, then
//! resolves it at the enclosing definition's boundary, once inference has
//! pinned the requirement's type variables. Resolution searches by type: first
//! the context binders in scope, then a flat index of the instances (globals
//! whose type's head is the requirement's `@Class`). An instance may itself
//! take a context, so resolution recurses; the Paterson conditions make it
//! terminate, with [`CTX_DEPTH`] as a backstop. One candidate is chosen,
//! without backtracking; none or several is an error naming the candidates. A
//! requirement whose head is not yet a constructor waits for inference to pin
//! it, and is never guessed.
//!
//! The blessed interfaces (`@IStrLit`, `@ISeqView`, ...) resolve the same way:
//! a literal, range or sequence pattern on a user type finds its instance by
//! type, and desugaring projects the interface's one field.
//!
//! See `documentation/language/interfaces.md` for the language-level rules.
//!
//! Entry points: [`Checker::plan_ctx`], [`Checker::resolve_pending_ctx`].

use super::*;

// ## Context signatures

impl<'a> Checker<'a> {
    /// Elaborate a signature into the type callers see and, when it has
    /// instance fields, the context parameter that carries them. Both are generalized together (as
    /// one tuple) so a variable they share becomes the same `Generic` in each.
    pub(super) fn scheme_and_ctx(&mut self, sig: Aol<Ty>, has_ctx: bool) -> (Type, Option<Type>) {
        self.unifier.enter_level();
        let mut tvars = self.sig_tvars(sig);
        let full = self.ty_of_ast(sig, &mut tvars);
        self.unifier.leave_level();
        let (ctx, exposed) = if has_ctx {
            match self.unifier.types.node(full) {
                TypeNode::Arrow(from, to, _) => (Some(from), to),
                // A context signature is built as an arrow by the parser; an alias
                // could still hide one, in which case there is nothing to strip.
                _ => (None, full),
            }
        } else {
            (None, full)
        };
        let items: Vec<Type> = std::iter::once(exposed).chain(ctx).collect();
        let bundle = self.unifier.types.tuple(items);
        self.unifier.generalize(bundle);
        let zonked = self.unifier.zonk(bundle);
        let TypeNode::Tuple(parts) = self.unifier.types.node(zonked) else {
            unreachable!("packed bundle stays a tuple");
        };
        let parts = self.unifier.types.items(parts).to_vec();
        (parts[0], parts.get(1).copied())
    }

    /// Elaborate a context-bearing signature at a USE site: fresh variables for
    /// its type variables, split into the context requirement and the type the
    /// caller applies. One map for the whole signature keeps the two aligned, so
    /// `Ito_string t -> t -> @Str` ties the requirement to the argument.
    pub(super) fn ctx_use_type(&mut self, sig: Aol<Ty>) -> (Type, Type) {
        let mut tvars = self.sig_tvars(sig);
        let full = self.ty_of_ast(sig, &mut tvars);
        match self.unifier.types.node(full) {
            TypeNode::Arrow(from, to, _) => (from, to),
            _ => (full, full),
        }
    }

    /// Pack an instance's exposed type with its own context requirement, so one
    /// instantiation keeps their variables aligned.
    pub(super) fn instance_bundle(&mut self, exposed: Type, ctx: Option<Type>) -> Type {
        let items: Vec<Type> = std::iter::once(exposed).chain(ctx).collect();
        self.unifier.types.tuple(items)
    }

    /// An instance field's type must be a `@Class` applied to its arguments.
    /// An ordinary record is never searched, and a bare variable or a base
    /// type would turn the search into "any value of this type in scope", which
    /// is never what is meant; the error belongs at the declaration rather than
    /// at every call site.
    pub(super) fn check_ctx_head(&mut self, name: StrId, ctx: Aol<Ty>, sig: Aol<Ty>) -> Result<()> {
        let fields: Vec<UseField> = match self.ast.use_params.get(sig) {
            Some(fs) => self.ast.slice(*fs).to_vec(),
            None => Vec::new(),
        };
        let mut tvars = self.sig_tvars(sig);
        let ty = self.ty_of_ast(ctx, &mut tvars);
        let zonked = self.unifier.zonk(ty);
        // A bundle of several contexts travels as a tuple; each component carries
        // the same requirement.
        let parts = match self.unifier.types.node(zonked) {
            TypeNode::Tuple(items) if fields.len() > 1 => self.unifier.types.items(items).to_vec(),
            _ => vec![zonked],
        };
        for (i, part) in parts.into_iter().enumerate() {
            // An unspliced `!` stands as a fresh variable until expansion.
            if fields.get(i).is_some_and(|f| matches!(self.ast.ty(f.ty), Ty::MetaE(_))) {
                continue;
            }
            let (field, span, written) = match fields.get(i) {
                Some(f) => (format!("`{}`", f.name), f.span, self.ast.ty_source(f.ty)),
                None => ("a field".to_string(), self.ast.ty_span(ctx).unwrap_or_else(|| Span::at(0)), None),
            };
            // A proposition field is proved at each use, not searched for.
            if self.is_prop(part) {
                continue;
            }
            match self.ctx_head(part) {
                Some(h) if self.is_class(h) => {}
                Some(h) if self.is_nominal(h) => {
                    return Err(diag!(
                        Code::TypeMismatch, span, 0,
                        "`@ctx` field {field} of `{name}` is a `{}`, which instance search never looks for",
                        written.unwrap_or_else(|| self.show(part));
                        note: "a field is searched for when its type is a `@Class`; `{h}` is an ordinary record";
                        help: "declare `{h}` at `@Class`, as in `$ {h} : (t: @Type) -> @Class = @struct ...`"
                    ));
                }
                _ => return Err(dependent_only(Some(span), "a `@ctx` field that is a value")),
            }
        }
        Ok(())
    }

    /// An instance's own instance fields are each smaller than the type it
    /// provides, the Paterson conditions: fewer constructors and variables,
    /// and no variable more often. Search on them then always terminates, so
    /// [`CTX_DEPTH`] is only a backstop.
    pub(super) fn check_instance_terminates(&mut self, name: StrId, sig: Aol<Ty>, exposed: Type, ctx: Option<Type>) {
        let Some(ctx) = ctx else { return };
        let fields: Vec<UseField> = match self.ast.use_params.get(sig) {
            Some(fs) => self.ast.slice(*fs).to_vec(),
            None => return,
        };
        let (mut head_size, mut head_occ) = (0, HashMap::new());
        self.paterson_measure(exposed, &mut head_size, &mut head_occ);
        let provided = match self.ast.ty(sig) {
            Ty::Arrow { to, .. } => self.ast.ty_source(*to),
            _ => None,
        };
        let provided = provided.unwrap_or_else(|| self.show(self.unifier.zonk(exposed)));
        let ctx = self.unifier.zonk(ctx);
        let parts = match self.unifier.types.node(ctx) {
            TypeNode::Tuple(items) if fields.len() > 1 => self.unifier.types.items(items).to_vec(),
            _ => vec![ctx],
        };
        for (f, part) in fields.iter().zip(parts) {
            let (mut size, mut occ) = (0, HashMap::new());
            self.paterson_measure(part, &mut size, &mut occ);
            let repeated = occ.iter().any(|(v, n)| *n > head_occ.get(v).copied().unwrap_or(0));
            if size < head_size && !repeated {
                continue;
            }
            let why = if repeated {
                "a type variable occurs in it more often than in the instance's type"
            } else {
                "it has as many constructors and variables as the instance's type, or more"
            };
            self.errors.push(diag!(
                Code::TypeMismatch, f.span, 0,
                "the instance `{name}` needs `{}`, which is not smaller than the `{provided}` it provides",
                self.ast.ty_source(f.ty).unwrap_or_else(|| self.show(part));
                note: "{why}, so searching for it may not terminate";
                help: "take `{}` apart into smaller requirements, or pass the instance explicitly", f.name
            ));
        }
    }

    /// The size of `ty` for the Paterson conditions, the constructors and
    /// variables it is built from, and how often each variable occurs.
    fn paterson_measure(&self, ty: Type, size: &mut usize, occ: &mut HashMap<VarId, usize>) {
        let ty = self.unifier.resolve(ty);
        let node = self.unifier.types.node(ty);
        if !matches!(node, TypeNode::App(..)) {
            *size += 1;
        }
        match node {
            TypeNode::Var(v) => *occ.entry(v).or_default() += 1,
            TypeNode::App(a, b) | TypeNode::NatAdd(a, b) | TypeNode::NatMul(a, b) | TypeNode::LevelMax(a, b) => {
                self.paterson_measure(a, size, occ);
                self.paterson_measure(b, size, occ);
            }
            TypeNode::LevelAdd(a, _) | TypeNode::Record(a) => self.paterson_measure(a, size, occ),
            TypeNode::Arrow(a, b, c) => {
                self.paterson_measure(a, size, occ);
                self.paterson_measure(b, size, occ);
                self.paterson_measure(c, size, occ);
            }
            TypeNode::RowField(_, a, b) | TypeNode::RowExtend(_, a, b) => {
                self.paterson_measure(a, size, occ);
                self.paterson_measure(b, size, occ);
            }
            TypeNode::Tuple(items) => {
                for t in self.unifier.types.items(items).to_vec() {
                    self.paterson_measure(t, size, occ);
                }
            }
            _ => {}
        }
    }

    /// Whether a type-constructor name is a declared `@Class`.
    pub(super) fn is_class(&self, head: utilities::StrId) -> bool {
        self.structs.get(&head).is_some_and(|s| s.class)
    }

    /// Whether a type-constructor name is a declared struct or union (as opposed to
    /// a base type like `@Int` or an arrow).
    pub(super) fn is_nominal(&self, head: utilities::StrId) -> bool {
        self.structs.contains_key(&head) || self.unions.contains_key(&head)
    }
}

// ## Resolution

impl<'a> Checker<'a> {
    /// Plan the context argument of `fname` at use `site`. The fields an explicit
    /// `@ctx {.f = e}` names are checked and used as given; the rest, and the whole
    /// context when there is no such argument, are resolved at the enclosing
    /// definition's boundary, where the requirement's type variables are pinned
    /// (so `max_of 3 7` searches for a context over `@Int` rather than over a bare
    /// variable). The binders that could satisfy it are captured now, because the
    /// scopes are gone by then. `sig` is the callee's signature, which names its
    /// instance fields.
    pub(super) fn plan_ctx(
        &mut self,
        site: Aol<Expr>,
        fname: StrId,
        req: Type,
        sig: Option<Aol<Ty>>,
    ) -> Result<()> {
        let mut given = Vec::new();
        if let Some(uses) = self.ctx_override.remove(&site) {
            given = self.use_given(fname, req, sig, &uses)?;
            let parts = self.bundle_items(req);
            if given.len() == parts.len().max(1) {
                let val = match parts.len() {
                    0 => CtxVal::Expr(given[0].1),
                    _ => {
                        given.sort_by_key(|g| g.0);
                        CtxVal::Tuple(given.iter().map(|g| CtxVal::Expr(g.1)).collect())
                    }
                };
                self.ctx_args.insert(site, val);
                return Ok(());
            }
        }
        let locals = self.ctx_locals(req);
        // Only a proposition field reads the hypotheses, and most contexts
        // have none, so the scopes are not walked for them.
        let proves = self.is_prop(req) || self.bundle_items(req).iter().any(|&p| self.is_prop(p));
        let hyps = (self.checking_def, if proves { self.hypotheses_in_scope() } else { Vec::new() });
        self.ctx_pending.push(PendingCtx {
            site,
            fname,
            req,
            sig: self.current_sig,
            locals,
            given,
            hyps,
        });
        Ok(())
    }

    /// Move the fields of explicit `@ctx` arguments `given` that name an
    /// instance field of `uses`, the signature of a callee with some, to the
    /// context `site` plans, each as its written expression. The rest, the
    /// fields unification solves, are returned, or `None` when none is left.
    pub(super) fn split_given(
        &mut self,
        site: Aol<Expr>,
        uses: Option<Aol<Ty>>,
        given: Option<Vec<UseOverride>>,
    ) -> Option<Vec<UseOverride>> {
        let given = given?;
        let Some(fields) = uses.and_then(|s| self.ast.use_params.get(s).copied()) else {
            return Some(given);
        };
        let names: Vec<StrId> = self.ast.slice(fields).iter().map(|f| f.name).collect();
        let (mut rest, mut found) = (Vec::new(), Vec::new());
        for u in given {
            let (mut ctx, mut inst) = (Vec::new(), Vec::new());
            for init in u.inits {
                match init {
                    FieldInit::Named { name, value } if names.contains(&name) => {
                        inst.push(FieldInit::Named { name, value });
                    }
                    other => ctx.push(other),
                }
            }
            if !inst.is_empty() {
                found.push(UseOverride { at: u.at, inits: inst, site: u.site });
            }
            if !ctx.is_empty() {
                rest.push(UseOverride { at: u.at, inits: ctx, site: u.site });
            }
        }
        if !found.is_empty() {
            self.ctx_override.insert(site, found);
        }
        (!rest.is_empty()).then_some(rest)
    }

    /// An explicit `@ctx` argument whose callee declares no `@ctx` field.
    pub(super) fn ctx_without_fields(&self, head: Aol<Expr>, given: &[UseOverride]) -> Diagnostic {
        let span = self.ast.expr_span(given[0].site).unwrap_or(Span::at(0));
        let callee = match self.node(head) {
            Expr::Var { name, .. } => format!("`{name}`"),
            _ => "this function".to_string(),
        };
        diag!(
            Code::TypeMismatch, span, 0,
            "a `@ctx` argument, but {callee} declares no `@ctx` parameter"
        )
    }

    /// A reference to `name` with explicit `@ctx {.f = v}` arguments, or to
    /// one with `@Nat` fields: its signature `sig` elaborated afresh, each field
    /// given unified with its value; the fields left out are solved as usual.
    /// `uses` tells a callee that also takes instance fields, planned here.
    pub(super) fn infer_ctx_given(
        &mut self,
        site: Aol<Expr>,
        name: StrId,
        sig: Option<Aol<Ty>>,
        uses: bool,
        bare: bool,
        given: &[UseOverride],
    ) -> Result<Type> {
        let Some(sig) = sig else {
            return Err(self.ctx_without_fields(site, given));
        };
        let mut fields: Vec<UseField> = match self.ast.level_params.get(sig) {
            Some(fs) => self.ast.slice(*fs).to_vec(),
            None => Vec::new(),
        };
        if let Some(fs) = self.ast.ctx_params.get(sig) {
            fields.extend(self.ast.slice(*fs).iter().copied());
        }
        let mut tvars = self.sig_tvars(sig);
        let full = self.ty_of_ast(sig, &mut tvars);
        // The signature elaborated afresh has none of the level constraints
        // the definition's body adds, on its named levels or the levels of its
        // effect variables; its scheme does. See Note [Level parameters].
        // See Note [Label variable levels].
        let effects = fields.iter().any(|f| self.is_effect_kind(f.ty));
        if bare && (self.ast.level_params.get(sig).is_some() || effects) {
            if let Some(scheme) = self.lookup(name) {
                let inst = self.unifier.instantiate(scheme);
                let exposed = match (uses, self.unifier.types.node(full)) {
                    (true, TypeNode::Arrow(_, to, _)) => to,
                    _ => full,
                };
                self.unifier.pair_labels(inst, exposed)?;
                self.unifier.unify(inst, exposed, &format!("against the signature of `{name}`"))?;
            }
        }
        let mut seen: Vec<StrId> = Vec::new();
        for u in given {
            for init in u.inits.clone() {
                let FieldInit::Named { name: f, value } = init else { continue };
                let span = self.ast.expr_span(value).or(self.ast.expr_span(u.site)).unwrap_or(Span::at(0));
                let Some(field) = fields.iter().find(|x| x.name == f).copied() else {
                    let uses = self.ast.use_params.get(sig).map(|fs| self.ast.slice(*fs).to_vec()).unwrap_or_default();
                    let known: Vec<&str> = fields.iter().chain(&uses).map(|x| x.name.as_str()).collect();
                    let mut d = diag!(Code::TypeMismatch, span, 0, "`{name}` has no `@ctx` field `{f}`");
                    if let Some(c) = utilities::error::closest(f.as_str(), known.iter().copied()) {
                        d = d.with_help(format!("did you mean `{c}`?"));
                    }
                    return Err(d);
                };
                if seen.contains(&f) {
                    return Err(diag!(Code::DuplicateSymbol, span, 0, "`@ctx` field `{f}` of `{name}` is given twice"));
                }
                seen.push(f);
                if field.before != u.at {
                    let at = self.ast.expr_span(u.site).unwrap_or(span);
                    return Err(diag!(
                        Code::TypeMismatch, at, 0,
                        "`@ctx` field `{f}` of `{name}` goes after {} explicit argument(s), not {}",
                        field.before, u.at;
                        note: "an explicit `@ctx` argument precedes the explicit argument that follows its parameter"
                    ));
                }
                if self.ast.level_params.get(sig).is_some_and(|ls| self.ast.slice(*ls).iter().any(|l| l.name == f)) {
                    let scoped = self.scoped_tvars.clone();
                    let level = self.level_of_expr(value, &scoped)?;
                    self.unifier
                        .unify(tvars[&f], level, &format!("in the level `{f}` of `{name}`"))
                        .map_err(|d| d.fill_span(span))?;
                    continue;
                }
                if self.is_effect_kind(field.ty) {
                    let (label, args) = self.label_of_expr(value, span)?;
                    let want = tvars[&f];
                    let want_args = self.unifier.label_args(want);
                    let where_ = format!("in the `@ctx` field `{f}` of `{name}`");
                    self.unifier.unify(want_args, args, &where_).map_err(|d| d.fill_span(span))?;
                    self.unifier.unify(want, label, &where_).map_err(|d| d.fill_span(span))?;
                    continue;
                }
                let vt = match self.kind_of_ast(field.ty) {
                    Some(ParamKind::Nat) => self.expr_as_size(value)?,
                    _ => self.expr_as_type(value)?,
                };
                let want = tvars[&f];
                self.unifier
                    .unify(want, vt, &format!("in the `@ctx` field `{f}` of `{name}`"))
                    .map_err(|d| d.fill_span(span))?;
            }
        }
        self.note_size_use(site, name, sig, &tvars);
        if !uses {
            return Ok(full);
        }
        match self.unifier.types.node(full) {
            TypeNode::Arrow(req, exposed, _) => {
                self.plan_ctx(site, name, req, Some(sig))?;
                Ok(exposed)
            }
            _ => Ok(full),
        }
    }

    /// The level an explicit `@ctx {.u = l}` argument gives: a number, a
    /// level `scoped` binds, `l + n` or `@max a b`.
    pub(super) fn level_of_expr(&mut self, e: Aol<Expr>, scoped: &HashMap<StrId, Type>) -> Result<Type> {
        let span = self.ast.expr_span(e).unwrap_or(Span::at(0));
        let bad = || diag!(Code::TypeMismatch, span, 0, "a level is a number, a level name, `l + n` or `@max a b`");
        match *self.node(e) {
            Expr::Int(n) => match u32::try_from(n) {
                Ok(n) => Ok(self.unifier.types.add(TypeNode::Level(n))),
                Err(_) => Err(bad()),
            },
            Expr::Var { module: None, name } => match scoped.get(&name) {
                Some(&l) if self.level_names.contains(&l) => Ok(l),
                _ => Err(self.unbound_level(name, span, scoped)),
            },
            Expr::BinOp { op, lhs, rhs } if op.as_str() == "+" => {
                let Expr::Int(k) = *self.node(rhs) else { return Err(bad()) };
                let k = u32::try_from(k).map_err(|_| bad())?;
                let l = self.level_of_expr(lhs, scoped)?;
                Ok(self.unifier.types.add(TypeNode::LevelAdd(l, k)))
            }
            Expr::App(f, b) => match *self.node(f) {
                Expr::App(m, a) if matches!(self.node(m), Expr::Var { module: None, name } if name.as_str() == "@max") => {
                    let (a, b) = (self.level_of_expr(a, scoped)?, self.level_of_expr(b, scoped)?);
                    Ok(self.unifier.types.add(TypeNode::LevelMax(a, b)))
                }
                _ => Err(bad()),
            },
            _ => Err(bad()),
        }
    }

    /// The components of a several-field instance bundle, or nothing for a
    /// one-field one (whose context is the field itself).
    fn bundle_items(&mut self, req: Type) -> Vec<Type> {
        let z = self.unifier.zonk(req);
        match self.unifier.types.node(z) {
            TypeNode::Tuple(items) => self.unifier.types.items(items).to_vec(),
            _ => Vec::new(),
        }
    }

    /// Match the instance fields of explicit `@ctx` arguments to `fname`'s
    /// by name, check each value against its field's type, and return
    /// `(position in the bundle, value)` for each. A field must be given where its
    /// parameter stands: after exactly the explicit arguments declared before it.
    fn use_given(
        &mut self,
        fname: StrId,
        req: Type,
        sig: Option<Aol<Ty>>,
        uses: &[UseOverride],
    ) -> Result<Vec<(usize, Aol<Expr>)>> {
        let fields: Vec<UseField> = match sig.and_then(|s| self.ast.use_params.get(s).copied()) {
            Some(fs) => self.ast.slice(fs).to_vec(),
            None => Vec::new(),
        };
        let parts = self.bundle_items(req);
        let mut out: Vec<(usize, Aol<Expr>)> = Vec::new();
        for u in uses {
            for init in u.inits.clone() {
                let FieldInit::Named { name, value } = init else { continue };
                let span = self.ast.expr_span(value).or(self.ast.expr_span(u.site)).unwrap_or(Span::at(0));
                let Some(i) = fields.iter().position(|f| f.name == name) else {
                    let known: Vec<&str> = fields.iter().map(|f| f.name.as_str()).collect();
                    let mut d = diag!(
                        Code::TypeMismatch, span, 0,
                        "`{fname}` has no `@ctx` field `{name}`"
                    );
                    if let Some(c) = utilities::error::closest(name.as_str(), known.iter().copied()) {
                        d = d.with_help(format!("did you mean `{c}`?"));
                    } else if known.is_empty() {
                        d = d.with_note(format!("`{fname}` declares no `@ctx` parameter"));
                    }
                    return Err(d);
                };
                if out.iter().any(|g| g.0 == i) {
                    return Err(diag!(
                        Code::DuplicateSymbol, span, 0,
                        "`@ctx` field `{name}` of `{fname}` is given twice"
                    ));
                }
                let field = fields[i];
                if field.before != u.at {
                    let site = self.ast.expr_span(u.site).unwrap_or(span);
                    return Err(diag!(
                        Code::TypeMismatch, site, 0,
                        "`@ctx` field `{name}` of `{fname}` goes after {} explicit argument(s), not {}",
                        field.before, u.at;
                        note: "an explicit `@ctx` argument precedes the explicit argument that follows its parameter"
                    ));
                }
                let want = if parts.is_empty() { req } else { parts[i] };
                self.check(value, want)?;
                out.push((i, value));
            }
        }
        Ok(out)
    }

    /// The binders in scope that could satisfy `req`, innermost scope first. A
    /// binder qualifies only when its type's head constructor is already the
    /// requirement's: a binder whose type is still open is not a candidate, because
    /// matching it would decide its type rather than read it.
    /// Extend `heads` with the heads of the contexts the instances of each one take,
    /// transitively.
    fn instance_context_heads(&self, heads: &mut Vec<utilities::StrId>) {
        let mut i = 0;
        while i < heads.len() {
            for inst in self.instances.get(&heads[i]).into_iter().flatten().filter(|inst| inst.has_ctx) {
                let Some(own) = self.bundle_parts(inst.bundle).1 else { continue };
                let own = self.unifier.zonk(own);
                let parts = match self.unifier.types.node(own) {
                    TypeNode::Tuple(items) => self.unifier.types.items(items).to_vec(),
                    _ => vec![own],
                };
                for part in parts {
                    if let Some(h) = self.ctx_head(self.unifier.zonk(part)) {
                        if !heads.contains(&h) {
                            heads.push(h);
                        }
                    }
                }
            }
            i += 1;
        }
    }

    pub(super) fn ctx_locals(&mut self, req: Type) -> Vec<CtxLocal> {
        let entries: Vec<(usize, StrId, Type)> = self
            .scopes
            .iter()
            .enumerate()
            .skip(1)
            .flat_map(|(d, s)| s.iter().map(move |(n, t)| (d, *n, *t)))
            .collect();
        // A bundle requirement (a callee with several instance fields) is resolved
        // component by component, so each component's head is wanted. So is every
        // head an instance of those needs as its own context, which resolving the
        // instance searches for next (`IFilter (Set t)` needs `IOrd t`).
        let zonked = self.unifier.zonk(req);
        let mut wants: Vec<utilities::StrId> = match self.unifier.types.node(zonked) {
            TypeNode::Tuple(items) => {
                let parts = self.unifier.types.items(items).to_vec();
                parts.into_iter().filter_map(|p| self.ctx_head(self.unifier.zonk(p))).collect()
            }
            _ => self.ctx_head(zonked).into_iter().collect(),
        };
        if wants.is_empty() {
            return Vec::new();
        }
        self.instance_context_heads(&mut wants);
        let wanted = |h: Option<utilities::StrId>| h.is_some_and(|h| wants.contains(&h));
        let mut out = Vec::new();
        for (depth, name, ty) in entries {
            let z = self.unifier.zonk(ty);
            if wanted(self.ctx_head(z)) {
                out.push(CtxLocal { depth, name, ty, index: None });
                continue;
            }
            // A binder holding a BUNDLE offers each of its components, so a function
            // that received several contexts at once can pass one of them onward.
            if let TypeNode::Tuple(items) = self.unifier.types.node(z) {
                let parts = self.unifier.types.items(items).to_vec();
                for (i, part) in parts.into_iter().enumerate() {
                    if wanted(self.ctx_head(part)) {
                        out.push(CtxLocal { depth, name, ty: part, index: Some(i) });
                    }
                }
            }
        }
        out.sort_by(|a, b| b.depth.cmp(&a.depth));
        out
    }

    /// The head constructor of a zonked type: `Ito_string (List t)` has head
    /// `Ito_string`. `None` when the head is not a constructor.
    pub(super) fn ctx_head(&self, ty: Type) -> Option<utilities::StrId> {
        let mut cur = ty;
        loop {
            match self.unifier.types.node(cur) {
                TypeNode::App(h, _) => cur = h,
                TypeNode::Con(n) => return Some(n),
                _ => return None,
            }
        }
    }

    // Note [Ctx resolution fixpoint]
    //
    // An instance requirement is resolved by its type, but at the use site that
    // type is usually still a variable: in `max_of 3 7` the requirement is
    // `IOrd a` until something says what `a` is. So a use only plans the
    // requirement (`plan_ctx`), and resolution waits for the definition
    // boundary, after its body is inferred.
    //
    // Even there the order matters. Three things pin variables, and each can
    // unblock the others: an operation several effects declare picks its
    // candidate once its argument types are known; a pending result type can
    // flow back to literal operands; and an unconstrained integer literal
    // defaults to `@Int`. `solve_pending` runs those to a fixpoint, trying the
    // next only when the previous made no progress, so a default never wins
    // over information inference could still find. Only then does
    // `resolve_pending_ctx` search for instances, against types that are as
    // pinned as they will get. A requirement whose type is still open there is
    // ambiguous, and reported, rather than resolved by a guess.
    //
    // The variables of the definition's own signature are rigid throughout:
    // the caller chooses them, so resolution may not specialize them to the one
    // instance that happens to exist.

    /// Solve every deferred context, at a definition boundary after overload
    /// solving and numeric defaulting have pinned the types.
    /// See Note [Ctx resolution fixpoint].
    pub(super) fn resolve_pending_ctx(&mut self) -> Result<()> {
        // Resolving one requirement can pin the types another one needs (the
        // builder `@IInterp` fixes is the one every `@IInterpText` of the string
        // reads), so a requirement that fails is retried while a pass makes
        // progress. A failed attempt is rolled back, so the retry sees the types
        // as the successful ones left them.
        let mut pending = std::mem::take(&mut self.ctx_pending);
        loop {
            let mut failed = Vec::new();
            let mut progress = false;
            for p in pending {
                let save = self.unifier.save();
                match self.resolve_pending_one(&p) {
                    Ok(val) => {
                        self.ctx_args.insert(p.site, val);
                        progress = true;
                    }
                    Err(d) => {
                        self.unifier.restore(save);
                        failed.push((p, d));
                    }
                }
            }
            progress |= self.solve_projections()?;
            if failed.is_empty() {
                return Ok(());
            }
            if progress {
                pending = failed.into_iter().map(|(p, _)| p).collect();
                continue;
            }
            for (p, d) in failed {
                // A metaprogram-expansion round: the instance may be injected by a
                // generator that has not run yet, so leave the site unresolved rather
                // than failing. The final strict round rejects it if it is still missing.
                if self.lenient {
                    self.defer(Some(p.site));
                    continue;
                }
                return Err(match self.ast.expr_span(p.site) {
                    Some(span) => d.fill_span(span),
                    None => d,
                });
            }
            return Ok(());
        }
    }

    /// Link each pending positional projection whose record has turned out a
    /// tuple to that tuple's component. Whether any was linked.
    fn solve_projections(&mut self) -> Result<bool> {
        let mut progress = false;
        for (rec, idx, t) in std::mem::take(&mut self.pending_projs) {
            let rec = self.unifier.resolve(rec);
            match self.unifier.types.node(rec) {
                TypeNode::Var(_) => self.pending_projs.push((rec, idx, t)),
                TypeNode::Tuple(items) => {
                    if let Some(&item) = self.unifier.types.items(items).get(idx) {
                        self.unifier.unify(item, t, "projecting a tuple component")?;
                        progress = true;
                    }
                }
                _ => {}
            }
        }
        Ok(progress)
    }

    /// One attempt at a planned requirement, with the types as they stand now.
    fn resolve_pending_one(&mut self, p: &PendingCtx) -> Result<CtxVal> {
        let req = self.unifier.zonk(p.req);
        let rigid: HashSet<VarId> = match p.sig {
            Some(sig) => {
                let mut vs = HashSet::new();
                self.unifier.collect_vars(self.unifier.zonk(sig), &mut vs);
                vs
            }
            None => HashSet::new(),
        };
        let outer = std::mem::replace(&mut self.proving, p.hyps.clone());
        let val = if p.given.is_empty() {
            self.resolve_ctx(p.fname, req, &p.locals, &rigid, 0)
        } else {
            self.resolve_partly_given(p.fname, req, &p.locals, &rigid, &p.given)
        };
        self.proving = outer;
        val
    }

    /// A several-field instance bundle some of whose fields an explicit argument
    /// gave: those are used as written, the rest are searched.
    fn resolve_partly_given(
        &mut self,
        fname: StrId,
        req: Type,
        locals: &[CtxLocal],
        rigid: &HashSet<VarId>,
        given: &[(usize, Aol<Expr>)],
    ) -> Result<CtxVal> {
        let parts = self.bundle_items(req);
        let mut vals = Vec::with_capacity(parts.len());
        for (i, part) in parts.into_iter().enumerate() {
            vals.push(match given.iter().find(|g| g.0 == i) {
                Some(&(_, value)) => CtxVal::Expr(value),
                None if self.is_prop(part) => self.prove(fname, self.use_field_at(fname, i), part, rigid)?,
                None => {
                    let part = self.unifier.zonk(part);
                    self.resolve_ctx(fname, part, locals, rigid, 1)?
                }
            });
        }
        Ok(CtxVal::Tuple(vals))
    }

    /// Resolve one context requirement. A tuple requirement splits into its
    /// components (several contexts travel as one bundle, built here so no global
    /// of the bundled type has to exist). Otherwise the innermost scope offering
    /// exactly one binder of the type wins, then the instances in scope, of which
    /// exactly one must match because global scope is flat. An instance that itself
    /// takes a context has it resolved here too, bounded by [`CTX_DEPTH`].
    pub(super) fn resolve_ctx(
        &mut self,
        fname: StrId,
        req: Type,
        locals: &[CtxLocal],
        rigid: &HashSet<VarId>,
        depth: usize,
    ) -> Result<CtxVal> {
        if depth > CTX_DEPTH {
            return Err(diag!(
                Code::TypeMismatch, Span::at(0), 0,
                "resolving the context of `{fname}` did not terminate within {CTX_DEPTH} steps"
            )
            .with_note("an instance whose own context leads back to itself cannot be built")
            .with_help("pass the context explicitly instead"));
        }
        if let TypeNode::Tuple(parts) = self.unifier.types.node(req) {
            let parts = self.unifier.types.items(parts).to_vec();
            let mut vals = Vec::with_capacity(parts.len());
            for (i, part) in parts.into_iter().enumerate() {
                let part = self.unifier.zonk(part);
                vals.push(match self.is_prop(part) {
                    true => self.prove(fname, self.use_field_at(fname, i), part, rigid)?,
                    false => self.resolve_ctx(fname, part, locals, rigid, depth + 1)?,
                });
            }
            return Ok(CtxVal::Tuple(vals));
        }
        if self.is_prop(req) {
            return self.prove(fname, self.use_field_at(fname, 0), req, rigid);
        }
        let Some(head) = self.ctx_head(req) else {
            return Err(self.ctx_unresolved(fname, req));
        };
        // The requirement's own rigid variables: a candidate may not bind these, so
        // only something that mentions the same variables (the enclosing
        // definition's context parameter) can satisfy a still-open requirement.
        // Which of the requirement's variables a candidate may not bind. For a LOCAL
        // binder that is all of them: a dictionary in scope must satisfy the
        // requirement as written, never specialize it, or an unrelated operator
        // whose type is not pinned yet (`i + 1` inside a function that takes a
        // dictionary) would silently adopt it. The instance search is allowed to
        // pin a flexible variable, which is how a unique instance decides the type
        // of a literal; it may still never touch a variable of the enclosing
        // signature, which belongs to the caller.
        let all: HashSet<VarId> = {
            let mut vs = HashSet::new();
            self.unifier.collect_vars(req, &mut vs);
            vs
        };
        let open: HashSet<VarId> = all.intersection(rigid).copied().collect();
        let req_vars = all.len();
        let local_closed: HashSet<VarId> = all.union(rigid).copied().collect();
        let depths: Vec<usize> = {
            let mut ds: Vec<usize> = locals.iter().map(|l| l.depth).collect();
            ds.dedup();
            ds
        };
        for d in depths {
            let hits: Vec<CtxLocal> = locals
                .iter()
                .filter(|l| l.depth == d)
                .filter(|l| self.ctx_matches(l.ty, req, &local_closed))
                .cloned()
                .collect();
            if hits.len() > 1 {
                let names: Vec<StrId> = hits.iter().map(|l| l.name).collect();
                return Err(self.ctx_ambiguous(fname, req, &names));
            }
            if let Some(l) = hits.first() {
                let (name, ty, index) = (l.name, l.ty, l.index);
                let inst = self.unifier.instantiate(ty);
                self.unifier.unify(
                    inst,
                    req,
                    &format!("resolving the context of `{fname}`"),
                )?;
                let base = CtxVal::Bare(name);
                return Ok(match index {
                    Some(i) => CtxVal::Proj(Box::new(base), i),
                    None => base,
                });
            }
        }
        let cands = self.instances.get(&head).cloned().unwrap_or_default();
        let mut hits: Vec<Inst> = Vec::new();
        for c in &cands {
            let save = self.unifier.save();
            let inst = self.unifier.instantiate(c.bundle);
            let exposed = self.bundle_parts(inst).0;
            let mut ok = self.unifier.keeping(&open, |u| u.unify(exposed, req, "resolving a context")).is_ok();
            if ok {
                ok = self.keeps_open(&open);
            }
            self.unifier.restore(save);
            if ok {
                hits.push(c.clone());
            }
        }
        // With the requirement still open, neither "none in scope" nor "several in
        // scope" is the user's problem: the type is not pinned, so say that instead.
        if req_vars > 0 && hits.len() != 1 {
            return Err(self.ctx_unresolved(fname, req));
        }
        if hits.len() > 1 {
            let names: Vec<StrId> = hits.iter().map(|c| c.name).collect();
            return Err(self.ctx_ambiguous(fname, req, &names));
        }
        let Some(c) = hits.first().cloned() else {
            let d = self.ctx_missing(fname, req);
            return Err(self.explain_near_miss(d, fname, &cands, req));
        };
        let inst = self.unifier.instantiate(c.bundle);
        let (exposed, own) = self.bundle_parts(inst);
        self.unifier.keeping(&open, |u| u.unify(exposed, req, &format!("resolving the context of `{fname}`")))?;
        let base = match c.module {
            Some(m) => CtxVal::Qualified {
                module: m,
                name: c.name,
            },
            None => CtxVal::Bare(c.name),
        };
        if !c.has_ctx {
            return Ok(base);
        }
        let own = self.unifier.zonk(own.expect("an instance with a context packs it"));
        let arg = self.resolve_ctx(c.name, own, locals, rigid, depth + 1)?;
        Ok(CtxVal::App(Box::new(base), Box::new(arg)))
    }

    /// Whether a candidate of type `ty` satisfies `req` without binding any variable
    /// in `closed`. The trial unification is rolled back either way.
    pub(super) fn ctx_matches(&mut self, ty: Type, req: Type, closed: &HashSet<VarId>) -> bool {
        let save = self.unifier.save();
        let inst = self.unifier.instantiate(ty);
        let mut ok = self.unifier.unify(inst, req, "resolving a context").is_ok();
        if ok {
            ok = self.keeps_open(closed);
        }
        self.unifier.restore(save);
        ok
    }

    /// Whether every variable in `closed` is still unbound after a trial
    /// unification. One that has been bound was specialized by the candidate, which
    /// is not this resolution's business: the variable belongs to the caller (a
    /// signature's) or to the requirement itself.
    pub(super) fn keeps_open(&self, closed: &HashSet<VarId>) -> bool {
        closed.iter().all(|v| self.unifier.is_free(*v))
    }

    /// Split an instantiated instance bundle into its exposed type and, when the
    /// instance takes a context of its own, that requirement.
    pub(super) fn bundle_parts(&self, bundle: Type) -> (Type, Option<Type>) {
        match self.unifier.types.node(bundle) {
            TypeNode::Tuple(parts) => {
                let items = self.unifier.types.items(parts);
                (items[0], items.get(1).copied())
            }
            _ => (bundle, None),
        }
    }
}

// ## Resolution failures

impl<'a> Checker<'a> {
    /// No instance matched `req`, but one may agree on its first parameter (the
    /// type the interface is "for") and disagree on another, typically one the
    /// call fixed indirectly, e.g. `for xs \\i => i` pins `IFor`'s element type
    /// through the body's result. Then the context IS determined and simply does
    /// not fit, so say that, naming the instance and the parameter that differs,
    /// rather than claim none is in scope.
    pub(super) fn explain_near_miss(&mut self, d: Diagnostic, fname: StrId, cands: &[Inst], req: Type) -> Diagnostic {
        let (_, want) = self.spine(req);
        let Some(&first) = want.first() else {
            return d;
        };
        for c in cands {
            let save = self.unifier.save();
            let inst = self.unifier.instantiate(c.bundle);
            let exposed = self.bundle_parts(inst).0;
            let (_, has) = self.spine(exposed);
            let mut differs = Vec::new();
            if has.len() == want.len() && self.unifier.unify(has[0], first, "").is_ok() {
                for i in 1..has.len() {
                    let probe = self.unifier.save();
                    if self.unifier.unify(has[i], want[i], "").is_err() {
                        differs.push(i);
                    }
                    self.unifier.restore(probe);
                }
            }
            if differs.is_empty() {
                self.unifier.restore(save);
                continue;
            }
            let mut out = diag!(
                Code::TypeMismatch, Span::at(0), 0,
                "`{}` does not fit this use of `{fname}`", c.name;
                note: "`{fname}` needs `{}` here, and `{}` has type `{}`",
                    self.show(req), c.name, self.show(self.unifier.zonk(exposed))
            );
            for i in differs {
                let (h, w) = (self.show(self.unifier.zonk(has[i])), self.show(self.unifier.zonk(want[i])));
                out = out.with_note(format!(
                    "its {} type parameter is `{h}`, but this use needs `{w}`",
                    ordinal(i + 1)
                ));
            }
            self.unifier.restore(save);
            if let Some(sig) = self.show_name(fname) {
                out = out.with_note(format!("`{fname} : {sig}`"));
            }
            return out.with_help(format!(
                "make the arguments of `{fname}` agree with `{}`",
                c.name
            ));
        }
        d
    }

    /// No value of the requirement's type is in scope.
    pub(super) fn ctx_missing(&self, fname: StrId, req: Type) -> Diagnostic {
        // A blessed interface comes from a desugar (`.[i]`, `1.2i`), so the site
        // has no call to pass a context to.
        if is_blessed_interface(fname.as_str()) {
            return diag!(
                Code::TypeMismatch, Span::at(0), 0,
                "no `{fname}` instance of type `{}` is in scope",
                self.show(req);
                help: "define or import a value of type `{}`", self.show(req)
            );
        }
        diag!(
            Code::TypeMismatch, Span::at(0), 0,
            "no value of type `{}` in scope to satisfy the context of `{fname}`",
            self.show(req)
        )
        .with_help(format!(
            "define or import a value of type `{}`, or pass one explicitly as `{}`",
            self.show(req),
            self.explicit_use_call(fname, req, "value")
        ))
    }

    /// The requirement is still open, so there is nothing to search for. Reported
    /// with both escapes, because neither is obvious from the call alone.
    pub(super) fn ctx_unresolved(&self, fname: StrId, req: Type) -> Diagnostic {
        diag!(
            Code::TypeMismatch, Span::at(0), 0,
            "the context `{}` of `{fname}` is not determined here",
            self.show(req)
        )
        .with_help(
            "annotate the call so its type is known, or declare a `@ctx` field of that type \
             on the enclosing definition so the context is passed in",
        )
    }

    /// Several values of the requirement's type are in scope. An annotation cannot
    /// break this tie, since the candidates share a type, so the note offers the
    /// explicit form instead.
    pub(super) fn ctx_ambiguous(&self, fname: StrId, req: Type, names: &[StrId]) -> Diagnostic {
        diag!(
            Code::TypeMismatch, Span::at(0), 0,
            "several values of type `{}` satisfy the context of `{fname}`: {}",
            self.show(req),
            names.iter().map(|n| n.as_str()).collect::<Vec<_>>().join(", ")
        )
        .with_help(format!(
            "pass the one you mean explicitly as `{}`",
            self.explicit_use_call(fname, req, names.first().map_or("value", |n| n.as_str()))
        ))
    }

    /// A call of `fname` passing `value` as its `@ctx` field for `req`. An
    /// operator is written in its function form, `(+) @ctx {.d = v} a b`, since
    /// the infix form has no place for an explicit argument.
    fn explicit_use_call(&self, fname: StrId, req: Type, value: &str) -> String {
        let field = self.use_field_hint(fname, req);
        let name = fname.as_str();
        if name.bytes().next().is_some_and(crate::lexer::data::is_operator_char) {
            format!("({name}) @ctx {{.{field} = {value}}} a b")
        } else {
            format!("{name} @ctx {{.{field} = {value}}} ...")
        }
    }

    /// The name of `fname`'s instance field whose type has `req`'s head, for a
    /// diagnostic's suggested explicit argument; `field` when it cannot tell.
    fn use_field_hint(&self, fname: StrId, req: Type) -> String {
        let sig = self.global_ctx.get(&fname).copied();
        let fields: Vec<UseField> = match sig.and_then(|s| self.ast.use_params.get(s).copied()) {
            Some(fs) => self.ast.slice(fs).to_vec(),
            None => return "field".to_string(),
        };
        let want = self.ctx_head(self.unifier.zonk(req));
        let hits: Vec<&UseField> = fields
            .iter()
            .filter(|f| want.is_some_and(|w| self.ty_head_name(f.ty) == Some(w)))
            .collect();
        match hits.as_slice() {
            [one] => one.name.as_str().to_string(),
            _ if fields.len() == 1 => fields[0].name.as_str().to_string(),
            _ => "field".to_string(),
        }
    }

    /// The name of `fname`'s instance field at position `i` of its bundle.
    fn use_field_at(&self, fname: StrId, i: usize) -> Option<StrId> {
        let sig = self.global_ctx.get(&fname).copied()?;
        let fields = self.ast.use_params.get(sig).copied()?;
        self.ast.slice(fields).get(i).map(|f| f.name)
    }

    /// The constructor a written type is headed by: `IOrd` in `IOrd t`.
    fn ty_head_name(&self, ty: Aol<Ty>) -> Option<StrId> {
        let mut cur = ty;
        loop {
            match self.ast.ty(cur) {
                Ty::App(f, _) => cur = *f,
                Ty::Con { name, .. } => return Some(*name),
                _ => return None,
            }
        }
    }
}

// ## Blessed interfaces

impl<'a> Checker<'a> {
    /// The requirement type, single field name, and field type of blessed interface
    /// `name` applied to `args`. `None` when the interface is not declared in scope,
    /// so a desugar site keeps its built-in meaning.
    pub(super) fn blessed_req(&mut self, name: StrId, args: &[Type]) -> Option<(Type, StrId, Type)> {
        let info = self.structs.get(&name)?.clone();
        if info.params.len() != args.len() || info.fields.len() != 1 {
            return None;
        }
        let mut tvars: HashMap<StrId, Type> = info
            .params
            .iter()
            .copied()
            .zip(args.iter().copied())
            .collect();
        let (field, field_ty) = info.fields[0];
        let field_ty = self.ty_of_ast(field_ty, &mut tvars);
        let mut req = self.unifier.types.con(name);
        for a in args {
            req = self.unifier.types.app(req, *a);
        }
        Some((req, field, field_ty))
    }

    /// Resolve blessed interface `name` applied to `args` at a desugar site: the
    /// instance found by type, plus the type of its single field (what the site's
    /// operands are checked against). A failure leaves the unifier untouched and
    /// returns `None`, so the site falls back to its built-in meaning.
    pub(super) fn blessed(&mut self, name: StrId, args: &[Type]) -> Option<(HookImpl, Type)> {
        let save = self.unifier.save();
        let Some((req, field, field_ty)) = self.blessed_req(name, args) else {
            self.unifier.restore(save);
            return None;
        };
        match self.resolve_blessed(name, req, field) {
            Some(hook) => Some((hook, field_ty)),
            None => {
                self.unifier.restore(save);
                None
            }
        }
    }

    /// The instance satisfying an already-built blessed requirement. Unlike
    /// [`Self::blessed`] a failure is NOT rolled back, so callers that have already
    /// committed unifications probe with their own `save`/`restore` first.
    pub(super) fn resolve_blessed(&mut self, name: StrId, req: Type, field: StrId) -> Option<HookImpl> {
        let locals = self.ctx_locals(req);
        let rigid = HashSet::new();
        self.resolve_ctx(name, req, &locals, &rigid, 0)
            .ok()
            .map(|ctx| HookImpl { ctx, field })
    }

    /// A desugar's blessed-interface call (`.[i]` emits `@IIndex`, `1.2i` emits
    /// `@IImagLit`). The arguments pin the interface's parameters through its
    /// method's declared type; the instance resolves here when that is enough, and
    /// otherwise at the enclosing definition's boundary, once the surrounding types
    /// pin what is left.
    ///
    /// With an `expected` result, it is pinned first, and an instance it alone
    /// determines is chosen before the arguments are checked, so they see its
    /// types: `@IInterp b Html` fixes the builder `b` the string's holes append to.
    pub(super) fn infer_blessed_app(
        &mut self,
        head: Aol<Expr>,
        name: StrId,
        args: &[Aol<Expr>],
        expected: Option<Type>,
    ) -> Result<Type> {
        let arity = self.structs.get(&name).map(|i| i.params.len()).unwrap_or(0);
        let vars: Vec<Type> = (0..arity).map(|_| self.unifier.fresh()).collect();
        let Some((req, field, method)) = self.blessed_req(name, &vars) else {
            let span = self.ast.expr_span(head).unwrap_or_else(|| Span::at(0));
            return Err(diag!(
                Code::TypeUnbound, span, 0,
                "`{name}` is not declared";
                note: "it is a blessed interface the compiler resolves at this site; \
                       CORE declares it as a one-field `@struct`"
            ));
        };
        if let Some(want) = expected {
            let save = self.unifier.save();
            let mut result = Ok(method);
            for _ in args {
                result = result.and_then(|t| self.arrow_parts(t)).map(|(_, next, _)| next);
            }
            let pinned = result.and_then(|t| self.unifier.unify(t, want, "against the expected type"));
            let zonked = self.unifier.zonk(req);
            match pinned.ok().and_then(|_| self.resolve_blessed(name, zonked, field)) {
                Some(hook) => {
                    self.ctx_args.insert(head, hook.ctx);
                    self.blessed_sites.insert(head, hook.field);
                    let mut rest = method;
                    for a in args {
                        let (param, next, eff) = self.arrow_parts(rest)?;
                        let amb = self.ambient;
                        self.unifier.subrow(eff, amb, "in a function application")?;
                        self.check(*a, param)?;
                        rest = next;
                    }
                    return Ok(self.unifier.zonk(rest));
                }
                None => self.unifier.restore(save),
            }
        }
        let mut rest = method;
        for a in args {
            let (param, next, eff) = self.arrow_parts(rest)?;
            let amb = self.ambient;
            self.unifier.subrow(eff, amb, "in a function application")?;
            self.check(*a, param)?;
            rest = next;
        }
        let probe = self.unifier.save();
        let zonked = self.unifier.zonk(req);
        let resolvable = self
            .resolve_blessed(name, zonked, field)
            .is_some();
        self.unifier.restore(probe);
        if resolvable {
            let zonked = self.unifier.zonk(req);
            let hook = self
                .resolve_blessed(name, zonked, field)
                .expect("the probe above resolved it");
            self.ctx_args.insert(head, hook.ctx);
            self.blessed_sites.insert(head, hook.field);
            return Ok(self.unifier.zonk(rest));
        }
        self.plan_ctx(head, name, req, None)?;
        self.blessed_sites.insert(head, field);
        Ok(rest)
    }

    /// Every instance of blessed interface `name` in scope, as the diagnostic that
    /// lists what a range can build needs them.
    pub(super) fn blessed_instances(&self, name: StrId) -> Vec<Inst> {
        self.instances.get(&name).cloned().unwrap_or_default()
    }

    /// The head constructor of `ty` if it is a user-declared type (struct / union /
    /// alias), following an application spine (`MyVec Int` -> `MyVec`). A
    /// builtin, a variable, a tuple, or a function returns `None`, so a construction
    /// hook only ever intercepts a literal aimed at a user type.
    pub(super) fn user_type_head(&self, ty: Type) -> Option<StrId> {
        let mut cur = self.unifier.resolve(ty);
        loop {
            match self.unifier.types.node(cur) {
                TypeNode::App(head, _) => cur = self.unifier.resolve(head),
                TypeNode::Con(name) => {
                    return (self.structs.contains_key(&name)
                        || self.unions.contains_key(&name)
                        || self.aliases.contains_key(&name))
                    .then_some(name);
                }
                _ => return None,
            }
        }
    }

    /// Route a literal (`"..."`, an int, a real, `[..]`) through the
    /// blessed `@I*` construction interface whose result type is the expected
    /// one. On a unique match it unifies, checks any element types, records the hook
    /// at `site` for lowering, and returns `true`; otherwise it leaves the unifier
    /// untouched and returns `false`, so the literal falls back to its built-in
    /// default (which lowering folds to a plain constant).
    pub(super) fn literal_hook_check(&mut self, e: Aol<Expr>, expected: Type) -> Result<bool> {
        // The target type must already have a constructor head: with it still open,
        // resolving would DECIDE what the literal is rather than read it.
        let zonked = self.unifier.zonk(expected);
        if self.ctx_head(zonked).is_none() {
            return Ok(false);
        }
        let (name, args, elem): (StrId, _, _) = match self.node(e) {
            Expr::Str(_) => (IF_STR_LIT.into(), vec![expected], None),
            Expr::Int(_) => (IF_INT_LIT.into(), vec![expected], None),
            Expr::Real(_) => (IF_REAL_LIT.into(), vec![expected], None),
            Expr::List(_) => {
                let elem = self.unifier.fresh();
                (IF_SEQ_LIT.into(), vec![elem, expected], Some(elem))
            }
            _ => return Ok(false),
        };
        let Some((hook, _)) = self.blessed(name, &args) else {
            return Ok(false);
        };
        // A sequence literal checks each element against the instance's element type.
        if let (Expr::List(items), Some(elem)) = (self.node(e), elem) {
            let items = self.ast.slice(*items).to_vec();
            for it in items {
                self.check(it, elem)?;
            }
        }
        if matches!(self.node(e), Expr::Str(_)) && self.is_code(expected) {
            self.quotations.insert(e);
        }
        self.literal_hooks.insert(e, hook);
        Ok(true)
    }

    /// Resolve a range (`[lo ... hi]` / `[lo ...]`) through its `@IRange` /
    /// `@IRangeFrom` instance: the bounds are the instance method's arguments, and
    /// what it returns is the range's type. Records the instance at `site` so
    /// lowering projects and applies it. `expected`, when known, takes part in the
    /// resolution, so a second instance is picked by context.
    pub(super) fn range_hook(
        &mut self,
        site: Aol<Expr>,
        lo: Aol<Expr>,
        hi: Option<Aol<Expr>>,
        expected: Option<Type>,
    ) -> Result<Type> {
        let name = StrId::intern(if hi.is_some() { IF_RANGE } else { IF_RANGE_FROM });
        let bound = self.infer(lo)?;
        if let Some(hi) = hi {
            let t = self.infer(hi)?;
            self.unifier.unify(bound, t, "between a range's bounds")?;
        }
        let result = self.unifier.fresh();
        if let Some(exp) = expected {
            let save = self.unifier.save();
            if self.unifier.unify(result, exp, "in a range").is_err() {
                self.unifier.restore(save);
            }
        }
        // With nothing to pin the result, several instances fit. Rather than call that
        // ambiguous, the FIRST one declared is the default, so CORE's declaration
        // order sets what a bare range builds: a `@Vec` for `[lo ... hi]`, a `Stream`
        // for `[lo ...]`. An annotation or a known expected type still picks another.
        let hook = self
            .blessed(name, &[bound, result])
            .or_else(|| self.blessed_first(name, &[bound, result]));
        let Some((hook, field_ty)) = hook else {
            let offered = self
                .blessed_instances(name)
                .iter()
                .map(|i| i.name.as_str())
                .collect::<Vec<_>>()
                .join(", ");
            let want = self.show(result);
            let note = if offered.is_empty() {
                format!("`{name}` is declared in CORE; a range builds whatever its instance returns")
            } else {
                format!("the `{name}` instances in scope are: {offered}")
            };
            return Err(diag!(
                Code::TypeMismatch, Span::at(0), 0,
                "no `{name}` instance builds a `{want}` from this range";
                note: "{note}"
            ));
        };
        // The method's own type decides how the bounds are typed, so a range over a
        // non-`@Int` bound works exactly as the instance declares it.
        let mut rest = field_ty;
        for arg in std::iter::once(lo).chain(hi) {
            let (param, next, _) = self.arrow_parts(rest)?;
            self.check(arg, param)?;
            rest = next;
        }
        self.unifier.unify(rest, result, "in a range")?;
        self.literal_hooks.insert(site, hook);
        Ok(self.unifier.zonk(result))
    }

    /// The FIRST blessed instance of `name` that satisfies the requirement,
    /// committing it. Used as the default when nothing constrains the result and
    /// several instances fit; the strict unique-match rule is [`Self::blessed`].
    pub(super) fn blessed_first(&mut self, name: StrId, args: &[Type]) -> Option<(HookImpl, Type)> {
        for inst in self.blessed_instances(name) {
            let save = self.unifier.save();
            let Some((req, field, field_ty)) = self.blessed_req(name, args) else {
                self.unifier.restore(save);
                return None;
            };
            let packed = self.unifier.instantiate(inst.bundle);
            let (exposed, own) = self.bundle_parts(packed);
            if self.unifier.unify(exposed, req, "resolving a range").is_err() {
                self.unifier.restore(save);
                continue;
            }
            let base = match inst.module {
                Some(m) => CtxVal::Qualified {
                    module: m,
                    name: inst.name,
                },
                None => CtxVal::Bare(inst.name),
            };
            let ctx = if inst.has_ctx {
                let own = self.unifier.zonk(own.expect("an instance with a context packs it"));
                let locals = self.ctx_locals(own);
                match self.resolve_ctx(inst.name, own, &locals, &HashSet::new(), 0) {
                    Ok(arg) => CtxVal::App(Box::new(base), Box::new(arg)),
                    Err(_) => {
                        self.unifier.restore(save);
                        continue;
                    }
                }
            } else {
                base
            };
            return Some((HookImpl { ctx, field }, field_ty));
        }
        None
    }
}

// ## Pattern hooks

impl<'a> Checker<'a> {
    /// The blessed construction interface for a literal PATTERN kind
    /// (`Str`/`Int`/`Real`), so a literal pattern reuses the same builder a literal
    /// expression does.
    pub(super) fn pattern_literal_hook(pat: &Pattern) -> Option<StrId> {
        Some(match pat {
            Pattern::Str(_) => IF_STR_LIT,
            Pattern::Int(_) => IF_INT_LIT,
            Pattern::Real(_) => IF_REAL_LIT,
            _ => return None,
        }
        .into())
    }

    /// Resolve the sequence view `view` (`@ISeqView` or `@ISeqViewBack`) for a
    /// pattern piece's scrutinee. On success records the hook at `pat` and returns
    /// `Some(element type)`; otherwise `None`, with the unifier untouched.
    pub(super) fn sequence_pattern_hook_check(
        &mut self,
        pat: Aol<Pattern>,
        expected: Type,
        view: StrId,
    ) -> Result<Option<Type>> {
        let elem = self.unifier.fresh();
        let Some((hook, _)) = self.blessed(view, &[expected, elem]) else {
            return Ok(None);
        };
        self.sequence_pattern_hooks.insert(pat, hook);
        Ok(Some(elem))
    }

    /// The element type of a sequence pattern piece's scrutinee, through `view`.
    /// A scrutinee not yet known DEFAULTS to `@Vec elem`. Records the hook at
    /// `pat` either way.
    pub(super) fn sequence_pattern_elem(&mut self, pat: Aol<Pattern>, expected: Type, view: StrId) -> Result<Type> {
        if let Some(elem) = self.sequence_pattern_hook_check(pat, expected, view)? {
            return Ok(elem);
        }
        if self.user_type_head(expected).is_some() || matches!(self.unifier.head(expected), TypeNode::Con(_)) {
            return Err(self.no_sequence_view(expected, view));
        }
        let elem = self.unifier.fresh();
        let vec_con = self.unifier.types.con(ty::VEC);
        let want = self.unifier.types.app(vec_con, elem);
        self.unifier.unify(expected, want, "in a sequence pattern")?;
        Ok(self.sequence_pattern_hook_check(pat, expected, view)?.unwrap_or(elem))
    }

    pub(super) fn no_sequence_view(&self, expected: Type, view: StrId) -> Diagnostic {
        let shown = self.unifier.show(expected);
        let end = if view == IF_SEQ_VIEW { "front" } else { "back" };
        diag!(
            Code::TypeMismatch, Span::at(0), 0,
            "`{shown}` cannot be matched from the {end} by a sequence pattern";
            note: "a sequence pattern steps the scrutinee through its `{view}` instance";
            help: "give `{shown}` an `{view}` instance, or match it another way"
        )
    }

    /// Route a literal pattern (`| "foo"`, `| 42`) whose scrutinee is a user type
    /// through that type's construction + equality hooks: it matches by building the
    /// literal into the user type and comparing with its `IEq` instance.
    /// On success records both hooks at `pat` for lowering and returns `true`;
    /// otherwise leaves the unifier untouched and returns `false` (the caller applies
    /// the built-in literal-pattern typing).
    pub(super) fn literal_pattern_hook_check(&mut self, pat: Aol<Pattern>, expected: Type) -> Result<bool> {
        if self.user_type_head(expected).is_none() {
            return Ok(false);
        }
        let Some(build_name) = Self::pattern_literal_hook(self.pnode(pat)) else {
            return Ok(false);
        };
        let save = self.unifier.save();
        let build = self.blessed(build_name, &[expected]);
        let eq = self.blessed(IF_EQ.into(), &[expected]);
        match (build, eq) {
            (Some((build, _)), Some((eq, _))) => {
                self.literal_pattern_hooks.insert(pat, (build, eq));
                Ok(true)
            }
            _ => {
                self.unifier.restore(save);
                Ok(false)
            }
        }
    }
}

/// `1` -> `first`, for a diagnostic naming a position.
pub(super) fn ordinal(n: usize) -> String {
    match n {
        1 => "first".to_string(),
        2 => "second".to_string(),
        3 => "third".to_string(),
        4 => "fourth".to_string(),
        _ => format!("#{n}"),
    }
}

/// How deep context resolution may chain instances (an instance whose own context
/// is satisfied by another instance) before it is reported as non-terminating.
pub(super) const CTX_DEPTH: usize = 32;

// ## Interface wrappers

/// The field an interface wrapper projects: `body` must be exactly
/// `\d p1 .. pn => d.field p1 .. pn`, with `d` and the parameters distinct variable
/// patterns applied in order. Anything else (`neg`'s `ds.0.sub ds.1.zero x`, a
/// wrapper that reorders or transforms) returns `None`.
pub(super) fn wrapper_field(ast: &Ast, body: Aol<Expr>) -> Option<StrId> {
    let Expr::Lambda { params, body } = ast.expr(body) else {
        return None;
    };
    let params = ast.slice(*params);
    let names: Vec<StrId> = params
        .iter()
        .map(|p| match ast.pat(p.pat) {
            Pattern::Var(n) => Some(*n),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()?;
    let (ctx, rest) = names.split_first()?;
    // Peel the applications off the spine; they must be the parameters in order.
    let mut args = Vec::new();
    let mut head = *body;
    while let Expr::App(f, x) = ast.expr(head) {
        args.push(*x);
        head = *f;
    }
    args.reverse();
    if args.len() != rest.len() {
        return None;
    }
    for (arg, want) in args.iter().zip(rest) {
        match ast.expr(*arg) {
            Expr::Var { module: None, name } if *name == *want => {}
            _ => return None,
        }
    }
    let Expr::Field { record, name } = ast.expr(head) else {
        return None;
    };
    match ast.expr(*record) {
        Expr::Var { module: None, name: r } if *r == *ctx => Some(*name),
        _ => None,
    }
}
