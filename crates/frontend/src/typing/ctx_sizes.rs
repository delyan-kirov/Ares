//! `@ctx {n: @Nat}` fields passed at run time.
//!
//! A `@Nat` field is erased unless its definition needs the number: its body
//! uses `n` as a value, or passes `n` (or a size built from it) to a callee
//! field that is itself passed. Which fields those are is only known once
//! every body of the module is checked, so the checker records two things on
//! the way and settles them at the end ([`Checker::finish_sizes`]):
//!
//! - the fields each body reads as a value (`size_refs`);
//! - at each reference to a global with `@Nat` fields, what each field was
//!   solved to, as a sum of products of literals and the caller's own fields
//!   (`size_uses`, converted at the definition boundary by
//!   [`Checker::settle_sizes`], while the types are pinned).
//!
//! The passed fields are then the least fixpoint of "read in the body, or
//! needed by a passed callee field". A passed field the caller cannot build
//! (a size it does not hold at run time) is an error there; an erased one
//! never is, so a size known only to the type (`slice : ... -> @Tensor k a`)
//! keeps working. Lowering prepends a definition's passed fields as lambda
//! parameters ([`Resolved::size_params`]) and applies the built sizes at each
//! reference ([`Resolved::size_args`]).
//!
//! Entry points: [`Checker::bind_size_fields`], [`Checker::note_size_use`],
//! [`Checker::settle_sizes`], [`Checker::finish_sizes`].

use super::*;
use super::signatures::{Shape, Written};

/// A size in terms of the caller's own `@Nat` fields: a sum of
/// `(coefficient, fields multiplied)` terms. `None` when it mentions a size
/// the caller does not hold.
pub(super) type NamedSize = Option<Vec<(u64, Vec<StrId>)>>;

/// A reference to a global with `@Nat` fields, before the types are pinned.
pub(super) struct SizePending {
    site: Aol<Expr>,
    caller: Option<StrId>,
    callee: StrId,
    sig: Aol<Ty>,
    fields: Vec<(StrId, Type)>,
}

/// The same reference with each field's size in terms of the caller's.
pub(super) struct SizeUse {
    site: Aol<Expr>,
    caller: Option<StrId>,
    callee: StrId,
    sig: Aol<Ty>,
    fields: Vec<(StrId, NamedSize)>,
}

impl<'a> Checker<'a> {
    /// The `@Nat` fields of a signature's `@ctx`, in the order written.
    pub(super) fn nat_fields(&self, sig: Aol<Ty>) -> Vec<StrId> {
        let Some(fields) = self.ast.ctx_params.get(sig) else { return Vec::new() };
        self.ast
            .slice(*fields)
            .iter()
            .filter(|f| self.kind_of_ast(f.ty) == Some(ParamKind::Nat))
            .map(|f| f.name)
            .collect()
    }

    /// Bind the `@Nat` fields of `def`'s signature as locals of its body, each
    /// of type `@Size n` (read as a `@Nat`), in a scope the caller leaves.
    pub(super) fn bind_size_fields(&mut self, def: StrId, sig: Aol<Ty>, body: Aol<Expr>, tvars: &HashMap<StrId, Type>) {
        let fields: Vec<(StrId, Type)> = self.nat_fields(sig).into_iter().filter_map(|f| tvars.get(&f).map(|&t| (f, t))).collect();
        self.enter_scope();
        let head = self.unifier.types.con(StrId::intern(SIZE_OF));
        for &(f, t) in &fields {
            let ty = self.unifier.types.app(head, t);
            self.bind(f, ty);
        }
        // A field that is not a type, size or row is an error already
        // (`check_ctx_fields`); as a local of its type it adds no other.
        let others: Vec<UseField> =
            self.sort_fields(sig).into_iter().filter(|f| self.kind_of_ast(f.ty).is_none() && !self.is_effect_kind(f.ty)).collect();
        for f in others {
            let mut scoped = tvars.clone();
            let ty = self.ty_of_ast(f.ty, &mut scoped);
            self.bind(f.name, ty);
        }
        self.def_sizes.insert(def, (sig, body, fields));
    }

    /// The parameter type `@TypeOf t` of `(t: @Type) ->`, or `@Size n` of
    /// `(n: @Nat) ->`: whether it is the size, and the variable.
    pub(super) fn dependent_param(&self, ty: Type) -> Option<(bool, Type)> {
        let TypeNode::App(head, arg) = self.unifier.types.node(self.unifier.resolve(ty)) else { return None };
        let TypeNode::Con(name) = self.unifier.types.node(self.unifier.resolve(head)) else { return None };
        match name.as_str() {
            ty::TYPE_OF => Some((false, arg)),
            SIZE_OF => Some((true, arg)),
            _ => None,
        }
    }

    /// Check the argument `e` of a `(t: @Type) ->` parameter (`nat` false) or a
    /// `(n: @Nat) ->` one: read as a type or a size, it is what `v` stands for.
    /// A type is erased at run time; a size is also the `@Nat` passed.
    pub(super) fn check_dependent_arg(&mut self, e: Aol<Expr>, nat: bool, v: Type) -> Result<()> {
        let span = self.ast.expr_span(e).unwrap_or(Span::at(0));
        let (t, what) = match nat {
            false => (self.expr_as_type(e)?, "the type argument"),
            true => (self.expr_as_size(e)?, "the size argument"),
        };
        self.unifier.unify(v, t, &format!("in {what}")).map_err(|d| d.fill_span(span))?;
        match nat {
            false => {
                self.type_terms.insert(e);
                Ok(())
            }
            true => self.check(e, self.unifier.types.con(ty::NAT)),
        }
    }

    /// An expression read as a type, by the elaborator of written types
    /// ([`Checker::elaborate`]) as an annotation in the body is. A size is
    /// not a type.
    pub(super) fn expr_as_type(&mut self, e: Aol<Expr>) -> Result<Type> {
        if matches!(self.shape(Written::Expr(e)), Shape::Nat(_) | Shape::SizeAdd(..) | Shape::SizeMul(..)) {
            return Err(expected_type(self.ast.expr_span(e)));
        }
        self.written_reporting(e, false)
    }

    /// The name an expression gives a type or an effect: `T`, `M.T`, or a
    /// lowercase global that computes one.
    pub(super) fn type_name_of_expr(&self, e: Aol<Expr>) -> Option<StrId> {
        match *self.node(e) {
            Expr::Var { name, .. } => Some(name),
            Expr::Variant { module: None, ty: Some(_), tag, fields } if self.ast.slice(fields).is_empty() => Some(tag),
            _ => None,
        }
    }

    /// An expression read as a size: a literal, a size in scope (a `@Nat`
    /// field, parameter or transparent `let`), a `@Nat` constant, or `+` and
    /// `*` of sizes.
    pub(super) fn expr_as_size(&mut self, e: Aol<Expr>) -> Result<Type> {
        self.written_reporting(e, true)
    }

    /// The size `n` of a `@Size n` type, the type of a `@Nat` field in its body.
    pub(super) fn size_of_req(&self, req: Type) -> Option<Type> {
        match self.unifier.types.node(self.unifier.resolve(req)) {
            TypeNode::App(head, size) if self.unifier.types.node(self.unifier.resolve(head)) == TypeNode::Con(StrId::intern(SIZE_OF)) => {
                Some(size)
            }
            _ => None,
        }
    }

    /// Record that the body being checked reads its `@Nat` field `name`.
    pub(super) fn note_size_ref(&mut self, name: StrId) {
        if let Some(def) = self.checking_def {
            self.size_refs.entry(def).or_default().insert(name);
        }
    }

    /// Record a reference at `site` to `callee`, whose signature `sig` was
    /// elaborated with the variables `tvars`, for each of its `@Nat` fields.
    pub(super) fn note_size_use(&mut self, site: Aol<Expr>, callee: StrId, sig: Aol<Ty>, tvars: &HashMap<StrId, Type>) {
        let fields: Vec<(StrId, Type)> = self.nat_fields(sig).into_iter().filter_map(|f| tvars.get(&f).map(|&t| (f, t))).collect();
        if fields.is_empty() {
            return;
        }
        self.size_pending.push(SizePending { site, caller: self.checking_def, callee, sig, fields });
    }

    /// Express each size recorded in the component just checked in terms of its
    /// caller's own `@Nat` fields, now that inference has pinned it.
    pub(super) fn settle_sizes(&mut self) {
        for p in std::mem::take(&mut self.size_pending) {
            let own: Vec<(StrId, TypeNode)> = match p.caller.and_then(|c| self.def_sizes.get(&c)) {
                Some((_, _, fs)) => fs.iter().map(|&(f, t)| (f, self.unifier.types.node(self.unifier.resolve(t)))).collect(),
                None => Vec::new(),
            };
            let mut fields = Vec::with_capacity(p.fields.len());
            for (f, t) in p.fields {
                let t = self.unifier.zonk(t);
                let named: NamedSize = self
                    .unifier
                    .size_poly(t)
                    .into_iter()
                    .map(|(k, vars)| {
                        let names: Option<Vec<StrId>> = vars
                            .into_iter()
                            .map(|v| {
                                let node = self.unifier.types.node(self.unifier.resolve(v));
                                own.iter().find(|(_, n)| *n == node).map(|(name, _)| *name)
                            })
                            .collect();
                        names.map(|ns| (k, ns))
                    })
                    .collect();
                fields.push((f, named));
            }
            self.size_uses.push(SizeUse { site: p.site, caller: p.caller, callee: p.callee, sig: p.sig, fields });
        }
    }

    /// Decide which `@Nat` fields each definition of the module takes at run
    /// time, and build the sizes each reference passes.
    pub(super) fn finish_sizes(&mut self) {
        let mut passed: HashMap<StrId, HashSet<StrId>> = HashMap::new();
        let defs: Vec<(StrId, Aol<Ty>, Aol<Expr>, Vec<StrId>)> =
            self.def_sizes.iter().map(|(d, (sig, body, fs))| (*d, *sig, *body, fs.iter().map(|(f, _)| *f).collect())).collect();
        let by_sig: HashMap<Aol<Ty>, StrId> = defs.iter().map(|(d, sig, _, _)| (*sig, *d)).collect();
        for (d, _, _, fields) in &defs {
            let refs = self.size_refs.get(d).cloned().unwrap_or_default();
            passed.insert(*d, fields.iter().copied().filter(|f| refs.contains(f)).collect());
        }
        loop {
            let mut changed = false;
            for u in &self.size_uses {
                let Some(caller) = u.caller.filter(|c| passed.contains_key(c)) else { continue };
                let wanted: Vec<StrId> = match by_sig.get(&u.sig) {
                    Some(d) => passed[d].iter().copied().collect(),
                    None => self.runtime_sizes.get(&u.sig).cloned().unwrap_or_default(),
                };
                for (f, size) in &u.fields {
                    let Some(terms) = size.as_ref().filter(|_| wanted.contains(f)) else { continue };
                    for name in terms.iter().flat_map(|(_, ns)| ns) {
                        changed |= passed.get_mut(&caller).expect("an own definition").insert(*name);
                    }
                }
            }
            if !changed {
                break;
            }
        }
        for (d, sig, body, fields) in &defs {
            let ordered: Vec<StrId> = fields.iter().copied().filter(|f| passed[d].contains(f)).collect();
            if ordered.is_empty() {
                continue;
            }
            if self.own_instances.iter().any(|(n, _)| n == d) {
                let span = self.ast.ty_span(*sig).unwrap_or(Span::at(0));
                self.errors.push(diag!(
                    Code::TypeMismatch, span, 0,
                    "the instance `{d}` uses its `@ctx` field `{}` at run time", ordered[0];
                    note: "an instance is found by search, which passes no sizes"
                ));
                continue;
            }
            self.runtime_sizes.insert(*sig, ordered.clone());
            self.own_runtime_sizes.push((*sig, ordered.clone()));
            self.size_params.insert(*body, ordered);
        }
        for u in std::mem::take(&mut self.size_uses) {
            let Some(wanted) = self.runtime_sizes.get(&u.sig).cloned() else { continue };
            let mut args = Vec::with_capacity(wanted.len());
            for w in &wanted {
                match u.fields.iter().find(|(f, _)| f == w).and_then(|(_, s)| s.as_ref()) {
                    Some(terms) => args.push(size_term(terms)),
                    None => {
                        let span = self.ast.expr_span(u.site).unwrap_or(Span::at(0));
                        self.errors.push(diag!(
                            Code::TypeMismatch, span, 0,
                            "cannot infer `{w}` of `{}` from the arguments, which it takes at run time", u.callee;
                            note: "a `@Nat` field its body uses is passed at run time: it must solve to literals \
                                   and the caller's own `@ctx` sizes";
                            help: "pass it explicitly, `{} @ctx {{.{w} = ...}}`, or bind the size in the caller's `@ctx`", u.callee
                        ));
                    }
                }
            }
            self.size_args.insert(u.site, args);
        }
    }
}

/// The run-time value of a size: its terms added, each a coefficient times
/// the fields it multiplies.
fn size_term(terms: &[(u64, Vec<StrId>)]) -> CtxVal {
    let app = |f: &str, a: CtxVal, b: CtxVal| {
        CtxVal::App(Box::new(CtxVal::App(Box::new(CtxVal::Bare(StrId::intern(f))), Box::new(a))), Box::new(b))
    };
    let mut sum: Option<CtxVal> = None;
    for (k, names) in terms {
        let mut term = (*k != 1 || names.is_empty()).then_some(CtxVal::Nat(*k));
        for n in names {
            term = Some(match term {
                None => CtxVal::Bare(*n),
                Some(t) => app("@imul", t, CtxVal::Bare(*n)),
            });
        }
        let term = term.expect("a term has a coefficient or a field");
        sum = Some(match sum {
            None => term,
            Some(s) => app("@iadd", s, term),
        });
    }
    sum.unwrap_or(CtxVal::Nat(0))
}

/// An expression where a type is expected that reads as none.
fn expected_type(span: Option<Span>) -> Diagnostic {
    diag!(Code::TypeMismatch, span.unwrap_or(Span::at(0)), 0, "expected a type, as in `@Int` or `List @Int`")
}
