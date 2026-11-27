//! What each `@ctx` field of a signature is (#590).
//!
//! The parser files a signature's `@ctx` fields by their place alone: the
//! levels `u: @l` in [`Ast::level_params`], every other field in
//! [`Ast::ctx_params`]. What a field is follows from its type, read with the
//! type-level globals at its head unfolded, since types are terms (#535):
//!
//! - a sort, `@Type`, `@Nat`, `@Row`, `@Effect` or `@Class`, or a global that
//!   stands for one (`$ Ty : @Type 2 = @Type`, then `@ctx {t: Ty}`): the field
//!   binds a variable unification solves;
//! - any other type: an instance field, found by instance search, or a
//!   proposition field (#540), proved at each use. These travel as the
//!   definition's one leading context parameter, the field's type alone or the
//!   tuple of several, which its body binds by the fields' names.
//!
//! Entry points: [`Checker::sort_fields`], [`Checker::use_fields`],
//! [`Checker::sig_and_ctx`], [`Checker::bind_use_fields`].

use super::*;

/// The sorts: a `@ctx` field of one of these types binds a variable.
const SORTS: [&str; 5] = [ty::UNIVERSE, ty::NAT, "@Row", "@Effect", "@Class"];

/// How many type-level globals reading a field's sort unfolds: one that
/// unfolds to itself is reported where it is elaborated.
const UNFOLD_LIMIT: usize = 64;

impl<'a> Checker<'a> {
    /// The sort `ty` is, read through the type-level globals at the head of
    /// its spine, or `None` for a type that is no sort.
    pub(super) fn sort_of_ast(&self, ty: Aol<Ty>) -> Option<&'static str> {
        let mut cur = ty;
        for _ in 0..UNFOLD_LIMIT {
            let mut head = cur;
            while let Ty::App(h, _) = self.tnode(head) {
                head = *h;
            }
            let name = match self.tnode(head) {
                Ty::Con { name, .. } | Ty::Var(name) => *name,
                _ => return None,
            };
            if let Some(sort) = SORTS.iter().find(|s| **s == name.as_str()) {
                return Some(sort);
            }
            cur = self.type_global_body(name)?;
        }
        None
    }

    /// The type a type-level global `name` unfolds to: this module's own
    /// first, registered or not yet, then one an import brought in.
    fn type_global_body(&self, name: StrId) -> Option<Aol<Ty>> {
        self.own_alias_bodies.get(&name).copied().or_else(|| self.aliases.get(&name).map(|(_, body)| *body))
    }

    /// Note this module's type-level globals, so a field's sort reads through
    /// one wherever it is declared.
    pub(super) fn note_type_globals(&mut self, program: &Program) {
        for item in self.ast.slice(program.items) {
            if let Item::Alias { name, ty, .. } = item {
                self.own_alias_bodies.insert(*name, *ty);
            }
        }
    }

    /// The `@ctx` fields of `sig` that unification solves, those whose type
    /// is a sort, in the order written.
    pub(super) fn sort_fields(&self, sig: Aol<Ty>) -> Vec<UseField> {
        self.ctx_fields(sig).filter(|f| self.sort_of_ast(f.ty).is_some()).collect()
    }

    /// The instance fields of `sig`, the `@ctx` fields whose type is no sort,
    /// in the order written: the parts of its context parameter.
    pub(super) fn use_fields(&self, sig: Aol<Ty>) -> Vec<UseField> {
        self.ctx_fields(sig).filter(|f| self.sort_of_ast(f.ty).is_none()).collect()
    }

    /// Whether `sig` declares an instance field, so the definition takes a
    /// context parameter.
    pub(super) fn has_uses(&self, sig: Aol<Ty>) -> bool {
        self.ctx_fields(sig).any(|f| self.sort_of_ast(f.ty).is_none())
    }

    fn ctx_fields(&self, sig: Aol<Ty>) -> impl Iterator<Item = UseField> + '_ {
        self.ast.ctx_params.get(sig).into_iter().flat_map(|fs| self.ast.slice(*fs).iter().copied())
    }

    /// The written types `sig` is elaborated from: its instance fields' and
    /// its own, for the walks that look for variables in a signature.
    pub(super) fn sig_roots(&self, sig: Aol<Ty>) -> Vec<Aol<Ty>> {
        self.use_fields(sig).iter().map(|f| f.ty).chain(std::iter::once(sig)).collect()
    }

    /// `sig` elaborated under `tvars`: its context parameter, the type of its
    /// one instance field or the tuple of several (`None` without any), and
    /// the type callers see. The context comes first, as it is written.
    pub(super) fn sig_and_ctx(&mut self, sig: Aol<Ty>, tvars: &mut HashMap<StrId, Type>) -> (Option<Type>, Type) {
        let fields = self.use_fields(sig);
        let ctx = match fields.as_slice() {
            [] => None,
            [one] => Some(self.ty_of_ast(one.ty, tvars)),
            many => {
                let parts: Vec<Type> = many.iter().map(|f| self.ty_of_ast(f.ty, tvars)).collect();
                Some(self.unifier.types.tuple(parts))
            }
        };
        let exposed = self.ty_of_ast(sig, tvars);
        (ctx, exposed)
    }

    /// The type a definition's body sees: its context parameter, if any,
    /// ahead of the type its callers see.
    pub(super) fn with_ctx(&mut self, ctx: Option<Type>, exposed: Type) -> Type {
        match ctx {
            Some(ctx) => {
                let pure = self.unifier.types.row_empty();
                self.unifier.types.arrow_eff(ctx, exposed, pure)
            }
            None => exposed,
        }
    }

    /// Bind the instance fields of `def`'s signature `sig` as locals of its
    /// body, each of its part of the context parameter `ctx`, in the scope
    /// open for the body, and record them for lowering, which binds them
    /// ahead of the body's own parameters.
    pub(super) fn bind_use_fields(&mut self, sig: Aol<Ty>, body: Aol<Expr>, ctx: Type) {
        let fields = self.use_fields(sig);
        let parts = match fields.as_slice() {
            [_] => vec![ctx],
            _ => match self.unifier.types.node(ctx) {
                TypeNode::Tuple(items) => self.unifier.types.items(items).to_vec(),
                _ => unreachable!("a context of several fields is their tuple"),
            },
        };
        for (f, part) in fields.iter().zip(parts) {
            self.bind(f.name, part);
        }
        self.use_params.insert(body, fields.iter().map(|f| f.name).collect());
    }
}
