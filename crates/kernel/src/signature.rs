//! The signature: every global the kernel has checked, in declaration order.
//!
//! A global has a name, its level parameters, its type (a closed term over
//! those parameters) and what it is: a transparent definition, an axiom with
//! no body, or one of the three globals an inductive declaration introduces
//! (the type former, its constructors and its recursor). Later globals may
//! refer to earlier ones only, so the signature is append-only and a
//! [`GlobalId`] never dangles.
//!
//! A global's terms keep their proofs, so [`Signature::axioms`] reads the
//! axioms it rests on off its terms.
//!
//! Entry point: [`Signature`].

use std::collections::{BTreeSet, HashMap};
use std::rc::Rc;

use crate::level::Level;
use crate::term::{globals, renumber, Name, Term};

/// A global's position in the signature.
pub type GlobalId = u32;

/// An inductive declaration's position in the signature.
pub type DataId = u32;

#[derive(Clone, Debug)]
pub enum GlobalKind {
    /// Unfolds to its body during evaluation.
    Definition(Rc<Term>),
    /// A postulate: a neutral constant of its type.
    Axiom,
    /// An inductive type former, applied to its parameters.
    Data(DataId),
    /// The `index`th constructor of an inductive type.
    Constructor(DataId, usize),
    /// The recursor (dependent eliminator) of an inductive type.
    Recursor(DataId),
    /// The projection out of `D a ~ D a'` for field `.2` of constructor
    /// `.1`: a proof, so its value is the irrelevant witness.
    /// See Rule [Data-Eq-Projection].
    Projection(DataId, usize, usize),
}

/// An inductive type `D (params) : @Type level` and its constructors. Its
/// level parameters are the type former's; the recursor adds one more, the
/// sort of its motive.
#[derive(Clone, Debug)]
pub struct DataDecl {
    pub global: GlobalId,
    /// The parameters, then the indices: an indexed family is stored forded,
    /// with its indices as parameters that constructors do not fix.
    /// See Note [Indexed families are forded].
    pub params: Vec<Param>,
    /// How many of `params` are uniform parameters; the rest are indices.
    pub uniform: usize,
    pub level: Level,
    pub constructors: Vec<ConstructorDecl>,
    /// The projections, constructor by constructor and field by field: none
    /// for a type without parameters. See Rule [Data-Eq-Projection].
    /// See Note [A declaration's globals are contiguous].
    pub projections: Vec<GlobalId>,
    pub recursor: GlobalId,
}

/// A parameter or a constructor field: its type is a term over the
/// parameters and fields before it, and `level` is its sort.
#[derive(Clone, Debug)]
pub struct Param {
    pub name: Name,
    pub ty: Rc<Term>,
    pub level: Level,
}

#[derive(Clone, Debug)]
pub struct ConstructorDecl {
    pub name: Name,
    pub global: GlobalId,
    /// The forded fields, over all of `params`: the fields as written, then
    /// one equality per index.
    pub fields: Vec<Param>,
    /// Which fields are `D` itself, at the uniform parameters.
    pub recursive: Vec<bool>,
    /// The fields as written, over the uniform parameters only.
    pub surface: Vec<Param>,
    /// The indices of the constructor's result, over the uniform parameters
    /// and `surface`.
    pub indices: Vec<Rc<Term>>,
}

#[derive(Clone, Debug)]
pub struct Global {
    pub name: Name,
    pub level_params: Vec<Name>,
    pub ty: Rc<Term>,
    pub kind: GlobalKind,
}

/// The prelude's globals the checker builds terms from, and the printer
/// reads back: the booleans a type may be, `if`, the naturals a numeral is,
/// the integers, and the functions on `@Nat` that compute on numerals.
/// See [`crate::prelude`].
#[derive(Clone, Copy, Debug)]
pub struct Builtins {
    pub bool: GlobalId,
    pub true_ctor: GlobalId,
    pub false_ctor: GlobalId,
    pub true_value: GlobalId,
    pub bool_if: GlobalId,
    pub nat: GlobalId,
    pub zero: GlobalId,
    pub succ: GlobalId,
    pub int: GlobalId,
    pub int_pos: GlobalId,
    pub int_neg_succ: GlobalId,
    pub arithmetic: [(GlobalId, Arithmetic); 7],
}

impl Builtins {
    /// What global `id` computes on numerals, if it is one that does.
    pub fn arithmetic(&self, id: GlobalId) -> Option<Arithmetic> {
        self.arithmetic.iter().find(|(g, _)| *g == id).map(|(_, op)| *op)
    }

    /// The same builtins in a signature where global `g` is `f(g)`.
    fn renumbered(&self, f: &dyn Fn(GlobalId) -> GlobalId) -> Builtins {
        Builtins {
            bool: f(self.bool),
            true_ctor: f(self.true_ctor),
            false_ctor: f(self.false_ctor),
            true_value: f(self.true_value),
            bool_if: f(self.bool_if),
            nat: f(self.nat),
            zero: f(self.zero),
            succ: f(self.succ),
            int: f(self.int),
            int_pos: f(self.int_pos),
            int_neg_succ: f(self.int_neg_succ),
            arithmetic: self.arithmetic.map(|(g, op)| (f(g), op)),
        }
    }
}

/// A prelude function on `@Nat` that numeral arguments compute directly.
/// See Rule [Nat-Literal].
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Arithmetic {
    Add,
    Sub,
    Mul,
    Lt,
    Eq,
    Pred,
    IsZero,
}

/// What an arithmetic global gives on numerals.
pub enum Computed {
    Nat(u64),
    Bool(bool),
}

impl Arithmetic {
    /// How many arguments it takes.
    pub fn arity(self) -> usize {
        match self {
            Arithmetic::Pred | Arithmetic::IsZero => 1,
            _ => 2,
        }
    }

    /// Its value on the numerals `args`, or `None` when the result does not
    /// fit a numeral. `-` stops at `0`, as the prelude's definition does.
    pub fn compute(self, args: &[u64]) -> Option<Computed> {
        Some(match (self, args) {
            (Arithmetic::Add, [a, b]) => Computed::Nat(a.checked_add(*b)?),
            (Arithmetic::Sub, [a, b]) => Computed::Nat(a.saturating_sub(*b)),
            (Arithmetic::Mul, [a, b]) => Computed::Nat(a.checked_mul(*b)?),
            (Arithmetic::Lt, [a, b]) => Computed::Bool(a < b),
            (Arithmetic::Eq, [a, b]) => Computed::Bool(a == b),
            (Arithmetic::Pred, [a]) => Computed::Nat(a.saturating_sub(1)),
            (Arithmetic::IsZero, [a]) => Computed::Bool(*a == 0),
            _ => unreachable!("an arithmetic global applied to the wrong number of numerals"),
        })
    }
}

#[derive(Default)]
pub struct Signature {
    globals: Vec<Global>,
    by_name: HashMap<Name, GlobalId>,
    datas: Vec<DataDecl>,
    /// How many globals, from the first, are the prelude's. A script's
    /// global may take a prelude global's name, which then names it.
    prelude: GlobalId,
    builtins: Option<Builtins>,
}

impl Signature {
    pub fn new() -> Signature {
        Signature::default()
    }

    pub fn global(&self, id: GlobalId) -> &Global {
        self.globals.get(id as usize).unwrap_or_else(|| panic!("global #{id} is not in the signature"))
    }

    pub fn lookup(&self, name: &str) -> Option<GlobalId> {
        self.by_name.get(name).copied()
    }

    /// How many globals there are; their ids are `0..len`.
    pub fn len(&self) -> usize {
        self.globals.len()
    }

    pub fn is_empty(&self) -> bool {
        self.globals.is_empty()
    }

    /// The names of the script's own globals, in declaration order.
    pub fn names(&self) -> impl Iterator<Item = &str> {
        self.globals[self.prelude as usize..].iter().map(|g| &*g.name)
    }

    /// Every name a script may refer to, the prelude's included.
    pub fn visible_names(&self) -> impl Iterator<Item = &str> {
        self.by_name.keys().map(|n| &**n)
    }

    /// Whether global `id` is the prelude's.
    pub fn is_prelude(&self, id: GlobalId) -> bool {
        id < self.prelude
    }

    /// The globals so far are the prelude, with `builtins` among them.
    pub(crate) fn seal_prelude(&mut self, builtins: Builtins) {
        self.prelude = self.next_global();
        self.builtins = Some(builtins);
    }

    pub fn builtins(&self) -> Option<Builtins> {
        self.builtins
    }

    /// Give global `id` the name `name`, which no global has.
    pub(crate) fn rename(&mut self, id: GlobalId, name: &str) {
        assert!(!self.by_name.contains_key(name), "global `{name}` is declared twice");
        let global = &mut self.globals[id as usize];
        self.by_name.remove(&global.name);
        global.name = name.into();
        self.by_name.insert(global.name.clone(), id);
    }

    pub fn data(&self, id: DataId) -> &DataDecl {
        &self.datas[id as usize]
    }

    pub fn data_mut(&mut self, id: DataId) -> &mut DataDecl {
        &mut self.datas[id as usize]
    }

    pub fn add_data(&mut self, decl: DataDecl) -> DataId {
        self.datas.push(decl);
        (self.datas.len() - 1) as DataId
    }

    /// The id the next [`Signature::add`] returns.
    pub fn next_global(&self) -> GlobalId {
        self.globals.len() as GlobalId
    }

    /// A global to tamper with, for tests that a re-check notices.
    #[cfg(test)]
    pub(crate) fn global_mut(&mut self, id: GlobalId) -> &mut Global {
        &mut self.globals[id as usize]
    }

    pub fn add(&mut self, global: Global) -> GlobalId {
        let taken = self.by_name.get(&global.name).is_some_and(|id| !self.is_prelude(*id));
        assert!(!taken, "global `{}` is declared twice", global.name);
        let id = self.globals.len() as GlobalId;
        self.by_name.insert(global.name.clone(), id);
        self.globals.push(global);
        id
    }

    /// The globals global `id`'s type and body name, for a type former the
    /// other globals its declaration gives, and for those the type former.
    /// See Note [Axioms are read off the terms].
    fn uses(&self, id: GlobalId) -> BTreeSet<GlobalId> {
        let global = &self.globals[id as usize];
        let mut out = BTreeSet::new();
        globals(&global.ty, &mut out);
        match &global.kind {
            GlobalKind::Definition(body) => globals(body, &mut out),
            GlobalKind::Data(data) => out.extend(self.declared_with(*data)),
            GlobalKind::Constructor(data, _) | GlobalKind::Recursor(data) | GlobalKind::Projection(data, _, _) => {
                out.insert(self.datas[*data as usize].global);
            }
            GlobalKind::Axiom => {}
        }
        out
    }

    /// The constructors, projections and recursor of inductive type `data`,
    /// as its declaration records them: those added so far, while the
    /// elaborator is still adding them.
    fn declared_with(&self, data: DataId) -> impl Iterator<Item = GlobalId> + '_ {
        let decl = &self.datas[data as usize];
        let constructors = decl.constructors.iter().map(|c| c.global);
        let all = constructors.chain(decl.projections.iter().copied()).chain(std::iter::once(decl.recursor));
        all.filter(|g| (*g as usize) < self.globals.len())
    }


    /// The globals global `id` rests on, itself included.
    pub fn rests_on(&self, id: GlobalId) -> BTreeSet<GlobalId> {
        let mut seen = BTreeSet::new();
        let mut stack = vec![id];
        while let Some(g) = stack.pop() {
            if seen.insert(g) {
                stack.extend(self.uses(g));
            }
        }
        seen
    }

    // Algorithm [Transitive axioms]
    /// The axioms global `id` depends on, itself included when it is one,
    /// in declaration order.
    pub fn axioms(&self, id: GlobalId) -> Vec<GlobalId> {
        self.rests_on(id).into_iter().filter(|g| matches!(self.globals[*g as usize].kind, GlobalKind::Axiom)).collect()
    }

    /// The signature cut down to the globals global `id` rests on, and
    /// `id`'s number in it. Its axioms are the ones [`Signature::axioms`]
    /// reports for `id`.
    /// See Note [The axiom report is complete].
    pub fn rests_on_signature(&self, id: GlobalId) -> (Signature, GlobalId) {
        let keep = self.rests_on(id);
        let at = keep.range(..id).count() as GlobalId;
        (self.restrict(&keep), at)
    }

    /// The signature of the globals in `keep` alone, in their order and
    /// numbered from 0, with the declarations whose type formers are kept.
    /// A term that names a global left out names `GlobalId::MAX`, which is
    /// no global, and a builtin left out is `GlobalId::MAX` too.
    pub(crate) fn restrict(&self, keep: &BTreeSet<GlobalId>) -> Signature {
        let mut ids = vec![GlobalId::MAX; self.globals.len()];
        for (new, old) in keep.iter().enumerate() {
            ids[*old as usize] = new as GlobalId;
        }
        let mut data_ids = vec![DataId::MAX; self.datas.len()];
        let mut kept_datas = Vec::new();
        for (old, decl) in self.datas.iter().enumerate().filter(|(_, d)| keep.contains(&d.global)) {
            data_ids[old] = kept_datas.len() as DataId;
            kept_datas.push(decl);
        }
        let global = |g: GlobalId| ids.get(g as usize).copied().unwrap_or(GlobalId::MAX);
        let term = |t: &Rc<Term>| Rc::new(renumber(t, &global));
        let param = |p: &Param| Param {
            name: p.name.clone(),
            ty: term(&p.ty),
            level: p.level.clone(),
        };
        let data = |d: DataId| {
            let new = data_ids[d as usize];
            assert!(new != DataId::MAX, "a global is kept without its declaration's type former");
            new
        };
        let mut out = Signature {
            prelude: keep.range(..self.prelude).count() as GlobalId,
            builtins: self.builtins.map(|b| b.renumbered(&global)),
            ..Signature::default()
        };
        for &old in keep {
            let g = &self.globals[old as usize];
            let kind = match &g.kind {
                GlobalKind::Definition(body) => GlobalKind::Definition(term(body)),
                GlobalKind::Axiom => GlobalKind::Axiom,
                GlobalKind::Data(d) => GlobalKind::Data(data(*d)),
                GlobalKind::Constructor(d, index) => GlobalKind::Constructor(data(*d), *index),
                GlobalKind::Recursor(d) => GlobalKind::Recursor(data(*d)),
                GlobalKind::Projection(d, index, field) => GlobalKind::Projection(data(*d), *index, *field),
            };
            out.by_name.insert(g.name.clone(), out.next_global());
            out.globals.push(Global {
                name: g.name.clone(),
                level_params: g.level_params.clone(),
                ty: term(&g.ty),
                kind,
            });
        }
        for decl in kept_datas {
            let constructors = decl.constructors.iter().map(|c| ConstructorDecl {
                name: c.name.clone(),
                global: global(c.global),
                fields: c.fields.iter().map(param).collect(),
                recursive: c.recursive.clone(),
                surface: c.surface.iter().map(param).collect(),
                indices: c.indices.iter().map(term).collect(),
            });
            out.datas.push(DataDecl {
                global: global(decl.global),
                params: decl.params.iter().map(param).collect(),
                uniform: decl.uniform,
                level: decl.level.clone(),
                constructors: constructors.collect(),
                projections: decl.projections.iter().map(|g| global(*g)).collect(),
                recursor: global(decl.recursor),
            });
        }
        out
    }
}

// Note [Axioms are read off the terms]
//
// A global rests on the globals its type and body name, and on the ones
// those rest on. Proofs stay in the terms (they are only never evaluated), so
// a global named only inside a proof still counts, which is the point: a
// theorem proved from a postulate rests on it.
//
// An inductive declaration is one declaration, as in Lean's `#print axioms`:
// its type former rests on its constructors, projections and recursor, and
// each of those rests on the type former its kind belongs to (and names it
// in its type besides), so all of them rest on the same globals. The constructors carry the field types, so a type whose field is
// a postulate rests on it, and so does every global that names the type.
// See Note [Proofs evaluate to an irrelevant witness].

// Note [The axiom report is complete]
//
// The claim: global `g` holds in a signature whose axioms are exactly the
// ones `g` rests on, so the axioms `Signature::axioms` reports for `g` are
// all the axioms a derivation of `g` needs. The derivation meant is the
// re-check, which checks `g` from its stored terms alone (see the `recheck`
// module). The elaborator reads more (it resolves names and suggests
// spellings), but what it builds is what is re-checked.
//
// How it is shown. `recheck` cuts the signature down to the globals `g`
// rests on (`Signature::rests_on_signature`): those globals alone, in their
// order and numbered from 0, with the declarations whose type formers are
// among them, and every term renumbered to match. It then re-checks `g` in
// that signature. Nothing else is in it, so there is nothing else for the
// re-check to read, by id, by name or by any route a future change adds;
// a term that named a global left out would name no global at all and fail.
// So every script the tests re-check, and every one `ares check` hands to
// the kernel, shows the claim for each of its globals directly.
//
// The cut is closed: every global in it rests only on globals in it, and a
// kept constructor, projection or recursor keeps its type former, since it
// names it. So the cut is a signature of its own, and the whole signature
// extends it with globals no term of `g`'s derivation names, which the
// derivation cannot meet: `g` holds there too, and is not checked again.
//
// One check stays on the whole signature: a declaration's record of its
// globals must run without a gap, and a global between them that the
// declaration does not rest on would be cut away.
// See Note [A declaration's globals are contiguous].
// See Algorithm [Transitive axioms].

// Note [A declaration's globals are contiguous]
//
// An inductive declaration gives a type former, its constructors, its
// projections and its recursor, added in that order with nothing between
// them. Its `DataDecl` records each of their ids, so the axiom report reads
// them off the declaration instead of off the globals around the type former
// (See Note [Axioms are read off the terms]), and `recheck` checks the
// record: every recorded id names a global of this declaration of the kind
// and position it is recorded as, the ids run on from the type former
// without a gap, and a projection the declaration does not record is
// rejected. So a declaration cannot leave out one of its globals, claim
// another's, or have one added after a later global.
