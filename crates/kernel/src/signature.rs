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

use std::cell::RefCell;
use std::collections::{BTreeSet, HashMap};
use std::rc::Rc;

use crate::level::Level;
use crate::term::{globals, Name, Term};

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
    /// The globals read since [`Signature::recording`] started, if it has.
    consulted: RefCell<Option<BTreeSet<GlobalId>>>,
}

impl Signature {
    pub fn new() -> Signature {
        Signature::default()
    }

    pub fn global(&self, id: GlobalId) -> &Global {
        self.consult(id);
        &self.globals[id as usize]
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

    /// An inductive declaration; reading it reads its type former.
    pub fn data(&self, id: DataId) -> &DataDecl {
        let decl = &self.datas[id as usize];
        self.consult(decl.global);
        decl
    }

    fn consult(&self, id: GlobalId) {
        if let Some(seen) = self.consulted.borrow_mut().as_mut() {
            seen.insert(id);
        }
    }

    /// Run `f`, and return with its result every global it read through
    /// [`Signature::global`] or [`Signature::data`].
    /// See Note [The axiom report is complete].
    pub(crate) fn recording<R>(&self, f: impl FnOnce() -> R) -> (R, BTreeSet<GlobalId>) {
        let previous = self.consulted.replace(Some(BTreeSet::new()));
        assert!(previous.is_none(), "recordings of the globals read do not nest");
        let result = f();
        let seen = self.consulted.take().expect("the recording is still on");
        (result, seen)
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

    /// The globals global `id`'s type and body name, and for a type former
    /// the other globals its declaration gives.
    /// See Note [Axioms are read off the terms].
    fn uses(&self, id: GlobalId) -> BTreeSet<GlobalId> {
        let global = &self.globals[id as usize];
        let mut out = BTreeSet::new();
        globals(&global.ty, &mut out);
        match &global.kind {
            GlobalKind::Definition(body) => globals(body, &mut out),
            GlobalKind::Data(data) => out.extend(self.declared_with(*data)),
            _ => {}
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
// each of those names the type former, so all of them rest on the same
// globals. The constructors carry the field types, so a type whose field is
// a postulate rests on it, and so does every global that names the type.
// See Note [Proofs evaluate to an irrelevant witness].

// Note [The axiom report is complete]
//
// The claim: every global a derivation of global `g` reads is one `g` rests
// on, so the axioms `g` rests on are all the axioms its derivation uses. The
// derivation meant is the re-check, which checks `g` from its stored terms
// alone (see the `recheck` module). The elaborator reads more (it resolves
// names and suggests spellings), but what it builds is what is re-checked.
//
// Why it holds. Inside the kernel a global is a `GlobalId`, and an id comes
// from one of three places:
//
// 1. a `Term::Global` in a term. The re-check of `g` starts from `g`'s type
//    and body, whose globals `uses` reads; every other term it meets is the
//    type or body of a global it read (evaluation unfolds a definition,
//    inference reads a type), or is built from values of those;
// 2. an inductive declaration read through `Signature::data`: its type
//    former, constructors, recursor and the types of its fields, which the
//    computation rules (Data-Iota, Eq-Ctor, Cast-Ctor) and the read-back of
//    a value use. Reading a declaration reads its type former, which rests
//    on all of them (See Note [Axioms are read off the terms]);
// 3. `Signature::lookup`, `Signature::names` and `Signature::visible_names`,
//    which resolve a name. Only
//    the elaborator calls them, never the re-check or the evaluator,
//    conversion and computation rules it shares.
//
// A computation rule that needs a proof passes the irrelevant witness. The
// proof it stands for is built from proofs already in the derivation and
// from the projections of a declaration already read, so it names no global
// the derivation did not read.
//
// How it is kept. `recheck` records every global it reads through
// `Signature::global` and `Signature::data` while it checks each global,
// and fails when one of them is not a global it rests on. So every script the
// tests re-check, and every one `ares check` hands to the kernel, checks the
// claim on that script. `tests/axioms.rs` checks that the modules the
// re-check runs never resolve a name, which is the third case.
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
