//! The kernel's prelude: the booleans and naturals of CORE, as globals the
//! kernel checks before every script.
//!
//! The frontend's #539 programs state propositions as booleans,
//! `(n: @Nat) -> n < 10 -> ...`, and the kernel reads them the same way: a
//! `Bool` where a type is expected is `b ~ true` (See Rule [Bool-Reflection]).
//! For that it needs a `Bool`, a `true`, and comparisons that compute, so the
//! prelude defines them as ordinary globals: `Bool` and `@Nat` are inductive
//! types, and `not`, `&&`, `||`, `+`, `*`, `<` and `==` are defined by their
//! recursors, so they compute by Data-Iota and nothing else. As in CORE,
//! every other comparison is `<` or `==` read one way or the other (`a > b`
//! is `b < a`, `a <= b` is `not (b < a)`), so a lemma about `<` or `==`
//! holds of them by computation.
//!
//! `@Nat` is the unary naturals `@Nat.Zero` and `@Nat.Succ`, with the
//! recursor `@Nat.elim`, and a numeral is its constructor chain: `3` is
//! `@Nat.Succ (@Nat.Succ (@Nat.Succ @Nat.Zero))`. They are unbounded, where
//! the frontend's sizes are modular, and `+` recurses on its right side, so
//! `n + 0 ~ n` holds by computation but `0 + n ~ n` needs induction. A
//! script writes a successor `n + 1`, or `.Succ.{ n }` when no constructor
//! of its own is tagged `Succ`. `<` and `==` recurse on their left side and
//! step the right one back with `@Nat.pred`, testing it with
//! `@Nat.is_zero`: the recursor computes every induction hypothesis, used or
//! not, so a case analysis nested inside the recursion would take time
//! exponential in the numbers compared.
//!
//! A script's global may take a prelude global's name, and the name is then
//! the script's (every kernel script that defines its own `Nat` or `Bool`
//! still checks). The prelude's `@`-spelled globals cannot be taken: a
//! script cannot declare an `@` name.
//!
//! Entry point: [`load`].

use std::rc::Rc;

use crate::level::Level;
use crate::signature::{Builtins, GlobalId, Signature};
use crate::syntax::{parse_script, Item};
use crate::term::Term;

/// The prelude's source. `Nat` is renamed `@Nat` once it is checked, since
/// a module cannot declare an `@` name.
pub const SOURCE: &str = r"$ @mod PRELUDE
$ Bool : @Type 1 = @union False: {}, True: {}
$ true : Bool = Bool.True
$ false : Bool = Bool.False
$ not : Bool -> Bool = \b => Bool.elim @ctx {.m = 1} (\_ => Bool) true false b
$ (&&) : Bool -> Bool -> Bool = \a b => Bool.elim @ctx {.m = 1} (\_ => Bool) false b a
$ (||) : Bool -> Bool -> Bool = \a b => Bool.elim @ctx {.m = 1} (\_ => Bool) b true a
$ Nat : @Type 1 = @union Zero: {}, Succ: Nat
$ (+) : Nat -> Nat -> Nat = \m n => Nat.elim @ctx {.m = 1} (\_ => Nat) m (\_ r => Nat.Succ.{ r }) n
$ (*) : Nat -> Nat -> Nat = \m n => Nat.elim @ctx {.m = 1} (\_ => Nat) Nat.Zero (\_ r => r + m) n
$ is_zero : Nat -> Bool = \n => Nat.elim @ctx {.m = 1} (\_ => Bool) true (\_ _ => false) n
$ pred : Nat -> Nat = \n => Nat.elim @ctx {.m = 1} (\_ => Nat) Nat.Zero (\k _ => k) n
$ (<) : Nat -> Nat -> Bool = \m =>
    Nat.elim @ctx {.m = 1} (\_ => Nat -> Bool) (\n => not (is_zero n)) (\_ r n => not (is_zero n) && r (pred n)) m
$ (==) : Nat -> Nat -> Bool = \m =>
    Nat.elim @ctx {.m = 1} (\_ => Nat -> Bool) is_zero (\_ r n => not (is_zero n) && r (pred n)) m
$ (>) : Nat -> Nat -> Bool = \a b => b < a
$ (<=) : Nat -> Nat -> Bool = \a b => not (b < a)
$ (>=) : Nat -> Nat -> Bool = \a b => not (a < b)
$ (!=) : Nat -> Nat -> Bool = \a b => not (a == b)
";

/// The globals `Nat` declares and its helpers, renamed to their `@`
/// spelling.
const RENAMED: [(&str, &str); 6] = [
    ("Nat", "@Nat"),
    ("Nat.Zero", "@Nat.Zero"),
    ("Nat.Succ", "@Nat.Succ"),
    ("Nat.elim", "@Nat.elim"),
    ("is_zero", "@Nat.is_zero"),
    ("pred", "@Nat.pred"),
];

/// Check the prelude into `sig`, with `check_item` checking one item, and
/// seal it. The prelude is fixed, so a failure is a bug in the kernel.
pub(crate) fn load(sig: &mut Signature, mut check_item: impl FnMut(&mut Signature, &Item) -> utilities::Result<()>) {
    let items = parse_script(SOURCE).unwrap_or_else(|e| panic!("the prelude does not parse:\n{}", e.render(SOURCE, "PRELUDE")));
    for item in &items {
        check_item(sig, item).unwrap_or_else(|e| panic!("the prelude does not check:\n{}", e.render(SOURCE, "PRELUDE")));
    }
    for (from, to) in RENAMED {
        let id = sig.lookup(from).expect("the prelude declares it");
        sig.rename(id, to);
    }
    let id = |name: &str| -> GlobalId { sig.lookup(name).expect("the prelude declares it") };
    let builtins = Builtins {
        bool: id("Bool"),
        true_ctor: id("Bool.True"),
        true_value: id("true"),
        nat: id("@Nat"),
        zero: id("@Nat.Zero"),
        succ: id("@Nat.Succ"),
    };
    sig.seal_prelude(builtins);
}

/// The numeral `n`: `@Nat.Succ` applied `n` times to `@Nat.Zero`.
pub(crate) fn numeral(builtins: Builtins, n: u64) -> Term {
    let none: Rc<[Level]> = Rc::new([]);
    (0..n).fold(Term::Global(builtins.zero, none.clone()), |acc, _| Term::app(Term::Global(builtins.succ, none.clone()), acc))
}
