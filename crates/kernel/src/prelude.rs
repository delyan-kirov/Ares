//! The kernel's prelude: the booleans, naturals and integers of CORE, as
//! globals the kernel checks before every script.
//!
//! The frontend's #539 programs state propositions as booleans,
//! `(n: @Nat) -> n < 10 -> ...`, and the kernel reads them the same way: a
//! `Bool` where a type is expected is `b ~ true` (See Rule [Bool-Reflection]).
//! For that it needs a `Bool`, a `true`, and comparisons that compute, so the
//! prelude defines them as ordinary globals: `Bool`, `@Nat` and `@Int` are
//! inductive types, and `not`, `&&`, `||`, `+`, `-`, `*`, `<` and `==` are
//! defined by their recursors, so they compute by Data-Iota (and on
//! numerals by Nat-Literal, which agrees with it). As in CORE, every other
//! comparison is `<` or `==` read one way or the other (`a > b` is `b < a`,
//! `a <= b` is `not (b < a)`), so a lemma about `<` or `==` holds of them by
//! computation.
//!
//! `@Nat` is the unary naturals `@Nat.Zero` and `@Nat.Succ`, with the
//! recursor `@Nat.elim`, and a numeral stands for its constructor chain: `3`
//! is `@Nat.Succ.{ @Nat.Succ.{ @Nat.Succ.{ @Nat.Zero } } }`. A numeral is
//! kept as a number, and `+`, `-`, `*`, `<`, `==`, `@Nat.pred` and
//! `@Nat.is_zero` compute on two numbers by machine arithmetic, so a
//! numeral may be large (See Rule [Nat-Literal]). They are unbounded,
//! where the frontend's sizes are modular, `-` stops at `0`, and `+`
//! recurses on its right side, so `n + 0 ~ n` holds by computation but
//! `0 + n ~ n` needs induction. A script writes a successor `n + 1`, or
//! `@Nat.Succ.{ n }`. `<` and `==` recurse on their left side and step the
//! right one back with `@Nat.pred`, testing it with `@Nat.is_zero`: the
//! recursor computes every induction hypothesis, used or not, so a case
//! analysis nested inside the recursion would take time exponential in the
//! numbers compared.
//!
//! `@Bool.if` is `if c => a else b`, at the type of its branches. `@Int` is
//! the integers as Lean has them: `@Int.Pos.{ n }` is `n` and
//! `@Int.NegSucc.{ n }` is `-(n + 1)`, so each integer has one form. Its
//! operations are `@Int.neg` (`-a`) and `@Int.+`, `@Int.-`, `@Int.*` and
//! the comparisons, defined by cases over the ones on `@Nat` and never by
//! recursion on a number, so on numerals they take constant time; an operator
//! whose operand is an `@Int` is the `@Int` one (the checker's
//! `operator`), and a numeral where an `@Int` is expected is `@Int.Pos`.
//!
//! A script's global may take a prelude global's name, and the name is then
//! the script's (every kernel script that defines its own `Nat` or `Bool`
//! still checks). The prelude's `@`-spelled globals cannot be taken: a
//! script cannot declare an `@` name.
//!
//! Entry point: `load`.

use crate::signature::{Arithmetic, Builtins, GlobalId, Signature};
use crate::syntax::{parse_script, Item};

/// The prelude's source. `Nat` and `Int` are renamed `@Nat` and `@Int`
/// once they are checked, since a module cannot declare an `@` name, and so
/// are the helpers in `RENAMED`.
pub const SOURCE: &str = r"$ @mod PRELUDE
$ Bool : @Type 1 = @union False: {}, True: {}
$ true : Bool = Bool.True
$ false : Bool = Bool.False
$ not : Bool -> Bool = \b => Bool.elim @ctx {.m = 1} (\_ => Bool) true false b
$ (&&) : Bool -> Bool -> Bool = \a b => Bool.elim @ctx {.m = 1} (\_ => Bool) false b a
$ (||) : Bool -> Bool -> Bool = \a b => Bool.elim @ctx {.m = 1} (\_ => Bool) b true a
$ ite : @ctx {u: @l} -> (t: @Type u) -> Bool -> t -> t -> t = \c a b => Bool.elim @ctx {.m = u} (\_ => t) b a c
$ Nat : @Type 1 = @union Zero: {}, Succ: Nat
$ (+) : Nat -> Nat -> Nat = \m n => Nat.elim @ctx {.m = 1} (\_ => Nat) m (\_ r => Nat.Succ.{ r }) n
$ (*) : Nat -> Nat -> Nat = \m n => Nat.elim @ctx {.m = 1} (\_ => Nat) Nat.Zero (\_ r => r + m) n
$ is_zero : Nat -> Bool = \n => Nat.elim @ctx {.m = 1} (\_ => Bool) true (\_ _ => false) n
$ pred : Nat -> Nat = \n => Nat.elim @ctx {.m = 1} (\_ => Nat) Nat.Zero (\k _ => k) n
$ (-) : Nat -> Nat -> Nat = \m n => Nat.elim @ctx {.m = 1} (\_ => Nat) m (\_ r => pred r) n
$ (<) : Nat -> Nat -> Bool = \m =>
    Nat.elim @ctx {.m = 1} (\_ => Nat -> Bool) (\n => not (is_zero n)) (\_ r n => not (is_zero n) && r (pred n)) m
$ (==) : Nat -> Nat -> Bool = \m =>
    Nat.elim @ctx {.m = 1} (\_ => Nat -> Bool) is_zero (\_ r n => not (is_zero n) && r (pred n)) m
$ (>) : Nat -> Nat -> Bool = \a b => b < a
$ (<=) : Nat -> Nat -> Bool = \a b => not (b < a)
$ (>=) : Nat -> Nat -> Bool = \a b => not (a < b)
$ (!=) : Nat -> Nat -> Bool = \a b => not (a == b)
$ Int : @Type 1 = @union Pos: Nat, NegSucc: Nat
$ neg_of_nat : Nat -> Int = \n => ite @ctx {.u = 1} Int (is_zero n) Int.Pos.{ Nat.Zero } Int.NegSucc.{ pred n }
$ sub_nat : Nat -> Nat -> Int = \m n => ite @ctx {.u = 1} Int (n <= m) Int.Pos.{ m - n } Int.NegSucc.{ pred (n - m) }
$ int_neg : Int -> Int = \a => Int.elim @ctx {.m = 1} (\_ => Int) (\m => neg_of_nat m) (\m => Int.Pos.{ Nat.Succ.{ m } }) a
$ int_add : Int -> Int -> Int = \a b => Int.elim @ctx {.m = 1} (\_ => Int)
    (\m => Int.elim @ctx {.m = 1} (\_ => Int) (\n => Int.Pos.{ m + n }) (\n => sub_nat m Nat.Succ.{ n }) b)
    (\m => Int.elim @ctx {.m = 1} (\_ => Int) (\n => sub_nat n Nat.Succ.{ m }) (\n => Int.NegSucc.{ Nat.Succ.{ m + n } }) b)
    a
$ int_sub : Int -> Int -> Int = \a b => int_add a (int_neg b)
$ int_mul : Int -> Int -> Int = \a b => Int.elim @ctx {.m = 1} (\_ => Int)
    (\m => Int.elim @ctx {.m = 1} (\_ => Int) (\n => Int.Pos.{ m * n }) (\n => neg_of_nat (m * Nat.Succ.{ n })) b)
    (\m => Int.elim @ctx {.m = 1} (\_ => Int) (\n => neg_of_nat (Nat.Succ.{ m } * n)) (\n => Int.Pos.{ Nat.Succ.{ m } * Nat.Succ.{ n } }) b)
    a
$ int_lt : Int -> Int -> Bool = \a b => Int.elim @ctx {.m = 1} (\_ => Bool)
    (\m => Int.elim @ctx {.m = 1} (\_ => Bool) (\n => m < n) (\_ => false) b)
    (\m => Int.elim @ctx {.m = 1} (\_ => Bool) (\_ => true) (\n => n < m) b)
    a
$ int_eq : Int -> Int -> Bool = \a b => Int.elim @ctx {.m = 1} (\_ => Bool)
    (\m => Int.elim @ctx {.m = 1} (\_ => Bool) (\n => m == n) (\_ => false) b)
    (\m => Int.elim @ctx {.m = 1} (\_ => Bool) (\_ => false) (\n => m == n) b)
    a
$ int_gt : Int -> Int -> Bool = \a b => int_lt b a
$ int_le : Int -> Int -> Bool = \a b => not (int_lt b a)
$ int_ge : Int -> Int -> Bool = \a b => not (int_lt a b)
$ int_ne : Int -> Int -> Bool = \a b => not (int_eq a b)
";

/// The helpers renamed to their `@` spelling, besides every global of `Nat`
/// and `Int`, which take an `@`.
const RENAMED: [(&str, &str); 15] = [
    ("ite", "@Bool.if"),
    ("is_zero", "@Nat.is_zero"),
    ("pred", "@Nat.pred"),
    ("neg_of_nat", "@Int.neg_of_nat"),
    ("sub_nat", "@Int.sub_nat"),
    ("int_neg", "@Int.neg"),
    ("int_add", "@Int.+"),
    ("int_sub", "@Int.-"),
    ("int_mul", "@Int.*"),
    ("int_lt", "@Int.<"),
    ("int_eq", "@Int.=="),
    ("int_gt", "@Int.>"),
    ("int_le", "@Int.<="),
    ("int_ge", "@Int.>="),
    ("int_ne", "@Int.!="),
];

/// Check the prelude into `sig`, with `check_item` checking one item, and
/// seal it. The prelude is fixed, so a failure is a bug in the kernel.
pub(crate) fn load(sig: &mut Signature, mut check_item: impl FnMut(&mut Signature, &Item) -> utilities::Result<()>) {
    let items = parse_script(SOURCE).unwrap_or_else(|e| panic!("the prelude does not parse:\n{}", e.render(SOURCE, "PRELUDE")));
    for item in &items {
        check_item(sig, item).unwrap_or_else(|e| panic!("the prelude does not check:\n{}", e.render(SOURCE, "PRELUDE")));
    }
    let typed: Vec<String> = sig
        .names()
        .filter(|n| ["Nat", "Int"].iter().any(|t| *n == *t || n.strip_prefix(t).is_some_and(|rest| rest.starts_with('.'))))
        .map(String::from)
        .collect();
    let renames = typed.iter().map(|n| (n.clone(), format!("@{n}"))).chain(RENAMED.iter().map(|(f, t)| (f.to_string(), t.to_string())));
    for (from, to) in renames.collect::<Vec<_>>() {
        let id = sig.lookup(&from).expect("the prelude declares it");
        sig.rename(id, &to);
    }
    let id = |name: &str| -> GlobalId { sig.lookup(name).expect("the prelude declares it") };
    let builtins = Builtins {
        bool: id("Bool"),
        true_ctor: id("Bool.True"),
        false_ctor: id("Bool.False"),
        true_value: id("true"),
        bool_if: id("@Bool.if"),
        nat: id("@Nat"),
        zero: id("@Nat.Zero"),
        succ: id("@Nat.Succ"),
        int: id("@Int"),
        int_pos: id("@Int.Pos"),
        int_neg_succ: id("@Int.NegSucc"),
        arithmetic: ARITHMETIC.map(|(name, op)| (id(name), op)),
    };
    sig.seal_prelude(builtins);
}

/// The globals of the prelude that compute on two numerals by machine
/// arithmetic. See Rule [Nat-Literal].
const ARITHMETIC: [(&str, Arithmetic); 7] = [
    ("+", Arithmetic::Add),
    ("-", Arithmetic::Sub),
    ("*", Arithmetic::Mul),
    ("<", Arithmetic::Lt),
    ("==", Arithmetic::Eq),
    ("@Nat.pred", Arithmetic::Pred),
    ("@Nat.is_zero", Arithmetic::IsZero),
];
