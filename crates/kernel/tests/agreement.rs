//! The frontend's checker and the kernel agree on the propositions of #539
//! (issue #595): each program here is checked by both, the frontend's with
//! CORE imported and the kernel's after its prelude, and both accept it or
//! both reject it.

use std::rc::Rc;

const CORE_SRC: &str = include_str!("../../../library/CORE.ares");

/// The frontend checker's verdict on `src`: its error, or `None`.
fn frontend(src: &str) -> Option<String> {
    let (ast, core) = frontend::parse_into(frontend::Ast::new(), CORE_SRC).expect("parse CORE");
    let (ast, prog) = frontend::parse_into(ast, src).expect("parse");
    let types = Rc::new(frontend::Types::new());
    let mut core_checker = frontend::Checker::new(&ast, types.clone());
    core_checker.check_program(&core).expect("check CORE");
    let mut checker = frontend::Checker::new(&ast, types);
    checker.import_from(&core_checker);
    checker.check_program(&prog).err().map(|e| e.render(src, "AGREE.ares"))
}

/// The kernel's verdict on `src`, re-check included.
fn kernel(src: &str) -> Option<String> {
    match kernel::check_script(src) {
        Ok(sig) => kernel::recheck(&sig).err().map(|e| e.to_string()),
        Err(e) => Some(e.render(src, "AGREE.ares")),
    }
}

fn module(src: &str) -> String {
    format!("$ @mod AGREE\n{src}")
}

/// Both checkers accept `src`.
fn both_accept(src: &str) {
    let src = module(src);
    if let Some(e) = frontend(&src) {
        panic!("the frontend rejects:\n{e}");
    }
    if let Some(e) = kernel(&src) {
        panic!("the kernel rejects:\n{e}");
    }
}

/// Both checkers reject `src`.
fn both_reject(src: &str) {
    let src = module(src);
    assert!(frontend(&src).is_some(), "the frontend accepts:\n{src}");
    let Some(e) = kernel(&src) else { panic!("the kernel accepts:\n{src}") };
    assert!(!e.contains("UNSUPPORTED") && !e.contains("UNKNOWN_SYMBOL"), "the kernel cannot read it:\n{e}");
}

const SMALL: &str = "$ small : (n: @Nat) -> n < 10 -> @Nat = \\p => n\n";
const BOTH: &str = "$ both : (n: @Nat) -> n < 3 && n > 0 || n == 7 -> @Nat = \\p => n\n";

#[test]
fn a_precondition_is_proved_by_computation() {
    both_accept(&format!("{SMALL}$ k : @Nat = small 3 (@refl true)\n"));
    both_reject(&format!("{SMALL}$ k : @Nat = small 30 (@refl true)\n"));
    both_accept(&format!("{BOTH}$ a : @Nat = both 2 (@refl true)\n$ b : @Nat = both 7 (@refl true)\n"));
    both_reject(&format!("{BOTH}$ a : @Nat = both 0 (@refl true)\n"));
}

#[test]
fn a_boolean_is_a_proposition() {
    both_accept("$ Small : (n: @Nat) -> @Type 0 = n < 10\n");
    both_accept("$ t : true = @refl true\n");
    both_reject("$ f : false = @refl true\n");
    both_reject("$ Small : (n: @Nat) -> @Type 1 = n < 10\n");
    both_accept("$ c : (n: @Nat) -> (n < 4) ~ (n < 4) = @refl (n < 4)\n");
    both_reject("$ r : (n: @Nat) -> n < 4 = @refl true\n");
}

#[test]
fn every_comparison_computes() {
    both_accept("$ a : 3 > 2 = @refl true\n$ b : 2 <= 2 = @refl true\n$ c : 4 >= 5 ~ false = @refl false\n");
    both_accept("$ d : 3 != 4 = @refl true\n$ e : not (5 < 5) = @refl true\n$ f : 2 + 2 == 4 = @refl true\n");
    both_reject("$ a : 2 > 3 = @refl true\n");
    both_reject("$ d : 3 != 3 = @refl true\n");
}

#[test]
fn a_let_stays_transparent() {
    both_accept("$ k : let n = 3 in n ~ 3 = @refl 3\n");
    both_accept("$ a : @Nat = let n = 4 in let p : n < 5 = @refl true in 0\n");
    both_reject("$ a : @Nat = let n = 6 in let p : n < 5 = @refl true in 0\n");
}

#[test]
fn sizes_compute() {
    both_accept("$ z : (n: @Nat) -> n + 0 ~ n = @refl n\n");
    both_accept("$ s : 2 * 3 ~ 6 = @refl 6\n");
    both_reject("$ w : 1 ~ 2 = @refl 1\n");
}

// The frontend folds `n == n` to `true` and `n < n` to `false` for a
// variable `n`; the kernel's comparisons are recursive definitions, so there
// they are lemmas, proved by induction.
#[test]
fn folding_laws_are_lemmas_in_the_kernel() {
    let law = module("$ r : (n: @Nat) -> n == n = @refl true\n");
    assert_eq!(frontend(&law), None);
    assert!(kernel(&law).is_some_and(|e| e.contains("expected `n == n`")), "{:?}", kernel(&law));
    let lemma = module("$ r : (n: @Nat) -> n == n = @Nat.elim (\\k => k == k) (@refl true) (\\k ih => ih) n\n");
    assert_eq!(kernel(&lemma), None);
    let irreflexive = module("$ r : (n: @Nat) -> not (n < n) = @Nat.elim (\\k => not (k < k)) (@refl true) (\\k ih => ih) n\n");
    assert_eq!(kernel(&irreflexive), None);
}

// Numerals of any size (#609): the kernel computes on their numbers.
#[test]
fn large_numerals_compute() {
    both_accept("$ big : (n: @Nat) -> n < 1000000 -> @Nat = \\p => n\n$ k : @Nat = big 999999 (@refl true)\n");
    both_reject("$ big : (n: @Nat) -> n < 1000000 -> @Nat = \\p => n\n$ k : @Nat = big 1000000 (@refl true)\n");
    both_accept("$ m : 4096 * 4096 == 16777216 = @refl true\n");
    both_reject("$ m : 4096 * 4096 == 16777217 = @refl true\n");
}

// The kernel computes an `if` in a type (#609); the frontend's propositions
// compare sizes, booleans and types, and an `if` is none of them yet.
#[test]
fn an_if_in_a_type_is_the_kernels() {
    let src = module("$ k : (if 3 < 4 => 1 else 2) ~ 1 = @refl 1\n");
    assert!(frontend(&src).is_some_and(|e| e.contains("UNSUPPORTED")), "{:?}", frontend(&src));
    assert_eq!(kernel(&src), None);
    let wrong = module("$ k : (if 3 > 4 => 1 else 2) ~ 1 = @refl 1\n");
    assert!(kernel(&wrong).is_some_and(|e| e.contains("expected `@Bottom`")), "{:?}", kernel(&wrong));
}

#[test]
fn transport_moves_a_comparison() {
    both_accept(
        "$ moved : (n: @Nat) -> (m: @Nat) -> n ~ m -> n < 10 -> m < 10 = \\e p => @transp n (\\k => k < 10) p m e\n",
    );
}
