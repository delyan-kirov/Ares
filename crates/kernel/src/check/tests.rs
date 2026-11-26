use crate::{check_script, normal_form, Signature};

/// `src` as a module: a test's script is its items alone.
pub(crate) fn module(src: &str) -> String {
    format!("$ @mod TEST\n{src}")
}

pub(crate) fn accept(src: &str) -> Signature {
    let src = &module(src);
    match check_script(src) {
        Ok(sig) => {
            crate::recheck(&sig).unwrap_or_else(|e| panic!("does not re-check: {e}"));
            sig
        }
        Err(e) => panic!("rejected:\n{}", e.render(src, "TEST.ares")),
    }
}

pub(crate) fn reject(src: &str, needle: &str) {
    let src = &module(src);
    match check_script(src) {
        Ok(_) => panic!("accepted, expected an error containing `{needle}`"),
        Err(e) => {
            let shown = e.render(src, "TEST.ares");
            assert!(shown.contains(needle), "error does not mention `{needle}`:\n{shown}");
        }
    }
}

// Church numerals over a proposition-free universe, so conversion has some
// computation to do.
const CHURCH: &str = r"
$ Num : @Type 2 = (t: @Type 1) -> (t -> t) -> t -> t
$ zero : Num = \t s z => z
$ succ : Num -> Num = \n t s z => s (n t s z)
$ add : Num -> Num -> Num = \m n t s z => m t s (n t s z)
$ two : Num = succ (succ zero)
$ four : Num = succ (succ two)
$ P : Num -> @Type 1 = @axiom
";

#[test]
fn identity_at_every_level() {
    accept(
        r"
$ id : @ctx {u: @l} -> (t: @Type u) -> t -> t = \x => x
$ id1 : (t: @Type 1) -> t -> t = id @ctx {.u = 1} t
$ selfapp : (t: @Type 1) -> t -> t = id @ctx {.u = 2} ((t: @Type 1) -> t -> t) id1 t
",
    );
}

#[test]
fn conversion_evaluates() {
    let src = format!("{CHURCH}$ p : P (add two two) = @axiom\n$ q : P four = p\n");
    accept(&src);
    let src = format!("{CHURCH}$ p : P (add two two) = @axiom\n$ q : P two = p\n");
    reject(&src, "expected `P");
}

#[test]
fn normal_forms_read_back() {
    let sig = accept(CHURCH);
    assert_eq!(normal_form(&sig, "two").unwrap(), r"\t => \s => \z => s (s z)");
}

#[test]
fn functions_are_compared_up_to_eta() {
    accept(
        r"
$ A : @Type 1 = @axiom
$ f : A -> A = @axiom
$ Q : (A -> A) -> @Type 1 = @axiom
$ q : Q f = @axiom
$ r : Q (\x => f x) = q
",
    );
}

#[test]
fn proofs_of_a_proposition_are_equal() {
    accept(
        r"
$ P : @Type 0 = @axiom
$ p : P = @axiom
$ p2 : P = @axiom
$ Q : P -> @Type 1 = @axiom
$ q : Q p = @axiom
$ r : Q p2 = q
",
    );
    // Data are not proofs.
    reject(
        r"
$ A : @Type 1 = @axiom
$ a : A = @axiom
$ a2 : A = @axiom
$ Q : A -> @Type 1 = @axiom
$ q : Q a = @axiom
$ r : Q a2 = q
",
        "expected `Q a2`",
    );
}

#[test]
fn propositions_are_impredicative() {
    accept(
        r"
$ True : @Type 0 = (p: @Type 0) -> p -> p
$ tt : True = \p x => x
",
    );
}

#[test]
fn universes_are_not_cumulative() {
    accept("$ A : @Type 1 = @axiom\n$ B : @Type 1 = A\n");
    reject("$ A : @Type 1 = @axiom\n$ B : @Type 2 = A\n", "expected `@Type 2`, found `@Type 1`");
    reject("$ A : @Type 0 = @axiom\n$ B : @Type 1 = A\n", "expected `@Type 1`, found `@Type 0`");
    reject("$ A : @Type 2 = @axiom\n$ B : @Type 1 = A\n", "expected `@Type 1`, found `@Type 2`");
    reject("$ F : @Type 1 -> @Type 1 = @axiom\n$ G : @Type 1 -> @Type 2 = F\n", "expected");
}

#[test]
fn levels_must_be_given_and_bound() {
    reject("$ id : @ctx {u: @l} -> (t: @Type u) -> t -> t = \\x => x\n$ f : @Type 1 = id\n", "cannot infer level `u` of `id`");
    reject("$ A : @Type v = @axiom\n", "unknown level `v`");
}

#[test]
fn names_are_resolved() {
    reject("$ A : @Type 1 = @axiom\n$ B : @Type 1 = Aa\n", "unknown name `Aa`");
    reject("$ A : @Type 1 = @axiom\n$ A : @Type 1 = @axiom\n", "already defined");
}

#[test]
fn let_is_transparent() {
    let src = format!("{CHURCH}$ p : P four = @axiom\n$ q : P (let n = two in add n n) = p\n");
    accept(&src);
}

#[test]
fn unannotated_lambdas_need_an_expected_type() {
    reject("$ f = \\x => x\n", "needs its type");
    reject("$ A : @Type 1 = @axiom\n$ f : @Type 1 = (\\x => x) A\n", "cannot infer the type of `x`");
}

#[test]
fn pairs_are_dependent() {
    let sig = accept(
        r"
$ A : @Type 1 = @axiom
$ B : A -> @Type 1 = @axiom
$ a : A = @axiom
$ b : B a = @axiom
$ p : {x: A, snd: B x} = {a, b}
$ second : B p.0 = p.1
$ swap : {A, A} -> {A, A} = \q => {q.1, q.0}
$ again : {A, A} = swap (swap {a, a})
",
    );
    assert_eq!(normal_form(&sig, "again").unwrap(), "{a, a}");
    reject("$ A : @Type 1 = @axiom\n$ a : A = @axiom\n$ p : {A, A} = {a, @tt}\n", "expected `A`, found `@Top`");
}

#[test]
fn pairs_are_compared_up_to_eta() {
    accept(
        r"
$ A : @Type 1 = @axiom
$ p : {A, A} = @axiom
$ Q : {A, A} -> @Type 1 = @axiom
$ q : Q p = @axiom
$ r : Q {p.0, p.1} = q
",
    );
}

#[test]
fn a_pair_of_proofs_is_a_proposition() {
    accept(
        r"
$ P : @Type 0 = @axiom
$ Q : @Type 0 = @axiom
$ And : @Type 0 = {P, Q}
$ p : P = @axiom
$ q : Q = @axiom
$ both : And = {p, q}
$ swap : {P, Q} -> {Q, P} = \h => {h.1, h.0}
",
    );
}

#[test]
fn refined_values_are_data() {
    // A pair of data and a proof (a refinement, `{x: A if p x}`) is data,
    // and two of them are equal when their data parts are.
    accept(
        r"
$ A : @Type 1 = @axiom
$ P : A -> @Type 0 = @axiom
$ Refined : @Type 1 = {x: A, snd: P x}
$ a : A = @axiom
$ p : P a = @axiom
$ p2 : P a = @axiom
$ Q : Refined -> @Type 1 = @axiom
$ q : Q {a, p} = @axiom
$ r : Q {a, p2} = q
",
    );
}

#[test]
fn bottom_proves_anything() {
    accept(
        r"
$ A : @Type 1 = @axiom
$ Not : @Type 0 -> @Type 0 = \p => p -> @Bottom
$ explode : @Bottom -> A = \e => (e |> @absurd : A)
$ trivial : @Top = @tt
$ contradiction : (p2: @Type 0) -> p2 -> Not p2 -> @Bottom = \p n => n p
",
    );
    reject("$ A : @Type 1 = @axiom\n$ a : A = @axiom\n$ bad : A = (@tt |> @absurd : A)\n", "expected `@Bottom`, found `@Top`");
}

pub(crate) const NAT: &str = r"
$ Nat : @Type 1 = @union Zero: {}, Succ: Nat
$ add : Nat -> Nat -> Nat = \m n => Nat.elim @ctx {.m = 1} (\_ => Nat) n (\_ r => Nat.Succ.{ r }) m
$ two : Nat = Nat.Succ.{ Nat.Succ.{ Nat.Zero } }
$ four : Nat = Nat.Succ.{ Nat.Succ.{ Nat.Succ.{ Nat.Succ.{ Nat.Zero } } } }
$ P : Nat -> @Type 1 = @axiom
";

#[test]
fn recursors_compute_on_constructors() {
    let src = format!("{NAT}$ p : P (add two two) = @axiom\n$ q : P four = p\n");
    let sig = accept(&src);
    assert_eq!(normal_form(&sig, "q").unwrap(), "p");
    reject(&format!("{NAT}$ p : P (add two two) = @axiom\n$ q : P two = p\n"), "expected `P two`, found `P (add two two)`");
}

#[test]
fn applications_of_one_definition_compare_by_arguments() {
    // `pow two sixteen` unfolds to 65536 constructors; equal arguments make
    // the two sides equal without unfolding it.
    let src = format!(
        "{NAT}$ mul : Nat -> Nat -> Nat = \\m n => Nat.elim @ctx {{.m = 1}} (\\_ => Nat) Nat.Zero (\\_ r => add n r) m\n$ pow : Nat -> Nat -> Nat = \\b e => Nat.elim @ctx {{.m = 1}} (\\_ => Nat) Nat.Succ.{{ Nat.Zero }} (\\_ r => mul b r) e\n$ sixteen : Nat = mul four four\n$ p : P (pow two sixteen) = @axiom\n$ q : P (pow two (add (mul two four) (mul four two))) = p\n"
    );
    accept(&src);
}

#[test]
fn recursors_are_stuck_on_variables() {
    // `add n zero` does not reduce: the recursion is on the first argument.
    let src = format!("{NAT}$ n : Nat = @axiom\n$ p : P (add Nat.Zero n) = @axiom\n$ q : P n = p\n");
    accept(&src);
    reject(&format!("{NAT}$ n : Nat = @axiom\n$ p : P (add n Nat.Zero) = @axiom\n$ q : P n = p\n"), "expected `P n`");
}

#[test]
fn recursor_types_are_generated() {
    let sig = accept(NAT);
    let elim = sig.lookup("Nat.elim").unwrap();
    let ty = crate::term::TermDisplay {
        sig: &sig,
        names: &[],
        level_names: &sig.global(elim).level_params,
        term: &sig.global(elim).ty,
    }
    .to_string();
    assert_eq!(
        ty,
        "(motive: Nat -> @Type m) -> motive Nat.Zero -> ((f0: Nat) -> motive f0 -> motive Nat.Succ.{ f0 }) -> (x: Nat) -> motive x"
    );
}

#[test]
fn parameters_and_dependent_motives() {
    accept(&format!(
        r"{NAT}
$ List : @ctx {{u: @l}} -> (a: @Type (u + 1)) -> @Type (u + 1) = @union Nil: {{}}, Cons: {{h: a, t: List @ctx {{.u = u}} a}}
$ length : List @ctx {{.u = 0}} Nat -> Nat = \xs => List.elim @ctx {{.u = 0, .m = 1}} Nat (\_ => Nat) Nat.Zero (\_ _ r => Nat.Succ.{{ r }}) xs
$ xs : List @ctx {{.u = 0}} Nat = List.Cons.{{ two, List.Cons.{{ four, List.Nil }} }}
$ p : P (length xs) = @axiom
$ q : P two = p
$ Unit : @Type 1 = @union Unit: {{}}
$ Vec : Nat -> @Type 1 = \n => Nat.elim @ctx {{.m = 2}} (\_ => @Type 1) Unit (\_ t => {{Nat, t}}) n
$ v : Vec two = {{Nat.Zero, four, Unit.Unit}}
"
    ));
}

#[test]
fn constructors_are_injective_by_conversion() {
    accept(&format!(
        r"{NAT}
$ n : Nat = @axiom
$ p : P Nat.Succ.{{ add Nat.Zero n }} = @axiom
$ q : P Nat.Succ.{{ n }} = p
"
    ));
}

#[test]
fn inductive_declarations_are_checked() {
    reject("$ Bad : @Type 1 = @union Mk: {Bad -> Bad}\n", "may only occur as the result of a field");
    reject("$ Prop : @Type 0 = @union Yes: {}\n", "inductive propositions are not supported");
    reject("$ Big : @Type 1 = @union Mk: @Type 1\n", "too large");
    reject("$ Idx : @Type 1 -> @Type 2 = @union Mk: {}\n$ I : @Type 1 = @union A: {}, A: {}\n", "`I.A` is already defined");
    reject("$ F : @Type 1 = @union Mk: {}\n$ G : F = @union Mk: {}\n", "must end in `@Type l`");
}

const VEC: &str = r"
$ Vec : (a: @Type 1) -> (n: Nat) -> @Type 1 = @union Vnil: {} -> Vec a Nat.Zero, Vcons: {m: Nat, h: a, t: Vec a m} -> Vec a Nat.Succ.{ m }
";

#[test]
fn indexed_families_have_an_indexed_recursor() {
    let sig = accept(&format!("{NAT}{VEC}"));
    let elim = sig.lookup("Vec.elim").unwrap();
    let shown = crate::term::TermDisplay {
        sig: &sig,
        names: &[],
        level_names: &sig.global(elim).level_params,
        term: &sig.global(elim).ty,
    };
    assert_eq!(
        shown.to_string(),
        "(a: @Type 1) -> (motive: (n: Nat) -> Vec a n -> @Type m) -> motive Nat.Zero Vec.Vnil \
         -> ((m: Nat) -> (h: a) -> (t: Vec a m) -> motive m t -> motive Nat.Succ.{ m } Vec.Vcons.{ m, h, t }) \
         -> (n: Nat) -> (x: Vec a n) -> motive n x"
    );
}

#[test]
fn the_index_rules_out_constructors() {
    // `head` needs no real case for `vnil`: its motive is `{}`-like at zero.
    let src = format!(
        r"{NAT}{VEC}
$ Unit : @Type 1 = @union Unit: {{}}
$ Head : Nat -> @Type 1 = \k => Nat.elim @ctx {{.m = 2}} (\_ => @Type 1) Unit (\_ _ => Nat) k
$ head : (n: Nat) -> Vec Nat Nat.Succ.{{ n }} -> Nat = \v => Vec.elim @ctx {{.m = 1}} Nat (\k _ => Head k) Unit.Unit (\m h t r => h) Nat.Succ.{{ n }} v
$ h : Nat = head Nat.Zero Vec.Vcons.{{ Nat.Zero, four, (Vec.Vnil : Vec Nat Nat.Zero) }}
"
    );
    let sig = accept(&src);
    assert_eq!(normal_form(&sig, "h").unwrap(), "Nat.Succ.{ Nat.Succ.{ Nat.Succ.{ Nat.Succ.{ Nat.Zero } } } }");
}

#[test]
fn a_value_at_propositionally_equal_indices_is_a_cast() {
    let src = format!(
        r"{NAT}{VEC}
$ length : (a: @Type 1) -> (n: Nat) -> Vec a n -> Nat = \v => Vec.elim @ctx {{.m = 1}} a (\_ _ => Nat) Nat.Zero (\m h t r => Nat.Succ.{{ r }}) n v
$ k : Nat = @axiom
$ e : Nat.Succ.{{ Nat.Zero }} ~ k = @axiom
$ one : Vec Nat Nat.Succ.{{ Nat.Zero }} = Vec.Vcons.{{ Nat.Zero, two, (Vec.Vnil : Vec Nat Nat.Zero) }}
$ moved : Vec Nat k = @cast (Vec Nat Nat.Succ.{{ Nat.Zero }}) (Vec Nat k) (@transp Nat.Succ.{{ Nat.Zero }} (\j => Vec Nat Nat.Succ.{{ Nat.Zero }} ~ Vec Nat j) (@refl (Vec Nat Nat.Succ.{{ Nat.Zero }})) k e) one
$ len : Nat = length Nat k moved
"
    );
    let sig = accept(&src);
    assert!(normal_form(&sig, "moved").unwrap().starts_with("@cast (Vec Nat Nat.Succ.{ Nat.Zero }) (Vec Nat k) @irrelevant Vec.Vcons.{ Nat.Zero"));
    assert_eq!(normal_form(&sig, "len").unwrap(), "Nat.Succ.{ Nat.Zero }");
}

#[test]
fn the_identity_type_is_an_indexed_family() {
    let src = format!(
        r"{NAT}
$ Id : (a: @Type 1) -> (x: a) -> (y: a) -> @Type 1 = @union Idrefl: {{}} -> Id a x x
$ J : (a: @Type 1) -> (x: a) -> (p2: (y: a) -> Id a x y -> @Type 1) -> p2 x (Id.Idrefl : Id a x x) -> (y: a) -> (p: Id a x y) -> p2 y p = \d y p => Id.elim @ctx {{.m = 1}} a x p2 d y p
$ p : P two = @axiom
$ q : P (J Nat two (\_ _ => Nat) two two (Id.Idrefl : Id Nat two two)) = p
"
    );
    accept(&src);
}

#[test]
fn indexed_families_are_restricted() {
    reject(&format!("{NAT}$ V : (n: Nat) -> @Type 1 = @union A: {{}} -> V Nat.Zero, B: {{}}\n"), "must state its result");
    reject(&format!("{NAT}$ V : (n: Nat) -> @Type 1 = @union Mk: {{}} -> Nat\n"), "must be `V` at its own parameters");
    reject(
        &format!("{NAT}$ V : (n: Nat) -> (f: P n) -> @Type 1 = @union Mk: {{p: P Nat.Zero}} -> V Nat.Zero p\n"),
        "may depend on the parameters, not on earlier indices",
    );
    reject("$ V : (p: @Top) -> @Type 1 = @union Mk: {} -> V @tt\n", "must be data");
}

const EQUALITY: &str = r"
$ trans : (x: Nat) -> (y: Nat) -> (z: Nat) -> x ~ y -> y ~ z -> x ~ z = \e f => @transp y (\w => x ~ w) e z f
$ sym : (x: Nat) -> (y: Nat) -> x ~ y -> y ~ x = \e => @transp x (\w => w ~ x) (@refl x) y e
$ a : Nat = @axiom
$ b : Nat = @axiom
$ c : Nat = @axiom
$ ab : a ~ b = @axiom
$ bc : b ~ c = @axiom
";

#[test]
fn holes_are_solved_from_the_expected_type_and_the_arguments() {
    // `x` and `z` from the expected type, `y` from `ab`.
    accept(&format!("{NAT}{EQUALITY}$ ac : a ~ c = trans _ _ _ ab bc\n"));
    // With no expected type, from the arguments alone.
    accept(&format!("{NAT}{EQUALITY}$ ca : c ~ a = sym _ _ (trans _ _ _ ab bc)\n"));
    // The solutions are in the elaborated term, which re-checks.
    let sig = accept(&format!("{NAT}{EQUALITY}$ ba : b ~ a = sym _ _ ab\n"));
    crate::recheck(&sig).unwrap();
}

#[test]
fn a_motive_level_left_out_is_inferred() {
    let sig = accept(&format!(
        "{NAT}$ double : Nat -> Nat = \\n => Nat.elim (\\_ => Nat) Nat.Zero (\\_ r => Nat.Succ.{{ Nat.Succ.{{ r }} }}) n\n$ add_zero : (n: Nat) -> add n Nat.Zero ~ n = Nat.elim (\\n => add n Nat.Zero ~ n) @tt (\\_ ih => ih) n\n"
    ));
    assert_eq!(normal_form(&sig, "double").unwrap(), r"\n => Nat.elim @ctx {.m = 1} (\_ => Nat) Nat.Zero (\_ => \r => Nat.Succ.{ Nat.Succ.{ r } }) n");
}

#[test]
fn holes_that_nothing_fixes_are_rejected() {
    reject(&format!("{NAT}{EQUALITY}$ f : (x: Nat) -> a ~ x -> a ~ x = \\e => trans _ _ _ e (@refl _)\n"), "cannot infer this `_`");
    reject(&format!("{NAT}{EQUALITY}$ t : Nat -> Nat -> @Type 0 = \\x y => trans x _ y\n"), "cannot infer this argument");
    reject(&format!("{NAT}$ n : @Type 1 = Nat.elim\n"), "cannot infer level `m` of `Nat.elim`");
    reject(&format!("{NAT}$ n : Nat = _\n"), "cannot infer this `_`");
}

#[test]
fn a_wrong_proof_is_rejected_with_holes_as_without() {
    reject(&format!("{NAT}{EQUALITY}$ ac : a ~ c = trans _ _ _ bc ab\n"), "TYPE_MISMATCH");
    reject(&format!("{NAT}{EQUALITY}$ ac : a ~ b = trans _ _ _ ab bc\n"), "TYPE_MISMATCH");
}

#[test]
fn a_level_left_out_of_a_declaration_is_inferred() {
    accept("$ List : @ctx {u: @l} -> (a: @Type (u + 1)) -> @Type (u + 1) = @union Nil: {}, Cons: {h: a, t: List a}\n");
}

#[test]
fn an_if_takes_the_type_of_its_branches() {
    let sig = accept(
        r"
$ a : @Nat = if 3 < 4 => 1 else 2
$ b : a ~ 1 = @refl 1
$ max : (m: @Nat) -> (n: @Nat) -> @Nat = if m < n => n else m
$ c : max 7 12 ~ 12 = @refl 12
$ t : @Type 1 = if 1 == 1 => @Nat else @Int
$ d : t = 5
$ p : (n: @Nat) -> if n == 0 => @Top else n > 0 = @Nat.elim (\k => if k == 0 => @Top else k > 0) @tt (\k ih => @refl true) n
",
    );
    assert_eq!(normal_form(&sig, "a").unwrap(), "1");
    reject("$ a : @Nat = if 3 => 1 else 2\n", "expected `Bool`, found `@Nat`");
    reject("$ a : @Nat = if 3 < 4 => 1 else true\n", "expected `@Nat`, found `Bool`");
}

#[test]
fn integers_have_their_own_operators() {
    let sig = accept(
        r"
$ a : @Int = -3
$ b : a + 5 ~ 2 = @refl 2
$ c : a * -4 ~ 12 = @refl 12
$ d : 2 - 7 < a = @refl false
$ e : -a == 3 = @refl true
$ abs : (x: @Int) -> @Int = if x < 0 => -x else x
$ f : abs (-7) ~ 7 = @refl 7
$ g : (x: @Int) -> x + 0 ~ x + 0 = @refl (x + 0)
$ n : @Nat = 2 - 7
$ h : -1000000 * 3 + 1 ~ -2999999 = @refl (-2999999)
",
    );
    assert_eq!(normal_form(&sig, "a").unwrap(), "-3");
    assert_eq!(normal_form(&sig, "n").unwrap(), "0");
    assert_eq!(crate::type_of(&sig, "g").unwrap(), "(x: @Int) -> (x + 0) ~ (x + 0)");
    reject("$ a : @Nat = -3\n", "expected `@Nat`, found `@Int`");
    reject("$ a : @Int = 3\n$ b : @Nat = a + 1\n", "expected `@Nat`, found `@Int`");
}

#[test]
fn a_successor_is_written_with_its_constructor() {
    accept("$ s : (n: @Nat) -> @Nat.Succ.{ n } ~ n + 1 = @refl (n + 1)\n$ z : @Nat.Zero ~ 0 = @refl 0\n");
    reject("$ s : (n: @Nat) -> @Nat.Succ.{ n } ~ n = @refl n\n", "expected `(n + 1) ~ n`");
}

// The prelude's arithmetic on numerals gives what its definitions compute:
// each definition's body, applied to small numerals, unfolds by the
// recursor to the value `Arithmetic::compute` gives. A body that calls
// another arithmetic global (`*` calls `+`, `<` calls `@Nat.pred`) relies
// on that one, which the same loop checks.
#[test]
fn arithmetic_on_numerals_agrees_with_the_definitions() {
    use std::rc::Rc;

    use crate::nbe::{apply, eval, eval_global, quote_unfolded, Env, Val};
    use crate::signature::{Computed, GlobalKind};

    let sig = accept("");
    let builtins = sig.builtins().expect("the prelude");
    for (id, op) in builtins.arithmetic {
        let GlobalKind::Definition(body) = &sig.global(id).kind else { panic!("an arithmetic global is a definition") };
        for a in 0..6u64 {
            for b in 0..6u64 {
                let args = if op.arity() == 1 { vec![a] } else { vec![a, b] };
                let defined = args.iter().fold(eval(&sig, &Env::new(), body), |f, n| apply(&sig, f, Val::Nat(*n)));
                let computed = match op.compute(&args).expect("small numerals fit") {
                    Computed::Nat(n) => Val::Nat(n),
                    Computed::Bool(b) => eval_global(&sig, if b { builtins.true_ctor } else { builtins.false_ctor }, Rc::new([])),
                };
                assert_eq!(
                    quote_unfolded(&sig, 0, &defined),
                    quote_unfolded(&sig, 0, &computed),
                    "`{}` on {args:?}",
                    sig.global(id).name
                );
            }
        }
    }
}
