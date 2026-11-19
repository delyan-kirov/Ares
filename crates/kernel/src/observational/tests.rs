use crate::check::tests::{accept, reject, NAT};
use crate::normal_form;

const EQUALITY: &str = r"
$ sym : @ctx {u: @l} -> (a: @Type (u + 1)) -> (x: a) -> (y: a) -> x ~ y -> y ~ x = \e => @transp x (\z => z ~ x) (@refl x) y e
$ trans : @ctx {u: @l} -> (a: @Type (u + 1)) -> (x: a) -> (y: a) -> (z: a) -> x ~ y -> y ~ z -> x ~ z = \e f => @transp y (\w => x ~ w) e z f
$ ap : @ctx {u: @l, v: @l} -> (a: @Type (u + 1)) -> (b: @Type (v + 1)) -> (f: a -> b) -> (x: a) -> (y: a) -> x ~ y -> f x ~ f y = \e => @transp x (\z => f x ~ f z) (@refl (f x)) y e
$ subst : @ctx {u: @l, v: @l} -> (a: @Type (u + 1)) -> (p2: a -> @Type (v + 1)) -> (x: a) -> (y: a) -> x ~ y -> p2 x -> p2 y = \e p => @cast (p2 x) (p2 y) (@transp x (\z => p2 x ~ p2 z) (@refl (p2 x)) y e) p
";

#[test]
fn equality_is_reflexive_by_computation() {
    accept(&format!("{NAT}$ t : add two two ~ four = @refl four\n"));
    reject(&format!("{NAT}$ t : add two two ~ two = @refl two\n"), "expected `@Bottom`");
}

#[test]
fn constructors_are_disjoint_and_injective() {
    accept(&format!(
        r"{NAT}
$ disjoint : Nat.Zero ~ Nat.Succ.{{ Nat.Zero }} -> @Bottom = \e => e
$ injective : (m: Nat) -> (n: Nat) -> Nat.Succ.{{ m }} ~ Nat.Succ.{{ n }} -> m ~ n = \e => e
"
    ));
}

#[test]
fn function_extensionality_holds_by_computation() {
    accept(&format!(
        r"{NAT}
$ funext : (f: Nat -> Nat) -> (g: Nat -> Nat) -> ((x: Nat) -> f x ~ g x) -> f ~ g = \h => h
$ plus_zero : (n: Nat) -> add Nat.Zero n ~ n = @refl n
$ same : (\(n: Nat) => add Nat.Zero n) ~ (\n => n) = \n => @refl n
"
    ));
}

#[test]
fn propositions_are_extensional() {
    accept(
        r"
$ P : @Type 0 = @axiom
$ Q : @Type 0 = @axiom
$ propext : (P -> Q) -> (Q -> P) -> P ~ Q = \f g => {f, g}
$ A : @Type 1 = @axiom
$ boxed : (u: {A, P}) -> (v: {A, P}) -> u.0 ~ v.0 -> u ~ v = \e => {e, @tt}
",
    );
}

#[test]
fn equality_is_not_formed_at_a_proposition() {
    let props = "$ P : @Type 0 = @axiom\n$ p : P = @axiom\n";
    reject(&format!("{props}$ bad : p ~ p = @axiom\n"), "equality is not formed at the proposition `P`");
    reject(&format!("{props}$ bad : @Top = @refl p\n"), "equality is not formed at the proposition `P`");
    reject(&format!("{props}$ bad : @Top = @transp p (\\q => @Top) @tt p @tt\n"), "equality is not formed at the proposition `P`");
}

#[test]
fn pairs_are_equal_componentwise() {
    accept(&format!(
        r"{NAT}
$ annotated : (a: Nat) -> (b: Nat) -> a ~ b -> ({{a, Nat.Zero}} : {{Nat, Nat}}) ~ {{b, Nat.Zero}} = \e => {{e, @tt}}
"
    ));
}

#[test]
fn equality_of_types_compares_formers() {
    accept(&format!(
        r"{NAT}
$ same : Nat ~ Nat = @tt
$ different : Nat ~ (Nat -> Nat) -> @Bottom = \e => e
$ universes : @Type 1 ~ @Type 1 = @tt
$ levels : (@Type 1 -> Nat) ~ (Nat -> @Type 1) -> @Bottom = \e => e
$ arrows : (Nat -> Nat) ~ (Nat -> Nat) = {{@tt, \_ => @tt}}
"
    ));
}

#[test]
fn transport_derives_the_usual_lemmas() {
    accept(&format!("{NAT}{EQUALITY}"));
}

#[test]
fn cast_computes_on_canonical_types() {
    let sig = accept(&format!(
        r"{NAT}{EQUALITY}
$ moved : Nat = subst @ctx {{.u = 0, .v = 0}} Nat (\_ => Nat) two two (@refl two) four
$ pair : {{Nat, Nat}} = @cast {{Nat, Nat}} {{Nat, Nat}} {{@tt, \_ => @tt}} {{two, four}}
$ fn : Nat -> Nat = @cast (Nat -> Nat) (Nat -> Nat) {{@tt, \_ => @tt}} (\n => Nat.Succ.{{ n }})
$ fn_is_succ : fn ~ (\n => Nat.Succ.{{ n }}) = \n => @refl Nat.Succ.{{ n }}
"
    ));
    assert_eq!(normal_form(&sig, "moved").unwrap(), "Nat.Succ.{ Nat.Succ.{ Nat.Succ.{ Nat.Succ.{ Nat.Zero } } } }");
    assert_eq!(
        normal_form(&sig, "pair").unwrap(),
        "{Nat.Succ.{ Nat.Succ.{ Nat.Zero } }, Nat.Succ.{ Nat.Succ.{ Nat.Succ.{ Nat.Succ.{ Nat.Zero } } } }}"
    );
    // Cast-Pi casts the argument and the result, and those casts between
    // `Nat` and itself stay in the normal form: Cast-Refl is conversion only.
    assert_eq!(normal_form(&sig, "fn").unwrap(), r"\_ => Nat.Succ.{ @cast Nat Nat @irrelevant (@cast Nat Nat @irrelevant _) }");
}

#[test]
fn cast_is_stuck_on_variables() {
    let sig = accept(&format!(
        r"{NAT}
$ A : @Type 1 = @axiom
$ e : A ~ Nat = @axiom
$ a : A = @axiom
$ n : Nat = @cast A Nat e a
"
    ));
    assert_eq!(normal_form(&sig, "n").unwrap(), "@cast A Nat @irrelevant a");
}

#[test]
fn a_cast_between_convertible_types_is_the_identity() {
    let sig = accept(&format!(
        r"{NAT}{PARITY}
$ q : Parity = @axiom
$ e : Parity ~ Parity = @axiom
$ same : Parity = @cast Parity Parity e q
$ refl : same ~ q = @refl q
$ m : Nat = @axiom
$ under : even (@cast Nat Nat @tt m) ~ even m = @refl (even m)
"
    ));
    // It is a conversion rule, not a reduction.
    assert!(normal_form(&sig, "same").unwrap().starts_with("@cast "));
    reject(&format!("{NAT}$ m : Nat = @axiom\n$ bad : @cast Nat Nat @tt m ~ Nat.Succ.{{ m }} = @refl m\n"), "expected");
}

#[test]
fn equality_proofs_must_typecheck() {
    reject(&format!("{NAT}$ bad : (m: Nat) -> (n: Nat) -> m ~ n = @refl m\n"), "expected `m ~ n`, found `m ~ m`");
    reject(&format!("{NAT}$ bad : @cast Nat (Nat -> Nat) @tt Nat.Zero ~ Nat.Zero = @axiom\n"), "expected `@Bottom`, found `@Top`");
}

// Naturals up to parity: `R m n` is `even m ~ even n`, an equality of
// booleans, so it computes.
const PARITY: &str = r"
$ Bool : @Type 1 = @union False: {}, True: {}
$ not : Bool -> Bool = \b => Bool.elim @ctx {.m = 1} (\_ => Bool) Bool.True Bool.False b
$ even : Nat -> Bool = \n => Nat.elim @ctx {.m = 1} (\_ => Nat -> Bool) (\_ => Bool.True) (\_ r _ => not (r Nat.Zero)) n Nat.Zero
$ R : Nat -> Nat -> @Type 0 = \m n => even m ~ even n
$ Parity : @Type 1 = @Quot Nat R (\x => @refl (even x)) (\x y e => @transp (even x) (\b => b ~ even x) (@refl (even x)) (even y) e) (\x y z e f => @transp (even y) (\b => even x ~ b) e (even z) f)
$ class : Nat -> Parity = \n => @qin n
";

#[test]
fn classes_are_equal_by_the_relation() {
    accept(&format!(
        r"{NAT}{PARITY}
$ same : class Nat.Zero ~ class two = @tt
$ apart : class Nat.Zero ~ class Nat.Succ.{{ Nat.Zero }} -> @Bottom = \e => e
$ related : (m: Nat) -> (n: Nat) -> R m n -> class m ~ class n = \e => e
"
    ));
}

#[test]
fn eliminating_a_class_needs_respect() {
    let sig = accept(&format!(
        r"{NAT}{PARITY}
$ parity : Parity -> Bool = \q => @qelim (\_ => Bool) even (\x y e => e) q
$ of_four : Bool = parity (class four)
$ classes_agree : (p: Parity) -> (q: Parity) -> p ~ q -> parity p ~ parity q = \e => @transp p (\r => parity p ~ parity r) (@refl (parity p)) q e
"
    ));
    assert_eq!(normal_form(&sig, "of_four").unwrap(), "Bool.True");
    // The identity on representatives does not respect parity.
    reject(
        &format!("{NAT}{PARITY}$ leak : Parity -> Nat = \\q => @qelim (\\_ => Nat) (\\n => n) (\\x y e => e) q\n"),
        "~ y`, found",
    );
}

#[test]
fn quotients_need_an_equivalence() {
    reject(
        &format!("{NAT}$ Lt : @Type 1 = @Quot Nat (\\m n => @Bottom) (\\x => @tt) (\\x y e => e) (\\x y z e f => e)\n"),
        "expected `@Bottom`, found `@Top`",
    );
    reject(
        "$ P : @Type 0 = @axiom\n$ Q : @Type 1 = @Quot P (\\x y => @Top) (\\x => @tt) (\\x y e => e) (\\x y z e f => e)\n",
        "only data can be quotiented",
    );
}

#[test]
fn casts_move_classes_through_representatives() {
    let sig = accept(&format!(
        r"{NAT}{PARITY}
$ moved : Parity = @cast Parity Parity {{@tt, \a b => {{\h => h, \h => h}}}} (class two)
"
    ));
    assert_eq!(normal_form(&sig, "moved").unwrap(), "@qin Nat.Succ.{ Nat.Succ.{ Nat.Zero } }");
}
