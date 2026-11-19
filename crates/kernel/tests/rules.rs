//! A test for every rule in the theory ledger (issue #484): each calls
//! `applies` on a script where the rule fires and `blocked` on a near miss
//! where it must not. `tests/ledger.rs` fails when an implemented rule has
//! no test tagged with its name here.

use kernel::{check_script, normal_form, Signature};

/// Shared definitions, checked before every case.
const PRELUDE: &str = r"$ @mod RULE
$ Nat : @Type 1 = @union Zero: {}, Succ: Nat
$ Bool : @Type 1 = @union False: {}, True: {}
$ List : @ctx {u: @l} -> (a: @Type (u + 1)) -> @Type (u + 1) = @union Nil: {}, Cons: {h: a, t: List @ctx {.u = u} a}
$ add : Nat -> Nat -> Nat = \m n => Nat.elim @ctx {.m = 1} (\_ => Nat) n (\_ r => Nat.Succ.{ r }) m
$ two : Nat = Nat.Succ.{ Nat.Succ.{ Nat.Zero } }
$ four : Nat = Nat.Succ.{ Nat.Succ.{ Nat.Succ.{ Nat.Succ.{ Nat.Zero } } } }
$ P : Nat -> @Type 1 = @axiom
$ not : Bool -> Bool = \b => Bool.elim @ctx {.m = 1} (\_ => Bool) Bool.True Bool.False b
$ even : Nat -> Bool = \n => Nat.elim @ctx {.m = 1} (\_ => Nat -> Bool) (\_ => Bool.True) (\_ r _ => not (r Nat.Zero)) n Nat.Zero
$ R : Nat -> Nat -> @Type 0 = \m n => even m ~ even n
$ Parity : @Type 1 = @Quot Nat R (\x => @refl (even x)) (\x y e => @transp (even x) (\b => b ~ even x) (@refl (even x)) (even y) e) (\x y z e f => @transp (even y) (\b => even x ~ b) e (even z) f)
$ class : Nat -> Parity = \n => @qin n
$ parity : Parity -> Bool = \q => @qelim (\_ => Bool) even (\x y e => e) q
";

/// The prelude and `src` check; the signature, to read normal forms from.
fn applies(src: &str) -> Signature {
    let all = format!("{PRELUDE}{src}");
    match check_script(&all) {
        Ok(sig) => {
            kernel::recheck(&sig).unwrap_or_else(|e| panic!("does not re-check: {e}"));
            sig
        }
        Err(e) => panic!("rejected:\n{}", e.render(&all, "RULE.ares")),
    }
}

/// The prelude checks, `src` does not, and the error mentions `needle`.
fn blocked(src: &str, needle: &str) {
    let all = format!("{PRELUDE}{src}");
    match check_script(&all) {
        Ok(_) => panic!("accepted, expected an error containing `{needle}`:\n{src}"),
        Err(e) => {
            let shown = e.render(&all, "RULE.ares");
            assert!(shown.contains(needle), "error does not mention `{needle}`:\n{shown}");
        }
    }
}

fn normal(sig: &Signature, name: &str) -> String {
    normal_form(sig, name).expect("a definition")
}

// ## Universes and functions

// Test [Univ]
#[test]
fn univ() {
    applies("$ u : @Type 2 = @Type 1\n$ o : @Type 1 = @Type 0\n");
    blocked("$ u : @Type 1 = @Type 1\n", "expected `@Type 1`, found `@Type 2`");
}

// Test [Level-Polymorphism]
#[test]
fn level_polymorphism() {
    applies("$ id : @ctx {u: @l} -> (t: @Type u) -> t -> t = \\x => x\n$ n : Nat = id @ctx {.u = 1} Nat Nat.Zero\n");
    // A level left out is inferred from the types around the use.
    applies("$ id : @ctx {u: @l} -> (t: @Type u) -> t -> t = \\x => x\n$ n : Nat = id Nat Nat.Zero\n");
    blocked("$ id : @ctx {u: @l} -> (t: @Type u) -> t -> t = \\x => x\n$ n : @Type 1 = id\n", "cannot infer level `u` of `id`");
}

// Test [Pi-Form]
#[test]
fn pi_form() {
    applies("$ F : @Type 2 = @Type 1 -> Nat\n$ G : @Type 0 = (a: @Type 0) -> a\n");
    blocked("$ F : @Type 1 = @Type 1 -> Nat\n", "expected `@Type 1`, found `@Type 2`");
}

// Test [Fun]
#[test]
fn fun() {
    applies("$ f : Nat -> Nat = \\n => Nat.Succ.{ n }\n");
    blocked("$ f : Nat = \\(n: Nat) => n\n", "expected `Nat`, found `Nat -> Nat`");
}

// Test [App]
#[test]
fn app() {
    applies("$ n : Nat = add two Nat.Zero\n");
    blocked("$ n : Nat = add Bool.True Nat.Zero\n", "expected `Nat`, found `Bool`");
}

// Test [Beta]
#[test]
fn beta() {
    applies("$ p : P Nat.Succ.{ Nat.Zero } = @axiom\n$ q : P ((\\(n: Nat) => Nat.Succ.{ n }) Nat.Zero) = p\n");
    blocked("$ p : P Nat.Succ.{ Nat.Zero } = @axiom\n$ q : P ((\\(n: Nat) => n) Nat.Zero) = p\n", "expected `P Nat.Zero`");
}

// Test [Eta-Pi]
#[test]
fn eta_pi() {
    applies("$ f : Nat -> Nat = @axiom\n$ Q : (Nat -> Nat) -> @Type 1 = @axiom\n$ p : Q f = @axiom\n$ q : Q (\\n => f n) = p\n");
    blocked("$ f : Nat -> Nat = @axiom\n$ Q : (Nat -> Nat) -> @Type 1 = @axiom\n$ p : Q f = @axiom\n$ q : Q (\\n => f Nat.Zero) = p\n", "expected `Q");
}

// Test [Let]
#[test]
fn let_() {
    applies("$ p : P Nat.Succ.{ Nat.Zero } = @axiom\n$ q : P (let n: Nat = Nat.Zero in Nat.Succ.{ n }) = p\n");
    blocked("$ p : P Nat.Succ.{ Nat.Zero } = @axiom\n$ q : P (let n: Nat = Nat.Zero in n) = p\n", "expected `P Nat.Zero`");
}

// Test [Proof-Irrelevance]
#[test]
fn proof_irrelevance() {
    let proofs = "$ a : A = @axiom\n$ b : A = @axiom\n$ Q : A -> @Type 1 = @axiom\n$ q : Q a = @axiom\n$ r : Q b = q\n";
    applies(&format!("$ A : @Type 0 = @axiom\n{proofs}"));
    blocked(&format!("$ A : @Type 1 = @axiom\n{proofs}"), "expected `Q b`, found `Q a`");
}

// ## Pairs, truth and falsity

// Test [Sigma-Form]
#[test]
fn sigma_form() {
    applies("$ S : @Type 1 = {Nat, Nat}\n$ E : @Type 0 = {@Top, @Top}\n");
    blocked("$ S : @Type 1 = {@Type 1, Nat}\n", "expected `@Type 1`, found `@Type 2`");
}

// Test [Sigma-Pair]
#[test]
fn sigma_pair() {
    applies("$ s : {Nat, Nat} = {Nat.Zero, Nat.Succ.{ Nat.Zero }}\n$ p : P Nat.Succ.{ Nat.Zero } = @axiom\n$ q : P s.1 = p\n");
    blocked("$ s : {Nat, Nat} = {Nat.Zero, Nat.Succ.{ Nat.Zero }}\n$ p : P Nat.Succ.{ Nat.Zero } = @axiom\n$ q : P s.0 = p\n", "expected `P Nat.Zero`");
}

// Test [Eta-Sigma]
#[test]
fn eta_sigma() {
    let pair = "$ s : {Nat, Nat} = @axiom\n$ Q : {Nat, Nat} -> @Type 1 = @axiom\n$ p : Q s = @axiom\n";
    applies(&format!("{pair}$ q : Q {{s.0, s.1}} = p\n"));
    blocked(&format!("{pair}$ q : Q {{s.1, s.0}} = p\n"), "expected `Q");
}

// Test [Top]
#[test]
fn top() {
    applies("$ t : @Top = @tt\n");
    blocked("$ t : @Bottom = @tt\n", "expected `@Bottom`, found `@Top`");
}

// Test [Bottom]
#[test]
fn bottom() {
    applies("$ f : @Bottom -> Nat = \\e => (e |> @absurd : Nat)\n");
    blocked("$ f : @Top -> Nat = \\e => (e |> @absurd : Nat)\n", "expected `@Bottom`, found `@Top`");
}

// ## Equality

// Test [Eq-Form]
#[test]
fn eq_form() {
    applies("$ E : @Type 0 = Nat.Zero ~ Nat.Succ.{ Nat.Zero }\n");
    blocked("$ E : @Type 0 = Nat.Zero ~ Bool.True\n", "expected `Nat`, found `Bool`");
    blocked("$ E : @Type 0 = @tt ~ @tt\n", "equality is not formed at the proposition `@Top`");
}

// Test [Eq-Box]
#[test]
fn eq_box() {
    applies("$ t : (u: {Nat, @Top}) -> (v: {Nat, @Top}) -> u.0 ~ v.0 -> u ~ v = \\e => {e, @tt}\n");
    blocked("$ t : (u: {Nat, @Top}) -> (v: {Nat, @Top}) -> u ~ v = {@tt, @tt}\n", "expected `u.0 ~ v.0`, found `@Top`");
}

// Test [Eq-Stuck]
#[test]
fn eq_stuck() {
    let maybe_proofs = "@ctx {u: @l} -> (A: @Type u) -> (a b: A)";
    applies(&format!("$ r : @ctx {{u: @l}} -> (a2: @Type u) -> (a: a2) -> (b: a2) -> a ~ a = @refl a\n"));
    // `@Type u` may be the propositions, but is not known to be.
    blocked(&format!("$ r : @ctx {{u: @l}} -> (a2: @Type u) -> (a: a2) -> (b: a2) -> a ~ b = @tt\n"), "expected `a ~ b`, found `@Top`");
}

// Test [Eq-Data-Stuck]
#[test]
fn eq_data_stuck() {
    applies("$ r : (a: @Type 1) -> List @ctx {.u = 0} a ~ List @ctx {.u = 0} a = @refl (List @ctx {.u = 0} a)\n");
    let lists = "(A B: @Type 1) -> List @ctx {.u = 0} A ~ List @ctx {.u = 0} B";
    blocked(&format!("$ inj : (a: @Type 1) -> (b: @Type 1) -> List @ctx {{.u = 0}} a ~ List @ctx {{.u = 0}} b -> a ~ b = \\e => e\n"), "expected `a ~ b`, found `List @ctx {.u = 0} a ~ List @ctx {.u = 0} b`");
}

// Test [Refl]
#[test]
fn refl() {
    applies("$ t : add two two ~ four = @refl four\n");
    blocked("$ t : add two two ~ two = @refl two\n", "expected `@Bottom`");
}

// Test [Transport]
#[test]
fn transport() {
    let pre = "$ Q : Nat -> @Type 0 = @axiom\n";
    applies(&format!("{pre}$ tr : (m: Nat) -> (n: Nat) -> m ~ n -> Q m -> Q n = \\e q => @transp m (\\k => Q k) q n e\n"));
    blocked(&format!("{pre}$ tr : (m: Nat) -> (n: Nat) -> m ~ n -> Q m -> Q n = \\e q => @transp n (\\k => Q k) q m e\n"), "expected `Q n`, found `Q m`");
}

// Test [Cast]
#[test]
fn cast() {
    applies("$ c : (a2: @Type 1) -> (b: @Type 1) -> a2 ~ b -> a2 -> b = \\e a => @cast a2 b e a\n");
    blocked("$ c : (a2: @Type 1) -> (b: @Type 1) -> a2 ~ b -> a2 -> b = \\e a => @cast a2 b @tt a\n", "found `@Top`");
}

// Test [Eq-Fun]
#[test]
fn eq_fun() {
    applies("$ fe : (f: Nat -> Nat) -> (g: Nat -> Nat) -> ((n: Nat) -> f n ~ g n) -> f ~ g = \\h => h\n");
    blocked("$ fe : (f: Nat -> Nat) -> (g: Nat -> Nat) -> f Nat.Zero ~ g Nat.Zero -> f ~ g = \\h => h\n", "found `f Nat.Zero ~ g Nat.Zero`");
}

// Test [Eq-Pair]
#[test]
fn eq_pair() {
    applies("$ t : (a: Nat) -> (b: Nat) -> a ~ b -> ({a, Nat.Zero} : {Nat, Nat}) ~ {b, Nat.Zero} = \\e => {e, @tt}\n");
    blocked("$ t : (a: Nat) -> (b: Nat) -> a ~ b -> ({a, Nat.Zero} : {Nat, Nat}) ~ {b, Nat.Succ.{ Nat.Zero }} = \\e => {e, @tt}\n", "expected `@Bottom`");
}

// Test [Eq-Omega]
#[test]
fn eq_omega() {
    let pre = "$ A : @Type 0 = @axiom\n$ B : @Type 0 = @axiom\n";
    applies(&format!("{pre}$ ext : (A -> B) -> (B -> A) -> A ~ B = \\f g => {{f, g}}\n"));
    blocked(&format!("{pre}$ ext : (A -> B) -> A ~ B = \\f => f\n"), "expected `{A -> B, B -> A}`, found `A -> B`");
}

// Test [Eq-Univ]
#[test]
fn eq_univ() {
    applies("$ t : @Type 1 ~ @Type 1 = @tt\n");
    blocked("$ t : @Type 1 ~ (Nat -> @Type 1) = @tt\n", "expected `@Bottom`, found `@Top`");
}

// Test [Eq-Univ-Neq]
#[test]
fn eq_univ_neq() {
    applies("$ t : Nat ~ (Nat -> Nat) -> @Bottom = \\e => e\n$ l : (@Type 1 -> Nat) ~ (Nat -> @Type 1) -> @Bottom = \\e => e\n");
    blocked("$ t : Nat ~ Nat -> @Bottom = \\e => e\n", "expected `@Bottom`, found `@Top`");
}

// Test [Eq-Pi]
#[test]
fn eq_pi() {
    applies("$ t : (Nat -> Nat) ~ (Nat -> Nat) = {@tt, \\_ => @tt}\n");
    blocked("$ t : (Nat -> Nat) ~ (Nat -> Bool) = {@tt, \\_ => @tt}\n", "expected `@Bottom`, found `@Top`");
}

// Test [Eq-Sigma]
#[test]
fn eq_sigma() {
    applies("$ t : {Nat, Nat} ~ {Nat, Nat} = {@tt, \\_ => @tt}\n");
    blocked("$ t : {Nat, Nat} ~ {Nat, Bool} = {@tt, \\_ => @tt}\n", "expected `@Bottom`, found `@Top`");
}

// Test [Eq-Ctor]
#[test]
fn eq_ctor() {
    applies("$ t : (m: Nat) -> (n: Nat) -> m ~ n -> Nat.Succ.{ m } ~ Nat.Succ.{ n } = \\e => e\n");
    blocked("$ t : Nat.Zero ~ Nat.Succ.{ Nat.Zero } = @tt\n", "expected `@Bottom`, found `@Top`");
}

// Test [Eq-Univ-Data]
#[test]
fn eq_univ_data() {
    applies("$ t : Nat ~ Nat = @tt\n");
    blocked("$ t : Nat ~ Bool = @tt\n", "expected `@Bottom`, found `@Top`");
}

// Test [Data-Eq-Projection]
#[test]
fn data_eq_projection() {
    let lists = "(A B: @Type 1) -> List @ctx {.u = 0} A ~ List @ctx {.u = 0} B";
    let sig = applies(&format!("$ inj : (a: @Type 1) -> (b: @Type 1) -> List @ctx {{.u = 0}} a ~ List @ctx {{.u = 0}} b -> a ~ b = \\e => List.eq_Cons_h @ctx {{.u = 0}} a b e\n"));
    // A projection is part of the theory, not a postulate.
    assert_eq!(kernel::axioms(&sig, "inj"), Some(Vec::new()));
    // Only the field types are equal, not the parameters: `X` is not a field.
    let family = "$ D : (x2: @Type 1 -> @Type 1) -> @Type 1 = @union Mk: {x: x2 Nat}\n";
    applies(&format!("{family}$ f : (x2: @Type 1 -> @Type 1) -> (y: @Type 1 -> @Type 1) -> D x2 ~ D y -> x2 Nat ~ y Nat = \\e => D.eq_Mk_x x2 y e\n"));
    blocked(
        &format!("{family}$ f : (x2: @Type 1 -> @Type 1) -> (y: @Type 1 -> @Type 1) -> D x2 ~ D y -> x2 ~ y = \\e => D.eq_Mk_x x2 y e\n"),
        "expected `(_: @Type 1) -> x2 _ ~ y _`, found `x2 Nat ~ y Nat`",
    );
}

// Test [Eq-Quot-Class]
#[test]
fn eq_quot_class() {
    applies("$ t : class Nat.Zero ~ class two = @tt\n");
    blocked("$ t : class Nat.Zero ~ class Nat.Succ.{ Nat.Zero } = @tt\n", "the claim `R Nat.Zero Nat.Succ.{ Nat.Zero }` computes to `@Bottom`");
}

// Test [Eq-Quot]
#[test]
fn eq_quot() {
    applies("$ t : Parity ~ Parity = {@tt, \\x y => {\\r => r, \\r => r}}\n");
    blocked("$ t : Parity ~ Nat = @tt\n", "expected `@Bottom`, found `@Top`");
}

// ## Cast

// Test [Cast-Pi]
#[test]
fn cast_pi() {
    let sig = applies("$ f : Nat -> Nat = @cast (Nat -> Nat) (Nat -> Nat) {@tt, \\_ => @tt} (\\n => Nat.Succ.{ n })\n");
    assert!(normal(&sig, "f").starts_with('\\'), "{}", normal(&sig, "f"));
    blocked("$ f : Nat -> Nat = @cast (Nat -> Nat) (Nat -> Bool) {@tt, \\_ => @tt} (\\n => Nat.Succ.{ n })\n", "expected `@Bottom`, found `@Top`");
}

// Test [Cast-Sigma]
#[test]
fn cast_sigma() {
    let sig = applies("$ s : {Nat, Nat} = @cast {Nat, Nat} {Nat, Nat} {@tt, \\_ => @tt} {Nat.Zero, two}\n");
    assert_eq!(normal(&sig, "s"), "{Nat.Zero, Nat.Succ.{ Nat.Succ.{ Nat.Zero } }}");
    blocked("$ s : {Nat, Nat} = @cast {Nat, Nat} {Nat, Bool} {@tt, \\_ => @tt} {Nat.Zero, two}\n", "expected `@Bottom`, found `@Top`");
}

// Test [Cast-Univ]
#[test]
fn cast_univ() {
    let sig = applies("$ T : @Type 1 = @cast (@Type 1) (@Type 1) @tt Nat\n$ n : T = Nat.Zero\n");
    assert_eq!(normal(&sig, "T"), "Nat");
    blocked("$ T : @Type 1 = @cast (@Type 1) (@Type 1) @tt Nat\n$ n : T = Bool.True\n", "the expected type computes to `Nat`");
}

// Test [Cast-Ctor]
#[test]
fn cast_ctor() {
    let sig = applies("$ n : Nat = @cast Nat Nat @tt Nat.Succ.{ Nat.Zero }\n");
    assert_eq!(normal(&sig, "n"), "Nat.Succ.{ Nat.Zero }");
    blocked("$ n : Nat = @cast Bool Nat @tt Bool.True\n", "expected `@Bottom`, found `@Top`");
}

// Test [Cast-Quot]
#[test]
fn cast_quot() {
    let sig = applies("$ e : Parity ~ Parity = @axiom\n$ c : Parity = @cast Parity Parity e (class Nat.Zero)\n");
    assert_eq!(normal(&sig, "c"), "@qin Nat.Zero");
    blocked("$ c : Parity = @cast Nat Parity @tt Nat.Zero\n", "expected `@Bottom`, found `@Top`");
}

// Test [Cast-Refl]
#[test]
fn cast_refl() {
    applies("$ m : Nat = @axiom\n$ e : Nat ~ Nat = @axiom\n$ p : P m = @axiom\n$ q : P (@cast Nat Nat e m) = p\n");
    let pre = "$ A : @Type 1 = @axiom\n$ e : A ~ Nat = @axiom\n$ a : A = @axiom\n$ m : Nat = @axiom\n$ p : P m = @axiom\n";
    blocked(&format!("{pre}$ q : P (@cast A Nat e a) = p\n"), "expected `P (@cast A Nat @irrelevant a)`, found `P m`");
}

// Test [Proof-Witness]
#[test]
fn proof_witness() {
    let sig = applies("$ t : add two two ~ four = @refl four\n");
    assert_eq!(normal(&sig, "t"), "@irrelevant");
    blocked("$ t : add two two ~ two = @refl four\n", "expected `@Bottom`");
}

// ## Inductive types

// Test [Data-Form]
#[test]
fn data_form() {
    applies("$ Tree : @Type 1 = @union Leaf: {}, Node: {Tree, Nat, Tree}\n");
    blocked("$ Big : @Type 1 = @union Mk: @Type 1\n", "too large");
    blocked("$ Yes : @Type 0 = @union Yes: {}\n", "inductive propositions are not supported");
}

// Test [Data-Ctor]
#[test]
fn data_ctor() {
    applies("$ xs : List @ctx {.u = 0} Nat = List.Cons.{ two, List.Nil }\n");
    blocked("$ n : Nat = Nat.Succ.{ Bool.True }\n", "expected `Nat`, found `Bool`");
}

// Test [Data-Elim]
#[test]
fn data_elim() {
    applies("$ pred : Nat -> Nat = \\n => Nat.elim @ctx {.m = 1} (\\_ => Nat) Nat.Zero (\\k _ => k) n\n");
    blocked("$ pred : Nat -> Nat = \\n => Nat.elim @ctx {.m = 1} (\\_ => Nat) Nat.Zero (\\k => k) n\n", "expected `Nat -> Nat`, found `Nat`");
}

// Test [Data-Ford]
#[test]
fn data_ford() {
    let vec = r"
$ Vec : (a: @Type 1) -> (n: Nat) -> @Type 1 = @union Vnil: {} -> Vec a Nat.Zero, Vcons: {m: Nat, h: a, t: Vec a m} -> Vec a Nat.Succ.{ m }
$ vlength : (a: @Type 1) -> (n: Nat) -> Vec a n -> Nat = \v => Vec.elim @ctx {.m = 1} a (\_ _ => Nat) Nat.Zero (\m h t r => Nat.Succ.{ r }) n v
";
    let sig = applies(&format!("{vec}$ one : Vec Nat Nat.Succ.{{ Nat.Zero }} = Vec.Vcons.{{ Nat.Zero, two, (Vec.Vnil : Vec Nat Nat.Zero) }}\n$ n : Nat = vlength Nat Nat.Succ.{{ Nat.Zero }} one\n"));
    assert_eq!(normal(&sig, "n"), "Nat.Succ.{ Nat.Zero }");
    blocked(&format!("{vec}$ bad : Vec Nat Nat.Succ.{{ Nat.Zero }} = (Vec.Vnil : Vec Nat Nat.Zero)\n"), "expected `Vec Nat Nat.Succ.{ Nat.Zero }`, found `Vec Nat Nat.Zero`");
}

// Test [Data-Iota]
#[test]
fn data_iota() {
    applies("$ p : P (add two two) = @axiom\n$ q : P four = p\n");
    blocked("$ p : P (add two two) = @axiom\n$ q : P two = p\n", "expected `P two`, found `P (add two two)`");
}

// Test [Positivity-Restricted]
#[test]
fn positivity_restricted() {
    applies("$ Rose : @Type 1 = @union Leaf: {}, Node: {Rose, Rose}\n");
    blocked("$ Bad : @Type 1 = @union Mk: {Bad -> Bad}\n", "may only occur as the result of a field");
    blocked("$ Nest : @Type 1 = @union Mk: List @ctx {.u = 0} Nest\n", "may only occur as the result of a field");
}

// Test [Positivity-Branching]
#[test]
fn positivity_branching() {
    // A countable ordinal and the length of its leftmost branch.
    let ord = r"
$ Ord : @Type 1 = @union Oz: {}, Os: Ord, Lim: {f: Nat -> Ord}
$ left : Ord -> Nat = \o => Ord.elim @ctx {.m = 1} (\_ => Nat) Nat.Zero (\_ r => Nat.Succ.{ r }) (\_ r => Nat.Succ.{ r Nat.Zero }) o
$ n : Nat = left Ord.Lim.{ \k => Nat.elim @ctx {.m = 1} (\_ => Ord) Ord.Oz (\_ r => Ord.Os.{ r }) k }
";
    let sig = applies(ord);
    assert_eq!(normal(&sig, "n"), "Nat.Succ.{ Nat.Zero }");
    // A W-type: the branching depends on an earlier field.
    let w = r"
$ W : (a2: @Type 1) -> (b: a2 -> @Type 1) -> @Type 1 = @union Sup: {a: a2, f: b a -> W a2 b}
$ size : (a2: @Type 1) -> (b: a2 -> @Type 1) -> W a2 b -> Nat = \w => W.elim @ctx {.m = 1} a2 b (\_ => Nat) (\a f r => Nat.Succ.{ Nat.Zero }) w
";
    applies(w);
    // An index that depends on the branch.
    let indexed = r"
$ T : (n: Nat) -> @Type 1 = @union Tl: {m: Nat} -> T m, Tn: {f: (k: Nat) -> T k} -> T Nat.Zero
$ depth : (n: Nat) -> T n -> Nat = \t => T.elim @ctx {.m = 1} (\_ _ => Nat) (\_ => Nat.Zero) (\f r => Nat.Succ.{ r two }) n t
$ d : Nat = depth Nat.Zero T.Tn.{ \k => T.Tl.{ k } }
";
    let sig = applies(indexed);
    assert_eq!(normal(&sig, "d"), "Nat.Succ.{ Nat.Zero }");
    // The hypothesis is a function, not a value.
    blocked(
        &format!("{ord}$ bad : Ord -> Nat = \\o => Ord.elim @ctx {{.m = 1}} (\\_ => Nat) Nat.Zero (\\_ r => Nat.Succ.{{ r }}) (\\_ r => Nat.Succ.{{ r }}) o\n"),
        "expected `Nat`, found `Nat -> Nat`",
    );
    blocked("$ Bad : @Type 1 = @union Mk: {(Bad -> Nat) -> Bad}\n", "may only occur as the result of a field");
    blocked("$ Bad : @Type 1 = @union Mk: {Nat -> List @ctx {.u = 0} Bad}\n", "may only occur as the result of a field");
}

// ## Quotients

// Test [Quot-Form]
#[test]
fn quot_form() {
    applies("$ Q : @Type 1 = @Quot Nat (\\x y => @Top) (\\x => @tt) (\\x y e => @tt) (\\x y z e f => @tt)\n");
    blocked("$ Q : @Type 1 = @Quot Nat (\\x y => @Bottom) (\\x => @tt) (\\x y e => e) (\\x y z e f => e)\n", "expected `@Bottom`, found `@Top`");
}

// Test [Quot-Intro]
#[test]
fn quot_intro() {
    applies("$ c : Parity = @qin four\n");
    blocked("$ c : Parity = @qin Bool.True\n", "expected `Nat`, found `Bool`");
}

// Test [Quot-Elim]
#[test]
fn quot_elim() {
    applies("$ flip : Parity -> Bool = \\q => @qelim (\\_ => Bool) (\\n => not (even n)) (\\x y e => @transp (even x) (\\b => not (even x) ~ not b) (@refl (not (even x))) (even y) e) q\n");
    blocked("$ leak : Parity -> Nat = \\q => @qelim (\\_ => Nat) (\\n => n) (\\x y e => e) q\n", "~ y`, found");
}

// Test [Quot-Beta]
#[test]
fn quot_beta() {
    let sig = applies("$ b : Bool = parity (class four)\n");
    assert_eq!(normal(&sig, "b"), "Bool.True");
    blocked("$ q : Parity = @axiom\n$ Q : Bool -> @Type 1 = @axiom\n$ t : Q Bool.True = @axiom\n$ u : Q (parity q) = t\n", "expected `Q (");
}
