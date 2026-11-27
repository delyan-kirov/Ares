use std::rc::Rc;

use crate::check::tests::accept;
use crate::recheck;
use crate::recheck::recheck_within;
use crate::signature::{DataId, GlobalId, GlobalKind, Signature};
use crate::term::Term;

const NAT: &str = "\n$ Nat : @Type 1 = @union Zero: {}, Succ: Nat\n$ ok : Nat.Zero ~ Nat.Zero = @refl Nat.Zero\n$ bad : Nat.Zero ~ Nat.Succ.{ Nat.Zero } = @axiom\n$ two : Nat = Nat.Succ.{ Nat.Succ.{ Nat.Zero } }\n";

/// `name`'s definition body.
fn body(sig: &Signature, name: &str) -> Rc<Term> {
    match &sig.global(sig.lookup(name).unwrap()).kind {
        GlobalKind::Definition(body) => body.clone(),
        _ => panic!("`{name}` is not a definition"),
    }
}

/// Replace `name`'s kind and require a re-check to fail at `name` for a
/// reason that mentions `needle`.
fn tampered(sig: &mut Signature, name: &str, kind: GlobalKind, needle: &str) {
    let id = sig.lookup(name).unwrap();
    sig.global_mut(id).kind = kind;
    match recheck(sig) {
        Ok(()) => panic!("re-checked `{name}` after tampering"),
        Err(e) => {
            assert_eq!(e.global, name);
            assert!(e.message.contains(needle), "error does not mention `{needle}`: {e}");
        }
    }
}

#[test]
fn an_elaborated_signature_rechecks() {
    recheck(&accept(NAT)).unwrap();
}

#[test]
fn a_kept_proof_is_rechecked() {
    let mut sig = accept(NAT);
    let proof = body(&sig, "ok");
    assert!(matches!(&*proof, Term::Proof(p) if matches!(**p, Term::Refl(_))), "the proof was not kept");
    tampered(&mut sig, "bad", GlobalKind::Definition(proof), "expected `@Bottom`");
}

#[test]
fn an_erased_proof_is_not_rechecked() {
    let mut sig = accept(NAT);
    tampered(&mut sig, "ok", GlobalKind::Definition(Rc::new(Term::Irrelevant)), "erased proof");
}

#[test]
fn data_is_not_a_proof() {
    let mut sig = accept(NAT);
    let wrapped = Rc::new(Term::Proof(body(&sig, "two")));
    tampered(&mut sig, "two", GlobalKind::Definition(wrapped), "not a proposition");
}

#[test]
fn a_global_names_only_earlier_ones() {
    let mut sig = accept(NAT);
    let later = sig.lookup("two").unwrap();
    let forward = Rc::new(Term::Global(later, Rc::new([])));
    tampered(&mut sig, "ok", GlobalKind::Definition(Rc::new(Term::Proof(forward))), "not declared before it");
}

#[test]
fn a_generated_type_is_the_declarations() {
    let mut sig = accept(NAT);
    let succ = sig.lookup("Nat.Succ").unwrap();
    let zero = sig.lookup("Nat.Zero").unwrap();
    sig.global_mut(succ).ty = sig.global(zero).ty.clone();
    let e = recheck(&sig).unwrap_err();
    assert_eq!(e.global, "Nat.Succ");
    assert!(e.message.contains("does not give"), "{e}");
}

const BOX: &str = "\n$ Box : (a: @Type 1) -> @Type 1 = @union Put: {v: a, w: a}, Empty: {}\n$ t : @Type 1 -> @Type 1 = Box\n$ u : @Type 1 -> @Type 1 = Box\n";

/// The declaration whose type former is `name`.
fn data_of(sig: &Signature, name: &str) -> DataId {
    match sig.global(sig.lookup(name).unwrap()).kind {
        GlobalKind::Data(data) => data,
        _ => panic!("`{name}` is not a type former"),
    }
}

/// Require a re-check to fail at `name` for a reason that mentions `needle`.
fn rejected(sig: &Signature, name: &str, needle: &str) {
    match recheck(sig) {
        Ok(()) => panic!("re-checked `{name}` after tampering"),
        Err(e) => {
            assert_eq!(e.global, name);
            assert!(e.message.contains(needle), "error does not mention `{needle}`: {e}");
        }
    }
}

#[test]
fn a_declaration_records_its_projections() {
    let sig = accept(BOX);
    let ids: Vec<GlobalId> = ["Box.eq_Put_v", "Box.eq_Put_w"].iter().map(|n| sig.lookup(n).unwrap()).collect();
    assert_eq!(sig.data(data_of(&sig, "Box")).projections, ids);
    let nat = accept(NAT);
    assert!(nat.data(data_of(&nat, "Nat")).projections.is_empty());
    recheck(&sig).unwrap();
}

#[test]
fn a_recorded_projection_is_owned() {
    let mut sig = accept(BOX);
    let (data, t) = (data_of(&sig, "Box"), sig.lookup("t").unwrap());
    sig.data_mut(data).projections[1] = t;
    rejected(&sig, "Box", "not its global");
}

#[test]
fn recorded_projections_are_in_order() {
    let mut sig = accept(BOX);
    let data = data_of(&sig, "Box");
    sig.data_mut(data).projections.swap(0, 1);
    rejected(&sig, "Box", "not its global");
}

#[test]
fn recorded_projections_are_contiguous() {
    let mut sig = accept(BOX);
    let (data, u) = (data_of(&sig, "Box"), sig.lookup("u").unwrap());
    sig.global_mut(u).kind = GlobalKind::Projection(data, 0, 1);
    sig.data_mut(data).projections[1] = u;
    rejected(&sig, "Box", "apart from its other globals");
}

#[test]
fn every_projection_is_recorded() {
    let mut sig = accept(BOX);
    let data = data_of(&sig, "Box");
    sig.data_mut(data).projections.pop();
    rejected(&sig, "Box", "fields do not give");
}

#[test]
fn an_unrecorded_projection_is_not_the_declarations() {
    let mut sig = accept(BOX);
    let data = data_of(&sig, "Box");
    tampered(&mut sig, "t", GlobalKind::Projection(data, 0, 0), "not a projection its declaration has");
}

#[test]
fn a_type_without_parameters_records_no_projection() {
    let mut sig = accept(NAT);
    let (data, two) = (data_of(&sig, "Nat"), sig.lookup("two").unwrap());
    sig.data_mut(data).projections.push(two);
    rejected(&sig, "Nat", "fields do not give");
}

#[test]
fn a_recursor_follows_the_projections() {
    let mut sig = accept(BOX);
    let (data, elim, u) = (data_of(&sig, "Box"), sig.lookup("Box.elim").unwrap(), sig.lookup("u").unwrap());
    let recursor = sig.global(elim).kind.clone();
    sig.global_mut(u).kind = recursor;
    sig.data_mut(data).recursor = u;
    rejected(&sig, "Box", "recursor apart from its other globals");
}

const PROVED: &str = "\n$ Nat : @Type 1 = @union Zero: {}, Succ: Nat\n$ ax : Nat.Zero ~ Nat.Succ.{ Nat.Zero } = @axiom\n$ pr : (p: Nat -> @Type 0) -> p Nat.Zero -> p Nat.Succ.{ Nat.Zero } = \\h => @transp Nat.Zero (\\x => p x) h Nat.Succ.{ Nat.Zero } ax\n";

#[test]
fn a_global_holds_in_what_it_rests_on() {
    let sig = accept(PROVED);
    let pr = sig.lookup("pr").unwrap();
    let keep = sig.rests_on(pr);
    assert!(keep.len() < sig.len(), "`pr` rests on every global");
    recheck_within(&sig, &keep, pr).unwrap();
}

#[test]
fn a_global_fails_without_an_axiom_it_needs() {
    let sig = accept(PROVED);
    let (pr, ax) = (sig.lookup("pr").unwrap(), sig.lookup("ax").unwrap());
    let mut keep = sig.rests_on(pr);
    assert!(keep.remove(&ax), "`pr` does not rest on `ax`");
    let e = recheck_within(&sig, &keep, pr).unwrap_err();
    assert!(e.contains("outside its signature"), "{e}");
}
