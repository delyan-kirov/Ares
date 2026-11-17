use std::rc::Rc;

use crate::check::tests::accept;
use crate::recheck;
use crate::signature::{GlobalKind, Signature};
use crate::term::Term;

const NAT: &str = "\n$ Nat : @union = Zero: {}, Succ: Nat\n$ ok : Nat.Zero ~ Nat.Zero = @refl Nat.Zero\n$ bad : Nat.Zero ~ Nat.Succ.{ Nat.Zero } = @axiom\n$ two : Nat = Nat.Succ.{ Nat.Succ.{ Nat.Zero } }\n";

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
