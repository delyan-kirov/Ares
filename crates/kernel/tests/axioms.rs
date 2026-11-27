//! The axiom report (`kernel::axioms`, Lean's `#print axioms`) is complete:
//! `recheck` checks each global in the signature cut down to the globals it
//! rests on, whose axioms are the ones reported (issues #480 and #582).
//! See Note [The axiom report is complete].

fn checked(src: &str) -> kernel::Signature {
    let sig = kernel::check_script(src).unwrap_or_else(|e| panic!("{}", e.render(src, "test")));
    kernel::recheck(&sig).unwrap_or_else(|e| panic!("does not re-check: {e}"));
    sig
}

#[test]
fn an_inductive_type_rests_on_its_constructors() {
    let sig = checked(
        "\
$ @mod BLOCK
$ ax : @Type 1 = @axiom
$ D : @Type 2 = @union Mk: ax, Other: {}
$ t : @Type 2 = D
$ id : D -> D = \\x => x
$ other : D = D.Other
",
    );
    for name in ["D", "D.Mk", "D.Other", "D.elim", "t", "id", "other"] {
        assert_eq!(kernel::axioms(&sig, name).unwrap(), ["ax"], "`{name}`");
    }
}

#[test]
fn a_projection_rests_on_its_declaration() {
    let sig = checked(
        "\
$ @mod PROJECTION
$ ax : @Type 1 = @axiom
$ Box : (a: @Type 1) -> @Type 1 = @union Put: {v: a, w: ax}
$ t : @Type 1 -> @Type 1 = Box
",
    );
    for name in ["Box", "Box.Put", "Box.eq_Put_v", "Box.eq_Put_w", "Box.elim", "t"] {
        assert_eq!(kernel::axioms(&sig, name).unwrap(), ["ax"], "`{name}`");
    }
}

#[test]
fn an_unrelated_axiom_is_not_reported() {
    let sig = checked(
        "\
$ @mod UNRELATED
$ ax : @Type 1 = @axiom
$ Nat : @Type 1 = @union Zero: {}, Succ: Nat
$ two : Nat = Nat.Succ.{ Nat.Succ.{ Nat.Zero } }
",
    );
    for name in ["Nat", "Nat.Succ", "Nat.elim", "two"] {
        assert!(kernel::axioms(&sig, name).unwrap().is_empty(), "`{name}`");
    }
}

#[test]
fn a_global_is_cut_down_to_what_it_rests_on() {
    let sig = checked(
        "\
$ @mod CUT
$ ax : @Type 1 = @axiom
$ other : @Type 1 = @axiom
$ D : @Type 2 = @union Mk: ax, Other: {}
$ t : @Type 2 = D
$ u : @Type 1 = other
",
    );
    let name_of = |sig: &kernel::Signature, g: u32| sig.global(g).name.to_string();
    for name in sig.names() {
        let id = sig.lookup(name).unwrap();
        let (cut, at) = sig.rests_on_signature(id);
        let kept: Vec<String> = sig.rests_on(id).into_iter().map(|g| name_of(&sig, g)).collect();
        assert_eq!((0..cut.len() as u32).map(|g| name_of(&cut, g)).collect::<Vec<_>>(), kept, "`{name}`");
        assert_eq!(name_of(&cut, at), name);
        let axioms = (0..cut.len() as u32).filter(|g| matches!(cut.global(*g).kind, kernel::signature::GlobalKind::Axiom));
        assert_eq!(axioms.map(|g| name_of(&cut, g)).collect::<Vec<_>>(), kernel::axioms(&sig, name).unwrap(), "`{name}`");
    }
    assert_eq!(kernel::axioms(&sig, "t").unwrap(), ["ax"]);
    assert_eq!(kernel::axioms(&sig, "u").unwrap(), ["other"]);
}
