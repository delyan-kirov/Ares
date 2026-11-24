//! The axiom report (`kernel::axioms`, Lean's `#print axioms`) is complete:
//! the globals a re-check reads are ones the global rests on (`recheck`
//! fails otherwise), and the re-check never resolves a name, which would
//! read a global no term names (issue #480).
//! See Note [The axiom report is complete].

use std::path::Path;

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

/// The modules the re-check runs, and the `crate::` modules each may use.
const RECHECK: &[(&str, &[&str])] = &[
    ("recheck.rs", &["check", "conversion", "inductive", "level", "nbe", "observational", "signature", "term"]),
    ("nbe.rs", &["inductive", "level", "observational", "signature", "term"]),
    ("conversion.rs", &["inductive", "level", "nbe", "observational", "signature", "term"]),
    ("observational.rs", &["inductive", "level", "nbe", "signature", "term"]),
    ("inductive.rs", &["level", "nbe", "observational", "signature", "term"]),
    ("level.rs", &[]),
    ("term.rs", &["level", "signature"]),
];

/// What the re-check takes from the elaborator's module: functions that
/// build values, not ones that read names.
const FROM_CHECK: &[&str] = &["equivalence_laws", "is_recursive_field", "respect_type"];

/// Code that resolves a name to a global.
fn resolves_a_name(code: &str) -> Option<&'static str> {
    if code.contains(".names()") {
        return Some(".names()");
    }
    if code.contains("by_name") {
        return Some("by_name");
    }
    code.match_indices(".lookup(").any(|(at, _)| !code[..at].ends_with("env")).then_some(".lookup(")
}

/// The body of the item `fn name`, up to its closing brace at column 0.
fn function<'a>(src: &'a str, name: &str) -> &'a str {
    let start = src.find(&format!("fn {name}(")).unwrap_or_else(|| panic!("check.rs has no `fn {name}`"));
    let end = src[start..].find("\n}\n").expect("a closing brace") + start;
    &src[start..end]
}

/// The modules `use crate::m::...` lines name, and for `check` the items.
fn crate_uses(src: &str) -> Vec<(String, Vec<String>)> {
    let mut out = Vec::new();
    for line in src.lines().filter_map(|l| l.strip_prefix("use crate::")) {
        assert!(!line.contains('{') || line.contains('}'), "write `use crate::{line}` on one line");
        let line = line.trim_end_matches(';');
        let (module, rest) = line.split_once("::").unwrap_or((line, ""));
        let items = rest.trim_matches(|c| c == '{' || c == '}').split(',').map(|s| s.trim().to_string()).filter(|s| !s.is_empty());
        out.push((module.to_string(), items.collect()));
    }
    out
}

#[test]
fn the_recheck_resolves_no_name() {
    let src_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut problems = Vec::new();
    for (file, allowed) in RECHECK {
        let src = std::fs::read_to_string(src_dir.join(file)).expect("a readable module");
        let code = src.split("\n#[cfg(test)]").next().unwrap();
        if let Some(how) = resolves_a_name(code) {
            problems.push(format!("{file} resolves a name with `{how}`"));
        }
        for (module, items) in crate_uses(code) {
            if !allowed.contains(&&*module) {
                problems.push(format!("{file} uses `crate::{module}`; list it in RECHECK if it resolves no name"));
            }
            if module == "check" {
                for item in items.iter().filter(|i| !FROM_CHECK.contains(&&***i)) {
                    problems.push(format!("{file} uses `check::{item}`; list it in FROM_CHECK if it resolves no name"));
                }
            }
        }
    }
    let check = std::fs::read_to_string(src_dir.join("check.rs")).expect("a readable module");
    for name in FROM_CHECK {
        if let Some(how) = resolves_a_name(function(&check, name)) {
            problems.push(format!("check::{name} resolves a name with `{how}`"));
        }
    }
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}

#[test]
fn the_name_check_sees_a_lookup() {
    assert_eq!(resolves_a_name("let id = self.sig.lookup(name)?;"), Some(".lookup("));
    assert_eq!(resolves_a_name("closest(name, self.sig.names())"), Some(".names()"));
    assert_eq!(resolves_a_name("Term::Var(ix) => env.lookup(*ix),"), None);
}
