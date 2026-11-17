//! A prototype kernel for the dependent type theory of issue #406:
//! observational equality after Pujet and Tabareau's TT^obs ("Observational
//! Equality: Now for Good", POPL 2022, and "Impredicative Observational
//! Equality", POPL 2023).
//!
//! It stands apart from the frontend's checker: it reads Ares modules through
//! the frontend's parser, where types are expressions, and checks them itself,
//! so the theory can be tried before the checker grows into it.
//!
//! * [`level`] is universe levels, with `@Type 0` the universe of
//!   propositions, and the decision procedure for `<=`.
//! * [`term`] is the core terms (de Bruijn indices) and [`signature`] the
//!   checked globals.
//! * [`nbe`] evaluates terms to values and reads them back; [`inductive`]
//!   gives the declared inductive types their recursors.
//! * [`observational`] is the computation of equality and cast.
//! * [`conversion`] decides definitional equality.
//! * [`syntax`] lowers a parsed module to the kernel's input and [`check`]
//!   elaborates it by bidirectional type checking.
//! * [`mod@recheck`] checks an elaborated signature again from its terms alone.
//!
//! Entry point: [`check_script`].

pub mod check;
pub mod conversion;
pub mod inductive;
pub mod level;
pub mod nbe;
pub mod observational;
pub mod recheck;
pub mod signature;
pub mod syntax;
pub mod term;

pub use check::check_script;
pub use recheck::{recheck, RecheckError};
pub use signature::Signature;

/// The names of the axioms global `name` depends on, transitively (Lean's
/// `#print axioms`).
pub fn axioms(sig: &Signature, name: &str) -> Option<Vec<String>> {
    let id = sig.lookup(name)?;
    Some(sig.axioms(id).into_iter().map(|a| sig.global(a).name.to_string()).collect())
}

/// The normal form of global `name`'s body, printed (for tests and tools).
pub fn normal_form(sig: &Signature, name: &str) -> Option<String> {
    let id = sig.lookup(name)?;
    let global = sig.global(id);
    let signature::GlobalKind::Definition(body) = &global.kind else {
        return None;
    };
    let value = nbe::eval(sig, &nbe::Env::new(), body);
    let term = nbe::quote_unfolded(sig, 0, &value);
    let shown = term::TermDisplay {
        sig,
        names: &[],
        level_names: &global.level_params,
        term: &term,
    };
    Some(shown.to_string())
}
