# 9. Effects

**Question:** how do effects and dependent types mix: what may a type depend
on, which effects threaten consistency or decidability, and where does
non-termination (`@Di`, #546) fit?

Ares has algebraic effects with deep handlers and row-typed arrows today
(`documentation/language/effect-system-design.md`); #544 gives effects
parameters of any type, and #546 makes divergence an effect. Neither the
kernel nor any proof in the ledger covers effects yet. This page collects
what the literature says, to ground those two issues.

## Comparison

| System | What a type may depend on | Effects | Non-termination |
|---|---|---|---|
| The Fire Triangle (PT20) | n/a | a no-go theorem: a type theory with substitution, dependent elimination and observable effects is inconsistent (§2.1, Theorem 1); call-by-value keeps substitution only for values (§2.2), call-by-name loses dependent elimination (§2.3) | not an observable effect in its sense, nor are printing and exceptions without handlers (§2.1, Non Example 1) |
| Dependent call-by-push-value (PT20 §2.6) | values; a `let` in the type synchronises an effectful computation with its use | value types and computation types in two universe hierarchies | n/a |
| Exceptional type theory (PT18) | anything, in CIC | call-by-name exceptions by a translation of CIC into itself: decidable and canonical, but inconsistent; a parametric layer that requires every raised exception to be caught restores consistency (abstract) | n/a |
| eMLTT (Ahm18, AGP16) | value variables only: computation types are `F A`, `Σx:A.C`, `Πx:A.C` over value types (Ahm18 §2) | fibred algebraic effects, operations indexed by values (§3) | n/a |
| Handlers in eMLTT (Ahm18 §4) | the same | conventional term-level handlers make unsound equations derivable (§4.1); handlers are typed through a user-defined algebra type (§4.2) and can define predicates on computations by handling into a universe (§7) | n/a |
| Vákár's dependent CBPV (Vak15, *not vendored*) | values; a dependent `let` needs a value restriction (as PT20 §2.6 summarises it) | general, by a categorical semantics | n/a |
| F*, Dijkstra monads (AHMM17) | pure (`Tot`) terms; an effectful computation has type `M t wp`, a monad indexed by its weakest precondition (§3, the computation types `Tot t \| M t wp`) | user-defined monads, specified by Dijkstra monads derived for free (§3) | a primitive `Div` effect for partial correctness, with strict evaluation order, is future work for its calculus (§7); F* itself has one (*not vendored*) |
| Capretta's delay monad (Cap05) | n/a | n/a | general recursion as a coinductive type of partial elements `A^ν`, a strong monad (abstract, §3); total type theory stays total because a partial function returns a delayed value |
| Idris's effects (Bra13, *not vendored*) | values | effects indexed by a resource state, checked by the type checker | n/a |

## By the criteria

1. **Published with a proof.** The Fire Triangle is the boundary: we keep
   substitution and dependent elimination, so effects must not be observable
   inside types. eMLTT and dependent CBPV do this by letting types depend
   only on values, with soundness proved by a semantics (Ahm18 §8). Capretta's
   delay monad needs nothing beyond coinductive types.
2. **Computes.** Types that depend only on values compute as before; an
   effectful term is never unfolded by conversion. A delayed value computes
   one step at a time.
3. **Fewest kernel rules.** The kernel needs no effect rules at all if
   effectful code never reaches it: the frontend checks effects, and only
   empty-row terms are elaborated into types. That is the rule #544 already
   states ("only empty-row terms are unfolded").
4. **Efficient implementation.** F* is the production precedent for a
   separation between total code, which types may compute with, and effectful
   code, which they may not. Its `Div` is the precedent for #546.
5. **Fits Ares.** Ares is call-by-value with lazy data constructors and
   row-typed effects. PT20 §2.2 says call-by-value keeps substitution only for
   values, which is the value restriction Ares gets from its rows: an arrow
   with an empty row is a value-like total function, anything else is not.

## Decision record (proposed)

**Types depend only on values and on empty-row (total) terms. The checker
unfolds a term in a type only when its row is empty, and `@Di` counts as an
effect for that rule, so a function not proved terminating never computes in
a type.** This is the eMLTT/dependent-CBPV discipline (Ahm18 §2, PT20 §2.6)
read through Ares's rows, and it keeps Ares outside the Fire Triangle (PT20
§2.1) without restricting effects anywhere else. The kernel stays effect-free:
effectful code is checked by the frontend, and only total terms reach the
kernel.

Follow-ups this suggests, not yet issues: handlers typed through an algebra
(Ahm18 §4.2) rather than term-level clauses once dependent types reach
handlers; effects indexed by values that operations update (Bra13); the delay
monad (Cap05) as the library type a `@Di` computation can be turned into, so
partial results can be passed to total code.
