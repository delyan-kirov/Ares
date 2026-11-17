# The observational kernel

**Status:** prototype, plan step 1 of issue #406. A separate crate,
`crates/kernel`, that the frontend does not use yet.
**Date:** 2026-11-10.
**Scope:** what the kernel checks, the Ares it reads, how it
computes, and where it departs from the published system.

---

## 1. Purpose

Issue #406 makes Ares dependently typed with observational equality, after
Pujet and Tabareau's TT^obs ("Observational Equality: Now for Good", POPL
2022; "Impredicative Observational Equality", POPL 2023). Step 1 of its plan is
a kernel that implements the theory on its own, so the rules can be tried and
tested before the frontend's checker grows into them (steps 2 to 4).

The milestone the plan sets is rationals over a user-defined binary `Integer`
with respectful quotient elimination. It is `crates/kernel/scripts/RATIONALS.ares`.

## 2. Layout

| Module | Job |
|---|---|
| `level` | universe levels, `imax`, the case split that decides `<=` |
| `term` | core terms with de Bruijn indices, printing, shifting |
| `signature` | the checked globals and inductive declarations, and the axioms each rests on |
| `nbe` | evaluation to values and read-back (normalisation by evaluation) |
| `inductive` | constructor and recursor types, iota reduction |
| `observational` | the computation of `a ~ b` and `@cast` |
| `conversion` | typed definitional equality |
| `syntax` | lowering of a module the frontend parsed to the kernel's input |
| `check` | bidirectional elaboration of scripts into core terms |

No external crates; the parser is the frontend's. Values are `Rc`-shared
because closures capture the terms they evaluate.

## 3. The language it reads

A script is an Ares module (#473). The kernel parses it with the frontend's
parser, where types are expressions (#406 step 3, parser half), and lowers
the tree itself; the frontend's checker rejects the dependent forms until its
elaborator takes types as terms. Every argument is explicit except where a
`_` or a left-out level stands for it:

```ares
$ @mod NAT
$ id : @ctx {u: @l} -> (t: @Type u) -> t -> t = \x => x
$ Nat : @union = Zero: {}, Succ: Nat
$ add : Nat -> Nat -> Nat = \m n => Nat.elim @ctx {.m = 1} (\_ => Nat) n (\_ r => Nat.Succ.{ r }) m
$ two : Nat = Nat.Succ.{ Nat.Succ.{ Nat.Zero } }
$ four : add two two ~ Nat.Succ.{ Nat.Succ.{ two } } = @refl (add two two)
```

- `$ name : T = e` defines and `$ name : T = @axiom` postulates. A signature's leading named parameters `(x: A) ->` are bound by the signature, as in every Ares definition (#437): `id`'s body binds only `x`. A capitalized name defines a type, `$ Frac : @Type 1 = {Integer, Pos}`.
- An inductive type is a union. `$ D : @union = Tag: payload, ...` is in `@Type 1`; with parameters, indices or another universe, the signature states them and the body is the union, `$ D : (params) -> @Type l = @union ...`. A constructor may state its result, `Tag: {fields} -> D params indices`; the leading binders every constructor passes through unchanged are parameters, the rest indices: `$ Vec : (a: @Type 1) -> (n: Nat) -> @Type 1 = @union Nil: {} -> Vec a Nat.Zero, Cons: {m: Nat, h: a, t: Vec a m} -> Vec a Nat.Succ.{ m }`. A payload is `{}`, a bare type, or braced fields, named or not.
- Constructor `Tag` of `D` is the global `D.Tag`, written `D.Tag.{ fields }` (positional or `.f = e`) or `.Tag.{ fields }` when one constructor has that tag; its parameters are inferred. Each declaration adds `D.elim`, and, with parameters, the projections `D.eq_Tag_f` (`D.eq_Tag_argN` for an unnamed field).
- `@ctx {u: @l, ...} ->` at the start of a signature binds levels; a use passes them as `name @ctx {.u = l}`, or leaves them out. Kernel levels range over every level, `0` included; the surface default `n >= 1` is a kernel `k + 1`.
- Terms: `\x => e`, `\(x: A) => e`, `(x: A) -> B`, `A -> B`, `let x: T = e in b`, `(e : T)`, `a ~ b`, `f <| x` and `x |> f`. `{a, b}` is a pair where a pair type is expected and otherwise the type of pairs; `{x: A, y: B x}` is a dependent pair type; `p.0` and `p.1` project.
- Primitives: `@Type l`, `@Top`, `@tt`, `@Bottom`, `x |> @absurd` (at the type expected), `@Eq A a b`, `@refl a`, `@transp t B u t2 e`, `@cast A B e t`, `@Quot A R rr rs rt`, `@qin a`, `@qelim P f resp q`.
- An argument written `_`, and a level left out of a use, are inferred by local argument synthesis: first-order matching against the expected type and the other arguments' types, such as `trans _ _ _ e f` against `a ~ c` or `Nat.elim (\n => P n) ...`. The checker then checks the application again with the solutions by the ordinary rules, so the elaborated terms are explicit and a wrong guess only rejects (#470). Matching does not see through computation: a step that proves `a ~ b` used as `Nat.Succ.{ a } ~ Nat.Succ.{ b }` needs its endpoints written.
- `#` starts a comment.

## 4. The theory as implemented

- **Universes.** `@Type 0` is the impredicative universe of propositions; the sort of a Pi type is `imax`. Universes are not cumulative, as in CC^obs: a type lives in exactly one universe, so a type in `@Type 1` is not a type in `@Type 2` (#475).
- **Proof irrelevance.** Conversion is typed. Two values of a proposition are equal, decided from the type. Proofs are kept in the elaborated terms but evaluate to one irrelevant witness without being evaluated themselves (Note [Proofs evaluate to an irrelevant witness]). `kernel::recheck` checks a signature again from those terms alone, without the script syntax or the elaborator (#465).
- **Pi and Sigma** with eta. A Sigma of data and a proof is data (the shape a refinement desugars to).
- **Inductive types**, parameterised and indexed, in data universes, with fields that may depend on earlier fields. A recursive field is `D params indices`, or infinitely branching, `(a: A) -> D params indices`, whose induction hypothesis is a function `(a: A) -> P indices (f a)`; nested occurrences such as `List (D params)` are rejected (#467). Indexed families are stored forded, as in CIC^obs: indices become parameters and each constructor gets an equality field per index; the recursor has the indexed motive and casts each method's result to the value's indices (Note [Indexed families are forded], #466). An index's type may depend on the parameters, not on earlier indices. Each declaration adds the type former, its constructors and `D.elim`, and, when it has parameters, a projection `D.eq.c.f` per constructor field from `D a ~ D a'` to the equality of that field's types (`D.eq.c.argN` for an unnamed field), as CIC^obs's `eq_c` (#477).
- **Equality** `a ~ b` computes by its type: pointwise at Pi types (function extensionality), componentwise at Sigma types, constructor-wise at inductive types, structurally at universes (contravariant Pi domains), as the relation at quotients, and as logical equivalence at `@Type 0`. It is not formed at a proposition, since two proofs are already equal by conversion; a proof inside data, such as the second component of a pair, contributes `@Top`.
- **Cast** computes by the heads of its two types, through lambdas, pairs, constructors and classes.
- **Quotients** of data by a relation proved reflexive, symmetric and transitive. `@qelim` needs the method to respect the relation.

## 5. Departures and gaps

Every rule the kernel implements, where it comes from, what theorem covers it
and where it departs, is in the theory ledger,
[`documentation/type-theory/LEDGER.md`](LEDGER.md) (#472). The code tags
each rule's implementation with `// Rule [Name]`, and
`crates/kernel/tests/ledger.rs` keeps the two in step. The main departures:

- `@cast A B e t` is convertible with `t` when `A` and `B` are convertible (Cast-Refl of CIC^obs, a conversion rule, not a reduction). TT^obs reaches `t` only through its structure; without the rule the outer respect proof of a binary quotient operation meets a stuck cast.
- Equality between two instances of one inductive type with parameters, `D a ~ D a'`, is left stuck: computing it to `a ~ a'` would make type formers injective, which is inconsistent (#477).
- Index types that depend on earlier indices are rejected (#490), as are nested recursive fields (#467). Infinitely branching fields are in, but outside the Lean consistency proof, whose model has only `ω` stages.
- Definitions unfold eagerly, so error messages show unfolded terms. Glued evaluation would keep the names.
- No metavariables or implicit arguments: the kernel checks elaborated terms. Scripts may leave arguments to local argument synthesis (section 3), which only fills in the script before the ordinary rules check it.

## 5.1 Axioms

`kernel::axioms` lists the postulates a global rests on, transitively and
through proofs (Lean's `#print axioms`). A script pins them with a
`# axioms: a b` line above each declaration that rests on any, which
`tests/scripts.rs` checks, so a new dependence on a postulate fails a test. `RATIONALS.ares` rests on none: the
ring laws it needs are proved through unary naturals (#463).

## 6. Next steps

Plan step 2 is done: `documentation/syntax/ares.y` has one grammar for types and
expressions, and every corpus file groups as it did under the separate type
grammar. The parser in `crates/frontend` reads type positions as expressions
too (#473), which is how the kernel reads Ares; the checker still takes the
`Ty` view of them and rejects the dependent forms. Step 3 grows the
frontend's Algorithm W into a bidirectional elaborator with NbE conversion,
for which this kernel is the reference.
