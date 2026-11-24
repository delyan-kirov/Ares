# Interfaces, `@Class` and instance fields

Status: **implemented** (issue #213; instance fields moved into `@ctx`, and
interfaces to the kind `@Class`, in #573). This replaces both the old by-name
`@ctx` design and function overloading, which is gone.

Ares has two polymorphism mechanisms: generics, and interfaces resolved by type.
There used to be a third, function overloading, and it made a name's type
dishonest: `:type to_string` printed `to_string : a`, and `$ _ = to_string` failed
with a `RUNTIME_FAULT` instead of a type error. One name now has one definition and
one type.

## The whole mechanism

An interface is a `@struct` declared at the kind `@Class`, whose fields are its
operations. Implementing it is defining a value of that type: a global whose type
is a `@Class` is an instance (`impl_X_for_Y` is a naming convention only). A
function that needs one names it in its `@ctx`, as a field like any other. The
fields are in scope by name in the body, and call sites do not write them.

```
$ IToString : (t: @Type) -> @Class = @struct show: t -> @Str,

$ to_string : @ctx {t: @Type, d: IToString t} -> t -> @Str = \x => d.show x

$ impl_IToString_for_int : IToString @Int = .{ .show = int_to_str }

$ a : @Str = to_string 1                         # the field is found by type
$ b : @Str = to_string @ctx {.d = show_hex} 255  # or written by hand
```

`@type_of "to_string"` gives `@ctx {d: IToString a} -> a -> @Str`. The caller-visible
type is the arrow without the context, so `to_string 1` is a complete call.

**One rule: the sort of a `@ctx` field's type decides how it is solved.**

| field's sort | solved by |
| --- | --- |
| `@Type`, `@Nat`, `@Row`, levels `@l` | unification |
| `@Class` | instance search |
| `@Type 0` (propositions) | a decision procedure (#540, not yet) |

`@Class` is an elaborator sort. Past the search a dictionary is a record, so the
kernel sees `@Type`: no kernel rule, ledger row or Lean change goes with it.

Rules, all of them:

1. **Any number of `@ctx` parameters, anywhere on the signature's arrows**, each
   with one or more named fields: `@ctx {t: @Type, o: IOrd t, s: ISub t, z: IZero t} -> t -> t`
   or `t -> @ctx {d: IEq t} -> t -> Bool`. Field names are unique across the
   signature, and `@ctx {}` is an error. Internally every instance field travels
   in ONE leading bundle (the field itself, or a tuple of them) that the call site
   BUILDS, so no global of the bundled type has to exist. `@ctx` stands only on a
   global definition's own signature, not inside a parameter's type, an annotation
   or a field type (no higher-rank instance parameters), and not yet on a local
   `let`. A constructor's or effect operation's own `@ctx` takes no instance.
2. **An instance field's type is a `@Class`.** An ordinary record is never
   searched, so `@ctx {d: Show t}` with `Show` at `@Type` is a declaration error
   that says to declare `Show` at `@Class`. A field of a base or function type
   (`@ctx {d: @Int}`, `@ctx {d: a -> a -> Ordering}`) is a value, which needs
   dependent types: once grounded it would mean "any value of this type in scope",
   a search over every value.
3. **Resolution happens at the enclosing definition's boundary**, after numeric
   defaulting, so `1 + 2` has `t` pinned to `@Int` before any search runs. Within
   one `@ctx`, the unification fields are solved before the instance fields are
   searched.
4. **Search order**: the innermost matching local binder whose type is a `@Class`
   first (this includes the enclosing definition's own instance fields, which is
   what makes generic code chain without writing anything), then the instances in
   scope. Exactly one must match: zero and two are both errors, because global
   scope is flat. There is no backtracking: the one match is committed.
5. **Rigid heads only.** A requirement is matched only once its head is a
   constructor. One stuck on an unsolved variable waits for inference to pin it,
   and is reported as not determined if it never is, rather than guessed.
6. **Recursive resolution terminates.** A matching instance may itself take
   instance fields (`$ impl_IEq_for_vec : @ctx {t: @Type, d: IEq t} -> IEq (@Vec t)`),
   so resolution recurses into them. Each such field must be smaller than the
   instance's type (the Paterson conditions: fewer constructors and variables,
   and no variable more often), checked at the instance's declaration, so the
   recursion always ends. A depth of 32 stays as a backstop that well-formed code
   never reaches.
7. **No overlapping instances.** A ground instance and a generic one that both
   match is an ambiguity error, not most-specific-wins.
8. **Partial grounding is allowed.** The search unifies, so a unique match may pin
   the requirement's remaining variables. This is how `[lo ... hi]` finds its
   target type. Rule 2 keeps it from degenerating.
9. **Explicit form**: `f @ctx {.d = e} x`. It names the fields it supplies, by
   name, instances and types alike; omitted fields are still solved (an exception
   to the struct-literal "every field" rule). It goes where its parameter stands
   in the signature, before the explicit argument that follows it, and a field it
   does not know is an error with a did-you-mean.
10. **Proofs never go through instance search.** A proposition field goes to a
   decision procedure (#540); a lemma-shaped instance would make the search a
   Prolog prover.

Five diagnostics, each with its own escape:

- *not determined here*: the requirement is still open at the boundary
  (`$ g : @ctx {a: @Type} -> a -> a = \x => foo x`). Annotate the call, or declare an
  instance field of that type on `g` so chaining applies. The constraint is never
  inferred and added to `g`'s type silently; that would reintroduce the dishonesty.
- *no value of type `I T` is in scope*: define an instance.
- *ambiguous*: two instances of one grounded type. Annotation cannot help, so the
  note offers the explicit `f @ctx {.d = e}` form, or removing one.
- *never searched*: rule 2, at the declaration.
- *not smaller*: rule 6, at the instance.

## Elaboration

The parser gathers a signature's instance fields into one leading parameter and
binds them by name ahead of the body's own parameters (`\x y => e` becomes
`\d x y => e`, or `\{o, s, z} x => e` for several fields). `Desugarer::def`
then treats it as an ordinary first parameter, and every use site injects the
resolved value as a leading argument (`apply_ctx`). A resolved
context is a `CtxVal`: a bare local name, a qualified global, an instance applied to
the context resolved for it, a tuple built here, a projection out of a bundle
already in scope, or an explicit expression. The backends need no support at all.

The middle end then removes the dispatch wherever the instance is known
statically (`passes/specialize.rs`, issue #383). A call that passes a
context-taking function a global instance, a bundle of them, or an instance function applied to
one, calls a clone of the function with that instance substituted, memoized per
(function, instance). Inside the clone, `d.method` reads the known literal: a
lambda method is lifted to a global (`impl_IEq_for_Pt#f_eq`) and called directly,
and `eta_fold` turns a primitive one (`impl_IAdd_for_int#f_add`) into the
intrinsic. A generic function's calls to other context-taking functions with the same
instance chain into their clones, and a recursive call reaches the clone itself.
Only a clone whose body is a value is made (it becomes a global, evaluated once),
and the instance nesting depth and the number of clones are capped.

## What CORE provides

Arithmetic is one interface per operation, so a type implements exactly what it
has (`Money` adds but does not divide): `IAdd ISub IMul IDiv IMod IZero IOne IPow`.
An operator takes ONE type for both operands, so mixed-width arithmetic is written
explicitly (`@cast`, `f32_to_f64`, `ARES.of_real`); the 220 mixed-width operator
pairs are gone.

Comparison is `IEq` and `IOrd`. There is no structural fallback for `==`: a type
needs an `IEq` instance, by hand or from `ARES.derive_eq` / `derive_ord`. CORE has
instances for the base types, tuples, `@Vec`, `@Array` and `Cpx`.

The rest: `IToString` / `IFromString` (which `"?(e)"` interpolation uses), `ICat`
(`++`), `ICons` (`::`), `IFor` / `IFormap` (`for` / `formap`, whose effect row is an
ordinary interface parameter: `$ IFor : (s: @Type) -> (a: @Type) -> (e: @Row) -> @Class = @struct ...`), and `DERIVE`'s
three-way `ICmp`.

`ARES.min` / `max` / `clamp` / `abs` / `pow` are ONE definition each over these
interfaces, so they work for any type that has them, `@Str` included.

## Blessed interfaces

Ten interface types are the compiler's own: a desugar site resolves a value of the
applied type and calls its single field. Their names carry the `@` sigil, only CORE
declares them, and each has exactly one field (validated at the declaration), so
the compiler needs the type name and never the method name.

```
$ @IRange : (b: @Type) -> (t: @Type) -> @Class = @struct range: b -> b -> t,          # in CORE

$ range_span : @IRange @Int Span = .{ .range = \lo hi => Span.{ lo, hi } }
```

The set and what reaches it:

| interface | surface |
| --- | --- |
| `@IIntLit` `@IRealLit` `@IImagLit` `@IStrLit` | a literal whose expected type is a user type (or `@Code`, through CORE's `@IStrLit` instance) |
| `@ISeqLit` | `[a, b, c]` |
| `@IRange` `@IRangeFrom` | `[lo ... hi]`, `[lo ...]` |
| `@IIndex` | `recv.[i]`, `recv.[i, j]` |
| `@ISlice` | `recv.[lo ... hi]` on a non-tensor |
| `@ISeqView` | `[]` / `[a, b]` / `[a] ++ r` / `h :: t` PATTERNS (pieces before the middle) |
| `@ISeqViewBack` | `r ++ [y, z]` PATTERNS (pieces after the middle) |
| `@IInterp` `@IInterpText` `@IInterpHole` | `"a ?(x) b"` whose expected type has an `@IInterp` instance (CORE's for `@Code` make it a quotation) |

A literal PATTERN on a user type uses the construction interface plus the type's
ordinary `IEq` instance, so no separate equality hook exists.

Where nothing constrains a range's result, the FIRST instance declared wins, so
CORE's declaration order decides that a bare `[lo ... hi]` is a `@Vec` and a bare
`[lo ...]` is a `Stream`. An annotation picks any other.

These replace the `@compiler_interface_*` hook family, which was built on the
overload resolver and is deleted.

## One name, one definition

- Two definitions of a name in one module is an error.
- A local definition SHADOWS an imported one of the same name.
- A name two imports bring in has no bare meaning: using it says so and names the
  owners, and `Module.name` still reaches either.

The one thing left that picks a definition from argument types is an effect
OPERATION whose name several effects declare (`ask` in both `Reader` and `Config`),
which resolves against the ambient effect. That is not name overloading: the
operations belong to different effects, and a handler clause always qualifies.
