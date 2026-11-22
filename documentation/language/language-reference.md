# Ares Language Reference

Every language feature, one entry each, with a simple example and a more
involved one. The examples use the language's real, current surface syntax
(branches are `if c => t else e`, matches are `scrut |> \ | pat => e ...`).
Where a feature is only partly built, the entry says so.

Every code block below is self-contained and type-checks on its own; a block
that needs a library imports it (`$ @import LA`, etc.). `cargo test` checks
each one (`crates/ares/tests/docs.rs`). The few that cannot check alone (an
error being shown, a CORE excerpt, a sketch with `...`) are fenced as
`ares-fragment`, and the test requires those to fail.

Conventions used throughout: a global is `$ name : Type = expr`; a lambda is
`\x => e` (curried: `\a b => e`); a branch is `if c => t else e`; a match is
`scrut |> \ | pat => e ...`. The comparison operators are `==` (equal),
`!=` (not equal), `<` (less), `>` (greater), `<=` (at most), `>=` (at least),
each of type `a -> a -> Bool`.

---

## Table of contents

1. Lexical structure
2. Program structure (modules, globals, imports, entry point)
3. Types
4. Expressions and syntactic sugar
5. Pattern matching
6. Algebraic data types (structs, unions, recursion)
7. Functions (currying, higher-order, interfaces, TCO)
8. Algebraic effects and handlers
9. Sized tensors and linear algebra
10. Foreign function interface
11. Compile-time evaluation
12. Intrinsic types and primitives
13. The `@`-sigil catalogue
14. Compiler CLI
15. Standard library modules
16. Dependent types (preview, checked by the kernel)

---

# 1. Lexical structure

## 1.1 Comments
A `#` starts a comment to end of line. There is no block comment.

```ares
$ x : @Int = 1   # trailing comment
# whole-line comment
```

## 1.2 Integer literals
Decimal, hexadecimal (`0x`), and binary (`0b`).

```ares
$ a   : @Int = 255
$ b   : @Int = 0xFF
$ c   : @Int = 0b1010
$ mix : @Int = 0x10 + 0b10 + 8   # bases mix freely in arithmetic
```

## 1.3 Real literals
Decimal point or scientific notation.

```ares
$ pi   : Real = 3.14159
$ tiny : Real = 12e-3        # 0.012
$ half : Real = 1.0 / 2.0     # an integer literal never becomes a real
```

## 1.4 Imaginary literals
An `i` suffix on any numeric literal form makes it imaginary. The suffixed
literal is not a base type: it desugars to the `@IImagLit` interface, whose `CORE`
instance builds the `Cpx` struct (see 15). The `i` counts as a suffix only when no
identifier character follows, so `3if` is still `3` then `if`.

```ares
$ @import ARESxCPX
$ unit : Cpx = 1.0i
$ whole: Cpx = 3i                    # the magnitude is a Real either way
$ tiny : Cpx = 2.5e-2i               # scientific notation suffixes too
$ z    : Cpx = ARES.of_real 3.4 + 1.2i  # real plus imaginary
```

An operator takes ONE type for both operands, so a real joins a complex only by
being made one: `ARES.of_real 3.4 + 1.2i`. Nothing is promoted silently, in either
direction. There is no imaginary PATTERN; match the fields (`z |> \ | Cpx.{re, im}`)
or compare with `==` in a guard.

## 1.5 String literals and escapes
A string is a block of bytes; source text must be well-formed UTF-8. Escapes:
`\n \t \r \0 \\ \" \' \a \b \f \v`, `\xHH` (one raw byte), `\u{...}` (a Unicode
scalar, UTF-8 encoded).

```ares
$ hi   : @Str = "hello\n"
$ raw  : @Str = "\x41\x42"            # "AB" via hex bytes
$ emoji: @Str = "\u{1F600} café"      # code point + raw UTF-8
```

## 1.6 String interpolation
`"... ?(expr) ..."` splices an expression into a string. `\?` is a literal `?`, so
`\?(` is not a hole; braces are ordinary characters, so JSON, SQL or JS embed as
written.

What the literal builds is decided by its expected type, as for `[..]`, ranges
and numeric literals. A `@Str`, or no expectation at all, gets the default:
each hole is stringified through `to_string` over its `IToString` instance and
the pieces are concatenated, `chunk ++ to_string expr ++ chunk`.

Simple:
```ares
$ greet : @Str -> @Str = \who => "hello ?(who)!"
```

Involved (a user type interpolates by defining an `IToString` instance):
```ares
$ Point : @Type = @struct x: @Int, y: @Int
$ impl_IToString_for_Point : IToString Point = .{ .show = \p => "(?(p.x), ?(p.y))" }
$ msg : @Str = "at ?(Point.{ .x = 3, .y = 4 }), n=?(40 + 2)"   # "at (3, 4), n=42"
```

**Building another type.** A type with an `@IInterp` instance builds the string
through a builder instead, so its holes stay structured: bound parameters,
escaping, quoting. Three blessed CORE interfaces make up the protocol:

```ares-fragment
# Declared in CORE, which alone may declare a blessed interface.
$ @IInterp     : (b: @Type) -> (t: @Type) -> @Type = @struct interp: (b -> b) -> t,   # start a builder, finish it
$ @IInterpText : (b: @Type) -> @Type = @struct text: b -> @Str -> b,    # append a literal piece
$ @IInterpHole : (b: @Type) -> (h: @Type) -> @Type = @struct hole: b -> h -> b,       # append one hole
```

`"a ?(x) b"` expected as `t` is `@IInterp`'s `interp` applied to a chain that
appends `"a "`, then `x` through the `@IInterpHole b h` instance for its type `h`,
then `" b"`. Each hole resolves its own instance, keyed on the builder and the
hole's type, so `@Int` and `@Str` holes mix with no overloading. The holes are
evaluated first, left to right, and empty pieces are skipped. The expected type
must be known at the literal (a signature, a parameter, an annotation); a string
whose type is still open is a `@Str`.

```ares
$ Param : @Type = @union PInt: @Int, PStr: @Str
$ Sql : @Type = @struct text: @Str, params: @Vec Param

$ impl_IInterp_for_Sql : @IInterp Sql Sql =
    .{ .interp = \build => build Sql.{ .text = "", .params = [] } }
$ impl_IInterpText_for_Sql : @IInterpText Sql = .{ .text = \q s => Sql.{ .text = q.text ++ s | q } }
$ impl_IInterpHole_for_Sql_Str : @IInterpHole Sql @Str = .{
    .hole = \q s =>
        let params = @vec_push q.params (Param.PStr.{ s }) in
        Sql.{ .text = q.text ++ "$" ++ to_string (@vec_len params), .params = params },
}

$ by_name : @Str -> Sql = \name =>
    "SELECT id FROM users WHERE name = ?(name)"   # text `... = $1`, params [name]
```

`examples/INTERPOLATION.ares` builds a prepared statement and escaped HTML this
way. Expected as `@Code`, a string is a quotation: source for a compile-time
splice (section 11.2).

---

# 2. Program structure

## 2.1 Module header `@mod`
Every file begins with `$ @mod NAME`. A module name is uppercase with digits, `_`,
and the inert lowercase `x` allowed (so `MAIN`, `LIST_UTIL`, `MODxA`). A module
may span several files (repeat the header).

```ares
$ @mod MAIN
```

## 2.2 Global definitions `$`
`$ name : Type = expr`. The annotation is always required, with no exceptions:
a global's type is its contract with every importer. Leaving it out is a
`TYPE_ANNOTATION_REQUIRED` error whose fix inserts the inferred type. Parts of
it may be left to the body with `_` (3.11). `$a` and `$ a` are the same.

Simple:
```ares
$ answer : @Int = 42
$ id : @ctx {t: @Type} -> t -> t = \x => x
```

Involved (definitions may appear in any order and reference each other):
```ares
$ even : @Int -> Bool = \n => if n == 0 => true else odd (n - 1)
$ odd  : @Int -> Bool = \n => if n == 0 => false else even (n - 1)
```

## 2.3 Imports `$ @import`
`$ @import MOD` brings a module's public names into scope, bare or qualified.
A qualified `MOD.symbol` needs the import too. An import brings in the whole
module, not one symbol.

A module may span several files, its PARTS. A part is the file `MODxPART.ares`
(the `x` is lowercase), which declares `$ @mod MOD`. Each part is imported on its
own, `$ @import MODxPART`, and brings in that part's names only, reached bare or
as `MOD.symbol`. The parts share one namespace: a name, private or not, and a
variant tag are defined in one part only, and a part may use what another
defines once it imports it. The standard library is the module `ARES` in parts
(`ARESxVEC`, `ARESxMAP`, `ARESxSTR`, ...).

```ares
$ @import ARESxMATH            # pi, or ARES.pi
$ @import ARESxSTR             # index_of, or ARES.index_of
```

When two imports export the same name, the bare name is ambiguous and the
qualified form picks one (`A.f`, `B.f`).

`$ @import ALIAS = MOD` imports `MOD` (or a part, `ALIAS = MODxPART`) qualified
only, under the name `ALIAS`. None of its names come into scope bare, so several
modules with overlapping names import side by side without ambiguity. Its values,
types and constructors are all reached through the alias (`V.push`,
`M.Map @Str @Int`). Writing the module's own name as the alias makes a plain
qualified-only import. Several parts of one module may share an alias.

```ares
$ @import V = ARESxVEC         # V.push, never bare push
$ @import M = ARESxMAP         # M.insert, never bare insert
$ @import M = ARESxSET         # M.add: both parts of ARES
```

An alias is one capitalized name. It may not name two modules, nor reuse the name
of another imported module, of this module, or of the built-in `C` namespace.

A name means one thing in a scope: an alias, or a module imported bare, may not
share its name with a type in scope. That keeps `A.B.{ .. }` unambiguous: it is
struct `B` of module `A` when `A` is a module or alias (`V.Box.{ 2, 3 }`, and
`V.Box.{ .w = w, .h = h }` as a pattern), and variant `B` of union `A`
otherwise (`Shape.Square.{ 3 }`).

Each `$ @import` names one module; there is no import list.

## 2.4 Visibility `$ @private`
Symbols are public by default. `$ @private` hides every symbol below it, to the
end of the file, from importers. There is no `@public` counterpart, so a
module's public interface sits above the marker.

```ares
$ api : @Int -> @Int = \x => helper x + 1
$ @private
$ helper : @Int -> @Int = \x => x * x    # module-private
```

## 2.5 Entry point
The program entry is `@main`, the one name the compiler knows, and it has exactly
one accepted signature: it takes the argument vector and returns the `@Int` exit
code, performing `@IO`. Together with `@build` (section 11.4), the compile-time
entry, those are the only `@`-names a program may define, besides the blessed
`@I*` interface types, which only `CORE` declares.

```ares
$ @main : @Vec @Str -> <@IO> @Int = \args => 0      # args[0] is the program path
```

A module without `@main` is a library: `ares check` type-checks it and runs its
compile-time assertions, and `ares run`/`build` reject it. Nothing else is
special, so a test harness is ordinary code: a check under `$ !` (section 11)
or a global some tool evaluates by name.

---

# 3. Types

## 3.1 Base numeric and string types
The word-size numbers are `@`-spelled like every other primitive: `@Int`
(signed word), `@Nat` (unsigned word). `Real` and `Str` keep friendly names.
They are distinct nullary constructors.

```ares
$ n : @Int = -5
$ u : @Nat = 5
$ r : Real = 2.5
$ s : @Str  = "hi"
```

Complex numbers are NOT a base type: `Cpx` is an ordinary `CORE` struct
(`re`/`im`), with the `i` literal suffix (1.4) and its operators supplied as
library instances. `CPX` holds the math (15).

## 3.2 Sized numerics
Fixed widths are `@`-spelled: `@Int8/@Int16/@Int32/@Int64`,
`@Nat8/@Nat16/@Nat32/@Nat64`, `@Float32/@Float64`. They are distinct from `@Int`
etc. (`@Int` and `@Int32` do not unify). Each width has its own arithmetic
instances; a literal takes the width expected of it. An operator takes ONE type for
both operands, so crossing a width is explicit (`@cast`, `f32_to_f64`).

```ares
$ w : @Int32 = 1000
$ z : @Int32 = w * 2          # @Int32 + @Int32 : @Int32
```

## 3.3 Other `@`-typed built-ins
`@Ptr` (raw pointer), `@Array` (byte block), `@Vec` (the growable vector, and
the default sequence). `Bool` is not one of them: it is a CORE union (12.1).

```ares
$ flag : Bool  = true
$ bytes: @Array = @Array.{ 8 }      # 8 zeroed bytes
$ xs   : @Vec @Int = [1, 2, 3]
```

## 3.4 Unit `{}`
The empty record type is unit; its sole value is also `{}`. Disambiguated by
position (type vs term).

```ares
$ nothing : {} = {}
$ ignore : @Int -> {} = \x => {}
```

## 3.5 Function types and effect rows
`A -> B` is a function. A row between the arrow and result lists the effects a
call may perform: `A -> <E> B`. A bare arrow is pure (empty row). `<| e>` is an
open row (a row variable), which is what makes a function effect-polymorphic.

```ares
$ State : @Effect = get : {} -> @Int, put : @Int -> {},
$ pure : @Int -> @Int = \x => x                       # pure (empty row)
$ act  : {} -> <State> @Int = get {}                  # may perform State
$ poly : @ctx {a: @Type, e: @Row, b: @Type} -> (a -> <e> b) -> a -> <e> b = \f x => f x   # effect-polymorphic
```

A parameter may be named, `(x: A) -> B`. The type is the same as `A -> B`, and
callers pass plain arguments.

A definition's signature binds the parameters it names, so the body needs no
lambda for them: a named parameter `(x: A)` binds `x`, a closed record
`{x: A, y: B}` binds its fields, and `{}` binds nothing. This covers the
leading run of such parameters (after any `@use`). The body's lambdas bind the
parameters after that run, left to right, so which parameter a lambda binds
is read off the signature alone. A record kept whole is a named parameter,
`(r: {x: A, y: B})`.

```ares
$ add   : (a: @Int) -> (b: @Int) -> @Int = a + b
$ scale : (k: @Int) -> @Int -> @Int = \x => k * x
$ norm  : {x: @Int, y: @Int} -> @Int = x * x + y * y
$ later : {} -> @Int -> @Int = \x => x + 1
```

The result type may not name the parameter yet: `(n: @Nat) -> @Tensor n @Int`
is a dependent function type, which comes with dependent types (#406).

## 3.6 Type variables and `@ctx`
A signature binds its type variables in a `@ctx` parameter, the record of what
unification solves (#537): a type `t: @Type`, a size `n: @Nat` or an effect row
`e: @Row`. A lowercase name in a type is whatever is in scope: a `@ctx` field, a
`(t: @Type)` parameter, or a global (3.10). A name nothing binds is a
`TYPE_UNBOUND` error whose fix adds it to the signature's `@ctx`, with the kind
its uses give it. A field the signature uses as a size is a `@Nat`.

```ares
$ fst : @ctx {a: @Type, b: @Type} -> {a, b} -> a = \t => t.0
$ const : @ctx {t: @Type, u: @Type} -> t -> u -> t = \x y => x
```

A caller leaves `@ctx` fields to unification, or gives some by name with an
explicit argument that mirrors the binder, `f @ctx {.t = @Int} x`; the others
are still solved. Like `@use` (7.4), `@ctx` parameters stand anywhere on a
global's signature, at least one field each, names unique across the
signature, and never inside a parameter's type, an annotation, a local `let`'s
type or a field type. An instance is a `@use` field and a type a `@ctx` one;
writing either in the other binder is an error that says so. Inside the body,
an annotation names the signature's variables, `\(x: a) => ...`.

A `(t: @Type)` or `(n: @Nat)` parameter is bound explicitly instead: the
result may name it, and each call passes it, a type (erased at run time) or a
size (passed as the `@Nat` it is).

```ares
$ ident : (t: @Type) -> t -> t = \x => x
$ seven : @Int = ident @Int 7
```

A `@Nat` field is erased unless the body needs the number: when the body reads
it as a value, or passes it to a callee that needs its own, callers pass the
size they solved it to. Such a size must then be known at the call: a literal,
or a size the caller's own `@ctx` binds. A size only the types mention, like a
slice's, is never passed, so nothing has to supply it.

```ares
$ size_of : @ctx {n: @Nat, a: @Type} -> @Tensor n a -> @Nat = \_ => n
$ three : @Nat = size_of [1, 2, 3]
```

## 3.7 Tuples
`{A, B, ...}` is a structural product of any arity. `{}` is unit, `{A}` a
one-tuple. Elements read positionally with `.0`, `.1`.

Simple:
```ares
$ p : {@Int, @Str} = {42, "answer"}
$ n : @Int = p.0
```

Involved (generic, nested, first-class):
```ares
$ swap : @ctx {a: @Type, b: @Type} -> {a, b} -> {b, a} = \t => {t.1, t.0}
$ nested : {@Int, {@Int, @Int}} = {1, {2, 3}}
$ deep : @Int = nested.1.0 + nested.1.1        # 5
```

## 3.8 Records and row polymorphism
A record type may leave its tail open with a row variable:
`{ x: @Int, y: @Int | r }` accepts any record (nominal struct or anonymous) with at
least those fields. Records are structural (unify by field name).

Simple:
```ares
$ area : @ctx {r: @Row} -> { x: @Int, y: @Int | r } -> @Int = \p => p.x * p.y
```

Involved (update preserves the open tail; `..p` extends `p` with a field):
```ares
$ shift : @ctx {r: @Row} -> { x: @Int | r } -> { x: @Int | r } = \p => { .x = p.x + 10 | p }
$ tag   : @ctx {r: @Row} -> { x: @Int | r } -> { x: @Int, t: @Int | r } = \p => { .t = 99, ..p }
```

## 3.9 Sized tensors
`@Tensor n T` is a vector of `n` elements; `n` is a type-level natural (its own
kind). A matrix is a tensor of tensors, `@Tensor m (@Tensor n T)`, which `LA`
names `Matrix m n T`. `@Tensor` heads its application (as an argument it is
parenthesized). A size is a `@Nat` term the checker evaluates: a literal, a size
variable, a `@Nat` constant (unfolded to its value), or parenthesized `+` and
`*` of them (`@Tensor (n + m) a`), decided by a canonical form. Any other term,
such as a call, needs dependent types (section 16). See section 9.

A size is inferred when it has exactly one solution once equal terms cancel:
passing a `@Tensor 5 @Int` where `@Tensor (n + 1) @Int` is expected makes `n` 4.
An equation with several solutions (`n + m = 5`) waits until another use fixes
one of its variables, and is an error if the definition ends first.

```ares
$ v : @Tensor 3 @Int = [10, 20, 30]
$ g : @Tensor 2 (@Tensor 2 @Int) = [ [1,2], [3,4] ]
$ dim : @Nat = 2
$ h : @Tensor (dim + 1) @Int = [1, 2, 3]
```

## 3.10 Type-level functions
Types are expressions (#406), so a type is named by a global whose type is
`@Type`, and a type with parameters by a function returning one. Its
signature lists the parameters, each a type (`@Type`) or a size (`@Nat`), and
its lambda binds every one. It is transparent: it unifies with its unfolding,
and errors show it as written.

Simple:
```ares
$ Count : @Type = @Int
```

A lowercase name works too (`$ pair : @Type -> @Type = \t => {t, t}`). In a
type, a lowercase name means a global in scope before it means a type
variable, unless the same type already binds it: a type-level function, or a
`@Nat` constant, which a size unfolds to its value (3.9).

Involved (partial instantiation, a size parameter):
```ares
$ Pair : (a: @Type) -> (b: @Type) -> @Type = @struct fst: a, snd: b,
$ IntPair : @Type -> @Type = \b => Pair @Int b    # fix the first arg, keep the second open
$ ip : IntPair @Str = .{ .fst = 3, .snd = "z" }  # same as Pair @Int @Str
$ Square : @Nat -> @Type -> @Type = \n t => @Tensor n (@Tensor n t)
```

A type may be computed where it is written. A `let` names a part of it, and
an applied lambda reduces to its body:
```ares
$ endo : @Type -> @Type = \t => let p = {t, t} in p -> p
$ Point : @Type = (\t => {x: t, y: t}) @Float64
```
Choosing a type by a value (`if`, a match) waits for dependent types (#406).

A type may also stand where a value does. Its type is its kind: `@Int` and
`@Int -> Bool` are `@Type`, `pair` and `@Vec` are `@Type -> @Type`, and a
size parameter takes a `@Nat`. A type carries nothing at run time, so it
erases to `{}`:
```ares
$ pair : @Type -> @Type = \t => {t, t}
$ arity : @Type -> @Int = \_ => 1
$ n : @Int = arity (pair @Str) + arity (@Int -> Bool)
```
In term position `{@Str, @Str}` is a tuple whose two items are types, of type
`{@Type, @Type}`; the product type stands there through a name, as `pair @Str`
does.
A parameter of type `@Type` is not yet in scope in the types that follow it;
that needs dependent function types (#406).

Types and values share one namespace, since a type is a global of type
`@Type`: a module may not name a type and a value alike, as it may not define
a value twice. When one import brings in a type and another a value of the
same name, the bare name is ambiguous in types and terms alike; `A.pair @Int`
and `B.pair 3` name each.

A row is not a type: an effect row or a record row is written out where it
is used.

## 3.11 Types left to elaboration `_`
`_` in a type is solved by the checker. In a global's signature it makes the
signature a shape that the body fills in (a partial signature), and the
global's type is the filled-in one. Each `_` is its own unknown.

```ares
$ succ : _ -> @Int = \x => x + 1        # succ : @Int -> @Int
$ same : @ctx {a: @Type} -> a -> _ = \x => x               # same : a -> a
$ n : @Int = let p : {_, Bool} = {3, true} in p.0
```

What `_` comes out as may use the signature's own type variables but no new
one: `$ k : _ -> @Int = \x => 3` is a `TYPE_ANNOTATION_REQUIRED` error, since
the signature would hide a type variable it never wrote. A type declaration
(`@struct`, `@union`, `@effect`, a type-level function), a foreign or builtin
signature and a signature with `@use` parameters have no body to solve one, so
`_` there is an error too. A definition whose signature has `_` cannot recurse
at another type, as one without a signature cannot.

`_` in a term (a value left to elaboration) waits for dependent types (#406).
`???` (4.12) is different: it is always an error, reporting the type it needs.

## 3.12 Universes and levels
Types are values, and a type's type is a universe `@Type n`, the types at
level `n`. Data (`@Int`, `{@Str, Bool}`, `@Int -> @Int`) lives in `@Type 1`,
and `@Type n` itself in `@Type (n + 1)`. Universes are not cumulative: a type
lives in exactly one, so `@Type 1` is in `@Type 2` and nowhere else.

```ares
$ Count : @Type 1 = @Int
$ small : @Type 2 = @Type 1
```

A bare `@Type` is level-polymorphic: each use picks its level, and the checker
infers the constraints between levels from the definition's body. A signature
names its levels in its first `@ctx`, as `u: @l` fields ahead of every
parameter, and writes `@Type u`, `@Type (u + 1)` or `@Type (@max u v)`. A
named level is the signature's own, so the body cannot fix it; a use leaves it
to unification or gives it as a `@ctx` argument.

```ares
$ id : @ctx {u: @l} -> (t: @Type u) -> t -> t = \x => x
$ three : @Int = id @ctx {.u = 1} @Int 3
```

Without an `if`, the constraints between named levels are inferred as for a
bare `@Type`. An `if` ending the `@ctx` states them exactly: `<`, `<=`, `>`,
`>=` and `==` between levels, joined by `&&`. The body may need only what the
`if` entails, and every use must meet it.

```ares
$ Both : (a: @Type) -> (b: @Type) -> @Type = {a, b}
$ same_level : @ctx {w: @l} -> (t: @Type w) -> (p: @Type w) -> @Int = 0
$ check : @ctx {u: @l, v: @l if v <= u} -> (a: @Type u) -> (b: @Type v) -> @Int = same_level (Both a b) a
```

A declared type (`@struct`, `@union`, `@effect`) lives in the universe its
signature states, and every member must fit in it. A bare `@Type` there is the
least universe that holds every member, so `List t` is at the level of `t`. A
constructor or operation that binds a type in its own `@ctx` stores a
universe, which makes its type large, and an effectful arrow `a -> <E x> b`
lives at the level of its effects too. A declared type's level names must each
be the universe of one of its parameters.

```ares
$ Pair : @ctx {u: @l} -> (a: @Type u) -> (b: @Type u) -> @Type u = @struct fst: a, snd: b,
$ Kinds : @Type 2 = @struct small: @Type 1,
```

Levels range over 1 and up. `@Type 0`, the universe of propositions, and an
`if` that lets a level reach it (`u >= 0`) come with propositions in the
frontend (#406); the kernel already has them (16).

---

# 4. Expressions and syntactic sugar

## 4.1 Lambdas
`\pat ... => e`. Parameters are juxtaposed and curried sugar. A parameter may
be an irrefutable pattern, and may carry a `: Type` annotation, always inside
parens, `(x: T)`, even when it is the only parameter, so the type ends at `)`.
(A type is an expression, so a bare annotation would swallow the next
parameter as its argument.)

```ares
$ Person : @Type = @struct name: @Str, age: @Int,
$ inc : @Int -> @Int = \x => x + 1
$ add : @Int -> @Int -> @Int = \a b => a + b                  # curried
$ name_of : Person -> @Str = \Person.{ name, _ } => name       # destructuring parameter
$ dec : @Int -> @Int = \(x: @Int) => x - 1                     # annotated parameter
$ sub : @Int -> @Int -> @Int = \(a: @Int) (b: @Int) => a - b  # one annotation per parameter
```

`\x = e` and `\x: T => e` are errors with fix-its. The three tokens have one
job each: `=` names something (`$ x = e`, `let x = e`), `=>` abstracts over a
pattern (lambdas and every kind of arm), `->` is the function type.

## 4.2 Application
Juxtaposition, left-associative, binds tighter than any operator.

```ares
$ inc : @Int -> @Int = \x => x + 1
$ add : @Int -> @Int -> @Int = \a b => a + b
$ r : @Int = add (inc 2) 3   # (add (inc 2)) 3
```

When the context fixes a call's result type, it is fixed before the arguments
are checked, so an argument sees the parameter type that result implies. With
`id : t -> t`, `$ x : Big = id 3` checks `3` against `Big` and builds it through
`Big`'s `@IIntLit` instance. Pipes are calls, so `3 |> id` and `id <| 3` do the
same. Tuples and qualified variants pass their expected type to their parts too:
`{1, 2} : {Big, Big}`, `Opt.Some.{ 1 } : Opt Big`.

## 4.3 Arithmetic and unary operators
`+ - * / %` and unary `-` (negation); boolean not is the CORE function `not`.
Standard precedence, `( )` groups.

```ares
$ a : @Int  = 1 + 2 * 3 - 4      # 3
$ b : @Int  = (1 + 2) * (3 - 4)  # -3
$ c : @Int  = -42
$ d : Bool = not true          # false
```

The bitwise operators work on every integer type: `&&&` (and), `|||` (or),
`^^^` (xor), `<<<` and `>>>` (shifts by an `@Int` count) and unary `~~~`
(complement). `&&&` and the shifts bind like `*`, `|||` and `^^^` like `+`, so
all bind tighter than a comparison. `>>>` is arithmetic on the signed types and
logical on the nats. A count of 64 or more, or a negative one, shifts every bit
out. A narrow type wraps what leaves its range.

```ares
$ e : @Int  = 12 &&& 10 ||| 1    # 9
$ f : @Int  = (0 - 16) >>> 2     # -4
$ g : @Nat8 = ~~~200             # 55
```

## 4.4 Comparisons
`==` `!=` `<` `>` `<=` `>=`, all `a -> a -> Bool`.

```ares
$ lt : Bool = 3 < 8
$ le : Bool = 8 <= 8
$ ne : Bool = 3 != 4
```

Like arithmetic, these are `CORE` functions over interfaces: `==` and `!=` over
`IEq`, the four orderings over `IOrd`, whose instances bottom out at the
comparison intrinsics (`@ieq`, `@ilt`, `@ult`, `@feq`, `@flt`, `@seq`, `@slt`).
A type of your own joins them with an instance:

```ares
$ Money : @Type = @struct cents: @Int

$ impl_IOrd_for_Money : IOrd Money = .{ .lt = \a b => a.cents < b.cents }
$ cheaper : Bool = Money.{ .cents = 150 } < Money.{ .cents = 900 }
```

There is NO structural fallback: a type with no `IEq` instance cannot be compared
with `==`, which is an error at the comparison rather than a surprise at run time.
`ARES.derive_eq` / `derive_ord` generate the instances for a declared type.

`<` and `>` are also the effect-row brackets (§3.5), but a row only ever appears
in type position, so the two never collide.

## 4.5 Concatenation `++` and cons `::`
`++` joins strings/arrays/vectors of the same type; `::` prepends to a `@Vec`. Both
are `CORE` functions over interfaces (`ICat`, `ICons`), so a sequence of your own
joins them with instances of its own.

```ares
$ s  : @Str = "Hello" ++ " " ++ "world"
$ xs : @Vec @Int = 1 :: 2 :: 3 :: []
```

`::` builds a fresh vector, so it is O(n) and a `::`-recursion is quadratic;
`ARES.push` is the idiomatic way to build one up.

## 4.6 Short-circuit `&&` / `||`
Desugar to a lazy `if`, so the right operand runs only when needed.

```ares
$ safe : @Int -> Bool = \n => n > 0 && 100 / n > 5
```

## 4.7 Conditional `if ... => ... else`
`if c => t else e`. The condition is a `Bool`. One `if` has one arm; several
chain with `else if`. It is lazy (only the taken branch runs) and is not a
pattern match.

Simple:
```ares
$ abs : @Int -> @Int = \n => if n > 0 => n else -n
```

Involved (else-if chain):
```ares
$ sign : @Int -> @Int = \n =>
	if n == 0 => 0
	else if n > 0 => 1
	else -1
```

## 4.8 Local bindings `let ... in`
`let pat = e in body`. One `let` has one binding; several nest, each scoping
the rest (`let a = 1 in let b = a + 1 in b`). A binding is recursive exactly when its name occurs in its own body
(no `let rec`). A binder may carry a type annotation.

A local binding has one type, shared by every use: only globals are
generalized. `let id = \x => x in {id 1, id "s"}` is a mismatch at the second
use; a function needed at several types is a global with a signature.

Simple:
```ares
$ x : @Int = let a = 6 in a * 7
```

Involved (chain, destructuring, recursion, annotation):
```ares
$ r : @Int =
	let {a, b} = {3, 4} in
	let s = a + b in
	s * 2
$ len : @Vec @Int -> @Int =
	let go : @Vec @Int -> @Int -> @Int = \l n =>
		l |> \ | _ :: t => go t (n + 1) | _ => n
	 in \l => go l 0
```

## 4.9 Sequencing `;`, pipes `|>` `<|`, composition `<|>`
Parser sugar, lowest precedence. `a ; b` = `let _ = a in b`. `x |> f` = `f x`
(left-assoc). `f <| x` = `f x` (right-assoc).

`f <|> g` composes, and is the lambda it means: `\x => f (g x)`. It is
right-associative and the tightest infix operator, so `f <|> g <|> h` is
`f <|> (g <|> h)`, and application still binds tighter (`f <|> g x` is
`f <|> (g x)`). Because it expands to a lambda, it is typed per use site, and the
composed function's effect row is the UNION of the two steps' rows: `shout <|> show`
where only `shout` performs `@IO` has type `@Int -> <@IO | r> {}`, and two different
effects give `<@IO, St | r>`.

The FUNCTION form `(<|>)` is CORE's `compose`, which is an ordinary definition and
so has one written type, `(b -> <e> c) -> (a -> <e> b) -> a -> <e> c`: one row for
both steps, so it composes two functions that agree on their effects. Taking two
different rows is a property of the infix form, which has no signature to share,
the way short-circuiting is a property of infix `&&` (§4.10). A single row that is
the union of two variables is not expressible today (issue #200).

```ares
$ @import ARESxIO
$ inc : @Int -> @Int = \x => x + 1
$ double : @Int -> @Int = \x => x * 2
$ step1 : {} -> @Int = 0
$ step2 : {} -> @Int = 0
$ eff : @Int = step1 {} ; step2 {} ; 0     # run for effect, return 0
$ y   : @Int = 5 |> inc |> double          # double (inc 5)
$ z   : @Int = double <| inc <| 5          # same
$ f   : @Int -> @Int = double <|> inc      # \x = double (inc x)
$ w   : @Int = (double <|> inc) 5          # 12
$ shout : @Str -> <@IO> {} = \s => ARES.println s
$ show  : @Int -> <@IO> {} = shout <|> to_string   # the row is the union
$ h2    : @Int -> @Int = (<|>) double inc          # = compose double inc
```

## 4.10 Operators as functions `(op)`
An operator in parentheses is a plain function value, the same binding a
`$ (op) : ... = ...` definition binds. It curries and passes as an argument; since
it takes a context parameter, the type it is used at decides which instance is
injected, so a bare `(+)` with nothing to pin its type is an error that says so.

```ares
$ @import ARESxALGO
$ @import ARESxVEC
$ two   : @Int = (+) 1 1                   # 1 + 1
$ add1  : @Int -> @Int = (+) 1             # curried
$ plus  : @Int -> @Int -> @Int = (+)       # the instance comes from the type
$ total : @Int = foldl (+) 0 [1, 2, 3] # as an argument
```

The parens must hold exactly one operator, so `(a + b)` and `(-1)` still group.
`|` and `<>` are grammatical delimiters, not operators, and have no function
form. An operator the parser rewrites rather than calls (`&&`, `||`, `;`, `|>`,
`<|`) has no binding of its own, so `(op)` is the function `\l r => l op r`;
`(&&)` therefore evaluates both sides, since short-circuiting is a property of
the infix form. `<|>` is rewritten too, but its function form names a binding:
`(<|>)` is CORE's `compose` (§4.9).

## 4.11 `@cast`
Converts an integer to another integer type, wrapping it into the target's
range: the value is truncated to the target's width, then sign-extended for
`@intN` or zero-extended for `@natN` (so `@cast 250` as an `@Int8` is `-6`). The
target type comes from context (annotate if unknown). Integer widths only, not
int/real/ptr (those use `C.i2f` / `C.i2p`).

Every value of a sized type stays in its range: arithmetic on `@Int8` .. `@Int32`
and `@Nat8` .. `@Nat32` wraps the same way, and a literal that does not fit its
type (`300` as a `@Nat8`) is a compile error (`INT_LITERAL_RANGE`).

```ares
$ big   : @Int64 = 300
$ small : @Int32 = @cast big              # reinterpret across integer widths
$ back  : @Int    = @cast small            # and back to the platform word
```

## 4.12 Typed holes `???`
`???` stands for an expression not written yet. It takes whatever type its
context needs, and it is always a compile error (`TYPED_HOLE`) that names that
type and lists the names in scope that fit it, each offered as a fix. A hole is
how to ask the compiler what goes in a spot.

```ares-fragment
$ f : @Int -> @Int = \n => n + ???
# error[TYPED_HOLE]: hole `???` has type `@Int`
# note: in scope with this type: `n`
```

---

# 5. Pattern matching

## 5.1 The multi-arm lambda and matches
`\ | pat => e | pat => e ...` is a lambda matched against the arms top to
bottom; the first matching pattern wins and binds its variables. A match is the
multi-arm lambda applied to the scrutinee, usually with `|>`:
`scrut |> \ | pat => e ...`. There is no default branch: a catch-all is an
ordinary arm whose pattern matches anything, `| _ => d` (or `| x => d` to use
the value). Arms belong to the innermost multi-arm lambda or handler, so a
nested one is parenthesized.

An arm lists one pattern per argument, separated by commas: `\ | 0, _ => ...`
takes two curried arguments and matches both at once. Every alternative of
every arm has the same number of patterns. The comma separates arguments and
never builds a tuple; a tuple argument is matched with `{ a, b }`, which is one
argument. A handler's value arms match its one value, so they take one pattern.

Simple:
```ares
$ classify : @Int -> @Str = \ | 0 => "zero" | 1 => "one" | _ => "many"
$ yn : @Str -> @Int = \s => s |> \ | "yes" => 1 | "no" => 0 | _ => 99
$ take : @ctx {t: @Type} -> @Int -> List t -> List t = \
    | 0, _       => []
    | _, []      => []
    | n, x :: xs => x :: take (n - 1) xs
$ total : { @Int, @Int } -> @Int = \ | { 0, acc } => acc | { n, acc } => total { n - 1, acc + n }
```

Involved (nested union patterns, exhaustive so no catch-all, see 5.9):
```ares
$ Wrap : @Type = @union Empty: {}, W: { Opt }
$ Opt  : @Type = @union None: {}, Some: { @Int }
$ unwrap : Wrap -> @Int = \
    | Wrap.Empty                => 0
    | Wrap.W.{ Opt.None }       => 1
    | Wrap.W.{ Opt.Some.{ n } } => n
```

An empty match, on a value of an uninhabited type, is `x |> @absurd`.

## 5.2 Literal patterns
Match integers (any width), Real, and Str by equality (refutable). A numeric
literal may be negative (`-1`, `-0.5`), also as a range bound (`-10 ... -1`).

```ares
$ describe : @Int -> @Str = \n => n |> \ | 0 => "z" | 1 => "o" | -1 => "m1" | _ => "m"
$ yn : @Str -> @Int = \s => s |> \ | "yes" => 1 | "no" => 0 | _ => 99
```

A string literal can be a piece of a `++` pattern (5.7): `"GET " ++ path`
strips a prefix, `name ++ ".ares"` a suffix, and `"<" ++ body ++ ">"` both.

## 5.3 Wildcard and variable patterns
`_` matches anything binding nothing; a lowercase name binds the value.

```ares
$ tag : @Int -> @Int = \n => n |> \ | 0 => 100 | m => m + 1
```

## 5.4 Struct patterns
`Type.{ ... }` matches a struct. Positional (bare fields, in order, all listed)
or named (dotted, any order, others ignored; a lone `.name` puns).

```ares
$ Point  : @Type = @struct x: @Int, y: @Int,
$ Person : @Type = @struct name: @Str, age: @Int,
$ sum_xy : Point -> @Int = \p => p |> \ | Point.{ x, y } => x + y
$ who    : Person -> @Str = \p => p |> \ | Person.{ .name } => name
```

## 5.5 Variant patterns
`Type.Tag` (unit) or `Type.Tag.{ payload }`. May be written bare (`.Tag`), with
the union inferred from the arms. Payloads nest.

```ares
$ Maybe : (t: @Type) -> @Type = @union Just: t, None: {}
$ get : @Int -> Maybe @Int -> @Int = \d m => m |> \ | Maybe.Just.{ x } => x | _ => d
$ isJust : @ctx {t: @Type} -> Maybe t -> Bool = \m => m |> \ | .Just.{ _ } => true | _ => false
```

## 5.6 Range patterns
`lo ... hi` matches the inclusive interval (bounds are literals of the
scrutinee's type). Open `lo ...` matches `lo <= x`. Refutable, binds nothing.

Simple:
```ares
$ grade : @Int -> @Str = \n => n |> \ | 90 ... 100 => "A" | 60 ... 89 => "C" | _ => "F"
```

Involved (open range, Real):
```ares
$ sign : @Int -> @Str = \n => n |> \ | 0 ... => "nonneg" | _ => "neg"
$ band : Real -> @Int = \x => x |> \ | 0.0 ... 0.5 => 1 | 0.5 ... 1.0 => 2 | _ => 0
```

## 5.7 Sequence and array patterns
A closed `[a, b]` matches a sequence of exactly those elements, and `[]` an
empty one. `++` splits a sequence into fixed pieces around at most one part of
unknown length: `pre ++ mid ++ suf`. A fixed piece is a closed `[..]` list or,
on a `@Str`, a string literal; adjacent pieces merge (`[1] ++ [2]` is `[1, 2]`).
`h :: t` is shorthand for `[h] ++ t`.

Pieces before the middle step the scrutinee's `@ISeqView` from the front;
pieces after it step its `@ISeqViewBack` from the back. `@Vec` (the default),
`@Array`, and `@Str` (as its bytes) have both, `CORE`'s cons `List` only the
front one, and any type of your own joins with an instance. Two parts of unknown
length (`"a" ++ x ++ "b" ++ y`) are an error: the sequence could split between
them in more than one way.

Simple:
```ares
$ sum : @Vec @Int -> @Int = \xs => xs |> \ | [] => 0 | h :: t => h + sum t
```

Involved (a prefix, a suffix, and both ends):
```ares
$ second : @Vec @Int -> @Int = \xs => xs |> \ | [_, x] ++ rest => x | _ => -1
$ ext    : @Str -> @Str = \s => s |> \ | name ++ ".ares" => name | _ => s
$ ends   : @Array -> @Int = \a => a |> \ | [x] ++ mid ++ [z] => x + z | _ => 0
```

A sized tensor `@Tensor n T` (3.9) knows its length, so its patterns are checked
at compile time instead of tested: `[x, y, z]` covers a `@Tensor 3 T` with no `_`
arm, a wrong length is a type error, and the middle of a split gets an exact size
(`[a] ++ r` on a `@Tensor 3 T` binds `r : @Tensor 2 T`). The size must be concrete there.
A rank-2 tensor splits along its first axis, one row per element.

```ares
$ sum3 : @Tensor 3 @Int -> @Int = \t => t |> \ | [x, y, z] => x + y + z
```

## 5.8 Or-patterns and guards
`| p1 | p2 => e` shares one body (alternatives bind no variables). `| pat if g
=> e` adds a boolean guard; a failed pattern or guard falls through to the next
arm, even one with the same constructor.

Or-pattern:
```ares
$ small : @Int -> @Int = \n => n |> \ | 0 | 1 | 2 => 1 | _ => 0
```

Guards falling through the same constructor:
```ares
$ Box : @Type = @union Some: @Int, Nil: {},
$ grade : Box -> @Int = \x =>
	x |> \ | Box.Some.{ v } if v > 100 => 3
	     | Box.Some.{ v } if v > 0   => 2
	     | Box.Some.{ _ }             => 1
	     | Box.Nil.{}                 => 0
```

## 5.9 Exhaustiveness
Every match, and every set of handler value arms, is checked after type
inference. A match that misses a value is a compile error
(`NON_EXHAUSTIVE_MATCH`) that names a missing shape, such as `Light.Green` or
`Opt.Some.{ _ }`. An arm the earlier arms already cover is a warning
(`UNREACHABLE_ARM`).

- A match needs no catch-all when its arms cover every constructor of a union.
  Booleans, tuples, and structs are covered the same way, nested to any depth.
- A guarded arm covers nothing for exhaustiveness, since its guard can fail.
- Integer literals and ranges are checked as intervals of their type's values,
  so `| 0 ... 127 => a | 128 ... => b` covers a `@Nat8`, and an arm whose range
  earlier arms already cover is unreachable. `@Int` and `@Nat` are taken at 64
  bits. A missing interval is named, such as `100` or `10 ...`.
- `@Float64`, `@Str`, and the other infinite domains need a `_` or binder arm.
  Real ranges and string `++` patterns never cover a whole domain.
- A union with its own `@ISeqView` cannot be matched with both its variants and
  sequence patterns in one position (only `List` can); that is reported.
- A sequence pattern (`[]`, `h :: t`, `[a] ++ r`) is checked through the
  sequence view, so `[]` and `_ :: _` together cover any sequence. A piece
  matched from the back (`r ++ [z]`) is not modeled, so it needs a `_` arm.

```ares
$ Light : @Type = @union Red: {}, Yellow: {}, Green: {}
$ go : Light -> @Int = \l =>
	l |> \ | Light.Red => 0 | Light.Yellow => 1 | Light.Green => 2   # no catch-all needed
```

## 5.10 Irrefutable patterns in `let` and lambda
A `let` binder or a lambda parameter has no next arm to fall through to, so its
pattern must match every value of its type. `_`, variables, and struct, tuple,
and record patterns built from them always do. A pattern that can fail, such as
a literal or a variant of a union with several, is a compile error
(`NON_EXHAUSTIVE_MATCH`) naming a value it misses; match it instead,
`e |> \ | pat => ... | _ => ...`. For a lambda's one unannotated parameter
the error carries that rewrite as a fix: `\P => B` becomes
`\ | P => B | _ => ???`. There is no `let ... else`: `let` is a definition, not
sugar for applying a lambda.

```ares
$ Point  : @Type = @struct x: @Int, y: @Int,
$ Person : @Type = @struct name: @Str, age: @Int,
$ Line   : @Type = @struct from: Point, to: Point,
$ person : Person = Person.{ .name = "A", .age = 30 }
$ age : @Int = let Person.{ .age = a } = person in a
$ start : Line -> @Int = \Line.{ .from = Point.{ x, _ }, .to = _ } => x
```

---

# 6. Algebraic data types

## 6.1 Structs `@struct`
A named record type: `$ Name : @Type = @struct field: Type, ...`. Built with a
literal (`Type.{ .f = e }`, bare `.{ ... }`, or positional `Type.{ a, b }`);
read with `.field`. Nominal (unifies by name).

A type with parameters states them in its signature, each with what it ranges
over: a type (`@Type`), a size (`@Nat`, for `@Tensor n T`) or a row (`@Row`,
for an effect row or a record's open tail). Every parameter is named and
written; a type variable used in the body that the signature does not bind is
an error, and one used as something other than what it ranges over is too.

Simple:
```ares
$ Person : @Type = @struct name: @Str, age: @Int,
$ p : Person = Person.{ .name = "Will", .age = 21 }
$ who : @Str = p.name
```

Involved (generic, applied by juxtaposition, nested field types, a size):
```ares
$ Box : (t: @Type) -> @Type = @struct val: t,
$ Samples : (n: @Nat) -> @Type = @struct data: @Tensor n @Float64,
$ Wrap : (t: @Type) -> @Type = @struct inner: Box t,
$ w : Wrap @Int = .{ .inner = Box.{ .val = 7 } }
$ deep : @Int = w.inner.val
```

## 6.2 Record update
`Type.{ .field = e | base }` copies unlisted fields from `base`. The `| base`
comes last; a listed field may read from `base`.

```ares
$ Person : @Type = @struct name: @Str, age: @Int,
$ base : Person = Person.{ .name = "A", .age = 30 }
$ older : Person = Person.{ .age = base.age + 1 | base }
$ clone : Person = .{ | base }
```

## 6.3 Unions `@union`
A tagged sum: `$ Name : @Type = @union Tag: Payload, ...`. A `{}` payload is a
unit variant. Recursive, and generic with parameters stated as for a struct.
Non-strict data constructors (lazy payloads).

Simple:
```ares
$ Maybe : (t: @Type) -> @Type = @union Just: t, None: {}
$ some : Maybe @Int = Maybe.Just.{ 5 }
$ none : Maybe @Int = .None
```

Involved (recursive, multi-field payload, positional or named):
```ares
$ Tree : (a: @Type) -> @Type = @union Leaf: a, Node: { Tree a, Tree a }
$ t : Tree @Int = Tree.Node.{ Tree.Leaf.{ 1 }, Tree.Leaf.{ 2 } }
```

An indexed family's signature goes on after the parameters with indices, and
each constructor states the result it builds after its payload. The leading
binders every result passes through as themselves are the parameters; the rest
are indices. Building a value checks its index:

```ares
$ Vec : (a: @Type) -> @Nat -> @Type =
    @union Nil: {} -> Vec a 0, Cons: @ctx {n: @Nat} -> {a, Vec a n} -> Vec a (n + 1)
$ two : Vec @Int 2 = Vec.Cons.{ 1, Vec.Cons.{ 2, Vec.Nil } }
$ length : @ctx {a: @Type, n: @Nat} -> Vec a n -> @Int = \v => v |> \ | Vec.Cons.{ _, t } => 1 + length t | Vec.Nil => 0
```

A variable of a stated result that is not a parameter, `n` above, belongs to
the constructor, which binds it in a `@ctx` ahead of its payload (#558), as a
signature binds its own (3.6). Only a constructor that states its result has
one, and it binds only names of its own, not the declaration's parameters. A
name nothing binds is a `TYPE_UNBOUND` error whose fix adds it to the
constructor's `@ctx`. A match does not tell what it was built with yet (dependent
matching, #543): in `Vec.Cons.{ _, t }`, `t` has the type `Vec a n` for an `n`
of its own, which the arm may not take for any other size. Indices are erased,
so a `Vec` is a list at run time.

## 6.4 Generated members `!`
An entry `!X` of a `@struct` or `@union` runs `X` at build time and splices the
fields or variants its `@Code` spells in its place.
DERIVE's `fields_of` and `variants_of` copy another declaration's members, a
copy with no subtyping relationship. A copied type may itself be generated; a
generic one is applied to the new type's parameters (`fields_of "Pair b"`). A
duplicate member is an error.

```ares
$ @import ARESxDERIVE
$ Point  : @Type = @struct x: @Int, y: @Int
$ Point3 : @Type = @struct !ARES.fields_of "Point", z: @Int   # x, y, then z
$ Base   : @Type = @union Red: {}, Green: {}
$ Color  : @Type = @union !ARES.variants_of "Base", Blue: {} # Red, Green, then Blue
```

## 6.5 Recursive types are lazy
A slot whose type leads back to the type that declares it holds its value
lazily: building one cell does not build the rest, and a cell is computed when
something looks at it. The forced value replaces the thunk, so a cell costs its
work once however many times it is read. This makes an unbounded structure an
ordinary declaration, with no separate kind for it.

Laziness belongs to the slot, so it does not depend on how the value is written.
It stops at an arrow: a slot typed `{} -> T` is already a suspension and stays a
plain function.

Simple (an unbounded sequence, a recursive `@struct`):
```ares
$ Seq : (t: @Type) -> @Type = @struct first : t, rest : Seq t
$ from : @Int -> Seq @Int = \n => { .first = n, .rest = from (n + 1) }
$ third : @Int = (from 1).rest.rest.first
```

A recursive `@union` works the same way, which is how a `List` is consumed one
cons at a time, and why an infinite `List` is an ordinary one (`count_from` and
the open range `[lo ...]` build them):
```ares
$ nat : @Int -> List @Int = \n => List.Cons.{ n, nat (n + 1) }
$ head : List @Int -> @Int = \l => l |> \ | List.Cons.{h, t} => h | _ => 0
$ seven : @Int = head (nat 7)
```

Evaluation is otherwise call by value, so a slot filled through a function
argument is evaluated at the call, as any argument is. `List.Cons.{ n, from (n
+ 1) }` suspends the tail; `cons n (from (n + 1))` does not, because `from (n +
1)` is an argument to `cons`.

---

# 7. Functions

## 7.1 Currying
Every function of several parameters is curried; partial application yields a
function.

```ares
$ add : @Int -> @Int -> @Int = \a b => a + b
$ add5 : @Int -> @Int = add 5           # partial application
```

## 7.2 Higher-order functions
Functions are first-class values.

```ares
$ apply_twice : @ctx {t: @Type} -> (t -> t) -> t -> t = \f x => f (f x)
$ compose : @ctx {b: @Type, c: @Type, a: @Type} -> (b -> c) -> (a -> b) -> a -> c = \f g x => f (g x)
```

## 7.3 One name, one definition
A name has one definition and one type. Two definitions of a name in one module is
an error; a local definition shadows an imported one of the same name; and a name
two imports bring in has no bare meaning, so a use of it says so and names the
owners (`A.name` and `B.name` still reach either). An operation that covers several
types is an interface (§7.4), not several definitions.

A local binder (a lambda parameter, a `let`, a pattern variable, a record
parameter's field, a handler binder) cannot reuse the name of a global defined in
the same module (`SHADOWED_GLOBAL`), so inside a module a global's name always
means that global. Imported names may be shadowed locally.

## 7.4 Interfaces and `@use` parameters
An interface is an ordinary `@struct` whose fields are its operations; implementing
it is defining a value of that type. A function that needs one declares a `@use`
parameter, a record of named fields, each an instance it needs. Call sites do not
write it: the compiler finds each field BY TYPE, taking the nearest binder in scope
and otherwise the one instance in scope (two would be an error, since global scope
is flat). The fields are in scope by name in the body, so the body's lambda starts
at the first explicit parameter. It elaborates to a leading argument, so the
backends need no support.

Simple:
```ares
$ Ordering : @Type = @union LT: {}, EQ: {}, GT: {}
$ IOrder : (t: @Type) -> @Type = @struct compare: t -> t -> Ordering,
$ impl_IOrder_for_int : IOrder @Int = .{
	.compare = \a b => if a < b => Ordering.LT else if a > b => Ordering.GT else Ordering.EQ,
}
$ max_of : @ctx {t: @Type} -> @use {d: IOrder t} -> t -> t -> t = \x y =>
	d.compare x y |> \ | Ordering.GT => x | _ => y
$ biggest : @Int = max_of 3 7
```

A signature may have any number of `@use` parameters, anywhere on its arrows, and
each names one or more fields; a field's type must be a declared struct or union
applied to its arguments, and field names are unique across the signature:

```ares
$ abs : @ctx {t: @Type} -> @use {o: IOrd t, s: ISub t, z: IZero t} -> t -> t = \x =>
	if o.lt x z.zero => s.sub z.zero x else x
$ floor_at : @ctx {t: @Type} -> @use {o: IOrd t} -> t -> @use {z: IZero t} -> t -> t = \x y =>
	if o.lt x z.zero => y else x
```

Calls inside the body find the fields by search, so they pass down without being
written. An explicit `@use {.f = e}` argument names the fields it supplies (the
rest are still searched) and goes where its parameter stands, before the explicit
argument that follows it:

```ares
$ Ordering : @Type = @union LT: {}, EQ: {}, GT: {}
$ IOrder : (t: @Type) -> @Type = @struct compare: t -> t -> Ordering,
$ impl_IOrder_for_int : IOrder @Int = .{
	.compare = \a b => if a < b => Ordering.LT else if a > b => Ordering.GT else Ordering.EQ,
}
$ max_of : @ctx {t: @Type} -> @use {d: IOrder t} -> t -> t -> t = \x y =>
	d.compare x y |> \ | Ordering.GT => x | _ => y
$ max3 : @ctx {t: @Type} -> @use {d: IOrder t} -> t -> t -> t -> t = \x y z =>
	max_of (max_of x y) z          # d satisfies max_of's requirement, so it passes down
$ as_min : @Int =
	let flip : IOrder @Int = .{ .compare = \a b => impl_IOrder_for_int.compare b a } in
	max_of @use {.d = flip} 3 7
```

`@use` stands only on a global definition's own signature: not inside a
parameter's type (`(@use {d: IOrd t} -> t) -> t`), an annotation, a field type, or
(for now) a local `let`'s signature. `@use {}` is an error. `@ctx` binds what
unification solves instead (3.6); an instance in `@ctx`, or a type in `@use`, is
an error naming the other binder.

An instance may itself take a context, which resolution fills in recursively, so
`IEq (@Vec t)` is built from `IEq t`. `CORE`'s operators are all ordinary functions
over such interfaces: `+ - * / %` over `IAdd`/`ISub`/`IMul`/`IDiv`/`IMod`, `^` over
`IPow`, `== != < > <= >=` over `IEq`/`IOrd`, `++` over `ICat`, `::` over `ICons`, and
`to_string` over `IToString`. A type joins any of them by defining an instance:

```ares
$ Money : @Type = @struct cents: @Int
$ impl_IAdd_for_Money : IAdd Money = .{ .add = \a b => Money.{ .cents = a.cents + b.cents } }
$ total : Money = Money.{ .cents = 1 } + Money.{ .cents = 2 }
```

See `documentation/language/interfaces.md` for the full rules, the diagnostics, and the
blessed `@I*` interfaces the compiler's own desugars resolve.

## 7.5 Tail-call optimization
Tail-recursive calls (self, mutual, or through a recursive local `let`) run in
constant stack.

```ares
$ sum_to : @Int -> @Int -> @Int = \n acc =>
	if n == 0 => acc else sum_to (n - 1) (acc + n)      # constant stack at any depth
```

---

# 8. Algebraic effects and handlers

## 8.1 Declaring an effect `@effect`
`$ Name : @Effect = op : Arg -> Resume, ...`. Each operation takes one argument
and names its resume type. An operation whose handler never resumes (an
exception) names a type variable of its own as its result, `@ctx {a: @Type}`.

```ares
$ State : @Effect = get : {} -> @Int, put : @Int -> {},
$ Exn   : @Effect = throw : @ctx {a: @Type} -> @Str -> a,
$ Yield : @Effect = yield : @Int -> {},
```

An effect may take parameters, stated in its signature like a struct's.
In a row the effect is applied to its arguments, `<State @Str>`. One handler
serves every operation the body performs on it, so it fixes the parameters for
all of them: under one `State` handler every `get` and `put` is at one type. A
parameter may be a row, `(e: @Row)`, for an operation that takes an effectful
function, and a bare mention of the effect inside its own declaration stands for
its parameters. Arguments left out of a row (`<State>`) are inferred.

```ares
$ State : (s: @Type) -> @Effect = get : {} -> s, put : s -> {},
$ Async : (m: @Type) -> (e: @Row) -> @Effect = spawn : ({} -> <Async m e | e> {}) -> {}, send : m -> {},
$ count : {} -> <State @Int> @Int = let n = get {} in put (n + 1); n
```

An operation's type may also use variables the effect does not declare, like
`throw` above, bound in a `@ctx` that opens its type (#558); a name nothing
binds is a `TYPE_UNBOUND` error whose fix adds it there. Each use chooses those types, so a handler clause sees them as
opaque: it can pass such a value along (resume with the argument it was given,
store it), but it cannot make one up or inspect it. A clause that needs a
concrete type takes it from an effect parameter instead.

```ares
$ Exn : @Effect = throw : @ctx {a: @Type} -> @Str -> a,
$ safe : @Int = do 1 + Exn.throw "no" is k | Exn.throw m => 0     # aborts: fine
# `| Exn.throw m => k 0` is an error: `k` wants `a` of `Exn.throw`, not @Int
```

## 8.2 Performing an operation
Just call it; there is no `perform` keyword. A use injects the effect into the
ambient row.

```ares
$ State : @Effect = get : {} -> @Int, put : @Int -> {},
$ tick : {} -> <State> @Int = let x = get {} in let _ = put (x + 1) in x
```

## 8.3 Handling `do ... is`
`do body is k | op a => e ... | pat => e ...`. `k` is the captured
continuation, shared by every clause. Each `| op a => e` handles an operation. A
value arm `| pat => e` runs on normal completion, matching the body's final value
like a match arm; with none, that value is the handler's result. An operation
clause always names an operation and its argument (`| op a`, `| Eff.op a`),
which no pattern can look like, so the two kinds of arm need no marker. A shared
operation name is qualified in a clause head.

Exception (ignores `k`, so it resumes zero times):
```ares
$ Exn : @Effect = throw : @Str -> @Int,
$ safeDiv : @Int -> @Int -> @Int = \a b =>
	do if b == 0 => Exn.throw "div0" else a / b
	is k | Exn.throw msg => -1
```

Generator (resume once per yield, summing results):
```ares
$ Yield : @Effect = yield : @Int -> {},
$ sumGen : ({} -> <Yield> {}) -> @Int = \gen =>
	do gen {}
	is k | Yield.yield v => v + k {}
	      | _ => 0
```

## 8.4 Resuming
Resuming is applying `k`. `k v` splices the suspended computation back and
delivers `v`. `k` may be resumed **any number of times**, and may be stored
before use, which is what coroutines need. Handlers are deep (a resumed
computation is still governed by the same handler).

```ares
$ Yield : @Effect = yield : @Int -> {},
$ Task : @Type = @union Fin: {}, Susp: { @Int, {} -> Task }
$ spawn : ({} -> <Yield> {}) -> Task = \t =>
	do t {}
	is k | Yield.yield v => Task.Susp.{ v, k }     # store k, resume later
	      | _ => Task.Fin.{}
```

Resuming more than once runs the rest of the computation once per resume, each on
its own copy, which is what nondeterminism and backtracking are:

```ares
$ Amb : @Effect = flip : {} -> Bool,
$ sum_all : ({} -> <Amb> @Int) -> @Int = \body =>
	do body {}
	is k | Amb.flip u => k true + k false        # both branches
	      | x => x
```

A resume copies the captured computation only when something else could still
resume it: when nothing else holds `k`, the engine hands the computation over
instead. So a continuation resumed once costs nothing, whether it is applied in
the clause, captured by a lambda, or stored and resumed later, and n resumes of
one continuation cost n-1 copies, the last taking the original. A clause that
never mentions `k`, as in an exception, captures nothing at all.

## 8.5 Effect rows in types
A function's type carries the effects it may perform as a row on the arrow.
Absent row means pure. A row variable makes it effect-polymorphic. A handler
discharges the effects it handles. A performed-but-unhandled effect is a compile
error. Subsumption: a pure function is callable in any effectful context, and
a function passed as an argument may perform fewer effects than its parameter
allows: `compose` shares one row `<e>` between its two functions, yet
`compose shout double` composes an `<@IO>` function with a pure one. Arrows
relate the usual way round, covariant in results and contravariant in
parameters, so a function that only accepts pure callbacks is not one that
accepts effectful ones.

```ares
$ map : @ctx {a: @Type, e: @Row, b: @Type} -> (a -> <e> b) -> @Vec a -> <e> @Vec b = \f xs =>
	xs |> \ | [] => [] | h :: t => f h :: map f t
```

## 8.6 `@finale`
`@finale cleanup body` runs `body {}`, then `cleanup {}` when the body's scope
exits: on normal completion, on an abort by an outer non-resuming handler, or
when a stored continuation holding it completes. Nested finales run
innermost-first. It is an ordinary CORE function, not syntax, so the parser has
no rule for it and it can be partially applied and passed around. The
resource-safe FFI idiom.

```ares
$ open  : @Str -> @Int = \path => 0        # stand-ins for real handles
$ close : @Int -> {} = \h => {}
$ read  : @Int -> @Int = \h => h
$ useFile : @Str -> @Int = \path =>
	let f = open path in
	@finale (\_ => close f) <| \_ =>
	read f
```

Several cleanups nest as separate `@finale`s, and run innermost-first (here
`close g`, then `close f`):
```ares
$ open  : @Str -> @Int = \path => 0        # stand-ins for real handles
$ close : @Int -> {} = \h => {}
$ read  : @Int -> @Int = \h => h
$ useTwo : @Str -> @Str -> @Int = \a b =>
	let f = open a in
	let g = open b in
	@finale (\_ => close f) <| \_ =>
	@finale (\_ => close g) <| \_ =>
	read f + read g
```

Both arguments are thunks, because Ares is call-by-value: `@finale (close f)`
would close the file before the body ran. The cleanup returns `{}`, and its row
is the body's, so a pure function passed directly where the body performs
effects needs a lambda around it (`\_ => closeWindow {}`). A library wraps it
in a bracket function so callers never see the handle's cleanup:
```ares
$ open  : @Str -> @Int = \path => 0        # stand-ins for real handles
$ close : @Int -> {} = \h => {}
$ read  : @Int -> @Int = \h => h
$ with_file : @Str -> (@Int -> @Int) -> @Int = \path body =>
	let f = open path in
	@finale (\_ => close f) <| \_ => body f
```

---

# 9. Sized tensors and linear algebra

## 9.1 Tensor literals and indexing
`@Tensor n T` is built from a `[..]` literal whose length fixes `n` (a mismatch
is a type error). Read with modular indexing `t.[i]` (the index reduces mod the
size, so it is total, `t.[n]` wraps to `t.[0]`). Indexing an empty `@Tensor 0 T`
is the sole fault.

```ares
$ @import ARESxLA
$ v : @Tensor 3 @Int = [10, 20, 30]
$ a : @Int = v.[1]        # 20
$ b : @Int = v.[3]        # wraps to v.[0] = 10
```

## 9.2 Multi-dimensional and multi-axis indexing
A matrix is a tensor of tensors, `Matrix m n T` = `@Tensor m (@Tensor n T)`.
`t.[i, j]` reads one element (`t.[i].[j]`).

```ares
$ @import ARESxLA
$ g : Matrix 2 2 @Int = [ [1,2], [3,4] ]
$ z : @Int = g.[1, 0]     # 3
```

## 9.3 Size arithmetic
A size may be `+`/`*` over literals and size variables, evaluated mod 2^64 and
compared by a canonical form (`n + m` equals `m + n`; `n + n` is `2 * n`). This
drives size-changing operations, whose result size is computed at compile time.

```ares
$ @import ARESxLA
# ARESxLA provides `concat_tensors`, its result size computed at compile time:
#   concat_tensors : @Tensor n a -> @Tensor m a -> @Tensor (n + m) a
$ joined : @Tensor 5 @Int = concat_tensors [1, 2] [3, 4, 5]      # 2 + 3 = 5
```

## 9.4 Slicing
Multi-axis slicing `t.[s0, s1, ...]`: `i` indexes an axis, `p ... q` narrows it
to an inclusive range, `..` keeps it whole. Every result is an O(1) strided view.

```ares
$ @import ARESxLA
$ row : @ctx {m: @Nat, n: @Nat, a: @Type} -> Matrix m n a -> @Int -> @Tensor n a = \m i => m.[i]
$ col : @ctx {m: @Nat, n: @Nat, a: @Type} -> Matrix m n a -> @Int -> @Tensor m a = \m j => m.[.., j]
$ sub : @Tensor 8 @Int -> @Tensor 4 @Int = \m => m.[2 ... 5]      # inclusive 2..5, four elements
```

## 9.5 Tensor primitives and the `LA` library
The compiler provides only `@`-primitives over the buffer; every named operation
lives in `LA`. `t.[i]` desugars to the `@IIndex` interface and a lone
`t.[lo ... hi]` to `@ISlice`, so a container of your own joins the `.[..]` surface
by defining an instance. A multi-axis slice stays tensor-only: its result shape is
computed from the slots.

```ares
$ @import ARESxLA
$ transpose : @ctx {m: @Nat, n: @Nat, a: @Type} -> Matrix m n a -> Matrix n m a = \t =>
	@tensor_create (@tensor_index t 0)
		(\j => @tensor_create t (\i => @tensor_index (@tensor_index t i) j))
```

## 9.6 Expression-form ranges
`[lo ... hi]` builds whatever the resolved `@IRange` instance returns, and the open
`[lo ...]` whatever `@IRangeFrom` returns; `CORE` has instances for `List` and
`@Vec`, and for `List`. The expected type picks one, so a range of your own type
needs only its own instance. When nothing constrains it, the **first instance
declared** wins, which is how `CORE`'s order (not the compiler) makes a bare range
a `List`.
A sized tensor is the exception: literal bounds fix `n`, and the compiler builds it
directly.

```ares
$ tv : @Tensor 4 @Int = [1 ... 4]     # tensor, n = 4
$ ls : List @Int      = [1 ... 5]     # list (the bare closed range)
$ ns : @Vec @Int      = [1 ... 5]     # vector, where one is expected
$ s  : List @Int      = [1 ...]       # unbounded (the bare open range)
```

A `List` is lazy in the tail, which is what makes a range you only walk part of
cheap; a `@Vec` range materializes every element up front:

```ares
$ @import ARESxALGO
$ @import ARESxLIST
$ @import ARESxIO
$ first5 : {} -> <@IO> {} =
	for [1 ... 100000000000000] (\i => if i > 5 => break {} else ARES.print "?(i), ")
```

---

# 10. Foreign function interface

## 10.1 `@extern` binding
A foreign binding is a global whose body is `@extern "C" "symbol" "lib"`. A
signature is required and drives C-ABI marshalling. An extern takes exactly one
argument (one arrow).

```ares
$ puts : @Str -> @Int = @extern "C" "puts" "libc"
$ used : @Int = puts "hi"
```

## 10.2 Multi-parameter C functions
A C function is not curried, so several parameters group into a record; its
fields, in declaration order, are the positional C arguments (marshalled by name,
so a reordered call site is fine). A nullary C function takes `{}`.

```ares
$ pow : {base: Real, exp: Real} -> Real = @extern "C" "pow" "libm"
$ a : Real = pow {2.0, 10.0}                 # positional
$ b : Real = pow {.exp = 10.0, .base = 2.0}  # named, reordered
$ getchar : {} -> @Int = @extern "C" "getchar" "libc"
```

## 10.3 C structs and unions by value
`Name : @Type = @struct @extern "C" ...` is a C-layout foreign type (fields must be
C-representable, not generic). Built and read with the ordinary struct literal
and `.field`, and it crosses the boundary by value. A C union is
`Name : @Type = @union @extern "C" ...` (members share offset 0).

```ares
$ Color : @Type = @struct @extern "C" r: @Nat8, g: @Nat8, b: @Nat8, a: @Nat8,
$ clear : Color -> {} = @extern "C" "ClearBackground" "libraylib.so"
$ go : {} = clear Color.{ .r = 0, .g = 0, .b = 0, .a = 255 }
```

## 10.4 Callbacks and array parameters
A function-typed parameter is a C function pointer: pass a Ares closure. A
`@Vec T` parameter (T a C-repr struct) is passed as a packed `T*` with a separate
count.

```ares
$ Vector2 : @Type = @struct @extern "C" x: @Float32, y: @Float32,
$ sort : {@Ptr, @Int, (@Int -> @Int -> @Int)} -> {} = @extern "C" "qsort_r" "libc"
$ draw : {@Vec Vector2, @Int} -> {} = @extern "C" "DrawLineStrip" "lib"
```

## 10.5 The `C` namespace and engine intrinsics
`library/C.ares` binds libc/libm as the auto-injected `C` namespace (used
qualified, `C.sqrt`, no import). It also holds a few conversions the language
cannot express with `@cast` (which is integer widths only): `C.i2f`/`C.f2i`
(@Int and @Float32), `C.i2d`/`C.d2i` (@Int and Real), `C.i2p`/`C.p2i` (@Int to
@Ptr and back), `C.ptr_add` (an address `n` bytes on), and `C.null` (the null
pointer). These are provided by the engines' runtimes (an
empty `lib`); see `documentation/runtime/native-backend.md`.

```ares
$ x : @Float32 = C.i2f 41
$ nul : @Ptr = C.null
```

Limitation: variadic C functions (`printf(fmt, ...)`) have no single binding.
Declare a fixed-arity binding per argument shape you use; there is no `...`
marker.

## 10.6 Reading C memory
C memory reaches Ares two ways, both copies:

- **Bytes**: `@ptr_bytes p n` (CORE) is a fresh `@Str` of the `n` bytes at `p`,
  NUL bytes and all. (A `@Str` *result* of a C function is a `char*` and ends at
  its first NUL.) This is how `ARES.read_file` reads: `C.read` into `C.malloc`
  memory, then `@ptr_bytes`.
- **Typed elements**: a binding with `@extern "load"` (no symbol, no library)
  reads element `i` of a C array of `T` at `p`. Its type must be
  `{ p: @Ptr, i: @Int } -> T`, where `T` is a sized number, `@Int`/`@Nat`, `@Ptr`,
  `@Str` (a `char*`, copied up to its NUL; NULL reads as `""`), or a
  `@struct @extern "C"` type. A C `bool` loads as `@Nat8`. `ARES.from_c at p n`
  collects the first `n` elements as a vector.

```ares
$ @import ARESxVEC
$ Point : @Type = @struct @extern "C" x: @Int32, y: @Int32,
$ point_at : { p: @Ptr, i: @Int } -> Point = @extern "load"
$ arg_at : { p: @Ptr, i: @Int } -> @Str = @extern "load"      # a `char**`

$ points : @Ptr -> @Int -> @Vec Point = \p n => ARES.from_c point_at p n
```

Like a C dereference, a load trusts the program: the memory must hold `n`
valid elements (a load from NULL faults; anything else out of bounds is
undefined).

## 10.7 Builtins: `@extern "ares"`
The primitives the compiler and runtime implement (`@iadd`, `@vec_push`,
`@chan_send`, `@lex`, ...) are declared in `library/CORE.ares`, each with its
signature and a comment:

```ares-fragment
# Declared in CORE, which alone may declare a builtin.
$ @iadd : @ctx {t: @Type} -> t -> t -> t = @extern "ares"
$ @vec_push : @ctx {a: @Type} -> @Vec a -> a -> @Vec a = @extern "ares"
```

The definition's name is the builtin, so there is no symbol or library string,
and a reference compiles to a direct call with no wrapper. Unlike a C extern, a
builtin is curried. Only CORE may declare one, and no module may redefine one.
The operators the parser rewrites (`;`, `|>`, `<|`) are declared the same way, for
their types: `$ (|>) : @ctx {a: @Type, e: @Row, b: @Type} -> a -> (a -> <e> b) -> <e> b = @extern "ares"`. A few primitives stay inside the
compiler because their types have no surface syntax: `@cast` is checked
specially, and the `@tensor_*` primitives are typed in the compiler (#342).

---

# 11. Compile-time evaluation

## 11.1 `!`, the splice
`!X` runs `X` at build time and replaces itself with the result:

- an `@Code` is spliced in as source, usually written as a quotation
  (section 11.2);
- first-order data (a number, a `Bool` or a `@Str`) is inserted as a literal.

The inserted source is then checked like hand-written code. Any other result,
such as a function, is an error at the `!`. In type, row, member and item
position only code makes sense, so there the operand is expected as `@Code`
and a string literal is a quotation; in expression and pattern position a
string is data.

`!` is syntax, not a function: there is no `(!)` section, no `x |> !`, and no
`$ (!)` definition. It binds like the other prefix operators, so it scopes over
an application: `!f a b` splices `f a b`, `!f a ++ b` is `(!(f a)) ++ b`, and a
pipe chain is parenthesized, `!(x |> f)`. It works in every position:

```ares
$ fib : @Int -> @Int = \k => if k < 2 => k else fib (k - 1) + fib (k - 2)
$ fib10 : @Int = !fib 10                            # expression: inserts `55`
$ n     : !"@Int64" = 1024                          # type
$ !"$ injected : @Int = 99"                         # item
$ is55  : @Int -> Bool = \ | !fib 10 => true | _ => false   # pattern
```

A type splice may stand at any type position: a signature, a struct field, a
union payload, a type-level function's body, an effect operation, an effect-row argument, a
`@use` field, or an annotation inside a body (`let x : T`, `\(x : T)`,
`(e : T)`). Effect-row entries themselves can be spliced too, as `<!X>`; a
`!` right after an operator lexes on its own, so `<!X>` is `<` then `!X`.

```ares
$ pick : {} -> @Code = "@Int"
$ Point : @Type = @struct x: !pick {}, y: !pick {}
```

In a pattern, `!X` is how a value the compiler can compute stands as a
constant: `!answer` matches the value of the global `answer`, while a bare
`answer` would bind. Because the value is inserted as a real literal,
exhaustiveness and `UNREACHABLE_ARM` treat it like a hand-written `42`. The
operand ends before the `=>`, `|` or `::` after it. A generator may also build
a pattern as `@Code`; that pattern may bind names, and its coverage is checked
once it is spliced.

A generator never runs code the checker could not yet resolve. While `!` sites
remain, a missing name or instance is left open, since a generator may still
supply it; a `!` whose code reaches one waits for a later round, and if no
round supplies it the error is reported as written.

`X` may perform the compile-time operations (`@emit`, `@abort`, `@fresh`,
`@link`, `@link_path`, and the reflection `@type_kind`, `@type_params`,
`@type_fields`, `@type_variants`, `@type_of`). They carry the `<@Meta>` effect,
which `!` discharges. The richer ones speak CORE types:

- `@lookup name` is a `Decl`: `Struct`, `Union` (each with its shape), `Value`
  (a global's type as source) or `Missing`.
- `@here {}` is the running `!`'s `Site` (`file`, `line`, `column`).
- `@check code` type-checks an expression fragment as if written at the `!`
  and gives its type as source; an ill-typed fragment fails the build.
- `@fail d` and `@warn d` report a `Diag` (`message`, `notes`, `helps`; `diag
  msg` has none) at the `!`: `@fail` as `META_ABORT`, ending the build, `@warn`
  as a `META_WARNING` warning.

`@Code` is source text with no syntax category of its own: the site that
splices it decides what it must parse as (an expression, a type, the entries of
a row, a pattern, fields, variants or items) and checks it there. An effect-row
splice `<!X>` stands for one or more entries.

`!` discharges `<@Meta>` and nothing else, so it is **hermetic**: a generator
cannot perform `@IO`. Compile-time IO lives in `@build` alone (section 11.4).

Empty code inserts nothing. A site that runs only for its effect returns it, so
the directive disappears once it has run.

A syntax error in a fragment points into the string literal that spells it,
escapes accounted for, even when that literal is in a helper the `!` calls. A
fragment built at compile time (`"a" ++ b`, or a quotation with holes) has no
such literal, so the error points at the `!` and quotes the fragment.

## 11.2 Quotations
A string literal expected as `@Code` is a **quotation**: its text is source. It
is the `@Code` case of the type-directed literal (section 1.6), resolved through
CORE's `@IStrLit @Code` and `@IInterp @Code @Code` instances, so no call builds
it. Its holes run in the generator, and what a hole pastes depends on its type:

| Hole type | Pasted |
|---|---|
| `@Code` | its source, as is |
| a number, `Bool`, `@Str` | the literal spelling its value: `3`, `Bool.True`, `"hi"` |

```ares
$ times : @Int -> @Code -> @Code = \n c => "(?(c)) * ?(n)"
$ sum   : @Code = "1 + 2 * 3"
$ x     : @Int = !times 3 sum                   # inserts `(1 + 2 * 3) * 3`
$ greet : @Str -> @Code = \s => "?(s) ++ \"!\""
$ hi    : @Str = !greet "hi"                    # inserts `"hi" ++ "!"`
```

A hole pastes code bare, so the quotation decides precedence: write `(?(c))`
where it matters. A `@Str` hole is always a string literal; to paste a computed
name or other text as code, convert it with `@code : @Str -> @Code`, as in
`"$ ?(@code name) : @Int = 1"`. `@code` is also how a generator turns text it
built (`join ", " fields`) into code. Neither checks syntax: the splice site
does. `@parse_str` remains for code that only exists at run time; it checks the
text as an expression on the spot.

A quotation is **hygienic**. A name it spells means what it means where the
quotation is written: a generator's `scale` is its own module's `scale`, even
where the code lands in a module with a `scale` of its own. A binder it spells
binds only names the same quotation spells, so a generator's `let tmp` never
captures the caller's `tmp`. Code the site hands in keeps the site's meaning: a
quotation written in the `!` operand itself, and `@code` text.

```ares
$ @import ARESxOPT
$ plus_one : @Code -> @Code = \c => "let tmp = 1 in tmp + ?(c)"
$ add_one  : @Int -> @Int = \tmp => !plus_one "tmp"      # tmp + 1, the caller's tmp
$ some_of  : @Code -> @Code = \v => "Opt.Some.{?(v)}"
$ or_zero  : Opt @Int -> @Int = \ | !some_of "x" => x | _ => 0
```

So a generated pattern binds a name for the arm body only when the site names
it, as `!some_of "x"` does. The splice site renames a generator's binders apart
(`tmp__6`) and qualifies the names it reaches (`GEN.scale`), which `ares expand`
shows; operators and effect operations resolve at the site.

A string literal expected as CORE's `Template` is a **macro argument**:

```ares
$ Template : @Type = @struct pieces: @Vec @Str, holes: @Vec @Code
```

Its pieces stay text and its holes are **quoted**, not evaluated, since they
name what is in scope where the literal is written, which at a `!` is often a
run-time parameter. `@check` at that `!` sees the locals in scope there, so a
macro learns a hole's type:

```ares-fragment
$ sql : Template -> <@Meta> @Code = ...   # numbers the holes `$1`, `$2`, ...
$ by_name : @Str -> @Int -> Query = \name age =>
    !sql "SELECT id FROM users WHERE name = ?(name) AND age > ?(age)"
```

`sql` receives `pieces = ["SELECT id FROM users WHERE name = ", " AND age > ", ""]`
and the code `name` and `age`, whose types `@check` reports as `@Str` and
`@Int`. A hole is pasted back as the site's code, so it keeps the site's
meaning. A literal with no holes is a `Template` of one piece.
`examples/META_TEMPLATE.ares` is the whole macro.

## 11.3 Compile-time assertions and build directives
There is no `@assert` builtin. `CORE.assert : Bool -> @Str -> <@Meta> @Code` is
one line of ordinary Ares over `@abort` that returns empty code, so a module
states its own invariants and checking it is testing it.

```ares
$ fib  : @Int -> @Int = \n => if n < 2 => n else fib (n - 1) + fib (n - 2)
$ fact : @Int -> @Int = \n => if n == 0 => 1 else n * fact (n - 1)
$ !assert (fib 10 == 55) "fib 10 should be 55"
$ !assert (fact 5 == 120) "fact 5 should be 120"
```

A failing assertion, like any `@abort`, is an `error[META_ABORT]` carrying the
message, pointed at the `!` site. A fault the code runs into on its own (a
division by zero, a failed match) stays a `RUNTIME_FAULT`.

`@link` / `@link_path` steer the compilation itself: they add a library to the
link line and the dlopen set, or a directory to the search path. Both return
empty code.

```ares
$ !@link "m"             # link/preload libm
$ !@link_path "/opt/lib"
```

## 11.4 `@build`, the compile-time entry
`@build` is to compiling what `@main` is to running: the one name the *build*
starts from. The compiler runs it during compilation and adds the items of the
`@Code` it returns to the module that declared it. Like the entry, it has exactly
one accepted signature.

```ares
$ @build : {} -> <@Meta, @IO> @Code =
	"$ answer : @Int = 42"

$ @main : @Vec @Str -> <@IO> @Int = \args => answer      # 42
```

The `<@IO>` in that row is its whole privilege: `@build` is the one context where
a generator may read the world. The IO itself is not special, and there is no
compile-time IO primitive: it is `library/ARESxIO.ares` over the `C` namespace, the
same code a program runs, performed by the compile-time interpreter. So a
compile-time path is relative to the **working directory**, exactly like a path a
running program opens. `ARES.read_dir` (a directory's entry names, sorted) is the
listing a `@build` usually wants.

Rules: every module may have one (not just the root, unlike `@main`), it runs
once, and it runs before any `$ !` of that round, so code it generates is
available to the rest of the compile-time code. Anything it injects is itself
expanded, so a generated `$ !` still runs and a generated `$ @import M` loads M.
Note what "every module" implies: importing a module lets its `@build` perform IO
during *your* build, the same trust an imported `build.rs` carries.

`tests/MAIN.ares` is the worked example: it reads `examples/` at compile time and
generates its own imports and `@main`, so adding an example to the corpus is
adding a file. See `examples/META_BUILD.ares` and
documentation/language/metaprogramming.md.

To see what a metaprogram produced, `ares expand <file> [MODULE]` prints the
source as the checker finally saw it: every `!` spliced and every
`@build`'s items appended. That is the view to debug a generator from, since
nothing else shows the generated text.

## 11.5 `BUILD.ares`, the project file
A program's own modules are found beside it (section 2). A project that keeps
them elsewhere says so in a `BUILD.ares`: the module `BUILD`, whose `@build` calls
`@import_path` once per directory to add to the module search, and `@option`
once per project option it sets.

```ares
$ @mod BUILD

$ @build : {} -> <@Meta, @IO> @Code =
    @import_path "source";
    @option "format.width" "120";
    @option "lints.unreachable_arm" "deny";
    ""
```

`@option "section.name" "value"` takes the value as text, read in the option's
kind; an unknown option or a value it does not accept is a `BUILD_SCRIPT` error.
An option not set keeps its default:

| Opt | Default | Accepts | Meaning |
|---|---|---|---|
| `format.width` | `100` | 40 to 400 | the line width `ares fmt` fits code into |
| `format.indent` | `4` | 1 to 16 | spaces per indentation level |
| `check.max_errors` | `20` | 1 to 10000 | the most errors `ares check` prints |
| `check.checker` | `frontend` | `frontend`, `kernel` | what checks a module: the compiler's checker, or the kernel for dependent modules (section 16) |
| `lsp.check` | `type` | `type`, `save` | check as you type, or only when a file is saved |
| `lsp.focus` | `roots` | `all`, `roots`, `one` | how loudly errors are shown (see `documentation/tooling/lsp.md`) |
| `lsp.debounce_ms` | `150` | 0 to 5000 | how long typing must pause before the file is checked |
| `lsp.grace` | `true` | `true`, `false` | hold back errors in the definition being typed |
| `lsp.grace_ms` | `1500` | 0 to 60000 | the pause after which held-back errors are shown |
| `lsp.max_diagnostics` | `50` | 1 to 10000 | the most diagnostics shown per file |
| `lints.unreachable_arm` | `warn` | `allow`, `warn`, `deny` | a match arm no value can reach |

An editor's settings override the `lsp` options for that editor. When
`BUILD.ares` fails, `ares fmt` and the language server report it and carry on
with the defaults; a compile stops.

The compiler looks for `BUILD.ares` in the root file's directory and then in each
directory above it, and runs the nearest one before it loads the program. Its
directories are searched for every root at or below it, after `--import-dir`
and before the program's neighbourhood. A path is relative to `BUILD.ares`.

Rules, each a `BUILD_SCRIPT` error:

- it declares `$ @mod BUILD` and its `@build` returns empty code;
- `@import_path` works only there, in any other module it faults;
- nothing imports `BUILD`.

`BUILD.ares` runs before its own directories are searched, so its imports see only
the standard library, its neighbours and `--import-dir`. `applications/alec` is
the worked example: `MAIN.ares`, `TEST.ares` and `BENCH.ares` sit at the top and
every module they import is in `source/`.

---

# 12. Intrinsic types and primitives

## 12.1 `Bool`
An ordinary CORE union, `$ Bool : @Type = @union False: {}, True: {},`, which the
engines hold as a machine boolean. CORE names its values `true` and `false`; a
pattern spells the constructor, `Bool.True` or `.True`, since a bare `true`
would bind a variable. `if`, guards, `&&` and `||` branch on it, comparisons
yield it, and the CORE function `not` negates it.

```ares
$ b : Bool = 3 < 4
$ chk : @Int = b |> \ | Bool.True => 0 | _ => 1
```

## 12.2 `@Array` (byte block)
Allocated with `@Array.{ n }` (n zeroed bytes). Primitives: `@array_len`,
`@array_get`, `@array_set`, `@array_push`, `@array_slice`, `@array_alloc`. `Str`
is a byte array, so these apply to strings too. An `@Array` also joins the `[..]`
literal, pattern, and slice surfaces through its `CORE` instances of the blessed
interfaces, like any other sequence.

Simple:
```ares
$ buf : @Array = @Array.{ 64 }
$ n : @Int = @array_len "hello"          # 5
```

Involved (build a string byte by byte, as CORE's integer stringifier does):
```ares
$ digit : @Int -> @Str = \d => @array_push "" (48 + d)   # push a byte onto a @Str
```

## 12.3 `@Vec` (growable vector)
A growable typed vector, wrapped by the `VEC` library over `@vec_new`,
`@vec_push`, `@vec_get`, `@vec_set`, `@vec_len`, `@vec_fill`.

```ares
$ @import ARESxALGO
$ @import ARESxVEC
$ v : @Vec @Int = push 2 (push 1 (new {}))   # VEC over @vec_* primitives
```

## 12.4 `to_string` (CORE) and interpolation
`CORE` (implicitly imported) provides `to_string` for `Str`, `Bool`, and `@Int`,
and the `Stream`/`range`/`count_from` prelude. String interpolation desugars
through `to_string`; extend it (7.3) for your own types.

```ares
$ s : @Str = to_string 42 ++ " " ++ to_string true      # "42 true"
```

## 12.5 `TARGET` reflection
The `TARGET` module (qualified, no import) reflects the compilation target: word
size, @Int bounds, and os/arch names, fixed at compile time.

```ares
$ wide : Bool = TARGET.int_bits == 64
$ name : @Str = TARGET.arch ++ "-" ++ TARGET.os     # equals TARGET.name
```

---

# 13. The `@`-sigil catalogue

A quick index of the `@`-forms and where each is documented above.

| Form | Kind | Section |
| --- | --- | --- |
| `@mod` | module header | 2.1 |
| `@main` | program entry | 2.5 |
| `@build` | compile-time entry | 11.3 |
| `@struct` `@union` `@effect` | type declarations | 6, 8.1 |
| `@extern` | foreign binding, builtin declaration | 10 |
| `@use` | instance (interface) parameter and explicit argument | 7.4 |
| `@ctx` | parameters solved by unification, and explicit arguments for them | 3.6, 16 |
| `@Type` `@l` `@max` `@imax` | universes and levels | 16 |
| `@axiom` | a postulate | 16 |
| `@Top` `@tt` `@Bottom` `@Eq` `@refl` `@transp` `@cast` `@Quot` `@qin` `@qelim` | kernel primitives | 16 |
| `@absurd` | the empty match | 5.1 |
| `@private` | visibility | 2.4 |
| `!` `@abort` | compile-time splice | 11 |
| `@link` `@link_path` | build directives | 11.2 |
| `@import_path` | module search, in `BUILD.ares` | 11.4 |
| `@cast` | integer-width reinterpret | 4.11 |
| `@Int8..64` `@Nat8..64` `@Float32/64` | sized numerics | 3.2 |
| `@I*` | blessed literal / indexing / range / interpolation interfaces | 1.4, 1.6, 9.5 |
| `@Ptr` `@Array` `@Vec` | built-in containers/pointer | 3.3, 12 |
| `@Tensor` | sized tensor type | 3.9 |
| `@array_len/get/set/push/slice/alloc` | array primitives | 12.2 |
| `@vec_new/push/get/set/len/fill` | vector primitives | 12.3 |
| `@tensor_index/length/create/concat/slice/...` | tensor primitives | 9.5 |

---

# 14. Compiler CLI

`ares [--target=ARCH-OS] <command> [file.ares] [args...]`. With no file the root
is `MAIN.ares` in the current directory (or the sole `.ares` file there).

| Command | Effect |
| --- | --- |
| `run` | run a program (needs `$ @main`) on the interpreter; extra args pass to it |
| `build` | compile a program to a native executable beside the source |
| `check` | run `@build`, expand metaprograms, run `$ !` checks, print inferred types |
| `expand` | print the source after expansion, to inspect what a metaprogram made |
| `emit-c` | emit standalone C to stdout |
| `parse` | print the parsed syntax tree |
| `lex` | print the token stream |
| `fmt` | format files in place; `fmt --check` only lists unformatted ones |
| `fix` | apply every fix the compiler is sure of, rechecking until none is left |
| `explain` | explain a diagnostic code (`ares explain TYPE_MISMATCH`) |
| `lsp` | run the language server on stdin/stdout (see `documentation/tooling/lsp.md`) |

Flags: `--target=ARCH-OS` cross-compiles (e.g. `x86_64-linux`, `wasm32-wasi`);
`-h` / `--help` prints usage.

```sh
ares run                       # run ./MAIN.ares
ares run app.ares a b           # run app.ares with args `a b`
ares check examples/FIB.ares    # a library module: type-check and run its checks
ares expand app.ares APP        # the source as the checker saw it, one module
ares build app.ares
ares --target=wasm32-wasi build app.ares
```

---

# 15. Standard library modules

Imported with `$ @import MOD` (except `CORE`, `C`, and `TARGET`, which need no
import). A brief map:

| Module | Contents |
| --- | --- |
| `CORE` | `to_string`, `compose`, `Stream`, `range`, `count_from` (implicitly imported) |
| `C` | libc/libm bindings and engine conversion intrinsics (qualified) |
| `MATH` | @Int/Real helpers, libm wrappers, int/real conversions |
| `STR` | string operations (`from_int`, `substr`, `contains`, `to_lower`, ...) |
| `LIST` | list operations (`sum`, `length`, `map`, ...) |
| `VEC` | growable vectors over the `@Vec` primitives |
| `MAP` `SET` | keyed containers |
| `OPT` `RESULT` | optional and result types |
| `PATH` | path manipulation |
| `RANDOM` | pseudo-random numbers |
| `IO` | console, file, and directory IO over the `C` namespace |
| `LA` | shape-checked linear algebra over sized tensors |
| `CPX` | complex math over `CORE`'s `Cpx`: parts, polar form, roots, transcendentals |
| `TARGET` | compilation-target reflection (qualified) |

---

# 16. Dependent types (preview, checked by the kernel)

Ares is becoming dependently typed, with observational equality (issue #406).
The parser already reads the whole language: types are expressions, so any
term may stand in a type position and a function type may stand in a term. The
compiler's checker does not take types as terms yet; it rejects these forms
(`UNSUPPORTED`). What checks them today is the observational kernel
(`crates/kernel`, see `documentation/type-theory/kernel.md`), for modules in a
project whose `BUILD.ares` sets `@option "check.checker" "kernel"`. There
`ares check` and the language server hand the module to the kernel, which
prints each global with its type; such a module is not compiled.

```ares-fragment
$ @mod NAT
$ Nat : @Type 1 = @union Zero: {}, Succ: Nat
$ add : Nat -> Nat -> Nat = \m n => Nat.elim (\_ => Nat) n (\_ r => Nat.Succ.{ r }) m
$ two : Nat = Nat.Succ.{ Nat.Succ.{ Nat.Zero } }
$ four : add two two ~ Nat.Succ.{ Nat.Succ.{ two } } = @refl (add two two)
```

## 16.1 Universes and functions

`@Type l` is the universe at level `l`; `@Type 0` holds the propositions, and a
type lives in exactly one universe. A level is a number, a level name, `l + n`,
`@max a b` or `@imax a b`. A function type may name its parameter and mention
it in its result, `(t: @Type 1) -> t -> t`; as in every definition, the
signature's leading named parameters are bound in the body (section 7.4), so
the identity is written `$ id : (t: @Type 1) -> t -> t = \x => x`.

A signature that starts with `@ctx {u: @l, ...} ->` binds levels. A use passes
them by name, `id @ctx {.u = 2} ...`, or leaves them out to be inferred. An
argument written `_` is inferred from the types around it:
`trans _ _ _ e f`.

## 16.2 Types as terms

A capitalized name with a signature defines a type, or a type family, as a term:

```ares-fragment
$ Frac : @Type 1 = {Integer, Pos}
$ Pred : Nat -> @Type 0 = \n => n ~ n
```

`{a, b}` is a pair where a pair type is expected, and otherwise the type of
pairs `{A, B}`; `{x: A, y: B x}` is a dependent pair type, and `p.0`, `p.1`
project. `$ name : T = @axiom` postulates `name`.

## 16.3 Inductive types

An inductive type is a union, declared as in section 6.3; the kernel needs its
universe's level, `$ D : @Type 1 = @union Tag: payload, ...`. A constructor's
fields may depend on the earlier ones, so a field can carry what its result's
index is built from:

```ares-fragment
$ Vec : (a: @Type 1) -> Nat -> @Type 1 =
    @union Nil: {} -> Vec a Nat.Zero, Cons: {m: Nat, h: a, t: Vec a m} -> Vec a Nat.Succ.{ m }
```

Constructor `Tag` of `D` is written `D.Tag.{ fields }`, or `.Tag.{ fields }`
when one constructor has that tag; the type's parameters are inferred. A
declaration adds the recursor `D.elim`, whose motive comes first after the
parameters, and for a type with parameters the projections `D.eq_Tag_f` from
`D a ~ D b` to the equality of field `f`'s types.

## 16.4 Equality, casts and quotients

`a ~ b` is the observational equality, a proposition computed from the type of
`a` and `b`: pointwise at functions, componentwise at pairs,
constructor-wise at inductive types. `@refl a` proves `a ~ a`;
`@transp t B u t2 e` transports a proof `u : B t` along `e : t ~ t2`;
`@cast A B e x` moves `x : A` to `B` along `e : A ~ B`. `@Top`, `@tt` and
`@Bottom` are truth, its proof and falsity, and `x |> @absurd` eliminates a
proof `x` of `@Bottom` at the type expected. `@Quot A R rr rs rt` is `A`
quotiented by an equivalence `R`, `@qin a` a class, and `@qelim P f resp q`
eliminates a class by a function `f` that respects `R`.

