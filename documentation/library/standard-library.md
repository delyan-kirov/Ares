# The standard library

The standard library is ONE module, `ARES`, written as ordinary Ares in parts
under `library/`: thin, readable code over the auto-injected `C` libc namespace
and the byte-vector primitives. Each part is a file `library/ARESxPART.ares`
that declares `$ @mod ARES`, and a program imports the parts it uses,
`$ @import ARESxVEC`, reaching their names bare or as `ARES.name` (or under an
alias, `$ @import V = ARESxVEC`). The parts share one namespace, so one name is
one definition across all of them (see documentation/language/module-resolution.md,
1e). It is deliberately separate from `CORE`, the implicitly imported prelude:
`CORE` holds what the language itself needs (the numeric types and operators,
`IEq`/`IOrd`, `List`, `Opt`, `Result`, the literal interfaces, `to_string` /
`from_str`), while `ARES` is a toolbox a program opts into.

## How it reaches a program

A distribution ships the standard library beside the binary, and the binary
finds it relative to its own path: `<prefix>/bin/ares` resolves
`<prefix>/library`, which is what the Nix package installs. The tree is
relocatable, so moving or copying it keeps working, and nothing reads an
environment variable. The same files are also embedded in the binary
(`crates/ares/src/stdlib.rs`, one `include_str!` per module), so a binary with
no distribution around it still runs: that is what a bare `cargo build` or
`cargo install` produces.

`DR::load_module` puts the two together. It searches on disk first, in this
order, and falls back to the embedded copy when nothing matches:

1. the `--import-dir=DIR` directories, in the order given;
2. the program's own neighbourhood: its `library/`, the `examples/` the combined
   test runner imports, then a module file sitting beside it;
3. the standard libraries on disk: one beside the program's own tree (a
   checkout's `library/`), then the ones this executable ships with.

So:

- the standard library is identically available to the interpreter, `emit-c` and
  `build`, inside a checkout and outside one;
- diagnostics name the file the source was read from, so a span stays a location
  a reader can open. For an embedded part that is `library/ARESxPART.ares`, the file
  it was taken from;
- a program pays only for what it reaches. Loading is lazy: `CORE`, `C`, and the
  modules a program actually imports, transitively, and nothing else;
- editing a `library/*.ares` in a checkout takes effect on the next run, because
  disk beats the embedded copy. `include_str!` is tracked in cargo's dep-info, so
  the embedded copy refreshes on the next `cargo build` as well;
- a new standard-library part has to be added to `stdlib::MODULES`. A test
  compares that list against `library/*.ares` and fails if they drift.

First match wins, so a `library/ARESxPART.ares` a program ships beside itself
replaces that part. That is the supported way to patch a part without touching
the distribution, with one thing to keep in mind: replacing a part the rest of
the standard library depends on means taking on its contract. A partial
`ARESxSTR` breaks `ARESxPATH`, which imports it. A directory only
counts as a standard library when it holds `CORE.ares`, so an unrelated
`library/` above a program is never mistaken for one.

## The parts

Convention: predicates (and predicate parameters) are `@Bool`-typed, matching
`if` and comparisons; three-way COMPARISONS (`cmp_int`, `cmp_str`, the `sort_by`
orderings) stay `@Int` (negative / 0 / positive). Where an operation needs
equality or ordering on a type parameter, it asks for CORE's `IEq` / `IOrd`
interface with `@use`, resolved by type at the call site (`Map`, `Set`). IO's
`write_file` / `append_file` / `remove_file` return `@Bool` success. Paired
results use the language's tuples (`{\`A, \`B}`, accessed `.0`/`.1`).

**Pipelines.** Every operation takes the value it works on LAST, so a chain of
them reads left to right: `xs |> filter p |> fmap f |> foldl g z`,
`m |> insert k v |> remove k2`, `s |> split "," |> fmap trim`. The arguments that
come first are what the operation is about (the key, the predicate, the needle).

**Shared names are interfaces.** The operations several containers have (`len`,
`fmap`, `filter`, `foldl`, `get`, `has`, `new {}`, ...) are each ONE definition in
`ARESxALGO`, an interface plus a generic function, and each container's part gives
its instances. `len m` and `len "abc"` resolve by type; a container whose part is
not imported has no instance, so import the parts whose types you use.

| part | contents |
|------|----------|
| `ARESxALGO` | the shared operations, each an interface: `len`, `is_empty`, `new {}`, `fmap`, `filter`, `filter_map`, `concat`, `append`, `reverse`, `to_list`, `from_list`, `get`, `get_or`, `has`, `remove`, `merge`, `fold`, `foldl`, `foldr`, `find`, `any`, `all`, `zip`, `take`, `drop`, `take_while`, `drop_while`, `nth`, `last`, `slice`, `unwrap_or`; iteration `for` / `formap` with the `Loop` effect (`break {}`, `continue {}`) and `forever` |
| `ARESxOPT`  | functions over CORE's `Opt` (`Some`/`None`): `is_some`, `is_none`, `opt_then`; an `Opt` is a container of at most one element, so it answers `fmap`, `for`, `formap`, `filter`, the folds, `len`, `any`, `all`, `find`, `to_list`, `concat`, `unwrap_or` |
| `ARESxLIST` | CORE's cons `List`, lazy in the tail (`fmap`, `filter`, `append`, `take`, `concat`, `zip` build cells as they are walked, so pipelines stream, and an infinite list is an ordinary one): `empty`, `singleton`, `head`, `tail`, `reverse_onto`, `concat_map`, `lookup`, `to_vec`, `from_vec`, and the ALGO instances |
| `ARESxVEC`  | the growable vector `@Vec \`T`: `fill`, `push`, `set`, `first`, `init`, `flat_map`, `intersperse`, `find_index`, `contains_by`, `lookup_by`, `span`, `split_at`, `partition`, `remove_first`, `zip_with`, `unzip`, `sum`, `product`, `minimum`, `maximum`, `sort_by`, `merge_by`, `from_c`, and the ALGO instances |
| `ARESxSTR`  | byte strings: `at`, `substr`, `eq`, `cmp_str`, `from_byte`, `starts_with`, `ends_with`, `index_of`, `index_of_from`, `contains`, `split`, `lines`, `join`, `trim`(`_left`/`_right`), `repeat`, `pad_left`, `pad_right`, `replace`, `count`, `map_bytes`, `to_upper`, `to_lower`, `is_space`/`is_digit`/`is_alpha`/`is_alnum`/`is_upper`/`is_lower`, `byte_set`; the code point `Char` (`"C"` literals, `char_code`, `char_of_code`, `chars`), and `fmap` / `for` / `foldl` over a string's characters |
| `ARESxMAP`  | `Map \`K \`V` (immutable AVL tree): `insert`, `insert_with`, `update`, `keys`, `values`, `map_values`, `min_entry`, `max_entry`, `m.[k]`, and the ALGO instances |
| `ARESxSET`  | `Set \`T` (ordered, over Map): `add`, `inter`, `diff`, and the ALGO instances |
| `ARESxMATH` | `min`, `max`, `clamp`, `abs` (any ordered type), `cmp_int`, `sign`, `even`, `odd`, `gcd`, `pow`; `sqrt`, `sin`, `cos`, `tan`, `exp`, `log` as interfaces (reals here, complex numbers in `ARESxCPX`); `pi`, `euler`, `floor`, `ceil`, `round`, `fmod`, `atan2`, int/real conversions |
| `ARESxCPX`  | complex math over CORE's `Cpx`: `zero`, `one`, `re`, `im`, `of_real`, `conj`, `magnitude`, `norm`, `arg`, `is_real`, `is_zero`, `scale`, `recip`, `div_smith`, `polar`, `from_polar`, `powi`, `sinh`, `cosh`, `tanh`, `roots_of_unity`, `roots`; `^` and the elementary functions by instance |
| `ARESxLA`   | linear algebra over `@Tensor n T`: `create`, `concat_tensors`, `row`, `col`, `transpose`, `dot`, `matmul`, `par_map_chunks`; `len`, `slice`, `fmap`, `par_map` by instance |
| `ARESxBITS` | named bitwise operations on the 64-bit `@Int` (CORE also has `&&&` `|||` `^^^` `<<<` `>>>` `~~~`): `band`, `bor`, `bxor`, `bnot`, `shl`, `shr_u`, `shr_s`, `zext`, `sext`, `pow2`, `bit_len`, `min_int`, `max_int`; IEEE 754 encodings `f64_bits`, `f32_bits`, `bits_f64`, `bits_f32` |
| `ARESxIO`   | `print`, `println`, `eprint`, `eprintln`, `print_int`, `println_int`, `read_line`, `read_file`, `write_file`, `append_file`, `remove_file`, `read_dir`, `env`, `now` (all `<@IO>`) |
| `ARESxPATH` | POSIX paths, pure `@Str`: `basename`, `dirname`, `extension`, `strip_ext`, `join_path`, `parts`, `is_abs` |
| `ARESxRESULT` | functions over CORE's `Result` (`Ok`/`Err`): `is_ok`, `is_err`, `map_ok`, `map_err`, `and_then`, `ok_opt`, `unwrap_or` by instance; the `Fail` effect, `try`, `try_or`, `untry`, `expect` |
| `ARESxRANDOM` | `Rng` (Lehmer / MINSTD): `seed`, `next`, `next_below`, `next_range` |
| `ARESxASYNC` | concurrency on one thread: the `Async` effect (`spawn`, `yield`, `chan`, `send`, `recv`) and `run_async`, a structured round-robin scheduler |
| `ARESxPAR`  | parallel tasks: `Future \`B`, `par`, `spawn`, `wait`, `both`, `par_with`, `spawn_with`, channels; over `@Vec`: `par_map`, `par_formap`, `map_chunks`, `par_fold` (see documentation/language/concurrency-design.md) |
| `ARESxSTM`  | `TVar` and the `Stm` effect |
| `ARESxDERIVE` | compile-time derives: `derive_show`, `derive_eq`, `derive_ord`, `fields_of`, `variants_of` |
| `ARESxSHELL` | the `ares shell` commands (`type`, `scope`, `help`, `quit`, ...) |

`@IO` is the one builtin effect, the outside world, and every IO function and
`C` binding that touches it is `<@IO>`. A finer effect (a GPU, a log) is an
ordinary `@effect` whose handler discharges into `@IO`.

### The map

`Map \`K \`V` is an immutable ORDERED map -- an AVL tree, the same design as
Haskell's `Data.Map` -- polymorphic in key and value. The key ordering is
CORE's `IOrd` interface: every operation that compares keys takes
`@use { o: IOrd k }`, found by type at the call site, so `new` is just the
empty map and any ordered key works (base types, tuples lexicographically,
anything `derive_ord` reaches). Lookup, insert and remove are
O(log n); `to_list`/`keys`/`fold` visit entries in ascending key order. Maps are values: `insert`/`remove` return an updated
copy and never disturb the original -- structural sharing makes that cheap
(path copying only). A MUTABLE hash table (Rust/Jai flavor) is future work,
now unblocked by `Vec`; see documentation/library/stdlib-design.md.

### The vector

`Vec \`T` is the generic growable vector: O(1) indexed access over elements
of any type (the byte vectors `Str`/`Array` cover the @Int-byte case). `Vec`
is an OPAQUE core type -- the type checker knows only its name and arity;
the behavior lives in the built-in primitives `vec_new` / `vec_fill` /
`vec_len` / `vec_get` / `vec_set` / `vec_push` (reserved names, like the
`array_*` family), and `library/ARESxVEC.ares` is the derived surface: `get`
returns `Opt` and `set` leaves the vector unchanged out of range (the raw
primitives FAULT), plus the ALGO instances. At runtime a
Vec is a variant tagged `"%vec"` whose payload fields are the elements, so
neither engine grew a new value kind. A Vec is a VALUE: mutators return an
updated vector and never disturb the original; the native backend reuses a
uniquely-owned (rc==1) spine in place for `set`/`push`, the same
opportunistic trick as the byte vectors.

### Fallible code: Result and the Fail effect

`ARESxRESULT` carries both shapes of fallibility and the bridges between them:
`Result` for storing outcomes as values, and the `Fail` effect for
propagating them. A function that may fail says so in its row
(`@Int -> <Fail> @Int`) and just calls `Fail.fail "msg"`; callers compose with
no plumbing (the row does what Rust's `?` does, implicitly), and a boundary
turns the possibility back into a value with `try` (giving a
`Result \`T Str`, Koka's `error<a>` pattern) or `try_or` (a default).
`untry`/`expect` re-raise a `Result`/`Opt` inside a failing computation.

## The libc seam (and its sharp edge)

IO goes through the injected `C` namespace, which DR extended with `fopen`,
`fclose`, `fgetc`, `fputs`, `fflush`, `fseek`, `ftell`, `write`, `remove`,
`getenv` and `time`, plus the libm functions (`sqrt`, `sin`, `cos`, `tan`,
`atan2`, `exp`, `log`, `floor`, `ceil`, `round`, `pow`, `fmod`). The
declarations name their libraries SYMBOLICALLY (`"libc"`, `"libm"`); where
the symbols actually live is resolved at the edge -- `TG::Target::soname`
for the interpreter's dlopen (on Linux libm is its own soname: Nix ships the
symbols only in libm.so.6 even though glibc >= 2.34 folded them into libc
for static linking; elsewhere the C library carries them), and a link-line
flag for the native backend (generated programs never dlopen). Two
deliberate compromises, both documented at the declarations in app/DR.cpp:

- **`FILE*` travels as `@Int`, not `Ptr`.** The handle is only passed back to
  the same functions or tested against 0 (NULL), and `==` is defined on @Int
  but not Ptr.
- **A C `int` return does not arrive sign-extended.** The FFI widens returns
  by the DECLARED Ares type; declaring libc's 32-bit `int` results as the
  64-bit `@Int` means a negative return (EOF, error codes) arrives as its
  zero-extended bit pattern, not a negative @Int. The stdlib therefore never
  tests `< 0`: success is `== 0` (exact under any extension), and
  end-of-stream is "not a byte", i.e. outside 0..255 (`IO.is_byte`) -- also
  exact under any extension. File reads are counted (`fseek`/`ftell`), not
  EOF-terminated. The principled fix is FFI awareness of C's `int` width
  (declare `Int32` and make sized ints usable, or a TG-provided `cint`);
  until then, new `C` declarations must follow the same rules.

Console output uses unbuffered `C.write` throughout (never mixed with C's
buffered stdout), so ordering is deterministic. `C.puts` remains for the
prelude's `assert` and quick scripts.

### Complex numbers

The TYPE is CORE's, not this module's: `Cpx` (fields `re`/`im`), the `i` literal
suffix, `+ - * /` on `Cpx`, and `to_string` all live in CORE, so `3.4 + 1.2i`
needs no import. An operator takes ONE type for both operands, so a real joins a
complex only through `of_real`. `ARESxCPX` adds everything else, in ordinary Ares
over libm through `C`.

Two notes on the arithmetic. CORE's `/` forms `|b|^2` directly, which is the
readable quotient but loses range near the float limits; `div_smith` is
Smith's algorithm, which scales by the larger component first and keeps it.
And `z ^ w` on two complexes goes through `exp`/`log` (principal branch, by the
`IPow Cpx` instance), so for an integer exponent prefer `z |> powi n`, which
multiplies and stays exact for small powers and at `z = 0`; one operator takes one
type for both operands, so an integer exponent is `powi` by name.

CORE's `IAdd Cpx` / `IMul Cpx` / `IZero Cpx` instances are what `dot` and
`matmul` resolve, so a `@Tensor n Cpx` flows through them with no tensor-side support.
`IEq Cpx` is in CORE too, so `==` works on a complex without a definition here.

## Testing

`examples/STDLIB_{CORE,LIST,STR,CHAR,MAP,RESULT,RANDOM,IO,SET,PATH,VEC,PAR,ASYNC}.ares`
exercise the
library and run in BOTH engines via the combined runner (tests/MAIN.ares):
`thrax corpus` (both engines, output diffed). The IO
test round-trips a file under /tmp and cleans up after itself; the MAP test
stresses the AVL balance with 200 ascending inserts (the classic worst case
for an unbalanced BST); the RANDOM test pins the exact MINSTD sequence.

## A note on inference

A context requirement is resolved at the enclosing definition's BOUNDARY, after
numeric defaulting, not at the call site: that is what lets `p.snd == "one"` (a
polymorphic struct projection feeding `==`) find `IEq @Str` rather than defaulting
to `@Int` first. Everything that used to need an operator-resolution fixpoint over
competing candidates is gone with overloading; what remains is one search per
requirement, by type, over a flat instance index.

## Future work

See documentation/library/stdlib-design.md for the full inventory-driven roadmap (Koka/Jai
module surveys, the mutable hash table, tuples, SET/PATH/DIR/PROCESS/...).
Smaller items:

- A guard against user modules merging with stdlib module names.
- `Real` formatting and parsing in STR (`gcvt`-style via libm/libc),
  buffered readers.
- Proper C `int` FFI marshalling (kills the `is_byte` idiom).
- Migrate IO's error reporting from @Int codes / Opt to `Result` with a
  standard `Error` union, or `<Fail>` rows, once the shape settles.
