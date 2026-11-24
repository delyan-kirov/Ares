<p align="center">
<picture>
<source media="(prefers-color-scheme: dark)" srcset="documentation/assets/lockup-dark.svg">
<img src="documentation/assets/lockup-light.svg" alt="Ares programming language logo: Effects in a functional style" height="140">
</picture>
</p>

# Ares: a functional programming language with algebraic effects

Ares is a statically typed functional programming language built around
**typed algebraic effects and handlers**. It compiles to **native code through
C**, cross-compiles to **WebAssembly**, and also runs in an interpreter.

## Try Ares in your browser

**[Open the Ares playground](https://delyan-kirov.github.io/ares-applications/)**
to edit and run examples with no install. The playground runs the full compiler
and language server as WebAssembly, so programs are checked as you type.

## Why Ares

- **Algebraic effects and handlers.** Exceptions, state, generators, async,
  backtracking and probabilistic inference are all ordinary library code. The
  effects a function may perform are part of its type, and handlers get
  first-class continuations that can resume more than once.
- **Dependent types with observational equality (in progress).** Ares is
  growing into a dependently typed language based on observational type
  theory (OTT, after Pujet and Tabareau's TT^obs). The type-checking kernel
  exists as a prototype, and its consistency is proved in Lean.
- **Metaprogramming.** Compile-time code runs as ordinary Ares code.
- **Interfaces as implicit parameters.** The language supports implicit parameters
  that can be automatically infered during compile time. This single feature can do
  what Cpp can do with templates + inheritence + function overloading, all this in
  a much simpler and cleaner way.   
- **WebAssembly and native C.** One compiler targets native executables (C,
  with reference counting) and `wasm32`. Ares interfaces with C and WASM(javascript)
  seemlessly.

## Projects written in Ares

The [applications](https://github.com/delyan-kirov/ares-applications)
repository holds larger programs written in Ares:

- **[alec](applications/alec/)**: a C11 compiler that targets WebAssembly
  (wasm32 and wasm64), with every stage built on algebraic effects.
- **[xml](applications/xml/)**: an XML parser, serializer and query engine
  where backtracking comes from a multi-shot effect handler.
- **[zalmoxis](applications/zalmoxis/)**: a parallel line counter in the
  manner of tokei, running within about 1.3x of its speed.
- **[cbindgen](applications/cbindgen/)**: generates Ares bindings from C
  header files.
- **[launcher](applications/launcher/)**: a graphical program launcher on
  raylib through the C FFI.
- **[web](applications/web/)**: the browser playground itself.

## Examples

The **[examples](examples/)** directory has a small, commented program for
each language feature: effects, pattern matching, records, metaprogramming,
tensors, the standard library and more. Every example is also part of the test
suite, and its results are checked on both the interpreter and the native
backend.

## Documentation

- **[Language reference](documentation/language/language-reference.md)**: the
  syntax and meaning of every construct.
- **[Effect system](documentation/language/effect-system-design.md)**:
  effects, handlers and continuations.
- **[Interfaces](documentation/language/interfaces.md)**: `@Class` types,
  instance fields in `@ctx`, and how instances are found.
- **[Metaprogramming](documentation/language/metaprogramming.md)**:
  quotations, splices and compile-time code.
- **[Standard library](documentation/library/standard-library.md)**.
- **[Type theory](documentation/type-theory/kernel.md)**: the observational
  kernel, its [rule ledger](documentation/type-theory/LEDGER.md) and the Lean
  consistency proof.
- **[Native backend](documentation/runtime/native-backend.md)** and
  **[platforms](documentation/runtime/platforms.md)** (Linux, macOS, Windows,
  WebAssembly).
- **[Language server](documentation/tooling/lsp.md)** and
  **[error codes](documentation/tooling/errors.md)**.

## Building Ares from source

Ares builds with [Nix](https://nixos.org/download/):

```sh
nix develop      # enter the development shell
thrax build      # build the compiler
```

`thrax` is the repository's task runner, itself written in Ares. Run
`thrax help` for the full list of commands

Inside the shell, the `ares` compiler is on your `PATH`: `ares run FILE.ares`
interprets a program, `ares build FILE.ares` makes a native executable, and
`ares repl` for interactive session.

## License

Ares is released under the [MIT License](LICENSE).
