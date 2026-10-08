# Comptime-resolved locals (Q01 fuzz seeds 18, 19, 39)

When Sema can resolve a local's value at compile time (a `const` whose address is taken,
`const u: U = .{ .b = 0 }; _ = &u;`), it stores the value in a constant global, redirects every
live use of the local's pointer to that global, and rewrites the local's now-dead `alloc` and
stores to `bitcast`s of the integer 0 to the `alloc`'s pointer type
(`finishResolveComptimeKnownAllocPtr`; 0.15.2 and 0.16.0). Liveness marks these placeholders and
their field pointers unused, so the compiler generates no code for them. A source program cannot
produce such a `bitcast`: `@ptrFromInt(0)` to a non-`allowzero` pointer is a compile error.

The heavy Zig differential (`docs/fuzzing.md`) found that the translation of such a program did
not elaborate:

- The placeholders became `Zig.callM (Zig.ptrFromAddr 0)` in a function the translator
  treated as pointer-free (`Zig.M`), so the monads did not match. The same mismatch hit any
  `@ptrFromInt` in an otherwise pointer-free function.
- `mem0` holds the globals of every function, but `Zig.Enc` instances were emitted only for
  the global types of functions that use memory. When the local was in a pointer-free function and
  some other function used memory, `mem0` encoded the constant without a `Zig.Enc` instance.

No elaborating translation read a wrong pointer: live uses already referred to the global as
`⟨some k, 0⟩` (a global base), the placeholders were never read, and natively they are address 0
as well.

The translation now:

| AIR | Translation |
|---|---|
| placeholder `bitcast` of address 0 to a non-`allowzero` pointer, and its pointer projections, read only by each other and debug instructions | dropped (`Canon.lean`, `dropDeadAllocPlaceholders`) |
| such a placeholder that another instruction reads | rejected: `INSTRUCTION_FAILURE`, "a read of the address-0 placeholder ..." |
| integer-to-pointer `bitcast` (`@ptrFromInt`) | the function uses memory (`Memory.lean`) |
| a global of a pointer-free function when the program has `mem0` | its type gets a `Zig.Enc` instance (`Emit.lean`, `encTypeNames`) |

Fixtures (AIR exported by the patched 0.16.0 compiler, `-OReleaseSafe -target x86_64-linux
-mcpu=baseline`):

- `fuzz_s19.zig`: the shrunk fuzz reproducer; `FuzzS19/Gen.lean` is its retained translation.
- `const_locals.zig`: the fuzz case next to a function that uses memory (`dead`, `stack`), a
  live pointer to a comptime-resolved local passed to a callee (`live`, `read`), and
  `@ptrFromInt` in a pointer-free function (`roundTrip`). `ConstLocals/Gen.lean` is its retained
  translation.

`provenance.json` records the source, AIR and compiler hashes (`test_cli.py` checks the AIR and
source hashes; `scripts/coverage.py` counts both AIR directories as compiler fixtures).
`ConstLocals/Proofs.lean` checks with `#guard` that `mem0` block 1 is `live`'s constant, that a
read through its global base `⟨some 1, 0⟩` and every entry point return the values that
`zig test` checks natively. `test_cli.py` checks the retained translation byte for byte and
rejects two edited inputs that read a placeholder, directly or through a field pointer.

```sh
lake build air2lean ZigLean
bash tests/roadmap/const-locals/check.sh
AIR2LEAN_ZIG_NATIVE=/path/to/stock/zig-0.16.0 bash tests/roadmap/const-locals/check.sh --native
AIR2LEAN_ZIG_AIR=/path/to/patched/zig-0.16.0 bash tests/roadmap/const-locals/check.sh --export
```

Scope: 0.14.1 leaves a `bitcast` of a `u8` 0 to `u8` instead, which is a pointer-free no-op and
needs no rule. The native checks run on the host target; the AIR targets x86_64 Linux.
