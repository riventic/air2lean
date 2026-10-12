# Language long tail (L09, L10)

Compiler-exported fixtures for the open L rows that real Zig code needs first. The order follows
what each item unblocks in the std modules the allocator, thread and IO tracks translate
(`std.heap`, `std.Thread`, `std.Io.Threaded`, `std.mem`, `std.fmt`), measured by translating
their closures (`--diagnostics-json`, Zig 0.16.0, x86_64-linux ReleaseSafe):

| Source | Row | What it unblocks |
|---|---|---|
| `error_params.zig` | L10 | Error values as runtime parameters. A one-name error set (`error{Boom}`) or an error union has a runtime value in every supported Zig version (Zig's `Type.onePossibleValue` is null for every error set and error union), so its parameter has an AIR `arg`; the translator had treated it as one-possible-value and rejected the 47 `Io.Threaded.Syscall.fail(s, err: anytype)` instances. An enum has one value only when its tag has none (`u0`), not when it has one field. |
| `vector_casts.zig` | L09 (L07) | Zig ≤0.16 `@bitCast` with a vector side: `[n]T` ↔ `@Vector(n, T)` is lane `i` = item `i` (also for padded items such as `u24`), and every other vector cast reinterprets the vector's bit-packed memory image (`Zig.reprCast` over `Vec.packedEnc`, `ZigLean/VecCast.lean`). `std.mem.eql(u8, …)` on more than 16 bytes runs `mem.eqlBytes`, which compares `@Vector(16, u8)` chunks cast from arrays (`stdEql`). Zig 0.17.0 exports translate with its logical bit order (`docs/bitcast-semantics.md`). |

| File | Content |
|---|---|
| `air/<stem>/<version>` | exports of `<stem>.zig` by the patched 0.17.0, 0.16.0, 0.15.2 and 0.14.1 compilers (`export.sh`; `<stem>.filter` adds the std prefixes the fixture calls, and only the call closure of the fixture's own functions is kept), pinned by `provenance.json` |
| `LangLongTail/<Ns>.lean` | the retained 0.16.0 translation; `LangLongTail/<Ns>-<version>.lean` where a version translates to another text (std code that differs by version, 0.17's bit casts) |
| `Proofs<Ns>.lean` | kernel-checked properties of the 0.16.0 translation |
| `Model<Ns>.lean`, `probe_<stem>.zig`, `native/<stem>-<version>.txt` | the model's lines against the native probe of each version (recorded with stock compilers on aarch64-macos; CI re-runs the 0.16.0 probe on x86_64-linux) |
| `test_cli.py` | edited exports that must be rejected: a missing `arg` of an error parameter, a one-field `enum(u8)` parameter treated as one-possible-value, array items that do not fill whole bytes cast to another vector type, unequal bit sizes, non-byte lanes on a backend other than LLVM |
| `mutants.py` | semantic mutants of the retained translations that the native comparison must kill: a forwarded error replaced by another name, reversed lanes, an item-type cast copied lane by lane |

```sh
lake build ZigLean ZigLean.VecCast Air2Lean air2lean
bash tests/roadmap/lang-long-tail/check.sh
AIR2LEAN_ZIG_NATIVE_0_16=/path/to/zig-0.16.0/zig bash tests/roadmap/lang-long-tail/check.sh --native
```

To re-export: build the four patched compilers with `zig-patch/build.sh`, point
`AIR2LEAN_ZIG_AIR` at their parent directory, run `export.sh [STEM...]`, then
`python3 test_provenance.py --refresh`, retranslate the retained files and re-record `native/`.
