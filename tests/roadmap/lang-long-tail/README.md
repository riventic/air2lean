# Language long tail (L09, L10, L12)

Compiler-exported fixtures for the open L rows that real Zig code needs first. The order follows
what each item unblocks in the std modules the allocator, thread and IO tracks translate
(`std.heap`, `std.Thread`, `std.Io.Threaded`, `std.mem`, `std.fmt`), measured by translating
their closures (`--diagnostics-json`, Zig 0.16.0, x86_64-linux ReleaseSafe):

| Source | Row | What it unblocks |
|---|---|---|
| `error_params.zig` | L10 | Error values as runtime parameters. A one-name error set (`error{Boom}`) or an error union has a runtime value in every supported Zig version (Zig's `Type.onePossibleValue` is null for every error set and error union), so its parameter has an AIR `arg`; the translator had treated it as one-possible-value and rejected the 47 `Io.Threaded.Syscall.fail(s, err: anytype)` instances. An enum has one value only when its tag has none (`u0`), not when it has one field. |
| `vector_casts.zig` | L09 (L07) | Zig ≤0.16 `@bitCast` with a vector side: `[n]T` ↔ `@Vector(n, T)` is lane `i` = item `i` (also for padded items such as `u24`), and every other vector cast reinterprets the vector's bit-packed memory image (`Zig.reprCast` over `Vec.packedEnc`, `ZigLean/VecCast.lean`). `std.mem.eql(u8, …)` on more than 16 bytes runs `mem.eqlBytes`, which compares `@Vector(16, u8)` chunks cast from arrays (`stdEql`). Zig 0.17.0 exports translate with its logical bit order (`docs/bitcast-semantics.md`). |
| `tls_pointers.zig` | L12 | Pointer-bearing `threadlocal` storage, the shape of `Io.Threaded`'s `threadlocal var current: ?*Thread = null`: each thread's instance starts from the same initial bytes (null, a pointer to an ordinary global, a string slice). `ModelTlsPointers.lean` runs the probe under 16 schedules, requires a dead thread's instance read through a leaked pointer to be `.illegal`, and kills two mutants (one shared instance; instances that outlive their thread). 0.14.1 writes a `threadlocal`'s address as a constant and is rejected (`tls_pointers.reject`). |
| `extern_storage.zig` | L12 | Pointer-bearing `extern` globals and the storage they reach: `ExternInit` gets the external blocks `storage` (`docs/generated-code.md` §Globals). Natively linked with `provider_extern_storage.c`; `ModelExternStorage.lean` runs the translation with the provider's definitions as `ext` and its static storage as the external blocks; `ProofsExternStorage.lean` proves the initialization order and `slotValue` from program start for every placement and every external state of that shape. |
| `error_ints.zig` | L10 | `@intFromError`/`@errorFromInt` over the compilation's numbering (`error-table.air2lean`, `docs/air-json.md` §Error table). The export is of the native probe's own compilation (`error_ints.export`), so codes and names are the native program's; `ProofsErrorInts.lean` proves the casts for every code and every numbered error. `error_ints_w8` is the same at `--error-limit 255` (8 bits); 0.14.1 is rejected there (its `@errorName` sign-extends codes that reach bit 7). |
| `runtime_lanes.zig` | L09 | Zig 0.14.1/0.15.2 lane stores at a runtime index (`vector_store_elem`) into bit-packed `u9`, `u24`, `bool` and `f80` vectors, a store through the lane pointer of lane `i` (`Zig.storeLaneAt`; `ProofsRuntimeLanes.lean`). 0.16.0 and later reject the source (`only_versions`). |
| `float_lanes.zig` | L09 | Comptime lane pointers into `@Vector(n, f80)`, whose lanes the LLVM backend bit-packs at an 80-bit stride: bit-pointers on the lane's bits (`Zig.Packed (Float fmt)`). 0.17.0 has no lane-pointer evidence and is rejected (`float_lanes.reject`). |

| File | Content |
|---|---|
| `air/<stem>/<version>` | exports of `<stem>.zig` by the patched 0.17.0, 0.16.0, 0.15.2 and 0.14.1 compilers (`export.sh`; `<stem>.filter` adds the std prefixes the fixture calls, and only the call closure of the fixture's own functions is kept), pinned by `provenance.json`. `<stem>.export` sets the exported program (`root_src`, as an executable), its name prefix (`module`), compiler flags (`args`), the native build's extra inputs (`native_extra`) and the versions that compile it (`only_versions`); `<stem>.reject` lists versions the translator must reject, with the diagnostic |
| `LangLongTail/<Key>.lean` | the retained 0.16.0 translation (or of the newest version that compiles the source); `LangLongTail/<Key>-<version>.lean` where a version translates to another text (std code that differs by version, 0.17's bit casts, the error numbering) |
| `Proofs<Ns>.lean` | kernel-checked properties of the 0.16.0 translation |
| `Model<Ns>.lean`, `probe_<stem>.zig`, `native/<stem>-<version>.txt` | the model's lines against the native probe of each version (`error_params`, `vector_casts` recorded with stock compilers on aarch64-macos; the batch-G fixtures built for x86_64-linux with the export's flags and run in a `linux/amd64` container; CI re-runs the 0.16.0 probes on x86_64-linux) |
| `test_cli.py` | edited exports that must be rejected: a missing `arg` of an error parameter, a one-field `enum(u8)` parameter treated as one-possible-value, array items that do not fill whole bytes cast to another vector type, unequal bit sizes, non-byte lanes on a backend other than LLVM, a function-pointer `extern`, an error-storage `extern`, a pointer-bearing `extern` beside error-bearing globals, integer/error casts without the numbering or with another compilation's (version, width, a duplicate name, too many errors), a runtime lane store on another backend, a read runtime lane pointer, `f80` lane pointers on another backend |
| `mutants.py` | semantic mutants of the retained translations that the native comparison must kill: a forwarded error replaced by another name, reversed lanes, an item-type cast copied lane by lane, `mem0` without the external storage, the numbering guessed from the program's own error set, the runtime lane store with a wrong lane count, an `f80` lane at a 64-bit stride |

```sh
lake build ZigLean ZigLean.VecCast Air2Lean air2lean
bash tests/roadmap/lang-long-tail/check.sh
AIR2LEAN_ZIG_NATIVE_0_16=/path/to/zig-0.16.0/zig bash tests/roadmap/lang-long-tail/check.sh --native
```

To re-export: build the four patched compilers with `zig-patch/build.sh`, point
`AIR2LEAN_ZIG_AIR` at their parent directory, run `export.sh [STEM...]`, then
`python3 test_provenance.py --refresh`, retranslate the retained files and re-record `native/`.
