# C01: complete spawn argument captures

The translator retains every field of the Zig argument tuple in source order. Empty captures use `Unit`; a single field preserves the existing scalar `Tgt` constructor; two or more fields use a right-associated product. The dispatcher applies every field to the worker. Pointer identities are copied with the tuple, while pointed-to bytes remain in shared memory.

`thread_tuples.zig` exercises empty and instantiated generic empty workers, four fields alternating values and pointers, copied scalar values changed by the parent after spawn, two workers sharing an atomic pointer while owning separate ordinary outputs, and Zig 0.16 Group async/concurrent workers. `native.zig` checks actual source behavior. The generated Lean runtime checks sixteen deterministic scheduling oracles, including rejection of two workers writing through the same ordinary pointers. These are sampled executions, not a proof over all schedules.

`ThreadTuples/Proofs.lean` kernel-checks the actual generated dispatcher for zero and four-field captures, plus the full captured target passed to `Tgt.spawnInit` (generated for programs with an empty or multi-field capture). A protocol records the captured tuple and the child private heap. Its fork theorems use `Owned.fork` with an explicit disjoint split of the parent's heap. The mixed-worker grant separates both ordinary output cells; the atomic-worker grant transfers its ordinary output and requires its private heap to be disjoint from the shared atomic resource. Sharing an atomic pointer requires a global invariant; capturing a pointer alone supplies no exclusive permission. The proofs introduce no additional axioms.

`Pipeline.lean` exercises all three spawn boundaries (`Thread.spawn`, `Io.Group.async`, `Io.Group.concurrent`) with zero, one, and four arguments; rejects wrong arity, an incompatible middle field, a non-tuple capture, and unsupported worker results; and checks const/alignment qualification across different local AIR type tables. It emits and kernel-checks the legacy scalar constructor without the new alias, three ordered fields, a nested tuple retained as one argument, and two independently converted pure-worker slices. A mutation swaps the second and third fields of a same-width tuple. The worker performs checked subtraction of the second and third arguments, so the mutation changes its error behavior even though the worker result is discarded; the dispatcher equality must stop proving.

## Qualification and provenance

`provenance.json` pins the source hash, checked AIR hashes and twelve-root inventory, std Thread source hashes, and the declared export profile. The actual export command uses Zig 0.16.0 with `-target x86_64-linux -mcpu=baseline -OReleaseSafe -fno-error-tracing`. The checked schema 11 AIR has legacy/unverified target-profile metadata, so these recorded flags do not establish target-profile preservation or T01 qualification. Native testing uses a stock host compiler separately from the patched AIR-only compiler.

The local Zig 0.14.1, 0.15.2, and 0.16.0 std `Thread.zig` implementations were inspected. Each copies the entire generic `Args` into child storage and eventually invokes `@call(.auto, f, args)`. Their source hashes are recorded. Zig 0.16 `Io.Group` converts the capture to `std.meta.ArgsTuple`, copies the context by value, and calls the worker with that tuple. AIR fields supply logical argument order, so translation does not assume tuple byte offsets or host layout. Source inspection alone does not qualify a compiler version; the manifest states which live validation has actually passed.

At source revision `61c7ced`, the root serialized validation queue passed the fresh twelve-root export (including `atomic.Value(u32).init` and the instantiated generic worker), regenerated translation, generated kernel proofs, sixteen deterministic runtime schedules, pipeline fixtures, and the tuple-order mutant. The complete artifact gate passed in 3.1 seconds (515 MiB peak memory); the stock Zig 0.16.0 native gate passed both tests in 5.2 seconds (399 MiB peak memory) on the arm64 Darwin host. The native command uses ReleaseSafe without a target/CPU override, so it does not assert an exact host CPU profile. Lean is pinned to v4.34.0. Local retained logs are:

- `/opt/dev/air2lean/.lake/review-resume/roadmap/thread-tuples-source16-closure.log`
- `/opt/dev/air2lean/.lake/review-resume/roadmap/thread-tuples-translation-closure.log`
- `/opt/dev/air2lean/.lake/review-resume/roadmap/thread-tuples-pipeline-repaired.log`
- `/opt/dev/air2lean/.lake/review-resume/roadmap/thread-tuples-native-first.log`

CI runs the complete scoped gate only in the existing full nonmutation 0.16.0 Linux job. It checks matching patched/stock compiler versions, exports into a fresh `RUNNER_TEMP` directory, compares the fresh translation with the checked generated file, and runs the native and artifact gates sequentially. Fresh temporary evidence is cleaned up; this gate adds no cache or upload. Linux CI and 0.14.1/0.15.2 live export/native qualification remain pending.

This is partial C01 evidence for complete zero/multiple-field captures and explicit ownership obligations at the accepted spawn boundaries. Sixteen schedules are finite samples. The change makes no detached-thread, TLS, foreign-memory or general lifecycle claim.

## Run the gates

The scripts call compilers sequentially. During coordinated development, only the root validation queue may run these commands. A built translator and ZigLean/Air2Lean libraries are prerequisites.

```bash
python3 tests/roadmap/thread-tuples/guard-tests.py
python3 tests/roadmap/thread-tuples/check-artifacts.py
bash tests/roadmap/thread-tuples/check.sh --check-artifacts

AIR2LEAN_ZIG_NATIVE=/path/to/stock-host-zig \
  bash tests/roadmap/thread-tuples/check.sh --native

AIR2LEAN_ZIG_AIR=/path/to/qualified-patched-zig \
  bash tests/roadmap/thread-tuples/check.sh --export /absolute/empty/output
```

The artifact gate regenerates Lean from checked AIR and compares it with checked `Gen.lean`, then checks the generated definitions, proofs, runtime samples, pipeline fixtures, and mutation. It needs no production repository and no Zig compiler. `AIR2LEAN_TRANSLATOR` can select an already-built translator; `AIR2LEAN_LEAN` can select the exact Lean binary, otherwise the gate uses `lake env lean`.

Fresh exports must include `filter`: the source functions and `atomic.Value(u32).init`. The atomic wrapper's load/fetchAdd methods inline into AIR operations; init remains a direct callee and needs its own AIR file. Refresh source/AIR hashes only after a successful fresh export and generated Lean check.

The accepted worker boundary is deliberately explicit: Thread workers return void, noreturn, or unsigned u8; Group workers return void or noreturn. Implicit coercions other than mutable-to-const pointers and sufficient-to-weaker pointer alignment require a source cast. Error-returning workers remain rejected until the std worker error/panic handling is modeled.
