# C01: complete spawn argument captures

The translator retains every field of the Zig argument tuple in source order. Empty captures use `Unit`; a single field preserves the existing scalar `Tgt` constructor; two or more fields use a right-associated product. The dispatcher applies every field to the worker. Pointer identities are copied with the tuple, while pointed-to bytes remain in shared memory.

`thread_tuples.zig` exercises empty and instantiated generic empty workers, four fields alternating values and pointers, copied scalar values changed by the parent after spawn, two workers sharing an atomic pointer while owning separate ordinary outputs, and Zig 0.16 Group async/concurrent workers. `native.zig` checks actual source behavior. The generated Lean runtime checks sixteen deterministic scheduling oracles, including rejection of two workers writing through the same ordinary pointers. These are sampled executions, not a proof over all schedules.

`ThreadTuples/Proofs.lean` kernel-checks the actual generated dispatcher for zero and four-field captures, plus the full captured target passed to `Tgt.spawnInit` (generated for programs with an empty or multi-field capture). A protocol records the captured tuple and the child private heap. Its fork theorems use `Owned.fork` with an explicit disjoint split of the parent's heap. The mixed-worker grant separates both ordinary output cells; the atomic-worker grant transfers its ordinary output and requires its private heap to be disjoint from the shared atomic resource. Sharing an atomic pointer requires a global invariant; capturing a pointer alone supplies no exclusive permission. The proofs introduce no additional axioms.

`Pipeline.lean` exercises all three spawn boundaries (`Thread.spawn`, `Io.Group.async`, `Io.Group.concurrent`) with zero, one, and four arguments; rejects wrong arity, an incompatible middle field, a non-tuple capture, and unsupported worker results; and checks const/alignment qualification across different local AIR type tables. It emits and kernel-checks the legacy scalar constructor without the new alias, three ordered fields, a nested tuple retained as one argument, and two independently converted pure-worker slices. A mutation swaps the second and third fields of a same-width tuple. The worker performs checked subtraction of the second and third arguments, so the mutation changes its error behavior even though the worker result is discarded; the dispatcher equality must stop proving.

## Qualification and provenance

`provenance.json` records the twelve required AIR roots, their hashes, inspected std Thread
source hashes, and the declared Zig 0.16.0 export profile. The checked source SHA-256 is
`1e41b455969d69d9079cb8a6098a14b52a7df5faa7e05f205352d80ac67b5efc`.
The export command uses `-target x86_64-linux -mcpu=baseline -OReleaseSafe
-fno-error-tracing`. Schema 11 carries legacy/unverified target-profile metadata, so the
recorded flags do not establish target-profile preservation or T01 qualification. A stock
host compiler supplies the separate native test; the patched compiler supplies AIR.

The inspected Zig 0.14.1, 0.15.2 and 0.16.0 std `Thread.zig` implementations copy the entire
generic `Args` into child storage and invoke `@call(.auto, f, args)`. Zig 0.16 `Io.Group`
converts the capture to `std.meta.ArgsTuple`, copies the context by value, and calls the
worker with that tuple. AIR fields supply logical argument order; translation does not
assume tuple byte offsets or host layout. Source inspection alone does not qualify live
export or execution on a compiler version.

The dispatcher adapts captures to the shared worker declaration's type contract. Mutable
slices may pass to a const worker, and a sufficiently aligned capture may pass to a worker
requiring weaker alignment. The contract is independent of which capture is encountered
first. Multi-field dispatchers destructure once into reserved capture locals; zero/single-field
formatting preserves the existing constructors. Pipeline regressions cover mutable-to-const
slices, stronger-first/weaker-later `u64` slices, and a valid unaligned read. The standard
noreturn `debug.defaultPanic` call is recognized as `.panic`; foreign-name and returning-call
regressions keep that boundary explicit.

At implementation revision `1a27326`, the guarded artifact gate passed in 4.1 seconds with
530.5 MiB peak memory. It regenerated Lean from checked AIR, compared the output, and checked
kernel proofs, ownership obligations, sixteen deterministic runtime schedules, pipeline
adapters, and the tuple-order mutant. A separate fresh Zig 0.16.0 adapter export produced
exactly four roots: a shared const-slice worker and mutable, align(8), and align(1) captures.
Its translation and kernel elaboration passed. The adapter shell gate also passed through
both its default compiler invocation and an absolute `AIR2LEAN_LEAN` override with inherited
`LEAN_PATH` unset. These adapter checks establish export/translation/elaboration, not native
execution of that separate source fixture.

The checked `ThreadTuples/Gen.lean` has 398 lines and SHA-256
`61b61e629d96f44c62d7a40c585451bbcea121d4e14f5bacbd661ce4446ecc0a`.
It was regenerated from the unchanged checked AIR with the current dispatcher destructuring:

```sh
.lake/build/bin/air2lean tests/roadmap/thread-tuples/air/0.16.0 \
  -o tests/roadmap/thread-tuples/ThreadTuples/Gen.lean \
  --namespace ThreadTuples --prefix thread_tuples.
```

The earlier source qualification recorded in `provenance.json` at `61c7ced` passed a fresh
Zig 0.16.0 twelve-root export and translation, including `atomic.Value(u32).init` and the
instantiated generic worker. Both stock native tests passed on arm64 Darwin in 5.2 seconds
with 399 MiB peak memory. The native command uses ReleaseSafe without a target/CPU override;
it does not assert an exact host CPU profile or correspondence with the Linux AIR target.
The checked source and all twelve AIR hashes remain unchanged. Lean is pinned to v4.34.0.
Recorded timings describe individual validation runs with existing build artifacts.

CI runs the complete scoped gate in the existing full nonmutation Zig 0.16.0 Linux job.
It checks matching patched/stock compiler versions, exports into a fresh `RUNNER_TEMP`
directory, compares fresh translation with checked generated Lean, and runs native/artifact
gates sequentially. The fresh four-root adapter export is also translated and kernel checked.
Shell gates run through `bash`; temporary evidence is cleaned up, with no new cache or upload.
Linux CI and Zig 0.14.1/0.15.2 live export/native qualification remain pending.

This is partial C01 qualification of the accepted spawn boundaries and their explicit
ownership obligations. Capturing an ordinary pointer grants no ownership; the fork proof
requires disjoint child heaps, while shared atomics require a global invariant. Sixteen
schedules are finite samples, and the kernel ownership proofs do not establish general
lifecycle behavior or native weak-memory adequacy. No detached-thread, TLS, or foreign-memory
qualification is claimed.

## Run the gates

The scripts call compilers sequentially. During coordinated development, only the root validation queue may run these commands. A built translator and ZigLean/Air2Lean libraries are prerequisites.

```bash
python3 tests/roadmap/thread-tuples/guard-tests.py
python3 tests/roadmap/thread-tuples/mutation-tests.py
python3 tests/roadmap/thread-tuples/check-artifacts.py
bash tests/roadmap/thread-tuples/check.sh --check-artifacts

AIR2LEAN_ZIG_NATIVE=/path/to/stock-host-zig \
  bash tests/roadmap/thread-tuples/check.sh --native

AIR2LEAN_ZIG_AIR=/path/to/qualified-patched-zig \
  bash tests/roadmap/thread-tuples/check.sh --export /absolute/empty/output

AIR2LEAN_ZIG_AIR=/path/to/qualified-patched16-zig \
  bash tests/roadmap/thread-tuples/check.sh --adapter-contract /absolute/empty/adapter-output
```

The tuple-order mutant is counted only for normal Lean exit 1 with exactly one located `rfl` non-definitional-equality diagnostic at the dispatcher equality assertion. Import, I/O, syntax, signal exits and mixed/unlocated errors fail the gate. The guarded artifact gate passed this classification. Seventeen offline guard tests and thirteen adversarial diagnostic/CI/environment tests accompany the gate. Both adapter Lean branches prepend the built repository library path and preserve an inherited `LEAN_PATH`, including an explicit `AIR2LEAN_LEAN` binary override.

The artifact gate regenerates Lean from checked AIR and compares it with checked `Gen.lean`, then checks the generated definitions, proofs, runtime samples, pipeline fixtures, and mutation. It needs no production repository and no Zig compiler. `AIR2LEAN_TRANSLATOR` can select an already-built translator; `AIR2LEAN_LEAN` can select the exact Lean binary, otherwise the gate uses `lake env lean`.

Fresh exports must include `filter`: the source functions and `atomic.Value(u32).init`. The atomic wrapper's load/fetchAdd methods inline into AIR operations; init remains a direct callee and needs its own AIR file. Refresh source/AIR hashes only after a successful fresh export and generated Lean check.

The accepted worker boundary is deliberately explicit: Thread workers return void, noreturn, or unsigned u8; Group workers return void or noreturn. Implicit coercions other than mutable-to-const pointers and sufficient-to-weaker pointer alignment require a source cast. Error-returning workers remain rejected until the std worker error/panic handling is modeled.
