# C01: complete spawn argument captures

The translator retains every field of the Zig argument tuple in source order. Empty captures use `Unit`; a single field preserves the existing scalar `Tgt` constructor; two or more fields use a right-associated product. The dispatcher applies every field to the worker. Pointer identities are copied with the tuple, while pointed-to bytes remain in shared memory.

`thread_tuples.zig` exercises empty and instantiated generic empty workers, four fields alternating values and pointers, copied scalar values changed by the parent after spawn, two workers sharing an atomic pointer while owning separate ordinary outputs, and Zig 0.16 Group async/concurrent workers. `native.zig` checks actual source behavior. The generated Lean runtime checks sixteen deterministic scheduling oracles, including rejection of two workers writing through the same ordinary pointers. These are sampled executions, not a proof over all schedules.

`ThreadTuples/Proofs.lean` kernel-checks the actual generated dispatcher for zero and four-field captures, plus the full captured target passed to `Tgt.spawnInit` (generated for programs with an empty or multi-field capture). A protocol records the captured tuple and the child private heap. Its fork theorems use `Owned.fork` with an explicit disjoint split of the parent's heap. The mixed-worker grant separates both ordinary output cells; the atomic-worker grant transfers its ordinary output and requires its private heap to be disjoint from the shared atomic resource. Sharing an atomic pointer requires a global invariant; capturing a pointer alone supplies no exclusive permission. The proofs introduce no additional axioms.

The generated `Tgt.captures` classifies every captured field from its AIR type. Here the classes are `[.value, .ptr out, .value, .ptr other]` for `mixedWorker` and `[.ptr out, .ptr shared, .value, .value]` for `atomicWorker`. `ownedProtocol mode` requires each child's private heap to satisfy the generated per-argument obligation `Capture.grant mode target.captures` (`ZigLean/Conc/Transfer.lean`). `atomic_spawn` covers a value + pointer + atomic tuple: the output cell is handed over (`Transfer.owned`), the atomic is `Transfer.shared` and disjoint from the child, and the copied values add nothing. `mixed_spawn` hands over two disjoint output cells. `worker_join` regains the joined child's whole part. Two negative theorems show that, when a pointer's mode is `owned`, the obligation cannot be discharged if the caller does not own that pointer's region. Marking a pointer `shared` hands the child no cells. Any access through that pointer must then be justified by the global invariant. `reused_output_rejected` covers an output cell already held by another thread, and `unowned_output_rejected` covers a parent with an empty part.

`Pipeline.lean` exercises all three spawn boundaries (`Thread.spawn`, `Io.Group.async`, `Io.Group.concurrent`) with zero, one, and four arguments; rejects wrong arity, an incompatible middle field, a non-tuple capture, and unsupported worker results; and checks const/alignment qualification across different local AIR type tables. It emits and kernel-checks the legacy scalar constructor without the new alias, three ordered fields, a nested tuple retained as one argument, and two independently converted pure-worker slices. A mutation swaps the second and third fields of a same-width tuple. The worker performs checked subtraction of the second and third arguments, so the mutation changes its error behavior even though the worker result is discarded; the dispatcher equality must stop proving.

## Qualification and provenance

`provenance.json` records the twelve required AIR roots, their hashes, inspected std Thread
source hashes, and the declared Zig 0.16.0 export profile. The checked source SHA-256 is
`77ecd985ecaf82efa54412941189af7b1eaed6e5338a90b1bc4eb20363336a9d`.
The export command uses `-target x86_64-linux -mcpu=baseline -OReleaseSafe
-fno-error-tracing`. The checked AIR is schema 12 and carries the exported
`abi64-le-v1` profile. This profile does not establish compiler preservation or T01
qualification. A stock host compiler supplies the separate native test; the patched
compiler supplies AIR. The exporter writes the generic `ZeroWorker(u8).run` and std
`atomic.Value(u32).init` roots under `~air2lean-sha256-*.json` names; inventory checks use
each file's `name` field.

### `groupMixed` group lifetime

`Group.async` and `Group.concurrent` attach tasks that `Group.await` or `Group.cancel` must
finish (Zig 0.16 `std/Io.zig`). An earlier `groupMixed` returned through
`try group.concurrent(...)` without either. With a failing `concurrent`
(`error.ConcurrencyUnavailable`), a `mixedWorker` already assigned by `group.async` could
still write `out` and `other` after the frame was freed. The source now uses the std idiom
`defer group.cancel(io)`; after a successful `await` the cancel is a no-op. The generated
model calls `groupCancelC` on all three exits.

`ThreadTuples/FallibleRuntime.lean` runs `groupMixed` translated with `--spawn-policy fallible`
under 256 deterministic oracles. Every schedule must return 680 or
`ConcurrencyUnavailable` without a memory error, with no group entry left and every child
joined. The suite must reach the path where both `async` tasks were assigned to children and
`concurrent` then failed. On the previous checked AIR this gate fails with `Zig.Error.illegal`
(schedule 8, stride 1). The model reports `illegal` both for an access to a freed block and for
a run whose main thread ends with an unjoined child, so the error code alone does not tell
which of the two occurred. Both follow from the missing await.
The native test runs the failing path with `std.Io.Threaded` `concurrent_limit = .nothing`. It
exercises the failure exit natively; it cannot itself detect a late write to a freed frame.

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

The checked `ThreadTuples/Gen.lean` has 410 lines and SHA-256
`c5918726a02a24ce1eb05f6d942da2e02d04e3ed5bf2bc4ba6c66b48c53d60a6`.
It was regenerated from the fresh schema-12 AIR of the fixed source. The only change from
the previous semantic body (408 lines) is the three `groupCancelC` calls in `groupMixed`; the
other generated definitions are unchanged. The validated profile header line is omitted, as
before:

```sh
.lake/build/bin/air2lean tests/roadmap/thread-tuples/air/0.16.0 \
  -o tests/roadmap/thread-tuples/ThreadTuples/Gen.lean \
  --namespace ThreadTuples --prefix thread_tuples.
```

For the `groupMixed` fix, a fresh Zig 0.16.0 twelve-root export of the fixed source passed,
including `atomic.Value(u32).init` and the instantiated generic worker. The export used a
patched compiler built from the current `zig-patch` exporter. All twelve AIR files were
replaced. Apart from schema and profile, `atomicShared`, `copied`, `genericEmpty`, `mixed` and
`groupMixed` changed body and type-table encoding. Only `groupMixed` changed the generated
Lean. All three stock native tests passed on arm64 Darwin in 5.2 seconds with 331 MiB peak
memory. The native command uses ReleaseSafe without a target/CPU override; it does not
assert an exact host CPU profile or correspondence with the Linux AIR target. Lean is pinned
to v4.34.0.
Recorded timings describe individual validation runs with existing build artifacts.

Current profile-aware translators prepend a validated profile record. The artifact
gate binds the raw retained AIR and full headered generated output in a temporary
receipt, then compares the complete semantic body to historical `Gen.lean`; it
kernel-checks the full generated module. Fresh export gates validate uniform schema
11/12 profiles and the exact function inventory. CI also binds fresh AIR and full
headered output, compares its semantic body, and kernel-checks that fresh module.
Only the validated generated profile header is excluded from the body comparison;
source, checked AIR, historical generated definitions, and origin receipts are
retained. These compatibility checks do not establish compiler preservation or
change the original qualification scope.

CI runs the complete scoped gate in the existing full nonmutation Zig 0.16.0 Linux job.
It checks matching patched/stock compiler versions, exports into a fresh `RUNNER_TEMP`
directory, compares fresh translation with checked generated Lean, and runs native/artifact
gates sequentially. The fresh four-root adapter export is also translated and kernel checked.
Shell gates run through `bash`; temporary evidence is cleaned up, with no new cache or upload.
Linux CI and Zig 0.14.1/0.15.2 live export/native qualification remain pending.

This is partial C01 qualification of the accepted spawn boundaries and their explicit
ownership obligations. Capturing an ordinary pointer grants no ownership; the fork proof
requires disjoint child heaps, while shared atomics require a global invariant. The generated
per-argument obligation decomposes only top-level pointer and slice fields. Aggregates that
embed pointers are `other`, and a protocol built on `Capture.grant` cannot discharge them.
A protocol may still use `Tgt.spawnInit` directly; `Capture.grant` does not force a client
to use it. Sixteen
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

The tuple-order mutant is counted only for normal Lean exit 1 with exactly one located `rfl` non-definitional-equality diagnostic at the dispatcher equality assertion. Import, I/O, syntax, signal exits and mixed/unlocated errors fail the gate. The guarded artifact gate passed this classification. Thirty-four offline guard tests and thirteen adversarial diagnostic/CI/environment tests accompany the gate. Both adapter Lean branches prepend the built repository library path and preserve an inherited `LEAN_PATH`, including an explicit `AIR2LEAN_LEAN` binary override.

The artifact gate regenerates Lean from checked AIR and compares it with checked `Gen.lean`, then checks the generated definitions, proofs, runtime samples, pipeline fixtures, and mutation. It needs no production repository and no Zig compiler. `AIR2LEAN_TRANSLATOR` can select an already-built translator; `AIR2LEAN_LEAN` can select the exact Lean binary, otherwise the gate uses `lake env lean`.

Fresh exports must include `filter`: the source functions and `atomic.Value(u32).init`. The atomic wrapper's load/fetchAdd methods inline into AIR operations; init remains a direct callee and needs its own AIR file. Refresh source/AIR hashes only after a successful fresh export and generated Lean check.

The accepted worker boundary is deliberately explicit: Thread workers return void, noreturn, or unsigned u8; Group workers return void or noreturn. Implicit coercions other than mutable-to-const pointers and sufficient-to-weaker pointer alignment require a source cast. Error-returning workers remain rejected until the std worker error/panic handling is modeled.
