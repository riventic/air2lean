# Premise and contract reference (D03)

This is the single indexed reference for the premises behind every shipped theorem in
`Proofs/` and every theorem-bearing roadmap, tutorial and case-study client. Each premise
has a stable ID. [premise-index.md](https://github.com/riventic/air2lean/blob/generated/docs/premise-index.md) lists, per theorem, the IDs it
uses. `scripts/premises.py` derives that index mechanically and checks it.

To read a proof: find the theorem in [premise-index.md](https://github.com/riventic/air2lean/blob/generated/docs/premise-index.md), then read each
listed premise below. The theorem holds in the model under those premises and its own
stated hypotheses. Nothing else in the runtime is assumed. A premise ID marked
*environment* is a model choice that the theorem quantifies over or fixes. A premise marked
*trusted* is believed, not proved. A premise marked *meaning* says what kind of statement a
proof makes (for example partial correctness).

```sh
python3 scripts/premises.py check            # fails on a stale index, undefined/orphan ID or unmapped module
python3 scripts/premises.py write            # regenerate docs/premise-index.md (not committed: a whole-tree
                                             # generated file, docs/ci.md; CI publishes it on the `generated` branch)
python3 scripts/premises.py explain parallelCounter_spec   # which tokens/modules caused each premise
python3 scripts/premises.py compiled --assurance .lake/assurance/assumptions.json --output premises.json --strict
```

## How premises are derived

The rules are in [assurance/premises.json](../assurance/premises.json). For each theorem,
the tool:

1. Strips comments and tokenizes the theorem's statement and proof. It resolves each
   identifier through the file's namespaces and `open` declarations, against declarations
   visible through its transitive imports. Three implicit forms are approximated:
   `x.f` on a binder or `variable` `x : T ...` resolves to `T.f` (generalized field
   notation); `.c` resolves to the inductive that declares constructor `c` when exactly one
   visible inductive does; and a visible instance is assumed used when every name in its
   instance type (for example `Enc ThreadId`) occurs in the closure.
2. Follows resolved project declarations (proof helpers, other theorems, generated `Gen.lean`
   functions and their callees) transitively. It stops at runtime (`ZigLean.*`) declarations
   and records their modules.
3. Maps every recorded runtime module through the reviewed `runtime_modules` table. It
   applies the token rules to every identifier and resolved name in the closure. `statement`
   rules see only the theorem's own hypotheses and conclusion.
4. Adds the profile of every generated module reached. Its first-line
   `-- air2lean-profile:` header selects PRF-02 (`abi64-le-v1`) or PRF-05 (`abi64-be-v1`); no
   header or `legacy-abi64-le` selects PRF-01. A generated import absent from the repository uses PRF-03.
   Each admission opt-in that the header records maps to its premises (`admissions`:
   `no-libc` selects MTH-05); an admission without a mapping fails the check. A committed
   example translation (`Proofs/<Ex>/Gen.lean`, a canonical body without a header) takes the
   opt-ins of `examples/<ex>/translate.args`, which every translation of the example uses.
   Adds the caller obligations of every generated definition reached: the translator writes
   `-- air2lean-premises: {"ALC-09":[0]}` on the line before a `def` whose parameter (here
   parameter 0) contains a `std.mem.Allocator` (ALC-09) or a `std.Io` (IOM-01). Only the IDs
   in `generated_markers` are accepted (`scripts/premise_markers.py` reads them), and a malformed marker or one that is not directly
   above a `def` fails the check.
5. Closes the set under the `implies` table and adds TRU-01 to every theorem.

The check fails if a runtime module with declarations has no mapping, if any ID is not
defined here, if a defined premise is referenced by no rule/module/report, if an import is
neither resolvable nor an allowed generated import, or if the committed index is stale.
Every theorem therefore has a derived premise set. TRU-01 alone means that the theorem
uses no runtime model.

**Limits of the source derivation.** Some implicit dependencies are still not visible in
source: simp sets such as `zig_unfold`, unification and tactic-generated terms, and field
notation on a value whose type is not written in a binder. The `compiled` mode applies the
same tables to the kernel dependency graph of `scripts/assumptions.sh`. That is the
authoritative closure for `Proofs/` and `ZigLean/`. It lists each theorem's `source_gaps`
(compiled premises absent from the source index) with the reason for each (`gap_via`).
`--strict` fails on any gap, and CI runs it after the audit, so the committed index is a
superset of the kernel-derived premises for every audited theorem.

**Reviewed compiled-mode gaps.** The first strict review of the 0.16.0 audit found 441
theorems with gaps. They were closed by general rules, not per-theorem entries:

- Struct updates such as `{ m with current := c }` mention every `Mem` field, including
  `allocPolicy` and `failAt`, in the kernel term. These fields are inert data; the policy acts
  only through the allocator modules. ALC-02 and ALC-03 therefore come from those modules and
  from policy-content tokens, not from the `Mem` fields or the `ByteRemapMode` type.
- The runtime model is layered, and `implies` records the layers: THR-01 implies SEM-02 (the
  scheduler runs over the block memory), and SEM-02 and SEM-03 imply SEM-01 (memory ops and
  loops return `Zig.Result`).
- `ZigLean.Conc.Word` and `ZigLean.Conc.WeakWord` map to THR-05: their ops and frame
  structures use the futex and `ZigLean.Conc.Lock` (`LocsKeep`, `AllLe`).
- Field notation on typed binders, unique `.ctor` names and instances are resolved as in
  step 1.
- A proof that names a runtime definition can unfold it, so the closure rules also see the
  tokens of its body (`simp only [allocBytes]` exposes `Zig.alloc`, STK-01). Only the proof of a
  theorem in the closure unfolds: a statement, or a generated definition that applies a runtime
  definition, keeps the constant, and a type (inductive, structure, class) has no body.
- A tactic applies library lemmas that the source does not name. `tactic_modules` maps the tactic
  token to the runtime modules whose lemmas it applies; `fsym` reaches `ZigLean.Sep.Full.AutoAll`,
  the union of every `@[fsym]` rule module (THR-01, ORD-01, OSM-01, THR-08, SEM-04 for the
  concurrent and mmap rules).
- A model binding's extern premise (EXT-03) is derived from a generated module's
  `-- air2lean-models:` record when the closure names one of the binding's declarations
  (`air2lean_model_<i>*`) or its implementation, as the audit derives it from the evidence
  axiom or implementation opaque.

Roadmap clients outside `Proofs/` have only the source derivation. Committed `Proofs/*/Gen.lean` files are the 0.16.0 translations;
`scripts/check.sh` replaces them per Zig version. The index describes the committed files.

## Index

| Category | IDs |
|---|---|
| Target and build profiles | [PRF-01](#prf-01) [PRF-02](#prf-02) [PRF-03](#prf-03) [PRF-04](#prf-04) [PRF-05](#prf-05) |
| Allocator policies | [ALC-01](#alc-01) [ALC-02](#alc-02) [ALC-03](#alc-03) [ALC-04](#alc-04) [ALC-05](#alc-05) [ALC-06](#alc-06) [ALC-07](#alc-07) [ALC-08](#alc-08) [ALC-09](#alc-09) [ALC-10](#alc-10) |
| Io interface | [IOM-01](#iom-01) |
| Thread creation and scheduling | [THR-01](#thr-01) [THR-02](#thr-02) [THR-03](#thr-03) [THR-04](#thr-04) [THR-05](#thr-05) [THR-06](#thr-06) [THR-07](#thr-07) [THR-08](#thr-08) [THR-09](#thr-09) [THR-10](#thr-10) [THR-11](#thr-11) |
| Memory ordering | [ORD-01](#ord-01) [ORD-02](#ord-02) [ORD-03](#ord-03) [ORD-04](#ord-04) [ORD-05](#ord-05) [ORD-06](#ord-06) |
| Timers and clocks | [TMR-01](#tmr-01) [TMR-02](#tmr-02) |
| Environment operations | [ENV-01](#env-01) [ENV-02](#env-02) [ENV-03](#env-03) |
| Device effects | [DEV-01](#dev-01) |
| Opaque math and floats | [MTH-01](#mth-01) [MTH-02](#mth-02) [MTH-03](#mth-03) [MTH-04](#mth-04) [MTH-05](#mth-05) |
| Inline assembly | [ASM-01](#asm-01) [ASM-02](#asm-02) [ASM-03](#asm-03) [ASM-04](#asm-04) [ASM-05](#asm-05) [ASM-06](#asm-06) [ASM-09](#asm-09) |
| Core runtime semantics | [SEM-01](#sem-01) [SEM-02](#sem-02) [SEM-03](#sem-03) [SEM-04](#sem-04) [SEM-06](#sem-06) [SEM-07](#sem-07) |
| External models | [EXT-01](#ext-01) [EXT-02](#ext-02) [EXT-03](#ext-03) [EXT-04](#ext-04) [EXT-05](#ext-05) [EXT-06](#ext-06) |
| OS page mapping | [OSM-01](#osm-01) |
| OS thread primitives | [OSF-01](#osf-01) [OSF-02](#osf-02) [OST-01](#ost-01) [OST-02](#ost-02) [OST-03](#ost-03) [OSY-01](#osy-01) [OSK-01](#osk-01) [OSK-02](#osk-02) [OSG-01](#osg-01) [OSM-02](#osm-02) |
| Compiler and tool trust | [TRU-01](#tru-01) [TRU-02](#tru-02) [TRU-03](#tru-03) [TRU-04](#tru-04) [TRU-05](#tru-05) |

## Target and build profiles

<a id="prf-01"></a>
### PRF-01 — Legacy 64-bit little-endian reference model

- Kind: environment.
- Statement: The generated model assumes 64-bit pointers, little-endian bytes, 16-bit error
  codes and the reference type layouts. Target triple, backend, CPU, build mode, float mode
  and export stage are unverified.
- Derived from: a reached generated module whose header is absent or names `legacy-abi64-le`.
- Sources: [profiles.md](profiles.md#target-and-build-profiles), `Air2Lean/Air/Profile.lean`.

<a id="prf-02"></a>
### PRF-02 — Recorded `abi64-le-v1` schema-12 profile

- Kind: environment.
- Statement: The theorem concerns the analyzed AIR of exactly the target triple, CPU and
  features, build mode, error tracing, Zig version and float selection recorded in the
  generated module's `-- air2lean-profile:` header. It makes no shipping-binary claim
  (`export_stage: analyzed-air`). Changing the profile requires regenerating and rechecking.
- Derived from: a reached generated module whose header names `abi64-le-v1`.
- Sources: [profiles.md](profiles.md#target-and-build-profiles).

<a id="prf-03"></a>
### PRF-03 — Gate-time generated module

- Kind: environment.
- Statement: A client imports a generated module that its gate writes at run time (for
  example `import Gen`). The profile is the one recorded in that gate's generated header.
  The committed client source does not fix it.
- Derived from: an import listed in `generated_imports`.
- Sources: [global-payload-pointers README](../tests/roadmap/global-payload-pointers/README.md).

<a id="prf-04"></a>
### PRF-04 — Parameterized pointer width

- Kind: environment.
- Statement: The theorem uses the width-parameterized memory model (`Zig.PtrWidth`): pointers,
  `?*T`, `usize`, slices and `std.mem.Allocator` of `PtrWidth.bytes` bytes, and allocation
  byte counts bounded by `2 ^ bits`. For `.w32` it concerns the wasm32 layouts that the
  exporter recorded for the generated module's profile; the model's block addresses are not
  bounded by the 32-bit address space, so `@intFromPtr` of an address outside it is
  `.unspecified`. Every `.w64` definition is proved equal to the 64-bit model.
- Derived from: the runtime module `ZigLean.Mem.Width` or its width names (`PtrWidth`,
  `Slice32`, `SliceOf`, `Wasm32`).
- Sources: [generated-code.md](generated-code.md#pointer-width), `ZigLean/Mem/Width.lean`.

<a id="prf-05"></a>
### PRF-05 — Recorded `abi64-be-v1` big-endian profile

- Kind: environment.
- Statement: As PRF-02, for a big-endian target (s390x-linux): the theorem concerns the
  analyzed AIR of the recorded profile under the big-endian encodings of `Zig.BigEndian`
  (`ZigLean/Endian.lean`): integers, floats, slice lengths, packed backing integers,
  bit-pointer hosts and whole-byte vector lanes most significant byte first. Pointer and error
  bytes stay symbolic. The operations of the fail-closed list are absent. No shipping-binary
  claim; the native observations of `tests/roadmap/big-endian` are bounded evidence.
- Derived from: a reached generated module whose header names `abi64-be-v1`.
- Sources: [profiles.md](profiles.md#byte-order-big-endian), `ZigLean/Endian.lean`.

## Allocator policies

<a id="alc-01"></a>
### ALC-01 — Single modelled allocator

- Kind: environment.
- Statement: `std.mem.Allocator` is one modelled allocator. Each allocation is a fresh
  `.heap` block with undefined bytes. A zero-byte allocation has no block. A free must name
  the start and whole length of a live heap block, or it is `.illegal`. `free` records the
  slice poison write. Addresses are fresh unless a theorem selects the opt-in reuse policy
  (`ALC-08`). No native malloc address or identity behavior is modelled.
- Derived from: `ZigLean.Mem.Alloc`, `ZigLean.Sep.Alloc`; tokens `Allocator`.
- Sources: [std-models.md](std-models.md#allocator-model), `ZigLean/Mem/Alloc.lean`.

<a id="alc-02"></a>
### ALC-02 — Allocation failure and request-cap policy

- Kind: environment.
- Statement: `Mem.allocPolicy` (per-request `maxBytes`, finite failure indices, an arbitrary
  failure oracle `fails` and an optional live-heap `budget`) and the legacy `Mem.failAt`
  decide `OutOfMemory`. The default has no fixed cap; the differential harness selects its
  1 MiB cap explicitly. Theorems over arbitrary `Mem` quantify over every policy; a theorem
  that fixes initial memory fixes the policy. Neither cap nor budget is a resource guarantee
  of the host.
- Derived from: `ZigLean.Mem.Alloc`; tokens `[Aa]llocPolicy.maxBytes`, `[Aa]llocPolicy.failures`,
  `[Aa]llocPolicy.fails`, `[Aa]llocPolicy.budget`, `releaseAttempt`. The
  `Mem.allocPolicy`/`Mem.failAt` fields alone (for example in a struct update) do not select it.
- Sources: [allocation-policy.md](allocation-policy.md), [allocation-policy-report.json](allocation-policy-report.json).

<a id="alc-03"></a>
### ALC-03 — Byte remap policy

- Kind: environment.
- Statement: `remap` fails for nonzero-size items under the default policy. An explicit
  `Mem.allocPolicy.byteRemap` selects in-place or moved success for whole alignment-1 byte
  buffers. `resize` is outside the boundary.
- Derived from: `ZigLean.Sep.Remap`; tokens `remap`, `Remap` (not `ByteRemapMode`).
- Sources: [std-models.md](std-models.md#allocator-model), `tests/roadmap/resize-remap`.

<a id="alc-04"></a>
### ALC-04 — Byte sentinel allocation

- Kind: environment.
- Statement: `allocSentinel(u8, n, s)` allocates `n + 1` owned bytes with the sentinel at
  offset `n`. The payload is undefined. Only Zig 0.16.0 with an explicit `sentinel_byte` is admitted.
- Derived from: `ZigLean.Sep.Sentinel`; tokens `allocSentinel`, `freeSentinel`.
- Sources: [std-models.md](std-models.md#allocator-model), [byte sentinel README](../tests/roadmap/byte-sentinel/README.md).

<a id="alc-05"></a>
### ALC-05 — Byte realloc and sentinel reallocation

- Kind: environment.
- Statement: `realloc(s, n)` of an alignment-1 nonsentinel `[]u8` (Zig 0.16.0) tries the
  selected byte-remap policy, then allocates `n` bytes, copies the retained prefix
  representation and poisons and frees the old block; allocation failure leaves `s` intact.
  Sentinel reallocation is the client composition over the absorbed `len + 1`-byte buffer
  with the sentinel stored at the new length; Zig rejects a sentinel-typed `realloc`.
- Derived from: `ZigLean.Sep.SentinelRealloc`; tokens `realloc`, `reallocSentinel`, `appendSentinel`.
- Sources: [std-models.md](std-models.md#allocator-model), [sentinel realloc README](../tests/roadmap/sentinel-realloc/README.md).

<a id="alc-06"></a>
### ALC-06 — Raw allocator interface contracts

- Kind: environment.
- Statement: the raw vtable calls are modelled by contract only (`vtableAlloc`, `vtableResize`,
  `vtableRemap`, `vtableFree`); the translator does not recognize them. Each requires an
  alignment `2 ^ k` with `k < 64` and a nonzero length; resize, remap and free also require
  the whole live heap block allocated with that alignment. A violation is `.illegal`.
- Derived from: `ZigLean.Sep.RawAlloc`; tokens `vtableAlloc`, `vtableResize`, `vtableRemap`, `vtableFree`, `rawAlignOk`.
- Sources: [allocation-policy.md](allocation-policy.md), [sentinel realloc README](../tests/roadmap/sentinel-realloc/README.md).

<a id="alc-07"></a>
### ALC-07 — Allocator identity, arena and fixed-buffer policies

- Kind: environment.
- Statement: `Mem.allocators[a]` is allocator `a`; its blocks have kind `.owned a`. A free,
  destroy or remap through one allocator of another's block is `.illegal`. An arena request is
  an `ALC-02` attempt; an arena free ends one block's lifetime; reset/deinit end exactly the
  arena's blocks. A fixed buffer pads from its base address, fails past its capacity and gives
  bytes back only for its last allocation. Owned blocks get fresh model addresses unless the
  reuse policy (`ALC-08`) selects a valid reused one; growing remap fails; reset records no race-check access. The translator does not route
  `std.heap` arena or fixed-buffer calls.
- Derived from: `ZigLean.Mem.Owned`, `ZigLean.Sep.Owned`, `ZigLean.Sep.ArenaClient`; tokens
  `AllocRef`, `Arena.`, `FixedBuffer.`, `Owned.`, `ownedFree`, `resetOwned`.
- Sources: [allocator-identity.md](allocator-identity.md), `tests/roadmap/allocator-identity`.

<a id="alc-08"></a>
### ALC-08 — Address reuse and provenance recovery

- Kind: environment.
- Statement: The placement oracle (SEM-07) may give a new block the address of a freed block.
  Block ids stay unique and every liveness check uses them, so lifetime theorems over arbitrary
  `Mem` hold under every placement (`FTriple.withPlacement`, `FTotalTriple.withPlacement`). `@ptrFromInt` of an address that two
  blocks cover (a dead and a live block, or one block's end and an adjacent block's start) is
  `.unspecified` under the default `.strict` provenance mode; the address-sensitive contract
  `.liveBlock` recovers the live block. A theorem that observes addresses holds only under the
  mode it states. No native allocator address behavior is claimed.
- Derived from: `ZigLean.Mem.Reuse`, `ZigLean.Sep.AddrReuse`; tokens `withPlacement`, `liveBlock` (the
  provenance mode; the default `ProvenanceMode.strict` that every `@ptrFromInt` unfolds to is not
  a token).
- Sources: [address-reuse.md](address-reuse.md), `tests/roadmap/address-reuse`.

<a id="alc-09"></a>
### ALC-09 — Caller-supplied `Allocator` behaves as the std model

- Kind: environment.
- Statement: a translated function with a parameter that contains a `std.mem.Allocator` is
  proved for the single model allocator of ALC-01, not for the allocator a caller passes. A
  theorem about it holds for a caller only if that allocator behaves as the model: every
  successful allocation is a fresh block, disjoint from all memory the caller can see; failures
  are `OutOfMemory` attempts of ALC-02; `remap` and `realloc` succeed only as ALC-03 and ALC-05
  allow; a free ends exactly that block. `std.heap.page_allocator` (its in-place shrinking
  `remap` of non-byte items, D-ALLOC-REMAP), a `FixedBufferAllocator` or arena over
  caller-visible memory (D-ALLOC-ALIAS), and user-written allocators are not covered.
  `tests/roadmap/model-inclusion` records which real std allocators stay within the model's
  outcomes for the allocator examples.
- Derived from: the `-- air2lean-premises:` marker of a reached generated definition
  (`generated_markers`); implies ALC-01.
- Sources: [std-models.md](std-models.md#caller-supplied-allocator-and-io), [architecture audit](architecture-audit/models.md), `Air2Lean/Emit.lean` (`interfacePremises`).

<a id="alc-10"></a>
### ALC-10 — Thread-safe allocator in concurrent code

- Kind: environment.
- Statement: In a concurrent run (`Zig.Sched.run`), the program's `std.mem.Allocator` is
  thread-safe: allocations and frees by threads that are not ordered by happens-before give
  disjoint blocks, as the model's allocator does. The model's allocator state (`nextAddr`,
  `allocs`, the policy) has no race footprint, so a non-thread-safe allocator used from two
  threads (`FixedBufferAllocator.allocator()`, a `DebugAllocator` with `thread_safe = false`)
  is outside the model. Every concurrent theorem carries this premise; it holds vacuously for
  a program that allocates from one thread only.
- Derived from: `ZigLean.Conc.Sched`.
- Sources: [std-models.md](std-models.md#allocator-model), `ZigLean/Mem/Alloc.lean`.

## Io interface

<a id="iom-01"></a>
### IOM-01 — Caller-supplied `Io` behaves as the std model

- Kind: environment.
- Statement: a translated function with a parameter that contains a `std.Io` is proved for
  the single model `Zig.Io` (THR-02, THR-04, THR-05), not for the `Io` implementation a
  caller passes. A theorem about it holds for a caller only if that `Io` behaves as the model:
  each `Group.async` and `Io.async` task gets a thread, runs in the caller or (`Group.async`)
  is deferred until `await`, as the run's environment (`Zig.Env`) allows; a `Group.concurrent`
  task is a new thread unless assignment fails; cancelation requests are delivered at the
  modelled cancelation points. User-written `Io`s are not covered.
- Derived from: the `-- air2lean-premises:` marker of a reached generated definition
  (`generated_markers`).
- Sources: [std-models.md](std-models.md#caller-supplied-allocator-and-io), [architecture audit](architecture-audit/models.md), `Air2Lean/Emit.lean` (`interfacePremises`).

## Thread creation and scheduling

<a id="thr-01"></a>
### THR-01 — Interleaving scheduler and partial-correctness meaning

- Kind: meaning.
- Statement: `Zig.Sched.run env dispatch fuel o main m0` interleaves threads only at sync ops.
  The environment `env : Zig.Env` is explicit in every statement: `env.io` (`Io.Threaded` on
  a stated CPU count, or any `Io` implementation) and `env.spawn` (assignment `available` or
  `fallible`); `Sched.run` has no default. The oracle `o` picks each turn. A data race between plain code is `.illegal`. A spec
  constrains every completed result for every oracle and fuel; out of fuel is `none`. No
  fairness or termination follows unless a theorem states it (see SEM-04, THR-07).
- Derived from: `ZigLean.Conc.Basic`, `ZigLean.Conc.Call`, `ZigLean.Conc.Sched`; implied by every THR premise.
- Sources: [std-models.md](std-models.md#thread-model), `ZigLean/Conc/Sched.lean`.

<a id="thr-02"></a>
### THR-02 — Thread spawn/join with the `available` policy

- Kind: environment.
- Statement: `Thread.spawn` is a sync op that always succeeds in an `available` environment
  (`env.spawn = .available`, a hypothesis of each theorem that needs it; in a `fallible`
  environment it may return a declared error). It copies the argument tuple and gives the child
  a copy of the parent clock. `join` waits for the child and merges its clock. Only the handle's
  owner (the spawner, or the thread an explicit transfer named, THR-10) may join, once. An owned
  handle neither joined nor detached at thread end is `.illegal`. The child protocol obligation
  (`spawnInit`) is explicit.
- Derived from: `ZigLean.Conc.Sched`; tokens `spawnC`, `joinC`, `spawnInit`.
- Sources: [std-models.md](std-models.md#thread-model), [generated-code.md](generated-code.md#atomics-and-threads).

<a id="thr-03"></a>
### THR-03 — Fallible thread assignment policy

- Kind: environment.
- Statement: The opt-in `fallible` translation policy adds explicit oracle wrappers with the
  declared spawn errors; a `fallible` environment (`Env.spawn`) lets every assignment fail. The per-caller budget `Mem.spawnLimit` (default none) removes
  assignment from the oracle range while the caller's live children reach it. WP rules must
  cover every oracle outcome.
- Derived from: `ZigLean.Conc.Spawn`, `ZigLean.Conc.SpawnLemmas`; tokens `SpawnPolicy`, `WithPolicyC`,
  `spawnLimit`, `spawnAdmits`, `assignmentCount`, `assignmentOutcome`, `assignmentChoiceC`.
- Sources: [spawn-failure.md](spawn-failure.md).

<a id="thr-04"></a>
### THR-04 — `Io.Group` tasks are model threads

- Kind: environment.
- Statement: `Group.async` is an oracle choice of the run's environment: a recorded task
  thread, the caller at once, or a task deferred until the group's `await`/`cancel` (gated).
  `concurrent` spawns a recorded task, or returns `ConcurrencyUnavailable` when the
  environment's assignment fails. `Group.await` joins the tasks in spawn order.
  `Group.cancel` gives each task a cancelation request (`Mem.cancels`) and joins it; a task's
  cancelation point (a cancelable futex wait, its own `Group.await`) delivers a pending request
  as `error.Canceled`. `main` is not an `Io` task and is never canceled.
- Derived from: tokens `groupAsyncC`, `groupDeferC`, `groupAsyncWithPolicyC`, `groupAwaitC`,
  `groupConcurrentC`, `groupCancelC`, `cancelPending`, `requestCancel`.
- Sources: [std-models.md](std-models.md#thread-model).

<a id="thr-05"></a>
### THR-05 — Futex model

- Kind: environment.
- Statement: A futex wait on a matching `u32` sleeps until a wake at that address, or returns
  spuriously in place of the sleep (an oracle choice, `Sched.spuriousWake`). The kernel's
  compare is an atomic read of the word (a plain write that races with it is `.illegal`). A
  wake of up to `n` waiters wakes the ones the oracle picks (no order is assumed); a sleeping
  waiter leaves the waiters only through a wake, a cancelation request or an OS interrupt
  (OSG-01). A wake adds no
  happens-before edge. No runnable thread with an unfinished thread is `Zig.Error.deadlock`.
- Derived from: `ZigLean.Conc.Lock`, `ZigLean.Conc.LockRules`, `ZigLean.Conc.Word`, `ZigLean.Conc.WeakWord`; tokens `futex`, `Futex`.
- Sources: [std-models.md](std-models.md#thread-model), `ZigLean/Conc/Call.lean`.

<a id="thr-06"></a>
### THR-06 — Darwin `os_unfair_lock` contract

- Kind: trusted.
- Statement: On macOS, `Thread.Mutex.DarwinImpl` stops at `os_unfair_lock_*`. The model is the
  lock's contract: an acquire `cmpxchg` 0→1 with a futex sleep, and a release `xchg` of 0
  with a wake, after an owner check (`Thread.mutexOwnerCheck`: an unlock by a thread that did
  not make the most recent acquire is `.illegal`, as the C function terminates the process). The C library is trusted to meet it. `Proofs/Threadsync/Lock.lean` elaborates
  its DarwinImpl proofs only for a macOS translation (`if_decl`). The committed Linux
  translation selects `FutexImpl`, so no indexed theorem currently lists THR-06.
- Derived from: tokens `osUnfairLock`, `DarwinImpl`.
- Sources: [std-models.md](std-models.md#thread-model), `Proofs/Threadsync/Lock.lean`.

<a id="thr-07"></a>
### THR-07 — Progress hints without fairness

- Kind: environment.
- Statement: `Thread.yield` and `spinLoopHint` are scheduling opportunities only. `yield`
  may return `SystemCannotYield`. No fence, happens-before edge or fairness follows. Total
  results hold for the finite single-task client in `ZigLean.Conc.Total`; any other
  termination claim names an explicit fairness premise such as THR-09.
- Derived from: `ZigLean.Conc.Progress`, `ZigLean.Conc.Total`; tokens `spinLoopHint`, `threadYield`.
- Sources: [progress-hints.md](progress-hints.md).

<a id="thr-08"></a>
### THR-08 — Protocol (rely-guarantee / CSL) proofs over all schedules

- Kind: meaning.
- Statement: `Conc.Proto.run_sound`/`run_safe` and the CSL/lock/word rules are
  kernel-proved. A client theorem holds for the protocol, global invariant, ghost state and
  ownership splits that it states or discharges. Strict-safety theorems additionally exclude
  every scheduler error, including races and deadlock.
- Derived from: `ZigLean.Conc.Logic`, `ZigLean.Conc.Csl`, `ZigLean.Conc.Own`, `ZigLean.Conc.Lemmas`, `ZigLean.Conc.Lock*`, `ZigLean.Conc.Word`, `ZigLean.Conc.Share`.
- Sources: [proofs.md](proofs.md), [rwlock-contracts.md](rwlock-contracts.md).


<a id="thr-09"></a>
### THR-09 — Eventually cooperative schedule (progress premise)

- Kind: environment.
- Statement: `Cooperative o`: from some oracle index on, every choice of `o` is option 0.
  The scheduler then runs the lowest-numbered ready thread, and each atomic read reads the
  newest message. It is a hypothesis of a progress theorem, never a property of the model:
  every oracle remains a legal schedule, and safety theorems quantify over all of them.
  Spin hints and `Thread.yield` do not establish it (`IdleLoop.Client.idle_starves`).
- Derived from: token `Cooperative`.
- Sources: [progress-hints.md](progress-hints.md#worker-idle-loop),
  `tests/roadmap/idle-loops/IdleLoop/Theorems.lean`.

<a id="thr-10"></a>
### THR-10 — Detached threads and explicit handle transfer

- Kind: environment.
- Statement: `Thread.detach` (Zig 0.16.0) consumes the owner's handle without a
  happens-before edge; the thread runs on, and `main`'s end ends the run as the process exit
  does, whatever detached threads still run: no detached thread takes a turn after `main`'s
  end, so its accesses after that point are not explored. A later join or detach of the handle is
  `.illegal`. `Thread.transferHandle` is a model step, not a `std` call: a proof or
  hand-written client inserts it where a handle passes to another thread, which then is the
  one thread that may join or detach it and must do so before it ends. The translator never
  emits it, so a translated thread that joins a handle it did not spawn is `.illegal`. A
  transfer to a thread that has already ended is not detected (its handle is then never
  consumed and no end check reports it). A
  strict-safety proof may order joins by a protocol rank (`Proto.rank`) instead of thread ids.
- Derived from: `ZigLean.Conc.Detach`; tokens `detachC`, `transferHandle`, `Thread.detach`.
- Sources: [std-models.md](std-models.md#thread-model), `Proofs/Detach/`.

<a id="thr-11"></a>
### THR-11 — `Io.Future` tasks and cancelation (0.16.0)

- Kind: environment.
- Statement: `Io.async` allocates a runtime record and spawns the task as a model thread, or
  runs it in the caller, as the run's environment picks (`SyncOp.asyncChoice`, `Env.spawn`)
  under every translation policy. `await`/`cancel` join it and return the result
  that it wrote. Only the spawner may consume a future, and an unconsumed future is `.illegal`.
  A cancelation request is delivered only at `Io.checkCancel`. Programs with `Future.cancel`
  whose tasks reach another cancelation point are rejected. Group support does not imply
  future support.
- Derived from: `ZigLean.Conc.Future`, `ZigLean.Conc.FutureLemmas`; tokens `asyncC`, `awaitC`,
  `cancelC`, `checkCancelC`, `futureProto`.
- Sources: [futures.md](futures.md).

## Memory ordering

<a id="ord-01"></a>
### ORD-01 — RC11 approximation for atomics

- Kind: environment.
- Statement: Each atomic location keeps a modification order of messages with release
  clocks. Reads may see any message not older than a happens-before or own observation.
  RMWs read a message with no RMW after it. Messages are write events (equal values stay
  distinct; a plain write of an equal value is its own message). The model admits more outcomes
  than RC11 (no SC order, read views not transferred through release/acquire), never fewer.
  Overlapping atomic accesses of another offset or size are `.unspecified`. Atomic pointees are
  integers, enums, bools, packed structs or single/many pointers (ORD-05). Under
  `--allocator-model translated` an `unordered` load may also read any message not older than
  one that happened before it, ignoring and not updating the thread's own read view.
- Derived from: `ZigLean.Mem.Thread`, `ZigLean.Conc.Word`, `ZigLean.Conc.AtomicWord`; tokens `atomicLoad*`, `atomicStore*`, `atomicRmw*`, `cmpxchg*`, `AtomicOrder`, `RmwOp`.
- Sources: [std-models.md](std-models.md#thread-model), `ZigLean/Mem/Thread.lean`.

<a id="ord-02"></a>
### ORD-02 — No load buffering in compiled code

- Kind: trusted.
- Statement: The compiled code exhibits no load buffering (the model has no promises). LLVM
  does not promise this for relaxed atomics. The translator rejects the straight-line shape
  (a relaxed read, then a relaxed write to another address, with no acquire-release or
  sequentially consistent op, call or branch between) unless `--assume-no-lb`; the check is not
  complete, so every theorem with atomics carries this premise.
- Derived from: implied by ORD-01.
- Sources: [std-models.md](std-models.md#thread-model) (**Trusted assumption**).

<a id="ord-03"></a>
### ORD-03 — `seq_cst` treated as `acq_rel`

- Kind: environment.
- Statement: There is no global SC order. A proof never relies on an outcome RC11 forbids,
  but proofs requiring the SC order (store buffering, Dekker) do not go through.
- Derived from: tokens `seqCst`.
- Sources: [std-models.md](std-models.md#thread-model).

<a id="ord-04"></a>
### ORD-04 — Weak CAS spurious failure

- Kind: environment.
- Statement: `cmpxchg_weak` may fail on a matching value with a failure-order read and no
  write, repeatedly. Its rules are safety-only; no retry liveness follows.
- Derived from: `ZigLean.Conc.WeakCas`, `ZigLean.Conc.WeakCasLemmas`, `ZigLean.Conc.WeakWord`; tokens `cmpxchgWeak`, `WeakCas`.
- Sources: [weak-cas.md](weak-cas.md).

<a id="ord-05"></a>
### ORD-05 — Pointer atomics keep provenance and compare identities

- Kind: environment.
- Statement: An atomic message of a `*T`/`?*T` pointee holds the pointer's bytes, which keep
  its block. `cmpxchg` compares identities (block, offset): equal identities succeed, different
  identities at different addresses fail, and different identities at the same address (or an
  address the memory cannot resolve) are `.unspecified`; the hardware compares addresses, and
  the model claims neither outcome. Only `.Xchg` is a pointer RMW.
- Derived from: `ZigLean.Mem.AtomicPtr`, `ZigLean.Conc.PtrAtomic`, `ZigLean.Conc.PtrAtomicLemmas`; tokens `AtomicPtrVal`, `ptrValEq`, `*PtrAt`, `*PtrC`.
- Sources: [pointer-atomics.md](pointer-atomics.md).

<a id="ord-06"></a>
### ORD-06 — Memory-model adequacy of the compiled code

- Kind: trusted.
- Statement: On the theorem's target, every behaviour of the compiled program is one of the
  model's outcomes: the backend's lowering of plain accesses and atomics and the hardware memory
  model (x86-TSO on x86_64, ARMv8 on aarch64) produce no outcome that the interleaving scheduler
  with its happens-before race check (THR-01) and the RC11 approximation (ORD-01) exclude. Not
  proved. The argument per target, and its bounded qualification evidence, are the `memory_model`
  record of [assurance/premises.json](../assurance/premises.json): a race between plain accesses
  is `.illegal`, so a theorem is about race-free executions (DRF-SC); the standard C11 mappings
  to x86-TSO and ARMv8 are proved sound for RC11, and ORD-01 admits every RC11 outcome; RC11's
  no-load-buffering axiom is ORD-02. LLVM's optimizer is assumed to respect the C++11 model.
  Targets in the record's `unqualified` list (wasm32, s390x) reject atomics and threads, so no
  theorem about them carries this premise.
- Derived from: implied by THR-01 and ORD-01, so every concurrency theorem carries it.
  `scripts/premises.py` (`check` and `compiled`) fails when a theorem or a report below whose
  premises contain THR-01 or ORD-01 omits it; `scripts/claims.py` lists it in each concurrency
  claim's `premises`.
- Sources: [research/C12.md](research/C12.md), [std-models.md](std-models.md#thread-model),
  [architecture-audit/concurrency.md](architecture-audit/concurrency.md).

## Timers and clocks

<a id="tmr-01"></a>
### TMR-01 — No clock in the default model

- Kind: environment.
- Statement: The default runtime has no clock. Reaching `time.Timer` or
  `Thread.Futex.timedWait` (0.15.2 `Futex.Deadline` with a timeout) is `.unsupportedTimer`,
  a model error kept apart from `.unspecified` (reports type it `unspecified_timer`).
  `Io.futexWaitTimeout` is rejected at translation. Theorems cover the no-timeout path only.
- Derived from: tokens `Deadline`, `time_Timer`, `timedWait`.
- Sources: [std-models.md](std-models.md#thread-model), `Proofs/Threadsync/Deadline.lean`.

<a id="tmr-02"></a>
### TMR-02 — Opt-in awake clock and timed scheduler

- Kind: environment.
- Statement: `Zig.Time.AwakeEnvironment` supplies bounded, monotone observations. The selected
  timed scheduler lets mismatch, wake, timeout and spurious returns compete through an
  oracle. `NoCancellation` is an explicit premise. No OS clock correspondence is claimed.
- Derived from: `ZigLean.Time`, `ZigLean.Conc.Timed*`; tokens `TimedSched`, `AwakeEnvironment`, `NoCancellation`.
- Sources: [deadline-runtime.md](deadline-runtime.md), [deadline-futex-design.md](deadline-futex-design.md), [deadline-cases.md](deadline-cases.md).

## Environment operations

<a id="env-01"></a>
### ENV-01 — Selected handle read/write/close contract

- Kind: environment.
- Statement: `Zig.Env.Ops` returns every read, write, open-handle and close result as a
  function of an arbitrary state, and theorems quantify over it. `Zig.Env.Contract` is the only
  assumption: on an open handle, a nonempty write accepts `0 < n ≤ len` bytes or returns an
  allowed enumerated `IoError`; reads return at most the requested bytes; reads and writes
  keep the open set; `close` releases exactly its handle. Closed-handle behavior is
  unconstrained. No OS, CPython or browser host correspondence is claimed.
- Derived from: `ZigLean.Env`.
- Sources: [env-boundaries.md](env-boundaries.md), `tests/roadmap/env-boundaries/WriteAll.lean`.

<a id="env-02"></a>
### ENV-02 — Distinct monotonic and wall clock observations

- Kind: environment.
- Statement: `Zig.Env.Ops.monotonicNow` and `wallNow` are separate state observations. No
  `Zig.Env` operation decreases the monotonic one. The wall clock has no ordering and may
  decrease. Neither is related to an OS clock or to `Zig.Time.AwakeEnvironment` (TMR-02).
- Derived from: tokens `monotonicNow`, `wallNow`.
- Sources: [env-boundaries.md](env-boundaries.md#operations).

<a id="env-03"></a>
### ENV-03 — Linux raw read/write/close are the bound models

- Kind: environment.
- Statement: On `x86_64-linux` without libc, each call of `std.os.linux.read`, `write` or
  `close` (one `syscall` instruction each) behaves as `Zig.Env.Linux.read`/`write`/`close` over
  the `Zig.Env.Host` installed in `Zig.Mem`: the raw `usize` result is the byte count or
  `-errno` for the six modelled errors (EAGAIN, EPIPE, ENOSPC, EACCES, EIO, ECONNRESET), `write`
  offers exactly the `count` bytes at `buf` and `read` stores the received bytes there. The
  models are stricter than the kernel: a descriptor that is negative or not open is `.illegal`
  (no `EBADF`, no reuse), and `EINTR`, other errnos, signals and blocking are not modelled.
  Everything above these three functions in std is translated from AIR, not assumed.
- Derived from: `ZigLean.Env.Linux` (with ENV-01 for the operations' contract).
- Sources: [env-boundaries.md](env-boundaries.md#bound-primitives),
  `tests/roadmap/env-boundaries/StdIo.lean`.

## Device effects

<a id="dev-01"></a>
### DEV-01 — Declared device: trace and read oracle

- Kind: environment.
- Statement: With `--device-contract`, every executed volatile load or store of an 8/16/32/64-bit
  integer is one event in `Mem.dev.trace`, in program order (`Zig.vload`/`Zig.vstore`). A read's
  value is `Mem.dev.oracle` applied to the whole trace so far, the address and the width; theorems
  quantify over the oracle or state which answers they need. Device registers are the declared
  addresses of the generated `air2lean_device`, reached through block-less pointers. A field or
  element pointer of a device pointer is formed inside the declared register window
  (`Zig.ptrProjectDevice`): the window is taken to be the allocation that LLVM's
  `getelementptr inbounds` requires, outside the model. The device
  neither observes nor changes model memory (no DMA, no aliasing of model blocks), so ordinary
  memory accesses are not events and their order relative to events is not claimed. Interrupts,
  other bus masters, timing, side effects of a read beyond the trace, and multi-threaded device
  access are outside the model. A declared `asm volatile` (`Zig.vasm`/`vasmEffect`) is an `asm`
  event of the same trace, with outputs from `Mem.dev.asmOracle`; a `memory` clobber is never
  declared. No correspondence with real hardware is claimed: the compiled
  program's volatile order is trusted to match the AIR order (TRU-03).
- Derived from: `ZigLean.Mem.Device`; tokens `vload`, `vstore`, `vasm`, `vasmEffect`, `DevOracle`, `AsmOracle`, `Device`, `ptrProjectDevice`,
  `DevState.oracle`, `DevState.asmOracle`. The `Mem.dev` field alone (for example in a struct update) does not select it.
- Sources: [volatile-effects.md](volatile-effects.md#device-contract), `tests/roadmap/volatile-effects/DeviceEffects/Proofs.lean`.

## Opaque math and floats

<a id="mth-01"></a>
### MTH-01 — Executable IEEE-754 float model

- Kind: environment.
- Statement: Float operations are the model's correctly rounded IEEE-754 operations
  (default `--float-semantics ieee`), with the documented NaN, signed-zero and f80 rules. No
  backend, CPU or optimization mode is qualified.
- Derived from: `ZigLean.Float.*` except `Libm` and `CompilerRt`.
- Sources: [floats.md](floats.md).

<a id="mth-02"></a>
### MTH-02 — Opaque libm transcendentals

- Kind: trusted.
- Statement: `Zig.Float.libm` is an opaque, uninterpreted function. No accuracy theorem
  exists. `implemented_by`/extern linkage supplies executable behavior only, and theorems
  can state results only in terms of the opaque.
- Derived from: `ZigLean.Float.Libm`; tokens `libm`.
- Sources: [floats.md](floats.md#transcendental-functions), [assumptions-audit.md](assumptions-audit.md), `assurance/policy.json`.

<a id="mth-03"></a>
### MTH-03 — Version-specific compiler-rt float semantics

- Kind: environment.
- Statement: Selected operations (f128 multiply/divide, `@mulAdd`, f80→f16, version-specific
  rounding) follow ported compiler-rt functions instead of correctly rounded IEEE results.
- Derived from: `ZigLean.Float.CompilerRt`; tokens `Rt016`, `mulRt`, `RtChk`, `…Xf3`, `fmaRtFused`; header `float_semantics: compiler-rt`.
- Sources: [floats.md](floats.md#--float-semantics-ieee--compiler-rt).

<a id="mth-04"></a>
### MTH-04 — aarch64 float lowering

- Kind: environment.
- Statement: The translation targets aarch64-macos or aarch64-linux, whose float lowering
  differs from x86_64's: `f80` is soft float (a noncanonical operand is unspecified; `__divxf3`
  division; before 0.16.0 `@sqrt` through `f64`) and `@mulAdd` on `f32`/`f64` is a fused
  instruction, on `f16` too where the baseline CPU has `fullfp16` (aarch64-macos `apple_m1`; not
  aarch64-linux `generic`, which rounds through `f32` like x86_64). The rules are those of the
  baseline CPU (`Target.floatRules`); they are read from the Zig 0.16.0 LLVM backend and
  compiler_rt sources and checked by each host's differential test. On aarch64-linux the
  `f128` `long double` libcalls (`sqrtl`, `fmal`, …) are compiler_rt's: the checker rejects the
  `f128` ops that call them unless `--assume-no-libc` (recorded in the header, premise MTH-05)
  states that the program links no libc.
- Derived from: tokens `softF80Chk`, `…Xf3`, `fmaFused`, `fmaRtFused`, `sqrtF80ViaF64`.
- Sources: [floats.md](floats.md#targets).

<a id="mth-05"></a>
### MTH-05 — Program linked without libc

- Kind: environment.
- Statement: The program is linked without libc, so on a target whose `c_longdouble` is `f128`
  (aarch64-linux, s390x, wasm32) the `long double` libm routines that `f128` `@sqrt`, `@mulAdd`,
  `@floor`/`@ceil`/`@trunc`/`@round`, `@min`/`@max` and the division family other than `/` call
  (`sqrtl`, `fmal`, `floorl`, …) are compiler_rt's, which the model ports. The AIR profile
  records no `link_libc` fact; the user states this with `--assume-no-libc`.
- Derived from: a reached generated module whose header records the admission `no-libc`
  (`assurance/premises.json` `admissions`).
- Sources: [floats.md](floats.md#targets), [air-json.md](air-json.md).

## Inline assembly

<a id="asm-01"></a>
### ASM-01 — Register-only assembly is an opaque function

- Kind: trusted.
- Statement: Each distinct register-only inline asm `(source, constraints, widths)` becomes
  an opaque `airAsm_<hash>`. The model knows nothing about the instruction. The assurance audit
  accepts the opaque as a generated declaration standing for this premise (`assurance/policy.json`
  `generated_declarations`).
- Derived from: tokens `airAsm_<n>`.
- Sources: [generated-code.md](generated-code.md#inline-asm), [assumptions-audit.md](assumptions-audit.md).

<a id="asm-02"></a>
### ASM-02 — Instruction behavior as an explicit hypothesis

- Kind: trusted.
- Statement: The theorem states the instruction fact it needs (for example `bswap` is an
  involution) as a hypothesis about the opaque. The result transfers to hardware only if
  that hypothesis holds for the target CPU.
- Derived from: `statement` rule on `airAsm_<n>` or `airAsmFx_<n>` in the theorem's own type.
- Sources: `Proofs/Asm/Proofs.lean`, `tests/roadmap/asm-effects/AsmEffects/Proofs.lean`.

<a id="asm-03"></a>
### ASM-03 — Assembly effects follow the declared contract

- Kind: trusted.
- Statement: An asm op with a read-write (`+r`, `+m`) or memory (`=m`) output, or a
  registry-approved `"memory"` clobber, is an opaque `airAsmFx_<hash>` whose generated wrapper
  holds every memory effect. The instructions read only their register inputs and the old values
  of their read-write outputs, write each declared output location whole and nothing else
  (no store through an address held in an integer input), and register/flag clobbers are not
  model state. Overlapping written locations are `.unspecified`. A `"memory"` clobber is
  accepted only for a reviewed `asmPureRegistry` entry, whose block has no model-visible effect.
- Derived from: tokens `airAsmFx_<n>`; runtime module `ZigLean.Asm`.
- Sources: [generated-code.md](generated-code.md#effect-contract-read-write-and-memory-operands-aliases-clobbers-a01), `Air2Lean/AsmContract.lean`, `Proofs/Asm/Effects.lean`.

<a id="asm-04"></a>
### ASM-04 — Allowlisted assembly faults exactly on its entry's condition

- Kind: trusted.
- Statement: Each entry of the reviewed allowlist (`Air2Lean/AsmAllowlist.lean`) states when
  its instruction faults (`AsmFault`): `divl` after `xorl %edx, %edx` exactly when the divisor
  is zero (#DE); `bswap`, `lzcnt` and `popcnt` never. The generated code guards the opaque with
  `Zig.asmTrap`, which throws `Zig.Error.trap` exactly on that condition. A no-panic or
  guaranteed-return claim over an asm opaque holds on hardware only if the condition is the
  instruction's whole fault set on the target CPU. That the CPU has the instruction (`popcnt`
  without POPCNT is #UD; `lzcnt` without LZCNT runs as `bsr`) is no longer part of ASM-04: each
  entry declares its `features`, the translator rejects a block whose features the profile lacks
  (`checkAsmCpuFeatures`), and ASM-09 admits them. `scripts/claims.py` lists ASM-04
  in the `premises` of every such goal.
- Derived from: implied by ASM-01.
- Sources: [volatile-effects.md](volatile-effects.md), `Air2Lean/AsmAllowlist.lean`,
  [outcome-taxonomy.md](outcome-taxonomy.md).

<a id="asm-05"></a>
### ASM-05 — Environment-read assembly returns fresh oracle values

- Kind: environment.
- Statement: An allowlisted asm entry with `envRead` semantics (`rdtsc` combined into `rax`,
  `rdrand` with or without its `setc` flag) reads state outside the model: each output is a
  fresh query of the explicit oracle `Mem.arbitrary` (`Zig.Asm.envWord`), cut to the output's
  width, in output order. The instruction touches no memory and writes only its outputs and
  clobbers. No relation between reads is claimed (no monotonic counter, no randomness), and a
  failed `rdrand` returns one of the oracle's values. The entry's fault condition and the CPU's
  support for the instruction are ASM-04 (`rdtsc` under CR4.TSD) and ASM-09 (`rdrand` without RDRAND).
- Derived from: tokens `Asm.envWord`; implies ASM-04.
- Sources: [volatile-effects.md](volatile-effects.md#inline-asm), `Air2Lean/AsmAllowlist.lean`,
  `tests/roadmap/asm-effects/AsmEnv/Proofs.lean`.

<a id="asm-06"></a>
### ASM-06 — Memory-region asm accesses only its declared regions

- Kind: trusted.
- Statement: An allowlisted asm entry with `regions` (`rep stosb`, `rep movsb`, with a
  `"memory"` clobber) reads memory only in its declared read regions and writes exactly its
  declared write regions, each a pointer operand and a byte length from an integer operand. The
  written bytes and the outputs are functions of the integer inputs, the old integer values and
  the read bytes (not of addresses); each pointer output is its old value moved by a signed
  offset, so it keeps its provenance. The direction flag is clear (the ABI's state at every
  call). The wrapper performs the accesses with the model's checked loads and stores
  (`Zig.Asm.readRegion`, `writeRegion`, `movePtr`); overlapping accessed regions (and written
  locations) are `.unspecified` (ASM-03's guard), since an overlapping copy depends on the
  regions' distance.
- Derived from: tokens `Asm.readRegion`, `Asm.writeRegion`, `Asm.movePtr`; implies ASM-03.
- Sources: [generated-code.md](generated-code.md#memory-regions-and-environment-reads-a01),
  `Air2Lean/AsmAllowlist.lean`, `Proofs/Asm/Effects.lean`.

<a id="asm-09"></a>
### ASM-09 — The running CPU has the asm features that the profile lacks

- Kind: environment.
- Statement: An allowlisted asm entry names the CPU features it needs (`features`: `lzcnt`,
  `popcnt`, `rdrnd`). The translator derives support from the profile's `features` and rejects
  an asm block with a missing one (`checkAsmCpuFeatures`; `lzcnt` without LZCNT executes as
  `bsr`, so `lzcnt(1)` would be 0, not 63). `--assume-asm-cpu-features` skips the check and states
  that the CPU that runs the program has the features, although the profile's CPU does not list
  them. The header records the admission `asm-cpu-features`.
- Derived from: a reached generated module whose header records the admission `asm-cpu-features`
  (`assurance/premises.json` `admissions`).
- Sources: [volatile-effects.md](volatile-effects.md), `Air2Lean/AsmAllowlist.lean`,
  [research/A02.md](research/A02.md).

## Core runtime semantics

<a id="sem-01"></a>
### SEM-01 — Zig value and safety semantics

- Kind: meaning.
- Statement: `Zig.Result` is `Option (Except Zig.Error α)`. Safety-checked illegal behavior
  is a `Zig.Error` (`.illegal`, `.unspecified`, panics) rather than undefined behavior.
  Zig error unions are ordinary values. Integer, bit, vector, packed and union operations
  follow `ZigLean/Basic.lean` and its companions.
- Derived from: `ZigLean.Basic`, `ZigLean.Bit`, `ZigLean.Permutation`, `ZigLean.Packed`, `ZigLean.PackedRepr`, `ZigLean.Union`, `ZigLean.Vec`, `ZigLean.Lemmas`; implied by TRU-02, SEM-02 and SEM-03.
- Sources: [generated-code.md](generated-code.md), [docs/generated-code.md §Panics](generated-code.md#panics).

<a id="sem-02"></a>
### SEM-02 — Byte-level block memory model

- Kind: environment.
- Statement: Memory is a CompCert-style list of blocks of bytes with kinds (stack, heap,
  global, `const` global, OS mapping). Layout comes from `Zig.Enc` instances checked against the
  profile. A `const` global is read-only static storage: a write to it (`Mem.accessW`) and a
  `free` of it (`Zig.free`) are `.illegal`, so its bytes never change while it is live.
  Out-of-bounds, misaligned or dead accesses are `.illegal`, and so is forming a derived pointer
  outside `[0, size]` of its block (`ptrProject`, `getelementptr inbounds`), an access below an
  OS mapping's first live offset (`BlockKind.mapped lo`), and two overlapping accesses of one
  call, one a write, through pointers with different `noalias` roots (`Zig.naMark`, LLVM's
  `noalias`). The blocks and, with `--device-contract`, the declared register window (DEV-01)
  are the only allocated objects: no object lies at address zero or at another address no block
  covers (a `@ptrFromInt` address, memory-mapped I/O outside the declared window), so a nonzero
  offset or a `@fieldParentPtr` from such an address is `.illegal`. Undefined bytes are explicit.
  `@returnAddress()` and an `undefined` pointer
  operand (`--allocator-model translated`) read the explicit oracle `Mem.arbitrary`, so a
  theorem over every initial memory covers every value sequence.
- Derived from: `ZigLean.Mem.Basic`, `ZigLean.Env.Host`, `ZigLean.Mem.Enc`, `ZigLean.Mem.Lemmas`, `ZigLean.Mem.Null`, `ZigLean.Mem.NullLemmas`, `ZigLean.Mem.Noalias`, `ZigLean.Sep.*`; implied by THR-01.
- Sources: [generated-code.md](generated-code.md#memory), [null-pointers.md](null-pointers.md).

<a id="sem-03"></a>
### SEM-03 — Loops and triples are partial correctness

- Kind: meaning.
- Statement: `Zig.loop` is a `partial_fixpoint`. Divergence is `none`. `Triple` and loop
  rules constrain only completed results, so a diverging program satisfies them. Finite
  loops do not reduce in the kernel, so loop clients use runtime assertions,
  invariant-based proofs, or a concrete scheduler run with each loop cut after `k`
  iterations (`unroll_sched`), whose result is the loop's result.
- Derived from: `ZigLean.Loop`, `ZigLean.Sep.*`, `ZigLean.VC.*`, `ZigLean.Conc.Unroll`; tokens `loop*`.
- Sources: [generated-code.md](generated-code.md#loops), [proofs.md](proofs.md).

<a id="sem-04"></a>
### SEM-04 — Total-correctness statements

- Kind: meaning.
- Statement: `TotalTriple` and `Conc.Total` theorems require an actual successful result
  for every satisfying state (or every oracle and sufficiently large fuel). They are stronger
  than SEM-03 and only cover their stated finite clients. `TotalTripleWithin B` additionally
  bounds the loop-body runs by `B` (`LoopRuns` counts); `ReturnsWithin B` bounds the scheduler
  budget uniformly in the oracle. `EventuallyReturnsUnder Fair` covers only the oracles that
  satisfy its stated premise and is not an unconditional total result. `Proto.returnsWithin`
  (a protocol that counts turns, `Proto.cost`) bounds every schedule's turns by `main`'s
  starting credits, uniformly in the oracle and without a fairness premise; its result is
  `main`'s value or a stack overflow (STK-01).
- Derived from: `ZigLean.Sep.Total`, `ZigLean.Sep.Bounded`, `ZigLean.Sep.Step`, `ZigLean.Conc.Total`, `ZigLean.Conc.Returns`; the `sep_*` step tactics (they elaborate to `ZigLean.Sep.Step` lemmas).
- Sources: `ZigLean/Sep/Total.lean`, [progress-hints.md](progress-hints.md).

<a id="sem-05"></a>
### SEM-05 — Model step and allocation counts are not time or memory measurements

- Kind: meaning.
- Statement: `Mem.allocs`, `Mem.liveHeap` and `LoopRuns` counts are counts in the model.
  They count allocation requests, live `.heap` blocks and loop-body runs of successful runs.
  A count does not measure CPU time, instruction count, cache behavior or native allocator
  memory use. Relating one to those needs a separate calibration argument.
- Derived from: `ZigLean.Sep.Cost`, `ZigLean.Sep.Bounded`.
- Sources: [proof-tools.md](proof-tools.md#model-cost-allocation-counts-and-counted-loops-p06), `ZigLean/Sep/Cost.lean`.

<a id="sem-06"></a>
### SEM-06 — Canonical AIR fragment semantics

- Kind: meaning.
- Statement: `Air2Lean.Sem` (`Air2Lean/Sem.lean`) is the meaning of a canonical AIR function in
  its fragment (integer arithmetic and safety checks, blocks, branches, switches, loops, stack
  locals, loads, stores, field pointers and comparisons through plain pointers, pointer
  arithmetic, slices of a function that uses memory, optionals and error unions as values,
  `try`, direct calls): an interpreter over the
  decoded `Air2Lean.Func`, with a typed SSA environment, over ZigLean's primitive operations and
  `Zig.MemM`, with `run` the least fixpoint over direct calls. Out-of-fragment and ill-typed
  steps are `⊥`. An `alloc` whose address is never taken (every use is the pointer of a `load`
  or `store`, or debug information; `Sem.regAlloc`, decided on the AIR alone) is a cell of the
  frame, not a memory block (a register local, as Clight's temporaries). This is faithful
  because such a local's address is unobservable, and theorems hold for every placement `σ`
  (SEM-07): every native address assignment of the remaining blocks is the one of some `σ`. An AIR certificate (`Proofs/<Ex>/AirCert.lean`)
  relates the generated definition to this meaning, so `Check.lean` and `Emit.lean` are not
  trusted for a certified function; it does not relate the meaning to Zig, the exporter or
  canonicalization (TRU-02). The plan to shrink this premise (raw-AIR certificates, executable
  conformance tests of `Sem`) is in air-semantics.md §How SEM-06 shrinks. `Sem.Ctx.view` is a
  certificate device that `execFunc` leaves empty; the relation of a viewed run to `execFunc` is
  proved (`SemView.execFunc_view`), under the theorem's hypothesis `Mem.ClockWf` on the start
  memory.
- Derived from: `Air2Lean.Sem`.
- Sources: [air-semantics.md](air-semantics.md).

<a id="sem-07"></a>
### SEM-07 — Block addresses are the environment's placement

- Kind: environment.
- Statement: The address of every block (global, stack, heap, allocator) is chosen by the
  placement oracle `Mem.place`, an arbitrary function of the block id. The model takes a
  proposal only if it satisfies what Zig guarantees (`Mem.placeOk`): nonzero, a multiple of the
  block's declared alignment, ending inside the user address space (`Placement.addrLimit`), and
  disjoint from every live block of nonzero size; adjacency, any order and reuse of a dead
  block's address are allowed. Otherwise the block goes after every block (`Mem.top`). The
  address space ends at `Placement.addrLimit`, at most `2^63` for every placement (every modelled
  64-bit target has its user space in the lower half; `2^47` by default): no block of any kind
  is placed above it (O-H). An allocation that has no room below it fails as for an exhausted
  address space: `rawAlloc` returns null (out of memory), `mmap`/`mremap` fail with `ENOMEM`
  (OSM-01), and `alloc` (a stack block, a thread-local instance or a runtime cell) throws
  `.stackOverflow` (STK-01: partial-correctness statements read it as non-termination; a
  total-correctness statement shows room, `Mem.allocOk`, e.g. with `TotalTripleIn`). A proposal
  inside a thread's stack reserve is not taken, and the fallback lies past every reserve (MM-18,
  STK-02). The
  full-state invariant `Mem.FSeq` holds only memories whose live blocks end below `2^63`
  (`Mem.LiveBounded`). A global at program start that the placement does not place and that has
  no room after `Mem.top` goes to the first fit (`Mem.globalPlace`, `Mem.firstFit`), so the
  memory at program start has that layout under every placement whenever the globals fit
  (`Mem.ofGlobals_liveBounded`, `Mem.GlobalsFit`); the translator rejects programs with more than
  `2^20` globals or `2^40` bytes of them (`GLOBALS_TOO_LARGE`). A generated program-start memory is `mem0 σ`
  and its theorems hold for every `σ`; the fixed layout `Placement.fresh` is used only to run
  programs. Pointer `==` compares addresses for every pointer kind. The declared alignment is
  the `alloc`'s pointer alignment for a stack block, and for a global its type's ABI alignment
  capped by the largest alignment of a pointer constant into it at an offset that alignment
  divides (the export does not record a global's own `align(N)`). Zero-size objects are not separated from other blocks. In-place
  growth needs only that the grown range is clear of other live blocks (`Mem.growFree`).
- Derived from: `ZigLean.Mem.Basic`; implied by SEM-02.
- Sources: [address-placement.md](address-placement.md),
  `tests/roadmap/architecture-audit/memory-model`.

<a id="stk-01"></a>
### STK-01 — The native stack holds every call chain

- Kind: environment.
- Statement: A statement about a function that recursion reaches (a `partial_fixpoint`
  definition, or a call of `Zig.enterFrame`) assumes that the native stack does not overflow
  on the runs it covers. The generated `mem0` gives no thread a stack budget (`Mem.stacks`
  empty); then the statement assumes this for every call chain. With a budget `S` of thread `t`
  (`Mem.withStack`, MM-18) it assumes only that the native stack of `t` holds every call chain
  whose model charge stays within `S`: a stack block charges `size + align`
  (`Zig.stackCharge`), the frame of a recursive function that uses memory `Zig.frameBase`, and
  the charges are popped LIFO; the model throws `.stackOverflow` at the charge that passes `S`.
  The charge is not a bound on the native frame (spills, saved registers, inlining), and pure
  recursive functions (`Zig.Result`) charge nothing. Native ReleaseSafe code that overflows its
  stack dies on a signal, which no model outcome without a budget reflects (MM-5, MM-18,
  [architecture-audit/memory-model.md](architecture-audit/memory-model.md)). The same outcome
  covers address-space exhaustion of a block without an allocator of a thread without a budget:
  an `alloc` (stack local, thread-local instance, runtime cell) without room below
  `Placement.addrLimit` throws `.stackOverflow` (O-H, SEM-07). Every partial-correctness
  statement (`Triple`, `TTriple`, `FTriple`, `CTriple`, and the strict concurrent `run_safe`,
  which excludes every other error) reads `.stackOverflow` as it reads a run that does not
  terminate; a total-correctness statement excludes it, so one that allocates shows room
  (legacy `TotalTripleIn`; in the full-state logic, until the stack-depth resource of
  `docs/sep-full-state.md` §Stack depth lands, the start-memory run premise of
  `FTriple.run_init_ok`). Regressions: `tests/roadmap/memory-hardening/NoRoom.lean`,
  `tests/roadmap/memory-hardening/Stack.lean`, `tests/roadmap/stack-region`,
  `tests/roadmap/outcome-accounting`.
- Derived from: tokens `partial_fixpoint`, `enterFrame`, `alloc`, `allocStack`, `stackOverflow`.
- Sources: `ZigLean/Mem/Basic.lean`, [generated-code.md](generated-code.md#memory),
  `tests/roadmap/memory-hardening/README.md`.

<a id="stk-02"></a>
### STK-02 — Stack reserves lie in address space the native run never maps

- Kind: environment.
- Statement: A thread with a stack budget `S` owns a reserve `[base, base + S)` (MM-18,
  `Mem.withStack`, `Placement.reserve`) that every other block of the model avoids; its stack
  blocks that the placement does not place go there. The premise: every live thread's reserve
  can be placed in address space that the native run does not map while the thread lives, so
  the placement that proposes every native address and puts each reserve there reproduces the
  native layout. It needs `S ≤ 2^40` and budgets of the live threads that sum to well below the
  address space the native run leaves unmapped (e.g. 64 threads of 1 GiB in a `2^47` space).
- Derived from: token `withStack` (a memory without a budget has no reserve).
- Sources: `ZigLean/Mem/Basic.lean`, [architecture-audit/memory-model.md](architecture-audit/memory-model.md)
  §MM-18, `tests/roadmap/stack-region`.

## External models

<a id="ext-01"></a>
### EXT-01 — User external model contracts

- Kind: environment.
- Statement: A registered external call runs a project-supplied `Zig.MemM` model with a typed
  `Zig.External.Contract` (termination, errors, effects, optional parameter footprint via
  `Contract.Respects`). A `proved` entry is a theorem obligation, and it is reported as verified
  only when `scripts/external-contracts.py --check` shows standard axioms alone.
  Correspondence to the real foreign function is not claimed.
- Derived from: `ZigLean.External`.
- Sources: [external-models.md](external-models.md).

<a id="ext-02"></a>
### EXT-02 — Assumed contracts and project axioms

- Kind: trusted.
- Statement: A `trust: "assumed"` binding emits a named axiom for its obligation and is listed
  under `assumptions` by `scripts/external-contracts.py`. The assurance audit accepts that
  generated evidence axiom only as this premise (`assurance/policy.json`
  `generated_declarations`: declared by a generated module whose model record has the assumed
  binding). Any other project `axiom` reached is a trusted premise and also fails the assurance
  gate unless it is allowlisted. The shipped policy allowlists none.
- Derived from: a reached source `axiom` declaration; a non-standard axiom in the compiled report.
- Sources: [external-models.md](external-models.md), [assumptions-audit.md](assumptions-audit.md).

<a id="ext-03"></a>
### EXT-03 — Extern functions at their linker identity

- Kind: environment.
- Statement: A call to an extern function (`extern fn`, a libc or OS primitive) is bound by its
  linker symbol and declared library only. Bound to a registry model, the model's contract is
  assumed to describe the real symbol that the target's linker resolves (an OS or libc
  primitive, for example `mmap` or `abs`); each such binding names this or a more specific
  premise. Bound to an `export fn` of the translated program, the program is assumed to be
  linked as one image in which that definition is the symbol's strong definition. Variadic
  and `noreturn` externs, `@export` aliases and weak definitions are outside the subset.
- Derived from: a `--model-registry` entry with an `extern` object; an `externs` entry bound by
  `Air2Lean/Check.lean` `resolveExterns`.
- Sources: [air-json.md](air-json.md#extern-calls), [external-models.md](external-models.md#extern-functions).

<a id="ext-04"></a>
### EXT-04 — Registry models in concurrent programs

- Kind: trusted.
- Statement: In a program with sync operations, a registry model call (direct, or through a
  function pointer such as an asynchronous callback run by a spawned thread) is one scheduler
  step. Its memory accesses lie in the blocks of its declared footprint parameters, which the
  generated call claims first (`Zig.External.claim`: one recorded whole-block access, read or
  write), so an unsynchronized conflicting access of another thread is a race (`.illegal`). A
  `const` global is never written: a write claim of one is `.illegal`, and a read claim records
  nothing (it races with nothing, MM-20). A binding without a footprint is rejected in a
  concurrent program.
- Derived from: tokens `External.claim`; implies EXT-01 and THR-01.
- Sources: [external-models.md](external-models.md#callback-contracts-e02),
  `tests/roadmap/callbacks/Callbacks/AsyncProofs.lean`.

<a id="ext-05"></a>
### EXT-05 — Environment implementations of open interfaces

- Kind: environment.
- Statement: For an interface that the model registry declares open (`interfaces`), a call
  through a pointer of one of its function types that is no function of the program runs the
  environment's implementation at that pointer (`Ext.call<i>`, the same one for the whole run),
  and that implementation meets the interface contract that the theorem assumes for it (for
  `std.mem.Allocator`, `CAllocSpec` of the vtable's entries). An implementation in the program
  is never covered by this premise: the dispatch runs its translated code. The pointers a
  theorem names in its contract hypothesis are the environment's functions, not addresses
  inside the program's blocks.
- Derived from: tokens `extCall` (the open arm of a generated call, `Zig.extCall`).
- Sources: [interfaces.md](interfaces.md), `Air2Lean/Emit.lean` (`emitExt`),
  `tests/roadmap/interfaces`.

<a id="ext-06"></a>
### EXT-06 — External static storage is not written during the run

- Kind: environment.
- Statement: The storage of an `extern` global that the program does not define (a field of the
  generated `ExternInit`), and every external storage block that such a global's initial value
  points into (`Zig.ExternBlock`), is written by no code outside the program while the program
  runs: no other object's code, C thread, signal handler or device changes it. Its contents are
  the initial value `ext` until the program itself writes a writable one. A read-only one (a
  `const` extern, an `ExternBlock` that is not `writable`) is a `const` global of the model, whose
  reads record no access (MM-20), so a concurrent external write to it would be a race that the
  model does not see; this premise excludes it.
- Derived from: tokens `ExternInit` (the generated structure of external initial values) and
  `ExternBlock`.
- Sources: [generated-code.md](generated-code.md) (§Globals),
  [architecture-audit/memory-model.md](architecture-audit/memory-model.md) (MM-20),
  [architecture-audit/structure-2026-10-13.md](architecture-audit/structure-2026-10-13.md) (#7),
  `tests/roadmap/global-init`.

## OS page mapping

<a id="osm-01"></a>
### OSM-01 — Trusted `posix.mmap`/`munmap`/`mremap` model

- Kind: trusted.
- Statement: Under `--allocator-model translated`, a call of `std.posix.mmap`, `munmap` or
  `mremap` (Zig 0.16.0, x86_64-linux or aarch64-macos) is a call of `Zig.Os.mmap`, `munmap` or
  `mremap`. Everything above that boundary, `std.heap.PageAllocator` and the `mem.Allocator`
  wrappers included, is translated from its AIR; the syscall and libc layer below it is not.
  The kernel's anonymous page mappings behave as `ZigLean/Os/Mmap.lean` says
  ([os-mmap.md](os-mmap.md)). `mmap` with any hint, `PROT.READ|WRITE`,
  `MAP.PRIVATE|ANONYMOUS`, `fd = -1`, offset 0 and `length > 0` either returns
  `error.OutOfMemory` (the failure decision is the allocator's `Mem.allocDenied`, one attempt
  index for every request) with no other change, or a new block of kind `.mapped 0` of
  exactly `length` zero bytes at the placement's page-aligned address for its pages (SEM-07). A
  mapping that would end above the target's user address space (`Os.Target.addrLimit`: `2^47`
  on x86_64-linux, at least `TASK_SIZE_MAX`; `MACH_VM_MAX_ADDRESS = 0x7FFFFE000000` on
  aarch64-macos) fails with `error.OutOfMemory`, as the kernel's does; assumed: no call passes a
  hint above `TASK_SIZE_MAX = 2^47 - 4096` (5-level-paging Linux maps above `2^47` for one,
  a hint of `2^47` included). The
  kernel fails such a mapping only with `ENOMEM` (no other `MMapError` member). Other argument
  combinations are outside the model (`.unspecified`); `length = 0` is `.illegal`. `munmap` of
  the whole live range of one mapping ends it, of a page-aligned prefix moves its first live
  offset, of a page tail shrinks it; any other range (middle, past the mapping, not a live
  mapping: a double `munmap`) is `.illegal`, stricter than the kernel. `mremap` (Linux only)
  of a whole live mapping with flags 0 or `MAYMOVE`, no new address and `new_len > 0` shrinks
  in place, or grows (an allocation attempt) in place when the grown pages end at or below
  `addrLimit` and are clear of every other live block, by a move to a new mapping at the placement's address
  under `MAYMOVE` (oracle `mremapMoves`, or no room) whose pages end at or below `addrLimit`,
  or fails with `error.OutOfMemory`;
  grown bytes up to the old page end are undefined, the rest zero, and a growth in place
  forgets the recorded accesses to the grown offsets (`Mem.forgetFrom`: they are new pages, so
  an access from before an earlier unmap of them races with nothing); `munmap` and a shrink
  retire the atomic locations over the removed bytes (`Mem.retire`: new pages carry no atomic
  message from before). Page size: 4 KiB
  (`linux`), 16 KiB (`macos`), fixed per target (`Os.Target.pageSize`). An address can be
  reused after `munmap` (the placement oracle).
- Derived from: `ZigLean.Os.Mmap`, `ZigLean.Os.MmapRun`, `ZigLean.Sep.Mmap`; tokens `Zig.Os`;
  implies SEM-02.
- Sources: [os-mmap.md](os-mmap.md), [allocator-model.md](allocator-model.md),
  `ZigLean/Os/Mmap.lean`, `tests/roadmap/os-mmap/Check.lean`, Zig 0.16.0 `lib/std/posix.zig`,
  `lib/std/heap/PageAllocator.zig`.

## OS thread primitives

These rows are the trusted base of the translated `std.Thread`/`std.Io` plan
(`docs/thread-io-translation.md` on `codex/spike-thread-io`): only the named `os.linux.*` wrapper
or the `extern "c"` symbol is modelled; everything above it is to be translated. Each model is a
`ZigLean/Os/` definition over the scheduler and memory of THR-01 and ORD-01. It takes the
explicit environment `Os.Env` (CPU mask, spawn policy, thread and process ids, clock oracle,
malloc slack), and a theorem states `Env.Valid` and whatever else it assumes of it (user
decision D2). Zig 0.16.0, x86_64-linux and aarch64-macos. Details: [os-threads.md](os-threads.md).

<a id="osf-01"></a>
### OSF-01 — Futex wait (`futex_4arg` WAIT, `__ulock_wait2`, `__ulock_wait`)

- Kind: trusted.
- Statement: The kernel compares the `u32` at the address with the expected value as one atomic
  read of the newest message of that word: an atomic-read footprint and a read-view update. A
  bad pointer is `.illegal` (stricter than `EFAULT`). A different value returns at once
  (`EAGAIN`, `0` on macOS). An equal value either returns at once with `EINTR`, or with
  `ETIMEDOUT` if a timeout was given, or sleeps. An untimed sleeper waits in the queue until a
  wake or an interrupt; the scheduler reads the word again first and a changed word is a return
  with `0`. A timed sleeper stays runnable and returns `0` if a wake reached it, else
  `ETIMEDOUT`. The waiter gets no happens-before edge from the waker. The non-negative result of
  `__ulock_wait*` is always `0`. Other commands, flags and `val2` are outside the model
  (`.unspecified`); an invalid timeout is `EINVAL`.
- Derived from: `ZigLean.Os.Futex`, `ZigLean.Conc.OsRules`; tokens `Os.futexWait`,
  `Os.Linux.futex_4arg`, `Os.Darwin.__ulock_wait2`, `Os.Darwin.__ulock_wait`; implies THR-01,
  ORD-01.
- Sources: [os-threads.md](os-threads.md#futex), `ZigLean/Os/Futex.lean`,
  `tests/roadmap/os-threads/Check.lean`, Zig 0.16.0 `lib/std/Io/Threaded.zig`
  (`futexWaitInner`), `lib/std/Thread.zig` (`LinuxThreadImpl.join`).

<a id="osf-02"></a>
### OSF-02 — Futex wake (`futex_3arg` WAKE, `__ulock_wake`)

- Kind: trusted.
- Statement: A wake of up to `n` waiters at an address wakes an oracle-chosen subset of
  `min n k` of the `k` threads queued there, in one step, and accesses no memory. On Linux `n`
  is `val`, at least 1 for `val ≤ 0`; on macOS it is 1, or all with `WAKE_ALL`. Linux returns
  the number woken. macOS returns `0`, `-ENOENT` if nobody was woken, or, as an oracle option,
  `-EINTR` with nobody woken. It gives no happens-before edge.
- Derived from: `ZigLean.Os.Futex`, `ZigLean.Conc.OsRules`; tokens `Os.futexWake`,
  `Os.Linux.futex_3arg`, `Os.Darwin.__ulock_wake`; implies THR-01.
- Sources: [os-threads.md](os-threads.md#futex), `ZigLean/Os/Futex.lean`.

<a id="ost-01"></a>
### OST-01 — Thread creation (`clone`, `pthread_create`)

- Kind: trusted.
- Statement: Linux `clone` with exactly std's flag set (`THREAD|DETACHED|VM|FS|FILES|
  PARENT_SETTID|CHILD_CLEARTID|SIGHAND|SYSVSEM|SETTLS`) and macOS `pthread_create` start a new
  thread that runs the call site's entry function with its argument (the translator's spawn
  target), with a happens-before edge from the parent: the scheduler's `spawn`. Under the
  run's `Zig.Env.spawn = fallible` (and `Mem.spawnLimit`) the scheduler may fail it instead with
  a declared error, which the row returns as `-ENOMEM` (`OutOfMemory`) or `-EAGAIN` on Linux,
  `EAGAIN` on macOS. The child gets fresh thread-local instances (batch7 C02); the stack and TLS
  arguments are not used. Linux writes the child's id (`Env.tid`) to `ptid` after the fork, and
  `pthread_create` writes the handle. The `pthread_attr_*` calls touch only the attribute bytes,
  which are undefined to Zig code.
- Derived from: `ZigLean.Os.Thread`, `ZigLean.Os.Env`; tokens `Os.Linux.clone`,
  `Os.Darwin.pthread_create`, `Os.Darwin.pthread_attr_*`; implies THR-01, THR-03.
- Sources: [os-threads.md](os-threads.md#threads), `ZigLean/Os/Thread.lean`, Zig 0.16.0
  `lib/std/Thread.zig` (`LinuxThreadImpl.spawn`, `PosixThreadImpl.spawn`).

<a id="ost-02"></a>
### OST-02 — Thread exit, join and detach

- Kind: trusted.
- Statement: When a `clone` thread's entry function returns, the kernel's `CHILD_CLEARTID` is
  one step: a release store of `0` to the `i32` at `ctid`, a wake of every waiter there, and the
  end of the thread's join obligation. Then the thread ends. Std's translated Linux join gets
  its edge from that store. macOS `pthread_join(h, null)` waits for the end of `h` and gets the
  edge from it; `pthread_detach` releases the obligation. A join or detach by a thread that does
  not own the handle, of a consumed handle, or a second one, is `.illegal`. A detached Linux
  thread's `freeAndExit` is outside the model.
- Derived from: `ZigLean.Os.Thread`, `ZigLean.Conc.OsRules`; tokens `Os.Linux.cloneThread`,
  `Os.Linux.cloneExit`, `Os.Darwin.pthread_join`, `Os.Darwin.pthread_detach`; implies THR-01.
- Sources: [os-threads.md](os-threads.md#threads), `ZigLean/Os/Thread.lean`.

<a id="ost-03"></a>
### OST-03 — Thread ids, process id and CPU count

- Kind: environment.
- Statement: `gettid`, `pthread_threadid_np` and `getpid` return `Env.tid t` and `Env.pid`.
  `Env.Valid` makes thread ids distinct and positive. Ids are never reused within a run, so a
  program that compares the id of an exited thread with a live one is outside the premise.
  `sched_getaffinity(0, size ≥ 128, set)` writes `Env.cpuMask`, and
  `sysctlbyname("hw.logicalcpu")` writes `Env.cpus`, which `Env.Valid` makes at least 1. Other
  arguments are outside the model.
- Derived from: `ZigLean.Os.Env`, `ZigLean.Os.Thread`; tokens `Os.Env.cpus`, `Os.Linux.gettid`,
  `Os.Linux.getpid`, `Os.Linux.sched_getaffinity`, `Os.Darwin.pthread_self`,
  `Os.Darwin.pthread_threadid_np`, `Os.Darwin.sysctlbyname`.
- Sources: [os-threads.md](os-threads.md#environment), `ZigLean/Os/Env.lean`.

<a id="osy-01"></a>
### OSY-01 — Yield

- Kind: trusted.
- Statement: `sched_yield` is a scheduling point and returns `0`.
- Derived from: `ZigLean.Os.Thread`; tokens `Os.Linux.sched_yield`, `Os.Darwin.sched_yield`;
  implies THR-01.
- Sources: [os-threads.md](os-threads.md#threads).

<a id="osk-01"></a>
### OSK-01 — Clock reads

- Kind: environment.
- Statement: `clock_gettime` of `REALTIME`, Linux `MONOTONIC`/`BOOTTIME`, or macOS
  `UPTIME_RAW`/`MONOTONIC_RAW`/`MONOTONIC` is a scheduling point. The `i`-th clock read of the
  run returns `Env.clock k i` as a `timespec`. `Env.Valid` makes the `awake` and `boot` clocks
  monotone along the run and makes every value fit a `timespec`. No relation to the scheduler's
  turns or to TMR-02's timed scheduler is claimed. Other clocks are outside the model.
- Derived from: `ZigLean.Os.Clock`, `ZigLean.Os.Env`; tokens `Os.Linux.clock_gettime`,
  `Os.Darwin.clock_gettime`, `Os.readClock`.
- Sources: [os-threads.md](os-threads.md#clocks), `ZigLean/Os/Clock.lean`.

<a id="osk-02"></a>
### OSK-02 — Sleep

- Kind: trusted.
- Statement: Linux `clock_nanosleep` and macOS `nanosleep` of a valid request are one oracle
  choice (a scheduling point). They return `0`, or `EINTR` after writing the whole request as
  the time left to a relative sleep's `remain` (macOS: `-1` with the thread's `errno` cell set).
  No duration is promised. An invalid request is `EINVAL`. `__error()` returns the calling
  thread's `errno` cell.
- Derived from: `ZigLean.Os.Clock`; tokens `Os.Linux.clock_nanosleep`, `Os.Darwin.nanosleep`,
  `Os.Darwin.__error`; implies THR-01.
- Sources: [os-threads.md](os-threads.md#clocks), `ZigLean/Os/Clock.lean`.

<a id="osg-01"></a>
### OSG-01 — Interrupting signal (`tgkill`, `pthread_kill` of `SIG.IO`)

- Kind: trusted.
- Statement: A `SIG.IO` to a live thread (std's cancelation of a blocked syscall, with a no-op
  handler installed) wakes the thread if it sleeps in a futex wait, which then returns `EINTR`.
  Otherwise it records a pending interrupt. The thread's next futex wait or sleep delivers it at
  its start without forcing `EINTR`. An unknown, exited (Linux) or joined (macOS) thread gives
  `ESRCH`; a detached macOS thread stays signalable, also after it ended. Installing the
  handler has no memory effect. Any other signal is outside the model.
- Derived from: `ZigLean.Os.Thread`, `ZigLean.Conc.OsRules`; tokens `Os.interrupt`,
  `Os.Linux.tgkill`, `Os.Darwin.pthread_kill`; implies THR-01.
- Sources: [os-threads.md](os-threads.md#interrupts), `ZigLean/Os/Thread.lean`, Zig 0.16.0
  `lib/std/Io/Threaded.zig` (`signalCanceledSyscall`).

<a id="osm-02"></a>
### OSM-02 — macOS `malloc`/`free`/`malloc_size`

- Kind: trusted.
- Statement: Libc's allocator is thread-safe. `malloc(n)` is one allocation attempt of the
  model heap. `Mem.allocDenied` decides failure (`null`); otherwise the result is a fresh `.heap`
  block of `n + Env.mallocSlack i n` undefined bytes at a 16-byte-aligned address. `free(null)`
  does nothing. `free(p)` of offset 0 of a live heap block ends the block and counts as a write
  of all its bytes. Any other pointer (double free, inner pointer, stack, global, mapping or
  arena block) is `.illegal`. `malloc_size` returns the block's byte count (`0` for `null`) and
  is `.illegal` for other pointers, which is stricter than macOS.
- Derived from: `ZigLean.Os.Malloc`, `ZigLean.Sep.Full.Malloc`; tokens `Os.Darwin.malloc`,
  `Os.Darwin.free`, `Os.Darwin.malloc_size`; implies SEM-02, ALC-02.
- Sources: [os-threads.md](os-threads.md#malloc), `ZigLean/Os/Malloc.lean`, Zig 0.16.0
  `lib/std/heap.zig` (`c_allocator`).

## Compiler and tool trust

<a id="tru-01"></a>
### TRU-01 — Lean kernel and standard axioms

- Kind: trusted.
- Statement: The pinned Lean toolchain kernel checks the proof. It may use only `propext`,
  `Classical.choice` and `Quot.sound`. `sorry`, project axioms, `native_decide` compiler axioms
  and unreviewed opaques/externs fail the assurance gate.
- Derived from: every theorem.
- Sources: [assumptions-audit.md](assumptions-audit.md), `scripts/no-sorry.sh`, `lean-toolchain`.

<a id="tru-02"></a>
### TRU-02 — Zig exporter and air2lean translation

- Kind: trusted.
- Statement: The generated Lean module is believed to model the analyzed AIR of the source,
  as exported by the patched Zig compiler and translated by `air2lean`. This is not proved.
  The evidence is golden comparisons, structural checks, mutation tests and bounded
  native/model differential tests.
- Derived from: a reached generated module.
- Sources: [generated-code.md](generated-code.md), [profiles.md](profiles.md#golden-comparisons-and-check-receipts), [air-json.md](air-json.md), [trust-report.md](trust-report.md).

<a id="tru-03"></a>
### TRU-03 — Backend lowering and native execution

- Kind: trusted.
- Statement: The proof concerns AIR before backend code generation. Native behavior
  (LLVM lowering, linking, OS, hardware) is related to it only by bounded differential and
  ABI-probe observations.
- Derived from: implied by TRU-02.
- Sources: [generated-code.md](generated-code.md#differential-test), [profiles.md](profiles.md#bounded-linux-native-abi-observations).

<a id="tru-04"></a>
### TRU-04 — Reviewed opaque, extern and runtime-redirection policy

- Kind: trusted.
- Statement: Opaques, extern primitives and `implemented_by` redirections reached by the
  theorem are listed with reasons in `assurance/policy.json`. Execution may use a different
  body than kernel reasoning.
- Derived from: implied by ASM-01 and MTH-02.
- Sources: [assumptions-audit.md](assumptions-audit.md), [`assurance/policy.json`](../assurance/policy.json).

<a id="tru-05"></a>
### TRU-05 — Artifact signing key

- Kind: trusted.
- Statement: An artifact manifest or proof receipt that `scripts/attest.py verify` accepts was
  signed by a holder of a private key whose public half the *verifier* listed in its
  `allowed_signers` file for the attested principal and the namespace
  `air2lean-attestation-v1`. The verifier obtains that file, or the key fingerprint it pins
  with `--pin-fingerprint`, out of band; the attestation never carries its own trust anchor.
  The signer is trusted to have recorded the manifest or receipt from the tree it describes,
  and to keep the private key secret. A signature authenticates the exact bytes, not their
  truth (TRU-02, TRU-03) and not their freshness: the manifest's own link checks decide
  whether it still describes the tree. A stolen key forges any artifact until its entry is
  removed from the verifier's allowed signers; there is no revocation list, timestamp or
  transparency log, only the optional `valid-after`/`valid-before` of `allowed_signers`
  (`--verify-time`). The signature primitive and its verification are OpenSSH's
  (`ssh-keygen -Y sign|verify`), trusted as installed.
- Derived from: use of an attestation (`--attestation`); not derived from any theorem.
- Sources: [artifact-manifest.md](artifact-manifest.md#authentication), `scripts/attest.py`.

## Reports

Each report below, and the premises a reader must accept to rely on it, is checked by the tool.

| Report | Premises |
|---|---|
| `scripts/assumptions.sh` JSON ([assumptions-audit.md](assumptions-audit.md)) | TRU-01, TRU-04, EXT-02 |
| `scripts/premises.py compiled` JSON (this page) | TRU-01, TRU-04 |
| Proof receipts ([proof-receipts.md](proof-receipts.md)) | TRU-01, TRU-04 |
| Authenticated manifests and receipts (`scripts/attest.py`, [artifact-manifest.md](artifact-manifest.md#authentication)) | TRU-05 |
| Check receipts `.lake/check-reports/` ([profiles.md](profiles.md#golden-comparisons-and-check-receipts)) | PRF-01, PRF-02, TRU-02 |
| Differential test results (`scripts/diff.sh`, [generated-code.md](generated-code.md#differential-test)) | TRU-02, TRU-03, THR-01, ORD-06, ALC-02, MTH-02 |
| ABI probe reports ([profiles.md](profiles.md#bounded-linux-native-abi-observations)) | PRF-02, TRU-03 |
| Allocation policy record ([allocation-policy-report.json](allocation-policy-report.json)) | ALC-01, ALC-02, TRU-02, TRU-03 |
| Weak CAS gate ([weak-cas.md](weak-cas.md)) | ORD-01, ORD-04, ORD-06, TRU-03 |
| Timed scheduler qualification (`tests/roadmap/deadline-futex/foundation-qualified-v4.json`) | TMR-02, THR-05, ORD-06 |
| Model registry evidence ([external-models.md](external-models.md)) | EXT-01, EXT-02, EXT-03, EXT-04, EXT-05, ORD-06 |
| Model inclusion evidence (`tests/roadmap/model-inclusion/evidence.json`, [std-models.md](std-models.md#caller-supplied-allocator-and-io)) | ALC-09, IOM-01, TRU-03 |
| Float probe (`scripts/floatprobe.sh`, [floats.md](floats.md)) | MTH-01, MTH-02, MTH-03, TRU-03 |
| Native/WASM correspondence records (`scripts/wasm-correspondence.py`, [research/T05.md](research/T05.md)) | PRF-04, TRU-03 |
