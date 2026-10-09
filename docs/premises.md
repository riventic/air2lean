# Premise and contract reference (D03)

This is the single indexed reference for the premises behind every shipped theorem in
`Proofs/` and every theorem-bearing roadmap, tutorial and case-study client. Each premise
has a stable ID. [premise-index.md](premise-index.md) lists, per theorem, the IDs it
uses. `scripts/premises.py` derives that index mechanically and checks it.

To read a proof: find the theorem in [premise-index.md](premise-index.md), then read each
listed premise below. The theorem holds in the model under those premises and its own
stated hypotheses. Nothing else in the runtime is assumed. A premise ID marked
*environment* is a model choice that the theorem quantifies over or fixes. A premise marked
*trusted* is believed, not proved. A premise marked *meaning* says what kind of statement a
proof makes (for example partial correctness).

```sh
python3 scripts/premises.py check            # fails on a stale index, undefined/orphan ID or unmapped module
python3 scripts/premises.py write            # regenerate docs/premise-index.md
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

Roadmap clients outside `Proofs/` have only the source derivation. Committed `Proofs/*/Gen.lean` files are the 0.16.0 translations;
`scripts/check.sh` replaces them per Zig version. The index describes the committed files.

## Index

| Category | IDs |
|---|---|
| Target and build profiles | [PRF-01](#prf-01) [PRF-02](#prf-02) [PRF-03](#prf-03) [PRF-04](#prf-04) [PRF-05](#prf-05) |
| Allocator policies | [ALC-01](#alc-01) [ALC-02](#alc-02) [ALC-03](#alc-03) [ALC-04](#alc-04) [ALC-05](#alc-05) [ALC-06](#alc-06) [ALC-07](#alc-07) [ALC-08](#alc-08) |
| Thread creation and scheduling | [THR-01](#thr-01) [THR-02](#thr-02) [THR-03](#thr-03) [THR-04](#thr-04) [THR-05](#thr-05) [THR-06](#thr-06) [THR-07](#thr-07) [THR-08](#thr-08) [THR-09](#thr-09) [THR-10](#thr-10) [THR-11](#thr-11) |
| Memory ordering | [ORD-01](#ord-01) [ORD-02](#ord-02) [ORD-03](#ord-03) [ORD-04](#ord-04) |
| Timers and clocks | [TMR-01](#tmr-01) [TMR-02](#tmr-02) |
| Environment operations | [ENV-01](#env-01) [ENV-02](#env-02) [ENV-03](#env-03) |
| Device effects | [DEV-01](#dev-01) |
| Opaque math and floats | [MTH-01](#mth-01) [MTH-02](#mth-02) [MTH-03](#mth-03) |
| Inline assembly | [ASM-01](#asm-01) [ASM-02](#asm-02) [ASM-03](#asm-03) |
| Core runtime semantics | [SEM-01](#sem-01) [SEM-02](#sem-02) [SEM-03](#sem-03) [SEM-04](#sem-04) [SEM-06](#sem-06) |
| External models | [EXT-01](#ext-01) [EXT-02](#ext-02) |
| OS page mapping | [OSM-01](#osm-01) |
| Compiler and tool trust | [TRU-01](#tru-01) [TRU-02](#tru-02) [TRU-03](#tru-03) [TRU-04](#tru-04) |

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
- Statement: `Mem.allocPolicy.reuseAddr` is an arbitrary opt-in oracle that may give a new heap
  or owned block the address of a freed block (`Mem.reuseOk`: nonzero, aligned, below
  `nextAddr`, clear of every live block with a 1-byte gap). Block ids stay unique and every
  liveness check uses them, so lifetime theorems over arbitrary `Mem` hold under every reuse
  policy. Stack blocks and globals keep fresh addresses. `@ptrFromInt` of an address that two
  blocks cover is `.unspecified` under the default `.strict` provenance mode; the
  address-sensitive contract `.liveBlock` recovers the live block. A theorem that observes
  addresses holds only under the policy and mode it states. No native allocator address
  behavior is claimed.
- Derived from: `ZigLean.Sep.AddrReuse`; tokens `withReuse`, `liveBlock` (the opt-in policy
  and provenance mode; the default path `Mem.reuseAddr?`/`ProvenanceMode.strict` that every
  `alloc`/`@ptrFromInt` unfolds to is not a token).
- Sources: [address-reuse.md](address-reuse.md), `tests/roadmap/address-reuse`.

## Thread creation and scheduling

<a id="thr-01"></a>
### THR-01 — Interleaving scheduler and partial-correctness meaning

- Kind: meaning.
- Statement: `Zig.Sched.run dispatch fuel o main m0` interleaves threads only at sync ops.
  The oracle `o` picks each turn. A data race between plain code is `.illegal`. A spec
  constrains every completed result for every oracle and fuel; out of fuel is `none`. No
  fairness or termination follows unless a theorem states it (see SEM-04, THR-07).
- Derived from: `ZigLean.Conc.Basic`, `ZigLean.Conc.Call`, `ZigLean.Conc.Sched`; implied by every THR premise.
- Sources: [std-models.md](std-models.md#thread-model), `ZigLean/Conc/Sched.lean`.

<a id="thr-02"></a>
### THR-02 — Thread spawn/join with the `available` policy

- Kind: environment.
- Statement: `Thread.spawn` is a sync op that always succeeds under the default `available`
  policy. It copies the argument tuple and gives the child a copy of the parent clock. `join`
  waits for the child and merges its clock. Only the handle's owner (the spawner, or the thread
  an explicit transfer named, THR-10) may join, once. An owned handle neither joined nor
  detached at thread end is `.illegal`. The child protocol obligation (`spawnInit`) is explicit.
- Derived from: `ZigLean.Conc.Sched`; tokens `spawnC`, `joinC`, `spawnInit`.
- Sources: [std-models.md](std-models.md#thread-model), [generated-code.md](generated-code.md#atomics-and-threads).

<a id="thr-03"></a>
### THR-03 — Fallible thread assignment policy

- Kind: environment.
- Statement: The opt-in `fallible` policy adds the declared spawn errors and the `Io.Group`
  caller-execution fallback. The per-caller budget `Mem.spawnLimit` (default none) removes
  assignment from the oracle range while the caller's live children reach it. WP rules must
  cover every oracle outcome.
- Derived from: `ZigLean.Conc.Spawn`, `ZigLean.Conc.SpawnLemmas`; tokens `SpawnPolicy`, `WithPolicyC`,
  `spawnLimit`, `spawnAdmits`, `assignmentCount`, `assignmentOutcome`, `assignmentChoiceC`.
- Sources: [spawn-failure.md](spawn-failure.md).

<a id="thr-04"></a>
### THR-04 — `Io.Group` tasks are model threads

- Kind: environment.
- Statement: `Group.async`/`concurrent` spawn a recorded task; `Group.await` joins the tasks
  in spawn order. `Group.cancel` gives each task a cancelation request (`Mem.cancels`) and
  joins it; a task's cancelation point (a cancelable futex wait, its own `Group.await`)
  delivers a pending request as `error.Canceled`. `main` is not an `Io` task and is never
  canceled.
- Derived from: tokens `groupAsyncC`, `groupAwaitC`, `groupConcurrentC`, `groupCancelC`, `cancelPending`, `requestCancel`.
- Sources: [std-models.md](std-models.md#thread-model).

<a id="thr-05"></a>
### THR-05 — Futex model

- Kind: environment.
- Statement: A futex wait on a matching `u32` sleeps until a wake at that address, or returns
  spuriously in place of the sleep (an oracle choice, `Sched.spuriousWake`). Waiters wake in
  FIFO order; a sleeping waiter leaves the queue only through a wake or a cancelation request.
  A wake adds no happens-before edge. No runnable thread with an unfinished thread is
  `Zig.Error.deadlock`.
- Derived from: `ZigLean.Conc.Lock`, `ZigLean.Conc.LockRules`, `ZigLean.Conc.Word`, `ZigLean.Conc.WeakWord`; tokens `futex`, `Futex`.
- Sources: [std-models.md](std-models.md#thread-model), `ZigLean/Conc/Call.lean`.

<a id="thr-06"></a>
### THR-06 — Darwin `os_unfair_lock` contract

- Kind: trusted.
- Statement: On macOS, `Thread.Mutex.DarwinImpl` stops at `os_unfair_lock_*`. The model is the
  lock's contract: an acquire `cmpxchg` 0→1 with a futex sleep, and a release `xchg` of 0
  with a wake. The C library is trusted to meet it. `Proofs/Threadsync/Lock.lean` elaborates
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
- Statement: `Io.async` allocates a runtime record and spawns the task as a model thread (or,
  under `fallible`, runs it in the caller). `await`/`cancel` join it and return the result
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
  does not promise this for relaxed atomics.
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
  addresses of the generated `air2lean_device`, reached through block-less pointers. The device
  neither observes nor changes model memory (no DMA, no aliasing of model blocks), so ordinary
  memory accesses are not events and their order relative to events is not claimed. Interrupts,
  other bus masters, timing, side effects of a read beyond the trace, and multi-threaded device
  access are outside the model. A declared `asm volatile` (`Zig.vasm`/`vasmEffect`) is an `asm`
  event of the same trace, with outputs from `Mem.dev.asmOracle`; a `memory` clobber is never
  declared. No correspondence with real hardware is claimed: the compiled
  program's volatile order is trusted to match the AIR order (TRU-03).
- Derived from: `ZigLean.Mem.Device`; tokens `vload`, `vstore`, `vasm`, `vasmEffect`, `DevOracle`, `AsmOracle`, `Device`,
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
- Derived from: `ZigLean.Float.CompilerRt`; tokens `Rt016`, `mulRt`, `RtChk`; header `float_semantics: compiler-rt`.
- Sources: [floats.md](floats.md#--float-semantics-ieee--compiler-rt).

## Inline assembly

<a id="asm-01"></a>
### ASM-01 — Register-only assembly is an opaque function

- Kind: trusted.
- Statement: Each distinct register-only inline asm `(source, constraints, widths)` becomes
  an opaque `airAsm_<hash>`. The model knows nothing about the instruction. The opaque is
  allowlisted in `assurance/policy.json`.
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

## Core runtime semantics

<a id="sem-01"></a>
### SEM-01 — Zig value and safety semantics

- Kind: meaning.
- Statement: `Zig.Result` is `Option (Except Zig.Error α)`. Safety-checked illegal behavior
  is a `Zig.Error` (`.illegal`, `.unspecified`, panics) rather than undefined behavior.
  Zig error unions are ordinary values. Integer, bit, vector, packed and union operations
  follow `ZigLean/Basic.lean` and its companions.
- Derived from: `ZigLean.Basic`, `ZigLean.Bit`, `ZigLean.Permutation`, `ZigLean.Packed`, `ZigLean.Union`, `ZigLean.Vec`, `ZigLean.Lemmas`; implied by TRU-02, SEM-02 and SEM-03.
- Sources: [generated-code.md](generated-code.md), [docs/generated-code.md §Panics](generated-code.md#panics).

<a id="sem-02"></a>
### SEM-02 — Byte-level block memory model

- Kind: environment.
- Statement: Memory is a CompCert-style list of blocks of bytes with kinds (stack, heap,
  global, OS mapping). Layout comes from `Zig.Enc` instances checked against the profile.
  Out-of-bounds, misaligned or dead accesses are `.illegal`; so is an access below an OS
  mapping's first live offset (`BlockKind.mapped lo`). Undefined bytes are explicit.
  `@returnAddress()` and an `undefined` pointer operand (`--allocator-model translated`) read
  the explicit oracle `Mem.arbitrary`, so a theorem over every initial memory covers every
  value sequence.
- Derived from: `ZigLean.Mem.Basic`, `ZigLean.Env.Host`, `ZigLean.Mem.Enc`, `ZigLean.Mem.Lemmas`, `ZigLean.Mem.Null`, `ZigLean.Mem.NullLemmas`, `ZigLean.Sep.*`; implied by THR-01.
- Sources: [generated-code.md](generated-code.md#memory), [null-pointers.md](null-pointers.md).

<a id="sem-03"></a>
### SEM-03 — Loops and triples are partial correctness

- Kind: meaning.
- Statement: `Zig.loop` is a `partial_fixpoint`. Divergence is `none`. `Triple` and loop
  rules constrain only completed results, so a diverging program satisfies them. Finite
  loops do not reduce in the kernel, so loop clients use runtime assertions or
  invariant-based proofs.
- Derived from: `ZigLean.Loop`, `ZigLean.RecTemplate`, `ZigLean.Sep.*`, `ZigLean.VC.*`; tokens `loop*`.
- Sources: [generated-code.md](generated-code.md#loops), [proofs.md](proofs.md).

<a id="sem-04"></a>
### SEM-04 — Total-correctness statements

- Kind: meaning.
- Statement: `TotalTriple` and `Conc.Total` theorems require an actual successful result
  for every satisfying state (or every oracle and sufficiently large fuel). They are stronger
  than SEM-03 and only cover their stated finite clients. `TotalTripleWithin B` additionally
  bounds the loop-body runs by `B` (`LoopRuns` counts); `ReturnsWithin B` bounds the scheduler
  budget uniformly in the oracle. `EventuallyReturnsUnder Fair` covers only the oracles that
  satisfy its stated premise and is not an unconditional total result.
- Derived from: `ZigLean.Sep.Total`, `ZigLean.Sep.Bounded`, `ZigLean.Sep.LoopTemplate`, `ZigLean.Sep.Step`, `ZigLean.Conc.Total`; the `sep_*` step tactics (they elaborate to `ZigLean.Sep.Step` lemmas).
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
  its fragment: an interpreter over the decoded `Air2Lean.Func`, over ZigLean's primitive
  operations and `Zig.MemM`, with `run` the least fixpoint over direct calls. Out-of-fragment
  and ill-typed steps are `⊥`. An AIR certificate (`Proofs/<Ex>/AirCert.lean`) relates the
  generated definition to this meaning; it does not relate the meaning to Zig, the exporter
  or canonicalization (TRU-02).
- Derived from: `Air2Lean.Sem`.
- Sources: [air-semantics.md](air-semantics.md).

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
  under `assumptions` by `scripts/external-contracts.py`. Any
  project `axiom` reached is a trusted premise and also fails the assurance gate unless it is
  allowlisted. The shipped policy allowlists none.
- Derived from: a reached source `axiom` declaration; a non-standard axiom in the compiled report.
- Sources: [external-models.md](external-models.md), [assumptions-audit.md](assumptions-audit.md).

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
  index for every request) with no other change, or a fresh block of kind `.mapped 0` of
  exactly `length` zero bytes at a page-aligned address above every earlier block. The
  kernel fails such a mapping only with `ENOMEM` (no other `MMapError` member). Other argument
  combinations are outside the model (`.unspecified`); `length = 0` is `.illegal`. `munmap` of
  the whole live range of one mapping ends it, of a page-aligned prefix moves its first live
  offset, of a page tail shrinks it; any other range (middle, past the mapping, not a live
  mapping: a double `munmap`) is `.illegal`, stricter than the kernel. `mremap` (Linux only)
  of a whole live mapping with flags 0 or `MAYMOVE`, no new address and `new_len > 0` shrinks
  in place, or grows (an allocation attempt) in place, by a move to a fresh page-aligned block
  under `MAYMOVE` (oracle `mremapMoves`, or no room), or fails with `error.OutOfMemory`;
  grown bytes up to the old page end are undefined, the rest zero. Page size: 4 KiB
  (`linux`), 16 KiB (`macos`), fixed per target (`Os.Target.pageSize`). Addresses are fresh:
  no address is reused after `munmap`.
- Derived from: `ZigLean.Os.Mmap`, `ZigLean.Sep.Mmap`; tokens `Zig.Os`; implies SEM-02.
- Sources: [os-mmap.md](os-mmap.md), [allocator-model.md](allocator-model.md),
  `ZigLean/Os/Mmap.lean`, `tests/roadmap/os-mmap/Check.lean`, Zig 0.16.0 `lib/std/posix.zig`,
  `lib/std/heap/PageAllocator.zig`.

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

## Reports

Each report below, and the premises a reader must accept to rely on it, is checked by the tool.

| Report | Premises |
|---|---|
| `scripts/assumptions.sh` JSON ([assumptions-audit.md](assumptions-audit.md)) | TRU-01, TRU-04, EXT-02 |
| `scripts/premises.py compiled` JSON (this page) | TRU-01, TRU-04 |
| Proof receipts ([proof-receipts.md](proof-receipts.md)) | TRU-01, TRU-04 |
| Check receipts `.lake/check-reports/` ([profiles.md](profiles.md#golden-comparisons-and-check-receipts)) | PRF-01, PRF-02, TRU-02 |
| Differential test results (`scripts/diff.sh`, [generated-code.md](generated-code.md#differential-test)) | TRU-02, TRU-03, THR-01, ALC-02, MTH-02 |
| ABI probe reports ([profiles.md](profiles.md#bounded-linux-native-abi-observations)) | PRF-02, TRU-03 |
| Allocation policy record ([allocation-policy-report.json](allocation-policy-report.json)) | ALC-01, ALC-02, TRU-02, TRU-03 |
| Weak CAS gate ([weak-cas.md](weak-cas.md)) | ORD-01, ORD-04, TRU-03 |
| Timed scheduler qualification (`tests/roadmap/deadline-futex/foundation-qualified-v4.json`) | TMR-02, THR-05 |
| Model registry evidence ([external-models.md](external-models.md)) | EXT-01, EXT-02 |
| Float probe (`scripts/floatprobe.sh`, [floats.md](floats.md)) | MTH-01, MTH-02, MTH-03, TRU-03 |
