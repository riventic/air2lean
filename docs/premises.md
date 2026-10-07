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
python3 scripts/premises.py compiled --assurance .lake/assurance/assumptions.json --output premises.json
```

## How premises are derived

The rules are in [assurance/premises.json](../assurance/premises.json). For each theorem,
the tool:

1. Strips comments and tokenizes the theorem's statement and proof. It resolves each
   identifier through the file's namespaces and `open` declarations, against declarations
   visible through its transitive imports.
2. Follows resolved project declarations (proof helpers, other theorems, generated `Gen.lean`
   functions and their callees) transitively. It stops at runtime (`ZigLean.*`) declarations
   and records their modules.
3. Maps every recorded runtime module through the reviewed `runtime_modules` table. It
   applies the token rules to every identifier in the closure. `statement` rules see only
   the theorem's own hypotheses and conclusion.
4. Adds the profile of every generated module reached. Its first-line
   `-- air2lean-profile:` header selects PRF-02; no header or `legacy-abi64-le` selects
   PRF-01. A generated import absent from the repository uses PRF-03.
5. Closes the set under the `implies` table and adds TRU-01 to every theorem.

The check fails if a runtime module with declarations has no mapping, if any ID is not
defined here, if a defined premise is referenced by no rule/module/report, if an import is
neither resolvable nor an allowed generated import, or if the committed index is stale.
Every theorem therefore has a derived premise set. TRU-01 alone means that the theorem
uses no runtime model.

**Limits of the source derivation.** Implicit dependencies are not visible in source.
These include simp sets such as `zig_unfold`, instances, auto-bound implicits and
tactic-generated terms. Generalized field notation on a local value also does not resolve.
The `compiled` mode applies the same tables to the kernel dependency graph of
`scripts/assumptions.sh`. That is the authoritative closure for `Proofs/` and `ZigLean/`.
It reports source-index gaps separately. Roadmap clients outside `Proofs/` have only the
source derivation. Committed `Proofs/*/Gen.lean` files are the 0.16.0 translations;
`scripts/check.sh` replaces them per Zig version. The index describes the committed files.

## Index

| Category | IDs |
|---|---|
| Target and build profiles | [PRF-01](#prf-01) [PRF-02](#prf-02) [PRF-03](#prf-03) |
| Allocator policies | [ALC-01](#alc-01) [ALC-02](#alc-02) [ALC-03](#alc-03) [ALC-04](#alc-04) |
| Thread creation and scheduling | [THR-01](#thr-01) [THR-02](#thr-02) [THR-03](#thr-03) [THR-04](#thr-04) [THR-05](#thr-05) [THR-06](#thr-06) [THR-07](#thr-07) [THR-08](#thr-08) |
| Memory ordering | [ORD-01](#ord-01) [ORD-02](#ord-02) [ORD-03](#ord-03) [ORD-04](#ord-04) |
| Timers and clocks | [TMR-01](#tmr-01) [TMR-02](#tmr-02) |
| Opaque math and floats | [MTH-01](#mth-01) [MTH-02](#mth-02) [MTH-03](#mth-03) |
| Inline assembly | [ASM-01](#asm-01) [ASM-02](#asm-02) |
| Core runtime semantics | [SEM-01](#sem-01) [SEM-02](#sem-02) [SEM-03](#sem-03) [SEM-04](#sem-04) |
| External models | [EXT-01](#ext-01) [EXT-02](#ext-02) |
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

## Allocator policies

<a id="alc-01"></a>
### ALC-01 — Single modelled allocator

- Kind: environment.
- Statement: `std.mem.Allocator` is one modelled allocator. Each allocation is a fresh
  `.heap` block with undefined bytes. A zero-byte allocation has no block. A free must name
  the start and whole length of a live heap block, or it is `.illegal`. `free` records the
  slice poison write. No native malloc address, reuse or identity behavior is modelled.
- Derived from: `ZigLean.Mem.Alloc`, `ZigLean.Sep.Alloc`; tokens `Allocator`.
- Sources: [std-models.md](std-models.md#allocator-model), `ZigLean/Mem/Alloc.lean`.

<a id="alc-02"></a>
### ALC-02 — Allocation failure and request-cap policy

- Kind: environment.
- Statement: `Mem.allocPolicy` (per-request `maxBytes`, finite failure indices) and the legacy
  `Mem.failAt` decide `OutOfMemory`. Theorems over arbitrary `Mem` quantify over every
  policy; a theorem that fixes initial memory fixes the policy. The cap is not a resource
  guarantee of the host.
- Derived from: `ZigLean.Mem.Alloc`; tokens `allocPolicy`, `AllocPolicy`, `failAt`, `releaseAttempt`.
- Sources: [allocation-policy.md](allocation-policy.md), [allocation-policy-report.json](allocation-policy-report.json).

<a id="alc-03"></a>
### ALC-03 — Byte remap policy

- Kind: environment.
- Statement: `remap` fails for nonzero-size items under the default policy. An explicit
  `Mem.allocPolicy.byteRemap` selects in-place or moved success for whole alignment-1 byte
  buffers. `resize` is outside the boundary.
- Derived from: `ZigLean.Sep.Remap`; tokens `remap`, `Remap`.
- Sources: [std-models.md](std-models.md#allocator-model), `tests/roadmap/resize-remap`.

<a id="alc-04"></a>
### ALC-04 — Byte sentinel allocation

- Kind: environment.
- Statement: `allocSentinel(u8, n, s)` allocates `n + 1` owned bytes with the sentinel at
  offset `n`. The payload is undefined. Only Zig 0.16.0 with an explicit `sentinel_byte` is admitted.
- Derived from: `ZigLean.Sep.Sentinel`; tokens `allocSentinel`, `freeSentinel`.
- Sources: [std-models.md](std-models.md#allocator-model), [byte sentinel README](../tests/roadmap/byte-sentinel/README.md).

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
  waits for the child and merges its clock. Only the spawner may join, once. An unjoined
  child at thread end is `.illegal`. The child protocol obligation (`spawnInit`) is explicit.
- Derived from: `ZigLean.Conc.Sched`; tokens `spawnC`, `joinC`, `spawnInit`.
- Sources: [std-models.md](std-models.md#thread-model), [generated-code.md](generated-code.md#atomics-and-threads).

<a id="thr-03"></a>
### THR-03 — Fallible thread assignment policy

- Kind: environment.
- Statement: The opt-in `fallible` policy adds the declared spawn errors and the `Io.Group`
  caller-execution fallback. WP rules must cover every oracle outcome.
- Derived from: `ZigLean.Conc.Spawn`, `ZigLean.Conc.SpawnLemmas`; tokens `SpawnPolicy`, `WithPolicyC`.
- Sources: [spawn-failure.md](spawn-failure.md).

<a id="thr-04"></a>
### THR-04 — `Io.Group` tasks are model threads

- Kind: environment.
- Statement: `Group.async`/`concurrent` spawn a recorded task; `Group.await` joins the tasks
  in spawn order. Cancellation is not modelled, so `Group.cancel` is `await`.
- Derived from: tokens `groupAsyncC`, `groupAwaitC`, `groupConcurrentC`, `groupCancelC`.
- Sources: [std-models.md](std-models.md#thread-model).

<a id="thr-05"></a>
### THR-05 — Futex model

- Kind: environment.
- Statement: A futex wait on a matching `u32` sleeps until a wake at that address. Waiters
  wake in FIFO order. There is no spurious wakeup or cancellation, and a wake adds no
  happens-before edge. No runnable thread with an unfinished thread is `Zig.Error.deadlock`.
- Derived from: `ZigLean.Conc.Lock`, `ZigLean.Conc.LockRules`; tokens `futex`, `Futex`.
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
  results hold only for the finite single-task client in `ZigLean.Conc.Total`.
- Derived from: `ZigLean.Conc.Progress`, `ZigLean.Conc.Total`; tokens `spinLoopHint`, `threadYield`.
- Sources: [progress-hints.md](progress-hints.md).

<a id="thr-08"></a>
### THR-08 — Protocol (rely-guarantee / CSL) proofs over all schedules

- Kind: meaning.
- Statement: `Conc.Proto.run_sound`/`run_safe` and the CSL/lock/word rules are
  kernel-proved. A client theorem holds for the protocol, global invariant, ghost state and
  ownership splits that it states or discharges. Strict-safety theorems additionally exclude
  every scheduler error, including races and deadlock.
- Derived from: `ZigLean.Conc.Logic`, `ZigLean.Conc.Csl`, `ZigLean.Conc.Own`, `ZigLean.Conc.Lemmas`, `ZigLean.Conc.Lock*`, `ZigLean.Conc.Word`.
- Sources: [proofs.md](proofs.md), [rwlock-contracts.md](rwlock-contracts.md).

## Memory ordering

<a id="ord-01"></a>
### ORD-01 — RC11 approximation for atomics

- Kind: environment.
- Statement: Each atomic location keeps a modification order of messages with release
  clocks. Reads may see any message not older than a happens-before or own observation.
  RMWs read a message with no RMW after it. The model admits more outcomes than RC11 (a plain
  write of the same value, read views not transferred through release/acquire), never fewer.
  Atomic pointees are integers, enums, bools or packed structs.
- Derived from: `ZigLean.Mem.Thread`, `ZigLean.Conc.Word`; tokens `atomicLoad*`, `atomicStore*`, `atomicRmw*`, `cmpxchg*`, `AtomicOrder`, `RmwOp`.
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

## Timers and clocks

<a id="tmr-01"></a>
### TMR-01 — No clock in the default model

- Kind: environment.
- Statement: The default runtime has no clock. Reaching `time.Timer` or
  `Thread.Futex.timedWait` (0.15.2 `Futex.Deadline` with a timeout) is `.unspecified`.
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
- Sources: [deadline-runtime.md](deadline-runtime.md), [deadline-futex-design.md](deadline-futex-design.md).

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
- Derived from: `statement` rule on `airAsm_<n>` in the theorem's own type.
- Sources: `Proofs/Asm/Proofs.lean`.

## Core runtime semantics

<a id="sem-01"></a>
### SEM-01 — Zig value and safety semantics

- Kind: meaning.
- Statement: `Zig.Result` is `Option (Except Zig.Error α)`. Safety-checked illegal behavior
  is a `Zig.Error` (`.illegal`, `.unspecified`, panics) rather than undefined behavior.
  Zig error unions are ordinary values. Integer, bit, vector, packed and union operations
  follow `ZigLean/Basic.lean` and its companions.
- Derived from: `ZigLean.Basic`, `ZigLean.Bit`, `ZigLean.Permutation`, `ZigLean.Packed`, `ZigLean.Union`, `ZigLean.Vec`, `ZigLean.Lemmas`; implied by TRU-02.
- Sources: [generated-code.md](generated-code.md), [docs/generated-code.md §Panics](generated-code.md#panics).

<a id="sem-02"></a>
### SEM-02 — Byte-level block memory model

- Kind: environment.
- Statement: Memory is a CompCert-style list of blocks of bytes with kinds (stack, heap,
  global). Layout comes from `Zig.Enc` instances checked against the profile. Out-of-bounds,
  misaligned or dead accesses are `.illegal`. Undefined bytes are explicit.
- Derived from: `ZigLean.Mem.Basic`, `ZigLean.Mem.Enc`, `ZigLean.Mem.Lemmas`, `ZigLean.Mem.Null`, `ZigLean.Sep.*`.
- Sources: [generated-code.md](generated-code.md#memory), [null-pointers.md](null-pointers.md).

<a id="sem-03"></a>
### SEM-03 — Loops and triples are partial correctness

- Kind: meaning.
- Statement: `Zig.loop` is a `partial_fixpoint`. Divergence is `none`. `Triple` and loop
  rules constrain only completed results, so a diverging program satisfies them. Finite
  loops do not reduce in the kernel, so loop clients use runtime assertions or
  invariant-based proofs.
- Derived from: `ZigLean.Loop`, `ZigLean.Sep.*`, `ZigLean.VC.*`; tokens `loop*`.
- Sources: [generated-code.md](generated-code.md#loops), [proofs.md](proofs.md).

<a id="sem-04"></a>
### SEM-04 — Total-correctness statements

- Kind: meaning.
- Statement: `TotalTriple` and `Conc.Total` theorems require an actual successful result
  for every satisfying state (or every oracle and sufficiently large fuel). They are stronger
  than SEM-03 and only cover their stated finite clients.
- Derived from: `ZigLean.Sep.Total`, `ZigLean.Sep.LoopTemplate`, `ZigLean.Conc.Total`.
- Sources: `ZigLean/Sep/Total.lean`, [progress-hints.md](progress-hints.md).

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
- Sources: [generated-code.md](generated-code.md), [profiles.md](profiles.md#golden-comparisons-and-check-receipts), [air-json.md](air-json.md).

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
