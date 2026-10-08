# Architecture audit 5/6: hand-written models and the size of the trust base

Status: audit of `origin/main` at `af9ddc30` (2026-10-08). Unmerged branches are named where they
change the picture. Nothing here changes a model. The native-vs-model counterexamples are in
[`tests/roadmap/architecture-audit/models/`](../../tests/roadmap/architecture-audit/models/check.sh).

**Principle (user decision, 2026-10-08).** Only base OS primitives get trusted models: memory
uses `posix.mmap`/`munmap`/`mremap` (premise OSM-01), and IO uses posix-level
`read`/`write`/`close`/clock (`allocators-from-os-primitives` design). Everything above them
must be translated from the real Zig code and proved: std allocators, `std.Io`, `std.Thread`
sync, containers, math and formatting. A hand-written model of std code can diverge from that
code. It also does not extend to user-written code with the same interface.

Already reported elsewhere, so not repeated here: B1 (std models are matched by bare
fully qualified name, without module identity; `codex/fix-module-identity`) and the
unchecked-illegal-behavior inventory (`codex/fix-unchecked-illegal`).

## Summary

| Class | Meaning | Count on main |
|---|---|---|
| **A** | OS or hardware primitive. Keep it trusted, behind an explicit premise. | 7 |
| **B** | Hand model of std code. Migrate it to translation. | 33 |
| **C** | Compiler builtin semantics. Needs a faithful spec of the builtin. | 8 |
| **R** | Recognized name that is rejected. No model, fails closed. | 2 |
| **U** | User boundary (project registry/contracts). Not std. | 1 (+1 policy hole) |

Most of the B items are *reachable without the user knowing*. Two built-in type
specializations do this. Every translated function with a `std.mem.Allocator` or `std.Io`
parameter is proved against **one** hand model, whatever allocator or Io the caller passes.
The generated code and the premise index do not record this as a caller obligation. Four
counterexamples (below; fixtures pass) show provable model properties that are false natively.

Top divergences:

1. **D-ALLOC-ALIAS**. An allocator over caller-visible memory (FixedBufferAllocator, arena
   over a buffer, any user allocator) returns memory that aliases existing data. The model
   always returns a fresh disjoint block. Native result `42`; model result `0` or
   `OutOfMemory` under every policy.
2. **D-ALLOC-REMAP**. In the model, `remap` of a slice of items wider than one byte returns
   `null` under every `Mem.allocPolicy`. `std.heap.page_allocator` shrinks in place and
   returns the slice. Native `1`; model always `0`.
3. **D-IO-CANCEL**. The model treats `Io.Group.cancel` as `await`, and a cancelable
   `Io.futexWait` never returns `error.Canceled`. Native `Io.Threaded` cancels the waiter and
   returns `1`. The model only deadlocks, so "never returns 1" is provable in the model.
4. **D-IO-INLINE**. Under the default `available` policy every `Group.async` task is a new
   thread. An Io that runs `async` inline (`Io.Threaded.global_single_threaded`; the API
   permits this) hangs natively on a hand-off that the model proves always completes with `5`
   and never deadlocks.
5. Futex spurious wakeups are absent from the model. They are documented std behavior
   (`lib/std/Io.zig:1541-1549`).
6. Evidence gap. Every allocator differential and native gate runs against a *hand-written
   mirror* of the model (`tests/diff/common.zig` `TestAllocator`,
   `tests/roadmap/resize-remap/native.zig` `BoundedAllocator`), never against a real std
   allocator. That is why 1 and 2 went unnoticed.

## Inventory

Columns:

- **Claims**: the Zig version or source the item claims to follow.
- **Check**: how correspondence to the real code is established.
- **Reach**: whether user code reaches the item without the user knowing.
- **Premise**: the ID in [docs/premises.md](../premises.md).

### 1. `Air2Lean/StdModels.lean` rows (31: 29 modelled, 2 rejected)

The translator selects a row by std name, or by an instance `<name>__anon_<n>`.

| ID | Symbol(s) | Lean model | Claims | Check | Premise | Reach | Class |
|---|---|---|---|---|---|---|---|
| S01–S04 | `mem.Allocator.create`, `destroy`, `alloc`, `alignedAlloc` | `Zig.Allocator.*` (`ZigLean/Mem/Alloc.lean`) | unqualified, so "every audited version" | Diff test against `TestAllocator`, a mirror of the model. No proof against `lib/std/mem/Allocator.zig`. | ALC-01, ALC-02 | Yes: any `Allocator` parameter | B |
| S05 | `mem.Allocator.allocSentinel` | `Zig.Allocator.allocSentinel` | 0.16.0 | 13-row native gate with `TestAllocator` | ALC-04 | Yes | B |
| S06 | `mem.Allocator.free` | `free`, `freeSentinel` (`poisonFree`) | unqualified | Diff test against the mirror | ALC-01 | Yes | B |
| S07 | `mem.Allocator.dupe` | `Zig.Allocator.dupe` | unqualified | Diff test against the mirror | ALC-01 | Yes | B |
| S08 | `mem.Allocator.remap` | `Zig.Allocator.remap` (null for item size > 1; byte policies) | unqualified | 3-row gate against `BoundedAllocator` (a mirror) | ALC-03 | Yes. **Diverges** (D-ALLOC-REMAP) | B |
| S09 | `mem.Allocator.realloc` | `Zig.Allocator.realloc` | 0.16.0 | Gate with mirror allocators | ALC-05 | Yes | B |
| S10–S11 | `Thread.spawn`, `Thread.join` | `spawnC`, `spawnWithPolicyC`, `joinC` | unqualified | Diff test (schedule search) against native threads | THR-01–03 | Yes | B (base A: `pthread_create`/`clone`, join futex) |
| S12 | `Thread.yield` | `threadYieldC` | unqualified | Progress-hint gate | THR-07 | Yes | B (thin; base A: `sched_yield`) |
| S13–S14 | `atomic.spinLoopHint`, `Thread.spinLoopHint` | `spinLoopHintC` | unqualified | Audited instruction list | THR-07 | Yes | C (CPU hint instruction) |
| S15–S17 | `Io.futexWait`, `Io.futexWaitUncancelable`, `Io.futexWake` | `futexWaitCancelableC`, `futexWaitC`, `futexWakeC` | 0.16.0 (row unqualified) | Diff test for `sync` (native `Io.Threaded`) | THR-05 | Yes. **Diverges**: no spurious wakeup, never cancels (D-IO-CANCEL) | B (vtable dispatch into `Io.Threaded`; base A: futex syscall / `__ulock`) |
| S18–S19 | `Thread.Futex.wait`, `Thread.Futex.wake` | `threadFutexWaitC`, `threadFutexWakeC` | 0.14.1, 0.15.2 (row unqualified) | Diff test for `threadsync` | THR-05 | Yes. No spurious wakeup. | B (thin; base A) |
| S20–S22 | `Thread.Mutex.DarwinImpl.lock`, `unlock`, `tryLock` | `osUnfairLockC`, `osUnfairUnlockC`, `osUnfairTryLockC` | 0.15.2 macOS | Kernel proofs of the contract only; no native check of non-owner behavior | THR-06 | Yes, on macOS. Diverges on non-owner unlock and recursive lock: native aborts, model proceeds (see D6). | A (`os_unfair_lock_*` is the OS primitive; the cut sits at the Zig wrapper because the exporter does not name `extern` functions) |
| S23–S25 | `time.Timer.start`, `time.Timer.read`, `Thread.Futex.timedWait` | `callRC` + `Error.unspecified` | unqualified | Diff test pins the count of `.unspecified` | TMR-01 | Yes. Conservative: always `.unspecified`. | B (base A: `clock_gettime`, timed futex) |
| S26–S29 | `Io.Group.async`, `concurrent`, `await`, `cancel` | `groupAsyncC`, `groupConcurrentC`, `groupAwaitC`, `groupCancelC` (= await) | 0.16.0 (row unqualified) | Diff test for `iogroup` (native `Io.Threaded`, 2 functions) | THR-02, THR-03, THR-04 | Yes. **Diverges** (D-IO-CANCEL, D-IO-INLINE) | B |
| S30 | `Io.futexWaitTimeout` | rejected | — | — | — | Fails closed | R |
| S31 | `Thread.detach` | rejected | — | — | — | Fails closed | R |

Unmerged `codex/alloc-translated-p1` adds `posix.mmap`, `posix.munmap` and `posix.mremap`
(`ZigLean/Os/Mmap.lean`, OSM-01). They are class A and active only under
`--allocator-model translated`. In that mode the allocator rows are inactive and
`mem.Allocator` is an ordinary struct.

### 2. Built-in type specializations (`Air2Lean/Air/Json.lean:185-187`)

| ID | Zig type | Becomes | Effect | Check | Premise | Reach | Class |
|---|---|---|---|---|---|---|---|
| T01 | `mem.Allocator` (`{ptr, vtable}`) | `Ty.allocator` → `Zig.Allocator` (a unit structure; 16 zero bytes in memory) | Every allocator a caller passes is the single model allocator. Allocator constants (`heap.page_allocator`, `Allocator.failing`) and `fba.allocator()` are rejected inside translated code (`'elems' constant of unexpected type`; provenance error). The collapse therefore enters only through **parameters**. Those parameters carry no premise in the generated output. | none | ALC-01 (only when a proof token reaches `Allocator`) | Yes, silently | B |
| T02 | `Thread` | `Ty.thread` → `Zig.ThreadId` | Native handle not modelled | — | THR-02 | Only via spawn | B |
| T03 | `Io` (`{userdata, vtable}`) | `Ty.io` → `Zig.Io` | Every Io implementation (Threaded, `global_single_threaded`, Uring, Kqueue, Dispatch, user-written) is one model | Diff test with `Io.Threaded` only | THR-02, THR-04, THR-05 | Yes, silently | B |

`Check.lean` also recognizes shapes by name for signature checks (`Thread.SpawnConfig`,
`Io.Group`, `time.Timer`, `Thread.Mutex.DarwinImpl`). These are not models, but they share
the B1 name-identity weakness.

### 3. `ZigLean` runtime modules that model std behavior

| ID | Module(s) | Models | Claims | Check | Premise | Reach | Class |
|---|---|---|---|---|---|---|---|
| Z01 | `Mem/Alloc.lean` | `std.mem.Allocator` wrappers, a single allocator, failure/remap policies | own rules, "same rules as `TestAllocator`" | mirror allocator | ALC-01–05 | via T01 | B |
| Z02 | `Sep/RawAlloc.lean` | vtable contracts `vtableAlloc`/`Resize`/`Remap`/`Free` | — | none (contracts only; the translator does not reach them) | ALC-06 | Not reached | B (superseded by `AllocSpec`, P3) |
| Z03 | `Mem/Owned.lean`, `Sep/Owned.lean`, `Sep/ArenaClient.lean` | `heap.ArenaAllocator`, `heap.FixedBufferAllocator` | 0.16.0 sources | none against the sources. Known gaps: fresh addresses instead of in-buffer addresses (M05, the same root cause as D-ALLOC-ALIAS); growth remap fails (M02); 0.16 arena is lock-free, the model is not. | ALC-07 | Hand-written clients only | B (legacy; delete) |
| Z04 | `Sep/Alloc.lean`, `Sep/Remap.lean`, `Sep/Sentinel.lean`, `Sep/SentinelRealloc.lean` | Lemma libraries over Z01 | — | kernel | ALC-01–05 | via proofs | B (retire with Z01) |
| Z05 | `Mem/Thread.lean` fork/join bookkeeping, `Conc/Call.lean` spawn/futex/group/os-lock ops, `Conc/Spawn.lean` policies | `Thread.spawn`/`join`, futex, `Io.Group`, `os_unfair_lock` | see S rows | see S rows | THR-02–06 | via S rows | B (os-lock: A) |
| Z06 | `Conc/Sched.lean`, `Mem/Thread.lean` atomics (RC11 approximation) | Hardware interleaving and memory model | RC11 | litmus tests, diff test | THR-01, ORD-01–04 | always | A (hardware) |
| Z07 | `Conc/Progress.lean` | yield / spin hint | — | gate | THR-07 | via S12–S14 | counted in S12–S14 |
| Z08 | `Time.lean`, `Conc/Timed*.lean` (`TimedCall` "source-shaped values mirror the audited AIR") | `std.Io` timed wait, clocks | 0.16.0 | Adapter tests only. No translator path. | TMR-02 | Not reachable (opt-in) | B (hand-written mirror of `std.Io` types) |
| Z09 | `Env.lean` | abstract handle IO and clocks | — | — | ENV-01, ENV-02 | Not reachable (opt-in) | A (abstract OS boundary) |
| Z10 | `Float/{Format,Value,Round,Ops,Lemmas,…}.lean` | AIR float ops, IEEE-754 | IEEE-754 | `floatprobe`, diff test | MTH-01 | always | C (diverges from the reference target's compiler_rt in groups A, B and E–H by design; documented in `docs/floats.md`) |
| Z11 | `Float/Allowed.lean` | target float variation (NaN payloads, ±0 in `@min`/`@max`) | x86-64 SSE | probe | MTH-01 | always | C |
| Z12 | `Float/CompilerRt.lean` (748 lines) | hand ports of `__multf3`, `__divtf3`, `fma*`, `__truncxfhf2`, `__fmodx`, floor/ceil, `sqrtq` | per version 0.14.1/0.15.2/0.16.0 | bit-exact sampling (`divRt016`: 80k random + 3.1M edge cases), probe, diff test (`floatops`) | MTH-03 | opt-in `--float-semantics compiler-rt` | B (compiler_rt is Zig source; translate it instead of porting by hand) |
| Z13 | `Float/Libm.lean` | `@sin`, `@cos`, `@tan`, `@exp`, `@exp2`, `@log`, `@log2`, `@log10` | Zig specifies no accuracy | opaque. Has no equations, so it is sound. `implemented_by` links real compiler_rt for tests. | MTH-02, TRU-04 | always | C |
| Z14 | `External.lean`, `External/Callback.lean` | user contracts | — | user proof or axiom | EXT-01, EXT-02 | explicit | U |

### 4. Translator-level substitutions

| ID | Where | What | Check | Premise | Class |
|---|---|---|---|---|---|
| X01 | `panicErrorFor?` (`Air2Lean/Air/Op.lean:299`) | `debug.defaultPanic` and `debug.FullPanic(defaultPanic).*` → a `Zig.Error` constructor. The std panic handler (printing, abort) is not translated. User-overridden handlers are rejected. | diff harness panic report | SEM-01 | C |
| X02 | `@tagName` helpers (`Emit.lean` enum helpers) | names come from the exporter's type table | goldens | SEM-01 | C |
| X03 | `errorNameOf` (`Emit.lean:2956`) | name table of the program's error sets; an unknown error is `.unspecified` | goldens | SEM-01 | C |
| X04 | register-only inline asm → opaque `airAsm_<n>` | — | — | ASM-01, ASM-02 | A |
| X05 | `extern` globals → `ExternInit` fields | link-time environment | — | (environment) | A |
| X06 | `ret_addr` → return-address oracle | `codex/alloc-translated-p1` only | — | — | C |
| X07 | project registry `--model-registry` (`ModelRegistry.lean`) | binds **any** untranslated direct callee except built-in std names. Nothing stops a project, or the unmerged `codex/roadmap-io-boundary` (`registry/std15.json`, `std16.json`), from hand-modelling std functions. | proof or axiom per binding | EXT-01, EXT-02 | U, plus a policy hole (W4) |
| X08 | `TestAllocator` (`tests/diff/common.zig:67`), `BoundedAllocator` (`resize-remap/native.zig`) | the "native" side of every allocator differential is a hand-written allocator that mirrors the model | — | — | evidence gap (W3) |

Additional class A items on unmerged branches: OSM-01 mmap (P1/P2), ENV-03 Linux
`read`/`write`/`close`/errno (`codex/roadmap-io-boundary`), and device volatile/asm effects
(`codex/roadmap-device-effects`).

Class tally on main (each ID once; Z05 and Z07 duplicate S rows and are not counted again;
X06 and the unmerged-branch items are excluded; X08 is evidence, not a pipeline model):

- A (7): S20–S22, Z06, Z09, X04, X05.
- B (33): S01–S12 (12), S15–S19 (5), S23–S29 (7), T01–T03 (3), and Z01, Z02,
  Z03, Z04, Z08, Z12 (6).
- C (8): S13, S14, Z10, Z11, Z13, X01, X02, X03.
- R (2): S30, S31.
- U (1): Z14, plus the X07 policy hole.

## Divergences (native vs model)

Run `bash tests/roadmap/architecture-audit/models/check.sh`. It needs the patched 0.16.0
exporter and stock 0.16.0, and exits 0 while the divergences are present. It runs on macOS
for native execution and exports AIR for `x86_64-linux`. Observed on 2026-10-08:

```
--- model                                  --- native
aliasProbe[default|inPlace|move]=0         aliasProbe(FixedBufferAllocator)=42
aliasProbe[fail0]=error.OutOfMemory
remapProbe[default|inPlace|move]=0         remapProbe(page_allocator)=1
remapProbe[fail0]=error.OutOfMemory
cancelProbe=error:Zig.Error.deadlock       cancelProbe(Threaded)=1
handoffProbe=5 (or out of fuel)            handoffProbe(single_threaded)=hang (timeout 124)
```

| ID | Root | Model statement that is provable but false natively | Fixture |
|---|---|---|---|
| D-ALLOC-ALIAS | T01 + Z01: fresh disjoint block for every allocator | "`create` leaves every existing block unchanged" (frame and separation). False for FixedBufferAllocator, an arena over a buffer, or any user allocator over visible memory. | `alloc_probe.zig` `aliasProbe` |
| D-ALLOC-REMAP | S08: `Allocator.remap` returns `none` when `size ≠ 1`, regardless of policy; byte remap also needs alignment 1 | "`remap` of a non-byte slice never succeeds". False for `page_allocator`, `c_allocator` and `smp_allocator` shrinks. | `remapProbe` |
| D-IO-CANCEL | S15, S29: never cancels; `cancel = await` | "the task's `futexWait` never fails", "`cancelProbe` never returns 1" | `io_probe.zig` `cancelProbe` |
| D-IO-INLINE | T03 + THR-02 default `available` | "the hand-off never deadlocks" (`run_safe`). False for an Io whose `async` runs inline (`global_single_threaded`, a saturated `async_limit`). `--spawn-policy fallible` includes the inline fallback, but it is opt-in. | `handoffProbe` |
| D5 futex spurious | S15–S19 | "a wait returns only after a wake". The std doc says spurious wakeups are possible (`Io.zig:1541-1549`, and the same for `Thread.Futex`). No fixture, because forcing one natively needs signal injection. | — |
| D6 os_unfair_lock | S20–S22 | Non-owner unlock succeeds in the model. Natively, libplatform aborts ("Unlock of an os_unfair_lock not owned by current thread"). Recursive lock is a model deadlock but a native abort. Zig documents non-owner unlock as illegal behavior, so the model misses illegal behavior. Overlaps the unchecked-IB inventory. | — |
| D7 float default | Z10 | The default `ieee` mode differs from the reference target for f128 `*` and `/`, `@mulAdd`, f80→f16, and f80 rem/floor (groups A, B, E–H). Documented and labeled, so not hidden. | `docs/floats.md` |

## Structural weaknesses

- **W1: identity collapse (T01, T03).** A `std.mem.Allocator` or `std.Io` parameter is a
  universally quantified interface in Zig, but the translator turns it into one concrete
  model. The resulting theorem is about the model allocator or Io, yet it reads as a theorem
  about the Zig function. The generated header, the `-- air2lean-models:` marker and the
  premise index do not name the parameter as a caller obligation. This is the main reason
  hand models "do not extend to user-written code": a user allocator or Io passed in is
  silently replaced.
- **W2: fail-open version qualification.** 27 of 29 modelled rows have
  `zigVersions := #[]` ("every audited version"). When a new version is added to
  `zig-patch/versions.toml` (0.17 is in progress), these rows apply to changed std code
  without review. In 0.17, `Allocator.create` goes through an inline
  `createAdvancedWithRetAddr`, and `Io` grew. Rows should list versions explicitly.
- **W3: mirror evidence.** The allocator rows are checked only against allocators written to
  match the model (X08). The model is never checked to include native behavior
  (model ⊇ native) of real std allocators.
- **W4: registry as a backdoor.** `--model-registry` lets a project hand-model any
  untranslated std function. Only names in `stdModels` are blocked, and that block is a bare
  name test (B1). Under the principle, std-namespace bindings should be limited to an
  OS-primitive allowlist. That needs B1 module identity first.
- **W5: cut points above the primitive.** `Thread.Mutex.DarwinImpl.*` and the P1 `posix.*`
  rows trust Zig wrapper code (`posix.mmap`'s errno switch, the `DarwinImpl` method) as well
  as the primitive, because the exporter does not name `extern` calls. The trusted base
  would be smaller if the cut moved to `system.mmap` / the `extern` symbol. The io-boundary
  branch already translates `posix.read` and its errno mapping.

## Migration plan (ordered by risk × reach)

Dependencies point to the allocator translated-mode track (P0–P6,
`codex/alloc-translated-p*`) and the IO boundary (E03, `codex/roadmap-io-boundary`).

| Step | What | Fixes | Depends on | Effort |
|---|---|---|---|---|
| 0a | Make `Allocator`/`Io` parameters an explicit premise. Generated output and the premise index mark every entry function whose signature contains T01 or T03 ("caller passes the model allocator/Io"). Alternatively, require `--allocator-model std` to be opted into per function. | W1 visibility | — | S (translator + premises.py) |
| 0b | Explicit `zigVersions` on every `stdModels` row; an empty list means rejected. | W2 | — | XS |
| 0c | Native "model ⊇ real" legs: run the allocator examples natively with `page_allocator`, `DebugAllocator` and `FixedBufferAllocator`, and check that each native result is in the model's outcome set over policies. Same for Io with `global_single_threaded`. | W3; would have caught D-ALLOC-*, D-IO-INLINE | — | S |
| 0d | Registry allowlist for std-namespace symbols (OS primitives only). | W4 | B1 module identity | S |
| 1 | **Allocator translated mode becomes the default.** P2 mmap model → P3 `AllocSpec` + `mem.Allocator` wrappers proved once for any vtable → P4 PageAllocator → FixedBufferAllocator → P5 lock-free Arena → P6 flip the default, regenerate goldens, port the proofs that use `Zig.Allocator`. Then retire S01–S09, T01, Z01–Z04 and `TestAllocator` (which becomes a translated user allocator). D-ALLOC-ALIAS and D-ALLOC-REMAP disappear by construction: FixedBufferAllocator memory *is* the buffer, and `PageAllocator.remap` is translated. | D-ALLOC-*, W1 for allocators | P1 (done), P2–P6 | L (~2–3 months, per the design) |
| 2 | Interim widening of the futex/Io rows (sound direction, small): an oracle choice for a spurious return of `futexWait`, `Canceled` for cancelable waits after `cancel`, and inline `async` in the default policy (make the `fallible` fallback the default for `Group.async`). Then the four Io-side divergences become model outcomes. | D-IO-*, D5 | — | S–M (proof updates for `sync`, `iogroup`, `threadsync`) |
| 3 | **OS thread and futex primitives (A) and translated `std.Thread`.** Trust `futex(2)` / `__ulock_wait` / `__ulock_wake`, `pthread_create`/`pthread_join` (or `clone`), `sched_yield`, `clock_gettime`, `os_unfair_lock_*` at the `extern` symbol. Translate `Thread.Futex`, `Thread.spawn`/`join`/`yield`, `time.Timer` and `Futex.timedWait`. Blockers: the exporter must name `extern` calls (W5); `*anyopaque` context casts and function pointers (shared with P1); `clone` inline asm on the non-libc Linux path (prefer the libc/pthread profile); thread stacks come from the page allocator (needs step 1). | S10–S12, S18–S25, Z05 | step 1 vtable machinery, exporter `extern` names | L |
| 4 | **`std.Io` as an interface, like the allocator.** Translate `Io.zig`'s vtable dispatch (`futexWait`, `Group.*`, `Mutex`, …). Define an `IoSpec` (futex, group, cancelation, timeouts) that a translated client is proved against for *any* Io. Prove `Io.Threaded` ⊨ `IoSpec` from the step 3 primitives and the E03 `read`/`write`/`close`. Retire S15–S17, S26–S29, T03 and Z08. | D-IO-*, W1 for Io | steps 1 and 3, E03 io-boundary | XL (`Io.Threaded` is large: thread pool, cancelation, kqueue/uring backends; start with Threaded's minimal futex + group path) |
| 5 | **compiler_rt translated instead of ported.** Export `lib/compiler_rt/{mulf3,divtf3,fma,truncxfhf2,fmod,floor_ceil,sqrt}.zig` with the AIR exporter as a library. In compiler-rt mode, bind the AIR float ops to the translated functions. Keep `ieee` as an abstract spec (C). | Z12 | exporter export of compiler_rt units; u128/f80 bit ops (present) | M (low reach: opt-in mode) |
| 6 | Delete legacy hand models: Z03 Arena/FBA (after P5), Z02 raw contracts (after P3), Z08 Timed mirror (after step 4). | trust base size | 1, 4 | S |

Keep trusted (class A, explicit premises): OSM-01 mmap/munmap/mremap; ENV-03
read/write/close and clocks; the futex syscall and `__ulock`; `pthread_create`/`join`;
`sched_yield`; `clock_gettime`; `os_unfair_lock_*`; the scheduler and RC11 approximation
(hardware); opaque asm; `extern` initial state. Keep as builtin specs (class C), each
checked against the langref and the compiler_rt actually linked: AIR op semantics, IEEE
floats with the target-variation sets, opaque libm, the panic map, tag and error names,
`@returnAddress` oracle.
