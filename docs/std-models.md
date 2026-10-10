# Std functions: translated or modelled

A std function that an example calls is one of these:

| Kind | How | Where |
|---|---|---|
| Translated | Its AIR is written and translated like user code, so the diff test checks it too. | its name prefix in `examples/<ex>/filter` |
| Modelled | Not translated. A call to it is a call to a Lean model. Only for the Zig versions its row lists. | `Air2Lean/StdModels.lean` (`stdModels`), `ZigLean/Mem/Alloc.lean` |
| Panic handler | A noreturn call: a `Zig.Error` constructor. | `panicErrorFor?` (`docs/generated-code.md` §Panics) |

`Check.lean` rejects a call to a function that has no AIR file and no model.

A model or panic handler matches only a function of the `std` module, and the special std
types (`mem.Allocator`, `Thread`, `Io`) only std types: the translator looks them up by a
module-qualified key ([AIR JSON §Identity](air-json.md#identity)). A user `Thread.zig` with a
`spawn` is user code (`root:Thread.spawn`), never the `Thread.spawn` model.

## Version qualification

Every modelled row of `stdModels` lists the Zig versions it is qualified for, each with the
std file that defines the symbol and that file's SHA-256 at review (`StdReview`). A version
that is not listed is rejected (`<symbol> qualified Zig <versions>; no reviewed std source for
Zig <version>`), so a new Zig release (0.17 changes `Allocator.create` and grows `Io`) never
inherits a model silently. Qualifying a version means reading that version's definition
against the model and adding its hash; `tests/roadmap/models/test_std_sources.py` recomputes
every hash from the std sources that are present.

| Rows | std file | Zig versions |
|---|---|---|
| `mem.Allocator.create`, `destroy`, `alloc`, `alignedAlloc`, `free`, `dupe`, `remap` | `mem/Allocator.zig` | 0.14.1, 0.15.2, 0.16.0 |
| `mem.Allocator.allocSentinel`, `realloc` | `mem/Allocator.zig` | 0.16.0 |
| `Thread.spawn`, `join`, `yield` | `Thread.zig` | 0.14.1, 0.15.2, 0.16.0 |
| `atomic.spinLoopHint` | `atomic.zig` | 0.14.1, 0.15.2, 0.16.0 |
| `Io.futexWait`, `futexWaitUncancelable`, `futexWake`, `Io.Group.async`, `concurrent`, `await`, `cancel` | `Io.zig` | 0.16.0 |
| `Thread.Futex.wait`, `wake`, `timedWait` | `Thread/Futex.zig` | 0.14.1, 0.15.2 |
| `Thread.Mutex.DarwinImpl.lock`, `unlock`, `tryLock` | `Thread/Mutex.zig` | 0.14.1, 0.15.2 |
| `time.Timer.start`, `read` | `time.zig` | 0.14.1, 0.15.2 |

Between the reviewed versions the allocator wrappers differ only in alignment types
(`?u29` → `?Alignment`), sentinel absorption and result-type spelling; spawn and join are
unchanged; `Thread.yield` on Windows changed, which the model already covers by keeping
`SystemCannotYield`. `std.Thread.spinLoopHint` is not a declaration in any reviewed version,
so its historical boundary name is now a rejected row.

## Caller-supplied allocator and Io

A parameter of type `std.mem.Allocator` or `std.Io` is an interface in Zig: the caller picks
the implementation. The translation replaces it by the one model (`Zig.Allocator`,
`Zig.Io`), so a theorem about the function is a theorem about callers that pass an allocator
or `Io` that behaves as that model. The generated code records this caller obligation: the
line before each `def` whose parameter contains an `Allocator` or an `Io` (directly, or through
a pointer, slice, optional, error union, struct, union or tuple) is

```lean
-- air2lean-premises: {"ALC-09":[0]}
def push (p0 : Zig.Allocator) (p1 : Option (Zig.Ptr)) (p2 : BitVec 32) : Zig.MemM (Except Zig.ErrName (Zig.Ptr)) := do
```

with the indices of those parameters. `scripts/premises.py` adds the premise
([ALC-09](premises.md#alc-09), [IOM-01](premises.md#iom-01)) to every theorem that reaches the
definition, in the source index and in the kernel-graph `compiled` derivation. Nothing else in
the generated code changes.

The model's outcomes do not include every real std implementation. For the allocator
examples, `tests/roadmap/model-inclusion` runs the same functions natively with
`std.heap.page_allocator`, `FixedBufferAllocator`, `ArenaAllocator` and `DebugAllocator`,
and the `Io` examples with `Io.Threaded` (multi- and single-threaded), and requires each native
result to be one of the model's outcomes over the allocation policies (or schedules; a native
hang must be a model deadlock). The known divergences of the
[models audit](architecture-audit/models.md) (D-ALLOC-ALIAS, D-ALLOC-REMAP, D-IO-INLINE,
D-IO-CANCEL, and D-IO-CONCURRENT, which this gate found: `global_single_threaded` makes
`Group.concurrent` return `error.ConcurrencyUnavailable`, outside the default `available`
policy) are listed in its `expected.json` as expected failures with reason and link; any other
native result outside the model fails the gate, and so does a known divergence that no longer
diverges. The model outcomes are a subset of the policies and schedules (the harness's 1 MiB
request cap and the first four failing attempts), so an inclusion is real; a native result of
an input above the cap is reported as unevaluated. `evidence.json` records each row (example,
implementation, function): runs, included, the native results, and its status.

```sh
AIR2LEAN_EXAMPLES="lists sync iogroup" AIR2LEAN_ZIG=<stock 0.16.0> scripts/diff.sh  # builds difftest
bash tests/roadmap/model-inclusion/check.sh      # writes evidence.json
python3 -B tests/roadmap/model-inclusion/inclusion.py validate   # CI: no toolchain
```

## `examples/<ex>/filter`

One name prefix per line. `scripts/check.sh` writes the AIR of every function whose name starts with `<ex>.` or with one of these prefixes (`ZIG_AIR_JSON_FILTER`, a comma list). A prefix names the instance: `array_list.Aligned(u32,null).` translates the `ArrayListUnmanaged(u32)` methods, and not the instances that std's own debug code uses. `examples/<ex>/filter-<version>` adds prefixes for one Zig version only: 0.17.0's `ArrayListUnmanaged` calls `debug.SafetyLock` (its new `pointer_stability` field), which 0.16.0's std debug code also has but the 0.16.0 translation does not call.

## Allocator model

`std.mem.Allocator` is `Zig.Allocator` (a structure without fields; 16 bytes in memory). The model is one allocator, with its state in `Zig.Mem`. Its state has no race footprint: in concurrent code the allocator is assumed thread-safe (premise [ALC-10](premises.md#alc-10), carried by every concurrent theorem); a non-thread-safe allocator shared by unordered threads is outside the model.

| Rule | |
|---|---|
| Blocks | Each allocation is a new block of kind `.heap`, with undefined bytes. |
| Failure | Allocation number `Mem.failAt` (from 0, counted in `Mem.allocs`), indices in `Mem.allocPolicy.failures`, requests above `Mem.allocPolicy.maxBytes`, requests the oracle `Mem.allocPolicy.fails` (attempt index, bytes) rejects, and requests that would exceed the live-heap `Mem.allocPolicy.budget` fail. The default has no failures and no fixed cap (`Zig.unboundedAllocBytes`); the differential harness selects the legacy 1 MiB cap (`AllocPolicy.harness`, `Zig.maxAllocBytes`) explicitly. The function returns `error.OutOfMemory`. An allocation of 0 bytes is no allocation: its pointer has no block (`Zig.zeroAllocPtr`). |
| `remap` | The default byte-remap policy fails for nonzero-size items. Explicit `Mem.allocPolicy.byteRemap` policies select in-place or moved success for a nonempty whole alignment-1 byte buffer within the request cap. In-place growth additionally requires the latest block and every historical block to end before its address. Retained byte representations are exact; grown bytes are undefined. Moved success frees the old block. Length 0 frees the slice; nonempty zero-size items can change length without allocating. `resize` is outside the recognized allocator boundary. |
| Free | For a nonzero byte count, the pointer must be the start of a live `.heap` block and the length must cover the entire block. Anything else (a double free, a free of a global or of a stack block) throws `.illegal`. `free` records the std slice poison write before freeing, including sentinel bytes, so it races with an unjoined concurrent read. `destroy` uses raw free without that poison write. Zero-byte frees do nothing. |

| Zig (`mem.Allocator.<fn>__anon_<n>`) | Lean |
|---|---|
| `create(T)` | `Zig.Allocator.create a size align` |
| `destroy(p)` | `Zig.Allocator.destroy a size p` |
| `alloc(T, n)`, `alignedAlloc(T, a, n)` | `Zig.Allocator.alloc a size align n` |
| `allocSentinel(u8, n, s)` (0.16.0 and 0.17.0) | `Zig.Allocator.allocSentinel a n s`; explicit exported `sentinel_byte` required |
| `free(s)` | `Zig.Allocator.free a size s`; `Zig.Allocator.freeSentinel a size s` for a `[:s]T` (`len + 1` items, the sentinel too) |
| `dupe(T, s)` | `Zig.Allocator.dupe a size align srcAlign s` |
| `remap(s, n)` | `Zig.Allocator.remap a size s n` |
| `realloc(s, n)` (0.16.0 only) | `Zig.Allocator.realloc a s n`; alignment-1 nonsentinel `[]u8` only |

`size` and `align` come from the call's result or argument type. `dupeZ` (and in 0.16.0 `dupeSentinel`, which it calls) is translated from its AIR (`examples/lists/filter`): it calls `alloc`. `allocSentinel(u8, n, s)` is admitted on Zig 0.16.0 and 0.17.0 when its result is a mutable byte sentinel slice with alignment 1, no packed-pointer host/offset metadata, and an explicit `sentinel_byte` in 0..255. Normalized API callers receive the same guards. The 0.16.0 and 0.17.0 exporters write that comptime value from the result pointer type as decimal text; older exports without it are rejected. It allocates `n + 1` bytes, stores `s` at checked offset `n`, and returns length `n`. The payload remains undefined and owned. Even `n = 0` allocates one byte and consumes an allocation-policy decision. ReleaseSafe `usize` addition overflow panics before allocation, matching `allocWithOptionsRetAddr`; ordinary cap/trace failures return `OutOfMemory`. Wider element types and other compiler versions remain rejected. [Byte sentinel scope and gate](../tests/roadmap/byte-sentinel/README.md) records the passed bounded kernel, fresh-source, 13-row native and overflow qualification, together with the passed ordinary slices/lists generated-source checks and remaining parent-composition/full CI checks. `realloc(s, n)` is admitted on Zig 0.16.0 for alignment-1 nonsentinel byte slices: it tries the selected byte-remap policy, then allocates `n` bytes, copies the retained prefix representation, poisons and frees the old block; failure leaves `s` unchanged. Zig 0.16.0 rejects `realloc` of a sentinel slice at compile time, so a `[:s]u8` client reallocates its absorbed `len + 1`-byte buffer and stores the sentinel at the new length (`Zig.Allocator.reallocSentinel`); a sentinel-typed realloc call is rejected. The raw vtable calls (`rawAlloc`, `rawResize`, `rawRemap`, `rawFree`) are `inline` and remain unrecognized; their model contracts and alignment/size preconditions are in `ZigLean/Sep/RawAlloc.lean`. [Sentinel reallocation scope and gate](../tests/roadmap/sentinel-realloc/README.md). Every other function of `std.mem.Allocator` is outside the subset. A `remap` of a slice with a sentinel is outside the subset.

The name of a generic instance has a number that differs between compiles (`mem.Allocator.dupeZ__anon_16959`). The translator names an instance by its content-addressed `instance_key` ([AIR JSON §Instances](air-json.md#instances)), so the Lean name is `mem_Allocator_dupeZ__anon_ad013b83a643` in every program, version and host; an instance without a key (a legacy export) gets a stable number by first use (`Air2Lean/Air/Anon.lean`, `mem_Allocator_dupeZ__anon_1`). A std model matches the generic name, whatever the suffix. A golden file of an instance is named `<name>__anon_N.json`.

`Mem.allocPolicy` is an explicit environment parameter: `maxBytes` bounds each request,
not total live bytes, and `failures` lists zero-based attempted nonzero allocations that
fail. An attempt advances `allocs` even when its size exceeds the cap. Duplicate failure
indices have no extra effect; indices beyond a finite run are unused. Every finite prefix
of an arbitrary failure trace can be selected, including several or all attempts failing.
Zero-byte allocation does not consume a decision. The model's default fresh-address policy
(address reuse is a separate opt-in parameter, [address-reuse.md](address-reuse.md)),
allocator identity, and default failure-only remap behavior are unchanged. Raising this cap
does not establish that native malloc has resources or the same address behavior.

`rawAlloc_run`, `create_run` and separation triples quantify over arbitrary `Mem`, including
every policy. `releaseAttempt_run` and `releaseAttempts_run` additionally establish an
actual returned outcome and restore the original heap after every successful allocation
or permitted failure. Their premises are positive request sizes/alignment and the existing
sequential memory invariant; they do not assume allocation success or a fixed resource cap.
The coordinator kernel-checked these definitions at `853cef53211d08a62e368739160f56dea6a3408e`;
[the policy report](allocation-policy-report.json) records the selected local profile and
remaining qualification/review gates.

The diff test runs each function with `TestAllocator` (`tests/diff/common.zig`), which has the same rules (a mirror of the model, not a std allocator; see [Caller-supplied allocator and Io](#caller-supplied-allocator-and-io) for the real-allocator check). Its first argument is the allocation that fails (legacy null/index), or
`{"fail_at": null, "failures": [0, 2], "max_bytes": 2097152}`. Missing object fields
use legacy defaults. Policy integers in the test transport are nonnegative signed-64-bit
JSON integers; semantic policy indices/caps are Lean naturals. The exact input policy is
part of the differential evidence; each result line has the number of live allocations after the call (`docs/generated-code.md` §Protocol).

The selected byte-remap policy is a bounded environment model, independent of native
allocator identity or address reuse. The Linux 0.16.0 gate in
`tests/roadmap/resize-remap` passed fresh export and translation, three exact
native/model observations (101 in-place, 201 moved, 301 failed), the ownership
module's kernel check and representation, lifetime, request-cap and frame
regressions. The initialized prefix and caller frame were preserved, and the
client released all live allocations. These results cover that bounded client
and the lemmas' explicit premises. Five targeted semantic mutations
also passed: fresh runtime builds and plain fixture elaboration succeeded, then
each execution failed at its expected assertion for length, byte representation,
old-block lifetime, failure-state preservation or address overlap. There is no
general allocator correspondence or successful `resize`/`realloc` claim; other
profiles and final composed CI remain unqualified.

## Thread model

`std.Thread.spawn`/`.join` are modelled, like the allocator. A function that reaches a sync op (an atomic op, `Thread.spawn`, `Thread.join`) is a concurrent function: it returns `Zig.ConcM Tgt α` (`ZigLean/Conc/`, `docs/generated-code.md` §Atomics and threads). Its run is a tree: it ends with a result, or it stops at a sync op and goes on from the scheduler's response. The scheduler (`Zig.Sched.run env dispatch fuel o main m0`, `ZigLean/Conc/Sched.lean`) runs all threads; they take turns only at sync ops. The environment `env : Zig.Env` is an explicit argument of every run and every concurrent theorem, with no default: `env.spawn` says whether thread assignment can fail (`available`, or `fallible`: `Thread.spawn` returns a declared error, `Group.concurrent` returns `ConcurrencyUnavailable`, and `Group.async` runs the task in the caller, within the per-caller budget `Mem.spawnLimit`), and `env.io` says which `Io` runs `Group.async` (`threaded cpus`: `Io.Threaded` with `async_limit = cpus - 1`; `any`: any implementation). A proof states the environments it covers (`Proto.spawnFails`, `run_sound`'s hypothesis). Plain code between two sync ops runs without a stop: a data race there is `.illegal`, so its order cannot change a result. `Thread.yield` and audited `std.atomic.spinLoopHint` instructions are scheduler opportunities with no fairness or progress guarantee; yield can return `error.SystemCannotYield` (`docs/progress-hints.md`). `Thread.detach` (0.16.0) is modelled (below, §Detached threads and handle ownership). `Io.futexWaitTimeout` is outside the subset and rejected at translation time (`Air2Lean/StdModels.lean`'s `stdModels`), with the reason in the error message.

| Rule | |
|---|---|
| Schedule | At each turn the oracle `o` picks one of the threads that can go on (`o i` modulo the number of options, so every `o` is a schedule). A partial-correctness spec constrains each completed result for every `o` and every `fuel`; a safety proof additionally excludes errors. Neither establishes termination or fairness. Out of fuel is `none`, as a loop that does not end. |
| `spawn(config, f, args)` | A sync op: a new thread with the target `Tgt.f args` (the program's spawn-target type, `docs/generated-code.md`), forked from the caller. It starts at its first turn with `dispatch`. In an `available` environment assignment succeeds; a `fallible` environment returns any declared spawn error (`Env.spawn`). The opt-in translation `--spawn-policy fallible` adds an explicit oracle over the declared spawn errors, honours the per-caller thread budget `Mem.spawnLimit`, and accepts only audited stack requests with a null allocator ([scope](spawn-failure.md)). `args` (the `.{...}` tuple) may have zero or multiple fields; every field is copied into the target in source order. The number and types must match the worker runtime parameters (`Check.lean`). |
| `join(handle)` | A sync op that can go on only when the thread has ended. Requires `handle` to be joined by its owner (the thread that spawned it, or the thread it was explicitly transferred to), and not already consumed (joined or detached); anything else throws `.illegal`. A thread that ends with a handle it owns and did not join or detach throws `.illegal` (`checkJoinedByChild`); the main thread's end ends the run. |
| `detach(handle)` | 0.16.0. No stop (`Zig.detachC`). The owner gives up the handle: the thread runs on, and no join of it is owed or allowed; a later join or detach throws `.illegal`. No happens-before edge. |
| Atomic op | A `pick` of the oracle (another thread can run first; the choice below), then the op in `MemM`. |
| RC11 approximation | An atomic location (`Zig.ALoc`) keeps its writes (`Zig.Msg`) in modification order; the block's bytes are the last one's. A read reads any message that is not older than one that happened before it (its clock is `≤` the reader's) or that the thread read or wrote before (`Mem.seen`); option 0 is the newest. A write goes to any place after those messages, not between an RMW and the message it read; option 0 is the end. An RMW, and a successful `cmpxchg`, reads a message with no RMW after it yet and goes right after it. A plain write to an atomic location becomes a message at the next atomic op. The limits below describe additional outcomes the approximation admits. |
| Happens-before | A vector clock per thread (`Zig.VClock`). `spawn` bumps the parent's clock and gives the child a copy; `join` merges the joined thread's clock into the caller's. An acquire read (`acquire`, `acq_rel`, `seq_cst`) adopts the message's release clock (`Msg.relClock`): the writer's clock for a release write, joined along the RMWs after it (the release sequence), empty for a relaxed write. Two accesses are concurrent when neither clock is `≤` the other. |
| Footprint | Every access (`Mem.footprint`) is a byte range, a kind (plain read/write, atomic read/write) and the clock at that time. A failed `cmpxchg` records only an atomic read; a successful one records the read and write, while remaining one scheduler operation. |
| Race check | Two concurrent accesses to the same bytes, at least one a write and at least one plain (not atomic), is a data race: `.illegal`. Two atomic accesses never race: the schedule orders them. While only the main thread can run (`Mem.solo`: it is current and every spawned thread is joined), no recorded access is concurrent with a new one, so `raceCheck` skips the scan of the footprint (MM-14, `docs/architecture-audit/memory-model.md`). Outcomes are unchanged (`raceCheck_eq_raceAt` for single-thread memories; the concurrent proofs and runtime gates check the rest); a single-thread run is linear instead of quadratic in its accesses. The footprint itself still grows with every access, and freed blocks stay in `Mem.blocks` (block ids are array indices). |

`ConcM.tryCatch` handles errors in a thread's computation. Across a sync boundary, its handler resumes from the shared memory returned by the scheduler, preserving other threads' intervening writes. Errors raised by the scheduler itself during spawn, join, wait, wake or the thread-end check terminate the run before the continuation and bypass that handler.

The orderings: `monotonic` is relaxed; `unordered` is outside the subset (it has no read-read coherence). `seq_cst` has the rule of `acq_rel`: the model has no global SC order, so it allows more results than RC11 (a proof never depends on a result that RC11 forbids), but a proof that needs the SC order (store buffering with `seq_cst`, Dekker) does not go through. `cmpxchg_weak` adds matching-value read-only failure choices; `cmpxchg_strong` retains success on a matching selected value. Failure uses the failure order, creates no message or RMW write, and may repeat forever. See `docs/weak-cas.md` for the qualified scope. **Mixed-size policy**: an atomic location is one `(block, offset, size)`; an atomic access that overlaps it with another offset or size throws `.unspecified` before it reads or writes a message (plain accesses of any size are unaffected).

**Trusted assumption** (premise [ORD-02](premises.md#ord-02), carried by every theorem with atomics): the compiled code has no load buffering, as RC11 requires (the model has no promises). LLVM does not promise this for relaxed atomics; no example depends on it. The translator rejects the load-buffering shape it can see: a relaxed read (a load, an RMW, a `cmpxchg`), then a relaxed store, RMW or `cmpxchg` to another address (field and element pointers compared by base and index) on a straight-line path (no acquire-release or sequentially consistent op, call or branch between; an acquire or a release alone does not order them; an inlined block is straight-line), unless `--assume-no-lb` assumes ORD-02 (`checkLoadBuffering`, `Air2Lean/Check.lean`; also `scripts/translate.sh --assume-no-lb`). The check is not complete (a call or a branch ends it), so ORD-02 stays a premise. An atomic op's pointee is an integer, an enum, a `bool` or a packed struct (`Io.Condition`'s state): such an op is the integer op on its bits (`Zig.Packed`; `Zig.atomicLoadAs`, `atomicStoreAs`, `atomicRmwAs`, `cmpxchgAs`), and a loaded tag value without a name of an exhaustive enum is `.illegal`. A single or many pointer pointee (`*T`, `[*]T`, `?*T`; C09, [pointer-atomics.md](pointer-atomics.md)) is a pointer op (`Zig.atomicLoadPtrAt`, `atomicStorePtrAt`, `atomicXchgPtrAt`, `cmpxchgPtrAt`, `cmpxchgWeakPtrAt`): its messages hold the pointer's bytes, which keep its block, and `cmpxchg` compares identities (block and offset); a different pointer at the same address is `.unspecified`, never a success. Only `.Xchg` is an RMW on a pointer. A `usize` from `@intFromPtr` stays an integer atomic. Float atomics, slice, C and allowzero pointer pointees are rejected, each with its reason. A `cmpxchg` (strong or weak) or an RMW `.Max`/`.Min` on an integer representation with padding bits (bit width other than `8 * @sizeOf`: `u24`, `u31`, `i40`, `enum(u24)`, a packed struct backed by `u40`) is rejected (`PADDED_ATOMIC`): Zig lowers it to an op on the whole ABI cell (`cmpxchg ptr, i64` for `u40`, on x86_64 and aarch64), so padding bits that a plain `iN` store left untouched, an RMW carry or a sign extension made nonzero make it fail (or keep the old value) natively where the model, whose padding is undefined, compares only the value bits. Loads, stores, `.Xchg` and the arithmetic/bitwise RMWs mask or only write the padding, and stay supported.

**Futex and `std.Io` (0.16.0).** `std.Io` is the model's `Zig.Io` (its `userdata` and `vtable` are not translated). The std sync primitives `Io.Mutex`, `Io.Condition`, `Io.Event`, `Io.Semaphore` (a mutex and a condition) and `Io.RwLock` (atomics on a `usize`, a mutex and a semaphore) are translated from their std code (`examples/<ex>/filter`); the futex under them is the model: `Io.futexWait`, `Io.futexWaitUncancelable` and `Io.futexWake` are sync ops (`Zig.futexWaitC`, `futexWaitCancelableC`, `futexWakeC`, `ZigLean/Conc/Call.lean`). A wait whose `u32` at the address is the expected value waits until a wake at the address; else it goes on. The kernel's compare is an atomic read of the word (`recordAccess … .atomicRead` in `Thread.futexWait`): a plain write that races with it is `.illegal`. A wake of up to `n` waiters wakes the ones that the scheduler's oracle picks (`Thread.wakeSet`, `Sched.State.chooseWake`): neither Linux nor darwin promises an order. The futex queue is in `Mem` (`Mem.waiters`, `Mem.woken`; `Thread.futexWait`, `Thread.futexWake`), as the thread table is. A wake gives no happens-before edge (the std code reads the value again with an acquire). A wait that would sleep may instead return spuriously (§Spurious wakeups and cancelation); `Io.futexWait` is also a cancelation point. `Io.futexWaitTimeout` is outside the model (it has no clock). If no thread can go on and one has not ended, the run is `Zig.Error.deadlock`. The example `sync` runs on 0.16.0 only (`examples/sync/zig-versions`).

The restricted `rwLockSnapshotPair` client holds one shared acquisition across two counter loads, releases and joins the writer before reclamation ([contract scope](rwlock-contracts.md)). Its adapter and all-fuel/all-oracle result and strict-safety proofs have passed local kernel checks; three compiled finite regressions passed for successful completion, sentinel preservation and missing-join rejection. The local Zig 0.16.0 Linux AIR/golden and translation checks passed. Native/model differential checks matched all 20 snapshot inputs and all 100 Sync inputs, with `fail_match=0`, `unspecified=0`, `capped=0` and `mismatch=0`. These bounded observations do not establish compiler correctness, general source/model correspondence, fairness or termination. The complete targeted Zig 0.16.0 Linux Sync pipeline passed, including the fresh golden/translation and native/model checks and the retained feature-prefix whole `Proofs` umbrella build. Validation of the current Outcome/public composition and final CI remains pending.

**`Io.Group` (0.16.0).** A task of a group that gets its own thread is a thread of the model (example `iogroup`), which the group records (`Mem.groups`, by the group's address); `Group.await` joins each task of the group in the order of its spawn (`Zig.groupAwaitC`). `Group.async(g, io, f, args)` promises no thread: std says the task is "not guaranteed to run until `await` or `cancel`", and `Io.Threaded` runs it in the caller once `async_limit` (default CPU count − 1) tasks are busy, always under `single_threaded`, and on allocation or `Thread.spawn` failure. So the environment picks `Group.async`'s execution (`Zig.groupAsyncWithPolicyC`, `SyncOp.asyncChoice`, `Zig.asyncOptions`) among three: under `env.io = any` all three, under `threaded cpus` a thread always and the caller once `cpus - 1` tasks may be busy (the model counts every unjoined thread, an upper bound), never deferred. The three executions are a new thread (`Zig.groupAsyncC`), the caller at once (eager; the task's captured call in the caller's `ConcM`), and deferred until the group's `await`/`cancel` (`Zig.groupDeferC`: a thread that waits at its `gate` while the group records it, `SyncOp.spawnGated`, `Mem.isGated`; its clock is the spawner's at `async`, so the model omits the edge from the awaiter, which only adds outcomes). A proof must cover every execution; a caller that waits for its task before `await` deadlocks under eager or deferred execution, as natively. The environment's choice stands for `Io.Threaded`'s own decision; a translation of `Io.Threaded` from its AIR, with only the OS primitives trusted, can replace it later. In an `available` environment `Group.concurrent` assignment succeeds; in a `fallible` one it can return `ConcurrencyUnavailable`, and a failed thread assignment of `async` runs the task in the caller ([scope and proof rules](spawn-failure.md)). `Group.cancel` requests cancelation of each task and joins it (§Spurious wakeups and cancelation). A task's args tuple supports the same zero and multiple fields as `Thread.spawn`. The thread that awaits a group must be the one that spawned its tasks (the model's `join` rule). Group support is not general async support: `Io.async`, `Future(T).await`/`.cancel` and `Io.checkCancel` are a separate 0.16.0 model with their own rejections ([futures.md](futures.md)).

**Shared reads and join-before-free.** `ZigLean/Conc/Share.lean` is a reusable contract over the footprint and clocks above. It adds no semantics. A region `R` is read-shared (`ReadShared`) when each access in it is a read that happened before some thread (a read share), or happened before every thread. Any number of threads can then read it without a race (`ReadShared.noRace_read`, `ReadShared.read`). A spawn hands the child a share (`ReadShared.fork`). After every reader is joined, its share is back, and the joiner owns the region alone (`ReadShared.reclaim`, `RegionOwned`). Only with that ownership does `std`'s poisoning `free` pass the race check (`RegionOwned.noRace`). With a read share outstanding, the poison write races and the free throws `.illegal` (`outstanding_races`, `poisonFree_outstanding`). A read after the free is a use after free (`access_freed`). Every `free` (a frame exit, `rawFree`) is a write of all the block's bytes for the race check (`Mem.freeRaces`): it throws `.illegal` if an access by another thread to the block did not happen before it (by the access's clock, by its thread's clock, or because the thread is a joined child of the freeing thread), in every schedule, also when an unordered (relaxed) handshake keeps the access before the free. The check records nothing; a later access to the dead block is `.illegal`. A proof of a free shows that it races with nothing (`free_noErr`; after the joins `Mem.ClocksLe`, `freeRaces_of_joined`). The client `groupCounter` (`Proofs/Iogroup/Counter.lean`) uses the contract for `io`, which its three tasks read-share. `groupCounter_safe` excludes races and use after free under every schedule. `groupCounter_reclaim` shows that `main` frees the block only with every task joined and every access to `io` before its clock. Kernel two-reader free checks and runtime early-free mutations of the generated client are in `tests/roadmap/shared-reclamation/Runtime.lean`. No fractional permissions, epoch/RCU, hazard-pointer or general reclamation scheme is claimed.

**Detached threads and handle ownership (C07).** `Thread.detach` consumes the handle (`Zig.Thread.detach`, `ZigLean/Mem/Thread.lean`): `std` makes any later use of it undefined ("Once called, this consumes the Thread object"), so a join or a second detach throws `.illegal`. The detached thread keeps running independently of its parent: the parent may end, and its frame's stack blocks die (`free` at the frame's exit), while the thread runs. Every access to a dead block, by any thread, throws `.illegal` (`frame_exit_kills`, `ZigLean/Conc/Detach.lean`), so a detached thread cannot read or write stack data that is gone; a proof grants a detached thread only values or regions that it owns and frees itself (`Proofs/Detach/Worker.lean`). `main`'s end ends the run, as the process exit does, whatever detached threads still run: a detached thread takes no turn after it, so an access that it could make only between `main`'s end and the real process exit is not explored (premise THR-10). A stack `free` records no access, so a detached thread's access before its creator's frame exit is not checked against the exit either. A handle has one owner (`ThreadRec.spawner`: the spawner, until a transfer). `Zig.Thread.transferHandle tid owner` (`transferHandleC`) is an explicit model step, not a `std` call: a proof or a hand-written client inserts it where a handle passes to another thread (a spawn argument or a store). Afterwards `owner` is the only thread that can join or detach the handle, and it must do so before it ends (a transfer to a thread that has already ended is not detected: that handle is then never consumed). The translator does not emit the transfer, so a translated thread that joins a handle it did not spawn stays `.illegal` (conservative: a valid Zig program that joins a handle once from another thread is rejected). A strict-safety proof orders its joins by a protocol rank (`Proto.rank`, default the thread id), so a later thread can join an earlier one (`Proofs/Detach/Transfer.lean`). Run-level witnesses are in `tests/roadmap/detached-threads/`; `Thread.detach` is qualified for Zig 0.16.0 only (its std source was reviewed for that version).

**`std.Thread` sync primitives (0.15.2).** `Thread.Mutex`, `Thread.Condition`, `Thread.ResetEvent` and `Thread.WaitGroup` are translated from their std code (example `threadsync`, 0.15.2 only). The OS boundary under them is the model:

- `Thread.Futex.wait`/`wake` are the futex sync ops (`Zig.threadFutexWaitC`, `threadFutexWakeC`), as `Io.futexWait`/`futexWake` are in 0.16.0.
- `Thread.Mutex` is other std code on each OS, so its translation differs by OS (`tests/golden/0.15.2/threadsync/Gen-darwin.lean`; `docs/generated-code.md`). On Linux it is `FutexImpl` (atomics and `Thread.Futex`). On macOS it is `DarwinImpl`, one C call of `os_unfair_lock_lock`/`unlock`/`trylock` each; the exporter does not name an `extern` function, so `Thread.Mutex.DarwinImpl.lock`/`unlock`/`tryLock` are the stop points. Their model is the lock's contract, built from the model's ops (`Zig.osUnfairLockC`, `ZigLean/Conc/Call.lean`): the word is 1 while a thread holds the lock; the lock is an acquire `cmpxchg` 0 → 1, and a thread that finds 1 sleeps at the futex; the unlock checks the owner, then is a release `xchg` of 0 (an RMW, as the C function is a release `cmpxchg` of the owner to 0) and a wake. The owner check (`Thread.unfairOwnerCheck`) is `.illegal` unless the word's newest message is the unlocking thread's and is not 0 (`Msg.writer`): an unlock by another thread, a double unlock or an unlock of a never-locked lock, which the C library answers by terminating the process. While a thread holds the lock, the newest message is its acquire, since waiters only read the word (a failed `cmpxchg`, the futex compare), so a contended lock still unlocks. `Proofs/Threadsync/Lock.lean` proves `lock` and `unlock` from this model (`docs/proofs.md`).
- `Thread.Futex.Deadline` is translated (`Thread.Condition` and `ResetEvent` wait through it); its clock (`time.Timer.start`, `time.Timer.read`, `Thread.Futex.timedWait`) is reached only with a timeout. The model has no clock, so a call is `.unsupportedTimer` at run time (a model error distinct from `.unspecified`; the legacy diff counter still pins it at 0), not a rejection.
- 0.15.2 lowers a field read of a local struct (`b.ready` for `var b: Box`) as a load of the whole struct. The model reads the AIR as it is, so that load races with another thread's atomics on the other fields (`.illegal`), though the compiled code reads the one field. `threadsync.handoff` reads through a pointer, which 0.15.2 lowers as a field load.

**Diff test.** The Lean side of a concurrent function searches the schedules (`tests/diff/ScheduleSearch.lean`'s `searchSchedules`, at most `scheduleCap` runs including probes). It first tries a bounded FIFO of sparse oracle prefixes, then resumes depth-first enumeration for the result that the compiled Zig gave. A schedule with a data race matches any Zig result (the program is undefined; `unspecified.txt`). A search that stops at the cap without Zig's result writes `Zig.Error.capped` (pinned per input in `tests/diff/<ex>/capped.txt`, same format as `unspecified.txt`). A capped search is not a demonstrated result match: `scripts/diff.sh` accepts it only within its separately pinned count (default 0). An exhausted search with neither a match nor a data race returns the first schedule's result for comparison.

**Captured arguments.** Empty tuples become `Unit`, one field retains its scalar target type, and multiple fields become a right-associated product. Pointer fields retain pointer identity; the tuple copy does not copy the pointed-to bytes or grant ownership. In programs with an empty or multi-field capture, the generated `Tgt.spawnInit P target ghost` names the child protocol obligation for the entire capture. The generated `Tgt.captures` classifies every field, and `Zig.Conc.Capture.grant` is the per-argument obligation. Copied values add nothing, every captured pointer or slice region is handed over or shown shared, and unclassified fields cannot be discharged. Proofs explicitly split private heaps with `Owned.fork`, or justify sharing through the global invariant (for example shared atomics). Ordinary aliased writes still fail the model's race check.

Existing one-field programs keep their generated source shape and express the same child obligation through `Conc.WP.spawnC` and the protocol directly.

The checker compares types across the caller and worker's separate AIR type tables. It permits a mutable pointer to become const and a pointer with sufficient alignment to satisfy a weaker alignment. Nested pointee and aggregate field types must match exactly. Other implicit `@call` coercions require an explicit source cast before capture. Thread workers returning `void`, `noreturn`, or unsigned `u8` are supported; Group workers must return `void` or `noreturn`. Worker error unions are rejected because the std panic/error handling at the worker boundary is not yet modeled.

**Proofs over all schedules.** `Conc.Proto.run_sound` (`ZigLean/Conc/Logic.lean`): if `main` and each spawned thread keep a protocol (a global invariant and a ghost value per thread, rely–guarantee), every result of `Sched.run` under every `o` and `fuel` satisfies `main`'s post. In strict mode also no run gives an error (`run_safe`: no data race, no deadlock, also with futex waits). [docs/proofs.md](proofs.md) §Proofs over all schedules. `parallelCounter n` gives `4 * n` under every schedule, and no run of it gives an error (`Proofs/Threads/Counter.lean`); the same for the `sync`, `iogroup` and `threadsync` examples over the translated std sync primitives ([docs/proofs.md](proofs.md) §Proved examples).

**Write events, not values.** Each atomic write is a message with its own id, clock, release clock and RMW edge, so equal values stay distinct in modification order. A plain write to an atomic location becomes a message at the next atomic op whenever it did not happen before the newest message (`Zig.plainSince`), whatever value it wrote; it has no release clock, so it ends release sequences. Proof invariants carry this as `PlainLe` (every plain write to the location happened before its newest message).

**Known limit (read views across synchronization)**: `Mem.seen` records only each thread's own observations; release/acquire transfers clocks, but does not transfer those observed messages to the acquiring thread. With initially zero `x` and `y`, three parallel threads can therefore run: A stores `x := 1` relaxed; B reads `x = 1` relaxed and stores `y := 1` release; C reads `y = 1` acquire and then reads `x = 0` relaxed. B's read happens before C's read, so RC11 read-read coherence forbids the final zero. The model can allow it because B's relaxed read did not acquire A's writer clock, and C has no own observation of `x`. Proofs about this model must cover that additional atomic outcome; they cannot rely on read-read coherence transferred through another location's release/acquire.

**Known limit (fairness)**: RC11 has no progress rule, so a retry loop (a `cmpxchg` loop, a spin-wait) can read the same old message at every turn; such a run ends only at the scheduler's fuel, with no result (as a loop that does not end). A proof of "`run o = .ok v` → `P v`" is not affected; the diff test's search finds the schedule that real hardware took.

**Known limit**: a spin-wait on a flag that another thread sets goes on for every turn of the scheduler in which the other thread does not run: the search reaches a schedule that sets the flag, but a spin-wait without an atomic op in its loop never stops, and `Zig.loop` returns `none` for it.

## Spurious wakeups and cancelation

C05. Each row is the outcome set the model permits for one API, with the Zig 0.16.0 source
(`lib/std/...` of the 0.16.0 source tree) that permits it. A proof over all schedules covers
every row; a client that needs a predicate must recheck it.

| API | Permitted outcomes in the model | std source |
|---|---|---|
| `Io.futexWait`, `Io.futexWaitUncancelable` (0.16.0), `Thread.Futex.wait` (0.14.1, 0.15.2) | value differs: return; woken: return; value matches: sleep until a wake, or return spuriously in place of the sleep (`Sched.spuriousWake`, option 1 of a two-way oracle choice). No happens-before edge on any return. | `Io.zig:1540-1549` ("a spurious ("random") wakeup occurs ... The caller is responsible for identifying spurious wakeups"); `Io/Threaded.zig:1022`, `1051`, `1096` (`EINTR`: "spurious wake") |
| `Io.futexWait` (cancelable) | as above, and: a request pending at the call returns `error.Canceled` at once (`Syscall.start`); a request that arrives while it waits wakes it, and it returns `error.Canceled` or `ok` with the request left pending (oracle). | `Io.zig:1552`; `Io/Threaded.zig:1347-1364` (`.canceling => return error.Canceled`), `1368-1371` (`checkCancel` after an interrupted syscall) |
| `Io.futexWaitUncancelable` | never `error.Canceled`; a cancelation request that wakes it is a spurious return. | `Io.zig:1565-1574`; `Io/Threaded.zig:932-934` |
| `Io.Condition.wait` / `waitUncancelable` | translated std code: it loops on a spurious futex return and returns after it consumed a signal or (cancelable) on `error.Canceled`. A signal can be consumed while another thread changes the predicate first, so callers recheck (`Io.Semaphore.waitUncancelable` does: `while (permits == 0)`). | `Io.zig:1668-1724` |
| `Io.Mutex.lock` (cancelable), `Io.Event.wait`, `Io.Semaphore.wait` | translated std code over the cancelable futex wait; their `error.Canceled` paths are std code. | `Io.zig:1602`, `1780`; `Io/Semaphore.zig:18-34` |
| `Io.Group.cancel` | a cancelation request for each task of the group (`Mem.cancels`; a task asleep at a futex wakes), then a join of each task. Never `error.Canceled` for the canceler. A task that ended before its request never observes it. | `Io.zig:1298-1302`; `Io/Threaded.zig:2350-2378` (`groupCancel`), `531-547` (a task that starts after the cancel sees `canceled`) |
| `Io.Group.await` | `main` (not an `Io` task) joins every task and returns `ok`. An awaiting task with a pending request delivers it before a join or after the last join, or leaves it pending (oracle: std returns `ok` when the group already finished); a delivered request before a join cancels the rest of its group, joins it and returns `error.Canceled`. | `Io.zig:1282-1286`; `Io/Threaded.zig:2291-2338` |
| `Io.checkCancel` (C08) | a pending request (from `Io.Group.cancel` or `Io.Future.cancel`) is delivered: `error.Canceled`, and the request is gone; else `ok` (`Zig.checkCancelC`, `ZigLean/Conc/Future.lean`, [futures.md](futures.md)). | `Io.zig:1356` |
| `Io.recancel`, `Io.swapCancelProtection`, `Io.sleep`, `Io.operate`, `Io.Batch.awaitAsync`, `Io.Batch.cancel` | rejected at translation time, with the reason (`Air2Lean/StdModels.lean`): no cancel protection, re-arming or clock is modelled. `Io.concurrent` and `Select` are outside the subset; `Io.async`/`Future` are the separate model of [futures.md](futures.md). | `Io.zig:1310`, `1342`, `2397`, `452`, `578`, `601` |

Only `Io` tasks are canceled: thread 0 (`main`) and `std.Thread` threads have no request
(`Thread.current` is null for them, `Io/Threaded.zig:1348`).

**Spurious wakeups.** The spurious return is taken at the wait, before the thread enters the
queue; other threads can then run before its next stop. A thread that already sleeps leaves the
queue through a wake (a spurious return after a sleep is the woken case, up to which waiter a
wake counts). The WP rule `WP.futexWaitC` (`ZigLean/Conc/Lemmas.lean`) requires the post of
the spurious return together with the invariant of the sleep, so every all-schedules proof over
a futex covers it: the std sync clients (`Proofs/Sync/*`, `Proofs/Threadsync/*`,
`Proofs/Iogroup/Counter.lean`) still prove their headline theorems, since each wait loop
rechecks. `Proofs/Cancel/Spurious.lean` has a client that waits once without a recheck and a
schedule where it reads the old value (`waitOnce_spurious`), and the rechecking client under
the same schedule (`waitLoop_spurious`).

**Cancelation.** `Proofs/Cancel/Group.lean` proves, for every oracle and fuel, that a canceled
task's result is reported as `canceled` and a completion only after all its work
(`cancelClient_spec`, `cancelClient_canceled_not_completed`), that the words handed to the task
(C01 `Owned.fork`) come back to `main` at the join of `Group.cancel` (`Owned.join`), and that no
heap byte is live when `main` returns. `Proofs/Cancel/Client.lean` reaches each of the four
results under a kernel-checked schedule. The proof is partial correctness; it does not show that
a canceled task ends (no fairness).

## Versions

The std code differs between Zig versions: 0.15.2's `growCapacity` has a loop, 0.16.0's does not. So an example with translated std code has a translation per version (`tests/golden/<version>/<ex>/Gen.lean`), and the proofs hold for each of them (CI builds `Proofs/` after `check.sh` writes that version's translation). 0.14.1 does not run `lists`: its `ArrayListUnmanaged` is a different type (`ArrayListAlignedUnmanaged`).

### Zig 0.17.0 audit

A row without explicit versions in `stdModels` covers 0.14.1, 0.15.2 and 0.16.0 (`baseZigVersions`). A later Zig is fail-closed: a row covers it only if it lists it. For 0.17.0, each modelled function's `lib/std` source was compared with 0.16.0's (stock release tarballs):

| Row | 0.17.0 | Reason |
|---|---|---|
| `mem.Allocator.create` | qualified | Now calls the inline `createAdvancedWithRetAddr(T, null, …)`: same size, alignment and result type `*T`. |
| `mem.Allocator.destroy`, `.alloc`, `.alignedAlloc`, `.dupe` | qualified | Unchanged (`allocBytesWithAlignment` is renamed `allocBytesAligned`, an internal callee). |
| `mem.Allocator.free` | qualified | Unchanged for slices. A new `*[N]T` argument form is rejected by the slice signature check. |
| `mem.Allocator.remap` | qualified | Unchanged for slices without a sentinel; the result type is now `?Slice(AbsorbSentinel(T))`, which differs only for a sentinel slice (already rejected) or the new `*[N]T` argument (rejected by the signature check). |
| `mem.Allocator.allocSentinel` | qualified | Unchanged (`allocWithOptionsRetAddr` overflow and sentinel store); the 0.17.0 exporter writes `sentinel_byte` (`Compat.v16` holds). The native byte-sentinel gate (`tests/roadmap/byte-sentinel`) still runs on 0.16.0 only. |
| `Thread.spawn`, `.join`, `.yield`, `atomic.spinLoopHint` | qualified | Unchanged (0.17.0's `Thread.zig` changes are other targets, `setName`/`getName` and `@enumFromInt` → `@fromBackingInt` on Windows). |
| `Io.futexWait`, `.futexWaitUncancelable`, `.futexWake` | qualified | `@intFromEnum` → `@backingInt` for an enum value: the same bits. |
| `Io.Group.async`, `.concurrent`, `.await`, `.cancel` | qualified | Documentation only: a task may run as late as `await`/`cancel`, which the thread model already allows. |
| `Thread.Futex.*`, `Thread.Mutex.DarwinImpl.*`, `time.Timer.*`, `Thread.spinLoopHint` | not qualified | Not in 0.16.0's or 0.17.0's std. |
| `Io.futexWaitTimeout`, `Thread.detach` | rejected | A rejection holds in every version. |

`sync`: 0.17.0's `Io.Condition.wait` (which `sync` does not call) goes through `waitTimeout`, `Io.Timeout.toDeadline` and the rejected `Io.futexWaitTimeout`, and `waitUncancelable` no longer calls `waitInner`. `examples/sync/filter-0.17.0` therefore names only `Io.Condition.signal` and `Io.Condition.waitUncancelable` (0.16.0 keeps the `Io.Condition.` prefix, `filter-0.16.0`), and the AIR goldens are per version (`tests/golden/0.16.0/sync`, `tests/golden/0.17.0/sync`). The 0.17.0 translation (`tests/golden/0.17.0/sync/Gen.lean`) inlines the uncancelable loops into `Io_Condition_waitUncancelable` (`loop22`, `loop45`); `Proofs/Sync/Semaphore.lean` and `Proofs/Sync/Handoff.lean` prove the same `condWait_spec` through either translation (`when_defined` blocks, `ZigLean/VersionGate.lean`), so every `Proofs/Sync` theorem builds against both and `sync` is selected for 0.17.0.

`mem.Allocator.dupeZ` (translated from its AIR for `lists`) is gone in 0.17.0; `examples/lists` calls `dupeSentinel(u8, xs, 0)` there. 0.17.0's `ArrayListUnmanaged` has a new `pointer_stability: debug.SafetyLock` field (8 more bytes in ReleaseSafe) whose methods `examples/lists/filter-0.17.0` translates; the AIR goldens are per version (`tests/golden/{0.15.2,0.16.0,0.17.0}/lists`, since 0.17.0 has no `dupeZ` instance to inherit). `Proofs/Lists/Append.lean` describes the header as `items`, `capacity` and `lockBytes` (an unlocked `SafetyLock` in 0.17.0, none before: 32 or 24 bytes, `Enc.size array_list_Aligned_u32_null`) and steps through 0.17.0's `assertUnlocked` in `ensureTotalCapacityPrecise`; `append_run` keeps its statement and builds against the 0.15.2, 0.16.0 and 0.17.0 translations (`tests/golden/0.17.0/lists/Gen.lean`), so `lists` is selected for 0.17.0. `threadsync` stays 0.15.2-only (`examples/threadsync/zig-versions`): it exercises 0.15.2's `std.Thread.Mutex`, `Thread.Condition` and `Thread.WaitGroup`, which 0.16.0 already removed (0.17.0 has none of them either); the `Io` primitives that replace them are covered by `sync`. New 0.17.0 std pieces are not modelled: `Io.Semaphore.waitTimeout` (a clock, like `Io.futexWaitTimeout`), `std.heap.SafeAllocator` and `std.heap.BufferFirstAllocator` (allocator implementations behind the `Allocator` vtable). The fallible spawn and `Io.Group` policies (`checkFallibleSpawnCalls`, `Air2Lean/Check.lean`) also accept 0.17.0: `Thread.spawn` and `SpawnConfig` are unchanged, and `Io.Threaded`'s `groupAsync`/`groupConcurrent`/`groupAwait`/`groupCancel` differ only by the `mutexLock` → `mutexLockUncancelable` rename (0.16.0's `mutexLock` was already uncancelable) and `@intFromEnum` → `@backingInt`.
