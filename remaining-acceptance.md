# Remaining acceptance — portable companion

All 88 IDs, order, classifications and remaining acceptance statements are retained. Counts are 37 complete, 41 partial, 0 open and 10 research. Merged bounded work does not automatically close broader acceptance. Published navigation: [roadmap](https://github.com/riventic/air2lean/blob/main/ROADMAP.md) and [this acceptance register](https://github.com/riventic/air2lean/blob/main/remaining-acceptance.md). These are the published navigation destinations. Evidence details remain in the separately reconciled handoff; this companion needs no temporary/private evidence paths.

## T01 — Explicit target and build profiles

Classification: complete.

Maintain exact-source/profile regression and release audit; wider scopes remain separate.

## T02 — Parameterized pointer and machine integer widths

Classification: partial.

a target parameter throughout pointer encoding, slices, lengths, addresses, allocation arithmetic, thread handles and layout checks. Acceptance: wasm32 and native 64-bit fixtures use their real layouts; boundary and overflow proofs hold under both profiles.

Bounded progress ([PR126](https://github.com/riventic/air2lean/pull/126)): the profile's pointer width (`Zig.PtrWidth`) parameterizes pointer and optional-pointer encoding, slices, lengths, `usize` arithmetic, addresses and allocation overflow (`ZigLean/Mem/Width.lean`; the `.w64` definitions are the 64-bit model); one source exported for wasm32-freestanding, wasm32-wasi and x86_64 uses each target's real layouts, and `PointerWidth/Proofs.lean` proves its boundary and overflow behavior under both profiles (`@mulWithOverflow`, increments, bounds checks, `alloc` overflow at 2^30 on wasm32 only, stored layouts); native layout and boundary tests run on the host and under Node's WASI, and a layout of the other width is rejected. Remaining: atomics, threads, futexes, Io, futures, vectors in memory, `@tagName`/`@errorName`, inline asm and C/allowzero pointers stay 64-bit only (rejected on wasm32), and machine integer widths other than pointers.

## T03 — Endianness support

Classification: research.

target-dependent integer, float, pointer-fragment, packed-field and aggregate byte encoding. Preserve rejection until a profile is qualified. Acceptance: encode/decode round trips and byte-sensitive differential fixtures pass on each supported endian profile.

## T04 — Architecture-specific ABI qualification

Classification: partial.

qualify aarch64-linux and aarch64-macos separately, including vector layout, unusual integer widths, f80/f128 behavior and synchronization boundaries. Acceptance: each profile has native probes, versioned expected results and proofs tied to that profile. Host exclusions cannot count as successful matches.

Bounded progress: [PR100](https://github.com/riventic/air2lean/pull/100) merged with bounded alignment and three-version controls. [PR126](https://github.com/riventic/air2lean/pull/126): aarch64-linux-gnu and aarch64-macos-none are qualified separately: native probes run only on their own host (`scripts/aarch64-abi.py`: unusual integer widths, f16 to f128 and `c_longdouble` layouts and results, f80 invalid encodings, atomic cells including u24/u40 with padding, the widest atomic, the cache line, L09 vector images), Zig 0.16.0 expected results are versioned per profile, and Lean checks with kernel-checked layout tables are tied to each file; host exclusions never count as matches. Remaining: aarch64 AIR stays outside the translator's accepted profiles (no native differential test or proof build on those hosts), only Zig 0.16.0 results are recorded, and synchronization boundaries beyond the atomic-cell probes.

## T05 — Native and WASM correspondence

Classification: research.

paired target fixtures, a precise observation relation and target-independent contracts for qualified integer/DES kernels. Specify tolerances for numerical code. Acceptance: equivalence claims distinguish exact outputs, tolerated differences and target-specific effects; no native theorem is automatically relabeled as a WASM theorem.

## T06 — Compiler backend and build-mode qualification

Classification: partial.

record the actual shipping compiler/backend/flags. Check ReleaseFast correspondence where claimed, and state the premise relating safe AIR behavior to that build. Acceptance: each supported mode has a qualification record; fast-math and other changed semantics require separate treatment.

Bounded progress ([PR120](https://github.com/riventic/air2lean/pull/120)): assurance/build-modes.json + scripts/build-modes.py check: a qualification record per optimize mode x backend pair; ReleaseSafe/llvm is qualified (probe profile and command evidence, analyzed-AIR claim with stated premises); ReleaseFast/llvm is unqualified pending native observations; fast-math and shipping-binary semantics are excluded with guard text checked in the sources. Remaining: native qualification of ReleaseFast and the other unqualified pairs (Debug, ReleaseSmall, stage2_x86_64).

## L01 — Executable full AIR coverage inventory

Classification: complete.

compare every supported compiler's tags against exporter decoding, normalization, semantic definitions, emission, tests and proof rules. Record unsupported types and constants as well. Acceptance: every tag has a named disposition. CI detects a new or renamed tag. The inventory is generated from compiler sources rather than inferred from README tables.

Completed in [PR119](https://github.com/riventic/air2lean/pull/119): Compiler-derived inventories for 0.14.1/0.15.2/0.16.0 give every AIR tag, type tag, intern key and pointer base a named disposition derived from exporter/Compat branches, normalizeOp gates, emitter dispatch and Check/Json rejections plus a reviewed override table; CI fails on new/renamed tags or any unclassified row. Semantics/proof columns remain symbol indices.

Maintain exact-source/profile regression and release audit; wider scopes remain separate.

## L02 — Integer bit operations and shift overflow

Classification: complete.

typed scalar and applicable vector semantics, emission and bitvector lemmas. Acceptance: zero, maximum values, signed/unsigned boundaries, narrow widths and shift boundaries are covered; tests exercise production-style bitset code.

Completed in [PR128](https://github.com/riventic/air2lean/pull/128): width-generic bit-operation lemmas in ZigLean/Bit.lean ([PR122](https://github.com/riventic/air2lean/pull/122): exact counts at every width, sign-boundary/all-ones counts, Log2Int validity, zero-count and shift rules, the `x & (x -% 1)` measure; runtime and checker cases for u16-u128, i128, u24, u40, i7 and vector lanes, including representable but illegal shift counts; IntegerBitSet/ArrayBitSet client proofs; operand-order mutants); tests/roadmap/bitops-native qualifies the wide cases natively: a generated corpus of wide-integer bit operations (runtime safety on) on Zig 0.14.1, 0.15.2 and 0.16.0 x x86_64-linux, aarch64-macos and aarch64-linux x 4 build modes gives native result streams equal to the Lean streams of fresh translations (31366 rows, 0 mismatches; a 408-row panic lane agrees everywhere), and Zig's shift-count safety check (`shiftRhsTooBig`) maps to `.overflow` (shift-panic regression on committed AIR for all three versions). Notes: aarch64-linux is qualified by AIR equivalence to x86_64-linux (its AIR equals the x86_64-linux AIR except `profile`); the 0.14.1 macOS AIR comes from a locally built patched compiler, not CI. Remaining: none for the wide cases.

## L03 — Loop switch and switch dispatch

Classification: partial.

preserve their control-flow meaning, target scope and captured values. Add loop invariants and termination measures where applicable. Acceptance: nested dispatch loops and legal exits translate; malformed control-flow targets are rejected.

Bounded progress ([PR124](https://github.com/riventic/air2lean/pull/124)): nested legal exits (two-level break, outer continue, inner return, inner loop result as outer selector, memory captures) translate; nested dispatches to an enclosing ordinary loop, a sibling loop-switch, itself, a non-control instruction or an absent ID, and wrong-kind/missing br/repeat targets are rejected; a loop invariant and termination measure are proved for the generated nested countdown machine (`Zig.loop_spec`). Remaining: invariants/measures are hand-written per client; unrestricted control flow is not implied.

## L04 — Pointer-form try

Classification: partial.

export and model pointer-based error-union propagation without copying or changing the addressed payload. Acceptance: success, error, aliasing and cleanup paths have differential tests and memory proof rules.

Bounded progress: Pointer try export/check/emission slice merged with qualified boundaries. [PR125](https://github.com/riventic/air2lean/pull/125): whole-union alias and cleanup memory rules (opt-in `ZigLean/Sep/TryAlias.lean`): every pointer try on one union returns the same payload address or the original error, loads/stores through it act in place without writing the tag; applied to the retained compiler-exported `writeAlias`, `cleanup` (distinct and shared counters) and `coldPayload`; two hand-written-AIR functions (`twoPaths` over one or two unions, `resetOnError` with errdefer cleanup) with proofs, runtime cases and native tests. Remaining: compiler export and native qualification of the alias fixture, concurrent aliases, overlapping unequal unions, aliases through casts or other element types, cleanup that frees the union, multi-byte payloads in generated cleanup rules, 0.14/0.15 export.

## L05 — C pointers and allowzero

Classification: partial.

explicit nullability, address-zero and access rules. Keep pointer representation distinct from the validity conditions needed for dereference. Acceptance: null tests and permitted casts translate; accesses require the right preconditions, with no invented valid allocation at address zero.

Bounded progress: Nonoptional scalar C/allowzero fragment merged. [PR125](https://github.com/riventic/air2lean/pull/125): stored C/allowzero pointers use the storage dictionary `Zig.nullablePtrEnc` (null is eight zero bytes; zero bytes read back as null, other integer or undefined bytes are `.unspecified`), also as extern/auto struct fields and array items; projections from a C/allowzero base (`struct_field_ptr`, `ptr_elem_ptr`, `ptr_add`, `ptr_sub`) are `.illegal` at address zero and keep the base's provenance; `[*c]T`/`*allowzero T` convert to and from `?*T`/`?[*]T` by explicit null mapping. Proof-only `ZigLean.Mem.NullLemmas` (lawful storage, null round trip, projected-access block); twelve hand-written AIR cases. Remaining: fresh export and native observations of the new operations; projections from address zero (including offset 0 and allowzero bases) are `.illegal` in the model even where native Zig is defined, a deliberate over-approximation that is conservative for no-illegal proofs but wrong for outcome reports and native diffs; optionals of nullable pointers, nullable pointers in unions/tuples/error-union payloads, nullable slicing, bulk memory and parent recovery.

## L06 — Constant pointer bases

Classification: partial.

resolve each supported base and offset into an explicit object/provenance model. Preserve deliberate rejection for unbacked addresses. Acceptance: nested constant slices, payload pointers and array-element pointers retain identity and offsets; invalid provenance remains an explicit error.

Bounded progress: [Global PR106](https://github.com/riventic/air2lean/pull/106) merged with bounded producer/export/generated alias/read proof and runtime controls. [PR126](https://github.com/riventic/air2lean/pull/126): nested constant bases have an explicit provenance model (`ZigLean/Mem/ConstPtr.lean`) with identity, offset, nesting, alias and disjointness lemmas; hand-written plus fresh 0.16.0 stage2_x86_64 fixtures agree, with generated-client proofs and a native x86_64 run; unbacked, comptime-only, unknown and out-of-object provenance are explicit errors. The LLVM 36/38 discrepancy is resolved as a Zig LLVM-backend `eu_payload` lowering bug (0.14.1 to 0.17.0); that shape is rejected on stage2_llvm. Remaining: 0.15.2/0.14.1 fresh exports (patched rebuilds), legacy-schema LLVM correspondence, and union-member bases.

## L07 — Aggregate and optional-pointer bitcasts

Classification: partial.

representation-based casts for arrays, structs, tuples and qualified unions, including padding/undefined bits. Extend optional-pointer conversions with explicit wrapping/unwrapping rules. Acceptance: round trips hold only under stated representation conditions; tests include padding and null values.

Bounded progress: Existing dedicated packed/optional conversions. [PR125](https://github.com/riventic/air2lean/pull/125): Zig ≤0.16 representation `@bitCast` of arrays, `extern` structs and `extern` unions (`Zig.reprCast`: encode, pad, decode; padding and unused bits undefined, so a result that needs them is `.unspecified`), with checked equal `@bitSizeOf` and a version gate (0.17+ and unversioned contexts reject); pointer-bearing repr casts are rejected (pointers and optional pointers at any depth, fail closed); `?*T` unwrap (null panics), `@intFromPtr`/`@ptrFromInt` null rules; proof-only `ZigLean.ReprCast` (round trip under the stated no-padding condition, undefined-byte throws); hand-written fixture and an aarch64-macos native probe whose defined bytes match the model. Remaining: compiler-exported fixtures, Zig 0.17's logical bit order, casts involving auto structs, tuples, tagged/packed unions, vectors, sentinel arrays or error storage.

## L08 — Packed representations and bit pointers

Classification: partial.

defined-bit masks for partial writes, broader qualified packed fields and unions, and correct host-width/bit-offset encoding. Acceptance: adjacent bits remain unchanged, undefined fields do not overwrite unrelated bits, and cross-boundary layouts are checked.

Bounded progress: [PR103](https://github.com/riventic/air2lean/pull/103) merged with bounded byte permutation controls. [PR125](https://github.com/riventic/air2lean/pull/125): bit-pointer loads and stores touch only the field's bits through defined-bit masks (`Byte.mask`, `writeField`), a store of `undefined` makes only the field's bits undefined, and `ZigLean.PackedLemmas` proves the frame; the checker compares every exported packed field pointer with the model's layout (`PACKED_LAYOUT`) and rejects bit-pointers without a packed bit size. Soundness fix: a byte-aligned field reached through a nested bit-pointer (`&reg.inner.c`) was addressed without the base's bit offset (wrong host byte); the emitter now adds it. Remaining: hand-written AIR only (no fresh export or native execution); packed unions as packed-struct fields, float and pointer fields, partly undefined packed constants, big-endian targets.

## L09 — Vector memory layouts

Classification: partial.

target-qualified lane stride, padding, packed bool addressing and element access metadata. Acceptance: memory round trips and lane writes preserve unrelated lanes; vector layout matches compiler probes.

Bounded progress ([PR122](https://github.com/riventic/air2lean/pull/122)): bit-packed `@Vector(n, uW/iW/fW)` memory layout as the LLVM backend lays it out (`Vec.packedEnc`); ZigLean/VecMem.lean proves the integer round trip at any width, LawfulEnc of the packed encodings and lane-write frames on lanes, on the image and through memory; the checker admits non-byte or ABI-padded lanes only for stage2_llvm profiles; stock Zig 0.16.0 probe images (aarch64-macos, CI x86_64-linux) match the model line for line. [PR124](https://github.com/riventic/air2lean/pull/124) (soundness fix): the exporter writes `vector_index` (lane, "runtime" or null) for every bit-pointer and the checker rejects lane pointers wherever they appear, accepting a field-less bit-pointer only as a packed `struct_field_ptr` result. [PR128](https://github.com/riventic/air2lean/pull/128): lane pointers `&v[i]` into bit-packed vectors of integer or `bool` lanes (`u3`, `u9`, `u24`, `bool`) are bit-pointers into the vector's integer (`lanePtrLayout`, `Zig.loadLane`/`Zig.storeLane`); ZigLean/VecMem.lean proves lane reads, host-only lane writes and `Vec.set` round trips for every width, count and lane; `Lanes/Proofs.lean` proves translated get/put/flip clients; `lanes.zig` passes natively and the probe matches the model on aarch64-macos and x86_64-linux; atomics and `undefined` stores through lane pointers are rejected. Remaining: other LLVM targets, the self-hosted and C backends, float (`f80`) lanes, 0.14.1/0.15.2 runtime lanes and legacy schema-11 files stay rejected.

## L10 — Error values and error layouts

Classification: partial.

standalone error encoding and target/configuration-dependent error-code layout, including `--error-limit` effects. Acceptance: error identities survive stores, loads, unions and casts on every qualified configuration.

Bounded progress: [Storage PR105](https://github.com/riventic/air2lean/pull/105) merged with bounded error-storage and declared version generation/proof/runtime controls. [PR125](https://github.com/riventic/air2lean/pull/125): the error model is parameterized by the profile's `error_set_bits` (1–32, from `--error-limit`): width-parameterized storage operations (`ZigLean/Mem/ErrWidth.lean`; the default 16 bits keeps byte-identical output), layout and capacity checks, and proof-only `ZigLean.Mem.ErrWidthLemmas` (store/load round trips, error-union laws, `@errorFromInt`/`@intFromError` over an explicit `ErrorTable`, out-of-range codes); hand-written fixtures at 8, 10, 16 and 17 bits are translated, elaborated and executed. Remaining: only 16 bits has native evidence; non-default widths have no compiler export, project workflow or ABI probe; integer/error casts stay untranslated (AIR does not export the numbering).

## L11 — Local parent pointers and constant indirect calls

Classification: complete.

parent-path recovery for local places and uniform callable-address resolution. Keep the existing direct/function-pointer call support. Acceptance: container recovery preserves aliasing; indirect dispatch covers declared targets and rejects incompatible signatures or unknown executable addresses.

Completed in [PR126](https://github.com/riventic/air2lean/pull/126): every function-pointer value resolves through one table of address-taken functions, so a call through a pointer of type `T` dispatches over exactly the declared targets of `T` whatever the pointer's origin (constant callee, global initializer, struct field, parameter, memory, integer address), and any other address or signature throws `.illegal`; `ZigLean.External.Callback` proves table completeness and incompatible-signature and unknown-address rejection, `Bridge.lean` ties them to the fresh generated dispatch, the checker rejects unknown fixed executable addresses and incompatible signatures, and dispatch mutants (dropped target, admitted unknown address, wrong target) are killed; together with PR95's local parent recovery, which keeps aliasing.

Maintain exact-source/profile regression and release audit; wider scopes remain separate.

## L12 — Globals and initialization

Classification: partial.

explicit initial-state parameters or contracts for external storage; qualified initialization and mutable-global ownership. Acceptance: generated proofs expose external initial-state assumptions and initialization order. No absent value is silently replaced with a default.

Bounded progress ([PR122](https://github.com/riventic/air2lean/pull/122)): a pointer-, union- and error-free named extern global becomes a field of a generated `ExternInit` and `mem0` takes `(ext : ExternInit)`; other externs are rejected; wholly undefined globals stay explicit undefined bytes; partly undefined global initializers, previously read as 0/false, are rejected (soundness fix); generated-client proofs over `mem0 ext`. Partly undefined constant operands are explicit undefined bytes or rejected (soundness fix). Wholly undefined stores to locals are dead stores or byte locals whose undefined bytes read as `.unspecified` ([PR124](https://github.com/riventic/air2lean/pull/124), soundness fix). Remaining: TLS, pointer-bearing externs and source/native correspondence of extern storage.

## L13 — Volatile and device effects

Classification: partial.

audit exporter metadata for volatile accesses; define observable effects, ordering and environmental changes, or reject device-facing use explicitly. Acceptance: device reads/writes cannot be treated as pure repeatable memory operations without a stated contract.

Bounded progress ([PR122](https://github.com/riventic/air2lean/pull/122)): the exporter's per-pointer `volatile` flag is audited (present on every committed pointer type for 0.14.1/0.15.2/0.16.0); the checker rejects every volatile load/store/atomic/item/memcpy/memset/pointer-state access, qualifier-dropping derivations and volatile std-model arguments with VOLATILE_ACCESS, and canonicalization no longer forwards a copy read through a volatile pointer; a model-registry binding naming the volatile parameter in its footprint is the only declared contract. Remaining: a modelled device-effect semantics (observable effects, ordering); the real-export check needs a patched compiler.

## L14 — Other compiler control and runtime features

Classification: partial.

decide which tags are meaningful at the export stage, which should be lowered first and which need new semantics. Do not claim a source feature is supported merely because one lowering works. Acceptance: each supported feature has a compiler-generated fixture; all remaining tags have explicit reasons and diagnostic guidance.

Bounded progress: PR89 merged selected runtime/control classifications. [PR125](https://github.com/riventic/air2lean/pull/125): every emitted tag either occurs in a selected compiler-generated fixture (goldens or reviewed `COMPILER_FIXTURE_ROOTS` exports) or is `emitted-unfixtured` with a reviewed `FIXTURE_REQUESTS` candidate; every rejected tag carries the translator's reason and guidance (`runtimeTagReason?`, `exporterTagReason?`, `optimizedFloatGuidance`); every roadmap AIR directory is classified compiler or non-compiler evidence; `coverage.py l14` gates it offline. Remaining: 29/34/65 emitted tags (0.16.0/0.15.2/0.14.1) still lack a compiler fixture (`runtime_tags.zig` requests are unexported); a fixture is one lowering, not universal tag semantics.

## C01 — General spawn argument tuples

Classification: partial.

zero-argument and multi-argument targets, with per-argument value copying and pointer ownership transfer. Acceptance: mixed value/pointer tuples dispatch correctly and their ownership obligations are generated.

Bounded progress ([PR122](https://github.com/riventic/air2lean/pull/122)): `Tgt.captures` is generated for empty or multi-field captures and classifies every captured field from its AIR type as a copied value, pointer, slice or other; ZigLean.Conc.Capture (runtime) and ZigLean.Conc.Transfer (CSL fork/join and unowned-region lemmas); the thread-tuples proofs discharge the per-argument obligations for value+pointer+atomic and value+pointer workers and prove two negative cases. Remaining: slice and other captures beyond the proved fixtures; general ownership inference.

## C02 — Thread-local storage

Classification: complete.

per-thread instances, initialization, address identity and lifetime rules. Acceptance: equal TLS names in different threads do not alias; thread creation and exit preserve TLS ownership rules.

Completed in [PR126](https://github.com/riventic/air2lean/pull/126): `threadlocal` globals with pointer-free, error-free storage are per-thread instances (`ZigLean/Mem/Tls.lean`): `main`'s instance is the global's block, every spawned thread makes its own from `tlsInit` when it starts and frees it when it ends (`ConcM.tlsThread`), and `runtime_nav_ptr` is the current thread's instance; `TlsWF.no_alias` proves that equal TLS names in different threads never alias, `tlsEnter_init` per-thread initialization, `twoCounters_spec`/`_safe` the concurrent client for every schedule, and `leaked_never_ok`/`tlsExit_dead` that thread exit ends the instance; `extern`, pointer-holding, over-aligned, volatile and constant-pointer forms are rejected. Scope: 0.16.0 and 0.15.2 exports; no thread-local destructors.

Maintain exact-source/profile regression and release audit; wider scopes remain separate.

## C03 — Yield and spin hints

Classification: complete.

map source operations to target-qualified scheduler/environment effects. Model a spin hint without assuming it guarantees progress. Acceptance: worker idle loops translate; safety proofs survive arbitrary schedules and progress claims require separate fairness premises.

Completed in [PR124](https://github.com/riventic/air2lean/pull/124): the retained 0.16.0 `progress.idle` worker loop (acquire load, `spinLoopHint`, `Thread.yield`) translates unchanged (byte-compared in CI); `idle_safe` holds for every oracle and fuel; `idle_progress` needs the explicit fairness premise `Cooperative` (THR-09); `idle_starves` exhibits a legal schedule under which the spinning, yielding worker never returns, so hints are not progress guarantees. Skipped-loop and relaxed-publication mutants race. Target qualification of the hints is in docs/progress-hints.md.

## C04 — Clocks deadlines and timeout races

Classification: complete.

explicit monotonic time observations, deadlines, timeout outcomes and wake-versus-timeout races. Distinguish monotonic duration clocks from wall-clock timestamps. Acceptance: deadline boundary, timeout, wake-before-timeout and wake-at-timeout cases have contracts and tests. Solver budget paths become provable.

Completed in [PR124](https://github.com/riventic/air2lean/pull/124): tests/roadmap/deadline-cases states deadline boundary, timeout, wake-before-timeout and wake-at-timeout as kernel/interpreter theorems over explicit awake monotonic observations, with runtime cases. The opt-in `ZigLean.Conc.TimedBudget` solver budget path has distinct monotonic timestamp, monotonic duration and wall-clock types; `*_sound` holds for every oracle, fuel, wake schedule and monotone clock, and the one liveness theorem takes an explicit clock-reaches-deadline premise. Boundary and no-recheck mutants are rejected by the soundness proofs. Scope: the selected timed interpreter; no OS clock, cancellation or native correspondence.

## C05 — Cancellation and spurious wakeups

Classification: complete.

target/API-specific cancellation and permitted spurious wake outcomes, with cleanup and ownership rules. Acceptance: callers that must recheck predicates are tested under those outcomes; cancellation cannot lose owned resources or disguise unfinished work as completion.

Completed in [PR126](https://github.com/riventic/air2lean/pull/126): every futex wait may return spuriously (`Sched.spuriousWake`) and `WP.futexWaitC` requires the post of that return, so the std sync proofs show their callers recheck predicates; `Io.Group.cancel` gives each task a request (`Mem.cancels`, waking a sleeping task) and joins it, and cancelable futex waits, `Io.Group.await` and `Io.checkCancel` deliver `error.Canceled` as the audited 0.16.0 std source does; `Proofs/Cancel/Group.lean` proves for every schedule that a canceled task either completes or reports cancelation with its unfinished work, its words return to `main` and every block is freed; other cancelable `std.Io` APIs (recancel, cancel protection, `Batch`, `sleep`, `operate`) are rejected with a reason, and client mutants (cancel as await, dropped cleanup) are rejected. Scope: `std.Io` 0.16.0; `Io.checkCancel` is shared with C08 futures.

Maintain exact-source/profile regression and release audit; wider scopes remain separate.

## C06 — Spawn failure and group fallback behavior

Classification: complete.

thread-creation failure, supported resource constraints and real API fallback behavior. Acceptance: failure leaves ownership with the caller; synchronous fallback and asynchronous success satisfy the same declared result contract where required.

Completed in [PR125](https://github.com/riventic/air2lean/pull/125): failure leaves ownership with the caller (`WP.spawnFailureRetains`: a refused spawn keeps the C01 `Capture.grant` of the generated captures, so the caller frees it); the synchronous fallback of `Group.async` and an assigned task establish the same declared post (`afterAsync_spec`, `await_spec`); a per-caller thread budget (`Mem.spawnLimit`) makes several failures in one run possible; `threadPair_spec`/`threadPair_safe` and `groupAsync_spec`/`groupAsync_safe` hold for every schedule, resource outcome and budget on the translated retained 0.16.0 export (`tests/roadmap/spawn-failure`). Scope: model proofs; no native adequacy, fairness, termination, `groupConcurrent` contract or process-wide quota.

Maintain exact-source/profile regression and release audit; wider scopes remain separate.

## C07 — Detached threads and broader join ownership

Classification: partial.

thread lifetime independent of parent return, explicit handle transfer and safe reclamation conditions. Acceptance: a detached thread cannot retain freed stack data; transferred handles have one authorized join owner.

Bounded progress ([PR126](https://github.com/riventic/air2lean/pull/126)): `Thread.detach` (0.16.0) consumes the handle (a later join or detach is `.illegal`); the detached thread runs on independently and any access to its creator's dead stack blocks is `.illegal` (`frame_exit_kills`); `transferHandleC` gives a handle one authorized join owner, and strict proofs order joins by a protocol rank (`Proofs/Detach/Worker.lean`, `Transfer.lean`); premise THR-10 records that no detached thread runs after `main` ends. Remaining: the translator never emits a handle transfer (a translated join of a handle its thread did not spawn stays `.illegal`), accesses after `main`'s end are not explored, a stack free records no access, and a transfer to an ended thread is not detected.

## C08 — Futures and general async IO

Classification: partial.

task states, await/cancel results, environment operations and ownership transfer. Qualify only the APIs selected for support. Acceptance: future completion, cancellation and error propagation have semantic rules and proof examples; group support is not reported as general async support.

Bounded progress ([PR126](https://github.com/riventic/air2lean/pull/126)): `Io.async`, `Future(T).await`/`.cancel` and `Io.checkCancel` (0.16.0) are a separate model (`ZigLean/Conc/Future.lean`, docs/futures.md): a task is a model thread that writes its result into a runtime record, await and cancel join and consume it, error unions propagate, cancel records a request observed at `Io.checkCancel`, a second await returns the stored result, an unconsumed or foreign-consumed future is `.illegal`, and the `fallible` policy covers the audited eager fallbacks; generated-code proofs for every oracle and fuel (`awaitValue_result`, `awaitError_result`, `cancelValue_result`, idempotence, kernel-checked illegal schedules); `Io.concurrent`, `Select`, `Batch`, Io operations, recancel and cancel protection are rejected with reasons, and group support is not reported as async support. Remaining: partial correctness only (no strict-mode error freedom), a `Future.cancel` request reaches only `Io.checkCancel` (programs whose tasks reach another cancelation point are rejected), only the spawner may consume a future, and no I/O environment operations.

## C09 — Pointer atomics and other atomic values

Classification: complete.

pointer values that preserve provenance through atomic messages; qualify other atomic formats separately. Acceptance: publish/read pointer examples prove visibility and lifetime; equality/CAS does not lose block identity by reducing pointers to bare integers.

Completed in [PR126](https://github.com/riventic/air2lean/pull/126): atomic ops on `*T`, `[*]T` and `?*T` are pointer ops whose messages hold the pointer's bytes with its block (`ZigLean/Mem/AtomicPtr.lean`); `cmpxchg` compares identities (block and offset), a different pointer at the same address is `.unspecified`, never a success, and only `.Xchg` is a pointer RMW; `publishRead_spec`/`publishRead_safe` prove visibility (0 or 42) and lifetime (no error; the published node is destroyed once, after the join) for every schedule (`Proofs/Atomics/PtrPublish.lean`); float, slice, C and allowzero pointer atomics are rejected with their reasons, and relaxed-publish and free-before-join mutants are rejected. Scope: 64-bit profiles; a `usize` from `@intFromPtr` stays an integer atomic.

Maintain exact-source/profile regression and release audit; wider scopes remain separate.

## C10 — Sequential consistency and unordered operations

Classification: research.

separate memory-order semantics, including a qualified SC order and the actual requirements of unordered operations. Acceptance: litmus proofs distinguish relaxed, acquire-release and SC outcomes. Stronger rules never remove an outcome permitted by the chosen target model without justification.

## C11 — Weak CAS and message precision

Classification: complete.

qualified spurious failure, explicit write-event tracking and a policy/model for mixed-size atomic accesses. Acceptance: retry loops remain correct under permitted failures; modification-order tests include repeated equal values and overlapping sizes.

Completed in [PR124](https://github.com/riventic/air2lean/pull/124): `locIdx` turns every plain write that did not happen before the newest message into its own write event (`plainSince`), so repeated equal values are distinct modification-order entries; overlapping atomic accesses of another offset or size are `.unspecified` (documented policy in docs/weak-cas.md). tests/roadmap/weak-cas/Messages.lean (kernel `decide +kernel` and runtime, in the weak-CAS gate) covers ABA values, coherent read pairs, CAS on an older equal message, release sequences through equal values and narrower/wider overlapping atomics; the qualified weak-CAS retry loops stay correct under permitted spurious failure. Proof invariants carry `PlainLe`.

## C12 — Memory-model adequacy

Classification: research.

establish a target/compiler correspondence argument for the supported subset, impose verified usage restrictions, or expand the model. Make the choice visible in proof claims. Acceptance: concurrency reports identify this premise and its qualification evidence. It must not disappear behind a general claim of race freedom.

## C13 — Termination fairness and starvation

Classification: research.

explicit scheduler and memory-progress assumptions, total-correctness rules, variants and liveness reasoning. Treat deadlock, starvation and divergence as distinct properties. Acceptance: prove a task completion or shutdown theorem under stated assumptions; bounded fuel exhaustion is not presented as evidence of termination.

## C14 — Reader writer locks and reusable synchronization contracts

Classification: partial.

Preserve the existing rwLockRead all-schedules result and strict-safety theorems. Finish exact composed snapshot-client/Outcome registry and integration qualification, then publish its bounded resource, clock, lifetime and join-before-free premises. General reusable RwLock/Condition/Event/WaitGroup contracts and further independent clients remain open; no fairness, termination or multiwriter claim.

Current closeout: the bounded snapshot-client/Outcome integration is merged in [PR104](https://github.com/riventic/air2lean/pull/104); the general reusable synchronization contracts and independent-client scope above remain incomplete.

Bounded progress: [PR104](https://github.com/riventic/air2lean/pull/104) merged with bounded snapshot-client kernel/native/integration controls. [PR125](https://github.com/riventic/air2lean/pull/125): reusable `MutexContract` and `SemContract`, a `CondContract` restricted to the `Io.Semaphore` layout and a restricted `RwContract` (`Proofs/Sync/Contracts.lean`) proved once against the translated 0.16.0 std code; two Lean model clients proved from the contracts and the `Lock.FitsOn`/`Sem.Fits` invariant interfaces, without unfolding the std code, for every fuel and oracle (`cache_spec`/`cache_safe` against `MutexContract`, `mailbox_spec`/`mailbox_safe` against `SemContract`), with compiled runtime witnesses. Remaining: a reusable RwLock contract for arbitrary readers/resources, Event/ResetEvent and WaitGroup contracts, broadcast, several condition waiters, timeouts, cancellation, fairness and native adequacy; the clients are not Zig exports.

## M01 — Multiple allocator identities and policies

Classification: partial.

allocator identity, allocation ownership and qualified policies for arenas, fixed buffers and custom allocators. Preserve their actual free/reset behavior. Acceptance: cross-allocator frees are checked where invalid; arena reset invalidates exactly its blocks; a production-style allocator client has a proof.

Bounded progress ([PR124](https://github.com/riventic/air2lean/pull/124)): blocks record their owning allocator (`.owned a`); arena and fixed-buffer policies follow the Zig 0.16 sources; cross-allocator free/destroy/remap is `.illegal`; reset/deinit end exactly the arena's blocks; a request-scoped arena session client is proved for every failure policy. Remaining: the translator does not route `std.heap` arena/fixed-buffer calls (the client is hand-written), owned blocks get fresh model addresses, growing remap fails, and custom allocators are not modelled.

## M02 — Successful resize remap and realloc

Classification: partial.

in-place success, relocated success and failure; specify preserved bytes, invalidated pointers and capacity changes. Acceptance: both successful growth paths and failure cleanup are proved and differentially tested with suitable allocators.

## M03 — General allocation failure and size policies

Classification: partial.

parameterized size/resource bounds and arbitrary permitted failure decisions, including several failures in one run. Acceptance: resource-independent safety statements quantify over permitted outcomes; large valid engine fixtures do not fail solely because of the model's fixed cap.

Bounded progress ([PR124](https://github.com/riventic/air2lean/pull/124)): `Mem.allocPolicy` adds an arbitrary failure oracle over (attempt, bytes) and an optional live-heap budget; the default has no fixed cap (the differential harness selects its 1 MiB cap explicitly); `appendEach_anyPolicy` proves a translated ArrayList append client for every policy with any number of failures in one run. Remaining: oracle/budget policies have no native differential counterpart, and large real engine fixtures are not yet exercised.

## M04 — Sentinel and lower-level allocator APIs

Classification: partial.

export required comptime parameters, extend selected allocator contracts and account for sentinel bytes during allocation, growth and free. Acceptance: sentinel invariants hold on success and failure; supported raw allocation APIs have alignment and size preconditions.

Bounded progress ([PR124](https://github.com/riventic/air2lean/pull/124)): `realloc` of alignment-1 nonsentinel `[]u8` (Zig 0.16.0) is recognized and modelled; `Triple.reallocSentinel` keeps the sentinel invariant on success and failure for every policy and remap mode, with an append client; raw vtable alloc/resize/remap/free contracts require power-of-two alignment, nonzero size and the whole live block. Remaining: other item types, alignments and versions of `realloc`; raw vtable calls are contracts only, not recognized by the translator.

## M05 — Address reuse and provenance contracts

Classification: complete.

state when proofs are address-independent; qualify address reuse, stale integer addresses and provenance recovery before generalizing. Acceptance: lifetime safety does not follow from an assumption that real allocators never reuse addresses; address-sensitive programs have separate contracts.

Completed in [PR126](https://github.com/riventic/air2lean/pull/126): lifetime safety does not assume fresh addresses: a pointer is a block id and an offset, and every liveness check uses the id; the opt-in `AllocPolicy.reuseAddr` oracle lets heap and owned blocks take a freed block's address (valid only if aligned, nonzero, below `nextAddr` and clear of live blocks), the Sep alloc rules and every triple hold under every reuse policy (`Triple.withReuse`), and use after free and double free stay `.illegal` after reuse (`ZigLean/Sep/AddrReuse.lean`); `@ptrFromInt` of an address that a dead and a live block share is `.unspecified` unless the program declares `ProvenanceMode.liveBlock` (premise ALC-08), and the memory-safety tutorial quantifies its headline client over reuse oracles and provenance modes. Scope: the model allocator; no native malloc address behavior.

Maintain exact-source/profile regression and release audit; wider scopes remain separate.

## M06 — Shared reads and reclamation proof interfaces

Classification: complete.

qualified read sharing/permissions and selected safe-reclamation rules, such as an explicit join-before-free protocol. Add more complex schemes only for a real use case. Acceptance: multiple readers can share a region under a checked contract; freeing it requires all relevant access rights to end.

Completed in [PR122](https://github.com/riventic/air2lean/pull/122): ZigLean/Conc/Share.lean is a reusable read-share contract (`ReadShared`) over footprints and vector clocks with split rules (share out, spawn hands a share, reads keep it), a join/recombination rule (after every reader is joined the joiner owns the region alone) and reclamation rules (std's poisoning free races with an outstanding read share and throws `.illegal`; a read after free is a use after free). The translated groupCounter's three Io.Group tasks read-share `io`; `groupCounter_reclaim` proves for every fuel and oracle that main frees it only after all readers joined. Kernel two-reader checks and heap/stack early-free mutants of the generated client are rejected with `.illegal`.

## F01 — Verified target profile selection

Classification: complete.

Completed in [PR117](https://github.com/riventic/air2lean/pull/117): Explicit IEEE/compiler-rt choice recorded in generated profile; every numerical theorem labeled ieee / compiler-rt@<versions> / abstract-spec (assurance/float-semantics.json), checked against the compiled dependency graph by the assumption audit (full audit: 191 labeled, none missing) and carried into schema-2 proof receipts; binary/native correspondence claims rejected. No automatic shipping-binary equivalence.

Maintain exact-source/profile regression and release audit; wider scopes remain separate.

## F02 — Transcendental specifications

Classification: research.

verified implementation models or target-qualified contracts for domain, classification, monotonicity and error bounds. State any assumed contracts explicitly. Acceptance: a real numeric client proves a useful property using a supported contract; a test FFI implementation is never treated as a kernel theorem.

## F03 — Fast math and permitted transformations

Classification: research.

define the allowed behaviors for each selected mode and flag, including NaN/inf/zero assumptions and contraction. Keep strict-mode proofs separate. Acceptance: proofs quantify over allowed transformed results or establish stronger preconditions; deleting the rejection without semantics does not count as support.

## F04 — Unspecified float cases

Classification: partial.

target-specific exact semantics or sets of allowed results where specified. Distinguish valid target variation from actual illegal behavior. Acceptance: useful proofs can tolerate permitted variation without pretending to know NaN payloads; invalid inputs remain explicit.

Bounded progress ([PR122](https://github.com/riventic/air2lean/pull/122)): ZigLean/Float/Allowed.lean: `Float.Allowed` (the exact result, or any NaN when the model's result is a NaN), `MinAllowed`/`MaxAllowed` for the f32/f64 signed-zero @min/@max case and the lifted `AllowedSpec`; the model is sound for the relation, classification/comparisons/arithmetic are payload-independent, and @intFromFloat errors stay errors on every allowed operand; clients in Proofs/Floats (isNan, clamp) and Proofs/Floatconv (toByte). Remaining: target-exact NaN payload and f80/compiler-rt variation contracts for the other operations.

## F05 — Complete version-specific f128 proofs

Classification: complete.

version/profile-specific specifications and proofs for the excluded selectors, including the compiler-rt implementation where selected. Acceptance: the full supported selector domain has an accurate theorem for each version/profile. A changed specification must reflect the implementation rather than force IEEE equality.

Completed in [PR125](https://github.com/riventic/air2lean/pull/125): `op128_spec_full` states every `f128` selector against each translation's division and `@sqrt` helpers (`op128Profile`: legacy for 0.14.1/0.15.2, v016 for 0.16.0), checked by guarded floatops runs for all three versions; `op128_eq_opSpec_of_special` gives `opSpec` for NaN, infinite or zero operands on every version (the IEEE result for `/`, `@divTrunc`, `@divFloor` and `@sqrt`); 0.16.0 deep-underflow division (`divRt016`) and 0.14/0.15 finite `@sqrt` (`sqrtF128ViaF64`) are specified by their compiler-rt ports, with IEEE agreement proved where it holds (`divRt016_eq_div_of_exp`, `divRt_eq_div_of_not_subnormal`). Scope: theorems about the model's ports; port/compiler_rt agreement is probe and diff-test evidence.

Maintain exact-source/profile regression and release audit; wider scopes remain separate.

## F06 — Practical numerical reasoning

Classification: complete.

non-NaN/finite closure, rounding bounds, range bounds, stable comparison conditions, and accumulated-error reasoning for sums, penalties and reductions. Acceptance: prove a fitness or bound calculation's stated numerical property, including its overflow/NaN conditions. Never assume float addition is associative.

Completed in [PR128](https://github.com/riventic/air2lean/pull/128): ZigLean/Float/Error.lean: non-NaN closure; relative rounding bounds `u·A + η` for `+`, `-`, `*`, `/`, `@sqrt`, `@floatCast` (exact when widening) and single-rounding `@mulAdd` on every format (f80 with `u = 2^-64`), double-rounding bounds for f16/f80 `@mulAdd`; compiler-rt bounds `fmaRt_error_f32` and `divRt_error_f128` (0.14.1/0.15.2), with the Dekker fma, f128 `__multf3` and 0.16.0 subnormal f128 division ports documented out of scope with native reproducers; NaN propagation lemmas; left-fold accumulated error applied to the translated dot product and to a fitness case study (Proofs/Floats/Fitness.lean: error bound, NaN, length-mismatch panic and threshold comparison) with a fitness differential test. Scope: correctly rounded `ieee` mode plus the two stated compiler-rt helpers.

## A01 — Assembly effects and operand coverage

Classification: complete.

explicit register, memory and observable-effect contracts before extending accepted constraints. Acceptance: writes affect the declared locations; aliases and clobbers are accounted for. Register assembly support does not imply arbitrary assembly safety.

Completed in [PR126](https://github.com/riventic/air2lean/pull/126): read-write and memory asm operands are accepted only through an explicit effect contract (premise ASM-03): the opaque `airAsmFx_<hash>` is a pure function of the register inputs and the old read-write values, and the generated wrapper holds every memory effect (alias guard, loads, call, one store per lvalue output); `incm_frame`/`setm_frame`/`swapm_frame` prove that a run changes only the declared operands, aliased `+m` operands are `.unspecified`, and a reviewed registry entry covers a `memory`-clobber barrier; 25 forms are rejected (a `memory` clobber outside the registry, early-clobber, `rm`/`g` and memory result outputs, memory inputs, writes through const pointers, two outputs to one location, clobbers of pinned registers), and wrapper mutants fail the A03 interpreter harness. Scope: x86_64 GPR families and one registry entry; register assembly support does not imply arbitrary assembly safety.

Maintain exact-source/profile regression and release audit; wider scopes remain separate.

## A02 — Instruction semantics and target expansion

Classification: research.

selected verified instruction semantics or qualified contracts; optional architecture-specific backends, including ARM, only with matching register/effect rules. Acceptance: an instruction's behavior is proved or marked as an assumption. Wrapper proofs and instruction proofs are reported separately.

## A03 — End-to-end assembly testing

Classification: complete.

test real generated wrappers and their result/memory plumbing, with an explicit executable interpretation. Retain a strict separation from proof definitions. Acceptance: mutation of operand order, result placement or wrapper stores fails a test; harness assumptions are listed and cannot enter theorem dependencies.

Completed in [PR120](https://github.com/riventic/air2lean/pull/120): Generated asm wrappers run unchanged under a test-only x86_64 interpretation bound to the translator's asm hash (tests/roadmap/asm-wrappers); operand-order, result-placement and wrapper-store mutants fail; harness assumptions AH-01..06 listed (instruction semantics hand-written from the Intel manual, not hardware-validated); audit.py keeps the harness out of theorem dependencies.

Maintain exact-source/profile regression and release audit; wider scopes remain separate.

## E01 — User-defined external function contracts

Classification: complete.

typed pre/postconditions, memory footprints, error/termination behavior and trusted/proved status, bound to an exact symbol/signature. Acceptance: a client proves its behavior from the declared contract; the report lists the contract as an assumption unless its implementation is verified.

Completed in [PR119](https://github.com/riventic/air2lean/pull/119): Exact-symbol/signature registry contracts with typed pre/post, errors, termination, effects, validated pointer/slice block footprints (Contract.Respects) and proved/assumed trust; scripts/external-contracts.py lists each used contract as an assumption unless its proved evidence kernel-checks with standard axioms only; Fill client proves frame preservation from the contract, also through the generated binding.

Maintain exact-source/profile regression and release audit; wider scopes remain separate.

## E02 — Callback and function pointer contracts

Classification: partial.

callback result, state mutation, ownership, reentrancy and cancellation rules. Handle captured context pointers explicitly. Acceptance: evaluator/observer clients can use contracts rather than translating every external callback body; unknown callbacks cannot be given empty effects.

Bounded progress ([PR122](https://github.com/riventic/air2lean/pull/122)): ZigLean.External.Callback: `CallbackContract` over an explicit context pointer with a fixed context/re-entry footprint, reentrancy and cancellation flags, a borrowed-context lifetime rule, `Contract.comap` and a dispatch model whose unknown-target arm never succeeds; forEach/evaluate clients are proved from the contract alone, a concrete callback on the E01 fill contract, and uncontracted/havoc callbacks get no effects. Remaining: binding translated function-pointer call sites to contracts; concurrent/async callbacks.

## E03 — IO operating system and foreign API boundaries

Classification: partial.

a selected environment-operation interface for handles, reads/writes, partial success, errors and cleanup. For production, start with clocks and the narrow Python/WASM boundary contracts actually used. Acceptance: environment-dependent behavior is parameterized and documented; no claim covers CPython, browser host imports or the OS without an explicit boundary.

Bounded progress ([PR122](https://github.com/riventic/air2lean/pull/122)): opt-in ZigLean.Env: `Ops` (monotonic/wall clocks, isOpen, read, write, close) over an arbitrary state with a contract for partial-write progress, enumerated errors, handle framing, close release and monotonic time (ENV-01/ENV-02); writeAllClose is proved to write all bytes or return the first error and close the handle exactly once, with a scripted-oracle instance whose wall clock runs backwards. Remaining: binding translated std I/O to the boundary; no OS/foreign interface qualification (CPython, browser host imports and the OS are not claimed).

## E04 — Model extension API

Classification: complete.

a typed registry for qualified standard-library and project models, with signature/layout checks, version/profile constraints and semantic dependencies. Acceptance: adding a model does not require scattering name tests through the pipeline; a same-name incompatible function is rejected.

Completed in [PR119](https://github.com/riventic/air2lean/pull/119): Single typed std model table (Air2Lean/StdModels.lean) consulted by Check/Emit/Memory/Diagnose/registry with per-row version qualification and ZigLean semantic dependencies; translated/project functions reusing a std name and same-name incompatible signatures are rejected; project dependencies checked (binding/qualified std/Lean ident, unique, acyclic).

Maintain exact-source/profile regression and release audit; wider scopes remain separate.

## P01 — Separation logic automation

Classification: complete.

associative/commutative normalization, frame inference, array splitting and proof-producing load/store steps. Acceptance: a mutable-array or heap client proof becomes materially shorter, while the Lean kernel checks every generated step.

Completed in [PR126](https://github.com/riventic/air2lean/pull/126): `ZigLean.Sep.Step` adds proof-producing symbolic-execution tactics (`sep_unfold`, `sep_step`, `sep_steps`, `sep_intro`, `sep_ret`, `sep_close`, `sep_split`): each load/store finds its points-to or array atom, the frame is inferred by definitional AC matching, supplied contracts apply to calls, and entailments close; every step elaborates to ordinary lemmas that the kernel checks (no axioms); re-proving `bump_spec` (11 to 4 lines), the slice `reverse_step` (64 to 52) and `Lists.reverse_step` (28 to 19) plus new step clients makes heap and array proofs materially shorter, while mutated specifications fail. Scope: no range or loop-invariant synthesis (P03).

Maintain exact-source/profile regression and release audit; wider scopes remain separate.

## P02 — Verification condition generation

Classification: complete.

compositional verification conditions for safety, functional results, memory effects and error returns. Expose unsolved obligations without inventing invariants. Acceptance: a contracted loop-free function receives complete checkable obligations; loop bodies request explicit invariants and variants.

Completed in [PR124](https://github.com/riventic/air2lean/pull/124): `#vc_extract` reflects loop-free generated `Zig.Result`/`Zig.MemM` functions into the VC AST with a kernel-checked `vc_f_source` equality and transported soundness; `vc_gen` splits a contract into tagged safety, result, memory and error obligations (the complete obligations; a wrong contract leaves a refuted goal); generated loops yield explicit "invariant + variant required" requests; recursion, unknown operations and uncontracted calls are refused with a reason; scripts/vc-report.py reports per function (CI golden). Scope: the accepted fragment of docs/vcs.md (no heap splitting; tagged-union dispatch, stack allocation, packed fields, vectors, memset/memmove and allocator calls need a supplied contract).

## P03 — Loop recursion and arithmetic tactics

Classification: partial.

invariant/measure templates, recursive induction scaffolding, arithmetic-range lemmas and proof-producing BitVec/Int/Nat conversions. Acceptance: a queue loop can be proved without unfolding unrelated runtime internals; automation reports the remaining premises.

Bounded progress ([PR120](https://github.com/riventic/air2lean/pull/120)): ZigLean/Sep/LoopTemplate.lean + loop_template?/loop_template tactics reduce a generated loop to invariant, step and exit premises; ZigLean/Range.lean zig_range discharges in-range casts and wrapping arithmetic; a linked-list queue walk is proved total without unfolding memory internals. [PR128](https://github.com/riventic/air2lean/pull/128): `rec_template` (ZigLean/RecTemplate.lean) scaffolds measure induction over generated `partial_fixpoint` groups (self and mutual recursion, memory-backed `addDown` proved total); `LoopTemplate.run` composes nested loops (a translated nested loop proved total with retained AIR and a byte-identical retranslation check); `loop_template?` suggests bounded counter measures, bound invariants and posts and reports the shapes it does not infer. Remaining: measures for recursion, signed or reset counters and ghost measures (list walks) are not inferred; side premises are never inferred; concurrent loops.

## P04 — Modular contracts and abstract data types

Classification: partial.

representation predicates and reusable contracts for selected arrays, lists, queues, maps and locks. Separate representation preservation from client functional properties. Acceptance: two clients reuse one verified container implementation; a representation-preserving change does not require rewriting every client proof.

Bounded progress ([PR122](https://github.com/riventic/air2lean/pull/122)): `Lists.SeqImpl` (a representation predicate and an abstract add contract) is instantiated for the generated linked-list `push` and `ArrayListUnmanaged(u32).append`; interface-only clients (addAll, addEvens) are proved once and reused for both containers. Remaining: queues, maps and general ADTs, other element types, removal operations.

## P05 — Total correctness interfaces

Classification: partial.

distinct total-correctness and partial-correctness interfaces, plus exact result-existence obligations and resource-bounded variants where useful. Acceptance: reports distinguish no-panic, correct-if-returned and guaranteed-return claims. A diverging program cannot satisfy a total-correctness goal vacuously.

Bounded progress: [PR111](https://github.com/riventic/air2lean/pull/111) merged: Sequential Returns/TotalTriple interface; reports classify each audited theorem as no-panic / correct-if-returned / guaranteed-return from its kernel type and reject overstated manifest goals; divergence cannot satisfy TotalTriple. [PR126](https://github.com/riventic/air2lean/pull/126): resource-bounded variants: `TotalTripleWithin B` (the loop exits within `B` body runs, `LoopRuns`) with composition and refutation rules, tight for the generated `sum` loop (`Proofs/Lists/Bounded.lean`); concurrent `ReturnsWithin B` (a scheduler budget uniform in the oracle) and `EventuallyReturnsUnder Fair` (only premise-satisfying oracles, never reported as unconditional; the C03 idle loop under THR-09); claims.py derives each head's strength and bound unit and rejects overstated or premise-conditional goals. Remaining: checking a bound's value against a manifest, bounded or conditional termination of generated concurrent programs beyond the idle-loop example, and exact result-existence obligations.

## P06 — Resource and complexity proofs

Classification: partial.

ghost counters or a qualified step/allocation cost semantics. Prove queue capacity, retained allocations and algorithmic operation bounds. Acceptance: a queue operation has a checked bound under explicit capacity premises. Do not equate model steps with measured CPU time without a separate calibration argument.

Bounded progress ([PR122](https://github.com/riventic/air2lean/pull/122)): ZigLean/Sep/Cost.lean: retained heap blocks (`Mem.liveHeap`), the allocator's request count, instrumentation lemmas for every successful load/store/create/destroy and `LoopRuns`, an exact loop-body count with exact/bound rules; Proofs/Lists/Cost.lean proves exact allocation and loop-step counts for the generated lists code and capacity-premise bounds for sum, pushAll and `ArrayListUnmanaged.append` (no allocation request with spare capacity). Counts are model counts (SEM-05), not time or native memory. Remaining: a queue-operation bound (no ring-buffer example), failing/diverging runs, concurrent cost.

## P07 — Proof-friendly and stable generation

Classification: partial.

documented stable proof interfaces, generated unfolding/step lemmas, source maps and semantic fingerprints. Preserve contracts across harmless AIR renumbering. Acceptance: adding an unrelated generic instantiation does not break downstream proof interfaces; semantic changes still invalidate affected proof checks.

Bounded progress: PR93 deterministic names and PR94 scalar stable proof API merged. [PR120](https://github.com/riventic/air2lean/pull/120): air2lean --source-map-json writes a per-function source-map sidecar bound to its Lean output; scripts/semantic-fingerprints.py computes renumbering-invariant fingerprints folded over call-graph SCCs and an invalidation checker reports exactly the changed functions, their cycles and callers. [PR126](https://github.com/riventic/air2lean/pull/126): `--proof-api` emits source-named unfolding lemmas for every function (pure, memory, concurrent, error-returning, recursive) and per-loop body/again/body-unfold/step lemmas, proved by `rfl`, `eq_def` or `Zig.loop.eq_1` and indexed by an `air2lean-proof-lemmas-v1` record; renumbering and an unrelated generic instance keep lemma names and statements while a semantic change alters only that function's; sidecar v2 carries a build-time translator revision (digests of the CLI and every imported `Air2Lean` module) that is part of every fingerprint, and I04's module keys are bound to it. Remaining: lemmas over the loop specifications beyond the step equation, and binding the runtime (`ZigLean`) revision.

## P08 — Counterexamples and proof diagnostics

Classification: partial.

map failed obligations to Zig file/line, AIR instruction and contract. Export executable failure inputs or scheduler traces when available; distinguish a counterexample from an unsolved proof. Acceptance: a failed queue or concurrency check produces a reproducible case where one exists; an automation timeout is never called a program bug.

Bounded progress ([PR120](https://github.com/riventic/air2lean/pull/120)): scripts/counterexample.py writes replayable counterexample bundles (input, full schedule prefix, violated contract, AIR candidate sites); only replayed failures are counterexamples, while timeouts, caps and fuel limits are unsolved and unreplayed failures stay candidates; a real-atomics relaxed message-passing race is localized end to end. Remaining: exact source maps, Lean goal-failure counterexamples, sequential replay without Zig.

## I01 — Zig build integration and root selection

Classification: complete.

a `zig build` integration or equivalent project command that selects roots, exports the required closure and preserves project flags. Report unreferenced requested roots. Acceptance: a real production kernel is translated from its original source without copied implementation code or a misleading empty export.

Completed in [PR126](https://github.com/riventic/air2lean/pull/126): `project.py export` goes from original Zig source to Lean: it selects the manifest roots, exports their AIR with the patched compiler using the project's verbatim flags, modules, build options and references, re-exports until the I02 dependency closure reaches a fixed point, and translates each root; unreferenced, inline-only or comptime-only requested roots, stalled closures, profile/version mismatches and changed pinned sources fail and publish nothing, so an empty or partial export is never mistaken for a translation; a `zig build` step runs it, and committed manifests for two production kernels (flow-time, pcg64) translate them from their original, SHA-256-pinned sources without copied implementation code. Scope: one patched-compiler export per Zig version; `build.zig` itself is not evaluated.

Maintain exact-source/profile regression and release audit; wider scopes remain separate.

## I02 — Dependency discovery

Classification: complete.

dependency closure over direct calls, qualified indirect targets, globals and generic instances, with model boundaries identified explicitly. Acceptance: the tool lists and exports every required dependency or reports the exact unresolved boundary.

Completed in [PR126](https://github.com/riventic/air2lean/pull/126): `scripts/dependency-closure.py` (`project.py closure`) computes each root's closure over direct calls, function values, global initializers, the comptime spawn workers of non-exported generic instances and qualified indirect targets; it classifies every target as exported, modelled (std model, registry binding, panic handler, extern initial state) or missing (exact FQN, chain from the root, filter prefix), lists each unresolvable boundary with its function and instruction, and writes the minimal `ZIG_AIR_JSON_FILTER` and a re-export command; `goldens` keeps every example's committed AIR closed and covered by its filter. Scope: the closure of exported AIR; calls inside a missing function are known once it is exported (I01 iterates to a fixed point).

Maintain exact-source/profile regression and release audit; wider scopes remain separate.

## I03 — Project configuration and support profiles

Classification: complete.

a versioned manifest for roots, targets, contracts, models, theorem goals, resource limits and allowed assumptions. Acceptance: one committed manifest reproduces translation and proof checking on another qualified machine.

Completed in [PR126](https://github.com/riventic/air2lean/pull/126): `scripts/second-machine.sh` reproduces `example-project.json` from a git bundle of the committed ref in a clean Ubuntu container (pinned elan and Lean, no caches, no Zig) and compares its check record with the host's; the committed run (`assurance/reproductions/i03-second-machine/`: a macOS arm64 host against linux/arm64 and linux/amd64 containers) is `reproduced` for both, and records of failed checks never compare as reproduced. Scope: the example manifest, translated from committed AIR.

Maintain exact-source/profile regression and release audit; wider scopes remain separate.

## I04 — Modular output and incremental checking

Classification: complete.

dependency-aware module splitting, incremental caches and deterministic interfaces, with invalidation for every semantic/profile change. Acceptance: an isolated function edit rebuilds only dependent modules; cold and warm builds produce equivalent definitions and proof status.

Completed in [PR126](https://github.com/riventic/air2lean/pull/126): `air2lean --split-modules <Module>` writes one Lean module per call group (a strongly connected component of the call graph) plus `Types`, `Dispatch` and umbrella modules and a manifest; the parts concatenate to the single-file output (checked), so proofs change only their import; `scripts/module-split.py` keys each module by its text, the profile metadata, the P07 translator revision, the semantic fingerprints of its functions and the keys of the modules it imports, and an isolated function edit invalidates only that group's module and its transitive importers (the Lake incremental demo rebuilds only those); cold and warm builds give identical definitions. Scope: keys are conservative (text and translator revision), not a semantic-equivalence claim.

Maintain exact-source/profile regression and release audit; wider scopes remain separate.

## I05 — Complete machine-readable diagnostics

Classification: complete.

collect independent blockers, stable diagnostic codes, source spans, dependency chains and JSON output. Keep fatal malformed-input errors separate from unsupported features. Acceptance: a coverage command reports every independent blocker in a project without requiring one edit-and-retry cycle per error.

Completed in [PR128](https://github.com/riventic/air2lean/pull/128): One check-only run reports every independent blocker: canonicalization of malformed input, the whole-program validator (`programIssues`) and profile validation (`BuildProfile.collect`) collect each independent violation instead of stopping at the first; schema-2 diagnostics carry exporter source spans (statement or declaration, from additive `src`/`column` exporter provenance), explicit total and per-unit caps (`--unit-diagnostic-limit`, `caps`, `capped_units`), and project-diagnostics.py validates the schema-2 protocol and spans. tests/roadmap/diagnostics-complete covers each formerly first-error boundary and, in CI, real exports whose spans point at the marked source lines. Scope: selected AIR validation; no proof or runtime outcomes.

## I06 — Verification coverage reports

Classification: partial.

per-root status for analyzed, exported, translated, compiled, differentially tested and proved; contract domain, theorem strength, assumptions and exclusions. Acceptance: a function with only a wrapper theorem or sampled tests is not counted as fully functionally verified.

Bounded progress ([PR110](https://github.com/riventic/air2lean/pull/110)): project.py coverage joins manifest roots with verified artifacts, current receipts/audits and typed diff summaries into per-root status, domain, declared vs bound strength, assumptions and exclusions; sampled tests, stale receipts and hash mismatches cannot reach functional levels. Remaining: goal binding uses proof-term dependencies, so a wrapper-statement theorem whose proof mentions the root still binds directly; analyzed/exported lack evidence sources; no end-to-end real-receipt run.

Bounded progress ([PR119](https://github.com/riventic/air2lean/pull/119)): Goals bind by statement: the conclusion of the audited kernel type (not hypotheses or proof term) must reference the generated root, and audits without statement dependencies fail closed; declared safety/partial/total strengths count only up to the strength claims.py derives from the conclusion, so a trivial `root x = root x` cannot reach functional levels. [PR128](https://github.com/riventic/air2lean/pull/128): the analyzed and exported coverage stages bind to a current I07 artifact manifest (export requires the analyzed-air profile; schema-2 receipts accepted); tests/roadmap/coverage-report/real_run.py runs the report in CI over the real translator and a real sealed receipt: `tardiness_spec` binds at derived total correctness, a wrapper theorem and sampled tests never reach a functional level, and a real manifest binds `exported` (and schema-12 analyzed AIR). Remaining: trivial-conclusion interpretation beyond derived strength; analyzed evidence and a real receipt are not yet on the same root.

## I07 — Provenance and artifact manifests

Classification: partial.

hashes for source closure, AIR, generated Lean, compiler patch, runtime semantics, toolchain and build profile, plus theorem names and dirty-tree provenance. Acceptance: a reviewer can identify exactly what was proved and detect stale generated files or proofs for another source/profile.

Bounded progress ([PR112](https://github.com/riventic/air2lean/pull/112)): Chained artifact manifest hashes source closure, compiler patch/pin, AIR, validated profile, translator, Gen.lean, runtime, toolchain, proofs, theorem names and optional receipt, with sealed dirty-tree provenance and per-link staleness/--expect checks. [PR128](https://github.com/riventic/air2lean/pull/128): a genuine receipt-chained manifest on a fresh schema-12 export (assurance/provenance: patched 0.16.0 AIR-only export, translation with profile header, proofs, schema-2 proof receipt) chains source, compiler patch, AIR, profile, translator, Gen.lean, runtime, toolchain, proofs/theorems and receipt; an optional `native` link records a stock-Zig build's identity (target, mode, cpu, compiler and binary sha256) and goes stale on another binary or compiler or a source/profile change; scripts/provenance-evidence.py checks the committed fixture offline in CI with edit-one-link regressions, `regenerate` reruns the whole chain under build-guard, and the committed receipt copy is path-redacted. Remaining: one example fixture; the native link is identity only (no binary-to-model correspondence); manifests and receipts are unauthenticated, and a committed receipt cannot be replayed once its revision is gone.

## I08 — Safe output and execution controls

Classification: partial.

atomic output publication, explicit overwrite behavior, bounded input size/depth, compiler/proof timeouts and cancellation that preserves prior verified artifacts. Acceptance: failed generation or interrupted checking cannot leave a partial file presented as a current verified artifact.

Bounded progress ([PR113](https://github.com/riventic/air2lean/pull/113)): Atomic fsync+rename/no-clobber publication with explicit overwrite policy for translate.sh, check.sh, proof receipts and project artifacts; per-stage timeouts and INT/TERM/HUP cancellation stop the stage process group and preserve prior artifacts. [PR128](https://github.com/riventic/air2lean/pull/128): `check.sh` bounds its final `lake build` and differential tests with per-stage timeouts and TERM/KILL cancellation, keeping published artifacts; the runner follows setsid-escaping descendants by sampled parent links and an `AIR2LEAN_STAGE_ID` environment marker and kills them on cancel, timeout or leader exit (exit 125). Remaining: a descendant that escapes within one sampling interval and scrubs its environment can be missed (the marker needs `ps` environments, not every macOS setup).

## I09 — Distribution and editor workflow

Classification: complete.

Completed in [PR114](https://github.com/riventic/air2lean/pull/114): Checksum-pinned build instructions with compatibility.json release metadata (compat.py check/release); doctor checks toolchains, patched Zig per version, AIR-only lock state, Docker, disk/memory (--json); scripts/clean-env.sh fresh-container first proof and --translate locked-compiler translation both recorded passing; editor/LSP docs. No prebuilt binary packages.

Maintain exact-source/profile regression and release audit; wider scopes remain separate.

## V01 — Formal AIR semantics

Classification: research.

define the supported raw/canonical AIR semantics, including memory, errors and target/profile parameters. Acceptance: the formal semantics covers the operations admitted by the checker and states explicit premises for all modeled external operations.

## V02 — Normalization and emission preservation

Classification: research.

preservation proofs or kernel-checkable translation certificates for reference rewrites, read-only-copy forwarding, control flow, escaping locals, indirect calls and generated encodings. Acceptance: each accepted translation comes with a checked relation to the formal AIR model. Sampled agreement remains an additional test layer.

## V03 — Exporter and compiler correspondence

Classification: partial.

identify those remaining trusted stages, add independent export validation, and investigate source/IR or IR/binary correspondence for the selected subset. Acceptance: the trust report distinguishes kernel-checked preservation, independently checked metadata and unverified compiler/export/backend assumptions.

Bounded progress ([PR122](https://github.com/riventic/air2lean/pull/122)): scripts/trust-report.py renders docs/trust-report.md from assurance/trust-stages.json and classifies every pipeline stage as kernel-checked, independently-checked-metadata or unverified-assumption; check fails on a stale report, a missing stage or class, an uncited premise, a missing checker/test or a check CI does not run. scripts/validate-air.py re-checks exported AIR JSON without the Lean decoder (ids, operand scoping, targets, terminators, type/global references, value-type cycles, per-version tag set); every committed golden AIR file passes. The recorded undefined-local-store gap is fixed in [PR124](https://github.com/riventic/air2lean/pull/124). Remaining: compiler/export/backend semantic preservation is unproved; decode, canonicalization, normalization, checker and emitter remain unverified assumptions.

## V04 — Theorem dependency and assumption auditing

Classification: complete.

Maintain exact-source/profile regression and release audit; wider scopes remain separate.

## V05 — Schema and whole-program validation

Classification: complete.

Maintain exact-source/profile regression and release audit; wider scopes remain separate.

## V06 — Explicit outcome taxonomy

Classification: partial.

make nondeterministic valid outcomes, undefined behavior, unsupported semantics, deadlock, divergence and test-search caps distinct in reports and contracts. Acceptance: no unsupported timer or capped schedule search is reported as proved absence of a failure; error returns stay distinct from model panics.

Bounded progress: [PR96](https://github.com/riventic/air2lean/pull/96) merged with explicit outcomes and exclusions. [PR119](https://github.com/riventic/air2lean/pull/119): scripts/outcomes.py maps typed differential observations onto one taxonomy (valid, nondeterministic_valid, error_return, panic, illegal/unspecified, unsupported_semantics, deadlock, divergence/fuel, search_cap); claims.py check --diff and project.py coverage refuse no-panic/guaranteed-return absence claims whose evidence has a capped, fuel-bounded, unsupported or unspecified outcome or a denied failure, and error returns never refuse no-panic; a Lean fixture keeps error returns apart from model failures. [PR126](https://github.com/riventic/air2lean/pull/126): unsupported timers are their own outcome: `Zig.Error.unsupportedTimer` (generated `time.Timer.start`/`.read`, `Thread.Futex.timedWait`, and the timed scheduler's no-clock, wrong-clock and unselected-timeout paths) is `unspecified_timer` in outcomes, accounting and claims, refuses no-panic/guaranteed-return with a timer-specific reason, and `claims.py check --diff` accepts only summaries bound to the current tree. Remaining: the taxonomy in contracts beyond these reports, separate from correspondence.

## Q01 — Generated program and parser fuzzing

Classification: partial.

typed Zig program generation, malformed JSON generation, reproducible seeds and failure shrinking. Include aliasing, globals, cleanup, unions, casts and nested control flow. Acceptance: failures reduce to a minimal reproducible source/input; malformed inputs fail predictably rather than reaching emitter placeholders.

Bounded progress ([PR120](https://github.com/riventic/air2lean/pull/120)): tests/roadmap/fuzz: a seeded malformed-AIR fuzzer with delta-debugging shrinking found and fixed 3 checker gaps (debug-instruction operand refs, non-pointer pointer arithmetic, array_to_slice of a non-array pointee), kept as 6 minimal regressions; 300 seeds run in CI; a typed Zig program generator runs in light mode. [PR128](https://github.com/riventic/air2lean/pull/128): the heavy Zig differential ran over seeds 0-39 (a corrupted-expectation control is rejected); the one translator bug it found (seeds 18/19/39: Sema's dead address-0 placeholders of a comptime-resolved const local, a missing memory-use flag for `@ptrFromInt` and missing `Zig.Enc` instances for global types) is fixed with regression tests/roadmap/const-locals, and all 40 seeds pass; harness bugs fixed (primitive-type name shadowing, unbounded and drifting shrinking); CI runs `--heavy` over seeds 0-2 with explicit caps. Remaining: larger seed ranges are a manual job; the generator covers a typed subset of Zig, not the whole language.

## Q02 — Property coverage and mutation expansion

Classification: partial.

coverage mapped to each register item and meaningful mutants for forwarding, layout, operand order, failure cleanup, profile selection and invariant transfer. Acceptance: a feature cannot close on positive examples alone; its negative tests and designated mutants detect the wrong behavior.

Bounded progress ([PR119](https://github.com/riventic/air2lean/pull/119)): assurance/mutation-map.json maps every register ID to negative tests and designated mutants by category; scripts/mutation-map.py check fails any complete row lacking negative tests or a designated mutant per declared category, and any unmapped mutant; in-memory Python-side mutants (tests/roadmap/mutation-map/mutants.py) are killed only by assertion failures of named regressions. The checker proves designated Lean/Zig mutants exist, not that they are killed. [PR128](https://github.com/riventic/air2lean/pull/128): assurance/mutation-kills.json records which regression (differential example or proof module) killed each mutate.sh mutant, bound to the mutation's block hash; all 33 mutate.sh mutants are killed (d/i on the linux/amd64 reference host); `check` fails a designated mutant without a current kill and CI shards `verify` their logs; mutate.sh aborts when a mutation changes no source; new negative tests for C07/C12/C14/L09/L12/L14. Remaining: negative tests and designated mutants for the remaining partial rows, and mutants beyond mutate.sh and the Python-side set.

## Q03 — Concurrent schedule exploration

Classification: partial.

separate observed-result matching from bounded outcome enumeration; replayable schedules, sound reduction techniques where proved, and explicit cap/fuel coverage. Acceptance: reports state schedules explored and limits; no capped run silently counts as demonstrated correspondence.

Bounded progress ([PR108](https://github.com/riventic/air2lean/pull/108)): Bounded Outcome FIFO/DFS enumeration and replay; differential reports publish separate observed-matching and bounded-enumeration coverage (schedules, fuel/cap/node/prefix limits, truncation, replay seeds); capped searches and truncated enumerations cannot count as correspondence (qualified=false); no reduction used. Exhaustive all-schedule correspondence and sound reduction proofs remain (research).

## Q04 — Host and skipped-case accounting

Classification: complete.

publish exact matches, host differences, undefined/unspecified cases, capped searches, skipped functions and proof exclusions separately by version/target. Acceptance: headline totals cannot include excluded cases as successful comparisons. Legacy-version support claims match the actual matrix.

Completed in [PR126](https://github.com/riventic/air2lean/pull/126): the published cross-version accounting table is assembled from the committed `diff-summary` artifacts of CI run 37747391759 (main 9f39e80): Zig 0.15.2 and 0.16.0 Linux-x86_64 rows with separate exact/host/illegal/unspecified/capped/bounded/mismatch/setup columns, skipped examples/functions and proof exclusions, headline 171,934 exact matches only; `check` and `claims --require-full-versions` pass and the tests re-check every committed table against its summaries; the macOS job uploads its own summaries (Q05). Scope: `qualified=false`, no cross-target rows, proof applicability unevaluated; the original Outcome-scope report is unchanged.

Maintain exact-source/profile regression and release audit; wider scopes remain separate.

## Q05 — Cross-target continuous integration

Classification: complete.

version/target/profile matrices for every declared supported path, including WASM execution once T02/T05 are implemented. Acceptance: platform support is backed by native execution, target probes and proof checks appropriate to that platform, not just compilation of foreign goldens.

Completed in [PR126](https://github.com/riventic/air2lean/pull/126): the 0.14.1 Linux and 0.15.2 macOS target-probe gaps are closed: the test job's 0.14.1 row and the macOS job's 0.15.2 steps run `scripts/abi-probe.py observe` against per-version contracts recorded with stock compilers, the target matrix records no gaps and CI runs `target-matrix.py check --strict`; T04's aarch64-linux-gnu and aarch64-macos-none ABI profiles are backed by native probes on their own hosts, and the macOS job uploads its differential summaries. Scope: the declared paths; WASM execution correspondence stays with T02/T05.

Maintain exact-source/profile regression and release audit; wider scopes remain separate.

## Q06 — Translation and proof performance budgets

Classification: partial.

measure parse/normalize/check/emit/proof time, peak memory, output size and warm-cache behavior on real modules. Improve lookup/indexing and modularization where measurements justify it. Acceptance: recorded workloads and budgets catch regressions; optimizations preserve definitions or carry preservation evidence.

Bounded progress ([PR116](https://github.com/riventic/air2lean/pull/116)): Real-module workload suite (7 uniform golden AIR sets with reference translations), air2lean --timing-json per-phase timing, cold/warm translate/elaborate/proof recorder with peak RSS and output hash, recorded Darwin arm64 baseline and regression gate. No measurement-driven optimization yet; budgets are reference-platform specific.

## Q07 — Compiler and model upgrade qualification

Classification: partial.

compare AIR tag/type lists, layout and float probes, std model boundaries, changed translations and theorem dependencies for every upgrade. Acceptance: an upgrade cannot expand support or change a model silently; affected proofs and target tests are rerun and documented.

Bounded progress ([PR119](https://github.com/riventic/air2lean/pull/119)): scripts/qualify-upgrade.py turns coverage.py's inventory diff into an obligation record (support-expansion reviews ranked by coverage.py's disposition vocabulary, std-model, universe and compiler-source reviews, float/layout probes, affected example translations and proof dependency audits), runs command obligations with per-obligation logs, and check fails on missing/failing results, unaccepted or evidence-free support/model reviews, edited logs or stale plans. Remaining: qualify an actual compiler/model upgrade through it and publish the record.

## Q08 — Review and release evidence

Classification: complete.

preserve review coverage, resolve confirmed findings, run release gates against one exact source/profile state and publish the results with known exclusions. Acceptance: the release record includes reproducible commands, successful gates and explicit unavailable checks; the review ledger identifies the reviewed revisions.

Completed in [PR121](https://github.com/riventic/air2lean/pull/121): the first release record, assurance/releases/25f89bbb405821b286e04ee7676bc24aa4c7e5ae.json, is published from a main push run: 259 gates passed with reproducible commands and no unavailable checks; REVIEW_COVERAGE.tsv names each reviewed revision and `release-record.py ledger` verifies it. [PR122](https://github.com/riventic/air2lean/pull/122) maps negative tests and killed pull-request-run, masked-failure and missing-reviewed-revision mutants.

## D01 — Reconcile stale milestones

Classification: complete.

Completed in [PR109](https://github.com/riventic/air2lean/pull/109): scripts/support-matrix.py generates docs/support-matrix.md and the README/PLAN version regions from committed sources; its CI check fails on stale regions or README/PLAN/ROADMAP-count/CI/CLI-help disagreement. PLAN's milestone table is historical and its open-work section names only incomplete register IDs.

Maintain exact-source/profile regression and release audit; wider scopes remain separate.

## D02 — Verify and close the current theorem inventory

Classification: complete.

build the current theorem modules for their declared version/target translations, then update T7 and related claims. Remaining scope includes C14 and F05. Acceptance: each listed theorem has a current check result and precise domain. A theorem about one step or one schedule is not labeled as a full all-schedules theorem.

Completed in [PR120](https://github.com/riventic/air2lean/pull/120): docs/theorem-inventory.md + scripts/theorem-inventory.py check: 67 listed theorems each have a scope class, precise domain and a current guarded check result per Zig version/target translation (0.16.0, 0.15.2 Linux and macOS threadsync, 0.14.1 floatops); single-step/single-schedule theorems cannot be labelled all-schedules. C14 general contracts and F05 excluded selectors remain under their own IDs.

Maintain exact-source/profile regression and release audit; wider scopes remain separate.

## D03 — Assumption and contract reference

Classification: complete.

one indexed reference for target profiles, allocator policies, thread creation, memory ordering, timers, opaque math, assembly and compiler trust; link each theorem/report to the premises it uses. Acceptance: a reader can determine what a proof means without searching every runtime module.

Completed in [PR122](https://github.com/riventic/air2lean/pull/122): every source gap of `premises.py compiled` on the real 0.16.0 audit was reviewed and closed with general resolver and implication rules (441 theorems with gaps before, 0 after); `compiled --strict` passes on the real audit and runs in CI. Negative tests and two Python mutants (hidden source gap, unmapped runtime module) are in the mutation map.

## D04 — Tutorials and supported model extension examples

Classification: complete.

tutorials for pure arithmetic, mutable arrays, generic containers, external contracts, allocation failure, concurrent clients and cross-target verification. Acceptance: each tutorial runs from a clean qualified environment and exposes the assumptions and remaining obligations.

Completed in [PR128](https://github.com/riventic/air2lean/pull/128): Seven checked tutorials (first proof, mutable arrays, generic containers, external contracts, allocation failure, concurrent clients, cross-target verification), each with a solved exercise, a negative control that must fail with its expected error and an assumptions section matching the premise index; scripts/tutorials.py lint/check in CI and scripts/clean-env.sh runs every tutorial in a clean container. The cross-target tutorial proves Threadsync `lock_spec`/`unlock_spec` target-generically (via `mutexC`); CI's macOS golden-swap step builds Proofs.Threadsync.Lock against the darwin translation, elaborates its Main and Solution there and asserts the darwin-side negative control fails. Scope: x86_64-linux and aarch64-macos translations of one client.
