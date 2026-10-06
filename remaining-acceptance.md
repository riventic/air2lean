# Remaining acceptance — portable companion

All 88 IDs, order, classifications and remaining acceptance statements are retained. Counts are 3 complete, 66 partial, 8 open and 11 research. Merged bounded work does not automatically close broader acceptance. Published navigation: [roadmap](https://github.com/riventic/air2lean/blob/main/ROADMAP.md) and [this acceptance register](https://github.com/riventic/air2lean/blob/main/remaining-acceptance.md). These are the published navigation destinations. Evidence details remain in the separately reconciled handoff; this companion needs no temporary/private evidence paths.

## T01 — Explicit target and build profiles

Classification: complete.

Maintain exact-source/profile regression and release audit; wider scopes remain separate.

## T02 — Parameterized pointer and machine integer widths

Classification: open.

a target parameter throughout pointer encoding, slices, lengths, addresses, allocation arithmetic, thread handles and layout checks. Acceptance: wasm32 and native 64-bit fixtures use their real layouts; boundary and overflow proofs hold under both profiles.

## T03 — Endianness support

Classification: research.

target-dependent integer, float, pointer-fragment, packed-field and aggregate byte encoding. Preserve rejection until a profile is qualified. Acceptance: encode/decode round trips and byte-sensitive differential fixtures pass on each supported endian profile.

## T04 — Architecture-specific ABI qualification

Classification: partial.

qualify aarch64-linux and aarch64-macos separately, including vector layout, unusual integer widths, f80/f128 behavior and synchronization boundaries. Acceptance: each profile has native probes, versioned expected results and proofs tied to that profile. Host exclusions cannot count as successful matches.

## T05 — Native and WASM correspondence

Classification: research.

paired target fixtures, a precise observation relation and target-independent contracts for qualified integer/DES kernels. Specify tolerances for numerical code. Acceptance: equivalence claims distinguish exact outputs, tolerated differences and target-specific effects; no native theorem is automatically relabeled as a WASM theorem.

## T06 — Compiler backend and build-mode qualification

Classification: partial.

record the actual shipping compiler/backend/flags. Check ReleaseFast correspondence where claimed, and state the premise relating safe AIR behavior to that build. Acceptance: each supported mode has a qualification record; fast-math and other changed semantics require separate treatment.

## L01 — Executable full AIR coverage inventory

Classification: partial.

compare every supported compiler's tags against exporter decoding, normalization, semantic definitions, emission, tests and proof rules. Record unsupported types and constants as well. Acceptance: every tag has a named disposition. CI detects a new or renamed tag. The inventory is generated from compiler sources rather than inferred from README tables.

## L02 — Integer bit operations and shift overflow

Classification: partial.

typed scalar and applicable vector semantics, emission and bitvector lemmas. Acceptance: zero, maximum values, signed/unsigned boundaries, narrow widths and shift boundaries are covered; tests exercise production-style bitset code.

## L03 — Loop switch and switch dispatch

Classification: partial.

preserve their control-flow meaning, target scope and captured values. Add loop invariants and termination measures where applicable. Acceptance: nested dispatch loops and legal exits translate; malformed control-flow targets are rejected.

## L04 — Pointer-form try

Classification: partial.

export and model pointer-based error-union propagation without copying or changing the addressed payload. Acceptance: success, error, aliasing and cleanup paths have differential tests and memory proof rules.

## L05 — C pointers and allowzero

Classification: partial.

explicit nullability, address-zero and access rules. Keep pointer representation distinct from the validity conditions needed for dereference. Acceptance: null tests and permitted casts translate; accesses require the right preconditions, with no invented valid allocation at address zero.

## L06 — Constant pointer bases

Classification: partial.

resolve each supported base and offset into an explicit object/provenance model. Preserve deliberate rejection for unbacked addresses. Acceptance: nested constant slices, payload pointers and array-element pointers retain identity and offsets; invalid provenance remains an explicit error.

## L07 — Aggregate and optional-pointer bitcasts

Classification: partial.

representation-based casts for arrays, structs, tuples and qualified unions, including padding/undefined bits. Extend optional-pointer conversions with explicit wrapping/unwrapping rules. Acceptance: round trips hold only under stated representation conditions; tests include padding and null values.

## L08 — Packed representations and bit pointers

Classification: partial.

defined-bit masks for partial writes, broader qualified packed fields and unions, and correct host-width/bit-offset encoding. Acceptance: adjacent bits remain unchanged, undefined fields do not overwrite unrelated bits, and cross-boundary layouts are checked.

## L09 — Vector memory layouts

Classification: partial.

target-qualified lane stride, padding, packed bool addressing and element access metadata. Acceptance: memory round trips and lane writes preserve unrelated lanes; vector layout matches compiler probes.

## L10 — Error values and error layouts

Classification: partial.

standalone error encoding and target/configuration-dependent error-code layout, including `--error-limit` effects. Acceptance: error identities survive stores, loads, unions and casts on every qualified configuration.

## L11 — Local parent pointers and constant indirect calls

Classification: partial.

parent-path recovery for local places and uniform callable-address resolution. Keep the existing direct/function-pointer call support. Acceptance: container recovery preserves aliasing; indirect dispatch covers declared targets and rejects incompatible signatures or unknown executable addresses.

## L12 — Globals and initialization

Classification: partial.

explicit initial-state parameters or contracts for external storage; qualified initialization and mutable-global ownership. Acceptance: generated proofs expose external initial-state assumptions and initialization order. No absent value is silently replaced with a default.

## L13 — Volatile and device effects

Classification: open.

audit exporter metadata for volatile accesses; define observable effects, ordering and environmental changes, or reject device-facing use explicitly. Acceptance: device reads/writes cannot be treated as pure repeatable memory operations without a stated contract.

## L14 — Other compiler control and runtime features

Classification: partial.

decide which tags are meaningful at the export stage, which should be lowered first and which need new semantics. Do not claim a source feature is supported merely because one lowering works. Acceptance: each supported feature has a compiler-generated fixture; all remaining tags have explicit reasons and diagnostic guidance.

## C01 — General spawn argument tuples

Classification: partial.

zero-argument and multi-argument targets, with per-argument value copying and pointer ownership transfer. Acceptance: mixed value/pointer tuples dispatch correctly and their ownership obligations are generated.

## C02 — Thread-local storage

Classification: open.

per-thread instances, initialization, address identity and lifetime rules. Acceptance: equal TLS names in different threads do not alias; thread creation and exit preserve TLS ownership rules.

## C03 — Yield and spin hints

Classification: partial.

map source operations to target-qualified scheduler/environment effects. Model a spin hint without assuming it guarantees progress. Acceptance: worker idle loops translate; safety proofs survive arbitrary schedules and progress claims require separate fairness premises.

## C04 — Clocks deadlines and timeout races

Classification: partial.

explicit monotonic time observations, deadlines, timeout outcomes and wake-versus-timeout races. Distinguish monotonic duration clocks from wall-clock timestamps. Acceptance: deadline boundary, timeout, wake-before-timeout and wake-at-timeout cases have contracts and tests. Solver budget paths become provable.

## C05 — Cancellation and spurious wakeups

Classification: open.

target/API-specific cancellation and permitted spurious wake outcomes, with cleanup and ownership rules. Acceptance: callers that must recheck predicates are tested under those outcomes; cancellation cannot lose owned resources or disguise unfinished work as completion.

## C06 — Spawn failure and group fallback behavior

Classification: partial.

thread-creation failure, supported resource constraints and real API fallback behavior. Acceptance: failure leaves ownership with the caller; synchronous fallback and asynchronous success satisfy the same declared result contract where required.

## C07 — Detached threads and broader join ownership

Classification: open.

thread lifetime independent of parent return, explicit handle transfer and safe reclamation conditions. Acceptance: a detached thread cannot retain freed stack data; transferred handles have one authorized join owner.

## C08 — Futures and general async IO

Classification: open.

task states, await/cancel results, environment operations and ownership transfer. Qualify only the APIs selected for support. Acceptance: future completion, cancellation and error propagation have semantic rules and proof examples; group support is not reported as general async support.

## C09 — Pointer atomics and other atomic values

Classification: open.

pointer values that preserve provenance through atomic messages; qualify other atomic formats separately. Acceptance: publish/read pointer examples prove visibility and lifetime; equality/CAS does not lose block identity by reducing pointers to bare integers.

## C10 — Sequential consistency and unordered operations

Classification: research.

separate memory-order semantics, including a qualified SC order and the actual requirements of unordered operations. Acceptance: litmus proofs distinguish relaxed, acquire-release and SC outcomes. Stronger rules never remove an outcome permitted by the chosen target model without justification.

## C11 — Weak CAS and message precision

Classification: partial.

qualified spurious failure, explicit write-event tracking and a policy/model for mixed-size atomic accesses. Acceptance: retry loops remain correct under permitted failures; modification-order tests include repeated equal values and overlapping sizes.

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

## M01 — Multiple allocator identities and policies

Classification: partial.

allocator identity, allocation ownership and qualified policies for arenas, fixed buffers and custom allocators. Preserve their actual free/reset behavior. Acceptance: cross-allocator frees are checked where invalid; arena reset invalidates exactly its blocks; a production-style allocator client has a proof.

## M02 — Successful resize remap and realloc

Classification: partial.

in-place success, relocated success and failure; specify preserved bytes, invalidated pointers and capacity changes. Acceptance: both successful growth paths and failure cleanup are proved and differentially tested with suitable allocators.

## M03 — General allocation failure and size policies

Classification: partial.

parameterized size/resource bounds and arbitrary permitted failure decisions, including several failures in one run. Acceptance: resource-independent safety statements quantify over permitted outcomes; large valid engine fixtures do not fail solely because of the model's fixed cap.

## M04 — Sentinel and lower-level allocator APIs

Classification: partial.

export required comptime parameters, extend selected allocator contracts and account for sentinel bytes during allocation, growth and free. Acceptance: sentinel invariants hold on success and failure; supported raw allocation APIs have alignment and size preconditions.

## M05 — Address reuse and provenance contracts

Classification: research.

state when proofs are address-independent; qualify address reuse, stale integer addresses and provenance recovery before generalizing. Acceptance: lifetime safety does not follow from an assumption that real allocators never reuse addresses; address-sensitive programs have separate contracts.

## M06 — Shared reads and reclamation proof interfaces

Classification: partial.

qualified read sharing/permissions and selected safe-reclamation rules, such as an explicit join-before-free protocol. Add more complex schemes only for a real use case. Acceptance: multiple readers can share a region under a checked contract; freeing it requires all relevant access rights to end.

## F01 — Verified target profile selection

Classification: partial.

target-driven selection or an explicit semantic choice recorded in generated code and reports; reject an unsupported binary-correspondence claim. Acceptance: every numerical theorem states whether it concerns IEEE behavior, a specific compiler-rt implementation or an abstract numerical specification.

## F02 — Transcendental specifications

Classification: research.

verified implementation models or target-qualified contracts for domain, classification, monotonicity and error bounds. State any assumed contracts explicitly. Acceptance: a real numeric client proves a useful property using a supported contract; a test FFI implementation is never treated as a kernel theorem.

## F03 — Fast math and permitted transformations

Classification: research.

define the allowed behaviors for each selected mode and flag, including NaN/inf/zero assumptions and contraction. Keep strict-mode proofs separate. Acceptance: proofs quantify over allowed transformed results or establish stronger preconditions; deleting the rejection without semantics does not count as support.

## F04 — Unspecified float cases

Classification: partial.

target-specific exact semantics or sets of allowed results where specified. Distinguish valid target variation from actual illegal behavior. Acceptance: useful proofs can tolerate permitted variation without pretending to know NaN payloads; invalid inputs remain explicit.

## F05 — Complete version-specific f128 proofs

Classification: partial.

version/profile-specific specifications and proofs for the excluded selectors, including the compiler-rt implementation where selected. Acceptance: the full supported selector domain has an accurate theorem for each version/profile. A changed specification must reflect the implementation rather than force IEEE equality.

## F06 — Practical numerical reasoning

Classification: partial.

non-NaN/finite closure, rounding bounds, range bounds, stable comparison conditions, and accumulated-error reasoning for sums, penalties and reductions. Acceptance: prove a fitness or bound calculation's stated numerical property, including its overflow/NaN conditions. Never assume float addition is associative.

## A01 — Assembly effects and operand coverage

Classification: partial.

explicit register, memory and observable-effect contracts before extending accepted constraints. Acceptance: writes affect the declared locations; aliases and clobbers are accounted for. Register assembly support does not imply arbitrary assembly safety.

## A02 — Instruction semantics and target expansion

Classification: research.

selected verified instruction semantics or qualified contracts; optional architecture-specific backends, including ARM, only with matching register/effect rules. Acceptance: an instruction's behavior is proved or marked as an assumption. Wrapper proofs and instruction proofs are reported separately.

## A03 — End-to-end assembly testing

Classification: partial.

test real generated wrappers and their result/memory plumbing, with an explicit executable interpretation. Retain a strict separation from proof definitions. Acceptance: mutation of operand order, result placement or wrapper stores fails a test; harness assumptions are listed and cannot enter theorem dependencies.

## E01 — User-defined external function contracts

Classification: partial.

typed pre/postconditions, memory footprints, error/termination behavior and trusted/proved status, bound to an exact symbol/signature. Acceptance: a client proves its behavior from the declared contract; the report lists the contract as an assumption unless its implementation is verified.

## E02 — Callback and function pointer contracts

Classification: partial.

callback result, state mutation, ownership, reentrancy and cancellation rules. Handle captured context pointers explicitly. Acceptance: evaluator/observer clients can use contracts rather than translating every external callback body; unknown callbacks cannot be given empty effects.

## E03 — IO operating system and foreign API boundaries

Classification: partial.

a selected environment-operation interface for handles, reads/writes, partial success, errors and cleanup. For production, start with clocks and the narrow Python/WASM boundary contracts actually used. Acceptance: environment-dependent behavior is parameterized and documented; no claim covers CPython, browser host imports or the OS without an explicit boundary.

## E04 — Model extension API

Classification: partial.

a typed registry for qualified standard-library and project models, with signature/layout checks, version/profile constraints and semantic dependencies. Acceptance: adding a model does not require scattering name tests through the pipeline; a same-name incompatible function is rejected.

## P01 — Separation logic automation

Classification: partial.

associative/commutative normalization, frame inference, array splitting and proof-producing load/store steps. Acceptance: a mutable-array or heap client proof becomes materially shorter, while the Lean kernel checks every generated step.

## P02 — Verification condition generation

Classification: partial.

compositional verification conditions for safety, functional results, memory effects and error returns. Expose unsolved obligations without inventing invariants. Acceptance: a contracted loop-free function receives complete checkable obligations; loop bodies request explicit invariants and variants.

## P03 — Loop recursion and arithmetic tactics

Classification: partial.

invariant/measure templates, recursive induction scaffolding, arithmetic-range lemmas and proof-producing BitVec/Int/Nat conversions. Acceptance: a queue loop can be proved without unfolding unrelated runtime internals; automation reports the remaining premises.

## P04 — Modular contracts and abstract data types

Classification: partial.

representation predicates and reusable contracts for selected arrays, lists, queues, maps and locks. Separate representation preservation from client functional properties. Acceptance: two clients reuse one verified container implementation; a representation-preserving change does not require rewriting every client proof.

## P05 — Total correctness interfaces

Classification: partial.

distinct total-correctness and partial-correctness interfaces, plus exact result-existence obligations and resource-bounded variants where useful. Acceptance: reports distinguish no-panic, correct-if-returned and guaranteed-return claims. A diverging program cannot satisfy a total-correctness goal vacuously.

## P06 — Resource and complexity proofs

Classification: open.

ghost counters or a qualified step/allocation cost semantics. Prove queue capacity, retained allocations and algorithmic operation bounds. Acceptance: a queue operation has a checked bound under explicit capacity premises. Do not equate model steps with measured CPU time without a separate calibration argument.

## P07 — Proof-friendly and stable generation

Classification: partial.

documented stable proof interfaces, generated unfolding/step lemmas, source maps and semantic fingerprints. Preserve contracts across harmless AIR renumbering. Acceptance: adding an unrelated generic instantiation does not break downstream proof interfaces; semantic changes still invalidate affected proof checks.

## P08 — Counterexamples and proof diagnostics

Classification: partial.

map failed obligations to Zig file/line, AIR instruction and contract. Export executable failure inputs or scheduler traces when available; distinguish a counterexample from an unsolved proof. Acceptance: a failed queue or concurrency check produces a reproducible case where one exists; an automation timeout is never called a program bug.

## I01 — Zig build integration and root selection

Classification: partial.

a `zig build` integration or equivalent project command that selects roots, exports the required closure and preserves project flags. Report unreferenced requested roots. Acceptance: a real production kernel is translated from its original source without copied implementation code or a misleading empty export.

## I02 — Dependency discovery

Classification: partial.

dependency closure over direct calls, qualified indirect targets, globals and generic instances, with model boundaries identified explicitly. Acceptance: the tool lists and exports every required dependency or reports the exact unresolved boundary.

## I03 — Project configuration and support profiles

Classification: partial.

a versioned manifest for roots, targets, contracts, models, theorem goals, resource limits and allowed assumptions. Acceptance: one committed manifest reproduces translation and proof checking on another qualified machine.

## I04 — Modular output and incremental checking

Classification: partial.

dependency-aware module splitting, incremental caches and deterministic interfaces, with invalidation for every semantic/profile change. Acceptance: an isolated function edit rebuilds only dependent modules; cold and warm builds produce equivalent definitions and proof status.

## I05 — Complete machine-readable diagnostics

Classification: partial.

collect independent blockers, stable diagnostic codes, source spans, dependency chains and JSON output. Keep fatal malformed-input errors separate from unsupported features. Acceptance: a coverage command reports every independent blocker in a project without requiring one edit-and-retry cycle per error.

## I06 — Verification coverage reports

Classification: partial.

per-root status for analyzed, exported, translated, compiled, differentially tested and proved; contract domain, theorem strength, assumptions and exclusions. Acceptance: a function with only a wrapper theorem or sampled tests is not counted as fully functionally verified.

## I07 — Provenance and artifact manifests

Classification: partial.

hashes for source closure, AIR, generated Lean, compiler patch, runtime semantics, toolchain and build profile, plus theorem names and dirty-tree provenance. Acceptance: a reviewer can identify exactly what was proved and detect stale generated files or proofs for another source/profile.

## I08 — Safe output and execution controls

Classification: partial.

atomic output publication, explicit overwrite behavior, bounded input size/depth, compiler/proof timeouts and cancellation that preserves prior verified artifacts. Acceptance: failed generation or interrupted checking cannot leave a partial file presented as a current verified artifact.

## I09 — Distribution and editor workflow

Classification: partial.

reproducible checksum-verified packages or build instructions, a dependency/target doctor command, release compatibility metadata and optional editor diagnostics. Acceptance: a clean supported environment can run a small complete proof without undocumented local state. Preserve the AIR-only compiler lock when LLVM is absent.

## V01 — Formal AIR semantics

Classification: research.

define the supported raw/canonical AIR semantics, including memory, errors and target/profile parameters. Acceptance: the formal semantics covers the operations admitted by the checker and states explicit premises for all modeled external operations.

## V02 — Normalization and emission preservation

Classification: research.

preservation proofs or kernel-checkable translation certificates for reference rewrites, read-only-copy forwarding, control flow, escaping locals, indirect calls and generated encodings. Acceptance: each accepted translation comes with a checked relation to the formal AIR model. Sampled agreement remains an additional test layer.

## V03 — Exporter and compiler correspondence

Classification: partial.

identify those remaining trusted stages, add independent export validation, and investigate source/IR or IR/binary correspondence for the selected subset. Acceptance: the trust report distinguishes kernel-checked preservation, independently checked metadata and unverified compiler/export/backend assumptions.

## V04 — Theorem dependency and assumption auditing

Classification: complete.

Maintain exact-source/profile regression and release audit; wider scopes remain separate.

## V05 — Schema and whole-program validation

Classification: complete.

Maintain exact-source/profile regression and release audit; wider scopes remain separate.

## V06 — Explicit outcome taxonomy

Classification: partial.

make nondeterministic valid outcomes, undefined behavior, unsupported semantics, deadlock, divergence and test-search caps distinct in reports and contracts. Acceptance: no unsupported timer or capped schedule search is reported as proved absence of a failure; error returns stay distinct from model panics.

## Q01 — Generated program and parser fuzzing

Classification: partial.

typed Zig program generation, malformed JSON generation, reproducible seeds and failure shrinking. Include aliasing, globals, cleanup, unions, casts and nested control flow. Acceptance: failures reduce to a minimal reproducible source/input; malformed inputs fail predictably rather than reaching emitter placeholders.

## Q02 — Property coverage and mutation expansion

Classification: partial.

coverage mapped to each register item and meaningful mutants for forwarding, layout, operand order, failure cleanup, profile selection and invariant transfer. Acceptance: a feature cannot close on positive examples alone; its negative tests and designated mutants detect the wrong behavior.

## Q03 — Concurrent schedule exploration

Classification: partial.

separate observed-result matching from bounded outcome enumeration; replayable schedules, sound reduction techniques where proved, and explicit cap/fuel coverage. Acceptance: reports state schedules explored and limits; no capped run silently counts as demonstrated correspondence.

## Q04 — Host and skipped-case accounting

Classification: partial.

publish exact matches, host differences, undefined/unspecified cases, capped searches, skipped functions and proof exclusions separately by version/target. Acceptance: headline totals cannot include excluded cases as successful comparisons. Legacy-version support claims match the actual matrix.

## Q05 — Cross-target continuous integration

Classification: partial.

version/target/profile matrices for every declared supported path, including WASM execution once T02/T05 are implemented. Acceptance: platform support is backed by native execution, target probes and proof checks appropriate to that platform, not just compilation of foreign goldens.

## Q06 — Translation and proof performance budgets

Classification: partial.

measure parse/normalize/check/emit/proof time, peak memory, output size and warm-cache behavior on real modules. Improve lookup/indexing and modularization where measurements justify it. Acceptance: recorded workloads and budgets catch regressions; optimizations preserve definitions or carry preservation evidence.

## Q07 — Compiler and model upgrade qualification

Classification: partial.

compare AIR tag/type lists, layout and float probes, std model boundaries, changed translations and theorem dependencies for every upgrade. Acceptance: an upgrade cannot expand support or change a model silently; affected proofs and target tests are rerun and documented.

## Q08 — Review and release evidence

Classification: partial.

preserve review coverage, resolve confirmed findings, run release gates against one exact source/profile state and publish the results with known exclusions. Acceptance: the release record includes reproducible commands, successful gates and explicit unavailable checks; the review ledger identifies the reviewed revisions.

## D01 — Reconcile stale milestones

Classification: partial.

one current support matrix generated where possible; separate historical milestone scope from present open work. Acceptance: no current gap list repeats completed work; comments, README, PLAN and CLI agree.

## D02 — Verify and close the current theorem inventory

Classification: partial.

build the current theorem modules for their declared version/target translations, then update T7 and related claims. Remaining scope includes C14 and F05. Acceptance: each listed theorem has a current check result and precise domain. A theorem about one step or one schedule is not labeled as a full all-schedules theorem.

## D03 — Assumption and contract reference

Classification: partial.

one indexed reference for target profiles, allocator policies, thread creation, memory ordering, timers, opaque math, assembly and compiler trust; link each theorem/report to the premises it uses. Acceptance: a reader can determine what a proof means without searching every runtime module.

## D04 — Tutorials and supported model extension examples

Classification: partial.

tutorials for pure arithmetic, mutable arrays, generic containers, external contracts, allocation failure, concurrent clients and cross-target verification. Acceptance: each tutorial runs from a clean qualified environment and exposes the assumptions and remaining obligations.
