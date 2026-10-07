# Roadmap handoff

This handoff finishes the existing eight-closeout batch and preserves the broader roadmap. All eight closeouts are merged at feature integration head `5f7f547ed885d56624c9536c90e2b0d60e901568`. The register has **88 requirements: 3 complete, 66 partial, 8 open and 11 research**. The other 85 requirements remain incomplete even where a useful bounded feature has shipped.

The repository translates a supported subset of Zig into Lean, supplies executable memory/concurrency models and kernel-checked proofs, and compares selected generated computations with compiled Zig. This batch improves error/outcome reporting, ABI/storage behavior, deadlines, sentinel allocation, byte permutations and a bounded RwLock snapshot client. Use the [README](https://github.com/riventic/air2lean/blob/main/README.md) to start, [PLAN](https://github.com/riventic/air2lean/blob/main/PLAN.md) for implemented milestones and [coverage](https://github.com/riventic/air2lean/blob/main/docs/coverage.md) for supported domains.

## Existing closeout batch

| Closeout | State | Evidence / remaining work |
|---|---|---|
| ABI alignment | Merged | [PR100](https://github.com/riventic/air2lean/pull/100): bounded equal-zero alignment behavior. |
| Deadline/atomic correspondence | Merged | [PR101](https://github.com/riventic/air2lean/pull/101): declared clock/resource premises remain. |
| Sentinel allocation | Merged | [PR102](https://github.com/riventic/air2lean/pull/102): bounded allocation/client scope. |
| Byte permutation | Merged | [PR103](https://github.com/riventic/air2lean/pull/103): bounded byte-buffer behavior. |
| Outcome taxonomy | Merged | [PR96](https://github.com/riventic/air2lean/pull/96): distinct outcomes, exclusions and skipped-case accounting. |
| RwLock snapshot client | Merged | [PR104](https://github.com/riventic/air2lean/pull/104): bounded two-load snapshot/result and safety contracts. |
| Storage | Merged | [PR105](https://github.com/riventic/air2lean/pull/105): bounded error-storage controls, normal-function-pointer provenance and same-finite-union regressions repaired, with declared version generation/proof/runtime controls. |
| Global payload pointers | Merged | [PR106](https://github.com/riventic/air2lean/pull/106): bounded payload-pointer identity/offset and generated alias/read clients, with fresh producers and declared proof/runtime/metadata/frame controls. |

For the next agent, start from a fresh isolated checkout of current public main; preserve the dirty primary. Read this register and the acceptance companion, choose the next broader incomplete requirement, and identify its unsupported domain and acceptance evidence before implementation. The existing eight-closeout batch is finished; work now proceeds from the 85 broader incomplete requirements. The scheduler remains stopped.

For the two final feature gates, use the [finite error-storage guide](https://github.com/riventic/air2lean/blob/main/tests/roadmap/error-storage/README.md) and [global payload-pointer guide](https://github.com/riventic/air2lean/blob/main/tests/roadmap/global-payload-pointers/README.md). Their matching-version fixtures, generated clients, negative controls and semantic mutations passed locally before final CI. The later global seven-family differential run records 27,424 cases, 27,068 exact matches, 191 illegal exclusions and 165 unspecified exclusions, with zero setup failures or mismatches and `qualified=false`; it remains a focused subset.

The original Outcome closeout’s Zig0.16 differential report contains **87,064 cases: 85,987 exact matches, 497 illegal cases and 580 unspecified cases**, with zero setup failures or mismatches and one example/three functions skipped. It is complete with `qualified=false`. These totals belong to the original Outcome scope, not a later focused subset or a new current full-run claim. They do not establish compiler/native correspondence or theorem applicability; the [assumptions audit](https://github.com/riventic/air2lean/blob/main/docs/assumptions-audit.md) and [proof documentation](https://github.com/riventic/air2lean/blob/main/docs/proofs.md) retain the relevant distinctions. Use the repository's [differential driver](https://github.com/riventic/air2lean/blob/main/scripts/diff.sh), documented generation/proof checks and exact-head [CI workflow](https://github.com/riventic/air2lean/blob/main/.github/workflows/ci.yml) for the scope being changed.

Native observations remain bounded by version, target, backend and profile. Global payload-pointer qualification retains its stage2_x86_64/Linux-musl ReleaseSafe domain; the LLVM constant-offset36 versus runtime38 discrepancy is unqualified. Concurrency proofs retain explicit ownership, clock, lifetime, join-before-free, schedule and fuel premises. They do not imply fairness, termination, multiwriter support or a general synchronization library. See [standard models](https://github.com/riventic/air2lean/blob/main/docs/std-models.md) and [coverage](https://github.com/riventic/air2lean/blob/main/docs/coverage.md).

Use an isolated checkout and preserve the dirty primary. Actual Lean/Zig/runtime work uses one serial lane with **8 CPUs, 16 GiB combined memory plus swap, and 512 PIDs**. Reuse quiescent version-private caches bound to current compiler inputs; keep builds, runtime checks and mutation shards serial. Keep later work scoped to an explicit requirement and its acceptance; a scheduler restart requires its own explicit instruction.

## Requirement register

The table preserves all88 IDs, order and classifications. The [remaining acceptance companion](https://github.com/riventic/air2lean/blob/main/remaining-acceptance.md) preserves every broader acceptance statement; Desktop readers can use its [GitHub main link](https://github.com/riventic/air2lean/blob/main/remaining-acceptance.md) once the final docs merge is published. A bounded merged slice does not change a requirement's classification unless its full acceptance is established.

| ID | Requirement | Status | Bounded status and remaining scope |
|---|---|---|---|
| T01 | Explicit target and build profiles | complete | Schema12 complete target/build facts and fail-closed mixed profiles, with named legacy ABI; completion is metadata policy, not target generalization or binary correspondence. |
| T02 | Parameterized pointer and machine integer widths | open | No new closing implementation established in the inspected public/resume evidence; retain existing source behavior and explicit rejection. |
| T03 | Endianness support | research | No new closing implementation established in the inspected public/resume evidence; retain existing source behavior and explicit rejection. |
| T04 | Architecture-specific ABI qualification | partial | [PR100](https://github.com/riventic/air2lean/pull/100) merged with bounded alignment and three-version controls. Broader float, synchronization and architecture qualification remains. |
| T05 | Native and WASM correspondence | research | Paired bounded integer ABI observations only; wasm32 and whole-program correspondence absent. |
| T06 | Compiler backend and build-mode qualification | partial | Profile/backend/mode disclosure and bounded probes; no backend preservation theorem. |
| L01 | Executable full AIR coverage inventory | partial | Compiler-derived exhaustive enum inventory exists for three versions; semantic hits remain navigation/unclassified rather than verified full coverage. |
| L02 | Integer bit operations and shift overflow | partial | Typed bit-operation subset and proof/test gate merged; qualify wider representation cases separately. |
| L03 | Loop switch and switch dispatch | partial | Structured loop-switch/dispatch support and lexical rejection gates merged; unrestricted control flow is not implied. |
| L04 | Pointer-form try | partial | Pointer try export/check/emission slice merged with qualified boundaries; broader aliases/cleanup remain explicit. |
| L05 | C pointers and allowzero | partial | Nonoptional scalar C/allowzero fragment merged; nullable storage/aggregates/projections remain restricted. |
| L06 | Constant pointer bases | partial | [Global PR106](https://github.com/riventic/air2lean/pull/106) merged with bounded producer/export/generated alias/read proof and runtime controls. Finite provenance/offset, alias and target/profile limits remain; general nested pointer/base acceptance and the LLVM discrepancy remain incomplete. |
| L07 | Aggregate and optional-pointer bitcasts | partial | Existing dedicated packed/optional conversions; no general aggregate representation cast. |
| L08 | Packed representations and bit pointers | partial | [PR103](https://github.com/riventic/air2lean/pull/103) merged with bounded byte permutation controls. General packed representations and target/backend correspondence remain outside this slice. |
| L09 | Vector memory layouts | partial | Existing byte-width vector layouts and checked-add proofs; padded/non-byte lanes and bool-lane pointers remain restricted. |
| L10 | Error values and error layouts | partial | [Storage PR105](https://github.com/riventic/air2lean/pull/105) merged with bounded error-storage and declared version generation/proof/runtime controls, including normal-function-pointer provenance and same-finite-union regression repairs. Target/configuration-wide error encoding acceptance remains incomplete. |
| L11 | Local parent pointers and constant indirect calls | partial | PR95 merged bounded local parent recovery and qualified constant calls; arbitrary executable addresses not admitted. |
| L12 | Globals and initialization | partial | Initialized mutable/constant globals supported; extern/uninitialized storage and TLS remain out. |
| L13 | Volatile and device effects | open | No new closing implementation established in the inspected public/resume evidence; retain existing source behavior and explicit rejection. |
| L14 | Other compiler control and runtime features | partial | PR89 merged selected runtime/control classifications; lowered source fixture coverage is not universal tag semantics. |
| C01 | General spawn argument tuples | partial | General checked worker tuples merged; ownership remains existing modeled fork/join obligations. |
| C02 | Thread-local storage | open | No new closing implementation established in the inspected public/resume evidence; retain existing source behavior and explicit rejection. |
| C03 | Yield and spin hints | partial | Merged qualified yield/spin hint model merged without fairness; bounded countdown rules do not prove general progress. |
| C04 | Clocks deadlines and timeout races | partial | [PR101](https://github.com/riventic/air2lean/pull/101) merged with bounded deadline/atomic correspondence. General OS cancellation, spurious wake, fairness and liveness remain outside scope. |
| C05 | Cancellation and spurious wakeups | open | No new closing implementation established in the inspected public/resume evidence; retain existing source behavior and explicit rejection. |
| C06 | Spawn failure and group fallback behavior | partial | [PR98](https://github.com/riventic/air2lean/pull/98) merged with scoped spawn failure/fallback controls. Broader resource, OS and group semantics remain. |
| C07 | Detached threads and broader join ownership | open | No new closing implementation established in the inspected public/resume evidence; retain existing source behavior and explicit rejection. |
| C08 | Futures and general async IO | open | No new closing implementation established in the inspected public/resume evidence; retain existing source behavior and explicit rejection. |
| C09 | Pointer atomics and other atomic values | open | No new closing implementation established in the inspected public/resume evidence; retain existing source behavior and explicit rejection. |
| C10 | Sequential consistency and unordered operations | research | No new closing implementation established in the inspected public/resume evidence; retain existing source behavior and explicit rejection. |
| C11 | Weak CAS and message precision | partial | Weak CAS spurious-failure fragment merged/qualified; equal-value messages and mixed-size atomic precision remain separate. |
| C12 | Memory-model adequacy | research | No new closing implementation established in the inspected public/resume evidence; retain existing source behavior and explicit rejection. |
| C13 | Termination fairness and starvation | research | PR90 bounded singleton/countdown total rules only; general concurrent liveness remains research. |
| C14 | Reader writer locks and reusable synchronization contracts | partial | [PR104](https://github.com/riventic/air2lean/pull/104) merged with bounded snapshot-client kernel/native/integration controls. General reusable synchronization contracts, fairness and native adequacy remain. |
| M01 | Multiple allocator identities and policies | partial | Allocation policy selection exists; no general allocator identity, arena reset or custom allocator lifetime model. |
| M02 | Successful resize remap and realloc | partial | PR99 merged at124e07a; bounded byte-buffer in-place/moved/failure model, five semantic mutants and final composed targeted gate passed. General resize/realloc, custom allocator identity and address reuse remain outside scope. |
| M03 | General allocation failure and size policies | partial | Parameterized bounded policies and selected failure controls; arbitrary multi-failure/resource-independent client theorem remains. |
| M04 | Sentinel and lower-level allocator APIs | partial | [PR102](https://github.com/riventic/air2lean/pull/102) merged with bounded sentinel-allocation, overflow and integration controls. General raw/sentinel reallocation remains outside scope. |
| M05 | Address reuse and provenance contracts | research | No new closing implementation established in the inspected public/resume evidence; retain existing source behavior and explicit rejection. |
| M06 | Shared reads and reclamation proof interfaces | partial | Existing shared concurrency permissions and bounded join-before-free client; general reclamation interfaces remain. |
| F01 | Verified target profile selection | partial | Explicit IEEE/compiler-rt choice recorded in generated profile; no automatic shipping binary equivalence. |
| F02 | Transcendental specifications | research | No new closing implementation established in the inspected public/resume evidence; retain existing source behavior and explicit rejection. |
| F03 | Fast math and permitted transformations | research | No new closing implementation established in the inspected public/resume evidence; retain existing source behavior and explicit rejection. |
| F04 | Unspecified float cases | partial | Existing explicit unspecified outcomes; target-exact NaN/f80/zero contract expansion remains. |
| F05 | Complete version-specific f128 proofs | partial | Existing restricted op128 theorem retained; division-family/sqrt excluded selectors remain. |
| F06 | Practical numerical reasoning | partial | Classification/comparison/conversion lemmas exist; practical error bounds/reductions remain. |
| A01 | Assembly effects and operand coverage | partial | Qualified register-only assembly; memory/read-write/clobber effect semantics absent. |
| A02 | Instruction semantics and target expansion | research | Reviewed opaque register instruction assumptions; no verified general instruction semantics. |
| A03 | End-to-end assembly testing | partial | Existing sampled assembly harness; complete generated-wrapper interpretation/mutations remain. |
| E01 | User-defined external function contracts | partial | Typed selected external model contracts/registry exist; arbitrary project external contracts and trusted-status workflow remain. |
| E02 | Callback and function pointer contracts | partial | Qualified known function targets; arbitrary callback/context/reentrancy/cancellation contracts absent. |
| E03 | IO operating system and foreign API boundaries | partial | Selected modeled synchronization boundaries; no general OS/foreign interface qualification. |
| E04 | Model extension API | partial | Typed model registry and signature/profile checks merged; extend selected models with dependencies rather than name-only claims. |
| P01 | Separation logic automation | partial | Merged optional tools plus PR91/97 optional AC/frame and scalar-array split/update/reassembly with two generated clients; no automatic range/loop invariant synthesis. |
| P02 | Verification condition generation | partial | Merged loop-free typed Lean VC AST/soundness and explicit generated-body links; no automatic AIR VC extraction/CLI or guessed invariants. |
| P03 | Loop recursion and arithmetic tactics | partial | Existing loop/measure and arithmetic proof rules; templates and broad automation remain. |
| P04 | Modular contracts and abstract data types | partial | PR97 reusable scalar array contracts and restricted lock candidate; queues/maps/general ADTs remain. |
| P05 | Total correctness interfaces | partial | Merged explicit sequential Returns/TotalTriple interface; general concurrency termination absent. |
| P06 | Resource and complexity proofs | open | No new closing implementation established in the inspected public/resume evidence; retain existing source behavior and explicit rejection. |
| P07 | Proof-friendly and stable generation | partial | PR93 deterministic names and PR94 scalar stable proof API merged; general memory/recursive source maps/fingerprints remain. |
| P08 | Counterexamples and proof diagnostics | partial | Typed diagnostics and bounded Outcome witness/replay candidate; full source-mapped proof obligation counterexamples remain. |
| I01 | Zig build integration and root selection | partial | Project manifests/root selection and checked existing AIR workflow; automatic original-source build/export closure integration remains. |
| I02 | Dependency discovery | partial | Explicit modeled/call boundary diagnostics; complete exporter dependency discovery remains. |
| I03 | Project configuration and support profiles | partial | Versioned project/typed diagnostics manifests and limits exist; theorem-goal/contract/assumption portability incomplete. |
| I04 | Modular output and incremental checking | partial | Build cache hygiene and stable names exist; dependency-aware generated module splitting/invalidation remains. |
| I05 | Complete machine-readable diagnostics | partial | Typed independent blockers/code/anchor/chain reporting exists; opaque first-error boundaries and caps explicitly remain. |
| I06 | Verification coverage reports | partial | Per-root typed/status receipts and inventories exist; complete property/domain/assumption proof coverage not inferred. |
| I07 | Provenance and artifact manifests | partial | Source/AIR/Gen/profile/raw receipts and theorem audits exist; complete shipping source-to-binary-to-theorem chain remains. |
| I08 | Safe output and execution controls | partial | Atomic no-clobber publication and bounded project input/control gates; continue cancellation/live-child/resource coverage. |
| I09 | Distribution and editor workflow | partial | Local Linux Docker/checksum compiler builds and bootstrap docs; release packages/doctor/editor workflow remain. |
| V01 | Formal AIR semantics | research | No new closing implementation established in the inspected public/resume evidence; retain existing source behavior and explicit rejection. |
| V02 | Normalization and emission preservation | research | No new closing implementation established in the inspected public/resume evidence; retain existing source behavior and explicit rejection. |
| V03 | Exporter and compiler correspondence | partial | Trust boundaries and source/profile receipts disclosed; compiler/export/backend preservation unproved. |
| V04 | Theorem dependency and assumption auditing | complete | Compiled-environment theorem dependency/axiom/opaque/extern policy audit merged, with scoped actual checked inventories; each new profile needs its own run. |
| V05 | Schema and whole-program validation | complete | Supported-schema/profile and whole-program structural/type/global/call rejection policy merged; future schemas/mixed inputs fail closed. |
| V06 | Explicit outcome taxonomy | partial | [PR96](https://github.com/riventic/air2lean/pull/96) merged with explicit outcomes and exclusions. Broader taxonomy acceptance remains separate from correspondence. |
| Q01 | Generated program and parser fuzzing | partial | Focused fuzz/parser/typed fixtures exist; general generated Zig programs and shrinking remain. |
| Q02 | Property coverage and mutation expansion | partial | Existing semantic mutation gates and new five M02 mutants; complete feature-to-stage mutation mapping remains. |
| Q03 | Concurrent schedule exploration | partial | Bounded Outcome FIFO/DFS enumeration and replay are available. Exhaustive all-schedule correspondence and sound reduction theorems remain. |
| Q04 | Host and skipped-case accounting | partial | The original Outcome-scope Zig0.16 report records87064 cases/85987 exact matches/497illegal/580unspecified with zero setup failures or mismatches, one example/three functions skipped. qualified=false; proof applicability is unevaluated. This is not a current focused-subset or new full-run total. |
| Q05 | Cross-target continuous integration | partial | Three-version Linux and selected macOS paths; no full cross-target/WASM matrix. |
| Q06 | Translation and proof performance budgets | partial | Measured bounded input/resource budgets, cache regression/prune, lookup fixes; representative module/proof budget suite incomplete. |
| Q07 | Compiler and model upgrade qualification | partial | Compiler universe/change-impact detector exists; actual release qualification remains required per changed source/profile. |
| Q08 | Review and release evidence | partial | Independent source/union review and source-bound actual gates; merged closeout release/CI evidence retained; broader release completeness remains. |
| D01 | Reconcile stale milestones | partial | README, PLAN and this register distinguish the merged closeout from broader gaps. A unified generated support matrix and full milestone reconciliation remain. |
| D02 | Verify and close the current theorem inventory | partial | Current bounded theorem/client checks and the merged RwLock snapshot slice are retained. Broader theorem/integration acceptance and f128 exclusions remain. |
| D03 | Assumption and contract reference | partial | Profiles/std models/assumptions audit docs cover many premises; single per-theorem local-premise index incomplete. |
| D04 | Tutorials and supported model extension examples | partial | Getting-started/project/model/proof-tools tutorials exist; clean production-container/foreign/cross-target workflows incomplete. |
