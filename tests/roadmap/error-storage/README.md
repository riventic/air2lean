# Finite symbolic 16-bit error storage

Draft source qualification target. No build, native run, exporter run, proof elaboration,
or release qualification is claimed by the author. Root owns the serialized bounded Linux lane.

The supported fragment uses distinct nonempty declared finite error names (at most 65535),
with exact 2-byte size/alignment. `E` excludes zero; `?E` stores `none` as zero with no flag.
Arrays, ordinary fields, nested optionals, globals, and error-union payloads select storage
dictionaries recursively. Existing public `String` error names and `Except` results remain.
A foreign name writes undefined bytes and cannot reload as a valid finite-domain error.
`FiniteError d` supplies membership as a type invariant for `LawfulEnc`; unrestricted String
has no global Enc or LawfulEnc instance. Existing framed memory lemmas apply to FiniteError.

These are finite symbolic name fragments, using the existing error-union abstraction. The
name table's order is not an ABI ordinal table. No compiler-wide numeric code is fabricated.
Integer/error casts, unresolved standalone anyerror/inferred error sets, non16-bit layouts,
empty standalone domains, invalid fragments, and foreign domain names fail closed.
Raw integer loads from error fragments remain unspecified in the memory model.

Compiler-source evidence: Type.optionalReprIsPayload returns true for error-set children in
0.14.1 (line 1993), 0.15.2 (1898), and 0.16.0 (1428). LLVM14's
optional_payload_ptr_set returns the same pointer without writing a flag: the subsequent
payload write establishes nonnull. Compiler-provided type layouts remain the acceptance gate.

Root recipe, strictly sequential, bounded by the owning Linux validation lane:

1. Build ZigLean, Air2Lean and air2lean on the frozen source snapshot.
2. `lake env lean --run tests/roadmap/error-storage/Runtime.lean`.
3. `lake env lean --run tests/roadmap/error-storage/Pipeline.lean /tmp/ErrorStorage.lean`, then
   elaborate the emitted file. This checks normalized boundary fixtures and negative domains.
4. Stock Zig 14/15/16 `test error_storage.zig -OReleaseSafe`; patched matching compiler exports
   with filter `error_storage.` on x86_64-linux baseline, no error tracing. Translate fresh AIR
   with namespace ErrorStorage and prefix error_storage.; elaborate generated definitions.
5. Run fresh generated functions on the same name/bool cases as native tests. No numeric error
   codes are compared. Prove the three concrete generated observation cases, including actual
   global frame reads, nested payloads, and both branches of an error-bearing struct payload.
   Run typed dictionary semantic mutations. Direct E!E success is qualified only in Runtime.lean;
   the native fixture uses E!struct{code:E}, since bare E coercion selects the error arm.
6. Run current regression suites involving error unions and optional/aggregate memory; record
   any deliberate dictionary-text updates separately from unchanged API semantics.

Independent MED8 source review is in progress before any commit or PR. Actual qualification
remains pending in Root’s lane. This draft is not full Zig error semantics.

The focused owner-only feature gate is `check.sh`, requiring AIR2LEAN_ZIG_AIR,
AIR2LEAN_ZIG_NATIVE, AIR2LEAN_ERROR_STORAGE_VERSION (an owner-verified label), and a fresh
AIR2LEAN_ERROR_STORAGE_OUT_DIR. Set AIR2LEAN_ERROR_STORAGE_BUILD=1 only when the owner
needs the initial build. It retains fresh AIR, generated source, both observation files,
compiled mutant definitions and semantic failure logs. The enclosing ROOT lane supplies
process-group cleanup and execution deadlines; this script launches all commands sequentially.
Root runs the integration regression suites from recipe step 6 separately.
The fresh generated global block labels bind observation pointers, requiring exactly one match.
Both oracles check the guard, updated fields, and untouched global array neighbors. Three
concrete generated observation proofs cover nine predicates each; no universal generated
function contract is claimed.

Source review boundary: differing optional/aggregate/error-union value bitcasts and pointer
casts exposing error-backed storage as numeric or opaque pointees are rejected. This is a
syntactic guard, not a global alias/provenance analysis; raw aliases supplied independently
across calls remain outside the qualified finite symbolic fragment. Error-free pointer casts
retain their existing handling. Empty E remains rejected standalone; error{}!T retains its
success encoding. Domain validation uses a hash set and payload dictionaries are computed
once per recursive emitter level. Repeated inline domain literals/proofs remain a known
source-size cost; globally shared declarations are deferred to avoid coordinated emitter
context and naming API changes in this focused patch. No timing measurements are claimed.

All three pristine Sema inventories lower runtime @intFromError to a bitcast (0.14.1:8545,
0.15.2:8156, 0.16.0:7763), and runtime @errorFromInt ends in a bitcast (8587/8198/7805).
Safety lowering also uses cmp_lt_errors_len on14/15 and cmp_lte_errors_len on16, which remain
unsupported. These source forms are rejected rather than mapped through name-table positions.
Comptime-folded integer literals come directly from the compiler's actual result; the symbolic
error-storage model does not infer an ordinal map from those literals.


The finite-global alias fragment checks folded addresses against the addressed subobject,
including a bit-pointer's complete host read. Numeric one-pointer local loads of ordinary
guard fields and successful `E!u16` payloads remain allowed, as do typed `E` reads and
ordinary error-name observations. Aliases overlapping symbolic error bytes are rejected.
Multiple-item pointer capabilities require a matching complete root or homogeneous array
backing; matching only the first field of mixed error/numeric storage does not suffice.
Unresolved pointer-valued local results, bulk and mixed-backing indexed operations, pointer escape
through returns/calls/stores, and pointer-to-integer views rooted in these globals fail
closed. This bounded local check is not general interprocedural pointer provenance.
`GlobalAlias.lean` supplies focused checker controls. ROOT must rebuild and run the retained
stock-compiler/real-AIR folded-cast packet before production qualification is claimed.
