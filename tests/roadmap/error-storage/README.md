# Finite symbolic 16-bit error storage

This fragment represents declared finite error domains using symbolic names in memory. Domains contain distinct nonempty names, at most 65535, and require compiler-provided 2-byte size and alignment. `E` excludes zero; `?E` uses zero for `none` without a separate flag. Arrays, ordinary fields, nested optionals, globals and error-union payloads select the corresponding storage dictionaries recursively. Public `String` error names and `Except` results retain their existing API.

A foreign name writes undefined bytes and cannot reload as a valid domain member. `FiniteError d` carries membership for `LawfulEnc`; unrestricted `String` has no global `Enc` or `LawfulEnc` instance. Existing framed memory lemmas apply to `FiniteError`. Direct `E!E` success is exercised in `Runtime.lean`; the native fixture uses `E!struct{code:E}`, since bare `E` coercion selects the error arm.

The name table is not a compiler ABI ordinal table. The model does not fabricate numeric error codes or compare compiler-wide ordinal assignments. Raw integer reads of symbolic error fragments remain unspecified. Integer/error casts, unresolved standalone `anyerror` or inferred sets, non-16-bit layouts, empty standalone domains and invalid fragments fail closed. `error{}!T` retains its success encoding. Comptime-folded integer literals come from the compiler's actual result and do not establish a symbolic ordinal map.

The checker rejects representation-changing error-bearing casts and numeric or opaque recovery of symbolic pointers. Narrow identity cases preserve the exact decoder: const qualification of an otherwise identical pointer, its own optional wrapper, and value error unions with equal valid ordered domains, the same payload type and equal complete known representation metadata. All remaining capability and provenance checks still apply.

Finite-global aliases are checked against complete typed subobjects and byte ranges, including a bit-pointer's complete host read. Numeric reads of ordinary fields and successful error-union payloads remain allowed. Multiple-item pointers require complete compatible backing; the first numeric field of mixed storage is insufficient. Symbolic aliases into numeric backing still require an exact typed subobject. Unresolved arithmetic, symbolic pointer escape through returns/calls/stores, numeric-to-symbolic parent recovery and unproven symbolic pointer origins fail closed. A final numeric pointer with a proven fixed global origin can use the bounded numeric exemption. These are bounded local checks, not general interprocedural provenance.

A global alias may also retain a closed, fully known error-free type graph containing shared or cyclic edges. Both its backing and view graphs must be checked within the bounded work budget; reachable errors, opaque or missing types and exhausted work are rejected. This exception applies only to global-alias checks whose strict capability walk cannot finish. Casts and parent recovery keep the strict cycle-rejecting checks.

The immutable-initializer exception requires a const, nonextern, nonthreadlocal global, complete known constructor values, no pointer-bearing backing types and an error-free pointee view. It classifies the whole block. Error names or arms, unknown/undefined constructor values, cycles and exhausted work fail closed. Successful error-union tags and optional null tags contain no symbolic fragment; padding may still be undefined. Symbolic views keep their complete-subobject checks, and model writes still reject const-global blocks. Type, capability and constructor walks use bounded work, including a shared 1024-node capability budget.

Run the focused gate separately for each matching compiler version (`0.14.1`, `0.15.2`, `0.16.0`), with a fresh retained output directory:

```sh
AIR2LEAN_ZIG_AIR=/absolute/path/to/matching-patched-zig \
AIR2LEAN_ZIG_NATIVE=/absolute/path/to/matching-stock-zig \
AIR2LEAN_ERROR_STORAGE_VERSION=0.16.0 \
AIR2LEAN_ERROR_STORAGE_OUT_DIR=/absolute/path/to/fresh-output \
bash tests/roadmap/error-storage/check.sh
```

Build `ZigLean`, `Air2Lean` and `air2lean` first, or set `AIR2LEAN_ERROR_STORAGE_BUILD=1`. The gate runs sequentially: model and normalized boundary controls, stock native tests, eight fresh AIR exports, generated-module elaboration, three native/model observation rows and concrete generated proofs covering nine predicates per row, then typed dictionary semantic mutants. It retains AIR, complete generated source, observations and classified mutation logs. Run it within a lane that provides execution deadlines and process cleanup. Checker controls (`Qualifier.lean`, `GlobalAlias.lean`) and current example/proof-client regressions are checked separately.

These finite observations and concrete proofs do not establish a universal generated-function contract, general Zig error semantics, native adequacy or compiler-wide correspondence. Independent aliases supplied across calls, arbitrary custom storage, ordinal-based casts and broader interprocedural provenance remain outside this fragment. Repeated inline domain declarations are a known source-size cost; no performance claim is made.

Validation: the focused Linux ReleaseSafe gate passed for Zig 0.14.1, 0.15.2 and 0.16.0, including fresh eight-function exports, generated elaboration, native/model observations, concrete observation proofs and typed dictionary mutants. Strict supported example generation and affected proof clients passed for five families on14, seven on15 and the current default selection on16, with Sync runtime and committed-source rebuilding checked separately. The three source inventories and exact committed-source closure passed. Six serial checker/model controls are inherited by exact source-closure identity from their completed run. These results retain the bounded fixture and profile scope above; final eight-job CI is a separate required gate.

The closed-cycle acceptance repair requires its own current-source API, CLI and checker regression gate; those checks are pending. The validation results above retain their pre-repair source scope.
