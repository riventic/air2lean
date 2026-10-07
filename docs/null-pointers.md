# C and allowzero pointer fragment (L05)

Nonoptional `[*c]T`, `*allowzero T` and `[*]allowzero T` values use `Zig.Ptr`.
Address zero is `Zig.Ptr.null = ⟨none, 0⟩`: no block and no allocation. The pointer
representation is separate from dereference validity: being nonnull never establishes
provenance, lifetime, bounds or alignment. The reference scope is the existing 64-bit
little-endian, ReleaseSafe AIR model. This fragment is deliberately smaller than complete
C/allowzero pointer support.

| Operation | Rule |
| --- | --- |
| Runtime integer → nullable pointer | `ptrFromAddrNullable 0` returns null without changing memory. Nonzero addresses use existing `ptrFromAddr` block-range resolution. |
| Pointer → integer | `ptrAddr` observes the address; it does not dereference or revive a dead allocation. |
| Null/non-null value tests | `ptrIsNull` compares the address with zero. It does not interpret a scalar pointer as `Option Ptr`. |
| Nullable pointer equality/inequality | `ptrEqAddr` compares addresses, including zero. |
| Nullable → nonnullable scalar pointer cast; C `p.?` | `ptrRequireNonNull` rejects zero with `.panic` and preserves a nonzero pointer. Being nonnull does not establish provenance, lifetime, bounds or alignment. |
| Direct load/store through a scalar nullable pointer | The existing `Mem.access`/`accessW` rules apply. Positive-size accesses require a real live block, bounds and alignment; stores also require writable storage. Source AIR safety guards remain part of the translation. |
| Zero pointer constant | An explicit `ptr: {"null": true, "off": 0}` becomes `Val.ptrNull`; the checker requires a C/allowzero type, also inside an aggregate constant. Other integer-base constants remain rejected. |
| Nullable pointer stored in memory (`*[*c]T`, global, escaping local) | Load/store of the pointer value itself use the storage dictionary `Zig.nullablePtrEnc`: address zero is eight zero integer bytes (the bytes of a null `?*T`); other pointers keep their provenance fragments. Zero bytes from any source read back as null; undefined or other integer bytes stay `.unspecified`. The access premises are those of the storage location, never of address zero. |
| C/allowzero pointers in extern/auto structs and arrays | The generated struct `Enc` and `Zig.Enc.vectorWith` select `Zig.nullablePtrEnc` per field/item; values of these aggregates are ordinary Lean structures/vectors of `Zig.Ptr`. |
| Projection from a C/allowzero base (`struct_field_ptr`, `ptr_elem_ptr`, `ptr_add`, `ptr_sub`) | `ptrProjectNullable p project` is `.illegal` for address zero (the compiler inserts no check; there is no object at zero) and `project p` otherwise. The result keeps the base's provenance, so any access through it still needs the existing live-block/bounds/alignment premises. |
| Item read through a C/allowzero pointer (`ptr_elem_val`, `p[i]`) | The existing item access; `Mem.access` rejects a null or raw base. |
| `[*c]T`/`*allowzero T` ↔ `?*T`/`?[*]T` (`bitcast`, in-memory coercion) | `ptrToOptional` maps address zero to the explicit `none` and other values to `some`; `ptrOfOptional` maps `none` to address zero. No dereference or allocation. |

Null tests are address observations. They do not promise a zero-address object or
MMIO semantics. A raw nonzero integer pointer also fails access until it has valid
block provenance. The model does not change its allocator or the global `Enc Ptr` and
`Enc (Option Ptr)` encodings; the null-byte storage rule is an explicit dictionary bound
only at C/allowzero storage sites.

The checker still rejects `?[*c]T` and `?*allowzero T` (an optional of a nullable pointer
needs a separate flag; its `none` must not be conflated with the payload's zero),
nullable pointers in unions, tuples, packed aggregates and error-union payloads,
nullable slices/bit-pointers/volatile pointers, conversions between a nullable pointer and
an optional slice, `wrap_optional` of a nullable operand, and nullable slice construction,
`@memset`/`@memcpy` and `@fieldParentPtr` through a nullable pointer. Use a checked
nonnullable cast before those operations.

Compiler source inspection of 0.16.0 (`Sema.elemPtrOneLayerOnly`, `Type.elemPtrType`,
`Type.fieldPtrType`, `Sema.analyzePtrArithmetic`, `Sema.coerceExtra`/`coerceCompatiblePtrs`)
shows that C-pointer element/field projections and arithmetic emit no null safety check,
and that `[*c]T` ↔ `?*T` coercions are in-memory `bitcast`s; the 0.14.1 and 0.15.2 sources
were spot-checked for the same C-pointer element path. These are source facts, not
compiler-execution or preservation evidence; no fresh export of the new operations has
been run.

Compiler source inspection of 0.14.1, 0.15.2 and 0.16.0 establishes the relevant
representation boundaries: `InternPool.Key.Ptr.BaseAddr.int` carries no payload;
the integer address is in `byte_offset`. `Type.optionalReprIsPayload` excludes
C/allowzero children from ordinary optional-pointer payload representation.
C null tests lower to `is_null`/`is_non_null`, and the C-pointer payload operation
retains the scalar C-pointer type (`Sema.zirOptionalPayload`). These source facts
are not new compiler-execution or preservation evidence.

## Proof and regression evidence

`ZigLean/Mem/Null.lean` contains universal theorem definitions `null_access`,
`nullable_from_zero`, `null_is_null`, `null_unwrap`, `raw_address_access`,
`null_project`, `null_offset_access`, `null_to_optional` and `optional_none_to_null`.
The direct-access validity premises reuse `ZigLean/Mem/Lemmas.lean`'s existing
`access_of`/`access_eq` rules. A nonnull check cannot discharge those premises.

The proof-only module `ZigLean/Mem/NullLemmas.lean` (outside the `ZigLean` runtime
umbrella, because it imports `ZigLean.Mem.Lemmas`; build it with
`lake build ZigLean.Mem.NullLemmas`) proves `nullablePtrEnc_lawful` (so the generic
`load_store_same`/`store_run` rules apply to stored C pointers), the representation match
`nullablePtrEnc_encode_eq_optional`, `nullablePtrEnc_decode_zero`, `load_store_null`,
`ptrProjectNullable_ok`, `projected_access_block` (an access through any projection
succeeds only in a live block of the base's own provenance) and `ptrOfOptional_toOptional`.

`tests/roadmap/null-pointers/Generate.lean` adds twelve hand-written AIR cases matching the
exporter schema: stored C and allowzero pointers (null bytes, round trips, zero-byte and
undefined-byte reads), extern-struct field projections and a struct round trip with a null
field, an array item, `ptr_add`/`ptr_elem_ptr`/`ptr_elem_val` from a C base, and both
optional conversions. Each checks the emitted helper and elaborates its `native_decide`
regressions; adjacent rejections cover the still-restricted forms above. These are
synthetic-AIR regressions, not fresh compiler exports.
Theorems apply to this model, with its existing compiler/export/normalization
trust boundary; they are not AIR/backend preservation theorems.

The scoped driver is sequential and requires supplied matching toolchains:

```sh
AIR2LEAN_NULL_ZIG_VERSION=0.16.0 \
AIR2LEAN_NULL_ZIG_AIR=/path/to/patched-0.16.0/bin/zig \
AIR2LEAN_NULL_ZIG_NATIVE=/path/to/shipping-0.16.0/zig \
AIR2LEAN_NULL_TRANSLATOR=/path/to/air2lean \
  tests/roadmap/null-pointers/check.sh
```

The patched compiler must include the updated zero-constant exporter. Run the
same driver for 0.14.1 and 0.15.2; it does not provision or build a Zig compiler.
The driver builds the runtime/translator, checks imported theorem definitions,
checks synthetic schema/checker rejections, elaborates twenty-one generated semantic
cases (nine before the storage/projection extension), kills an inverted-null-predicate mutant, exports fresh compiler-generated
fixtures, compares eight native/Lean observation lines, and checks two separate
compiler-generated rejection roots (`optional`, a stored `?*allowzero u8`, replaced the
former stored-`[*c]u8` root, which is now accepted). The six integer inputs include zero, small
addresses and the maximum 64-bit address. Native dereference is exercised only
with a live byte; invalid provenance/dead-block access is tested in the model.

`native_decide` occurs only in generated regression fixtures, following the
existing emitter-test convention. The shipped universal theorem definitions (nine in `Null.lean`, twelve in `NullLemmas.lean`)
use kernel reductions and do not use `native_decide`, `sorry`, `admit` or axioms.
The root serialized validation queue passed the complete driver at source
revision `a63879e` on Zig 0.16.0 in 15.4 seconds (614 MiB peak memory), after
building the updated patched exporter in 290 seconds (4422 MiB peak memory).
The driver checked the runtime's five theorem definitions, nine semantic cases,
one killed mutant, eight native observation lines, and two compiler rejection
roots. The shared-predicate cleanup subsequently passed the complete gate at `e1d5123`
in 19.7 seconds (740 MiB peak memory). The complete driver passed again at
`8eb82fb` in 15.5 seconds (809 MiB peak memory), including the successful-type-check
cache and both repeated-type per-value rejection regressions. The cache skips
only previously successful type-graph checks; null constants, unsupported pointer
constants and global-pointer alignment remain checked for every operand.

These recorded driver runs predate the storage/aggregate/projection extension. For that
extension only the offline part was run locally (generator, all twenty-one generated
modules and the proof module); the full driver with a fresh patched export and the new
`optional` rejection root (whose source compiles with shipping Zig 0.16.0) is pending.

The recorded local toolchains were the worktree's
`.lake/roadmap-null-zig16/bin/zig` (patched AIR exporter),
`/Users/konstantinrr/.cache/air2lean/host-0.16.0/zig` (shipping native compiler),
and pinned Lean `leanprover/lean4:v4.34.0` at
`/Users/konstantinrr/.elan/toolchains/leanprover--lean4---v4.34.0/bin/lean`.
Both Zig invocations used `-OReleaseSafe -fno-error-tracing`, with no `-target`
or `-mcpu` override. The run was on the root's arm64 macOS host using compiler
defaults; the retained logs do not establish an exact CPU profile. Exported
schema 11 target metadata is legacy/unverified. This observation set therefore
does not qualify the model's reference x86_64-linux target or every host CPU.

Local retained logs are
`/opt/dev/air2lean/.lake/review-resume/roadmap/null-pointers-full-first.log` and
`/opt/dev/air2lean/.lake/review-resume/roadmap/null-exporter16-build.log`.
CI reruns the driver in the full nonmutation 0.16.0 Linux job with that job's
fresh/cache-keyed patched exporter and separately pinned shipping host compiler.
Linux CI and 0.14.1/0.15.2 execution results are pending. Full L05 remains open
for optionals of nullable pointers, nullable pointers in unions/tuples/error-union
payloads, nullable bulk memory/slicing/parent recovery, native observations of the new
storage/projection operations, and the other deliberately rejected operations above;
eight finite observations are not a preservation theorem.

The nullable mutation gate requires normal Lean exit 1 and exactly the three
located `native_decide` evaluation refutations for `cNull` at 0, 1 and the maximum
u64 value. The classifier binds the inverted predicate source to the unmodified
baseline, checks the assertion line and column and displayed proposition, and
rejects extra diagnostics, abnormal exits and incomplete output. Its standalone
interface is `python3 tests/roadmap/null-pointers/classify_mutant.py EXIT LOG
MUTANT BASELINE`; each input is bounded to 64 KiB. The caller must first check the
baseline. Classification of these evaluation refutations does not establish
kernel proof adequacy or compiler preservation. Mock-only classifier regressions
run with `python3 -B tests/roadmap/null-pointers/test_classify_mutant.py`. Root
calibration with pinned Lean 4.34.0 passed all nine generated synthetic baseline
modules and classified exactly three intended refutations with normal exit 1.
The resource-guarded run took 36.747 seconds with 841.2 MiB peak sampled RSS.
This synthetic run does not establish fresh exporter or source correspondence.
