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
| Nullable pointer stored in memory (`*[*c]T`, global, escaping local) | Load/store of the pointer value itself use the storage dictionary `Zig.nullablePtrEnc`: `Ptr.null` is eight zero integer bytes (the bytes of a null `?*T`); other pointers, including one that reaches address zero by arithmetic on its provenance, keep their provenance fragments. Zero bytes from any source read back as null; undefined or other integer bytes stay `.unspecified`. The access premises are those of the storage location, never of address zero. |
| C/allowzero pointers in extern/auto structs and arrays | The generated struct `Enc` and `Zig.Enc.vectorWith` select `Zig.nullablePtrEnc` per field/item; values of these aggregates are ordinary Lean structures/vectors of `Zig.Ptr`. |
| Projection from a C/allowzero base (`struct_field_ptr`, `ptr_elem_ptr`, `ptr_add`, `ptr_sub`) | `ptrProjectNullable p project`. A zero byte offset (`project p = p`: the first field of a struct, item 0, a zero-size item) is the base itself for every base, including address zero: the backend emits no `getelementptr` for a constant offset 0, and a zero-offset `getelementptr inbounds` is defined. A nonzero offset from address zero is `.illegal`, for C and `allowzero` bases alike (see [Projections from address zero](#projections-from-address-zero)). Any other base is projected unchanged. The compiler inserts no null check. The result keeps the base's provenance, so any access through it still needs the existing live-block/bounds/alignment premises; a dereference of the zero-offset projection of address zero is `.illegal`. Where the compiler types the result as a nonnullable pointer (Zig 0.14.1/0.15.2 `struct_field_ptr`: `&p.*.f` of a `[*c]T` or `*allowzero T` is a `*F`; 0.16.0 keeps `allowzero`) the emitter uses `ptrProjectNonnull` instead: every offset from address zero is `.illegal`, so address zero never becomes a `*F`. |
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

## Projections from address zero

Zig 0.14.1, 0.15.2 and 0.16.0 lower `struct_field_ptr` through `ptraddConst` (0.16.0) or a
struct `getelementptr` (0.14.1/0.15.2), and `ptr_add`/`ptr_elem_ptr`/`ptr_sub` to
`getelementptr inbounds`; in 0.16.0 a constant offset 0 emits no instruction, and in every
version a zero-offset inbounds `getelementptr` is defined. The compiler adds no null check
(`Sema.analyzePtrArithmetic`, `Sema.elemPtrOneLayerOnly`). An inbounds offset requires an
allocated object at the base; the model never places one at address zero, and on the hosted
reference targets none exists. LLVM only marks a function `null_pointer_is_valid` when it loads or
stores through an `allowzero` pointer, so `allowzero` does not change the projection rule.

| Case | Zig 0.14.1–0.16.0 (native, aarch64-macos) | Model |
| --- | --- | --- |
| `&p.*.first` (offset 0), `p + 0`, `&p[0]`, `p - 0` from a null `[*c]T` | defined, address 0 (ReleaseSafe and Debug) | `Ptr.null` (0.14.1/0.15.2 `&p.*.first`, typed `*F`: `.illegal`) |
| the same from `*allowzero T`/`[*]allowzero T` at address 0 | defined, address 0 | `Ptr.null` (0.14.1/0.15.2 `&p.first`, typed `*F`: `.illegal`) |
| nonzero field offset, `p + n`, `&p[n]`, `p - n` (n ≠ 0) from address zero, C or `allowzero` | not address arithmetic: ReleaseSafe folds `(p + n) == null` to `p == null` (also for `allowzero`; 0.14.1 even in a `null_pointer_is_valid` function); Debug happens to yield `0 + offset` | `.illegal` |
| load/store through a projection of address zero (C or `allowzero`) | segmentation fault; no safety check in ReleaseSafe or Debug (the langref calls a C-pointer dereference of address 0 safety-checked on hosted targets; these compilers emit no check) | `.illegal` (`Mem.access`) |
| `p.?` of a null `[*c]T` or `?*T`; `[*c]T` → `*T` coercion of null | safety panic (`attempt to use null value`, `cast causes pointer to be null`) | `.panic` |

The model is therefore exact for the defined cases and `.illegal` exactly where the backend
treats the projection as undefined (LLVM poison) or the access faults, with one conservative
exception: Zig 0.14.1 and 0.15.2 type an offset-0 field pointer of address zero as a
nonnullable `*F` (`ptrProjectNonnull`), and the model makes it `.illegal` although the native
code yields address zero; whether later uses of that `*F` are defined is not confirmed natively. An `allowzero` object at
address zero (freestanding targets) is not modelled: a projection that would need it fails closed.
The theorems `null_project_zero`, `null_add_zero`, `null_project`, `null_add_ne` and
`null_project_nonnull` (`Null.lean`) and `ptrProjectNullable_same`, `ptrProjectNullable_ok`,
`ptrProjectNullable_zero_illegal` and `ptrProjectNonnull_ok` (`NullLemmas.lean`) state the rule.

Compiler source inspection of 0.16.0 (`Sema.elemPtrOneLayerOnly`, `Type.elemPtrType`,
`Type.fieldPtrType`, `Sema.analyzePtrArithmetic`, `Sema.coerceExtra`/`coerceCompatiblePtrs`)
shows that C-pointer element/field projections and arithmetic emit no null safety check,
and that `[*c]T` ↔ `?*T` coercions are in-memory `bitcast`s; the 0.14.1 and 0.15.2 sources
were spot-checked for the same C-pointer element path. These are source facts, not
preservation evidence; the fresh exports and native runs of these operations are recorded
below.

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
`null_project_zero`, `null_project`, `null_add_zero`, `null_add_ne`, `null_project_nonnull`,
`null_offset_access`,
`null_to_optional` and `optional_none_to_null`.
The direct-access validity premises reuse `ZigLean/Mem/Lemmas.lean`'s existing
`access_of`/`access_eq` rules. A nonnull check cannot discharge those premises.

The proof-only module `ZigLean/Mem/NullLemmas.lean` (outside the `ZigLean` runtime
umbrella, because it imports `ZigLean.Mem.Lemmas`; build it with
`lake build ZigLean.Mem.NullLemmas`) proves `nullablePtrEnc_lawful` (so the generic
`load_store_same`/`store_run` rules apply to stored C pointers), the representation match
`nullablePtrEnc_encode_eq_optional`, `nullablePtrEnc_decode_zero`, `load_store_null`,
`ptrProjectNullable_same`, `ptrProjectNullable_ok`, `ptrProjectNullable_zero_illegal`,
`ptrProjectNonnull_ok`,
`projected_access_block` (an access through any projection succeeds only in a live block of the
base's own provenance) and `ptrOfOptional_toOptional`.

`tests/roadmap/null-pointers/Generate.lean` adds eighteen hand-written AIR cases matching the
exporter schema: stored C and allowzero pointers (null bytes, round trips, zero-byte and
undefined-byte reads), extern-struct field loads and field pointers at offsets 0 and 8 (also from
an `allowzero` base) and a struct round trip with a null field, an array item,
`ptr_add`/`ptr_sub`/`ptr_elem_ptr`/`ptr_elem_val` from a C or `allowzero` base at offsets 0 and
nonzero, a field pointer typed nonnullable as 0.14.1/0.15.2 export it, and both optional
conversions. Each checks the emitted helper and elaborates its `native_decide`
regressions; adjacent rejections cover the still-restricted forms above. The same operations
are also compiler-exported and compared natively (below).
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
checks synthetic schema/checker rejections, elaborates twenty-seven generated semantic
cases, kills an inverted-null-predicate mutant, exports 24 compiler-generated roots of
`nullpointers.zig` (the original six plus storage, struct-field, array-item, projection,
`allowzero`-projection and optional-conversion roots, and the `addIsNull` fold witness), compares
25 native/Lean observation lines, and checks that the model is `.illegal` for five nonzero
offsets from address zero that native code never executes, and checks two separate
compiler-generated rejection roots (`optional`, a stored `?*allowzero u8`, replaced the
former stored-`[*c]u8` root, which is now accepted). The six integer inputs include zero, small
addresses and the maximum 64-bit address. Native dereference is exercised only
with a live byte; invalid provenance/dead-block access is tested in the model.

`native_decide` occurs only in generated regression fixtures, following the
existing emitter-test convention. The shipped universal theorem definitions (thirteen in `Null.lean`, sixteen in `NullLemmas.lean`)
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

These recorded driver runs predate the storage/aggregate/projection extension. The
complete driver with that extension and the precise projection rule passed on
aarch64-macos for Zig 0.16.0, 0.15.2 and 0.14.1 (patched exporters
`/opt/dev/air2lean-build/zig-air-<version>`, shipping compilers `host-0.16.0`, `host-0.15.2`
and `zig-aarch64-macos-0.14.1`; 39.5, 21.0 and 17.1 seconds, at most 1.7 GiB peak
memory): 27 semantic cases, one killed mutant, 25 native/Lean lines and two compiler
rejection roots. The lines are identical for 0.16.0; for 0.14.1 and 0.15.2 the driver expects
`illegal` in place of the native address 0 for exactly the two field pointers of address zero
(`nextPtr`, `allowzeroNextPtr`), the conservative `ptrProjectNonnull` case above. The `addIsNull` line records `illegal` natively because the
ReleaseSafe build answers `true` for `(null + 1) == null`, which address arithmetic would answer
`false`; it depends on LLVM's fold and is a witness, not a proof, of the undefined case.

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
Linux CI execution results are pending. Full L05 remains open
for optionals of nullable pointers, nullable pointers in unions/tuples/error-union
payloads, nullable bulk memory/slicing/parent recovery, and the other deliberately rejected
operations above; 25 finite observations are not a preservation theorem.

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
