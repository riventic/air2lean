# C and allowzero pointers (L05)

`[*c]T`, `*allowzero T` and `[*]allowzero T` values use `Zig.Ptr`; `[]allowzero T` uses
`Zig.Slice`. Address zero is `Zig.Ptr.null = ⟨none, 0⟩`: no block and no allocation. The pointer
representation is separate from dereference validity: being nonnull never establishes
provenance, lifetime, bounds or alignment. The reference scope is the existing 64-bit
little-endian, ReleaseSafe AIR model (C/allowzero pointers are rejected on 32-bit profiles,
T02).

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
| Projection from a C/allowzero base (`struct_field_ptr`, `ptr_elem_ptr`, `ptr_add`, `ptr_sub`) | The checked pointer formation of every derived pointer, `ptrProject p project` (MM-3, `docs/architecture-audit/memory-model.md`): the same pointer is always allowed, so an offset-0 projection from address zero is defined (the compiler emits no `getelementptr`); any other result is `.illegal` unless base and result lie in bounds of the base's block, so a nonzero offset from address zero or another provenance-free address is `.illegal` (`getelementptr inbounds` poison). When the result type is nonnullable (0.14.1 and 0.15.2 type `&p.*.f` of a `[*c]T` as `*F`), `ptrProjectNonnull` also rejects address zero. The result keeps the base's provenance, so any access through it still needs the existing live-block/bounds/alignment premises. |
| Item read through a C/allowzero pointer (`ptr_elem_val`, `p[i]`) | The existing item access; `Mem.access` rejects a null or raw base. |
| `[*c]T`/`*allowzero T` ↔ `?*T`/`?[*]T` (`bitcast`, in-memory coercion) | `ptrToOptional` maps address zero to the explicit `none` and other values to `some`; `ptrOfOptional` maps `none` to address zero. No dereference or allocation. |
| Optional of a nullable pointer (`?*allowzero T`, `?[*c]T`, `?[]allowzero T`) | `Option Zig.Ptr` (`Option Zig.Slice`) whose `none` differs from `some Ptr.null`: the compiler gives it a flag byte after the payload (16 bytes), stored with `Zig.Enc.optionWith Zig.nullablePtrEnc` (`nullableSliceEnc`). `is_null`, `optional_payload`, `wrap_optional`, `==`, `is_null_ptr`/`optional_payload_ptr(_set)` (`Zig.optIsSome`/`optSetSome` on the flag) are the ordinary optional rules. `?*u8` → `?*allowzero u8` is Sema's payload cast then `wrap_optional`, so `null` becomes `some` of address zero (native runs agree). A `@ptrCast` or `@ptrFromInt` to or from it is rejected: Zig miscompiles it ([upstream draft](upstream/optional-nullable-casts.md)). |
| Nullable pointers in unions, tuples and error-union payloads | The generated union `Enc`, the error-union dictionary (`Zig.Enc.errorUnionWith`, `Zig.errorUnionEnc`) and tuple values select `Zig.nullablePtrEnc` per payload; values are ordinary `Zig.Ptr`. Tuples have no memory encoding yet (any tuple in memory is rejected, not only a nullable one); a tuple local (`ret_ptr`, `struct_field_ptr`) is a value of nested pairs. Packed aggregates of pointers stay outside the subset. |
| Nullable slice `[]allowzero T` | `⟨ptr, len⟩` with a possibly-null `ptr`, stored with `Zig.nullableSliceEnc` (the pointer half is `nullablePtrEnc`). `slice`, `array_to_slice` (`*allowzero [n]T`), `slice_ptr`, `slice_len`, item reads and item pointers are the ordinary slice rules: an item access through address zero is `.illegal` (`Mem.access`), forming item 0 is address zero, a nonzero item offset from it is `.illegal`. A cast between a nullable and another slice type is rejected; a nullable slice is never a pure `Array` parameter. |
| Slicing a C pointer `p[a..b]` into `[]T` | Sema emits `ptr_add(p, a)`, the bounds check, the null check (`unwrapNull`, a panic) and `slice`. Canonicalization moves the start projection past the checks to its use (`sinkPastChecks`, `Air2Lean/Air/Canon.lean`, for every pointer formation that a safety check separates from its first use): an out-of-allocation `getelementptr inbounds` is poison, illegal only when used, and the native program panics on a null `p` with any start (native runs agree). The slice's pointer must not be address zero (`Zig.ptrNonnull`, `.illegal` when no check precedes). |
| Bulk memory (`@memset`, `@memcpy`) through nullable slices or C-pointer slices | The ordinary `Zig.memset`/`Zig.memcpy`: zero items touch nothing, also at address zero (`null_memset_empty`, `null_memcpy_empty`; LLVM's `memset`/`memcpy` with length 0 are no-ops); a positive count through address zero is `.illegal` (native: a segmentation fault, no safety check). A C-pointer operand is first sliced (`p[0..n]`), whose null check panics. |
| `@fieldParentPtr` through `*allowzero F` | Pointer formation `ptrProject p (·.add (-offset))` (LLVM: `ptrtoint`, `sub nuw`, `inttoptr`): offset 0 from address zero is address zero; a nonzero field offset from address zero is `.illegal` (`null_field_parent`; `sub nuw` wraps, native code returns `2^64 - offset`); from a provenance-free nonzero address it is `.illegal` under SEM-02 (no object outside the model's blocks). A `[*c]F` operand must be cast to `*allowzero F` first (a Sema rule). |

Null tests are address observations. They do not promise a zero-address object or
MMIO semantics. A raw nonzero integer pointer also fails access until it has valid
block provenance. The model does not change its allocator or the global `Enc Ptr` and
`Enc (Option Ptr)` encodings; the null-byte storage rule is an explicit dictionary bound
only at C/allowzero storage sites.

The checker still rejects nullable bit-pointers and volatile nullable pointers, packed
aggregates of pointers, conversions between a nullable pointer and an optional slice,
`wrap_optional` of a nullable operand into an ordinary `?*T` (Sema emits a `bitcast` with null
mapping instead), casts to or from an optional of a nullable pointer, and casts between a
nullable slice and another type. Each is a fail-closed diagnostic.

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
| `&p.*.first` (offset 0), `p + 0`, `&p[0]`, `p - 0` from a null `[*c]T` | defined, address 0 (ReleaseSafe and Debug); Zig 0.17.0 checks `&p.*.f` of a C pointer (`is_non_null` in the AIR) and panics (`attempt to use null value`) | `Ptr.null` (0.14.1/0.15.2 `&p.*.first`, typed `*F`: `.illegal`; 0.17.0 `&p.*.f`: `.panic`) |
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

## Address-zero projection policy

The model follows each version's analyzed AIR; at address zero it says:

| Projection from address zero | Model | Why |
| --- | --- | --- |
| offset 0 into a nullable result (`[*c]`, `allowzero`) | address zero | no `getelementptr` is emitted; native runs agree |
| offset 0 into a nonnullable result (0.14.1/0.15.2 `&p.*.f` typed `*F`) | `.illegal` | a non-`allowzero` pointer must not be zero (illegal behaviour that no check catches: the compiler mistypes the field pointer, 0.16.0 keeps `allowzero`) |
| a field of a null C pointer in 0.17.0 | `.panic` | Sema's `is_non_null` safety check, translated |
| any nonzero offset | `.illegal` | `getelementptr inbounds` without an allocated object is poison; the native ReleaseSafe build folds `(p + n) == null` to `p == null` (`addIsNull`) |

These are not over-approximations of the native result but the language's and the backend's
verdict: the two `.illegal` rows are illegal behaviour that ReleaseSafe does not check, so a native
run shows an address (0) where the model reports `.illegal`. Native diffs and outcome reports treat
them as pinned illegal-behaviour exclusions (`native-transcript.py` maps exactly the two
0.14.1/0.15.2 field-pointer lines `allowzeroNextPtr 0` and `nullNextPtr 0` to `illegal`), never as
agreement or as a mismatch.

## Provenance-free nonzero addresses (MMIO)

A nonzero offset from a nonzero address without a block (`@ptrFromInt` of an address no block
covers, a memory-mapped register block) is `getelementptr inbounds` of an inttoptr pointer: it is
defined only inside an object allocated there, which LLVM may assume of memory outside the
module. Which objects exist outside the model is a fact about the environment, so the model makes
it an explicit premise rather than an over-approximation: premise
[SEM-02](premises.md#sem-02) states that the model's memory holds no allocated object other than
its blocks and, with `--device-contract`, the declared register window (DEV-01). Under it the
projection is exactly `.illegal`: offset 0 is the pointer itself; inside the declared window it
is formed (`Zig.ptrProjectDevice`); any other offset has no object. A program that uses other
external memory must declare it (today: as the device window); otherwise its theorems do not
cover that access. Native evidence: on the reference hosts the low addresses (Linux
`mmap_min_addr` 64 KiB, macOS `__PAGEZERO` 4 GiB) hold no object, and ReleaseSafe folds
`(@ptrFromInt(2^64 - 4) + 4) == null` (`mmioIsNull`) to `false`, although address arithmetic
gives 0: the backend treats the out-of-object offset as poison. `@fieldParentPtr` of such an
address is the same rule.

## Fresh exports and native observations

`tests/roadmap/null-pointers/air/<version>` and `air-reject/<version>` are the exports of
`nullpointers.zig` (47 roots) and `reject.zig` by patched 0.17.0, 0.16.0, 0.15.2 and 0.14.1
compilers (x86_64-linux, baseline, ReleaseSafe; `export.sh`, `provenance.json`,
`test_provenance.py`; `COMPILER_FIXTURE_ROOTS`). `check.sh` translates each version, runs the
model on the native `main`'s inputs and compares with `expected/<version>.txt` (39 native `main`
lines, four `case` lines and two model-only lines), and checks both rejection roots of each
version (`optionalCast`, a cast of `?*allowzero u8`; `fixed`, a nonzero constant address).
`check.sh --native ZIG` runs `nullpointers.zig` with a stock Zig, then one variant per `case`
(`const case = "<name>";`; each ends the process): a C-pointer slice and a C-pointer `@memset` of
address zero (`sliceCNull`, `memsetCNull`: the null-check panic, also with a nonzero start), an
unwrap of a null `?*allowzero u8` (`optUnwrapNull`: panic) and a one-item `@memset` through a
null `[]allowzero u8` (`memsetAzNull`: a segmentation fault, illegal behaviour that no check
catches, recorded as `illegal`). It compares the transcript with the same file. It passed for
stock 0.14.1, 0.15.2, 0.16.0 and 0.17.0 on x86_64-linux (linux/amd64 container) and
aarch64-linux (linux/arm64 container), and for 0.15.2, 0.16.0 and 0.17.0 on aarch64-macos (stock
0.14.1 does not link on this macOS), 43 lines each. The 0.17.0 `main` ends with the null-field
panic, its last line. The model-only lines are illegal behaviour that native code runs without a
check: a nonzero start from a null `[*]allowzero u8`, `@fieldParentPtr` of a nonzero field offset
from address zero and from a provenance-free address, a one-item `@memset` at address zero, and
a nonzero offset from `@ptrFromInt(4096)` (SEM-02). `check.sh --export [VERSIONS]` checks that
a patched compiler reproduces the committed export.

## Proof and regression evidence

`ZigLean/Mem/Null.lean` contains universal theorem definitions `null_access`,
`nullable_from_zero`, `null_is_null`, `null_unwrap`, `raw_address_access`,
`null_project_zero` (an offset-0 projection from address zero is defined), `null_project`
(any other projection from it is `.illegal`), `null_project_nonnull` (into a nonnullable
result type every projection from it is `.illegal`), `null_offset_access`, `null_to_optional`,
`optional_none_to_null`, `null_memset_empty`, `null_memcpy_empty` (zero items at address zero
touch nothing), `null_nonnull` and `null_field_parent`.
The direct-access validity premises reuse `ZigLean/Mem/Lemmas.lean`'s existing
`access_of`/`access_eq` rules. A nonnull check cannot discharge those premises.

The proof-only module `ZigLean/Mem/NullLemmas.lean` (outside the `ZigLean` runtime
umbrella, because it imports `ZigLean.Mem.Lemmas`; build it with
`lake build ZigLean.Mem.NullLemmas`) proves `nullablePtrEnc_lawful` (so the generic
`load_store_same`/`store_run` rules apply to stored C pointers), the representation match
`nullablePtrEnc_encode_eq_optional`, `nullablePtrEnc_decode_zero`, `load_store_null`,
`ptrProjectNonnull_ok`, `projected_access_block` (an access through any projection
succeeds only in a live block of the base's own provenance), `ptrOfOptional_toOptional`,
`nullableSliceEnc_lawful` and `nullableSliceEnc_encode_null`.

`tests/roadmap/null-pointers/Generate.lean` adds thirty hand-written AIR cases matching the
exporter schema: stored C and allowzero pointers (null bytes, round trips, zero-byte and
undefined-byte reads), extern-struct field loads and field pointers at offsets 0 and 8 (also from
an `allowzero` base) and a struct round trip with a null field, an array item,
`ptr_add`/`ptr_sub`/`ptr_elem_ptr`/`ptr_elem_val` from a C or `allowzero` base at offsets 0 and
nonzero, a field pointer typed nonnullable as 0.14.1/0.15.2 export it, both optional
conversions, a stored `?*allowzero u8` (`none` versus `some` of address zero, the flag byte,
`is_null_ptr`), a C pointer sliced without a check (`Zig.ptrNonnull`), `@memset` and a stored
`[]allowzero u8`, `@fieldParentPtr` from address zero, and an extern union and an error union of
a C pointer. Each checks the emitted helper and elaborates its `native_decide`
regressions; adjacent rejections cover the still-restricted forms above. The same operations
are also compiler-exported and compared natively (below).
Theorems apply to this model, with its existing compiler/export/normalization
trust boundary; they are not AIR/backend preservation theorems.

The driver needs no compiler in its default mode:

```sh
lake build ZigLean air2lean ZigLean.Mem.NullLemmas
tests/roadmap/null-pointers/check.sh                  # offline cases, mutant, 4 versions' exports
tests/roadmap/null-pointers/check.sh --native ZIG     # a stock Zig on this host
AIR2LEAN_ZIG_AIR=<dir of zig-air-<version>> tests/roadmap/null-pointers/check.sh --export [VERSIONS]
```

It builds the runtime and translator, elaborates thirty generated semantic cases, kills an
inverted-null-predicate mutant, translates the committed exports of every version and compares
the model's lines with `expected/<version>.txt` (§Fresh exports), and checks the two rejection
roots of each version. The six integer inputs include zero, small addresses and the maximum 64-bit address.
Native dereference is exercised only with a live byte; invalid provenance and dead-block access
are tested in the model. The `addIsNull` line records `illegal` natively because the ReleaseSafe
build answers `true` for `(null + 1) == null`, which address arithmetic would answer `false`; it
depends on LLVM's fold and is a witness, not a proof, of the undefined case.

`native_decide` occurs only in generated regression fixtures, following the existing emitter-test
convention. The shipped universal theorem definitions (fifteen in `Null.lean`, fifteen in
`NullLemmas.lean`) use kernel reductions and do not use `native_decide`, `sorry`, `admit` or
axioms. CI runs the default mode, `--export 0.16.0` with that job's patched compiler and
`--native` with its stock 0.16.0 on x86_64-linux. The deliberately rejected operations above stay
fail-closed; finite observations are not a preservation theorem.

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
