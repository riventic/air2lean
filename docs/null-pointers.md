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
| Nullable → nonnullable scalar pointer cast; C `p.?` | `ptrRequireNonNull` rejects zero with `.illegal` (illegal behaviour that the op checks itself; Sema's null check before it is ordinary AIR and panics first) and preserves a nonzero pointer. Being nonnull does not establish provenance, lifetime, bounds or alignment. |
| Direct load/store through a scalar nullable pointer | The existing `Mem.access`/`accessW` rules apply. Positive-size accesses require a real live block, bounds and alignment; stores also require writable storage. Source AIR safety guards remain part of the translation. |
| Zero pointer constant | An explicit `ptr: {"null": true, "off": 0}` becomes `Val.ptrNull`; the checker requires a C/allowzero type, also inside an aggregate constant. Other integer-base constants remain rejected. |
| Nullable pointer stored in memory (`*[*c]T`, global, escaping local) | Load/store of the pointer value itself use the storage dictionary `Zig.nullablePtrEnc`: `Ptr.null` is eight zero integer bytes (the bytes of a null `?*T`); other pointers, including one that reaches address zero by arithmetic on its provenance, keep their provenance fragments. Zero bytes from any source read back as null; undefined or other integer bytes stay `.unspecified`. The access premises are those of the storage location, never of address zero. |
| C/allowzero pointers in extern/auto structs and arrays | The generated struct `Enc` and `Zig.Enc.vectorWith` select `Zig.nullablePtrEnc` per field/item; values of these aggregates are ordinary Lean structures/vectors of `Zig.Ptr`. |
| Projection from a C/allowzero base (`struct_field_ptr`, `ptr_elem_ptr`, `ptr_add`, `ptr_sub`) | The checked pointer formation of every derived pointer, `ptrProject p project` (MM-3, `docs/architecture-audit/memory-model.md`): the same pointer is always allowed, so an offset-0 projection from address zero is defined (the compiler emits no `getelementptr`); any other result is `.illegal` unless base and result lie in bounds of the base's block, so a nonzero offset from address zero or another provenance-free address is `.illegal` (`getelementptr inbounds` poison). When the result type is nonnullable (0.14.1 and 0.15.2 type `&p.*.f` of a `[*c]T` as `*F`), `ptrProjectNonnull` also rejects address zero. The result keeps the base's provenance, so any access through it still needs the existing live-block/bounds/alignment premises. |
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
| `&p.*.first` (offset 0), `p + 0`, `&p[0]`, `p - 0` from a null `[*c]T` | defined, address 0 (ReleaseSafe and Debug); Zig 0.17.0 checks `&p.*.f` of a C pointer (`is_non_null` in the AIR) and panics (`attempt to use null value`) | `Ptr.null` (0.14.1/0.15.2 `&p.*.first`, typed `*F`: `.illegal`; 0.17.0 `&p.*.f`: `.panic`) |
| the same from `*allowzero T`/`[*]allowzero T` at address 0 | defined, address 0 | `Ptr.null` (0.14.1/0.15.2 `&p.first`, typed `*F`: `.illegal`) |
| nonzero field offset, `p + n`, `&p[n]`, `p - n` (n ≠ 0) from address zero, C or `allowzero` | not address arithmetic: ReleaseSafe folds `(p + n) == null` to `p == null` (also for `allowzero`; 0.14.1 even in a `null_pointer_is_valid` function); Debug happens to yield `0 + offset` | `.illegal` |
| load/store through a projection of address zero (C or `allowzero`) | segmentation fault; no safety check in ReleaseSafe or Debug (the langref calls a C-pointer dereference of address 0 safety-checked on hosted targets; these compilers emit no check) | `.illegal` (`Mem.access`) |
| `p.?` of a null `[*c]T` or `?*T`; `[*c]T` → `*T` coercion of null | safety panic (`attempt to use null value`, `cast causes pointer to be null`) | `.panic` (Sema's check, translated as AIR); the op alone, without the check: `.illegal` |

The model is therefore exact for the defined cases and `.illegal` exactly where the backend
treats the projection as undefined (LLVM poison) or the access faults, with one conservative
exception: Zig 0.14.1 and 0.15.2 type an offset-0 field pointer of address zero as a
nonnullable `*F` (`ptrProjectNonnull`), and the model makes it `.illegal` although the native
code yields address zero; whether later uses of that `*F` are defined is not confirmed natively. An `allowzero` object at
address zero (freestanding targets) is not modelled: a projection that would need it fails closed.
The theorems `null_project_zero`, `null_project`, `null_project_nonnull` and
`null_offset_access` (`Null.lean`) and `ptrProjectNonnull_ok` (`NullLemmas.lean`) state the rule.

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
agreement or as a mismatch. The one remaining over-approximation is a nonzero offset from a nonzero
provenance-free address (MMIO, a `@ptrFromInt` register window) outside a declared
`--device-contract` window (L13/DEV-01, `docs/architecture-audit/memory-model.md` MM-3); it is
not about address zero.

## Fresh exports and native observations

`tests/roadmap/null-pointers/air/<version>` and `air-reject/<version>` are the exports of
`nullpointers.zig` (24 roots) and `reject.zig` by patched 0.17.0, 0.16.0, 0.15.2 and 0.14.1
compilers (x86_64-linux, baseline, ReleaseSafe; `export.sh`, `provenance.json`,
`test_provenance.py`; `COMPILER_FIXTURE_ROOTS`). `check.sh` translates each version, runs the
model on the native `main`'s inputs and compares with `expected/<version>.txt` (26 native lines
and one model-only line of the nonzero offsets from address zero), and checks both rejection roots
of each version. `check.sh --native ZIG` runs `nullpointers.zig` with a stock Zig and compares its
transcript with the same file. It passed for stock 0.14.1, 0.15.2, 0.16.0 and 0.17.0 on
x86_64-linux (linux/amd64 container) and aarch64-linux (linux/arm64 container), and for 0.15.2,
0.16.0 and 0.17.0 on aarch64-macos (stock 0.14.1 does not link on this macOS). The 0.17.0 run ends
with the null-field panic, its last line. `check.sh --export [VERSIONS]` checks that a patched
compiler reproduces the committed export.

## Proof and regression evidence

`ZigLean/Mem/Null.lean` contains universal theorem definitions `null_access`,
`nullable_from_zero`, `null_is_null`, `null_unwrap`, `raw_address_access`,
`null_project_zero` (an offset-0 projection from address zero is defined), `null_project`
(any other projection from it is `.illegal`), `null_project_nonnull` (into a nonnullable
result type every projection from it is `.illegal`), `null_offset_access`, `null_to_optional`
and `optional_none_to_null`.
The direct-access validity premises reuse `ZigLean/Mem/Lemmas.lean`'s existing
`access_of`/`access_eq` rules. A nonnull check cannot discharge those premises.

The proof-only module `ZigLean/Mem/NullLemmas.lean` (outside the `ZigLean` runtime
umbrella, because it imports `ZigLean.Mem.Lemmas`; build it with
`lake build ZigLean.Mem.NullLemmas`) proves `nullablePtrEnc_lawful` (so the generic
`load_store_same`/`store_run` rules apply to stored C pointers), the representation match
`nullablePtrEnc_encode_eq_optional`, `nullablePtrEnc_decode_zero`, `load_store_null`,
`ptrProjectNonnull_ok`, `projected_access_block` (an access through any projection
succeeds only in a live block of the base's own provenance) and `ptrOfOptional_toOptional`.

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

The driver needs no compiler in its default mode:

```sh
lake build ZigLean air2lean ZigLean.Mem.NullLemmas
tests/roadmap/null-pointers/check.sh                  # offline cases, mutant, 4 versions' exports
tests/roadmap/null-pointers/check.sh --native ZIG     # a stock Zig on this host
AIR2LEAN_ZIG_AIR=<dir of zig-air-<version>> tests/roadmap/null-pointers/check.sh --export [VERSIONS]
```

It builds the runtime and translator, elaborates twenty-seven generated semantic cases, kills an
inverted-null-predicate mutant, translates the committed exports of every version and compares
the model's lines with `expected/<version>.txt` (§Fresh exports), and checks the two rejection
roots of each version (`optional`, a stored `?*allowzero u8`; `fixed`, a nonzero constant
address). The six integer inputs include zero, small addresses and the maximum 64-bit address.
Native dereference is exercised only with a live byte; invalid provenance and dead-block access
are tested in the model. The `addIsNull` line records `illegal` natively because the ReleaseSafe
build answers `true` for `(null + 1) == null`, which address arithmetic would answer `false`; it
depends on LLVM's fold and is a witness, not a proof, of the undefined case.

`native_decide` occurs only in generated regression fixtures, following the existing emitter-test
convention. The shipped universal theorem definitions (eleven in `Null.lean`, thirteen in
`NullLemmas.lean`) use kernel reductions and do not use `native_decide`, `sorry`, `admit` or
axioms. CI runs the default mode, `--export 0.16.0` with that job's patched compiler and
`--native` with its stock 0.16.0 on x86_64-linux. Full L05 remains open for optionals of nullable
pointers, nullable pointers in unions/tuples/error-union payloads, nullable bulk
memory/slicing/parent recovery, and the other deliberately rejected operations above; finite
observations are not a preservation theorem.

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
