# C and allowzero pointer fragment (L05)

Nonoptional scalar `[*c]T`, `*allowzero T` and `[*]allowzero T` values use `Zig.Ptr`.
Address zero is `Zig.Ptr.null = ⟨none, 0⟩`: no block and no allocation. The reference
scope is the existing 64-bit little-endian, ReleaseSafe AIR model. This fragment
is deliberately smaller than complete C/allowzero pointer support.

| Operation | Rule |
| --- | --- |
| Runtime integer → nullable pointer | `ptrFromAddrNullable 0` returns null without changing memory. Nonzero addresses use existing `ptrFromAddr` block-range resolution. |
| Pointer → integer | `ptrAddr` observes the address; it does not dereference or revive a dead allocation. |
| Null/non-null value tests | `ptrIsNull` compares the address with zero. It does not interpret a scalar pointer as `Option Ptr`. |
| Nullable pointer equality/inequality | `ptrEqAddr` compares addresses, including zero. |
| Nullable → nonnullable scalar pointer cast; C `p.?` | `ptrRequireNonNull` rejects zero with `.panic` and preserves a nonzero pointer. Being nonnull does not establish provenance, lifetime, bounds or alignment. |
| Direct load/store through a scalar nullable pointer | The existing `Mem.access`/`accessW` rules apply. Positive-size accesses require a real live block, bounds and alignment; stores also require writable storage. Source AIR safety guards remain part of the translation. |
| Zero pointer constant | An explicit `ptr: {"null": true, "off": 0}` becomes `Val.ptrNull`; the checker requires a C/allowzero type. Other integer-base constants remain rejected. |

Null tests are address observations. They do not promise a zero-address object or
MMIO semantics. A raw nonzero integer pointer also fails access until it has valid
block provenance. The model does not change its allocator or pointer encodings.

The checker still rejects nullable pointer values stored in memory, nullable
pointers in value aggregates/error-union payloads, `?[*c]T` and `?*allowzero T`,
nullable slices/bit-pointers/volatile pointers, implicit conversion to an ordinary
optional pointer, and nullable pointer indexing/arithmetic/projections/slice
construction. Use a checked nonnullable cast before the existing projection rules.
These restrictions prevent the ordinary `Enc (Option Ptr)` null representation
from conflating an outer optional's `none` with a nullable payload's zero value.
They also avoid claiming that opaque pointer fragments model nullable zero bytes.

Compiler source inspection of 0.14.1, 0.15.2 and 0.16.0 establishes the relevant
representation boundaries: `InternPool.Key.Ptr.BaseAddr.int` carries no payload;
the integer address is in `byte_offset`. `Type.optionalReprIsPayload` excludes
C/allowzero children from ordinary optional-pointer payload representation.
C null tests lower to `is_null`/`is_non_null`, and the C-pointer payload operation
retains the scalar C-pointer type (`Sema.zirOptionalPayload`). These source facts
are not new compiler-execution or preservation evidence.

## Proof and regression evidence

`ZigLean/Mem/Null.lean` contains universal theorem definitions `null_access`,
`nullable_from_zero`, `null_is_null`, `null_unwrap`, and `raw_address_access`.
The direct-access validity premises reuse `ZigLean/Mem/Lemmas.lean`'s existing
`access_of`/`access_eq` rules. A nonnull check cannot discharge those premises.
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
checks synthetic schema/checker rejections, elaborates nine generated semantic
cases, kills an inverted-null-predicate mutant, exports fresh compiler-generated
fixtures, compares eight native/Lean observation lines, and checks two separate
compiler-generated rejection roots. The six integer inputs include zero, small
addresses and the maximum 64-bit address. Native dereference is exercised only
with a live byte; invalid provenance/dead-block access is tested in the model.

`native_decide` occurs only in generated regression fixtures, following the
existing emitter-test convention. The five shipped universal theorem definitions
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
for nullable storage, nested representations and the other deliberately rejected
operations above; eight finite observations are not a preservation theorem.

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
