# Illegal behaviour inventory

This page lists every illegal behaviour (IB) in the Zig 0.16.0 language reference
(§Illegal Behavior and the builtin pages that name one) and the safety checks in
`src/Sema.zig`. For each one it gives what a ReleaseSafe build does and what the model does.

**Rule.** Every op's model checks its own illegal-behaviour precondition. It throws `.illegal`
whether or not a Sema safety check comes before it. A Sema check is ordinary AIR: a
`cond_br` to a panic-handler call, which the model translates like any other branch. With
safety on, the check panics first, so ReleaseSafe outcomes do not change. Without the check
(`@setRuntimeSafety(false)`, ReleaseFast, ReleaseSmall, or IB that Sema never checks), the
op's own check gives `.illegal`. The model never returns a value for an input with IB. A
proof that a function never throws is then also a proof that it has no IB on those inputs
([build-modes.md](build-modes.md)).

The outcomes are `Zig.Error` constructors ([outcome-taxonomy.md](outcome-taxonomy.md)):

- `panic ctor`: a Sema check that fires (`.overflow`, `.outOfBounds`, `.divByZero`,
  `.unreachable`, `.panic`), from the handler table in `Air2Lean/Air/Op.lean`
  (`panicErrorFor?`).
- `.illegal`: IB that no check catches (outcome `illegal_behavior`).
- `.unspecified`: Zig leaves the result open. This is not IB.
- *rejected*: the translator refuses the function.

"Safe AIR" is the analyzed AIR of a ReleaseSafe build, which is what the translator reads.
"Unsafe AIR" is the same op with no check before it: code under `@setRuntimeSafety(false)`,
or IB that Sema does not check. Rows marked **fixed** changed on this branch.

## Safety-checked IB

| # | Illegal behaviour | ReleaseSafe check (handler) | Model, safe AIR | Model, unsafe AIR |
| --- | --- | --- | --- | --- |
| 1 | Reaching `unreachable` | `reachedUnreachable` | `.unreachable` | bare `unreach`: `.illegal` (**fixed**, was `.unreachable`) |
| 2 | Index out of bounds: array, slice | `outOfBounds` | `.outOfBounds` | pure `Zig.index`/`Zig.vindex`: `.outOfBounds`. Memory `slice_elem_val`: `Zig.checkIndex` (the sentinel item of `[:s]T` included), `.illegal` (**fixed**, was a value when the item lay inside the block) |
| 3 | Index out of bounds: many-item pointer | none (no length) | `Mem.access`: `.illegal` outside the allocation | same |
| 4 | Slice start greater than end | `startGreaterThanEnd` | `.outOfBounds` | the length `sub` overflows: `.overflow` |
| 5 | Slice end past the length | `outOfBounds` | `.outOfBounds` | `Zig.checkSliceEnd` on `slice(ptr_add(base, start), len)`, where `base` is a slice's `slice_ptr` or an array pointer: `.illegal` (**fixed**, was a slice past the operand). A many-item pointer has no length, so its slicing has no bound to break |
| 6 | Cast negative to unsigned / cast truncates data (`@intCast`) | `integerOutOfBounds` | `.overflow` | `intcast`: `Zig.intCast`, `.overflow` |
| 7 | Integer overflow (`+ - *`, negation, `/`, `@divTrunc`, `@divFloor`, 0.17.0 `@divCeil` of `minInt / -1`) | `integerOverflow`, `*_safe` tags | `.overflow` | plain `add`/`sub`/`mul`, `div_trunc`/`div_floor`/`div_ceil`: `.overflow` |
| 8 | Division by zero (integers) | `divideByZero` | `.divByZero` | `.divByZero` |
| 9 | Remainder division by zero (integers) | `divideByZero` | `.divByZero` | `.divByZero` |
| 10 | Exact division remainder (integers) | `exactDivisionRemainder` (Sema emits `div_trunc` and `rem`) | `.panic` | `div_exact`: `Zig.divExact`, `.illegal` for a remainder, a zero divisor and `minInt / -1` (**fixed**, was `.panic`/`.divByZero`/`.overflow`) |
| 11 | Exact division remainder (floats) | `exactDivisionRemainder`, catches a NaN quotient only | NaN: `.panic`. Any other inexact quotient: `Zig.Float.divExactTrunc`, `.illegal` (**fixed**, was the truncated quotient) | `div_exact`: `Zig.Float.divExactChk`, `.illegal`, NaN included (**fixed**, was the quotient) |
| 12 | Exact left shift overflow (`@shlExact`) | `shlOverflow` (Sema emits `shl_with_overflow`) | `.overflow` | `shl_exact`: `Zig.shlExact`, `.illegal` (**fixed**, was `.overflow`) |
| 13 | Exact right shift overflow (`@shrExact`) | `shrOverflow`, after the `shr_exact` | `Zig.shrExact`: `.overflow` | `.overflow` |
| 14 | Shift amount ≥ bit width (`<<`, `>>`, `@shlExact`, `@shrExact`), width not a power of two | `shiftRhsTooBig` | `.overflow` (the safety handler, L02; a shift whose count that check guards is total, since Sema may emit it before the check: `FCtx.shiftCountGuarded`) | `Zig.shlChk`/`Zig.shrChk`/`Zig.shlExact`/`Zig.shrExact`: `.illegal` (**fixed**, was `0` or the shifted bits) |
| 15 | Attempt to unwrap null | `unwrapNull` | `.panic` | `Zig.optPayload`, `Zig.optPtrUnwrap`: `.panic` |
| 16 | Attempt to unwrap error | `unwrapError` | `.panic` | `Zig.unwrapPayload`: `.panic` |
| 17 | Invalid error code (`@errorFromInt`) | `cmp_lte_errors_len` | *rejected* (normalizer) | *rejected*: raw error representation casts |
| 18 | Invalid enum cast (`@enumFromInt`) | `invalidEnumValue` | `.panic` | `Zig.enumOf`: `.panic` |
| 19 | Invalid error set cast (`@errorCast`) | `error_set_has_value` | *rejected* (exporter) | error set: `Zig.errorIn`, `.illegal` (**fixed**, was the error). Error union: *rejected* with or without safety (the checker refuses a `bitcast` between error unions of different sets; probes `errorCastUnionSafe`, `errorCastUnionUnsafe`) |
| 20 | Incorrect pointer alignment (`@alignCast`, `@ptrFromInt`) | `incorrectAlignment` | `.panic` | `Zig.checkAlign`, `Zig.checkAddr`: `.illegal` (**fixed**, was the pointer) |
| 21 | Wrong union field access (tagged, bare) | `inactiveUnionField` | `.panic` | `U.get_f`: `.panic` |
| 22 | Out-of-bounds float to integer (`@intFromFloat`, and `@floor`/`@ceil`/`@trunc`/`@round` to an integer) | `integerPartOutOfBounds`, false for a NaN | `.overflow`; NaN: `.illegal` (**fixed**, was `.unspecified`) | `int_from_float`: `.illegal` (**fixed**, was `.unspecified`) |
| 23 | Pointer cast invalid null (`@ptrFromInt(0)`, `?*T` or `[*c]T` to `*T`) | `castToNull` | `.panic` | `@ptrFromInt`: `Zig.checkAddr`, `.illegal` (**fixed**, was an address-zero pointer). Optional and C pointers: `.panic` |
| 24 | Sentinel mismatch (sentinel slicing) | `sentinelMismatch` | `.panic` | `u8` sentinel on 0.16.0 (the export records its value): `Zig.checkSentinelByte`, and the sentinel item must lie in the operand, `.illegal` (**fixed**, was a value). Any other sentinel without Sema's check: *rejected* (**fixed**) |
| 25 | `@memcpy` arguments of unequal length | `copyLenMismatch` | `.panic` | `Zig.memcpy`: `.illegal` (**fixed**, was `Zig.memmove` with the destination's count) |
| 26 | `@memcpy` arguments alias | `memcpyAlias` | `.panic` | `Zig.memcpy`: `.illegal` (**fixed**, was `Zig.memmove`) |
| 27 | `for` over operands of unequal length | `forLenMismatch` | `.panic` | Sema compares the lengths only with safety on; without it the AIR need not hold any operand length but the loop's own (a range `0..n` has no instruction). The patched Sema (`zig-patch/<version>/hook.patch`, every supported version) emits the same comparison as `if (!ok) unreachable`, and the export lists `for_len` in `unchecked_ib`; the bare `unreach` is `.illegal` (**fixed**, slices, ranges and arrays). A function with a loop in an export without that fact is rejected (`Check.checkForLenFact`) |
| 28 | `@tagName` of an unnamed non-exhaustive enum value | `invalidEnumValue` (via `is_named_enum_value`) | `.panic` | `E.tagName`: `.illegal` (**fixed**, was `.panic`) |
| 29 | Switch on a corrupt value | `corruptSwitch` | `.panic` | every model enum value is named; no corrupt value exists |
| 30 | A `noreturn` function returns | `noreturnReturned` | *rejected* (handler outside the table) | — |
| 31 | `@ptrCast` of a slice whose length does not divide | `sliceCastLenRemainder` | *rejected* | — |

## IB that ReleaseSafe does not check

| # | Illegal behaviour | Model |
| --- | --- | --- |
| 32 | Inexact float `@divExact` with a non-NaN quotient (row 11) | `.illegal` (**fixed**) |
| 33 | `@intFromFloat` of a NaN (row 22) | `.illegal` (**fixed**) |
| 34 | `@shlWithOverflow` count ≥ bit width (width not a power of two) | `Zig.shlWithOverflow`: `.illegal` |
| 35 | `@rem`/`@mod` of `minInt` by `-1` | `Zig.rem`/`Zig.mod`: `.illegal` |
| 36 | `@ptrCast` between a vector and another pointee (langref §Vectors: no defined byte layout) | *rejected* (**fixed**, was a value read with array layout) |
| 37 | Access to a freed or dead block (use after free, stack pointer after return), out of bounds or misaligned; double free; write to a `const` global | `Mem.access` and the allocator: `.illegal` |
| 38 | Loading an invalid `bool`, enum tag or packed-struct field pattern | `Enc` decode and `Packed.ofBits?`: `.illegal` |
| 39 | Data race | the race check of `ZigLean/Mem/Basic.lean`: `.illegal` |
| 40 | `@fieldParentPtr` of a pointer that is not to that field (parent without a defined layout) | local places: the checker requires the proven field. Memory: `Zig.checkParent`, the parent must be a live, aligned object of its size in the field pointer's block, `.illegal` (**fixed**, was a value). `extern`/`packed` parents: defined arithmetic, a value |
| 41 | Inline assembly with undeclared clobbers | premises [ASM-01](premises.md#asm-01), [ASM-02](premises.md#asm-02) |
| 42 | Branch on, or arithmetic with, `undefined` | `undefined` constant operands are *rejected*. A load of undefined bytes throws `.unspecified`, earlier than the IB |
| 43 | A `noalias` parameter's memory also accessed through another pointer during the call, one access a write ([below](#noalias-parameters)) | `Zig.naMark`: `.illegal` (**fixed**, was the value of the call). A function whose roots the translator cannot tell: *rejected* |

## noalias parameters

**Rule.** The language reference has no text for `noalias` ("TODO add documentation for
noalias" in 0.15.2, 0.16.0 and 0.17.0, 0.14.1 likewise). Sema records it as a bit of the
function type (`noalias_bits`: the first 32 parameters; "non-pointer parameter declared
noalias" for any other type), and the LLVM backend lowers each set bit to LLVM's `noalias`
argument attribute: on a pointer parameter, and on the pointer of a slice parameter
(`src/codegen/llvm.zig` `addByValParamAttrs` and the `.slice` lowering; the call-site attributes
in `src/codegen/llvm/FuncGen.zig`), in 0.14.1 to 0.17.0 alike. So the rule is LLVM's: during the
execution of the call, memory accessed through a pointer *based on* the parameter is not also
accessed through a pointer not based on it, if either access writes. Violating it is undefined
behaviour; no Zig safety check exists. A parameter of an `inline fn` has no attribute (Sema
inlines the body), so only a called function's own parameters count. `@memcpy`'s `noalias` is a
separate rule (row 26).

**Model.** The exporter writes each function's `noalias` parameter indices (`docs/air-json.md`).
For a function that has some and uses memory, `Air2Lean/Noalias.lean` computes the *root* of
every access: the parameter the pointer is based on (LLVM's rules: a derived pointer is based
on its base, `@ptrFromInt` on the pointers of its integer), or none. The generated function
opens a scope (`Zig.naEnter`) and follows each instruction that can touch memory with the mark
of its roots (`Zig.naMark`, `ZigLean/Mem/Noalias.lean`). The mark checks that instruction's
accesses at once against the scope's log and logs them: an access that overlaps a logged one
with another root, one of the two a write, throws `.illegal`. Every function that such a
function may call marks its own accesses the same way (root none), so a conflict inside a
callee is found there too. No later failure (an overflow, a safety panic, a callee's error) can
take the place of the violation. One instruction is the unit: a load whose read conflicts and
whose bytes are undefined throws `.unspecified` from its own decode before its mark (the
conflicting write must then have stored `undefined`), and a model function that records an
access and then fails in the same call keeps its failure.

**Rejected.** The translator rejects (fail closed) a function with `noalias` parameters in which
a value based on one reaches memory or another function (a store, an atomic or `memset`
operand, a call or asm argument, a copy out of a local that holds one): a pointer read back or
the callee's accesses could then be based on the parameter unseen. It also rejects an access
whose pointer may be based on more than one of a parameter and another pointer
(`if (c) p else q`), and a concurrent (`Zig.ConcM`) function with `noalias` parameters. A
function with `noalias` parameters that uses no memory needs no scope: it writes nothing.

`tests/roadmap/noalias/check.sh`: a `memcpy`-like copy (compiler_rt's `memcpySmall`) within one
buffer is `.illegal` for overlapping ranges and returns the value for disjoint ones;
`swap(&x, &x)` is `.illegal`, two `noalias` reads of one pointer are legal, a `noalias` write and
a read through a plain parameter of the same `u32` are `.illegal`, also when an unchecked
overflow or a callee's safety panic follows the conflict; a function that passes its `noalias`
pointer on is rejected.

## Not illegal behaviour

| Operation | Why | Model |
| --- | --- | --- |
| Float division, `@divTrunc`, `@divFloor`, `@rem`, `@mod` by zero | langref §Operators: division by zero is IB for floats only in `FloatMode.optimized`; Sema's `addDivByZeroSafety` skips strict floats | IEEE result (±inf, NaN) |
| `@truncate`, wrapping and saturating ops, `<<|` with any count | defined | value |
| `extern`/`packed` union field reads | reinterpretation is defined | `Zig.Raw.get`/`Zig.PackedU.get` |
| `@bitCast` of a NaN to an integer, `@min`/`@max` of `+0` and `-0` (f32/f64) | result left open | `.unspecified` |
| `@setFloatMode(.optimized)` | fast-math changes values | *rejected* |

## Gaps

`@setRuntimeSafety(false)` blocks inside a ReleaseSafe build produce the unchecked shapes,
so the rows above model each op's own check instead of relying on a Sema check. No case is open.
The last one, a `for` loop with runtime safety off whose later operand is a range or an array,
needs a fact the AIR did not carry; the patched Sema now exports it (row 27). AIR from a
compiler without that patch (no `unchecked_ib`) is accepted only for functions without loops.

## Evidence

- `tests/roadmap/illegal-behavior/check.sh`: the fixture sources `ib.zig` and `probe.zig`
  (each former gap as a `@setRuntimeSafety(false)` function),
  their retained 0.16.0 AIR (`air/`, `probe-air/`), the translation, `Cases.lean` on the
  generated functions, and `Runtime.lean` on the runtime ops. `forlen.zig` and its AIR from every
  supported version (`for-air/<version>/`) show the `for` length check (row 27) in each, and a
  copy without `unchecked_ib` is rejected.
- Native: `native.zig` prints what a ReleaseSafe and a ReleaseFast build return for each input
  class (`native/*.txt`; [build-modes.md](build-modes.md)). The differential harness (`scripts/diff.sh`) counts every
  `.illegal` row as an `illegal` exclusion in every mode, so it compares none of them:
  `tests/diff/floatops/unspecified.txt` pins `divExact64`: 123 of its 300 inputs are
  `.illegal`, 23 are the NaN panic. A ReleaseFast or ReleaseSmall build can differ from
  ReleaseSafe only where the quotient is not a whole number, and each such input is
  `.illegal`, so float `@divExact` needs no exception to the
  [build-modes](build-modes.md) transfer premise.
- `tests/roadmap/architecture-audit/trust-chain/check.py unchecked-memcpy --require-fixed`.
- `tests/roadmap/noalias/check.sh` (row 43).
