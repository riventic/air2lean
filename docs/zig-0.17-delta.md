# Zig 0.16.0 → 0.17.0 semantic delta

Source-level comparison of the pinned `zig-0.16.0.tar.xz`
(sha256 `43186959…bfdf`) and `zig-0.17.0.tar.xz` (sha256 `b6c7f172…8abd`) and the
[0.17.0 release notes](https://ziglang.org/download/0.17.0/release-notes.html). No compiler was
built or run. Line numbers are in the 0.17.0 tree unless marked 0.16. The inventory is
`coverage/0.17.0.json`; the qualification plan is `qualification/0.17.0.json`.

Track owners: **Z1** exporter/pin, **Z3** translator (Normalize/Canon/Check/Emit), **Z4** bitcast
semantics, **Z5** examples and std models, **Z6** CI/metadata.

## (a) AIR tags and data layout

Universe: 214 → 224 tags (16 added, 6 removed). Renames appear as remove + add.

| 0.16 tag (0.16 `Air.zig` line) | 0.17 tag(s) (`Air.zig` line) | Change | Impact | Owner |
|---|---|---|---|---|
| `bitcast` (282) | `bit_cast` (290), `bit_cast_safe` (294) | `bit_cast` now implements `@bitCast` only (scalar/array/vector/packed/enum bits). `bit_cast_safe` = `bit_cast` + `invalid_enum_value` panic when the result type is an exhaustive enum and the bits are not a named tag. | exporter, translator | Z1, Z3, Z4 |
| `bitcast` (pointer uses) | `ptr_cast` (302) | Pointer → pointer (incl. slice → slice, vector of pointers); `@ptrCast`/`@alignCast`/`@constCast`, read-only parameter copies, alloc const-casts. | exporter; translator (`Canon.forwardReadOnlyCopies` matches `"bitcast"` on const pointers, `Check` pointer rules, `Emit`) | Z1, Z3 |
| `bitcast` (`@ptrFromInt`) | `ptr_from_int` (308) | Operand always `usize`; vectors allowed. | exporter, translator (`Emit` chooses ptr↔int from types today) | Z1, Z3 |
| `bitcast` (`@intFromPtr`, pointer compares) | `int_from_ptr` (314) | Result always `usize`. Also emitted by Sema for `==` on slices/pointers (Sema.zig 15110). | exporter, translator | Z1, Z3 |
| `bitcast` (error sets) | `error_cast` (319), `error_from_int` (324), `int_from_error` (329) | Split out of `bitcast`. | exporter; translator (`Check` error-storage rules keyed on `.bitcast`) | Z1, Z3 |
| `bitcast` (enum → tagged union) | `union_from_enum` (334) | Enum → tagged union with only void payloads. Was already outside the subset as an aggregate bitcast. | exporter (stays rejected) | Z1, Z3 |
| (array → vector coercion) | `array_to_vector` (760) | New explicit tag. Vector bitcasts were already rejected. | exporter (stays rejected) | Z1, Z3 |
| `intcast` (598), `intcast_safe` (604) | `int_cast` (644), `int_cast_safe` (650) | Rename only, same `ty_op` and safety checks. `@enumFromInt` still lowers here (Sema.zig 7974/7976). | exporter, translator (Normalize string) | Z1, Z3 |
| `struct_field_val` (657) | `agg_field_val` (702) | Rename only, same `ty_pl` + `StructField` payload. | exporter (explicit arm), translator (Normalize; `Canon` maps field-ptr loads to `"struct_field_val"`) | Z1, Z3 |
| `bool_and` (543), `bool_or` (546) | removed | Sema safety conditions now use `bit_and`/`bit_or` on `bool` operands (Sema.zig 4181, 14472, 14485, 21681). | translator: `.bit .and/.or` must type-check and emit on `bool`; `.boolAnd/.boolOr` stay for ≤0.16 | Z3 |
| — | `div_ceil` (150), `div_ceil_optimized` (152) | `@divCeil`, `bin_op`, see (c). | exporter, translator, ZigLean semantics | Z1, Z3 |
| — | `spirv_runtime_array_len` (985) | SPIR-V only; unreachable on supported targets. | none (stays rejected) | Z1 |
| `splat` (731) | `splat` (786) | Result may now be an array, including a sentinel array, not only a vector. | translator (`Check` must reject or model array splat) | Z3 |

Inventory dispositions for 0.17.0 against the unchanged exporter: every added tag is
`rejected-exporter-unsupported` (fallback unsupported marker), except `div_ceil_optimized`,
which is `rejected-fast-math`. There are no `unclassified-forbidden` rows. The summary is 158
emitted-unqualified, 31 rejected-exporter-unsupported, 20 rejected-fast-math, 10
rejected-compiler-state-or-effect and 5 erased-at-emission. This disposition is computed from
source. **The current `json.zig` does not compile against 0.17** (see the exporter list below),
so Z1 must regenerate the inventory after porting.

**Data layout changes (`Air.Inst.Data`, Air.zig 1299–1344).** `arg.ty`, `ty_op.ty`, `ty_pl.ty`
and `ty_nav.ty` are now `Type`, not `Inst.Ref`/`InternPool.Index`. `typeOfIndex` returns them
directly (Air.zig 1703, 1730, 1784, 1868). `Air.Inst.Ref`'s static refs lost `i0_type`, so every
later static ref value shifts down by one (Air.zig 1100+). No payload struct changed.
`Air.Verify` (new, `Air/Verify.zig`) runs on AIR before and after legalization
(`Zcu/PerThread.zig` 4525/4530) and has no effect on the exported form.

**Exporter port items (Z1).** These were found by reading the sources. Z1's build is the
authority.
- `Compat` rejects minor > 16 (`json.zig` 35). The `Compat.v16` `std.Io` file/env branches also
  apply to 0.17. `std.Io` file APIs keep their 0.16 names: `Dir.CreateFileOptions` and
  `Dir.OpenFileOptions` already exist in 0.16.
- `writeInst` names `.bitcast`, `.intcast`, `.intcast_safe`, `.bool_and`, `.bool_or` and
  `.struct_field_val` (`json.zig` 680–681, 762–765, 869). These are compile errors on 0.17. They
  need version-selected arms. The new `ty_op` tags need operand arms: `bit_cast`,
  `bit_cast_safe`, `ptr_cast`, `ptr_from_int`, `int_from_ptr`, `error_cast`, `error_from_int`,
  `int_from_error`, `union_from_enum`, `int_cast`, `int_cast_safe`, `array_to_vector`.
  `agg_field_val` needs a `StructField` arm and `div_ceil` a `bin_op` arm. `coverage.py`'s
  version-branch parser only resolves `Compat.vNN`, so new gates should use that form.
- `aggregate_init` uses `ty_pl.ty.toType()` (`json.zig` 883). `Type` has no `toType`.
- Enum type entries use `ty.intTagType(zcu)` (`json.zig` 1671), which was removed. Use
  `ty.backingIntType(zcu)` (Type.zig 1645). For an empty exhaustive enum it is `noreturn`
  (see (b)).
- `@intFromEnum`/`@enumFromInt`, `std.fmt.bufPrint`/`allocPrint` and `std.builtin` still
  compile but are deprecated. `Type`/`Value`/`Zcu`/`InternPool` removed no other pub function the
  exporter calls.
- Hook: the 0.16 `hook.patch` context does not apply. `analyzeFuncBodyInner(func_index, reason)`
  is at `Zcu/PerThread.zig` 2297, after new tracy lines, and the preceding log line is now
  `"analyzeFuncBody {f}"`. LLVM major is 22 (`cmake/Findllvm.cmake` 20).

## (b) InternPool and type changes

| Change | Source | Impact | Owner |
|---|---|---|---|
| `std.builtin` → `std.lang` (alias kept, deprecated). `Type` is now in `lib/std/lang.zig` 640. | release notes; `std.zig` 71 | `coverage.py` read `lib/std/builtin.zig`. It now selects `lang.zig` when `builtin.zig` is absent and fails closed when both are missing (this branch). | Z6 (done here) |
| `std.lang.Type` gains `spirv` (lang.zig 665). `InternPool.Key` gains `spirv_type` (`SpirvType`). | lang.zig, InternPool.zig | The `spirv` type is `exported-as-other-rejected` and `spirv_type` is `type-key-via-type-table`. The plan's only `support:` obligation (`support:constants:spirv_type`) is a review that confirms it is unreachable on supported targets. | Z1 (review) |
| `i0` removed: `InternPool.Index.i0_type` and `Air.Inst.Ref.i0_type` are gone, and `i0` is a compile error. | release notes; InternPool.zig Index | Static ref numbering shifts. `tests/roadmap/byte-permutation/byte_permutation.zig` 31/33 use `i0` and must be gated to ≤0.16. The translator's signed 0-bit width handling stays for older versions. | Z5, Z6 |
| Empty exhaustive enums must be backed by `noreturn` (`Sema/type_resolution.zig` 1411–1429). `hasBitRepresentation` excludes them and auto-tagged enums (Type.zig 3266–3270). | type_resolution, Type.zig | The exporter writes `tag: noreturn` for such an enum. `Check` must reject an enum whose tag type is `noreturn` (the type is uninstantiable). | Z1, Z3 |
| `Type.intTagType` removed. `backingIntType`/`backingIntMode` cover enum, packed struct and packed union. | Type.zig 1645–1664 | exporter (above) | Z1 |
| `@typeInfo` struct/union info is struct-of-arrays: `field_names`, `field_types`, `field_attrs` (lang.zig 750–760). Pointer `alignment` → `attrs.@"align"`. | release notes; lang.zig | No exported AIR/type change. The test harnesses `tests/diff/common.zig` 325 and `tests/diff/vectors/harness.zig` 133 use `.fields`/`f.name`/`f.type` and need a compat helper. | Z5 |
| `Key.FuncType` drops comptime/noalias trailing bits in encoding, and `memoized_call` gains `branch_quota`. | InternPool.zig | none (internal) | — |

## (c) New builtins in 0.17 Sema

| Builtin | Lowering (runtime operands) | Safety (ReleaseSafe) | Impact | Owner |
|---|---|---|---|---|
| `@divCeil(a, b)` | `zirDivCeil` (Sema.zig 14263) emits `div_ceil` (`div_ceil_optimized` in `@setFloatMode(.optimized)`) on the peer-resolved type (14325). Ints and floats (ceil(a/b)); vectors allowed. | `addDivIntOverflowSafety` (signed `minInt / -1` → `integer_overflow`) and `addDivByZeroSafety` (`divide_by_zero`) precede the op (14320–14323), as for `@divFloor`. LLVM computes signed results as `sdiv`/`srem` plus an adjustment (`codegen/llvm/FuncGen.zig` 3584) and float results as `div` then `ceil`. | New Op (`div .divCeil`) in Normalize/Emit and ZigLean: round toward +∞. Integer `div_ceil` cannot overflow except at `minInt/-1`, which Sema guards. | Z1, Z3 |
| `@backingInt(x)` | `zirBackingInt` (9502). Enum → `bit_cast` to the backing int (9557). A tagged union first lowers through `unionToTag` (`get_union_tag`). A packed struct/union with an explicit backing int → `bit_cast`. Comptime values fold. | none | Same AIR as `@intFromEnum` (still accepted, deprecated, 7919: `bit_cast`). Today's `.bitcast` enum → int path covers it once the tag is mapped. | Z3 |
| `@fromBackingInt(i)` | `zirFromBackingInt` (9586). The operand is coerced to the backing int, then `bit_cast_safe` (safety on, 9633) or `bit_cast` (9635). The destination may be an enum or an explicit-backed packed struct/union. | `bit_cast_safe` checks the named-tag condition only for an exhaustive enum destination (Legalize `safeBitcastBlockPayload`, `Air/Legalize.zig` 2163–2216, returns plain `bit_cast` otherwise). Undefined input to an exhaustive enum is illegal behaviour. | New in AIR: an int → enum `bit_cast_safe` (0.16 used `intcast_safe` via `@enumFromInt`, which still exists and still emits `int_cast_safe`, 7974). Translator: `bit_cast_safe` to an exhaustive enum = bits + `isNamedEnum` check → `invalidEnumValue` (`.panic`), the same contract as `intcast_safe` today (`Emit.lean` 831). | Z3 |
| `@bitCast` to an enum (new) | `zirBitcast` (9403) emits `bit_cast_safe` when safety is on and `bit_cast` otherwise (9495–9499). **This is for every runtime `@bitCast`, not only enum destinations.** | Same enum check as above. For non-enum destinations `bit_cast_safe` behaves as `bit_cast` (Legalize 2171–2176). | **Every runtime `@bitCast` in ReleaseSafe goldens becomes `bit_cast_safe`**: `floatconv` 32/35, `layout` 70–151 and std code. Z3 must accept `bit_cast_safe` for all `bit_cast` shapes and add the enum check only for exhaustive enum results. | Z3, Z5 |
| `@SpirvType` | SPIR-V targets only (compile error otherwise). | — | none | — |

`@intFromEnum` and `@enumFromInt` remain accepted (deprecated). Their AIR is unchanged apart
from tag names.

## (d) `@bitCast` semantics (Z4)

**0.16.** `@bitCast` reinterpreted the *in-memory* representation:
- `zirBitcast` (0.16 Sema.zig 9524) allowed `extern`/`packed` struct and union, arrays whose
  element has a well-defined layout, vectors, int, float and bool. It rejected enums (9556:
  "use @enumFromInt"), pointers, optionals and `void`.
- The size check used `Type.bitSize`, which for arrays on the LLVM backend was
  `(len-1) * 8 * @sizeOf(E) + @bitSizeOf(E)` (0.16 Type.zig 1236–1241), so inter-element padding
  counted.
- Comptime folding went through byte memory (`Sema/bitcast.zig`, endian-dependent). Runtime was
  an LLVM `bitcast` or a memory round-trip.
- The result for arrays and vectors of non-byte-multiple elements, and on big-endian targets,
  depended on the target's memory layout.

**0.17 definition (release notes "@bitCast changes").** `@bitCast` reinterprets the *logical bit
representation*:
- Allowed types (`Type.hasBitRepresentation`, Type.zig 3242–3276) are `void`, `bool`, runtime
  ints and floats, enums with an *explicit* non-`noreturn` tag type, packed struct/union, and
  arrays/vectors of these.
- `extern` struct/union, auto-layout aggregates, error sets/unions, pointers, optionals and
  arrays/vectors of pointers are compile errors (`zirBitcast` 9416–9455). Use `@ptrCast` to pun
  memory.
- Bit size is `Type.bitSize` (Type.zig 1318–1329). Arrays and vectors are
  `len_including_sentinel * @bitSizeOf(E)`, densely packed with no padding. Enums use their
  backing int and packed types their backing int.
- **Bit order.** For an int or float, bit 0 is the LSB. For an array or vector, element `i`
  occupies logical bits `[i*eb, (i+1)*eb)`, where `eb = @bitSizeOf(E)`, so element 0 is the
  low-order bits. For a packed struct/union, the logical bits are the backing integer's.
  Comptime folding (`bitCastVal`, Sema.zig 30148) writes the operand with
  `Value.writeToPackedMemory` (Value.zig 392–470: concatenates elements at increasing bit
  offsets, enum/packed through the backing int, undef → all-undef). It then reads the
  destination with `readFromPackedMemory`.
- The result is endian-agnostic: the same logical value on every target.
- **Runtime lowering.** Pre-legalize AIR, which the exporter dumps, has one `bit_cast`/`bit_cast_safe`
  with the array/vector operand or result. The backend legalizes it: LLVM enables
  `scalarize_bit_cast_array` and, on big-endian, `scalarize_bit_cast_vector_non_elementwise`
  (`codegen/llvm.zig` 39–43). `scalarizeBitcastBlockPayload` (Legalize.zig 1551) uses an
  element-wise bitcast when lengths match and otherwise a `uN` bag of bits built by
  `shl`/`bit_or` of each element at offset `i*eb`, then extracted by `shr`/`trunc`. This is the
  logical order above. The translator must model the logical definition directly; exported
  AIR is never legalized.

**Where 0.17 and 0.16 differ.**
1. Arrays/vectors of elements with `@bitSizeOf(E) != 8*@sizeOf(E)` (`u4`, `bool`, `u24`, `i7`,
   enums with small tags). For example, `[2]u4 → u8` was a size mismatch error in 0.16 (12 vs 8
   bits) and is `e0 | e1 << 4` in 0.17. `[3]u24 → u72` is now legal and dense.
2. Big-endian targets. In 0.16, array → int took memory order; 0.17 always takes element 0 as the
   low bits. On little-endian with byte-multiple elements both agree. That covers today's
   x86_64/aarch64 Linux profiles.
3. Newly legal: enum ↔ int/packed of equal width (with the ReleaseSafe check), `void`, and arrays
   of enums or packed values. Newly illegal: `extern` struct/union. Examples `layout`
   157/305 declare extern structs but do not `@bitCast` them; this needs re-checking in Z5.

**Repository impact.** `Check.lean` (around 596–712) rejects every array/aggregate bitcast
except packed ↔ int and rejects vector bitcasts that change type. 0.17 therefore breaks no
modelled semantics. Its packed ↔ int, int ↔ float and same-type cases are unchanged.
Z4 may admit array/vector ↔ int/array/vector under the logical definition above: a little-endian
LSB-first concatenation with no padding. That is a new ZigLean function independent of
`Zig.Mem` byte layout, and must not reuse memory encoding/decoding. The model must keep 0.16
rejecting those shapes (memory semantics), so the rule is version-gated. Native differential
fixtures on a little-endian profile cannot tell the two definitions apart for byte-multiple
elements. Qualification needs sub-byte-element cases (`[2]u4`, `[8]bool`, `@Vector(3, u5)`).

## (e) std API changes against `Air2Lean/StdModels.lean`

Diffed `lib/std/{mem/Allocator,Thread,Io,Io/RwLock,Io/Semaphore,atomic,time,array_list}.zig`.

| Modelled / translated std surface | 0.16 → 0.17 | Impact | Owner |
|---|---|---|---|
| `mem.Allocator.create` | Now `createAdvancedWithRetAddr(T, null, @returnAddress())` (inline). New `alignedCreate`. Same signature and semantics. | Model name unchanged; re-qualify the instance name and signature. | Z5 |
| `.alloc`, `.alignedAlloc`, `.dupe`, `.allocSentinel` | Bodies unchanged. Internal `allocBytesWithAlignment` → `pub allocBytesAligned` (same body). `allocWithOptionsRetAddr` unchanged. | `allocSentinel` model is qualified `#["0.16.0"]` only. Add `"0.17.0"` after re-qualification (same overflow and sentinel logic). | Z5 |
| `.free`, `.destroy` | `free` also accepts `*[N]T`/`*[N:s]T` (single pointer to array). Alignment is read from `attrs.@"align"`. Slice semantics unchanged. | `Check` signature: a single-pointer-to-array `free` must stay rejected or be modelled (len = N(+1)). | Z5, Z3 |
| `.remap` | Return type `?@TypeOf(allocation)` → `?Slice(AbsorbSentinel(@TypeOf(allocation)))`. A sentinel slice now returns a non-sentinel slice. Also accepts `*[N]T`. | Equal for `[]T`. Sentinel remap stays outside the model. Signature check needs re-qualification. | Z5 |
| `.dupeZ` | **Removed** (use `dupeSentinel(T, m, 0)`, unchanged). | `examples/lists/lists.zig` 76 (`dupeZLen`) and `examples/lists/filter` (`mem.Allocator.dupeZ`) break on 0.17. Gate or switch to `dupeSentinel`. | Z5 |
| `mem.Allocator.print`/`printSentinel` | New (replacing `fmt.allocPrint`). | none | — |
| `Thread.spawn`/`join`/`yield`/`detach` | Signatures and bodies unchanged at the modelled boundary (lines 344/370/380/364). Diffs are Windows/emscripten/asm only. | none beyond re-qualification | Z5 |
| `atomic.spinLoopHint` / `Thread.spinLoopHint` | Only arm/mips/sparc/m88k arms changed. x86_64 and aarch64 unchanged. | none | — |
| `Io.futexWait`/`futexWaitUncancelable`/`futexWake`/`futexWaitTimeout` | Unchanged except `@intFromEnum` → `@backingInt` (Io.zig 1681–1709). | none | — |
| `Io.Condition.wait` | **Now `waitTimeout(…, .none)`**. `waitTimeout` (Io.zig 1817) calls `io.futexWaitTimeout` (rejected model) plus deadline logic and a new `deregister` (Io.zig 1908). `waitUncancelable` (1872) still calls `futexWaitUncancelable` but its loop lost the error branch. | Translated (filter `Io.Condition.`): cancelable `wait` now reaches the rejected `Io.futexWaitTimeout`. `sync` uses `waitUncancelable` (sync.zig 54), so it still translates, but the regenerated std translation changes. To admit `wait`, model `futexWaitTimeout` with `.none`. | Z5 |
| `Io.Semaphore.wait` | Now `waitTimeout(.none)` → `cond.waitTimeout`. `waitUncancelable` is unchanged in shape. | `sync` uses `waitUncancelable` (sync.zig 70). Same note as above. | Z5 |
| `Io.RwLock` | `tryLock` is now a `cmpxchgStrong` (was `atomicRmw .Or`). The `lock` cancel path is rewritten. `lockUncancelable`/`lockSharedUncancelable`/`unlock*` are unchanged. | Re-translate. `rwLockSnapshotPair` contracts (`docs/rwlock-contracts.md`) only need re-checking if `tryLock` is reached. | Z5 |
| `Io.Mutex`, `Io.Event` | Unchanged. | none | — |
| `Io.Group.async`/`concurrent`/`await`/`cancel` | Doc-only. "`function` is not guaranteed to have been called until `await` or `cancel`"; after `await`/`cancel` all tasks have run. | The model (async = spawn, fallible policy = caller execution) already admits deferred execution. Record the review in the `model-boundary` obligation. | Z5 |
| `time.Timer`, `Thread.Futex`, `Thread.Mutex.DarwinImpl` | Not present in 0.16 or 0.17 (0.15.2-only models). | none | — |
| `ArrayListUnmanaged` (`array_list.Aligned(u32,null).`) | New field `pointer_stability: debug.SafetyLock` (array_list.zig 653). It is a `usize` state in safe builds and a zero-size enum otherwise (`debug.zig` 1851). Every mutator calls `assertUnlocked()`. `addManyAt` no longer goes through the managed list: it uses `remap`, else `alignedAlloc` + `@memcpy` + `free`. `getLastOrNull` → `last`, and `lastPtr` is new. | Struct layout grows by 8 bytes in ReleaseSafe. `lists` translation and proofs change. The filter needs `debug.SafetyLock.` (or the lock calls modelled) because `assertUnlocked` calls `debug.assert`. | Z5 |
| `@import("builtin").mode` | `OptimizeMode` → `lang.Optimize` with tags `debug/safe/fast/small`. | `tests/roadmap/abi-probes/probe.zig` 24 prints `@tagName(builtin.mode)` → `safe` instead of `ReleaseSafe`. `scripts/abi-probe.py` 34/84 expect `ReleaseSafe`. | Z6 |
| `builtin.cpu`/`os`/`abi` | Deprecated (removed in 0.18). | `tests/diff/compat.zig` 18, `tests/diff/libm/selfcheck.zig` 93, `probe.zig` 20–34. Still compile. | Z6 |
| `std.heap.DebugAllocator` | Deprecated in favour of `SafeAllocator`. | 19 `tests/diff/*/harness.zig` uses. Still compile. | Z5 |

## (f) Safety checks and illegal behaviour

| Change | Source | Impact | Owner |
|---|---|---|---|
| Runtime `@bitCast`/`@fromBackingInt` to an exhaustive enum panics `invalid_enum_value` on an unnamed value (`bit_cast_safe`). | Sema.zig 9495–9497, 9631–9633; Legalize.zig 2163 | Same panic as `@enumFromInt` (`invalidEnumValue`, `panic-policy.tsv`). Translator check required (see (c)). | Z3 |
| `@divCeil`: `divide_by_zero`, `integer_overflow` (signed `minInt / -1`). | Sema.zig 14320–14323 | Reuse the existing `divFloor` checks. | Z3 |
| New simple panic `load_uninstantiable_type` → `std.debug.panic.loadUninstantiableType` (`simple_panic.zig` 161). It fires on a runtime load of a no-possible-value type. | Zcu.zig `SimplePanicId`; Sema.zig 31111 | Not in `scripts/panic-policy.tsv`. A call is rejected until mapped. | Z3 |
| `@errorCast` safety now calls `panic.unexpectedErrorCode(err)` with the error operand (was `invalid_error_code` simple panic). | Sema.zig 21667–21690; `simple_panic.zig` 85 | Not in `panic-policy.tsv`. A call is rejected until mapped. `Check` already restricts error-set casts (error-storage rules). | Z3 |
| Empty exhaustive enums are `noreturn`-backed and uninstantiable. | type_resolution.zig 1411 | See (b). | Z3 |
| `mem.eql`/`findDiff` no longer short-circuit equal float slices (NaN). | release notes | Only if translated std code reaches it. None today. | — |

## Per-track action list

- **Z1 exporter:**
  - Port `json.zig`: Compat range, `v16` → `≥16` std.Io branches, `Compat.vNN`-gated arms for
    the removed/renamed tags, and arms for the 13 new `ty_op` tags plus `agg_field_val` and
    `div_ceil`.
  - Fix `ty_pl.ty` (already a `Type`) and `intTagType` → `backingIntType`.
  - Write the 0.17 hook against `PerThread.zig` 2297. Pin LLVM 22.
  - Regenerate `coverage/0.17.0.json` and discharge `support:constants:spirv_type` (SPIR-V
    unreachable).
- **Z3 translator:**
  - Normalize: `int_cast(_safe)`, `agg_field_val`, and `bit_cast`/`ptr_cast`/`ptr_from_int`/
    `int_from_ptr`/`error_*` mapped onto today's `.bitcast` paths with their `Check` rules.
  - `bit_cast_safe` = `bit_cast` + exhaustive-enum named-value check.
  - New `div_ceil` op.
  - `bit_and`/`bit_or` on `bool`.
  - `Canon.forwardReadOnlyCopies` keyed on `ptr_cast`.
  - Reject array `splat`, `union_from_enum`, `array_to_vector`, `noreturn`-tagged enums.
  - Panic policy for `loadUninstantiableType`/`unexpectedErrorCode`.
- **Z4 bitcast semantics:**
  - Version-gated logical bitcast: LSB-first concatenation, dense, endian-agnostic, for
    arrays/vectors/enums. 0.16 keeps rejecting.
  - Differential cases with sub-byte elements.
- **Z5 examples and std models:**
  - `lists`: `dupeZ` removed, `ArrayList` `pointer_stability` field and filter, `addManyAt`
    rewrite.
  - `sync`: regenerated `Io.Condition`/`Io.Semaphore`/`Io.RwLock` translations. `wait` reaches
    `futexWaitTimeout`.
  - Allocator model re-qualification for 0.17: `allocSentinel` version list, `free`/`remap` on
    single-pointer arrays.
  - Harness `@typeInfo` SoA (`common.zig` 325, `vectors/harness.zig` 133).
  - `layout` extern-struct audit.
  - `examples/*/zig-versions` entries.
- **Z6 CI/metadata:**
  - `coverage.py` `lang.zig` support (done in this branch).
  - CI matrix entry and host-zig pin.
  - `abi-probe` build-mode tag rename (`safe`).
  - `i0` byte-permutation probe gated to ≤0.16.
  - Run the `qualification/0.17.0.json` obligations: 7 reviews, 5 probes, 19 translations, 19
    proof sets.
