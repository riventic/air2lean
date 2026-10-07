# Zig 0.17.0 vs 0.16.0

## AIR tags (`Air.Inst.Tag`)

214 tags in 0.16.0, 224 in 0.17.0 (16 added, 6 removed; a rename counts as both).

| Only in 0.16.0 | Only in 0.17.0 | Exporter (`zig-patch/air-json/json.zig`) |
|---|---|---|
| `bitcast` | `bit_cast` (`@bitCast` only), `bit_cast_safe` (`@bitCast`/`@fromBackingInt` with the `invalid_enum_value` check for an exhaustive enum result) | `ty_op` operand (`Compat.isNewTyOp`) |
| `bitcast` (pointer casts) | `ptr_cast` (pointer to pointer, slice to slice; `@ptrCast`, `@alignCast`, `@constCast`, read-only parameter copies, `&v[i]`), `ptr_from_int` (`@ptrFromInt`), `int_from_ptr` (`@intFromPtr`, pointer and slice `==`) | `ty_op` operand (`Compat.isNewTyOp`) |
| `bitcast` (error sets) | `error_cast`, `error_from_int`, `int_from_error` | `ty_op` operand (`Compat.isNewTyOp`) |
| `bitcast` (enum to tagged union) | `union_from_enum` | `ty_op` operand (`Compat.isNewTyOp`) |
| | `array_to_vector` | `ty_op` operand (`Compat.isNewTyOp`) |
| `intcast`, `intcast_safe` | `int_cast`, `int_cast_safe` (renamed, same checks) | `ty_op` operand (`Compat.isNewTyOp`) |
| `struct_field_val` | `agg_field_val` (renamed, same `StructField` payload) | operand and `index` (`Compat.isFieldVal`, `writeStructField`) |
| `bool_and`, `bool_or` | (removed: Sema emits `bit_and`/`bit_or` on `bool`) | `bin_op` operands (`Compat.isNewBinOp`, 0.16.0 and earlier) |
| | `div_ceil` (`@divCeil`) | `bin_op` operands (`Compat.isNewBinOp`) |
| | `div_ceil_optimized` | `"unsupported": true`, like every `*_optimized` tag |
| | `spirv_runtime_array_len` (SPIR-V only) | `"unsupported": true` |

The exporter writes each tag under its own name: `"tag"` is `bit_cast`, `int_cast`, `agg_field_val`
and so on in a 0.17.0 dump. Mapping them onto the 0.16.0 translator paths is the translator's job
(`Air2Lean/Air/Normalize.lean`, `Canon.lean`); until it knows 0.17.0, `supportedVersions` rejects
these dumps. `splat` keeps its name but may now produce an array.

## Data layout and type changes

- `Air.Inst.Data`: `ty_op.ty`, `ty_pl.ty`, `arg.ty` and `ty_nav.ty` are a `Type`, not an
  `Inst.Ref` (`Compat.tyPlType`).
- `Air.Inst.Ref`'s static refs lost `i0_type` (`i0` is removed); the exporter writes refs through
  `toIndex`/`toInterned`, so the renumbering is invisible in the JSON.
- `&v[i]` on a vector is a `ptr_cast` to a lane pointer for every element type (0.16.0: a
  `ptr_elem_ptr` to a plain element pointer for whole power-of-two-byte lanes). The lane index is
  only in the result type (`InternPool.Key.PtrType.Flags.vector_index`), and its `host_size` is
  the vector length. The exporter now writes it as `vector_index` on the pointer type entry, for
  every version (`docs/air-json.md`); before, two lanes had identical entries that read as a
  bit-pointer at bit 0.
- An empty exhaustive enum is backed by `noreturn`: its type entry has `"tag"` pointing at a
  `noreturn` type.

## SPIR-V types (`spirv_type`, `spirv_runtime_array_len`)

0.17.0 adds the InternPool key `spirv_type` (`std.lang.Type.spirv`) and the AIR tag
`spirv_runtime_array_len`. Their one source is `@SpirvType`: `InternPool.getReifiedSpirvType` has
a single caller, `Sema.zirReifySpirvType`, which fails first unless the target is SPIR-V
(`Sema.zig` 20849). So neither is reachable on a supported target (x86_64-linux, aarch64-macos).
Fixture, with the patched compiler:

```sh
# spirv.zig: const T = @SpirvType(.sampler); export fn f(x: u32) u32 { _ = @sizeOf(T); return x; }
zig-air-0.17.0/bin/zig build-obj -fno-emit-bin -OReleaseSafe -target x86_64-linux spirv.zig
# error: builtin @SpirvType is only available when targeting SPIR-V; targeted CPU architecture is x86_64
```

(the same for `-target aarch64-macos`). Were one exported, the type would be a `"k": "other"`
entry and the tag `"unsupported": true`, both rejected by the translator.

## Exporter port

`zig-patch/air-json/json.zig` is shared by every version; its `Compat` section has the 0.17.0
branch (`Compat.v17`; `v16` now means 0.16.0 or later, so the `std.Io` file and environment
branches apply unchanged):

- The removed and renamed tags leave the shared `writeInst` switch. `Compat.isNewTyOp`,
  `isNewBinOp` and `isFieldVal` name each version's own tags in comptime-selected branches.
- `Type.intTagType` became `backingIntType` (`Compat.enumTagType`).
- `Value.fmtValue` and `Type.fmt` take a `*Zcu`, not a `Zcu.PerThread` (`Compat.fmtValue`,
  `Compat.fmtType`).
- `Type.containerTypeName` returns `{ name, fqn }`; the JSON keeps the fully qualified name
  (`Compat.containerTypeName`).
- `std.lang.Optimize` (was `std.builtin.OptimizeMode`) has tags `debug`, `safe`, `fast`,
  `small`; `profile.build_mode` keeps `Debug`/`ReleaseSafe`/`ReleaseFast`/`ReleaseSmall`
  (`Compat.buildMode`).
- Hook (`hook.patch`): after `analyzeFuncBodyInner(func_index, reason)` in
  `src/Zcu/PerThread.zig` (line 2297), after the new tracy lines.

## Build

`build.sh` passes `-Dversion-string=<version>`: 0.17.0's `build.zig` fails on a tarball tree
(no `.git`) without it. The AIR-only build (`-Denable-llvm=false`, Debug, `-j1`) took about
2-3 minutes with a peak RSS of about 3 GB on aarch64-macos.

## Observed differences on the examples

Against the 0.16.0 goldens (`tests/golden/<ex>/air/` with the `tests/golden/0.16.0/` overlay),
on aarch64-macos:

| Difference | Examples |
|---|---|
| `bitcast` splits into `ptr_cast` (most), `bit_cast`, `bit_cast_safe` (every runtime `@bitCast` in ReleaseSafe), `error_cast`, `int_from_ptr`, `ptr_from_int`. | nearly all |
| `intcast`/`intcast_safe`/`struct_field_val` renamed. | `basic`, `floatconv`, `layout`, `variants`, … |
| `bool_or` becomes `bit_or` on `bool`. | `slices` (`copy`), `vectors` (`vDiv`) |
| `&v[i]`: `ptr_elem_ptr` becomes `ptr_cast` to a lane pointer (`vector_index`). | `layout` (`laneSet`, `maskStore`) |
| Two more `dbg_stmt`s around a `@bitCast` to a packed struct. | `layout` (`setMode`) |
| `f128` `abi_align` is 8, not 16 (aarch64-macos host). | `floatconv` (`f16ToF128`, `f80ToF64`), `floatops` (`op128`, `op80`) |
| std changes: `Io.Condition.wait` goes through `waitTimeout`; `waitUncancelable` inlines more; `Io.Condition.waitInner` is gone. | `sync` |

Every exported example's differing files are in `tests/golden/0.17.0/<ex>/air/`. `threadsync`
does not compile on 0.17.0 (it uses `Thread.Mutex`/`Thread.WaitGroup`, which 0.16.0 already
removed). `lists` calls `dupeSentinel` instead of the removed `Allocator.dupeZ` on 0.17.0, and `asm`
uses the x86_64 clobber `cc`, so it is exported on x86_64 only (CI).
