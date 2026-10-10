# AIR JSON format (schema 12)

The patched compiler writes one file per function. Safe short names use `$ZIG_AIR_JSON_DIR/<fqn>.json`; long or unsafe names use a reserved SHA-256 basename while JSON retains the complete identity. See [Exported function filenames](export-names.md) for the naming and collision contract. `ZIG_AIR_JSON_FILTER=<prefix>,<prefix>,…` limits output to functions whose fully qualified name starts with one of the prefixes. The format does not depend on the Zig version: AIR tags are written verbatim, and `Air2Lean/Air/Normalize.lean` maps them per version.

## File

```json
{
  "schema": 12,
  "zig_version": "0.15.2",
  "target_endian": "little",
  "profile": {
    "name": "abi64-le-v1",
    "target_triple": "x86_64-linux.4.19...6.1-gnu.2.28",
    "pointer_bits": 64,
    "endian": "little",
    "abi": "gnu",
    "zig_version": "0.15.2",
    "backend": "stage2_llvm",
    "cpu": "x86_64",
    "features": ["sse", "sse2"],
    "build_mode": "ReleaseSafe",
    "float_mode": "per-instruction",
    "error_set_bits": 16,
    "error_layout": "type-table",
    "error_tracing": false,
    "export_stage": "analyzed-air"
  },
  "name": "basic.scale",
  "module": "root",
  "src": { "file": "basic.zig", "module": "root", "decl_line": 14 },
  "params": [0, 1],
  "ret": 3,
  "export": {"name": "scale", "cc": "x86_64_sysv"},
  "body": [ Inst, ... ],
  "externs": [ Extern, ... ],
  "globals": [ Global, ... ],
  "types": [ Type, ... ]
}
```

| Field | Meaning |
|---|---|
| `schema` | Supported versions are 1–12. Schema 12 requires complete profile metadata and is decoded against the [schema table](#schema-table) (deny by default). Schemas 1–11 select the named `legacy-abi64-le` assumptions, which the translator accepts only with an explicit `--profile legacy-abi64-le`. Unsupported/future schemas fail closed. |
| `profile` | Mandatory schema-12 target/build facts from the function's owning module and compiler configuration. All facts must agree across a program. See [Target and build profiles](profiles.md) for the exact contract, accepted model ABI scopes and numerical-model disclosure. Metadata is not a shipping-binary correspondence theorem. |
| `target_endian` | Target byte order: `"little"` or `"big"` (additive schema 11 metadata). The translator accepts `"big"` only with a schema-12 big-endian profile of the same byte order (`docs/profiles.md` §Byte order) and rejects any other non-little-endian value. Legacy schema 1–11 files without this field are accepted, behind `--profile legacy-abi64-le`, under the named little-endian reference-target assumption; their target has not been verified. Schema 12 requires the field and `profile.endian`. |
| `name` | the function's fully qualified name: its path inside its module (`basic.scale`) |
| `module` | the function's module (§Identity): `root` for the main module, `std` for the standard library, else the module's name. Additive (no schema change); older exports omit it. |
| `src` | Additive source provenance (no schema change): `file` (the declaring file, relative to its module's root directory), `module` (the module name as the compiler spells it, e.g. `root` or `std`; not the §Identity key) and `decl_line` (1-based line of the function's declaration). Older exports omit it. Read only by check-only diagnostics to locate findings; translation never reads it, and `scripts/normalize-air.py` drops it from golden comparisons. |
| `instance_key` | a generic instance only (`name` is `<generic>__anon_<n>`): its content-addressed key, 64 hex digits (§Instances). Additive; older exports omit it, and so does an instance whose comptime arguments have no stable identity. |
| `params` | type ID of each runtime parameter, in order |
| `noalias` | the indices into `params` of the `noalias` parameters (Sema's `noalias_bits`: only the first 32 parameters can be `noalias`), in increasing order; `[]` for none. Required in schema 12; legacy schemas have none. The translator checks every call of such a function ([illegal-behavior.md](illegal-behavior.md#noalias-parameters)). `scripts/normalize-air.py` treats `[]` like an absent field, so older goldens compare equal |
| `ret` | type ID of the return type |
| `export` | `{name, cc}`: present only for a function declared with the `export` keyword. `name` is the linker symbol it defines, `cc` its calling convention's tag (`std.builtin.CallingConvention`, e.g. `x86_64_sysv`, `aarch64_aapcs_darwin`). `@export` aliases are not reported (§Extern calls). Additive; AIR golden comparison (`scripts/normalize-air.py`) ignores it. |
| `body` | main body (AIR `getMainBody`) |
| `externs` | the extern functions the body calls (§Extern calls), one entry per symbol, in first-call order. Missing if the body calls none. |
| `globals` | the globals that pointer constants point into (§Global). A global ID is an index into this array. Missing if the function has no pointer constant (schema 6). |
| `types` | type table. A type ID is an index into this array. Each type is listed once. |

The reader rejects cyclic value types (pointer recursion is allowed), out-of-range type IDs,
SSA uses before their definition or outside their lexical body, and malformed constant
shapes. Aggregate constants must have the exact number and types of their items; optional,
error-union and union payloads must match their child type. Presence markers such as `undef`,
`null` and shuffle `u` must be literal `true`. Supplied flags such as `noreturn`, `volatile`
and `unsupported` must be booleans. A reference or shuffle lane has exactly one value form.
Integer and enum constants must fit their type (and an exhaustive enum constant must name a
declared tag) when they are decoded.

## Schema table

`Air2Lean/Air/Schema.lean` lists, for every object kind of a schema-12 file, its keys:
required or optional, and the JSON shape of each value. The decoder validates the whole file
against it first. A key outside the table, a missing required key, or a value of another
shape rejects the file, so an absent flag never defaults and an attribute that a newer
exporter adds is never ignored. The exporter (`zig-patch/air-json/json.zig`) and the table
change together; the tables below and in §Type, §Inst, §Ref and §Global are the same
contract in prose.

| Object | Required keys | Optional keys |
|---|---|---|
| file | `schema`, `zig_version`, `target_endian`, `profile`, `name`, `params`, `noalias`, `ret`, `body`, `types` | `globals`, `module`¹, `src`, `instance_key` |
| `profile` | all fields of the example above ([profiles](profiles.md)) | — |
| every type | `k` | `abi_size`, `abi_align` |
| `int` / `float` | `signed`, `bits` / `bits` | — |
| `ptr` | `size` (`one`, `many`, `slice`, `c`), `const`, `child`, `volatile`, `allowzero`, `address_space`, `sentinel`, `host_size` | `ptr_align`, `sentinel_byte`, `bit_offset`, `vector_index` |
| `array` / `vector` | `len`, `child` (+ `sentinel` for `array`) | — |
| `optional` / `error_union` | `child` / `error`, `payload` | — |
| `error_set` | — | `errors`, `any: true`, `inferred: true` |
| `struct` / `union` | `name`, `layout` (`auto`, `extern`, `packed`) | `module`¹, `no_fields: true`, `fields`; `union`: `tag`, `safety_tag` |
| `tuple` / `enum` | `fields` / `name`, `tag`, `exhaustive`, `fields` | `enum`: `module`¹ |
| `other` | `name` | — |
| struct or tuple field | `ty` | `name`, `offset`, `comptime: true` |
| union / enum field | `name`, `ty` / `name`, `value` | — |
| instruction | `id`, `tag`, `ty`, the payload keys of its tag (§Inst) | — |
| unsupported instruction | `id`, `tag`, `unsupported: true` | `ty` |
| `Ref` | exactly one form of §Ref with its keys (`ty` for every constant form) | `module`¹, `comptime_fn`, `comptime_fn_module`, `instance_key`, `comptime_fn_instance_key` (`func`), `utag` (`uval`) |
| pointer constant target | `off` and one of `global`, `null: true`, `unsupported` | `payload_base: true` (with `global`) |
| shuffle lane | one of `a`, `b`, `u: true`, `v` | — |
| switch case | `items`, `ranges`, `body` | — |
| asm operand | `constraint`, `name` | `ref` |
| named global (`nav`) | `name`, `ty`, `const`, `threadlocal`, `extern` | `module`¹, `init` |
| unnamed global (`uav`) | `ty`, `const`, `init` | — |

¹ The module identity keys of the module-identity change. `Schema.moduleRequired` is set: every
schema-12 file carries them, and a file without them is rejected.

Each instruction tag has one payload entry (`instPayload`), following the exporter's
`writeInst`: for example `args` for every `bin_op`, `un_op` and `ty_op` tag, `callee` and
`args` for the four `call*` tags, `body` for blocks, `then`/`else` for `cond_br`. A tag
without an entry is accepted only as `"unsupported": true`, which the normalizer rejects.

**Semantic attributes.** The table also names the type attributes that the translator does
not model, with the one value it accepts:

| Kind | Attribute | Accepted value |
|---|---|---|
| `ptr` | `address_space` | `"generic"` (`*addrspace(.gs) T` is outside the subset) |
| `struct`, `tuple` field | `comptime` | absent (`false`): a comptime field has no runtime storage |

Another value is recorded in the type's layout facts, and the checker rejects every type that
a function uses (a parameter, result, instruction, constant or global type, or a type reached
through their fields and pointees) with such an attribute. Unused entries of the type table
do not reject the file. Independently, the checker rejects a non-packed struct or tuple whose
nonzero-sized fields overlap or extend beyond the type's `abi_size`, which also catches a
comptime field in an export that predates the `comptime` marker.

Schemas 1–11 predate the table and keep the historical reader (absent flags default to
`false`), behind the explicit legacy opt-in. Their goldens remain comparable with fresh
exports: `scripts/normalize-air.py` treats `"address_space": "generic"` like an absent field.

**Build-mode admission.** Only the build mode and backend pairs that
[build-modes.md](build-modes.md) qualifies (`ReleaseSafe` with `stage2_llvm`) are translated
by default. Any other profile needs `--allow-unqualified-build-mode`; the generated header's
`-- air2lean-profile:` record then carries `"admission": "unqualified-build-mode"`, which the
check reports and proof receipts copy with the rest of the header.

## Type

Every type is an object with `"k"`. Child types are type IDs (integers), never nested objects.

| `k` | Other fields |
|---|---|
| `int` | `signed: bool`, `bits: int` |
| `float` | `bits: int` (16, 32, 64, 80, 128; `c_longdouble` resolves to the target's width) |
| `bool`, `void`, `noreturn` | — |
| `ptr` | `size: "one"\|"many"\|"slice"\|"c"`, `const: bool`, `child: id`, `ptr_align: int` (the `align(N)` of the pointer type: explicit, or the child's ABI alignment; missing if the child has no layout yet), `volatile: bool`, `allowzero: bool`, `address_space: string` (the `std.builtin.AddressSpace` tag; the translator accepts only `generic`), `sentinel: bool`, optional `sentinel_byte: decimal string` (0.16.0 and later exports only: exact comptime sentinel for a u8 pointer; required by the byte allocSentinel model), `host_size: int` (a bit-pointer `&packed.field`: the host integer's size in bytes; else 0) (schema 5), `bit_offset: int` (a bit-pointer only: its field's first bit in the host integer) (schema 11), `vector_index: null\|int\|"runtime"` (present when `host_size` is nonzero or the pointer is a vector lane pointer: `null` for a packed field pointer, else the lane index of `&v[i]` into a vector, whose `host_size` is the lane count, not bytes (0.17.0 for every lane, earlier versions only for a lane that is not a power-of-two number of whole bytes; `Canon.lean` turns 0.17.0's whole-byte lanes back into 0.16.0's element pointers); `"runtime"` on 0.14.1/0.15.2 only. The translator models a comptime lane pointer into an integer or `bool` vector of an LLVM-backend x86_64/aarch64 profile as a bit-pointer into the vector's integer (`host_size` becomes `⌈n * w / 8⌉` bytes, `bit_offset` `i * w`, `docs/vector-proofs.md` §Lane pointers) and rejects every other lane pointer. An export without the field cannot tell the two apart, so the translator accepts a bit-pointer without it only as the result of a `struct_field_ptr` of a packed struct or union, never as a parameter, constant, load result or other value) |
| `array` | `len: int`, `child: id`, `sentinel: bool` (`[N:s]T`; schema 6) |
| `vector` | `len: int`, `child: id` (`@Vector(len, child)`; schema 9). The checked subset permits integer, float and bool lanes. Pointer vectors and nonidentity vector bitcasts are rejected. |
| `optional` | `child: id` |
| `error_union` | `error: id` (the error set type), `payload: id` |
| `error_set` | `errors: [string]` (sorted error names), `any: true` for `anyerror`, or `inferred: true` for an inferred set (`!T`) that is not resolved yet when the file is written |
| `struct` | `name: string`, `module: string` (§Identity), `layout: "auto"\|"extern"\|"packed"`, `fields: [{name, ty: id, offset: int}]` (`offset`: the field's byte offset; missing for a packed struct, and if the layout is not known; schema 5). A comptime field also has `comptime: true`; the translator rejects it. |
| `tuple` | `fields: [{ty: id, offset: int}]`, plus `comptime: true` on a comptime field (a comptime-known tuple item) |
| `enum` | `name: string`, `module: string`, `tag: id` (the integer tag type), `exhaustive: bool` (`false` for `enum(T) { …, _ }`), `fields: [{name, value: string}]` (the tag value in decimal) |
| `union` | `name: string`, `module: string`, `layout: "auto"\|"extern"\|"packed"`, `tag: id` (the tag enum; missing for a union without a tag), `safety_tag: id` (the hidden tag enum of a bare union in a safe build; schema 11), `fields: [{name, ty: id}]` in the order of the tag enum's fields |
| `struct`, `union` without known fields | `name`, `layout`, `no_fields: true` in place of the fields (schema 7). 0.16.0 knows the fields of a container only when its layout is wanted; a container that is only behind a pointer (`mem.Allocator.VTable`) can have none. The reader makes it `other`. |
| `other` | `name: string` (printed type; not in the subset). A function type (`fn (u32) u32`) is `other`; a pointer to it is a function pointer (M20). `anyopaque` is `other`; a pointer to it is a value only (Zig cannot load through it), so it is in the subset. |

Schema 5: a type that can be in memory (`int`, `bool`, `void`, `float`, `ptr`, `array`, `vector`, `optional`, `error_union`, `error_set`, `struct`, `enum`, `union`) also has `abi_size: int` and `abi_align: int`, in bytes, if its layout is known when the file is written. A vector's ABI size and alignment round up to a power of 2 (`n * @sizeOf(child)`, then `ceilPow2`); no special-casing in the exporter, which reads `ty.abiSize`/`ty.abiAlignment` for every in-memory type the same way. 0.16.0 resolves a container layout only when some code needs it (`want_layout`); 0.14.1 and 0.15.2 keep a status per container type (`Compat.hasLayout`). A type that a function body loads, stores or takes a field pointer of always has its layout.

`comptime_float` never reaches runtime AIR; if seen, it is `other`.

Example: `error{NotDigit}!u8` is `{"k": "error_union", "error": 5, "payload": 0}`, with type 5 being `{"k": "error_set", "errors": ["NotDigit"]}`.

## Inst

```json
{ "id": 5, "tag": "mul_safe", "ty": 3, "args": [Ref, Ref] }
```

| Field | When |
|---|---|
| `id` | always. AIR instruction index, unique in the function. |
| `tag` | always. AIR tag name, verbatim. Zig 0.17.0's renamed and split tags (`int_cast`, `bit_cast`, `ptr_cast`, `error_cast`, `agg_field_val`, …, `Canon.tagAliases017`) and `div_ceil` have the payload of the 0.16.0 tag they replace; the schema table lists them, and `Canon.versionTags` maps them to the 0.16.0 spelling after validation. |
| `ty` | result type ID. Missing only for `inferred_alloc*`. |
| `args` | operands, in AIR order |
| `param` | `arg`: ZIR parameter index |
| `body` | `block`, `loop`, `dbg_inline_block`, `try`, `try_cold`, `try_ptr`, `try_ptr_cold` (the error body) |
| `then`, `else` | `cond_br` (both are bodies) |
| `cases`, `else` | `switch_br`, `loop_switch_br`: `cases: [{items: [Ref], ranges: [[Ref, Ref]], body}]`, `else: body` |
| `target` | `br`, `switch_dispatch`: the block `id`; `repeat`: the loop `id` |
| `callee` | `call*`: a Ref |
| `index` | `struct_field_val`, `struct_field_ptr`, `union_init`: field index |
| `name` | `dbg_var_ptr`, `dbg_var_val`, `dbg_arg_inline`: variable name |
| `line` | `dbg_stmt`: 1-based line relative to the enclosing function's declaration (`1` is the declaration line), so the absolute line is `src.decl_line + line - 1`. Inside a `dbg_inline_block` it is relative to the inlined callee's declaration. |
| `column` | `dbg_stmt`: 1-based source column (additive provenance; older exports omit it) |
| `src` | `dbg_inline_block`: the inlined callee's declaration site, shaped like the function-level `src` (additive provenance) |
| `op` | `atomic_rmw`: `std.builtin.AtomicRmwOp` field name (schema 10); `reduce`, `reduce_optimized`: `std.builtin.ReduceOp` tag name (`And`, `Or`, `Xor`, `Min`, `Max`, `Add`, `Mul`); `cmp_vector`, `cmp_vector_optimized`: `std.math.CompareOperator` tag name (`lt`, `lte`, `eq`, `gte`, `gt`, `neq`) (schema 9) |
| `mask` | `shuffle`, `shuffle_one`, `shuffle_two`: the shuffle mask, one entry per output lane (schema 9) |
| `order` | `atomic_load`, `atomic_rmw`: `std.builtin.AtomicOrder` field name (schema 10) |
| `success_order`, `failure_order` | `cmpxchg_weak`, `cmpxchg_strong` (schema 10) |
| `unsupported` | `true` if the exporter does not decode this tag's operands |

`mul_add`: `args` is `[lhs, rhs, addend]` (the `pl_op` operand is the addend, written last).

Memory tags (schema 6), all `bin_op`: `memset`, `memset_safe` (the destination slice or array pointer, the item value), `memcpy`, `memmove` (the destination, the source pointer; 0.14.1 has no `memmove`). `tag_name` and `error_name` are `un_op`. The pointer tags `ptr_add`, `ptr_sub`, `ptr_elem_ptr`, `slice_elem_ptr`, `slice` (`ty_pl` + `Bin`), `ptr_elem_val`, `slice_elem_val`, `array_elem_val` (`bin_op`), `slice_ptr`, `slice_len`, `array_to_slice`, `ptr_slice_len_ptr`, `ptr_slice_ptr_ptr` (`ty_op`) have always been decoded.

Optional pointer tags (schema 5), all with `args: [pointer]`: `is_null_ptr`, `is_non_null_ptr` (`un_op`), `optional_payload_ptr`, `optional_payload_ptr_set` (`ty_op`).

Enum and union tags: `get_union_tag` (`ty_op`), `is_named_enum_value` (`un_op`), `set_union_tag` (`bin_op`: the union pointer, the tag), `union_init` (`args: [payload]`, `index`: the field). `@intFromEnum`/`@enumFromInt` are `bitcast`/`intcast`/`intcast_safe` with an enum on one side. The tag enum of `union(enum)` has the name `@typeInfo(U).@"union".tag_type.?`.

Float tags decoded as `bin_op`: `div_float`. As `un_op`: `sqrt sin cos tan exp exp2 log log2 log10 floor ceil round trunc_float`. As `ty_op`: `fptrunc fpext int_from_float int_from_float_safe float_from_int` (0.14.1 has no `int_from_float_safe`).

Vector tags (schema 9): `splat` is a `ty_op` (`args: [operand]`). `select` is `args: [lhs, rhs, pred]` (`pl_op` + `Air.Bin`: the predicate vector is the `pl_op` operand, written last). `reduce`/`reduce_optimized` are `args: [operand]` plus `op` (`std.builtin.ReduceOp` tag name). `cmp_vector`/`cmp_vector_optimized` are `args: [lhs, rhs]` plus `op` (`std.math.CompareOperator` tag name). `shuffle_one` (single source) and `shuffle_two` (two sources; 0.15.2+) have `args: [source]` or `args: [source_a, source_b]` plus `mask`: one entry per output lane, each `{"a": i}` (index into the first/only source), `{"b": i}` (index into the second source), `{"u": true}` (undefined lane), or `{"v": Ref}` (a comptime-known value lane; `shuffle_one` only). 0.14.1 has one `shuffle` tag instead, whose mask is a comptime `@Vector` of signed indices (negative for the second source); the exporter re-encodes it into the same four-shape mask so the reader never sees the version difference. Every `*_optimized` tag (float or vector) stays outside the subset: fast-math permits reassociation the translator does not claim to match, so the normalizer rejects any `_optimized` tag on sight, even one the exporter fully decoded (`reduce_optimized`, `cmp_vector_optimized`).

`assembly` (schema 8; M21 register operands, A01 read-write and memory lvalue outputs — `docs/generated-code.md` §Inline asm): `source: string` (the asm template, verbatim), `volatile: bool`, `clobbers: [string]` (the set fields of `std.builtin.assembly.Clobbers`: register/flag names, `memory`), `outputs: [{constraint, name, ref}]` (`ref` is the output pointer; missing when the output is the asm expression's own result, `-> T`), `inputs: [{constraint, name, ref}]` (`ref` is the input operand). 0.14.1 has no inline asm support: `assembly` is always `"unsupported": true` there.

Error-union pointer tags (schema 11), all with `args: [pointer]`: `is_err_ptr`, `is_non_err_ptr` (`un_op`), `unwrap_errunion_payload_ptr`, `unwrap_errunion_err_ptr`, `errunion_payload_ptr_set` (`ty_op`). `field_parent_ptr` (schema 11) is `args: [field pointer]` plus `index` (the field index, `Air.FieldParentPtr`).

Atomic and thread tags (schema 10, `docs/generated-code.md` § Atomics and threads): `atomic_store_unordered`, `atomic_store_monotonic`, `atomic_store_release`, `atomic_store_seq_cst` are `bin_op` (the pointer, the value); the order is the tag name's suffix, not a separate field. `atomic_load` is `args: [pointer]` plus `order`. `atomic_rmw` is `args: [pointer, operand]` plus `op` and `order` (`Air.AtomicRmw`'s extra struct). `cmpxchg_weak`/`cmpxchg_strong` are `args: [pointer, expected, new]` plus `success_order` and `failure_order` (`Air.Cmpxchg`'s extra struct). `Thread.spawn`/`.join` are ordinary calls (`call*`), not AIR tags — the translator recognizes the callee name (`Air2Lean/StdModels.lean`'s `stdModels`; `docs/std-models.md` §Thread model).

## Ref

One of:

| Shape | Meaning |
|---|---|
| `{"inst": 7}` | result of instruction 7 |
| `{"ty": 3, "val": "42"}` | constant, printed by Zig (`fmtValue`): integers in decimal, `true`/`false`, `void`. |
| `{"ty": 3, "fbits": "0x40490fdb"}` | float constant. `fbits`: the value `@bitCast` to an unsigned int of the same width, lowercase hex, zero-padded to `width/4` digits (`f80`: 20 digits). Read from the `InternPool` storage, not `fmtValue`. |
| `{"ty": 3, "undef": true}` | `undefined` |
| `{"ty": 9, "func": "basic.tardiness", "module": "root", "noreturn": false}` | function and its module (§Identity). `noreturn: true` when the return type is `noreturn` (panic handlers). A generic instance also has its `instance_key` (§Instances). A generic instance with a function as a comptime argument (`Thread.spawn`'s) also has `comptime_fn` and `comptime_fn_module`: that function and its module, and `comptime_fn_instance_key` if it is a keyed instance. |
| `{"ty": 9, "extern": "memset", "noreturn": false}` | extern function (`extern fn`, `@extern`, a function translate-c declares or demotes): its linker symbol; the file's `externs` table holds its declaration (§Extern calls). Before this form the exporter wrote `{"ty", "val": "(extern 'memset')"}`, which the translator rejected (`AIR_DECODE`). An extern that is not a function keeps the `val` form. |
| `{"ty": 1, "err": "NotDigit"}` | error value, or an error union constant in the error state. `ty`'s `k` (`error_set` vs `error_union`) disambiguates. |
| `{"ty": 1, "payload": Ref}` | error union constant holding a payload (nested `Ref`, recursively). |
| `{"ty": 2, "some": Ref}` | optional constant holding a payload (nested `Ref`, recursively). |
| `{"ty": 2, "null": true}` | optional constant, `null`. |
| `{"ty": 4, "enum": "5"}` | enum constant: its tag value in decimal (schema 4). |
| `{"ty": 6, "utag": Ref, "uval": Ref}` | union constant: the tag (an enum constant; missing for a union without a tag) and the payload (schema 4). |
| `{"ty": 8, "elems": [Ref, ...]}` | array, vector, struct or tuple constant: its constant items or fields (recursively nested constants only). An array with a sentinel has the sentinel as the last item (schema 6). A vector has no sentinel (schema 9). |
| `{"ty": 9, "ptr": {"global": 0, "off": 4}}` | pointer constant: byte `off` of global 0 (§Global). A pointer to a field of a global struct or slice, an optional or error-union payload, or an array element, at any nesting, is the global and the total offset (`payload_base: true` when a payload was crossed). The translator requires `off` to be at most the global's size, and on a `stage2_llvm` profile it rejects offsets at or one past an alignment-1 error-union payload (`tests/roadmap/const-bases`). A pointer without a global has `{"unsupported": "<reason>", "off": n}` instead: `int` (a nonzero constant `@ptrFromInt`), `comptime_alloc`, `comptime_field`, `arr_elem`, `field` of a packed struct, or a payload-resolution reason such as `payload_unbacked` (schema 6). |
| `{"ty": 9, "ptr": {"null": true, "off": 0}}` | address-zero scalar C/allowzero pointer constant. `null` must be true, the offset zero, and `global`/`unsupported` absent; the checker validates nullability. This additive schema-11 form needs the updated exporter. |
| `{"ty": 10, "slice_ptr": Ref, "slice_len": Ref}` | slice constant (schema 6). |

The translator accepts `{"inst": n}` as a top-level SSA operand. Inside a constant, every
recursive `Ref` in `payload`, `some`, `utag`, `uval`, `elems`, `slice_ptr` or `slice_len`
must itself be a constant. An instruction reference at any nesting depth is outside the
subset and is rejected before normalization; compiler-exported constants contain constants.

## Extern calls

An `externs` entry declares one extern function a call names (`{"extern": symbol}`):

```json
{"name": "memset", "library": null, "cc": "x86_64_sysv", "params": [10, 1, 0], "ret": 10,
 "varargs": false}
```

| Field | Meaning |
|---|---|
| `name` | the linker symbol (the extern's identity; never a Zig declaration name) |
| `library` | the library of `extern "lib" fn`, else `null` |
| `cc` | the calling convention's tag, as in the file's `export` |
| `params`, `ret` | type IDs of the declared parameter and return types (the variadic part excluded) |
| `varargs` | the declaration ends in `...` |

The translator decodes an extern call as a call to the callee `extern:<symbol>`, a form no
function name has. Before the whole-program checks it binds each extern call
(`Air2Lean/Check.lean` `resolveExterns`), by symbol only:

1. **Trusted base model.** A `--model-registry` entry whose `symbol` is `extern:<symbol>` and
   whose `extern` object gives the declared `library` and the `premise` (a `docs/premises.md`
   ID) that states the model's correspondence to the real primitive
   (`docs/external-models.md` §Extern functions), when the AIR set does not define the symbol
   (that combination is rejected). The call stays a model call. A registry entry
   for the Zig declaration's name does not bind the extern call.
2. **Translated definition.** Else the one function of the AIR set whose `export.name` is the
   symbol, with the declared `cc`. The call becomes a direct call of that definition, and its
   argument and result types are checked against the definition's parameters and return type
   like any direct call's. This is the static linker's rule for a program linked as one image
   with that strong definition (for example musl translated through the same route). A call
   to a symbol that several functions of the AIR set export is rejected.
3. Otherwise the program is rejected with `CALLEE_EXTERN_UNBOUND`, naming the symbol (and its
   library). A variadic extern (`varargs: true`) and a call to a `noreturn` extern are
   outside the subset. Each call's argument count and result type must be the entry's.

## Global

Schema 6. One entry per global that a pointer constant or a `runtime_nav_ptr` points into, in the order the exporter finds them (a pointer in the initial value of a global adds the global it points to after it).

| Field | Meaning |
|---|---|
| `name`, `module` | fully qualified name of a container-level `var` or `const`, and its module (§Identity). Missing for an unnamed constant (a string literal, the value behind `&.{…}`). |
| `ty` | type ID of the value |
| `const` | `false` only for a `var` |
| `threadlocal`, `extern` | a named global only. A `threadlocal` global is also listed when a `runtime_nav_ptr` names it. |
| `init` | the initial value, a Ref. Missing if Sema has not resolved it when the file is written (`Compat.navInfo`), and for an `extern`. |

`runtime_nav_ptr` (0.15.2+, `ty_nav`) has no `args`; `global` is the global's entry in
`globals` (an additive field of the current exporter). Zig emits it for a `threadlocal var`, an
`extern threadlocal var`, a DLL-imported or PC-relative `@extern`; the entry's flags say which,
and the translator admits only a non-`extern` `threadlocal` global
(`docs/generated-code.md` §Thread-local storage). An export without `global` (an older exporter
writes `"unsupported": true`) stays rejected. 0.14.1 has no such tag: it writes the address of a
`threadlocal` global as a pointer constant, which the translator rejects.

`try_ptr` and `try_ptr_cold` use one `args` operand (the pointer to the error union) and
`body` for the error branch. The instruction's `ty` is the payload pointer type. On
success they return that payload's address without reading or copying its bytes.

## Identity

A fully qualified name (`util.helper`) is the declaration's path inside its module. Two modules
can each have a `util.zig` with a `helper`, and a user `Thread.zig` declares `Thread` and
`Thread.spawn` like the standard library, so the name alone does not identify a function, a
type or a global (tests/roadmap/module-identity). The identity is the pair (module, name).

**Module.** The exporter writes the module next to every identity: the function's top-level
`module`, a function reference's `module` and `comptime_fn_module`, and the `module` of a
struct, enum or union type and of a named global. It is `root` for the compilation's main
module and `std` for the standard library, whatever the compiler calls them (0.16.0 names the
main module of `zig build-obj x.zig` `x`), and the module's `fully_qualified_name` otherwise
(the `-M<name>` of `zig build-obj`, the import name of `zig build`). The fields are additive:
older exports omit them, and `scripts/normalize-air.py` drops them from golden comparisons
(the generated Lean, which depends on them, is compared instead).

**Fail closed in the exporter.** One compilation never writes two different declarations under
one identity (`zig-patch/air-json/identity.zig`). The first declaration that writes an identity
claims it: a module name, an output file, a (module, name) of a struct, enum or union, or of a
named global. If a different declaration writes it later, the exporter reports
`two different declarations export the <kind> identity '<name>'` and the compiler exits with
status 1. Re-analysis of the same declaration may write its identity again. A function of the
`root` or `std` module keeps its historical file name, so a root and a std function with one
name (a user `ascii.zig` with `isDigit`, both exported) stop the export; a function of any
other module is stored under the SHA-256 of `<module>:<name>` ([filenames](export-names.md)).

**Keys in the translator.** Before parsing, `Air2Lean/Air/Identity.lean` replaces every
identity by its key, and every lookup uses the key: callee resolution, shared types and
globals, std models (`StdModels.lean`), the special std types (`mem.Allocator`, `Thread`,
`Io`), panic handlers and the Lean names.

| Module | Key |
|---|---|
| `std` | the name |
| `root` | the name (historical Lean names are unchanged), but `root:<name>` if the name's first component is a std namespace that the translator interprets by name: `mem`, `Thread`, `Io`, `atomic`, `time`, `debug` |
| other `m` | `m:<name>` (Lean name `m_<name>`) |

So only the std module can name a std model or a special std type. A user `Thread.zig` is
translated as user code (`root_Thread`, `root_Thread_spawn`); without its AIR, a call to it
has no target and is rejected. The translator rejects a key that two different (module, name)
pairs share (a root and a std declaration with one name), two input files with one function
key (`duplicate function name`), and a program that mixes files with and without `module`.

**Legacy exports.** AIR without a top-level `module` (an exporter before this field) is read
with its names as keys, as before. Such an export cannot tell modules apart: a name in a
dependency or a user file named like a std namespace is taken as the std name. Re-export with
the current exporter.

## Instances

The compiler names a generic instance `<generic>__anon_<n>` (`mem.Allocator.dupeZ__anon_16959`).
`n` is the instance's InternPool index: it depends on everything that the compilation analysed
before, so it differs between programs, source orders, Zig versions and host OSes. Two
compilations can even give two different instances one name. The name identifies the instance
only inside one compilation.

**Instance key.** The exporter writes an intrinsic identity next to the name: `instance_key`
for the function itself and for a function reference, `comptime_fn_instance_key` for a spawned
function (`zig-patch/air-json/identity.zig`). It is the SHA-256 (64 hex digits) of a canonical,
prefix-free encoding of what makes the instance (the compiler's own instance identity):

* the generic declaration: (module, fqn) (§Identity);
* each comptime argument, or "runtime" for a runtime parameter. A type is encoded by its
  stable identity: a struct, enum, union or opaque by its (module, name), every other type
  structurally (integer signedness and bits, pointer attributes and child, array length and
  sentinel, tuple fields, function types, error sets by their sorted names, …). A value is
  encoded with its type and its contents: an integer by sign and magnitude, a float by its bits,
  an aggregate by its elements, a pointer by its base (a declaration's identity, or the
  constant it points into) and byte offset, a function by its identity (a generic instance by
  its own encoding);
* the instance's parameter types, calling convention, `noalias` and `noinline` (an `anytype`
  parameter's type is not a comptime argument).

No InternPool index or compiler number enters the encoding, so the same instance has the same
key in every program that uses it and in every source order, and two different instances have
different keys. The encoding starts with its version (`air2lean-instance-v1`).

An instance has no key when an argument has no stable identity: a container whose
compiler-made name has a number (`__struct_<n>`, an `__anon_<n>` in it), a pointer into
comptime-mutable memory, a lazy `@sizeOf` before 0.16.0, or nesting deeper than 64. Such an
instance keeps the compiler's name (the translator numbers it, as for a legacy export). One
compilation never gives two instances one key: the exporter claims (generic, key) for the
instance (§Identity, *Fail closed*), and it claims the (module, name) of every container in a
key, as for a type table.

A key does not describe the instance's body: a user type `Foo` of two programs has the same
(module, name) whatever its fields. A cache of translated instances must also key the version
of the modules involved (architecture audit S1).

**Names in the translator.** `Air2Lean/Air/Anon.lean` renames a keyed instance
`<generic>__anon_<the key's first 12 hex digits>` (Lean `mem_Allocator_dupeZ__anon_ad013b83a643`)
in every identity, so the Lean name is the same in every program, version and host that
compiles the instance. A program with keyed instances emits its functions in the order of these
names. `Identity.rewrite` checks that a keyed name ends with its key's digits (one compiler name
with two keys, for example from two compilations, is rejected), and `checkProgram` that no two
keys share one name. An instance without a key keeps a number by first use
(`Anon.renumberAnon`), so a legacy export translates as before.

## Independent validation (V03)

`scripts/validate-air.py` re-checks exported AIR without the Lean decoder: strict JSON, unique
instruction IDs, operands that resolve to an earlier instruction of an enclosing body, no
instruction references inside constants, `br`/`repeat`/`switch_dispatch` targets that name an
enclosing block/loop/loop-switch, nonempty bodies ending in a `noreturn` terminator (a
`noreturn` call may precede it), type-table, parameter, global and child-type references,
acyclic value types, and tags and `"unsupported"` markers that match
`coverage/<zig_version>.json`. With no arguments it checks every committed golden AIR file;
CI runs it with `tests/roadmap/export-validation/test_validate_air.py`. Passing is a
structural fact about the export, not a semantic one (TRU-02). See the
[trust report](trust-report.md).
