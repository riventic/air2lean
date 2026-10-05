# AIR JSON format (schema 12)

The patched compiler writes one file per function: `$ZIG_AIR_JSON_DIR/<fqn>.json`. `ZIG_AIR_JSON_FILTER=<prefix>,<prefix>,…` limits output to functions whose fully qualified name starts with one of the prefixes. The format does not depend on the Zig version: AIR tags are written verbatim, and `Air2Lean/Air/Normalize.lean` maps them per version.

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
  "params": [0, 1],
  "ret": 3,
  "body": [ Inst, ... ],
  "globals": [ Global, ... ],
  "types": [ Type, ... ]
}
```

| Field | Meaning |
|---|---|
| `schema` | Supported versions are 1–12. Schema 12 requires complete profile metadata; schema 1–11 select the named `legacy-abi64-le` assumptions. Unsupported/future schemas fail closed. |
| `profile` | Mandatory schema-12 target/build facts from the function's owning module and compiler configuration. All facts must agree across a program. See [Target and build profiles](profiles.md) for the exact contract, accepted model ABI scopes and numerical-model disclosure. Metadata is not a shipping-binary correspondence theorem. |
| `target_endian` | Target byte order: `"little"` or `"big"` (additive schema 11 metadata). The current translator rejects explicit non-little-endian targets. Legacy schema 1–11 files without this field are accepted under the named little-endian reference-target assumption; their target has not been verified. Schema 12 also requires `profile.endian`. |
| `params` | type ID of each runtime parameter, in order |
| `ret` | type ID of the return type |
| `body` | main body (AIR `getMainBody`) |
| `globals` | the globals that pointer constants point into (§Global). A global ID is an index into this array. Missing if the function has no pointer constant (schema 6). |
| `types` | type table. A type ID is an index into this array. Each type is listed once. |

The reader rejects cyclic value types (pointer recursion is allowed), out-of-range type IDs,
SSA uses before their definition or outside their lexical body, and malformed constant
shapes. Aggregate constants must have the exact number and types of their items; optional,
error-union and union payloads must match their child type. Presence markers such as `undef`,
`null` and shuffle `u` must be literal `true`. Supplied flags such as `noreturn`, `volatile`
and `unsupported` must be booleans. A reference or shuffle lane has exactly one value form.

## Type

Every type is an object with `"k"`. Child types are type IDs (integers), never nested objects.

| `k` | Other fields |
|---|---|
| `int` | `signed: bool`, `bits: int` |
| `float` | `bits: int` (16, 32, 64, 80, 128; `c_longdouble` resolves to the target's width) |
| `bool`, `void`, `noreturn` | — |
| `ptr` | `size: "one"\|"many"\|"slice"\|"c"`, `const: bool`, `child: id`, `ptr_align: int` (the `align(N)` of the pointer type: explicit, or the child's ABI alignment; missing if the child has no layout yet), `volatile: bool`, `allowzero: bool`, `sentinel: bool`, `host_size: int` (a bit-pointer `&packed.field`: the host integer's size in bytes; else 0) (schema 5), `bit_offset: int` (a bit-pointer only: its field's first bit in the host integer) (schema 11) |
| `array` | `len: int`, `child: id`, `sentinel: bool` (`[N:s]T`; schema 6) |
| `vector` | `len: int`, `child: id` (`@Vector(len, child)`; schema 9). The checked subset permits integer, float and bool lanes. Pointer vectors and nonidentity vector bitcasts are rejected. |
| `optional` | `child: id` |
| `error_union` | `error: id` (the error set type), `payload: id` |
| `error_set` | `errors: [string]` (sorted error names), `any: true` for `anyerror`, or `inferred: true` for an inferred set (`!T`) that is not resolved yet when the file is written |
| `struct` | `name: string`, `layout: "auto"\|"extern"\|"packed"`, `fields: [{name, ty: id, offset: int}]` (`offset`: the field's byte offset; missing for a packed struct, and if the layout is not known; schema 5) |
| `tuple` | `fields: [{ty: id, offset: int}]` |
| `enum` | `name: string`, `tag: id` (the integer tag type), `exhaustive: bool` (`false` for `enum(T) { …, _ }`), `fields: [{name, value: string}]` (the tag value in decimal) |
| `union` | `name: string`, `layout: "auto"\|"extern"\|"packed"`, `tag: id` (the tag enum; missing for a union without a tag), `safety_tag: id` (the hidden tag enum of a bare union in a safe build; schema 11), `fields: [{name, ty: id}]` in the order of the tag enum's fields |
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
| `tag` | always. AIR tag name, verbatim. |
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
| `line` | `dbg_stmt`: 1-based source line |
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

`assembly` (schema 8; M21, register operands only): `source: string` (the asm template, verbatim), `volatile: bool`, `clobbers: [string]` (register/flag names), `outputs: [{constraint, name, ref}]` (`ref` is the output pointer; missing when the output is the asm expression's own result, `-> T`), `inputs: [{constraint, name, ref}]` (`ref` is the input operand). 0.14.1 has no inline asm support: `assembly` is always `"unsupported": true` there.

Error-union pointer tags (schema 11), all with `args: [pointer]`: `is_err_ptr`, `is_non_err_ptr` (`un_op`), `unwrap_errunion_payload_ptr`, `unwrap_errunion_err_ptr`, `errunion_payload_ptr_set` (`ty_op`). `field_parent_ptr` (schema 11) is `args: [field pointer]` plus `index` (the field index, `Air.FieldParentPtr`).

Atomic and thread tags (schema 10, `docs/generated-code.md` § Atomics and threads): `atomic_store_unordered`, `atomic_store_monotonic`, `atomic_store_release`, `atomic_store_seq_cst` are `bin_op` (the pointer, the value); the order is the tag name's suffix, not a separate field. `atomic_load` is `args: [pointer]` plus `order`. `atomic_rmw` is `args: [pointer, operand]` plus `op` and `order` (`Air.AtomicRmw`'s extra struct). `cmpxchg_weak`/`cmpxchg_strong` are `args: [pointer, expected, new]` plus `success_order` and `failure_order` (`Air.Cmpxchg`'s extra struct). `Thread.spawn`/`.join` are ordinary calls (`call*`), not AIR tags — the translator recognizes the callee name (`Air2Lean.Check.lean`'s `rejectedThreadFn?`; `docs/std-models.md` §Thread model).

## Ref

One of:

| Shape | Meaning |
|---|---|
| `{"inst": 7}` | result of instruction 7 |
| `{"ty": 3, "val": "42"}` | constant, printed by Zig (`fmtValue`): integers in decimal, `true`/`false`, `void`. |
| `{"ty": 3, "fbits": "0x40490fdb"}` | float constant. `fbits`: the value `@bitCast` to an unsigned int of the same width, lowercase hex, zero-padded to `width/4` digits (`f80`: 20 digits). Read from the `InternPool` storage, not `fmtValue`. |
| `{"ty": 3, "undef": true}` | `undefined` |
| `{"ty": 9, "func": "basic.tardiness", "noreturn": false}` | function. `noreturn: true` when the return type is `noreturn` (panic handlers). |
| `{"ty": 1, "err": "NotDigit"}` | error value, or an error union constant in the error state. `ty`'s `k` (`error_set` vs `error_union`) disambiguates. |
| `{"ty": 1, "payload": Ref}` | error union constant holding a payload (nested `Ref`, recursively). |
| `{"ty": 2, "some": Ref}` | optional constant holding a payload (nested `Ref`, recursively). |
| `{"ty": 2, "null": true}` | optional constant, `null`. |
| `{"ty": 4, "enum": "5"}` | enum constant: its tag value in decimal (schema 4). |
| `{"ty": 6, "utag": Ref, "uval": Ref}` | union constant: the tag (an enum constant; missing for a union without a tag) and the payload (schema 4). |
| `{"ty": 8, "elems": [Ref, ...]}` | array, vector, struct or tuple constant: its constant items or fields (recursively nested constants only). An array with a sentinel has the sentinel as the last item (schema 6). A vector has no sentinel (schema 9). |
| `{"ty": 9, "ptr": {"global": 0, "off": 4}}` | pointer constant: byte `off` of global 0 (§Global). A pointer to a field of a global struct or slice is the global and the total offset. A pointer without a global has `{"unsupported": "<base>", "off": n}` instead: `int` (a nonzero constant `@ptrFromInt`), `comptime_alloc`, `comptime_field`, `eu_payload`, `opt_payload`, `arr_elem`, or `field` of a packed struct (schema 6). |
| `{"ty": 9, "ptr": {"null": true, "off": 0}}` | address-zero scalar C/allowzero pointer constant. `null` must be true, the offset zero, and `global`/`unsupported` absent; the checker validates nullability. This additive schema-11 form needs the updated exporter. |
| `{"ty": 10, "slice_ptr": Ref, "slice_len": Ref}` | slice constant (schema 6). |

The translator accepts `{"inst": n}` as a top-level SSA operand. Inside a constant, every
recursive `Ref` in `payload`, `some`, `utag`, `uval`, `elems`, `slice_ptr` or `slice_len`
must itself be a constant. An instruction reference at any nesting depth is outside the
subset and is rejected before normalization; compiler-exported constants contain constants.

## Global

Schema 6. One entry per global that a pointer constant points into, in the order the exporter finds them (a pointer in the initial value of a global adds the global it points to after it).

| Field | Meaning |
|---|---|
| `name` | fully qualified name of a container-level `var` or `const`. Missing for an unnamed constant (a string literal, the value behind `&.{…}`). |
| `ty` | type ID of the value |
| `const` | `false` only for a `var` |
| `threadlocal`, `extern` | a named global only |
| `init` | the initial value, a Ref. Missing if Sema has not resolved it when the file is written (`Compat.navInfo`), and for an `extern`. |

`try_ptr` and `try_ptr_cold` use one `args` operand (the pointer to the error union) and
`body` for the error branch. The instruction's `ty` is the payload pointer type. On
success they return that payload's address without reading or copying its bytes.
