# AIR JSON format (schema 8)

The patched compiler writes one file per function: `$ZIG_AIR_JSON_DIR/<fqn>.json`. `ZIG_AIR_JSON_FILTER=<prefix>,<prefix>,…` limits output to functions whose fully qualified name starts with one of the prefixes. The format does not depend on the Zig version: AIR tags are written verbatim, and `Air2Lean/Air/Normalize.lean` maps them per version.

## File

```json
{
  "schema": 8,
  "zig_version": "0.15.2",
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
| `params` | type ID of each runtime parameter, in order |
| `ret` | type ID of the return type |
| `body` | main body (AIR `getMainBody`) |
| `globals` | the globals that pointer constants point into (§Global). A global ID is an index into this array. Missing if the function has no pointer constant (schema 6). |
| `types` | type table. A type ID is an index into this array. Each type is listed once. |

## Type

Every type is an object with `"k"`. Child types are type IDs (integers), never nested objects.

| `k` | Other fields |
|---|---|
| `int` | `signed: bool`, `bits: int` |
| `float` | `bits: int` (16, 32, 64, 80, 128; `c_longdouble` resolves to the target's width) |
| `bool`, `void`, `noreturn` | — |
| `ptr` | `size: "one"\|"many"\|"slice"\|"c"`, `const: bool`, `child: id`, `ptr_align: int` (the `align(N)` of the pointer type: explicit, or the child's ABI alignment; missing if the child has no layout yet), `volatile: bool`, `allowzero: bool`, `sentinel: bool`, `host_size: int` (a bit-pointer `&packed.field`: the host integer's size in bytes; else 0) (schema 5) |
| `array` | `len: int`, `child: id`, `sentinel: bool` (`[N:s]T`; schema 6) |
| `optional` | `child: id` |
| `error_union` | `error: id` (the error set type), `payload: id` |
| `error_set` | `errors: [string]` (sorted error names), `any: true` for `anyerror`, or `inferred: true` for an inferred set (`!T`) that is not resolved yet when the file is written |
| `struct` | `name: string`, `layout: "auto"\|"extern"\|"packed"`, `fields: [{name, ty: id, offset: int}]` (`offset`: the field's byte offset; missing for a packed struct, and if the layout is not known; schema 5) |
| `tuple` | `fields: [{ty: id, offset: int}]` |
| `enum` | `name: string`, `tag: id` (the integer tag type), `exhaustive: bool` (`false` for `enum(T) { …, _ }`), `fields: [{name, value: string}]` (the tag value in decimal) |
| `union` | `name: string`, `layout: "auto"\|"extern"\|"packed"`, `tag: id` (the tag enum; missing for a union without a tag), `fields: [{name, ty: id}]` in the order of the tag enum's fields |
| `struct`, `union` without known fields | `name`, `layout`, `no_fields: true` in place of the fields (schema 7). 0.16.0 knows the fields of a container only when its layout is wanted; a container that is only behind a pointer (`mem.Allocator.VTable`) can have none. The reader makes it `other`. |
| `other` | `name: string` (printed type; not in the subset) |

Schema 5: a type that can be in memory (`int`, `bool`, `void`, `float`, `ptr`, `array`, `optional`, `error_union`, `error_set`, `struct`, `enum`, `union`) also has `abi_size: int` and `abi_align: int`, in bytes, if its layout is known when the file is written. 0.16.0 resolves a container layout only when some code needs it (`want_layout`); 0.14.1 and 0.15.2 keep a status per container type (`Compat.hasLayout`). A type that a function body loads, stores or takes a field pointer of always has its layout.

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
| `body` | `block`, `loop`, `dbg_inline_block`, `try`, `try_cold` (the error body) |
| `then`, `else` | `cond_br` (both are bodies) |
| `cases`, `else` | `switch_br`, `loop_switch_br`: `cases: [{items: [Ref], ranges: [[Ref, Ref]], body}]`, `else: body` |
| `target` | `br`, `switch_dispatch`: the block `id`; `repeat`: the loop `id` |
| `callee` | `call*`: a Ref |
| `index` | `struct_field_val`, `struct_field_ptr`, `union_init`: field index |
| `name` | `dbg_var_ptr`, `dbg_var_val`, `dbg_arg_inline`: variable name |
| `line` | `dbg_stmt`: 1-based source line |
| `order` | `atomic_load`, `atomic_rmw`: `std.builtin.AtomicOrder` field name (schema 8) |
| `op` | `atomic_rmw`: `std.builtin.AtomicRmwOp` field name (schema 8) |
| `success_order`, `failure_order` | `cmpxchg_weak`, `cmpxchg_strong` (schema 8) |
| `unsupported` | `true` if the exporter does not decode this tag's operands |

`mul_add`: `args` is `[lhs, rhs, addend]` (the `pl_op` operand is the addend, written last).

Memory tags (schema 6), all `bin_op`: `memset`, `memset_safe` (the destination slice or array pointer, the item value), `memcpy`, `memmove` (the destination, the source pointer; 0.14.1 has no `memmove`). `tag_name` and `error_name` are `un_op`. The pointer tags `ptr_add`, `ptr_sub`, `ptr_elem_ptr`, `slice_elem_ptr`, `slice` (`ty_pl` + `Bin`), `ptr_elem_val`, `slice_elem_val`, `array_elem_val` (`bin_op`), `slice_ptr`, `slice_len`, `array_to_slice`, `ptr_slice_len_ptr`, `ptr_slice_ptr_ptr` (`ty_op`) have always been decoded.

Optional pointer tags (schema 5), all with `args: [pointer]`: `is_null_ptr`, `is_non_null_ptr` (`un_op`), `optional_payload_ptr`, `optional_payload_ptr_set` (`ty_op`).

Enum and union tags: `get_union_tag` (`ty_op`), `is_named_enum_value` (`un_op`), `set_union_tag` (`bin_op`: the union pointer, the tag), `union_init` (`args: [payload]`, `index`: the field). `@intFromEnum`/`@enumFromInt` are `bitcast`/`intcast`/`intcast_safe` with an enum on one side. The tag enum of `union(enum)` has the name `@typeInfo(U).@"union".tag_type.?`.

Float tags decoded as `bin_op`: `div_float`. As `un_op`: `sqrt sin cos tan exp exp2 log log2 log10 floor ceil round trunc_float`. As `ty_op`: `fptrunc fpext int_from_float int_from_float_safe float_from_int` (0.14.1 has no `int_from_float_safe`). Every `*_optimized` float tag stays `unsupported`.

Atomic and thread tags (schema 8, `docs/generated-code.md` § Atomics and threads): `atomic_store_unordered`, `atomic_store_monotonic`, `atomic_store_release`, `atomic_store_seq_cst` are `bin_op` (the pointer, the value); the order is the tag name's suffix, not a separate field. `atomic_load` is `args: [pointer]` plus `order`. `atomic_rmw` is `args: [pointer, operand]` plus `op` and `order` (`Air.AtomicRmw`'s extra struct). `cmpxchg_weak`/`cmpxchg_strong` are `args: [pointer, expected, new]` plus `success_order` and `failure_order` (`Air.Cmpxchg`'s extra struct). `Thread.spawn`/`.join` are ordinary calls (`call*`), not AIR tags — the translator recognizes the callee name (`Air2Lean.Check.lean`'s `rejectedThreadFn?`; `docs/std-models.md` §Thread model).

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
| `{"ty": 8, "elems": [Ref, ...]}` | array, struct or tuple constant: its items or fields. An array with a sentinel has the sentinel as the last item (schema 6). |
| `{"ty": 9, "ptr": {"global": 0, "off": 4}}` | pointer constant: byte `off` of global 0 (§Global). A pointer to a field of a global struct or slice is the global and the total offset. A pointer without a global has `{"unsupported": "<base>", "off": n}` instead: `int` (`@ptrFromInt`), `comptime_alloc`, `comptime_field`, `eu_payload`, `opt_payload`, `arr_elem`, or `field` of a packed struct (schema 6). |
| `{"ty": 10, "slice_ptr": Ref, "slice_len": Ref}` | slice constant (schema 6). |

## Global

Schema 6. One entry per global that a pointer constant points into, in the order the exporter finds them (a pointer in the initial value of a global adds the global it points to after it).

| Field | Meaning |
|---|---|
| `name` | fully qualified name of a container-level `var` or `const`. Missing for an unnamed constant (a string literal, the value behind `&.{…}`). |
| `ty` | type ID of the value |
| `const` | `false` only for a `var` |
| `threadlocal`, `extern` | a named global only |
| `init` | the initial value, a Ref. Missing if Sema has not resolved it when the file is written (`Compat.navInfo`), and for an `extern`. |

`try_ptr` and `try_ptr_cold` (the pointer form of `try`) are always `"unsupported": true` — not decoded.
