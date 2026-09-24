# AIR JSON format (schema 1)

The patched compiler writes one file per function: `$ZIG_AIR_JSON_DIR/<fqn>.json`. `ZIG_AIR_JSON_FILTER=<prefix>` limits output to functions whose fully qualified name starts with the prefix. The format does not depend on the Zig version: AIR tags are written verbatim, and `Air2Lean/Air/Normalize.lean` maps them per version.

## File

```json
{
  "schema": 1,
  "zig_version": "0.15.2",
  "name": "basic.scale",
  "params": [0, 1],
  "ret": 3,
  "body": [ Inst, ... ],
  "types": [ Type, ... ]
}
```

| Field | Meaning |
|---|---|
| `params` | type ID of each runtime parameter, in order |
| `ret` | type ID of the return type |
| `body` | main body (AIR `getMainBody`) |
| `types` | type table. A type ID is an index into this array. Each type is listed once. |

## Type

Every type is an object with `"k"`. Child types are type IDs (integers), never nested objects.

| `k` | Other fields |
|---|---|
| `int` | `signed: bool`, `bits: int` |
| `bool`, `void`, `noreturn` | — |
| `ptr` | `size: "one"\|"many"\|"slice"\|"c"`, `const: bool`, `child: id` |
| `array` | `len: int`, `child: id` |
| `optional` | `child: id` |
| `struct` | `name: string`, `layout: "auto"\|"extern"\|"packed"`, `fields: [{name, ty: id}]` |
| `tuple` | `fields: [{ty: id}]` |
| `other` | `name: string` (printed type; not in the subset) |

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
| `body` | `block`, `loop`, `dbg_inline_block` |
| `then`, `else` | `cond_br` (both are bodies) |
| `cases`, `else` | `switch_br`, `loop_switch_br`: `cases: [{items: [Ref], ranges: [[Ref, Ref]], body}]`, `else: body` |
| `target` | `br`, `switch_dispatch`: the block `id`; `repeat`: the loop `id` |
| `callee` | `call*`: a Ref |
| `index` | `struct_field_val`, `struct_field_ptr`: field index |
| `name` | `dbg_var_ptr`, `dbg_var_val`, `dbg_arg_inline`: variable name |
| `line` | `dbg_stmt`: 1-based source line |
| `unsupported` | `true` if the exporter does not decode this tag's operands |

## Ref

One of:

| Shape | Meaning |
|---|---|
| `{"inst": 7}` | result of instruction 7 |
| `{"ty": 3, "val": "42"}` | constant, printed by Zig (`fmtValue`): integers in decimal, `true`/`false` |
| `{"ty": 3, "undef": true}` | `undefined` |
| `{"ty": 9, "func": "basic.tardiness", "noreturn": false}` | function. `noreturn: true` when the return type is `noreturn` (panic handlers). |
