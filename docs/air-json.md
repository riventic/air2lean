# AIR JSON format (schema 2)

The patched compiler writes one file per function: `$ZIG_AIR_JSON_DIR/<fqn>.json`. `ZIG_AIR_JSON_FILTER=<prefix>` limits output to functions whose fully qualified name starts with the prefix. The format does not depend on the Zig version: AIR tags are written verbatim, and `Air2Lean/Air/Normalize.lean` maps them per version.

## File

```json
{
  "schema": 2,
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
| `error_union` | `error: id` (the error set type), `payload: id` |
| `error_set` | `errors: [string]` (sorted error names), `any: true` for `anyerror`, or `inferred: true` for an inferred set (`!T`) that is not resolved yet when the file is written |
| `struct` | `name: string`, `layout: "auto"\|"extern"\|"packed"`, `fields: [{name, ty: id}]` |
| `tuple` | `fields: [{ty: id}]` |
| `other` | `name: string` (printed type; not in the subset) |

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
| `index` | `struct_field_val`, `struct_field_ptr`: field index |
| `name` | `dbg_var_ptr`, `dbg_var_val`, `dbg_arg_inline`: variable name |
| `line` | `dbg_stmt`: 1-based source line |
| `unsupported` | `true` if the exporter does not decode this tag's operands |

## Ref

One of:

| Shape | Meaning |
|---|---|
| `{"inst": 7}` | result of instruction 7 |
| `{"ty": 3, "val": "42"}` | constant, printed by Zig (`fmtValue`): integers in decimal, `true`/`false`. An optional prints `null` or its payload's text. For a payload other than an integer, `bool` or `void` (e.g. `?(E!T)` in the error state prints `error.Bad`), the text is `fmtValue`'s own and the translator rejects the constant. |
| `{"ty": 3, "undef": true}` | `undefined` |
| `{"ty": 9, "func": "basic.tardiness", "noreturn": false}` | function. `noreturn: true` when the return type is `noreturn` (panic handlers). |
| `{"ty": 1, "err": "NotDigit"}` | error value, or an error union constant in the error state. `ty`'s `k` (`error_set` vs `error_union`) disambiguates. |
| `{"ty": 1, "payload": Ref}` | error union constant holding a payload (nested `Ref`, recursively). |

`try_ptr` and `try_ptr_cold` (the pointer form of `try`) are always `"unsupported": true` — not decoded.
