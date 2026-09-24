# Generated Lean code

`lake exe air2lean <air-dir> -o <File.lean> --namespace <Ns> [--prefix <p>]` writes one Lean file for all JSON files in `<air-dir>`.

## Names

| Zig | Lean |
|---|---|
| function `basic.scale` (with `--prefix basic.`) | `Ns.scale` |
| any other `.` in a name | `_` |
| struct type `basic.Job` | `Ns.Job` (a `structure`, same field names) |
| a name that is a Lean keyword | `«name»` |

## Types

| Zig | Lean |
|---|---|
| `uN`, `iN`, `usize`, `isize` | `BitVec N` (`usize`/`isize` = `BitVec 64`) |
| `bool` | `Bool` |
| `void` | `Unit` |
| `[]const T` | `Array T'` |
| `struct` (layout `auto` or `extern`) | `structure … deriving Repr, Inhabited, DecidableEq` |

## Signature

```lean
import ZigLean
namespace Ns
def scale (a : BitVec 32) (b : BitVec 8) : Zig.Result (BitVec 32) := ...
```

- Parameters keep the Zig order. Their names are `p0`, `p1`, … unless a `dbg_arg_inline` gives the source name.
- A function that panics (overflow, bounds, `unreachable`) returns `throw e`; for the error values see `Zig.Error`.
- A function that does not terminate returns `none` (the `Option` layer of `Zig.Result`).
- Functions come in dependency order. A function that calls itself, or a group that calls each other, becomes a `mutual` block with `partial_fixpoint`.
