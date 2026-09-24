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

## Loops

Each AIR `loop` body is its own top-level def, named `<fn>.loop<id>` (AIR instruction id of the `loop`), emitted just before `def <fn>` — so a proof can name the loop body directly (`Zig.loop_spec (body := <fn>.loop<id> …) …`), instead of only the anonymous term `Zig.loop` used to take inline.

```lean
def sum.again10 : sumExit → Bool
  | .rep10 => true
  | _ => false

def sum.loop10 (p0 : Array (BitVec 32)) (i8 : BitVec 64) : Zig.M sumLocals sumExit := do
  ...

def sum (p0 : Array (BitVec 32)) : Zig.Result (BitVec 64) := do
  ...
    Zig.loop (sum.loop10 p0 i8) sum.again10
  ...
```

- Parameters are the loop body's captures: every SSA value (`p<i>`/`i<id>`) it reads that is bound outside it. Names match the body text exactly (no renaming); order is params first (param order), then by id.
- A `Locals` field (`total`, `local5`, …) is not a capture: it goes through `get`/`modify`, unaffected by which def the code sits in.
- A nested loop gets its own def too, emitted before its enclosing loop's def; the enclosing loop's body calls it the same way `<fn>` calls the outer one.
- The repeat test is a named def `<fn>.again<id>` too. An inline `fun e => match …` would get a new matcher each time it is elaborated, so a proof could not restate it.

## Panics

`Zig.Error` has 5 constructors: `overflow`, `outOfBounds`, `divByZero`, `unreachable`, `panic`. Checked arithmetic (`add_safe`/`sub_safe`/`mul_safe`) and `unreach` map directly; a `call` to a noreturn function (AIR's `func` field, e.g. `debug.FullPanic((function 'defaultPanic')).outOfBounds`) is a Zig std lib panic-handler function named by its trailing `.`-segment — `Air2Lean/Emit.lean`'s `panicErrorFor` maps that segment to a constructor:

| segment | constructor |
|---|---|
| `integerOverflow`, `integerOutOfBounds`, `shlOverflow`, `shrOverflow` | `.overflow` |
| `outOfBounds` | `.outOfBounds` |
| `divideByZero` | `.divByZero` |
| `reachedUnreachable` | `.unreachable` |
| anything else (outside v0's scope) | `.panic` |

`tests/diff/harness.zig` installs a matching `std.builtin.panic` override (same member names, one per Zig safety check) so the Zig side reports which check tripped instead of aborting; `scripts/diff.sh` compares that name — via the same table (`expected_ctor_for_zig_kind`) — against the `Zig.Error` constructor the Lean side actually threw. A `fail`/`fail` line only counts as a match when the kinds agree; a Zig kind with no table entry, or `unknown` (the child died without reporting one, e.g. a signal), is always a mismatch.
