# Generated Lean code

`lake exe air2lean <air-dir> -o <File.lean> --namespace <Ns> [--prefix <p>] [--float-semantics ieee|compiler-rt]` writes one Lean file for all JSON files in `<air-dir>`.

`--float-semantics` (default `ieee`) picks the model behind `@divExact`/`/`/`@divTrunc`/`@divFloor`/`@mulAdd` on a float operand: `ieee` (what a proof assumes) or `compiler-rt` (bit-exact port of the compiler_rt routines the reference target, `x86_64-linux -mcpu=baseline`, actually calls; `docs/floats.md` §Semantics). `scripts/check.sh` reads one example's opt-in from `examples/<ex>/translate.args` (one line of extra CLI args) if present, so most examples stay on the default with no translator invocation to update.

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
| `f16`, `f32`, `f64`, `f80`, `f128` | `Zig.F16`, `Zig.F32`, `Zig.F64`, `Zig.F80`, `Zig.F128` (`Zig.Float .f16` … `.f128`; docs/floats.md) |
| `bool` | `Bool` |
| `void` | `Unit` |
| `[]const T` | `Array T'` |
| `?T` (`T` not a pointer) | `Option T'` |
| `struct` (layout `auto` or `extern`) | `structure … deriving Repr, Inhabited, DecidableEq` |
| `E!T` (error union) | `Except Zig.ErrName T'` |
| error set (`error{A, B}`, `anyerror`) | `Zig.ErrName` (`abbrev ErrName := String`; an error's identity is its name) |

## Signature

```lean
import ZigLean
namespace Ns
def scale (a : BitVec 32) (b : BitVec 8) : Zig.Result (BitVec 32) := ...
```

- Parameters keep the Zig order. Their names are `p0`, `p1`, … unless a `dbg_arg_inline` gives the source name.
- A function that panics (overflow, bounds, `unreachable`) returns `throw e`; for the error values see `Zig.Error`.
- A function that does not terminate returns `none` (the `Option` layer of `Zig.Result`).
- Functions come in dependency order: a callee before its caller.
- A recursive group (a function that calls itself, or functions that call each other) becomes one `mutual` block. The group's `Locals`/`Exit` types and `again<k>` defs come before the block. In the block, every function def and every `loop<k>` def has `partial_fixpoint`: a loop body can call a group member. The monotonicity lemmas in `ZigLean/Basic.lean` (`Zig.call`, `run'`, `Zig.loop`) let Lean accept these defs.

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

`Zig.Error` has 6 constructors: `overflow`, `outOfBounds`, `divByZero`, `unreachable`, `panic`, `unspecified`. `unspecified` = Zig leaves the result open and the model does not choose one (the bits of a NaN, `@intFromFloat` without a safety check out of range). Checked arithmetic (`add_safe`/`sub_safe`/`mul_safe`) and `unreach` map directly; a `call` to a noreturn function (AIR's `func` field, e.g. `debug.FullPanic((function 'defaultPanic')).outOfBounds`) is a Zig std lib panic-handler function named by its trailing `.`-segment — `Air2Lean/Air/Op.lean`'s `panicErrorFor?` maps that segment to a constructor, and `Check.lean` rejects a noreturn callee outside the table:

| segment | constructor |
|---|---|
| `integerOverflow`, `integerOutOfBounds`, `integerPartOutOfBounds`, `shlOverflow`, `shrOverflow` | `.overflow` |
| `outOfBounds` | `.outOfBounds` |
| `divideByZero` | `.divByZero` |
| `reachedUnreachable` | `.unreachable` |
| `exactDivisionRemainder`, `unwrapNull`, `unwrapError`, `call` (`@panic`) | `.panic` |

`tests/diff/common.zig` installs a matching `std.builtin.panic` override (same member names, one per Zig safety check), shared by every example's `tests/diff/<ex>/harness.zig`, so the Zig side reports which check tripped instead of aborting; `scripts/diff.sh` compares that name — via the same table (`expected_ctor_for_zig_kind`) — against the `Zig.Error` constructor the Lean side actually threw. A `fail`/`fail` line only counts as a match when the kinds agree; a Zig kind with no table entry, or `unknown` (the child died without reporting one, e.g. a signal), is always a mismatch. A Lean `unspecified` matches any Zig line; the number of such lines per function must equal `tests/diff/<ex>/unspecified.txt` (`<fn> <count>` lines, default 0).

## Differential test

One example directory `examples/<ex>/` = one namespace `<Ex>` = one prefix `<ex>.`. Per example:

| Path | What |
|---|---|
| `examples/<ex>/<ex>.zig` | The Zig source under test |
| `tests/golden/<v>/<ex>/air/` | Golden AIR-JSON, checked by `scripts/check.sh` |
| `Proofs/<Ex>/Gen.lean` | Committed translator output (`--namespace <Ex> --prefix <ex>.`) |
| `tests/diff/<ex>/inputs/<fn>.jsonl` | Generated inputs, one file per function (`tests/diff/gen_inputs.zig`) |
| `tests/diff/<ex>/harness.zig` | Per-function dispatch only: imports `<ex>` + `common`, forks, writes `tests/diff/out/zig/<ex>/<fn>.jsonl` |
| `tests/diff/out/lean/<ex>/<fn>.jsonl` | Lean-side output, written by `tests/diff/Diff.lean` (one exe, dispatches by example+function) |

`tests/diff/common.zig` holds everything shared across examples: the fork-per-input child, the panic override, `renderPayload` (the protocol below, generic over `@typeInfo(T)`, so one function serializes ints, `bool`, and nested `?T`/`E!T`), and the JSONL read/write loop. A harness only lists its example's functions.

`scripts/check.sh`, `scripts/diff.sh`, and `scripts/mutate.sh` loop over `AIR2LEAN_EXAMPLES` (default: every dir in `examples/`).

### Protocol

One JSONL line per input, `{"ok": v}` / `{"fail": "<kind>"}` / `{"diverge": true}` (`Zig.Result`'s `none` — non-termination), `v` per Zig type:

| Zig type | `v` |
|---|---|
| plain int | bare decimal, or quoted decimal for a wide (`u64`/`usize`) result |
| `bool` | `0` or `1` |
| `?T` | `null`, or `T`'s `v` |
| `E!T` | `{"err": "<Name>"}` (the bare error name, e.g. `@errorName` on the Zig side), or `T`'s `v` |

A `?T`/`E!T` result nests: e.g. `?(E!T)` renders as `null`, `{"err":"Name"}`, or `T`'s `v`, all three at the same JSON depth as a plain `?T`.

## Error unions

A Zig error (`error.Name`) is a return value, not a panic — a distinct type from `Zig.Error` above. `error.Name` becomes the string literal `"Name"`; an `E!T` constant becomes `.ok v` or `.error "Name"`.

`try v` (sugar for "return the error if `v` holds one, otherwise use its payload") becomes a `match` on `v`: the error arm runs the AIR `try`'s error body (itself ending in an exit, e.g. `ret`), and the ok arm binds the payload under a fresh name and continues with the rest of the instruction sequence:

```lean
match {v} with
| .error _ => (do ...)   -- the `try`'s error body; ends in an exit
| .ok v16 => (do ...)    -- the rest of the sequence, payload bound as `v16`
```

`catch` does not use `try`: it lowers to `is_err`/`is_non_err` plus a `cond_br`, so it becomes a plain `if`/`else` on `Zig.isNonErr`/`Zig.isErr`, unwrapping with `Zig.unwrapPayload`/`Zig.unwrapErr` (`ZigLean/Basic.lean`) in each arm.
