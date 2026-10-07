# Generated-program and parser fuzzing

Q01 has two seeded generators under `tests/roadmap/fuzz/`, each with a shrinker. A seed
fully determines its case for a given commit; failures reduce to a minimal reproducer.

## Malformed AIR JSON (`air_fuzz.py`)

`air_fuzz.py run BINARY --seeds N [--start S] [--save DIR]` mutates a corpus (three
in-file schema-11 seeds plus every committed `tests/golden/**/*.json` of at most 16 KiB,
sorted by path) and runs a previously built translator on each case, in emission mode and
with `--diagnostics-json`. Structural mutations delete keys or elements, swap in values of
the wrong type, perturb integers (instruction/type/global references), retag instructions
and type kinds, duplicate/swap/truncate lists, splice subtrees from other corpus files, add
keys, damage strings and nest deeply. Textual mutations truncate, cut, insert JSON
punctuation or invalid UTF-8, add a BOM, duplicate keys, inflate exponents and append
garbage. Some cases add a second corpus file.

Each case must end predictably:

| Mode | Accepted outcomes |
|---|---|
| emission | exit 0 with the `-- air2lean-profile:` header and no `panic! "air2lean: …"` emitter placeholder; or exit 1 with a non-empty diagnostic and the output path unchanged |
| `--diagnostics-json` | exit 0/1 with schema JSON whose `status` is `checked`/`rejected`, every `code` from the fixed vocabulary, and a rejection naming a non-skipped code |
| both | the same accept/reject decision |

Everything else is a failure: timeout (10 s), signal or other exit, a Lean `PANIC`
message, a placeholder, an untyped rejection, a partial output or mode disagreement.
A failure is shrunk with `shrink.py`: ddmin over the file list, then ddmin over JSON object
members and array elements plus node simplification/hoisting for parseable files, or
token- then byte-level ddmin for unparseable ones. Every accepted step must keep the same
failure kind and be strictly smaller, so the result is 1-minimal for these steps.
`--save DIR` writes each shrunk case as `seed-<N>/NN.json` plus `case.json`.

Committed reproducers live in `tests/roadmap/fuzz/regressions/`. Each `case.json` records
the seed, the original failure kind, the fix and `expected_exit` (written as null by `--save`; set it when committing the fix); `air_fuzz.py replay
BINARY` requires every case to pass the oracle with that exit status. Seeds 0–9999 found
three failure classes, each now rejected by the checker before emission:

| Shrunk reproducers | Original failure | Fix |
|---|---|---|
| `seed-582`, `seed-644`, `seed-8382` | emitter placeholder `unbound inst` | operands may not name a debug instruction (`dbg_stmt`, `dbg_var_*`, `dbg_arg_inline`, `dbg_empty_stmt`); it binds no value |
| `seed-6199`, `seed-8734` | `Option.get!` PANIC, exit 0 | `ptr_add`/`ptr_sub` with a non-pointer result type |
| `seed-6547` | placeholder `items of a pointer without a length` | `array_to_slice` of a pointer whose pointee is not an array or vector |

Emission and diagnostics may disagree only where diagnostics mode has its own documented
input limits (`INPUT_LIMIT`, such as 1024-character function names). Emission mode has
no such limits.

## Typed Zig programs (`zig_gen.py`)

`zig_gen.py` generates a JSON AST for a Zig program with up to two globals, up to two
helper functions (some returning `error{Fuzz}!u32`) and `work(p0: u32, p1: u32) u32`.
Statements cover locals of `u32`/`i32`/`u8`/`bool`, pointers to locals and globals,
stores through pointers, `bump`/`swap` helper calls (including `swap(&x, &x)` aliasing),
a `union(enum) { a: u32, b: i32 }` with re-tagging and capturing switches, `defer` and
`errdefer` blocks, `if`, bounded `while` loops with `break`, integer `switch` and early
`return`/`return error.Fuzz`. Expressions use wrapping arithmetic, bit operations, shifts,
modulo by constants, comparisons, short-circuit logic, `@bitCast`/`@truncate`/`@intCast`/
widening casts, calls and `catch`.

- `typecheck` states the generator's invariants: lexical scope, types, no shadowing,
  immutable parameters, Zig's unused-local, never-mutated and unreachable-code rules,
  bounded loops, `break` only in loops, no exits from `defer`, `errdefer`/errors only in
  error functions and calls only to earlier functions.
- `evaluate` is the reference semantics: wrapping integers, left-to-right operands,
  compound assignments that load their target first, LIFO `defer`, `errdefer` only on an
  error return and return values computed before defers run. `entry(a, b)` resets globals,
  calls `work` and XORs the final globals into the result, so cleanup effects are observed.
- The renderer chooses `var`/`const` and `_ = x;` from actual references, and emits a Zig
  `test` comparing `entry` with the reference results for four fixed inputs.
- `shrink` is a greedy fixpoint over AST reductions: drop functions/globals (with their
  calls or reads replaced by literals), delete statements, splice nested blocks
  into their parent, drop switch arms or `else` blocks, replace expressions with
  literals or subexpressions, and reduce loop bounds. Only well-typed, strictly smaller
  candidates that still fail are kept; the result is 1-minimal for these reductions.

## Running

```sh
tests/roadmap/fuzz/check.sh --light [SEEDS]          # unit tests + generator invariants; no tools
tests/roadmap/fuzz/check.sh --air .lake/build/bin/air2lean [SEEDS] [SAVE_DIR]
python3 scripts/build-guard.py --cwd "$PWD" --report /tmp/q01.json --log /tmp/q01.log \
  --timeout 3600 --rss-mib 12000 -- \
  env AIR2LEAN_ZIG_NATIVE=zig AIR2LEAN_ZIG_AIR=zig-air-0.16.0/bin/zig \
  tests/roadmap/fuzz/check.sh --heavy /tmp/q01-heavy 0 5
```

`--light` runs `test_fuzz.py`, which uses synthetic oracles to check generator
determinism, oracle classification, shrinker 1-minimality and the reference semantics, and
generates 300 typed programs. `--air` replays the committed regressions and then fuzzes the given
number of seeds (default 200). `--heavy` runs each seed in stages: native `zig test` of the
rendered program (Zig against the reference evaluator), `scripts/translate.sh` (AIR export,
translation and Lean elaboration), then `#guard` checks of the translated `entry` against
the same reference values (`zig_gen.py lean-checks`). The first failing stage is shrunk
over the AST with that stage as the oracle (`check.sh --reproduces`), and the minimal case
is written to `OUT_DIR/shrunk-<seed>/`. The heavy mode runs compilers and Lean sequentially; wrap it in one
build guard.

CI runs `--light` on every job and `--air` with 300 seeds against the built translator in
the full 0.16.0 job. The heavy differential is not in CI.

## Limits

The JSON oracle detects crashes, placeholders and inconsistent diagnostics. It does not
decide whether an accepted mutated input is semantically correct. The corpus is a
committed snapshot, so changing goldens changes what a seed generates. Reproduce a run with
the same commit. The Zig generator covers a
deliberately small, UB-free subset (no division by variables, no overflow traps, no
recursion, no slices, floats or threads); a native-test failure can be a generator or
evaluator bug rather than a translator bug.
