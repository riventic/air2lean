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

`--zig-version V` selects one version's seed set instead of the mixed corpus: the three in-file
seeds as V's schema-12 export (with the profile of one of V's committed exports, `module`
fields, a typed callee and the full pointer type), plus V's committed compiler AIR only: the
goldens and the outputs of every fixture export manifest (`tests/roadmap/*/exports.json`,
`scripts/fixture-exports.py`) of version V. For 0.17.1 that adds the fixture exports of the
0.17 tags the goldens lack (`div_ceil`, `error_from_int`, `int_from_error`, `union_from_enum`,
`array_to_vector`). Retagging then draws from V's tags, and also from the tags that only the other
supported versions' committed AIR uses (for 0.17.1: 0.16's `bitcast`, `intcast`,
`struct_field_val`, `bool_and` and others, which a 0.17 file must not contain), and one more
mutation relabels a `zig_version` (top-level or the profile's) as another supported version.
Without the flag the corpus is the mixed one as before, except that the in-file seeds' `arg`
instructions no longer carry an `args` key, which no export writes and schema 12 rejects.

Each case must end predictably:

| Mode | Accepted outcomes |
|---|---|
| emission | exit 0 with the `-- air2lean-profile:` header and no emitter placeholder (`air2lean_emitter_placeholder "…"`, formerly `panic! "air2lean: …"`); or exit 1 with a non-empty diagnostic and the output path unchanged |
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
the seed, the original failure kind, the fix and `expected_exit` (written as null by `--save`; set it when committing the fix),
and the seed set's `zig_version` when it has one (the directory is then `seed-<version>-<N>`); `air_fuzz.py replay
BINARY` requires every case to pass the oracle with that exit status, and every in-file seed
(legacy and each supported version's) to be accepted, so that mutations start from accepted
input. A case whose files are all legacy schema-11 documents without a target profile runs with
the explicit `--profile legacy-abi64-le` admission (docs/profiles.md), as a user would translate
it, so that it reaches the checker instead of ending at the profile check. Seeds 0–9999 found
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
Two profiles share one generator, typechecker, reference evaluator, renderer and shrinker.
`--profile core` (the default) is the original subset: statements cover locals of
`u32`/`i32`/`u8`/`bool`, pointers to locals and globals,
stores through pointers, `bump`/`swap` helper calls (including `swap(&x, &x)` aliasing),
a `union(enum) { a: u32, b: i32 }` with re-tagging and capturing switches, `defer` and
`errdefer` blocks, `if`, bounded `while` loops with `break`, integer `switch` and early
`return`/`return error.Fuzz`. Expressions use wrapping arithmetic, bit operations, shifts,
modulo by constants, comparisons, short-circuit logic, `@bitCast`/`@truncate`/`@intCast`/
widening casts, calls and `catch`. A test pins the core renderings of seeds 0-39 by hash,
so the seeds checked by the heavy runs keep their meaning.

`--profile wide` adds, with their own seed space:

| Feature | Constructs |
|---|---|
| `wide_int` | `u16`/`u64`/`i64` locals, arithmetic and comparisons at their own width, and a cast table (`widen`/`truncate`/`bitCast`/`intCast` between `u8`, `u16`, `u32`, `u64`, `i32`, `i64`) |
| `array` | `[4]u32` locals, indexed reads and writes (`a[(i % 4)]`), compound assignment, pointers to elements (`&a[k]`) that alias the array through `swap`/`bump`/stores |
| `slice` | `[]u32` views `a[lo..hi]` (possibly empty) that write through to the array, indexed reads and writes, `for (s) \|e\|` loops with `break`/`return` |
| `optional` | `?u32` locals from `if (c) e else null`, `orelse`, capturing `if (o) \|v\|`, reassignment |
| `struct` | `struct { x: u32, y: i32 }` locals, field reads/writes, by-value copies, pointers to fields and the pointer-taking helper `bumpP(*P, u32)` |

Indexes are side-effect free (literals and locals, never globals or calls), so Zig's unspecified
operand order between an lvalue and its right-hand side cannot affect the reference result;
every index is reduced modulo the static length, so no bounds trap is reachable.

`--profile ext` adds, with its own seed space, the constructs whose outcome may be illegal
behaviour. Each program draws its own types (`types` in the AST): three integer types of any width
from 1 to 128 bits and either signedness (half the draws at a byte, word or power-of-two edge),
one or two of `f16`/`f32`/`f64`, and the element, field and payload types of its array, struct and
optional. Every construct below is generated at every type of the program.

| Feature | Constructs |
|---|---|
| `int_width` | locals, wrapping arithmetic, comparisons and casts (`widen`, `@truncate`, `@bitCast`, `@intCast`) at `u1`..`i128` |
| `divmod` | `/` (unsigned), `@divTrunc`, `@divFloor`, `@divExact`, `@rem`, `@mod` by a run-time divisor |
| `shift` | `<<`, `>>`, `@shlExact`, `@shrExact` by a run-time count (`@intCast` of a `u32` to the `Log2Int` type) |
| `checked` | `+`, `-`, `*` and negation with their overflow checks |
| `conv` | `@intCast` to a type that may not hold the value |
| `bounds` | unreduced array and slice indexes |
| `unwrap` | `o.?` and `f() catch unreachable`; `unreachable` under a run-time condition |
| `try` | `try f()` in an error function (its `errdefer` runs, its caller catches) |
| `float` | `+ - * /`, negation, `@sqrt`, `@floor`, `@ceil`, `@trunc`, `@round`, `@abs`, comparisons, `@floatCast`, `@floatFromInt`, `@intFromFloat`, `@bitCast` to the bits |
| `alloc` | `alloc`/`free` of a slice and `create`/`destroy` of one value through `std.heap.FixedBufferAllocator` over a 64-byte buffer, freed by `defer`, at the end of the block or never, so that out-of-memory and reuse of the last allocation are reached |
| `generic` | `fn (comptime T: type, …)`, `anytype`, a `comptime` count unrolled by `inline for`, a `comptime_int` parameter and a generic struct `GPair(T)` with methods, each instantiated at the program's types |

An operation with a safety check comes guarded or unguarded. A guarded one tests its operands
first and never traps; an unguarded one traps for some operands, and then the program's outcome
for that input is the panic. The reference evaluator names the check (`std.builtin.panic`'s
member), the native harness (`driver.zig`, written beside the program) installs a panic namespace
that prints the member and goes on with the next input, and the translated `entry` must return the
`Zig.Error` that `scripts/panic-policy.tsv` assigns to that member. So an input agrees when all
three give the same value or the same check: the model is illegal exactly when the native program
panics, and for the same reason. Operands of these operations are bound to run-time locals
(`var t: T = e; _ = &t;`), because Sema rejects a comptime-known illegal operation and folds a
comptime-known legal one.

What `ext` leaves out, and why:

- Illegal behaviour without a native safety check has no native outcome to compare:
  `@rem`/`@mod` of the least value by -1 (rendered with the divisor tested, result 0), an inexact
  `@shrExact` (always guarded), `@intFromFloat` of a NaN (always guarded), reads of freed or
  uninitialized memory (a freed slice is out of scope, an allocation is initialized).
- Floats stay inside the model's exact subset (docs/floats.md, `assurance/float-semantics.json`):
  no `f80`/`f128`, `@mulAdd`, `@min`/`@max`, float `@rem`/`@mod`/`@divExact` or libm functions. A NaN's
  payload and sign are not observed: `@bitCast` of a float to its bits is rendered with a NaN
  replaced by the canonical quiet NaN, and a NaN stored to memory reads back as
  `Zig.Error.unspecified` in the model (docs/floats.md, "NaN in memory"), so for an input on which
  the evaluator produced a NaN the Lean stage accepts `.unspecified` in place of the value. The
  reference arithmetic is `softfloat.py`, exact rational arithmetic with one rounding per operation.
- Allocation goes through the translated allocator (`--allocator-model translated`,
  docs/allocator-model.md), never a hand-written model: the case's `expected.json` carries the
  `scripts/translate.sh` arguments (`--filter` with the allocator's code, `--closure` of the
  module's functions). The buffer is a `[4]u128`, whose type gives it alignment 16, and `entry`
  casts its address at run time: the AIR export does not record a declared `align(N)` of a global,
  so the model places a `[64]u8 align(16)` at any address (`collectGlobals` in
  `Air2Lean/Emit.lean`), and allocation offsets would then depend on the placement.
- Threads are not generated. The harness compares one value per input, and a concurrent function
  has none: it is a `Zig.ConcM` whose result depends on the schedule oracle, natively one run
  shows one schedule, and agreement is a search over schedules with caps (`scripts/diff.sh`,
  `tests/diff/ScheduleSearch.lean`), which a capped search excludes rather than decides. The
  `std.Thread` rows are also qualified for Zig 0.14.1-0.16.0 only, so a 0.17 program is rejected.
  Generated concurrent programs belong to that harness, not to this one.

The profiles share these parts:

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
tests/roadmap/fuzz/check.sh --air .lake/build/bin/air2lean [SEEDS] [SAVE_DIR] [ZIG_VERSION]
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

CI runs `--light` (both profiles) on every job, `--air` with 1000 seeds of the mixed corpus and 1000 of
the default version's seed set (`scripts/compat.py default`) against the built translator, and `--heavy`
over seeds 0-2 of each profile in the full 0.16.0 job. Larger ranges are a manual job (the same command with the
patched and stock 0.16.0 compilers). Caps: `--heavy` refuses `COUNT` above
`AIR2LEAN_FUZZ_HEAVY_MAX` (default 50); shrinking spends at most `AIR2LEAN_FUZZ_SHRINK_BUDGET`
pipeline probes (default 150). A shrink step only counts if the failure keeps the same normalized
first error (`check.sh --reproduces CASE STAGE SIG`), so shrinking cannot drift to another bug.

## Heavy differential run (seeds 0-39)

Commit 9f39e808 plus this change; macOS aarch64; stock Zig 0.16.0 for native tests, patched
`zig-air-0.16.0-v1` exporter (zig-unlocked sha256 8b4be884bf62095a...), Lean v4.34.0;
`check.sh --heavy OUT 0 40` under `build-guard.py` lane C. 40 seeds: 37 pass all three stages
(native test, translation, and `#guard` of `entry` on four inputs equal to native results).
A negative control (corrupted expected value) is rejected by Lean. 3 seeds failed at translation
(Lean did not elaborate Gen.lean); all were one translator bug, since fixed:

| Seeds | Stage | Triage |
|---|---|---|
| 18, 19, 39 | translate (Gen.lean elaboration) | FIXED: a comptime-known tagged-union local whose address is taken becomes a constant global. Sema points its live uses at the global and leaves its dead `alloc` and stores as `bitcast`s of address 0; the translator emitted those placeholders as `Zig.ptrFromAddr 0`, an integer-to-pointer `bitcast` did not mark the function as using memory, and the global's type had no `Zig.Enc` instance. It was not a wrong pointer. Canon now drops the dead placeholders (a placeholder that is still read is rejected), `@ptrFromInt` counts as memory use and every function's global types get `Zig.Enc` when `mem0` exists. Regression: `tests/roadmap/const-locals/` (`fuzz_s19.zig`). Seeds 18, 19 and 39 pass `check.sh --heavy` after the fix. |

Harness bugs found and fixed by the run: generated names `u<N>`/`i<N>` shadow Zig primitive
types (renamed `un<N>`/`lp<N>`); the old `zig-air-0.16.0` exporter predates pointer constants
(stale tool, not a harness bug: use a current patched build); shrinking accepted any failure at
the same stage (now matched on the normalized error) and had no cap.

## Heavy differential run, larger ranges (batch A)

Commit of this change on macOS aarch64; stock Zig 0.16.0 native tests, a freshly built patched
0.16.0 exporter (zig-patch of that commit), Lean v4.34.0; `check.sh --heavy` under `build-guard.py`.

| Profile | Seeds | Result |
|---|---|---|
| core | 40-139 (100) | all pass native test, translation and the `#guard` values |
| wide | 0-99 (100) | all pass the same three stages |

A corrupted-expectation control on a wide seed is rejected by Lean. The malformed-AIR fuzzer ran
20000 further seeds (10000-29999) against the built translator: 0 failures (CI runs seeds 0-999).
The wide profile found no new translator bug in this range; its value is regression coverage of
wide integers, array/slice/optional/struct lowering and element/field pointer aliasing. Larger ranges
remain a manual command (`AIR2LEAN_FUZZ_HEAVY_MAX` caps one invocation at 50 by default).

## Limits

The JSON oracle detects crashes, placeholders and inconsistent diagnostics. It does not
decide whether an accepted mutated input is semantically correct. The corpus is a
committed snapshot, so changing goldens changes what a seed generates. Reproduce a run with
the same commit. The Zig generator covers a
deliberately small subset: the `core` and `wide` profiles are free of illegal behaviour, and `ext`
generates only illegal behaviour that a native safety check reports (see its exclusions above). No
profile has recursion, threads, multi-dimensional types, allocators other than the fixed-buffer one,
or IO. A native-stage failure can be a generator or evaluator bug rather than a translator bug.
