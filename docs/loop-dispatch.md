# Loop-switch dispatch

`loop_switch_br` selects a case using an initial value. `switch_dispatch` jumps back to an
**enclosing loop-switch** using a replacement selector. It may target an outer loop-switch
through nested dispatch loops, ordinary loops, conditionals, or blocks. It does not leave
an ordinary block with a value. These contracts are the same in the pinned Zig 0.14.1,
0.15.2, and 0.16.0 `src/Air.zig` definitions. The existing exporter decodes both tags.

The normalizer retains distinct `Op.loopSwitchBr` and `Op.switchDispatch` forms. Before
renumbering, raw validation checks lexical target scope and SSA operand availability.
The subset checker also validates direct Core callers: selector/replacement types must
agree, loop-switch and dispatch instructions must be `noreturn`, and dispatch targets
must be enclosing loop-switches. Extra or missing operands fail explicitly. These checks do not constitute
a full AIR schema or terminal-flow audit. The block-emission rule relies on AIR's declared
`noreturn` contract; rejecting arbitrary malformed block fallthrough belongs to the separate
input-validation work.

Supported selectors are scalar integers, booleans, enums, and error names. Range cases
require an integer selector. Pointer or aggregate selectors remain explicit errors;
Zig tagged-union switches lower to a scalar tag selector plus ordinary capture stores and
loads, which the existing model retains. Both dispatch instructions are handled by exact tag matches.

Each generated `Locals` structure has one typed `dispatchValue<id>` field per loop-switch.
Entry initializes only that field. Its named `loop<id>` body selects on the field, captures
external SSA values using the existing loop capture analysis, and returns typed exits.
A `.dispatch<id> value` exit updates that loop's selector and repeats it using `Zig.loop`.
A noreturn block without an own-target branch propagates its body exit directly, following
the AIR block contract; it generates no nonexistent branch constructor. Other dispatches,
block exits, ordinary repeats, and returns propagate without changing
that selector. An inner loop therefore cannot consume an outer dispatch accidentally.

The original pre-loop SSA operand remains fixed when a dispatch replaces the selector.
Zig Sema emits any mutable switch capture as explicit stores/loads (`zirSwitchContinue`
and switch lowering in `src/Sema.zig`); those effects remain in the translated bodies.
The C backend uses the same separate selector-local interpretation in `airSwitchBr` and
`airSwitchDispatch` (`src/codegen/c.zig`). Selector fields and generated binders are reserved
before allocating source local/type names.

Generated loop bodies and `again<id>` predicates are named so proofs can refer to them.
`Zig.loop_spec` applies directly: its invariant and natural-number termination measure
range over all locals, including the selector. `Zig.loop_dispatch_spec` provides the same
rule when a target-specific `Exit → Option Selector` function recognizes repeating exits.
It is derived from `loop_spec`; it adds no runtime primitive or logical assumption. The
kernel proof fixture maintains a fixed capture and decreases the selector on each own-target
dispatch. `tests/roadmap/dispatch/CountdownProof.lean` applies `Zig.loop_spec` twice to the
*generated* nested `countdown` machine: the inner loop's measure is its selector, with
`acc + 2 * remaining` invariant; the outer loop's measure is its remaining state transitions.
`countdown_spec` proves that every input terminates with `2 * n`. Memory and concurrency
translations reuse the existing generic loop semantics;
the existing memory/concurrency loop proof rules remain applicable.

Run the serial gate under the project's compiler resource guard:

```sh
LEAN_NUM_THREADS=1 \
AIR2LEAN_DISPATCH_ZIG_VERSION=0.16.0 \
AIR2LEAN_DISPATCH_ZIG_AIR=/absolute/path/to/locked-zig \
AIR2LEAN_DISPATCH_ZIG_STOCK=/absolute/path/to/stock-zig \
tests/roadmap/dispatch/check.sh
```

Use `--synthetic-only` for an isolated parser/emitter/kernel-proof check and `--native-only`
for one version's stock execution, fresh AIR, translation, and generated semantic checks.
Every mode builds the common runtime and translator and runs the cheap offline harness.
The default runs both groups. The complete gate
requires both stock native execution and a fresh locked exporter dump. It verifies that
the source actually produces both AIR tags and distinct nested dispatch targets, translates
that dump, and elaborates checks against the source's expected results. The synthetic cases
cover inner/outer jumps, an ordinary-loop/block exit, fixed SSA and block-result captures,
ranges/else, booleans, and selector-field name collisions. Nested legal exits cover an inner
`cond_br` in a noreturn block that breaks out of both loop-switches or continues the outer
one, a return from inside the inner loop, an inner loop result consumed as the outer
replacement selector, and a two-level state machine with Sema-style memory captures.
Malformed scopes, operand types, arity, and sibling-case SSA values are rejected. In a nested
position, a dispatch to an enclosing ordinary loop, a sibling-case loop-switch, itself, a
non-control instruction, or an absent ID is rejected, and so are a `br` to a loop-switch or
sibling, a `repeat` to a loop-switch, and a missing target. Five generated-code semantic mutants must
fail only with located Lean `native_decide` false-assertion diagnostics and exit status 1:
a lost replacement selector, wrong initial selector, wrong
nested target, a two-level break redirected to the outer continue, and a dropped captured value. They run serially with bounded per-mutant timeouts.
The native source adds enum selection and mutable tagged-union capture coverage. Its real
AIR also exercises noreturn blocks that dispatch outward without an own-target branch.
Set `AIR2LEAN_DISPATCH_KEEP_WORK=1` to retain the fresh temporary AIR and generated sources
locally for inspection; the gate prints their directory. The default removes them on exit.

CI runs the default gate on the primary Zig 0.16.0 profile and `--native-only` on Zig
0.15.2/0.14.1 after building proofs, for non-mutation jobs. The fixed synthetic/proof/mutation
checks run once; fresh exporter/translation/native semantics remain required for each
version. It executes checks and introduces no report upload step. Results qualify the pinned
compiler, release-safe source fixture, and modeled selectors above; they do not establish
termination for arbitrary dispatch loops or introduce support for unmodeled selector types.

The final guarded Zig 0.16.0 default gate passed after the type-table and diagnostic/mode
harness changes: kernel proof, ten generated synthetic programs, four semantic mutations,
stock source execution, fresh AIR translation, and generated native-result assertions.
That run took 8.3 seconds with 593.2 MiB peak memory. The separate Zig 0.15.2 `--native-only`
gate passed stock execution, fresh AIR translation, and generated native-result assertions
in 6.2 seconds with 365.9 MiB peak memory. Both runs also passed all twelve offline harness
tests. These measurements describe individual runs with existing build artifacts, not a
runtime or resource guarantee. Zig 0.14.1 is configured for the same native-only CI gate;
its actual gate remains pending. The results qualify the selected source fixtures and
modeled fragment, rather than all upstream AIR control flow.
