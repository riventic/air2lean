# Separation proof tools

For the full-state logic (`ZigLean/Sep/Full`), the general symbolic executor `fsym` walks
generated code from an invariant alone: [proof-automation.md](proof-automation.md).

Import `ZigLean.Sep.Automation` for `sep_normalize` and `sep_frame`. Import
`ZigLean.Sep.Total` for total-correctness rules and `ZigLean.Sep.Step` for the
symbolic-execution tactics ([below](#symbolic-execution-steps-p01)). These are optional modules;
existing generated-code imports and `Triple` keep their current meaning.

`sep_normalize` rewrites assertion expressions with associativity, commutativity,
and the `emp` unit. It also accepts ordinary Lean locations, for example
`sep_normalize at hp ⊢`. The resulting simp proofs use proved assertion equalities;
the tactic does not extend the trusted kernel or execute a decision procedure.

`sep_frame rule` closes a `Triple` goal by inferring the unused atoms in the
goal's precondition, applying `Triple.frame`, and checking both consequences by
normalization. With `open Zig Assn`, for example:

```lean
example (P Q R : Assn) (c : MemM Unit)
    (rule : Triple P c (fun _ => Q)) :
    Triple (R ∗ P) c (fun _ => Q ∗ R) := by
  sep_frame rule
```

Separating atoms are opaque; candidate matching uses definitional equality.
Repeated atoms are counted separately. A missing atom, a changed command, or an
incorrect postcondition causes failure. Final proof checking uses Lean's standard
simp ordering, which can fail to align definitionally equal wrapper atoms or
atoms differing only in implicit typeclass instances. In those cases, first
rewrite wrappers explicitly or apply the separation equalities directly. This
is AC/unit simplification and syntactic frame inference. It does not split byte
ranges or arrays, choose existential witnesses, discharge arithmetic, or synthesize
loop invariants. It is a bounded part of P01.

Import `ZigLean.Sep.Array` for explicit array ownership framing. `arr_split hp hk hs`
splits `arr p xs` into `arr p (xs.take k)` and
`arr (p.add (Enc.size T * k)) (xs.drop k)`. It requires `k ≤ xs.length` and
`Enc.align T ∣ Enc.size T`; both endpoints, including empty arrays, are supported.
`arr_focus hp hk ha hs` additionally requires `k < xs.length` and
`a ∣ Enc.align T` and exposes the element as `pts` between those two ranges.
The suffix begins at element `k + 1`. These lemmas split the existing byte ownership
using `bytesAt_split`; they do not allocate, copy bytes, or assume an encoding
round-trip law. Empty ranges remain `arr` assertions, with their pointer and alignment
requirements, rather than becoming `emp` automatically.

`Triple.arr_focus_frame hk ha hs rule` applies a supplied rule for the selected
`pts` assertion. Its precondition is `arr p xs ∗ R`; its postcondition preserves
the unchanged prefix, suffix, and independent frame `R` alongside the element
rule's result. `Triple.arr_store_focus hn ha hs hi w` specializes it to an actual
`store` at `p.elem (Enc.size T) i`, retaining both neighboring ranges and `R`.
It additionally requires lawful encoding and positive element size. For example:

```lean
import ZigLean.Sep.Array
open Zig Assn
example (p : Ptr) (x y z w : BitVec 32) (R : Assn) :
    Triple (arr p [x, y, z] ∗ R) (store 4 (p.elem 4 1) w)
      (fun _ => (pts (p.elem 4 1) 4 w ∗
        (arr p [x] ∗ arr (p.add 8) [z])) ∗ R) := by
  simpa [Enc.size, intSize, intAlign, alignUp] using Triple.arr_store_focus (p := p) (vs := [x, y, z]) (i := 1)
    (a := 4) (R := R) (by decide) (by decide) (by decide)
    (by simp only [List.length_cons, List.length_nil]; decide) w
```

Import `ZigLean.Sep.Array.Reassemble` to recover whole-array ownership explicitly.
`arr_append_of_heap hn hp hm` joins contiguous typed ranges; `arr_reassemble hn hk
hp hm` joins a prefix, an updated element at full ABI alignment, and the original
suffix into `arr p (xs.set k w)`. Both require positive element size and actual
memory backing (`m.heap = h ∪ hF`). That premise matters: disjoint assertions alone
can describe different addresses or block kinds for two ranges in the same block.
The join proof reads consistent metadata from the actual memory. Empty boundaries
and empty concatenations are supported; no byte copying or new allocation occurs.

`Triple.arr_update hn hk hs rule` obtains backing from the returned memory of a
supplied full-alignment element rule and reassembles the array while retaining
`R`. `Triple.arr_store_reassemble hn hs hi w` specializes this contract to a scalar
store, and `Triple.arr_read hn hs hi` returns a selected value with unchanged
array ownership. The interface supports a second update or read without exposing
byte-level representation in the client proof. `ArrayClients.lean` reuses it for
the existing generated `Slices.at` and `Slices.bumpAt` bodies from the public
slice example, then composes the clients on independent arrays. The update is
modulo 256 and the returned byte is the updated array's element 3; a capacity
of four and an in-bounds selected index remain explicit premises.

Array selection and arithmetic remain explicit. `sep_frame` continues treating
arrays as opaque atoms. General array/range search, inferred loop invariants,
zero-size element reassembly, and production container invariants remain outside
this bounded P01/P04 contribution. These are contracts about existing generated
model bodies; this slice adds no source/exporter qualification or general compiler
correspondence claim.

`Proofs/Lists/Container.lean` defines `Lists.SeqImpl`, a reusable sequence contract: a handle
type `H`, a representation predicate `Rep h xs`, and `add` with `add_spec` stating only that the
abstract sequence becomes `xs ++ [v]` or stays `xs` with `error.OutOfMemory`. Two generated
containers from `examples/lists/lists.zig` implement it. `linkedSeq` wraps `push` and stores
the sequence in reverse (`list hd xs.reverse`). `arraySeq` wraps
`std.ArrayListUnmanaged(u32).append`. Its representation `AList` requires a zero-capacity
items pointer without a block, so owned bytes discharge the `ptrOk` premise of `append_run`.
The `.empty` value, whose pointer names a constant global, is therefore outside `arraySeq`.
`tests/roadmap/container-contracts/Clients.lean` proves two clients once for every `I : SeqImpl`
from `I.add_spec` and the generic triple rules, without unfolding a representation. `addAll`
gives exactly `xs ++ vs`, or `xs` followed by a prefix of `vs` after `OutOfMemory`. Its total
property is a lemma about abstract lists. `addEvens`, a Lean client modelled on the `evens` loop
(not the generated `evens` body), always keeps `xs` as a prefix. The same client theorems are
instantiated unchanged to both containers. A rejected attempt shows that an `OutOfMemory` outcome cannot claim every item was added. Run the fixture
with `lake build Proofs.Lists.Container` and
`lake env lean tests/roadmap/container-contracts/Clients.lean`. Queues with removal, maps,
container deallocation through the interface, and a general ADT library remain outside this
bounded P04 contribution.

`TotalTriple P c Q` requires an explicit `c.run m = pure (v, m')` witness for
every admissible sequential input and disjoint frame, along with ownership of
`Q v` and preservation of the frame. Divergence and safety panics cannot satisfy
this equality. An unsatisfiable precondition remains vacuous, as with ordinary
Hoare logic. Zig error-union values such as `OutOfMemory` remain return values.

`TotalTriple.toPartial` projects ordinary partial correctness. Conversely,
`TotalTriple.of_partial` additionally requires `Returns P c`; partial correctness
alone never establishes termination. The API includes consequence, frame, return,
bind, existential/pure-precondition rules, load/store, array store, and
`TotalTriple.loop_ghost`. The loop rule requires a natural-number measure that
strictly decreases on each repeat, through the existing `loop_sep_ghost` theorem.
It does not provide concurrency termination or a general recursive-call rule.
This is an honest total/partial interface and a bounded contribution to P05.
Reports classify theorems over these interfaces by their kernel types, not by labels
(`docs/claim-strength.md`).

The scenarios of the retired `Normalize`, `Clients` and `Total` regressions (AC normalization,
unit/duplicate handling, rejected framing, total bind, rejection of divergence/panics, partial
and total correctness) are `fsym` regressions in the full-state logic:
`tests/roadmap/sep-auto/Frame.lean` and `tests/roadmap/sep-auto/Total.lean`
([proof-automation.md](proof-automation.md)). The array regressions stay in
`tests/roadmap/proof-tools/` until the full-state library has array rules (`Full/Arr`):
`Array.lean` checks prefix/element/suffix ownership,
endpoint and singleton boundaries, a store preserving neighboring elements and an
independent heap allocation, and rejection of out-of-bounds access, overlap,
dropped frames, and incorrect postconditions. Build the optional modules with
`lake build ZigLean.Sep.Automation ZigLean.Sep.Array ZigLean.Sep.Array.Reassemble
ZigLean.Sep.Total Proofs.Slices.Gen`, then run
each with `lake env lean tests/roadmap/proof-tools/<name>.lean` (`Array`, `Reassemble` and
`ArrayClients`). Reassembly fixtures
include endpoint/singleton/empty boundaries, missing memory backing, inconsistent
metadata, duplicated ownership, lost frames, stale values, and changed neighbors.
CI retains the build and fixture logs.
These checks establish the stated model
contracts and rejected proof attempts; they add no native/export qualification.

## Symbolic execution steps (P01)

Import `ZigLean.Sep.Step` (optional; not in the `ZigLean` umbrella) to execute generated
`MemM`/`MM` code step by step against a `Triple` or `TotalTriple` goal. Each tactic elaborates
to applications of ordinary lemmas in that module, built from `bind`, `frame`, `conseq`, `lift`,
`ex` and the existing load/store/array rules. The kernel checks every generated step; the
tactics add no axiom and run no decision procedure.

| Tactic | Effect |
|---|---|
| `sep_unfold [e, …]` | Unfolds the named definitions in the command only, pushes `StateT.run` through binds, `get`, `modify`, `callM` and `StateT.lift`, and flattens binds. It unfolds the comparison helpers (`Zig.lt`, …) and decides branches with the given facts, such as a bound or an overflow fact `Zig.add false x 1 = pure (x + 1)`. |
| `sep_step [e, …]` | Executes the first command of `c >>= f`, or a lone `c`. For `load`/`store` at `p`, it finds `pts p a ?v` in the precondition. If there is none and the address is `q.elem size i`, it finds `arr q ?xs` instead. It frames the remaining atoms, applies the load/store lemma and continues with `f v`, normalized by `sep_unfold [e, …]`. A store to an array gives `arr q (xs.set i w)`. The array bound `i.toNat < xs.length` is tried with `assumption`/`omega`. An unproved bound stays a goal. |
| `sep_step [e, …] using rule` | Applies a supplied contract for the command, such as a function triple or a representation lemma like `Lists.node_next_total`. Its precondition atoms are matched, and the rest is the frame. A postcondition `⌜r = v⌝ ∗ P` continues with `f v`. Otherwise the result is introduced, followed by its pure facts and witnesses. |
| `sep_steps [e, …] using r₁, …` | Repeats `sep_step` while a built-in rule or one of the `rᵢ` applies. |
| `sep_intro x h …` | Moves `⌜φ⌝` atoms and `Assn.ex` witnesses of the precondition into the context, using the given names in order. An unnamed equation with a local variable on one side is substituted. |
| `sep_ret w …` | On `pure v`, proves `∀ h, P h → Q v h`. It instantiates existentials of `Q` with the witnesses `w …` and turns pure atoms into goals, closing them by `rfl`/`assumption` when possible. The spatial rest must equal `P` up to AC and `emp`. Otherwise it leaves `∀ h, P h → Q v h`. |
| `sep_close hp w …` | The same entailment step on a goal `Q h` with `hp : P h`. |
| `sep_split p k` | Splits `arr p xs` in the precondition at element `k` (`arr_split`). The bound and ABI divisibility are side conditions. |

`TotalTriple.step_run` turns a total triple of one loop-body run into the run-level step
premise of `loop_sep_ghost`/`loop_sep_spec`. Existing step lemmas therefore keep their
statements and can be proved at the triple level.

Frame inference matches atoms by definitional equality. It is not a search through
`emp`-padded or rewritten forms; such atoms need an explicit rewrite such as
`Lists.list_cons_eq` first. The tactics do not synthesize loop invariants, measures, ranges
or existential witnesses, and they do not prove arithmetic beyond the `omega` attempt on bounds.
Range and loop-invariant synthesis remain outside P01.

The following proofs were re-proved with these tactics. Line counts are non-blank, non-comment
proof lines. Statements are unchanged.

| Proof | Before | After |
|---|---|---|
| `bump_spec` (`Proofs/Slices/Sep.lean`, pointer load/add/store/load) | 11 | 4 |
| `reverse_step` (`Proofs/Slices/Sep.lean`, two indexed loads and stores in a `u32` slice) | 64 | 52 |
| `Lists.reverse_step` (`Proofs/Lists/Sep.lean`, in-place list reversal step) | 28 | 19 |
| `Lists.freeAll_step` (`Proofs/Lists/Sep.lean`, read `next`, then free the node) | 19 | 16 |
| `generated_at_array` → `at_array_steps` (`StepClients.lean`) | 15 | 3 |
| `generated_bumpAt_array` → `bumpAt_array_steps` (`StepClients.lean`) | 51 | 3 |
| the composition of both clients (`StepClients.lean`) | 18 | 3 |
| node triples `node_next_total`, `node_set_next_total`, `node_free_total`, `list_cons_eq` (new, shared) | — | 10 |
| total | 206 | 110 |

The reduction is 47% overall. Separation bookkeeping (memory threading, disjointness, frame
heaps, run equations) disappears entirely. What remains in `reverse_step` is the list-index
arithmetic of the invariant. `ArrayClients.lean` keeps its manual proofs as evidence for the
reassembly interface; `StepClients.lean` proves the same statements with the tactics.

The scenarios of the retired `Steps.lean` regressions are `fsym` regressions in the
full-state logic, `tests/roadmap/sep-auto/Steps.lean`: framed `pts` steps in partial and total
form, an item store through `p.elem` with its neighbours framed, a side condition left visible
as a goal, caller rules with existential/pure postconditions, existentials and facts of the
precondition, and a generated-style `MM` body. It also rejects a missing points-to, a dropped
frame, a store claiming the old value, a wrong array neighbor, and a rule for a different
command. Steps on whole-array ownership `arr p xs` at a symbolic index wait for `Full/Arr`;
`StepClients.lean` keeps the legacy tactics' generated array clients until then.

## Loops, recursion and range conversions

Generated loops are proved in the full-state logic with the loop rules of
`ZigLean/Sep/Full/Loop.lean`; each body's step is a triple walked by `fsym`
([proof-automation.md](proof-automation.md)). There is no loop template and no loop tactic:

* `FTotalTriple.loop_measure I μ post step`: total correctness with a measure `μ` on the locals.
  `step` is one run of the body from `I s` that either repeats with `I s'` and `μ s' < μ s` or
  exits with `post`.
* `FTotalTriple.loop_ghost inv post step`: total correctness with a ghost measure `n` carried by
  the invariant `inv s n` (`floopNext`), for loops whose progress no local counts, such as the
  rest of a list.
* `FTriple.loop inv post step`: partial correctness from the invariant alone (fixpoint
  induction). `FTriple.admissible_fun` is the partial recursion rule for a `partial_fixpoint`
  group in `MemM`.

A proved loop is a rule like any other: stated over `(@Zig.loop (MM σ) _ _ mb _ body again).run s`
with the `MonoBind` proof `mb` as a parameter, `fsym [loop_rule]` uses it inside the enclosing
body. That is how a nested loop is proved once and used by the outer step.

Range conversions are `fsym`'s step rules for checked arithmetic and unsigned `@intCast`
(`add_step`, `sub_step`, `intCast_step`, …) and its arithmetic solver `fsym_arith`.
`ZigLean/Range.lean` keeps the conditional lemmas and the sum bounds `sum_toNat_le` and
`sum_toNat_lt` (`l.length ≤ 2 ^ k` items of width `w` fit in `w + k` bits) as ordinary
theorems.

`tests/roadmap/loop-tactics/Queue.lean` proves the generated `Lists.sum` from
`examples/lists/lists.zig`, a walk over a singly linked queue from its head. `sum_total` is an
`FTotalTriple`: given the explicit capacity premise `xs.length ≤ 2 ^ 32`, `sum` returns the
exact sum of the items without an overflow panic and leaves the queue unchanged. The invariant
is a list segment with the number of remaining nodes as the ghost measure (`loop_ghost`); the
body's steps are `fsym` walks over the nodes' fields. `sum_total_legacy` derives the legacy
total triple through `FTotalTriple.toTotal_on`.

`tests/roadmap/loop-tactics/nested/Proof.lean` proves the translated `pairs` of
`tests/roadmap/loop-tactics/nested/nested.zig` (an inner `while (j < i)` inside an outer
`while (i < n)`) total: under the explicit premise that the result fits in `u64`, it returns
and adds `0 + 1 + … + (n - 1)` to `*acc`. Both loops use `loop_measure`; the outer step's walk
uses the inner loop's triple as a rule. The AIR is retained with its provenance in `nested/`;
`nested/check.sh` retranslates it, compares the result with the committed
`nested/Nested/Gen.lean` byte for byte, and checks the proof, including its legacy form by
`toTotal_on`.

A recursive group becomes a `mutual` block of `partial_fixpoint` defs with unfold equations
`<fn>.eq_1` and no induction principle. `tests/roadmap/loop-tactics/Recursion.lean` proves the
pure `Zig.Result` functions of `examples/recursion/recursion.zig` by well-founded induction on a
`Nat` measure and the unfold equations: `gcd` (the second argument decreases by `a % b < b`),
the mutual `isEven`/`isOdd` group (one conjunction, one measure) and `fact` (a range premise
carried through the induction hypothesis).

The scenarios of the retired template checks are `fsym` regressions in
`tests/roadmap/sep-auto/`: `Total.lean` proves a countdown with `loop_measure`, rejects a step
whose measure does not decrease (a counter stepping away from its bound, a reset counter) and
shows that no measure makes the step of a body that always repeats (`spin_no_measure`);
`Arith.lean` checks the range conversions and that a sum or narrowing cast without a range
premise is not proved.

Build with `lake build ZigLean.Sep.Full.Loop ZigLean.Sep.Full.Auto ZigLean.Sep.Full.Strength
ZigLean.Simp Proofs.Lists.Gen Proofs.Recursion.Gen air2lean`, then run
`lake env lean tests/roadmap/loop-tactics/<name>.lean` for `Queue` and `Recursion`, and
`tests/roadmap/loop-tactics/nested/check.sh`.

This is a bounded P03 contribution. The loop rules are sequential: concurrent loops (and
termination under a scheduler) are out of scope. Invariants and measures are not inferred. The
memory-backed recursive `Pointers.addDown` is not covered, and no ring-buffer example exists in
`examples/`.

### Dispatch loops (L03)

The emitter turns a labelled-switch state machine (`continue :sw`) into
`Zig.loop (f.loopN ..) f.againN`, with the selector in the locals field `dispatchValueN`. One
rule of `ZigLean/Sep/Full/Loop.lean` proves every such loop, `FTotalTriple.loop_dispatch sel inv
data rank B post step`; a machine supplies:

* the invariant indexed by the selector's state, `inv k s` (one case per state);
* the consumed data `data s` and the state's rank `rank k`, with a bound `B` above every rank: the
  measure `B * data + rank` is the lexicographic order of (data, rank), so a transition that
  consumes nothing must lower the rank. Tag the ranks `attribute [local fsym_arith] rank` so that
  `fsym` reads their values;
* the step premise, by a case split on the selector (`cases`) followed by `fsym`, which walks each
  prong. An integer selector needs no split: `fsym` splits on the selector's tests and the
  invariant excludes the other values.

`tests/roadmap/dispatch-templates/TokenizerProof.lean` proves `countTokens` from
`source.zig`, a tokenizer state machine (`start`/`ident`/`number`/`done`). It uses the
translation of a fresh compiler export. `countTokens_total` shows that over a buffer
`up (arr p xs)`, the function returns the reference automaton's token count modulo `2 ^ 32` and
leaves the buffer unchanged; `countTokens_total_legacy` is the legacy total triple through
`FTotalTriple.toTotal_on`. The byte load is the library rule `FTotalTriple.arr_load`, the index
check `checkIndex_of`, and the generated classifiers are rules proved against `alpha`/`digit` on
all 256 bytes. `Template.lean` instantiates the rule for small machines with an enum and an
integer selector, and shows that a wrong invariant (at `count`) and a rank that does not order the
states (at `idle`) are not established by the walk, next to positive controls. `check.sh` also requires air2lean to reject
the real exported AIR when one `switch_dispatch` target is changed to a block, an absent ID, or
the dispatch itself.

Invariants and measures are written by hand. A labelled switch has only structured
`continue :sw` dispatch, so these proofs imply nothing about unrestricted control flow.
Zig 0.16.0's `translate-c` demotes a C function that uses `goto` to an `extern` declaration
("TODO goto"), so C goto state machines do not reach this form. The tokenizer proof names
the 0.16.0 translation's loop identifiers and is qualified only there.

## Model cost: allocation counts and counted loops (P06)

Import `ZigLean.Sep.Cost` for a qualified cost layer. It adds no field to `Mem` and
changes no generated code. Each count is read off a run that the existing semantics
already defines:

- Allocation requests: `Mem.allocs`, the allocator model's own count of `rawAlloc`
  calls. A failed request counts too.
- Retained allocations: `Mem.liveHeap`, the number of live `.heap` blocks.
  `Mem.SameAllocs m m'` says that both counts are unchanged.
- Loop steps: `LoopRuns body again s m k e s' m'`, a run of `loop body again` with
  exactly `k` body runs. That is every repeat plus the final exit test.
  `LoopRuns.run` gives the loop's ordinary run equation. `LoopRuns.unique` shows `k`
  depends only on the start, so a proved count is exact.

The instrumentation lemmas hold for every successful run of a primitive from any
memory. `store_cost` and `load_cost` give `SameAllocs`. `create_cost` gives one request,
plus one retained block on success and none on `OutOfMemory`. `destroy_cost` gives one
fewer retained block and no request. `loopRuns_exact` turns a ghost count that each
repeat lowers by exactly one into an exact count. `loopRuns_bound` turns
`loopMM_ghost`'s decreasing measure `n` into the bound `k ≤ n + 1`.

`Proofs/Lists/Cost.lean` applies the layer to the generated code of
`examples/lists/lists.zig`:

- `push_cost`: one allocation request, with one new retained block on success and
  none on `OutOfMemory`.
- `pushAll_cost`: a client of the generated `push`. After `n` successful pushes there
  are exactly `n` more requests and `n` more retained blocks.
- `freeAll_cost`: frees exactly `n` retained blocks in exactly `n + 1` body runs.
- `sum_cost` and `sum_count_unique`: `sum` over `n` items runs its loop body exactly
  `n + 1` times, allocates nothing, and returns the sum. The sum must fit in `u64`;
  otherwise the checked add panics.
- Capacity premises: `sum_count_capacity` (`n ≤ C` gives at most `C + 1` body runs) and
  `pushAll_capacity` (at most `C` items gives at most `C` requests and at most `C` new
  retained blocks).
- `append_capacity`: `ArrayListUnmanaged(u32).append` with spare capacity
  (`xs.length < cap`) makes no allocation request and retains no new block, for every
  allocator policy. `Proofs/Lists/Append.lean`'s `append_cost_run` carries this
  through the generated `ensureTotalCapacity` and `addOneAssumeCapacity`.

These counts are model counts, premise SEM-05 (`docs/premises.md`). A body run, a load
and an allocation request have no time or byte weight. Nothing here relates a count
to CPU time, cache behavior, instruction counts, or a native allocator's memory use.
Such a claim needs a separate calibration argument, which this layer does not
provide. The counts cover only successful runs: a panic or divergence has no
`LoopRuns` witness. Build with `lake build ZigLean.Sep.Cost Proofs.Lists.Cost`.

### Resource-bounded total triples (P05)

`ZigLean.Sep.Bounded` defines `TotalTripleWithin B P body again s Q`: from every framed
precondition, the loop `loop body again` exits with `Q` after at most `B` body runs (a
`LoopRuns` witness). `toTotal` gives the total triple; the bound is extra information.
`count_le` applies the bound to the loop's single run, because the body is deterministic.
The rules are `mono` (a larger bound is weaker), `conseq` and `frame`. `step` composes one
body run (a `TotalTriple` of the body) with a bounded rest and adds one to the bound. `exit`
is the one-run case. `then_total` composes a bounded loop with a total continuation.
`of_ghost` is `TotalTriple.loop_ghost` with the bound `n + 1`. `not_within_of_count` and
`not_within_of_stuck` refute a bound from an admissible input. A run with more body runs
refutes it, and so does a loop with no counted run. So divergence cannot satisfy it
vacuously.

`Proofs/Lists/Bounded.lean` proves `sum_loop_within`: the generated `sum` loop over
`xs.length` items exits within `xs.length + 1` body runs with the sum. `sum_loop_total` is
the total triple it implies; the function-level total triple for `sum` is
`Lists.Linked.sum_total` (`Proofs/Lists/Linked.lean`, full-state logic).
`sum_loop_not_within` shows that the bound is tight. Only body runs of the counted loop
count, and straight-line code outside it does not. Build with `lake build ZigLean.Sep.Bounded
Proofs.Lists.Bounded`.

## Concrete runs of programs with loops (`unroll_sched`)

`Zig.loop` is a `partial_fixpoint`: the least fixpoint of its unfolding, which the kernel does
not compute, so `decide +kernel` cannot evaluate a run that reaches a loop. Import
`ZigLean.Conc.Unroll` (an optional module) for a kernel-checked run of a concurrent program
with loops under one schedule:

```lean
theorem parallelCounter_completes :
    Witness.okVal (Sched.run ⟨.any, .available⟩ dispatch 1000 (fun _ => 0) (parallelCounter 1)
      (mem0 .fresh)) = some 4 := by
  unroll_sched 10
```

`unroll_sched k` accepts a goal `g (Sched.run env dispatch fuel o main m₀) = v` with concrete
arguments (the environment `env` included), for an observation `g` of the run that tells a run
without a result from `v` (`Witness.okVal r = some n`, `Witness.errOf r = some e`; the kernel
checks `g Sched.noResult ≠ v`). It:

1. unfolds every definition reachable from `dispatch` and `main` that runs a `Zig.loop`
   (`Unroll.expand`), and replaces each `Zig.loop body again` by
   `Unroll.loopSel k s body again`. At `s = exact` this is the loop; at `s = approx` it is
   `loopN body again k`, the loop cut after `k` runs of its body, which is `⊥` (no result)
   where the loop would go on;
2. proves the expanded program monotone in `s` with core's `monotonicity` machinery
   (`monotone_loopSel` and the `partial_fixpoint_monotone` lemmas of the generated code),
   using `loopN_le_loop : loopN body again k ⊑ loop body again`;
3. applies `Sched.apply_le` (from `Sched.run_le`): if every thread of one program is below the
   corresponding thread of another, a run of the first with a result is a run of the second
   with the same result (a simulation of `Sched.go` that keeps the memory, the oracle step and
   each thread's op);
4. closes the goal about the cut program with `decide +kernel`.

The proof uses only the standard axioms; nothing is evaluated outside the kernel. A wrong
value, a run out of fuel, an error, or a loop that needs more than `k` runs of its body leaves
the goal unproved, with the message `unroll_sched: the kernel does not compute the run …`.
`k` bounds each loop's body runs per entry, so a loop entered again gets `k` more.

`unroll_solo k` (module `ZigLean.Sep.Full.Unroll`) does the same for the in-thread reading of a
concurrent function that `CTriple` speaks about: a goal `g ((Sched.soloRun fuel x).run m) = v`
(`Sched.soloRun_apply_le`, from `soloTree_le`: a reading with a result is the reading of every
tree above). `AllocArena.ArenaObstruction.client_illegal` runs the stock `ArenaAllocator`'s
`alloc`, `alloc`, `free` this way from a memory that `Mem.FSeq` holds in (`Mem.FSeq` of a concrete
memory is decidable).

A `partial_fixpoint` definition or mutual group (a recursive call group of generated code,
`Lean.Order.fix F h`) is cut the same way: it becomes `Unroll.fixSel k s (fun s => F) h`, which
is `fixN F k` (`F` applied `k` times to `⊥`) at `approx` and the fixpoint at `exact`
(`fixN_le_fix`, `monotone_fixSel`); `k` bounds the nested unfoldings of the group. A definition
met again inside its own expansion (a recursion through a dispatch table) stays uncut there.

The `completes` companions of the concurrent all-schedules theorems
([theorem-inventory.md](theorem-inventory.md)) use it: one concrete schedule (the oracle that
always picks option 0), fuel 1000, `mem0`. `tests/roadmap/proof-tools/Unroll.lean` checks a
run, its axioms, and the rejection of a wrong value, too few iterations, too little fuel and a
goal without a run, and a mutual `partial_fixpoint` group (`even_six`, rejected when cut too
early). Build with `lake build ZigLean.Conc.Unroll Proofs.Threads.Gen`, then run
`lake env lean tests/roadmap/proof-tools/Unroll.lean`.
