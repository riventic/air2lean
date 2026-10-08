# Separation proof tools

Import `ZigLean.Sep.Automation` for `sep_normalize` and `sep_frame`. Import
`ZigLean.Sep.Total` for total-correctness rules. These are optional modules;
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

The regression files in `tests/roadmap/proof-tools/` check AC normalization,
unit/duplicate handling, rejected framing, array mutation with inferred frames,
total bind, rejection of divergence/panics, and explicit conversion between
partial and total correctness. `Array.lean` checks prefix/element/suffix ownership,
endpoint and singleton boundaries, a store preserving neighboring elements and an
independent heap allocation, and rejection of out-of-bounds access, overlap,
dropped frames, and incorrect postconditions. Build the optional modules with
`lake build ZigLean.Sep.Automation ZigLean.Sep.Array ZigLean.Sep.Array.Reassemble
ZigLean.Sep.Total Proofs.Slices.Gen`, then run
each with `lake env lean tests/roadmap/proof-tools/<name>.lean` (`Normalize`,
`Clients`, `Array`, `Reassemble`, `ArrayClients`, and `Total`). Reassembly fixtures
include endpoint/singleton/empty boundaries, missing memory backing, inconsistent
metadata, duplicated ownership, lost frames, stale values, and changed neighbors.
CI retains the build and fixture logs.
The optional-module build and all six proof-tool fixtures have passed kernel
checking with the pinned Lean toolchain. These checks establish the stated model
contracts and rejected proof attempts; they add no native/export qualification.

## Loop templates and range conversions

Import `ZigLean.Sep.LoopTemplate` for the invariant/measure template,
`ZigLean.RecTemplate` for recursive functions and `ZigLean.Range` for arithmetic-range lemmas.
All three are optional modules.

`LoopTemplate body again inv post` has one field, `step`: for every state `s` and
measure `n`, one run of the body is a `TotalTriple` from `inv s n` to
`loopNext again inv post n` (repeat with `inv s' n'` for some `n' < n`, or exit with
`post e s'`). The measure is a ghost `Nat` carried by the invariant, so it can count
remaining list nodes or queue items. For a measure `μ` on the locals, use
`inv s n := ⌜n = μ s⌝ ∗ I s`. `LoopTemplate.total` proves the whole loop through
`TotalTriple.loop_ghost` (strong induction on the measure). `LoopTemplate.partial` projects the
`Triple`. `loopNext_repeat` and `loopNext_exit` prove the step's postcondition.

`loop_template inv post` applies to a `TotalTriple` or `Triple` goal on
`(Zig.loop body again).run s` and leaves the named goals `step`, `entry`
(`P h → ∃ n, inv s n h`), and `exit` (`post e s' h → Q (e, s') h`). `exit` is closed
automatically when `post` already is the goal's postcondition. `loop_template?` additionally
logs the remaining premises and their types. The partial form still requires a decreasing
measure. A loop whose termination depends on a non-`Nat` argument must first define
such a measure.

`zig_range` rewrites fixed-width arithmetic with conditional lemmas: `toNat_add_of_lt`,
`toNat_sub_of_le`, `toNat_mul_of_lt`, `toNat_setWidth_of_le`/`_of_lt`,
`toNat_ofNat_of_lt`, `toInt_of_lt`, `toNat_ofInt_natCast`, checked
`add`/`sub`/`mul` without overflow, and unsigned widening/narrowing `intCast`. Each range
premise must follow from context by `assumption` or `omega`. When a premise does not, the
term is left unchanged and the obligation remains visible. `sum_toNat_le` and
`sum_toNat_lt` bound sums of fixed-width values (`l.length ≤ 2 ^ k` items of width `w` fit
in `w + k` bits). These lemmas are ordinary theorems and use no `native_decide`.

`tests/roadmap/loop-tactics/Queue.lean` applies both tools to the generated `Lists.sum`
from `examples/lists/lists.zig`, a walk over a singly linked queue from its head. `sum_total`
is a `TotalTriple`: given the explicit capacity premise `xs.length ≤ 2 ^ 32`, `sum` returns
the exact sum of the items without an overflow panic and leaves the queue unchanged. The
proof uses a list-segment invariant, the node interface of `Proofs/Lists/Sep.lean`
(`node_val_run`, `node_next_run`, `focus_mid`), and `zig_range`. It does not unfold `Zig.load`,
byte encodings, blocks, or allocators. A `#guard_msgs` check fixes `loop_template?`'s report
on that loop: exactly `step` and `entry` remain. `Template.lean` checks the report including
`exit`, the partial form, rejection of non-loop goals, the necessity of a decreasing measure,
and the `zig_range` conversions, including an undischarged premise.
### Nested loops

The translator emits an inner loop as `Zig.loop inner again'` inside the outer loop's body
def, over the same locals. `LoopTemplate.run` turns the inner loop's template into its run
from any state satisfying its invariant: it returns, preserves the frame and establishes the
inner `post`. The outer `step` uses that run like any other step of its body, so the inner
iterations are proved once. `LoopTemplate.bind` is the same rule as a `TotalTriple` for
`(Zig.loop inner again' >>= k).run s`.

`tests/roadmap/loop-tactics/nested/Proof.lean` proves the translated `pairs` of
`tests/roadmap/loop-tactics/nested/nested.zig` (an inner `while (j < i)` inside an outer
`while (i < n)`) total: under the explicit premise that the result fits in `u64`, it returns
and adds `0 + 1 + … + (n - 1)` to `*acc`. The proof uses `pts_load_run`/`pts_store_run` and
`zig_range` lemmas and does not unfold `Zig.load`, `Zig.store`, encodings or blocks. The AIR
is retained with its provenance in `nested/`; `nested/check.sh` retranslates it, compares
the result with the committed `nested/Nested/Gen.lean` byte for byte, and checks the proof.

### Bounded invariant and measure inference

`loop_template?` without arguments, or `loop_template? _ post`, prints suggestions for the
goal's loop and leaves the goal unchanged; it proves nothing. It unfolds the loop body once
and follows only generated shapes: locals read by `(← get).f`, writes by
`modify (fun s => { s with … })`, checked `Zig.add`/`Zig.sub` of a local by a literal, and
`Zig.lt`/`le`/`gt`/`ge` guards. It reports the loop-carried locals (written by the body) and
the unchanged ones. For an unsigned guard whose counter steps towards a bound that the loop
does not change, it suggests the measure `bound - counter` (or `counter - bound`) and the
bound invariant. Given `post`, it also suggests `post` with a bound from outside the loop
replaced by the counter. It reports, and does not infer, measures for signed guards, counters
that step away from their bound or are also reset, bounds the loop changes, and loops without
a counter (such as list walks, which need a ghost measure). Nested loop bodies, calls and memory
are not followed, and side premises such as overflow bounds are never inferred. `Infer.lean`
and `nested/Proof.lean` fix these reports with `#guard_msgs`. The suggested measures and bounds for the two loops of
`pairs` are the ones its invariants use.

### Recursive functions

A recursive group becomes a `mutual` block of `partial_fixpoint` defs with unfold equations
`<fn>.eq_1` and no induction principle. Import `ZigLean.RecTemplate` (optional, Lean-only) for
`rec_template μ unfolding f, g`. It proves a goal `∀ x₁ … xₖ, B` by strong induction on the
`Nat` measure `μ` of its first `k` binders (the arity of `μ`). It leaves one goal, `step`,
with `x₁ … xₖ` introduced and
`ih : ∀ y₁ … yₖ, μ y₁ … yₖ < μ x₁ … xₖ → B[y/x]`, and it rewrites each listed function's
`eq_1` once in the goal. Premises and ghost values after the first `k` binders stay in `B`
and are quantified in `ih`. A mutually recursive group is specified as one conjunction (or
over an index type such as `Sum`) with one measure, unfolding every member.
`rec_template? …` also reports the remaining premise. The scaffold does not infer the
measure. Each recursive call site discharges the decrease when it applies `ih`.

`tests/roadmap/loop-tactics/Recursion.lean` uses it on committed translations: `gcd`
(self-recursive, the second argument decreases by `a % b < b`), the mutual `isEven`/`isOdd`
group, `fact` (a range premise carried through `ih`), and the memory-backed `Pointers.addDown`
(`Zig.callM`). `addDown_total` is a `TotalTriple` proved through `pts_load_run`/`pts_store_run`
without unfolding memory internals.

Build with `lake build ZigLean.Sep.LoopTemplate ZigLean.RecTemplate ZigLean.Range
Proofs.Lists.Sep Proofs.Recursion.Gen Proofs.Pointers.Gen air2lean`, then run
`lake env lean tests/roadmap/loop-tactics/<name>.lean` for `Template`, `Queue`, `Infer` and
`Recursion`, and `tests/roadmap/loop-tactics/nested/check.sh`.

This is a bounded P03 contribution. Templates are sequential: concurrent loops (and
termination under a scheduler) are out of scope. Invariant inference is the syntactic
suggestion pass above and is never trusted. The recursion scaffold needs a user-given `Nat`
measure and specification. `zig_range` performs only conditional rewriting and is not a
general BitVec decision procedure. No ring-buffer example exists in `examples/`, and the
modules add no exporter or native qualification.

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
