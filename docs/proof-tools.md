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

Import `ZigLean.Sep.LoopTemplate` for the invariant/measure template and
`ZigLean.Range` for arithmetic-range lemmas. Both are optional modules.

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
Build with `lake build ZigLean.Sep.LoopTemplate ZigLean.Range Proofs.Lists.Sep`, then run
`lake env lean tests/roadmap/loop-tactics/<name>.lean` for `Template` and `Queue`.

This is a bounded P03 contribution. The template is single-loop and sequential. It does not
infer invariants or measures, provide a recursive-call (non-loop) induction rule, or handle
nested-loop or concurrent termination. `zig_range` performs only conditional rewriting and
is not a general BitVec decision procedure. The client is a linked-list queue traversal.
No ring-buffer example exists in `examples/`, and the module adds no exporter or native
qualification.
