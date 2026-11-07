import Proofs.Lists.OpenInv
import ZigLean.Sep.Full.Loop
import ZigLean.Sep.Full.ThreadLoop
import ZigLean.Sep.Full.AutoThread
import ZigLean.Sep.Full.Auto
import ZigLean.Sep.Full.Cost

/-!
# The linked list of `examples/lists/lists.zig` in the full-state logic

A node (`node X p v q`) owns its two fields, `next` at offset 0 and `val` at offset 8 (`pts`), and
`X p`: whatever else its owner keeps with it. The functions here never touch the rest of a node's
allocation, so they are proved for every `X`. A list that an allocator built carries the rest of
each node's grant in `X` (its padding bytes and the allocator's token), and `X := fun _ => emp` is
a list of bare fields. `lseg X hd tl ys` is the segment from `hd` to `tl` holding `ys`, and
`list X hd xs` the whole list (the segment that ends at `null`): the library list family
`listSeg` (`ZigLean/Sep/Full/ListSeg.lean`) at this node layout.

* `reverse_thread`: `reverse` turns the list into the list of the items in the other order, and
  returns, as a step of the thread that owns the list (`FTTotalTriple`, the loop by
  `FTTotalTriple.loop_ghost_ex`), so a concurrent client lifts it into its thread
  (`CTriple.liftMem`). `reverse_total` is its reading in one thread, `reverse_spec` the partial
  form.
* `sum_total`: if the sum of the items fits in a `u64`, `sum` returns it (no overflow panic) and
  leaves the list unchanged.

The loops are walked by `fsym` from their generated invariants (`Proofs/Lists/OpenInv.lean`,
`air2lean-invgen`'s list-walk family, `@[fsym_inv]`, with the number of nodes left as a ghost
measure: `loop_ghost_ex`): the cursor's test splits the ghost list of the nodes left, and a
repetition folds the node it passed back into the invariant's lists. Each generated invariant is
stated over its own node layout (`reverse.loop6.node`: `next` and an abstract rest, so `reverse`
holds for every node with a `next` field; `sum.loop6.node`: `next`, the item and `X`), which `node`
instantiates.
`sum_exact` counts the steps by `FTotalTriple.loop_exact` over `sumInv`, whose step `fsym`
walks. The program is `Proofs/Lists/Open.lean`, the translation in which the `Allocator`
parameter is an open interface; `push` and `freeAll`, which allocate and free nodes through it,
are proved for every allocator in `Proofs/Lists/Alloc.lean`, with `X` the rest of each node's
grant.
-/

namespace Lists.Linked
open Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto Lists.Open

variable (X : Ptr → FAssn)

/-- A node at `p` with the item `v` and the next pointer `q`, and `X p`: the library's node
layout (`ZigLean/Sep/Full/ListSeg.lean`: `next`, the item, the rest), reducible, so that its
lists are those of the generated invariants (`Proofs/Lists/OpenInv.lean`). -/
abbrev node (p : Ptr) (v : BitVec 32) (q : Option Ptr) : FAssn :=
  up (pts p 8 q) ⋆ (up (pts (p.add 8) 4 v) ⋆ X p)

/-- The segment from `hd` to `tl` holds `ys`; its last node points to `tl` (the library's list
family, `listSeg`). -/
abbrev lseg (hd tl : Option Ptr) (ys : List (BitVec 32)) : FAssn := listSeg (node X) hd tl ys

/-- The list from `hd` holds `xs`: the segment that ends at `null`. -/
abbrev list (hd : Option Ptr) (xs : List (BitVec 32)) : FAssn := lseg X hd none xs

variable {X}

/-! ## `reverse` -/

/-- **`reverse`** turns the list at `hd` into the list of the items in the other order, in the
thread that owns the list, in the plain mode. It returns. -/
theorem reverse_thread (hd : Option Ptr) (xs : List (BitVec 32)) :
    FTTotalTriple (list X hd xs ⋆ plain) (reverse hd) (fun r => list X r xs.reverse ⋆ plain) := by
  unfold reverse
  fsym

/-- `reverse_thread` read in one thread. -/
theorem reverse_total (hd : Option Ptr) (xs : List (BitVec 32)) :
    FTotalTriple (list X hd xs ⋆ plain) (reverse hd) (fun r => list X r xs.reverse ⋆ plain) :=
  (reverse_thread hd xs).toFTotalTriple

theorem reverse_spec (hd : Option Ptr) (xs : List (BitVec 32)) :
    FTriple (list X hd xs ⋆ plain) (reverse hd) (fun r => list X r xs.reverse ⋆ plain) :=
  (reverse_total hd xs).toPartial

/-! ## `sum` -/

variable (X)

/-- The invariant of `sum`: the visited prefix `ys` is a segment, the rest `zs` (`n` items) a list
at the cursor, and the total so far is the sum of `ys`. -/
def sumInv (hd : Option Ptr) (xs : List (BitVec 32)) (s : sumLocals) (n : Nat) : FAssn :=
  FAssn.ex fun ys => FAssn.ex fun zs =>
    ⟪xs = ys ++ zs ∧ zs.length = n ∧ s.s.toNat = (ys.map BitVec.toNat).sum⟫ ⋆
      (lseg X hd s.p ys ⋆ list X s.p zs)

def sumPost (hd : Option Ptr) (xs : List (BitVec 32)) (r : sumExit × sumLocals) : FAssn :=
  ⟪r.1 = .br5 ∧ r.2.s.toNat = (xs.map BitVec.toNat).sum⟫ ⋆ list X hd xs

variable {X}

theorem sum_step (hd : Option Ptr) (xs : List (BitVec 32))
    (htot : (xs.map BitVec.toNat).sum < 2 ^ 64) (s : sumLocals) (n : Nat) :
    FTotalTriple (sumInv X hd xs s n ⋆ credits 1) (sum.loop6.run s)
      (fun r => floopExact sum.again6 (sumInv X hd xs) (sumPost X hd xs) n r ⋆ spent 1) := by
  unfold sum.loop6 sumInv
  fsym [listSeg_snoc_upd]

/-- **The generated loop of `sum` with its exact step count**: from the list's head and a zero
total it exits with the sum after `xs.length + 1` body runs (one per node and the final null
test), paid by as many credits and returning as many receipts. -/
theorem sum_loop_exact {mb : Lean.Order.MonoBind (MM sumLocals)} (hd : Option Ptr)
    (xs : List (BitVec 32)) (htot : (xs.map BitVec.toNat).sum < 2 ^ 64) (s : sumLocals)
    (hs : s.s = 0) (hp : s.p = hd) :
    FTotalTriple (list X hd xs ⋆ credits (xs.length + 1))
      ((@Zig.loop (MM sumLocals) _ _ mb _ sum.loop6 sum.again6).run s)
      (fun r => (FAssn.ex fun t : sumLocals =>
        ⟪r = (.br5, t) ∧ t.s.toNat = (xs.map BitVec.toNat).sum⟫ ⋆ list X hd xs) ⋆
          spent (xs.length + 1)) :=
  (FTotalTriple.loop_exact (sum_step (X := X) hd xs htot) s xs.length).conseq
    (fun _ h => sep_mono_left (fun _ h => ⟨[], xs, sep_lift.mpr ⟨⟨rfl, rfl, by simp [hs]⟩,
      sep_lift.mpr ⟨hp.symm, by rwa [hp]⟩⟩⟩) h)
    fun ⟨e, t⟩ _ h => sep_mono_left (fun _ h => by
      obtain ⟨⟨he, ht⟩, h⟩ := sep_lift.mp h
      exact ⟨t, sep_lift.mpr ⟨⟨by simp only at he; rw [he], ht⟩, h⟩⟩) h

/-- **`sum`** returns the sum of the list's items and leaves the list unchanged, if the sum fits
in a `u64` (in the plain mode; the loop by its registered invariant). -/
theorem sum_total (hd : Option Ptr) (xs : List (BitVec 32))
    (htot : (xs.map BitVec.toNat).sum < 2 ^ 64) :
    FTotalTriple (list X hd xs ⋆ plain) (sum hd)
      (fun r => ⟪r = BitVec.ofNat 64 (xs.map BitVec.toNat).sum⟫ ⋆ (list X hd xs ⋆ plain)) := by
  unfold sum
  fsym [listSeg_snoc_upd]

/-- **`sum` with its exact step count**: `xs.length + 1` steps (the loop's body runs), paid by as
many credits and returning as many receipts. -/
theorem sum_exact (hd : Option Ptr) (xs : List (BitVec 32))
    (htot : (xs.map BitVec.toNat).sum < 2 ^ 64) :
    FTotalTriple (list X hd xs ⋆ credits (xs.length + 1)) (sum hd)
      (fun r => (⟪r = BitVec.ofNat 64 (xs.map BitVec.toNat).sum⟫ ⋆ list X hd xs) ⋆
        spent (xs.length + 1)) := by
  unfold sum
  fsym [sum_loop_exact (htot := htot)]

/-! ## Admissible inputs -/

/-- The empty list owns nothing: an admissible input of every list claim. -/
theorem list_nil_admit : Witness.FAdmit (list X none []) :=
  Witness.FAdmit.of_mem ⟨rfl, by funext ⟨b, o⟩; simp [Mem.fheap, Mem.heap, FHeap.empty], rfl, rfl⟩
    Witness.fseq_default

/-- The empty list in the plain mode. -/
theorem list_nil_admit_plain : Witness.FAdmit (list X none [] ⋆ plain) :=
  Witness.FAdmit.of_mem_plain ⟨rfl, by funext ⟨b, o⟩; simp [Mem.fheap, Mem.heap, FHeap.empty], rfl, rfl⟩
    Witness.fseq_default

nonvacuity_witness reverse_total := ⟨fun _ => emp, none, [], list_nil_admit_plain⟩
nonvacuity_witness reverse_spec := ⟨fun _ => emp, none, [], list_nil_admit_plain⟩
liveness_witness reverse_spec :=
  ⟨fun _ => emp, none, [], Witness.FLive.of_total (reverse_total none []) list_nil_admit_plain⟩
nonvacuity_witness sum_total := ⟨fun _ => emp, none, [], by decide, list_nil_admit_plain⟩

end Lists.Linked
