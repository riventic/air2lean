import Proofs.Lists.Open
import ZigLean.Sep.Full.Loop
import ZigLean.Sep.Full.Auto
import ZigLean.Sep.Full.Witness

/-!
# The linked list of `examples/lists/lists.zig` in the full-state logic

A node (`node X p v q`) owns its two fields, `next` at offset 0 and `val` at offset 8 (`pts`), and
`X p`: whatever else its owner keeps with it. The functions here never touch the rest of a node's
allocation, so they are proved for every `X`. A list that an allocator built carries the rest of
each node's grant in `X` (its padding bytes and the allocator's token), and `X := fun _ => emp` is
a list of bare fields. `lseg X hd tl ys` is the segment from `hd` to `tl` holding `ys`, and
`list X hd xs` the whole list (the segment that ends at `null`).

* `reverse_total`: `reverse` turns the list into the list of the items in the other order, and
  returns. `reverse_spec` is its partial form.
* `sum_total`: if the sum of the items fits in a `u64`, `sum` returns it (no overflow panic) and
  leaves the list unchanged.

The loop bodies are walked by `fsym` (`step_*`); the loops are `FTotalTriple.loop_ghost` with the
number of nodes left as the measure. The program is `Proofs/Lists/Open.lean`, the translation in
which the `Allocator` parameter is an open interface; `push` and `freeAll`, which allocate and
free nodes through it, are proved for every allocator in `Proofs/Lists/Alloc.lean`, with `X` the
rest of each node's grant.
-/

namespace Lists.Linked
open Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto Lists.Open

variable (X : Ptr → FAssn)

/-- A node at `p` with the item `v` and the next pointer `q`, and `X p`. -/
def node (p : Ptr) (v : BitVec 32) (q : Option Ptr) : FAssn :=
  up (pts p 8 q) ⋆ (up (pts (p.add 8) 4 v) ⋆ X p)

/-- The segment from `hd` to `tl` holds `ys`; its last node points to `tl`. -/
def lseg : Option Ptr → Option Ptr → List (BitVec 32) → FAssn
  | hd, tl, [] => ⟪hd = tl⟫
  | hd, tl, v :: vs => FAssn.ex fun p => FAssn.ex fun q =>
      ⟪hd = some p⟫ ⋆ (node X p v q ⋆ lseg q tl vs)

/-- The list from `hd` holds `xs`: the segment that ends at `null`. -/
abbrev list (hd : Option Ptr) (xs : List (BitVec 32)) : FAssn := lseg X hd none xs

variable {X}

theorem lseg_snoc {q : Option Ptr} {p : Ptr} {v : BitVec 32} :
    ∀ {hd : Option Ptr} {ys : List (BitVec 32)} {r : Res},
      (lseg X hd (some p) ys ⋆ node X p v q) r → lseg X hd q (ys ++ [v]) r
  | _, [], _, h => by
    obtain ⟨rfl, hn⟩ := sep_lift.mp h
    exact ⟨p, q, sep_lift.mpr ⟨rfl, sep_comm (sep_lift.mpr ⟨rfl, hn⟩)⟩⟩
  | _, y :: ys, _, h => by
    obtain ⟨p', h⟩ := sep_ex.mp h
    obtain ⟨q', h⟩ := sep_ex.mp h
    obtain ⟨hp, h⟩ := sep_lift.mp (sep_assoc h)
    exact ⟨p', q', sep_lift.mpr ⟨hp, sep_mono_right (fun _ => lseg_snoc) (sep_assoc h)⟩⟩

/-- A nonempty list, with its first node's pointers as witnesses. -/
theorem list_cons {hd : Option Ptr} {z : BitVec 32} {zs : List (BitVec 32)} {R : FAssn} {r : Res}
    (h : (list X hd (z :: zs) ⋆ R) r) :
    ∃ p q, hd = some p ∧ (node X p z q ⋆ (list X q zs ⋆ R)) r := by
  obtain ⟨p, h⟩ := sep_ex.mp h
  obtain ⟨q, h⟩ := sep_ex.mp h
  obtain ⟨hp, h⟩ := sep_lift.mp (sep_assoc h)
  exact ⟨p, q, hp, sep_assoc h⟩

/-! ## `reverse` -/

/-- The body at the end of the list: it exits. -/
theorem reverse_step_nil (pr : Option Ptr) (R : FAssn) :
    FTotalTriple R (reverse.loop6.run ⟨pr, none⟩) (fun r => ⟪r = (.br5, ⟨pr, none⟩)⟫ ⋆ R) := by
  unfold reverse.loop6
  fsym

/-- The body at a node: it points the node back at `prev` and moves on. -/
theorem reverse_step_cons (pr : Option Ptr) (p : Ptr) (q : Option Ptr) (z : BitVec 32) (R : FAssn) :
    FTotalTriple (node X p z q ⋆ R) (reverse.loop6.run ⟨pr, some p⟩)
      (fun r => ⟪r = (.rep6, ⟨some p, q⟩)⟫ ⋆ (node X p z pr ⋆ R)) := by
  unfold reverse.loop6 node
  fsym

variable (X)

/-- The invariant of `reverse`: `prev` holds the first items of `xs` reversed, `cur` the other
`n`. -/
def revInv (xs : List (BitVec 32)) (s : reverseLocals) (n : Nat) : FAssn :=
  FAssn.ex fun ys => FAssn.ex fun zs =>
    ⟪xs = ys.reverse ++ zs ∧ zs.length = n⟫ ⋆ (list X s.prev ys ⋆ list X s.cur zs)

def revPost (xs : List (BitVec 32)) (r : reverseExit × reverseLocals) : FAssn :=
  ⟪r.1 = .br5⟫ ⋆ list X r.2.prev xs.reverse

variable {X}

theorem reverse_step (xs : List (BitVec 32)) (s : reverseLocals) (n : Nat) :
    FTotalTriple (revInv X xs s n) (reverse.loop6.run s)
      (floopNext reverse.again6 (revInv X xs) (revPost X xs) n) := by
  obtain ⟨pr, cu⟩ := s
  refine FTotalTriple.ex fun ys => FTotalTriple.ex fun zs => FTotalTriple.lift fun ⟨hxs, hn⟩ => ?_
  cases zs with
  | nil =>
    refine FTotalTriple.pre (P := ⟪cu = none⟫ ⋆ list X pr ys) ?_ fun _ h => sep_comm h
    refine FTotalTriple.lift fun hcu => ?_
    subst hcu
    refine (reverse_step_nil pr _).post fun r x h => ?_
    obtain ⟨hr, h'⟩ := sep_lift.mp h
    subst hr
    exact floopNext_exit rfl (sep_lift.mpr ⟨rfl, by simpa [hxs] using h'⟩)
  | cons z zs =>
    refine FTotalTriple.pre (P := FAssn.ex fun p => FAssn.ex fun q =>
      ⟪cu = some p⟫ ⋆ (node X p z q ⋆ (list X pr ys ⋆ list X q zs))) ?_ fun _ h => by
        obtain ⟨p, q, hp, h⟩ := list_cons (sep_comm h)
        refine ⟨p, q, sep_lift.mpr ⟨hp, ?_⟩⟩
        exact sep_mono_right (fun _ h => sep_comm h) h
    refine FTotalTriple.ex fun p => FTotalTriple.ex fun q => FTotalTriple.lift fun hp => ?_
    subst hp
    refine (reverse_step_cons pr p q z _).post fun r x h => ?_
    obtain ⟨hr, h'⟩ := sep_lift.mp h
    subst hr
    refine floopNext_repeat rfl (n' := zs.length) (by simp at hn; omega)
      ⟨z :: ys, zs, sep_lift.mpr ⟨⟨by simp [hxs], rfl⟩, ?_⟩⟩
    exact sep_mono_left (fun _ h => ⟨p, pr, sep_lift.mpr ⟨rfl, h⟩⟩) (sep_assoc' h')

/-- The generated loop of `reverse`, as a rule for `fsym`: from `prev = null` and the list at
`cur`, it exits with the reversed list at `prev`. -/
theorem reverse_loop {mb : Lean.Order.MonoBind (MM reverseLocals)} (hd : Option Ptr)
    (xs : List (BitVec 32)) (s : reverseLocals) (hp : s.prev = none) (hc : s.cur = hd) :
    FTotalTriple (list X hd xs)
      ((@Zig.loop (MM reverseLocals) _ _ mb _ reverse.loop6 reverse.again6).run s)
      (fun r => FAssn.ex fun t : reverseLocals => ⟪r = (.br5, t)⟫ ⋆ list X t.prev xs.reverse) :=
  (FTotalTriple.loop_ghost (revInv X xs) (revPost X xs) (reverse_step xs) s xs.length).pre
    (fun _ h => ⟨[], xs, sep_lift.mpr ⟨⟨rfl, rfl⟩,
      sep_lift.mpr ⟨hp, by rwa [hc]⟩⟩⟩)
    |>.post fun ⟨e, t⟩ _ h => by
      obtain ⟨he, h⟩ := sep_lift.mp h
      exact ⟨t, sep_lift.mpr ⟨by simp only at he; rw [he], h⟩⟩

/-- **`reverse`** turns the list at `hd` into the list of the items in the other order. It
returns. -/
theorem reverse_total (hd : Option Ptr) (xs : List (BitVec 32)) :
    FTotalTriple (list X hd xs) (reverse hd) (fun r => list X r xs.reverse) := by
  unfold reverse
  fsym [reverse_loop]

theorem reverse_spec (hd : Option Ptr) (xs : List (BitVec 32)) :
    FTriple (list X hd xs) (reverse hd) (fun r => list X r xs.reverse) :=
  (reverse_total hd xs).toPartial

/-! ## `sum` -/

/-- The body at the end of the list: it exits. -/
theorem sum_step_nil (t : BitVec 64) (R : FAssn) :
    FTotalTriple R (sum.loop6.run ⟨t, none⟩) (fun r => ⟪r = (.br5, ⟨t, none⟩)⟫ ⋆ R) := by
  unfold sum.loop6
  fsym

/-- The body at a node: it adds the node's item and moves to the next node. -/
theorem sum_step_cons (t : BitVec 64) (p : Ptr) (q : Option Ptr) (z : BitVec 32) (R : FAssn)
    (hfit : t.toNat + z.toNat < 2 ^ 64) :
    FTotalTriple (node X p z q ⋆ R) (sum.loop6.run ⟨t, some p⟩)
      (fun r => ⟪r.1 = .rep6 ∧ r.2.p = q ∧ r.2.s.toNat = t.toNat + z.toNat⟫ ⋆ (node X p z q ⋆ R)) := by
  unfold sum.loop6 node
  fsym

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
    FTotalTriple (sumInv X hd xs s n) (sum.loop6.run s)
      (floopNext sum.again6 (sumInv X hd xs) (sumPost X hd xs) n) := by
  obtain ⟨t, sp⟩ := s
  refine FTotalTriple.ex fun ys => FTotalTriple.ex fun zs => FTotalTriple.lift fun ⟨hxs, hn, hsum⟩ => ?_
  simp only at hsum
  cases zs with
  | nil =>
    refine FTotalTriple.pre (P := ⟪sp = none⟫ ⋆ lseg X hd sp ys) ?_ fun _ h => sep_comm h
    refine FTotalTriple.lift fun hsp => ?_
    subst hsp
    refine (sum_step_nil t _).post fun r x h => ?_
    obtain ⟨rfl, h'⟩ := sep_lift.mp h
    exact floopNext_exit rfl (sep_lift.mpr ⟨⟨rfl, by simpa [hxs] using hsum⟩, by simpa [hxs] using h'⟩)
  | cons z zs =>
    refine FTotalTriple.pre (P := FAssn.ex fun p => FAssn.ex fun q =>
      ⟪sp = some p⟫ ⋆ (node X p z q ⋆ (lseg X hd sp ys ⋆ list X q zs))) ?_ fun _ h => by
        obtain ⟨p, q, hp, h⟩ := list_cons (sep_comm h)
        exact ⟨p, q, sep_lift.mpr ⟨hp, sep_mono_right (fun _ h => sep_comm h) h⟩⟩
    refine FTotalTriple.ex fun p => FTotalTriple.ex fun q => FTotalTriple.lift fun hp => ?_
    subst hp
    have hfit : t.toNat + z.toNat < 2 ^ 64 := by
      subst hxs
      simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons] at htot
      omega
    refine (sum_step_cons t p q z _ hfit).post fun ⟨e, s'⟩ x h => ?_
    obtain ⟨⟨he, hq, hs⟩, h2⟩ := sep_lift.mp h
    simp only at he hq hs
    subst he
    refine floopNext_repeat rfl (n' := zs.length) (by simp at hn; omega)
      ⟨ys ++ [z], zs, sep_lift.mpr ⟨⟨by simp [hxs], rfl, by simp [hs, hsum]⟩, ?_⟩⟩
    rw [hq]
    refine sep_mono_left (P := lseg X hd (some p) ys ⋆ node X p z q) (fun _ => lseg_snoc) ?_
    rwa [show ((lseg X hd (some p) ys ⋆ node X p z q) ⋆ list X q zs) =
      (node X p z q ⋆ (lseg X hd (some p) ys ⋆ list X q zs)) by ac_rfl]

/-- The generated loop of `sum`, as a rule for `fsym`: from the list's head and a zero total it
exits with the exact sum. -/
theorem sum_loop {mb : Lean.Order.MonoBind (MM sumLocals)} (hd : Option Ptr) (xs : List (BitVec 32))
    (htot : (xs.map BitVec.toNat).sum < 2 ^ 64) (s : sumLocals) (hs : s.s = 0) (hp : s.p = hd) :
    FTotalTriple (list X hd xs) ((@Zig.loop (MM sumLocals) _ _ mb _ sum.loop6 sum.again6).run s)
      (fun r => FAssn.ex fun t : sumLocals =>
        ⟪r = (.br5, t) ∧ t.s.toNat = (xs.map BitVec.toNat).sum⟫ ⋆ list X hd xs) :=
  (FTotalTriple.loop_ghost (sumInv X hd xs) (sumPost X hd xs) (sum_step hd xs htot) s xs.length).pre
    (fun _ h => ⟨[], xs, sep_lift.mpr ⟨⟨rfl, rfl, by simp [hs]⟩,
      sep_lift.mpr ⟨hp.symm, by rwa [hp]⟩⟩⟩)
    |>.post fun ⟨e, t⟩ _ h => by
      obtain ⟨⟨he, ht⟩, h⟩ := sep_lift.mp h
      exact ⟨t, sep_lift.mpr ⟨⟨by simp only at he; rw [he], ht⟩, h⟩⟩

/-- **`sum`** returns the sum of the list's items and leaves the list unchanged, if the sum fits
in a `u64`. -/
theorem sum_total (hd : Option Ptr) (xs : List (BitVec 32))
    (htot : (xs.map BitVec.toNat).sum < 2 ^ 64) :
    FTotalTriple (list X hd xs) (sum hd)
      (fun r => ⟪r = BitVec.ofNat 64 (xs.map BitVec.toNat).sum⟫ ⋆ list X hd xs) := by
  unfold sum
  fsym [sum_loop (htot := htot)]

/-! ## Admissible inputs -/

/-- The empty list owns nothing: an admissible input of every list claim. -/
theorem list_nil_admit : Witness.FAdmit (list X none []) :=
  Witness.FAdmit.of_mem ⟨rfl, by funext ⟨b, o⟩; simp [Mem.fheap, Mem.heap, FHeap.empty], rfl, rfl⟩
    Witness.fseq_default

nonvacuity_witness reverse_total := ⟨fun _ => emp, none, [], list_nil_admit⟩
nonvacuity_witness reverse_spec := ⟨fun _ => emp, none, [], list_nil_admit⟩
liveness_witness reverse_spec :=
  ⟨fun _ => emp, none, [], Witness.FLive.of_total (reverse_total none []) list_nil_admit⟩
nonvacuity_witness sum_total := ⟨fun _ => emp, none, [], by decide, list_nil_admit⟩

end Lists.Linked
