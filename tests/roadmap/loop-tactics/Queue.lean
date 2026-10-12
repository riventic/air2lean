import Proofs.Lists.Gen
import ZigLean.Sep.Full.Loop
import ZigLean.Sep.Full.Auto
import ZigLean.Sep.Full.Strength

/-!
# A queue traversal in the full-state logic

The queue is the singly linked list of `examples/lists/lists.zig`: `lseg hd tl ys` is the
segment from the head `hd` to the cursor `tl` holding the items `ys` in queue order, and
`list hd xs` is the whole queue. The generated `Lists.sum` walks the queue from its head and
adds each `u32` item to a `u64` total with overflow checking.

* `step_nil`/`step_cons`: one run of the loop body at the end of the queue and at a node, by
  `fsym` (the node's field loads, `&n.val`, the widening `@intCast` and the checked add).
* `sum_step`/`sum_loop`: the loop by `FTotalTriple.loop_ghost`; the ghost measure is the number
  of remaining nodes (no local counts it).
* `sum_total`: under the explicit capacity premise `xs.length ≤ 2 ^ 32`, `sum` returns (no
  overflow panic, no divergence) the exact sum and leaves the queue unchanged.
* `sum_total_legacy`: the legacy total triple on every `Mem.FSeq` memory, through
  `FTotalTriple.toTotal_on`.

A node owns its two fields (`pts`), not its padding and not the block's size: the rest of the
16-byte block stays in the frame. The legacy `Lists.node` of `Proofs/Lists/Sep.lean` also pins
the block's size and kind in every byte, so it is not size-free and `toTotal_on` does not take
it; the full-state statement is the one with the smaller footprint.
-/

namespace Lists.Queue
open Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto

/-- A node of `examples/lists/lists.zig` at `p`: `next` at offset 0, `val` at offset 8. -/
def node (p : Ptr) (v : BitVec 32) (q : Option Ptr) : FAssn :=
  up (pts p 8 q) ⋆ up (pts (p.add 8) 4 v)

/-- The segment from `hd` to `tl` holds `ys`; its last node points to `tl`. -/
def lseg : Option Ptr → Option Ptr → List (BitVec 32) → FAssn
  | hd, tl, [] => ⟪hd = tl⟫
  | hd, tl, v :: vs => FAssn.ex fun p => FAssn.ex fun q => ⟪hd = some p⟫ ⋆ (node p v q ⋆ lseg q tl vs)

/-- The queue from `hd` holds `xs`: the segment that ends at `null`. -/
abbrev list (hd : Option Ptr) (xs : List (BitVec 32)) : FAssn := lseg hd none xs

theorem lseg_snoc {q : Option Ptr} {p : Ptr} {v : BitVec 32} :
    ∀ {hd : Option Ptr} {ys : List (BitVec 32)} {r : Res},
      (lseg hd (some p) ys ⋆ node p v q) r → lseg hd q (ys ++ [v]) r
  | _, [], _, h => by
    obtain ⟨rfl, hn⟩ := sep_lift.mp h
    exact ⟨p, q, sep_lift.mpr ⟨rfl, sep_comm (sep_lift.mpr ⟨rfl, hn⟩)⟩⟩
  | _, y :: ys, _, h => by
    obtain ⟨p', h⟩ := sep_ex.mp h
    obtain ⟨q', h⟩ := sep_ex.mp h
    obtain ⟨hp, h⟩ := sep_lift.mp (sep_assoc h)
    exact ⟨p', q', sep_lift.mpr ⟨hp, sep_mono_right (fun _ => lseg_snoc) (sep_assoc h)⟩⟩


/-- The visited prefix `ys` is a segment, the rest `zs` (`n` items) a queue at the cursor. -/
def sumInv (hd : Option Ptr) (xs : List (BitVec 32)) (s : sumLocals) (n : Nat) : FAssn :=
  FAssn.ex fun ys => FAssn.ex fun zs =>
    ⟪xs = ys ++ zs ∧ zs.length = n ∧ s.s.toNat = (ys.map BitVec.toNat).sum⟫ ⋆ (lseg hd s.p ys ⋆ list s.p zs)

def sumPost (hd : Option Ptr) (xs : List (BitVec 32)) (r : sumExit × sumLocals) : FAssn :=
  ⟪r.1 = .br5 ∧ r.2.s.toNat = (xs.map BitVec.toNat).sum⟫ ⋆ list hd xs

/-- The body at the end of the queue: it exits. -/
theorem step_nil (t : BitVec 64) (R : FAssn) :
    FTotalTriple R (sum.loop6.run ⟨t, none⟩) (fun r => ⟪r = (.br5, ⟨t, none⟩)⟫ ⋆ R) := by
  unfold sum.loop6
  fsym

/-- The body at a node: it adds the node's item and moves to the next node. -/
theorem step_cons (t : BitVec 64) (p : Ptr) (q : Option Ptr) (z : BitVec 32) (R : FAssn)
    (hfit : t.toNat + z.toNat < 2 ^ 64) :
    FTotalTriple (node p z q ⋆ R) (sum.loop6.run ⟨t, some p⟩)
      (fun r => ⟪r.1 = .rep6 ∧ r.2.p = q ∧ r.2.s.toNat = t.toNat + z.toNat⟫ ⋆ (node p z q ⋆ R)) := by
  unfold sum.loop6 node
  fsym

theorem sum_step (hd : Option Ptr) (xs : List (BitVec 32)) (hlen : xs.length ≤ 2 ^ 32)
    (s : sumLocals) (n : Nat) :
    FTotalTriple (sumInv hd xs s n) (sum.loop6.run s) (floopNext sum.again6 (sumInv hd xs) (sumPost hd xs) n) := by
  obtain ⟨t, sp⟩ := s
  refine FTotalTriple.ex fun ys => FTotalTriple.ex fun zs => FTotalTriple.lift fun ⟨hxs, hn, hsum⟩ => ?_
  simp only at hsum
  cases zs with
  | nil =>
    refine FTotalTriple.pre (P := ⟪sp = none⟫ ⋆ lseg hd sp ys) ?_ fun _ h => sep_comm h
    refine FTotalTriple.lift fun hsp => ?_
    subst hsp
    refine (step_nil t _).post fun r x h => ?_
    obtain ⟨hr, h'⟩ := sep_lift.mp h
    subst hr
    exact floopNext_exit rfl (sep_lift.mpr ⟨⟨rfl, by simpa [hxs] using hsum⟩, by simpa [hxs] using h'⟩)
  | cons z zs =>
    refine FTotalTriple.pre (P := FAssn.ex fun p => FAssn.ex fun q =>
      ⟪sp = some p⟫ ⋆ (node p z q ⋆ (lseg hd sp ys ⋆ list q zs))) ?_ fun _ h => by
        obtain ⟨p, h⟩ := sep_ex.mp (sep_comm h)
        obtain ⟨q, h⟩ := sep_ex.mp h
        obtain ⟨hp, h⟩ := sep_lift.mp (sep_assoc h)
        refine ⟨p, q, sep_lift.mpr ⟨hp, ?_⟩⟩
        rwa [show (node p z q ⋆ (lseg hd sp ys ⋆ list q zs)) = ((node p z q ⋆ list q zs) ⋆ lseg hd sp ys) by ac_rfl]
    refine FTotalTriple.ex fun p => FTotalTriple.ex fun q => FTotalTriple.lift fun hp => ?_
    subst hp
    have hbound := sum_toNat_lt (k := 32) xs hlen
    have hfit : t.toNat + z.toNat < 2 ^ 64 := by
      subst hxs; simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons] at hbound
      omega
    refine (step_cons t p q z _ hfit).post fun ⟨e, s'⟩ x h => ?_
    obtain ⟨⟨he, hq, hs⟩, h2⟩ := sep_lift.mp h
    simp only at he hq hs
    subst he
    refine floopNext_repeat rfl (n' := zs.length) (by simp at hn; omega) ⟨ys ++ [z], zs, sep_lift.mpr ⟨⟨by simp [hxs], rfl, by simp [hs, hsum]⟩, ?_⟩⟩
    rw [hq]
    refine sep_mono_left (P := lseg hd (some p) ys ⋆ node p z q) (fun _ => lseg_snoc) ?_
    rwa [show ((lseg hd (some p) ys ⋆ node p z q) ⋆ list q zs) = (node p z q ⋆ (lseg hd (some p) ys ⋆ list q zs)) by ac_rfl]


/-- The generated loop of `sum`, as a rule for `fsym`: from the queue's head and a zero total it
exits with the exact sum. -/
theorem sum_loop {mb : Lean.Order.MonoBind (MM sumLocals)} (hd : Option Ptr) (xs : List (BitVec 32))
    (hlen : xs.length ≤ 2 ^ 32) (s : sumLocals) (hs : s.s = 0) (hp : s.p = hd) :
    FTotalTriple (list hd xs) ((@Zig.loop (MM sumLocals) _ _ mb _ sum.loop6 sum.again6).run s)
      (fun r => FAssn.ex fun t : sumLocals =>
        ⟪r = (.br5, t) ∧ t.s.toNat = (xs.map BitVec.toNat).sum⟫ ⋆ list hd xs) :=
  (FTotalTriple.loop_ghost (sumInv hd xs) (sumPost hd xs) (sum_step hd xs hlen) s xs.length).pre
    (fun _ h => ⟨[], xs, Full.sep_lift.mpr ⟨⟨rfl, rfl, by simp [hs]⟩,
      Full.sep_lift.mpr ⟨hp.symm, by rwa [hp]⟩⟩⟩)
    |>.post fun ⟨e, t⟩ _ h => by
      obtain ⟨⟨he, ht⟩, h⟩ := sep_lift.mp h
      exact ⟨t, sep_lift.mpr ⟨⟨by simp only at he; rw [he], ht⟩, h⟩⟩

/-- `sum` returns the exact sum of the queue's items and leaves the queue unchanged, under the
capacity premise `xs.length ≤ 2 ^ 32`. -/
theorem sum_total (hd : Option Ptr) (xs : List (BitVec 32)) (hlen : xs.length ≤ 2 ^ 32) :
    FTotalTriple (list hd xs) (sum hd)
      (fun r => ⟪r.toNat = (xs.map BitVec.toNat).sum⟫ ⋆ list hd xs) := by
  unfold sum
  fsym [sum_loop]


/-! ## The legacy statement (strength check) -/

/-- `list` as a legacy assertion. -/
def plist : Option Ptr → List (BitVec 32) → Assn
  | hd, [] => ⌜hd = none⌝ ∗ Assn.emp
  | hd, v :: vs => Assn.ex fun p => Assn.ex fun q =>
      ⌜hd = some p⌝ ∗ ((pts p 8 q ∗ pts (p.add 8) 4 v) ∗ plist q vs)

theorem up_plist : ∀ (hd : Option Ptr) (xs : List (BitVec 32)) (r : Res), up (plist hd xs) r ↔ list hd xs r
  | _, [], _ => by simp only [plist, list, lseg]; rw [up_lift, up_emp]; rfl
  | hd, v :: vs, r => by
    simp only [plist, list, lseg, up_ex, FAssn.ex]
    refine exists_congr fun p => exists_congr fun q => ?_
    rw [up_lift, Full.sep_lift]
    refine and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩
    · exact sep_mono (fun _ h => up_sep h) (fun r' h => (up_plist q vs r').mp h) (up_sep h)
    · exact sep_up (sep_mono (fun _ h => sep_up h) (fun r' h => (up_plist q vs r').mpr h) h)

theorem plist_sizeFree : ∀ (hd : Option Ptr) (xs : List (BitVec 32)), SizeFree (fun _ => none) (plist hd xs)
  | _, [] => SizeFree.sep SizeFree.lift SizeFree.emp
  | _, _ :: vs => SizeFree.ex fun _ => SizeFree.ex fun q => SizeFree.sep SizeFree.lift
      (SizeFree.sep (SizeFree.sep (SizeFree.pts _ _ _) (SizeFree.pts _ _ _)) (plist_sizeFree q vs))

/-- `sum_total` as the legacy total triple on every `Mem.FSeq` memory (`FTotalTriple.toTotal_on`). -/
theorem sum_total_legacy (hd : Option Ptr) (xs : List (BitVec 32)) (hlen : xs.length ≤ 2 ^ 32) :
    TotalTripleIn Mem.FSeq (plist hd xs) (sum hd)
      (fun r => ⌜r.toNat = (xs.map BitVec.toNat).sum⌝ ∗ plist hd xs) :=
  FTotalTriple.toTotal_on
    (((sum_total hd xs hlen).pre fun r h => (up_plist hd xs r).mp h).post fun _ r h => by
      obtain ⟨hv, h⟩ := Full.sep_lift.mp h
      exact up_lift.mpr ⟨hv, (up_plist hd xs r).mpr h⟩)
    fun _ => SizeFree.sep SizeFree.lift (plist_sizeFree hd xs)

end Lists.Queue

-- Only the standard axioms: no `sorryAx`, no `native_decide` (`Lean.ofReduceBool`).
/-- info: 'Lists.Queue.sum_total_legacy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lists.Queue.sum_total_legacy
