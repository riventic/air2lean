import Proofs.Lists.Sep
import ZigLean.Sep.LoopTemplate
import ZigLean.Range

/-!
# A queue traversal proved with the loop template

The queue is the singly linked list of `examples/lists/lists.zig`: `lseg hd tl ys` is the
segment from the head `hd` to the cursor `tl` holding the items `ys` in queue order, and
`Lists.list hd xs` is the whole queue. The generated `Lists.sum` walks the queue from its head
and adds each `u32` item to a `u64` total with overflow checking.

`sum_total` is a total-correctness theorem: under the explicit capacity premise
`xs.length ≤ 2 ^ 32`, `sum` returns (no overflow panic, no divergence) the exact sum and leaves
the queue unchanged. The proof uses `loop_template`, the `zig_range` conversions, the node
interface of `Proofs/Lists/Sep.lean` (`node_val_run`, `node_next_run`, `focus_mid`) and
separation connectives. It does not unfold `Zig.load`, byte encodings, blocks, or allocators.
-/

namespace Lists.Queue
open Zig Assn

/-- The segment from `hd` to `tl`: the nodes hold `ys`, and the last one points to `tl`. -/
def lseg (hd tl : Option Ptr) : List (BitVec 32) → Assn
  | [] => ⌜hd = tl⌝
  | v :: vs => fun h => ∃ p q, hd = some p ∧ (node p v q ∗ lseg q tl vs) h

/-- Extending a segment by the node at its cursor. -/
theorem lseg_snoc {hd q : Option Ptr} {p : Ptr} {v : BitVec 32} :
    ∀ {ys : List (BitVec 32)} {h : Heap},
      (lseg hd (some p) ys ∗ node p v q) h → lseg hd q (ys ++ [v]) h
  | [], _, hs => by
    obtain ⟨rfl, hn⟩ := sep_lift.mp hs
    exact ⟨p, q, rfl, sep_comm (sep_lift.mpr ⟨rfl, hn⟩)⟩
  | y :: ys, _, ⟨h₁, h₂, d, he, ⟨p', q', hp, hs₁⟩, hn⟩ => by
    subst he
    obtain ⟨g₁, g₂, d', he', hy, hr⟩ := sep_assoc (h := h₁ ∪ h₂) ⟨h₁, h₂, d, rfl, hs₁, hn⟩
    exact ⟨p', q', hp, g₁, g₂, d', he', hy, lseg_snoc hr⟩

/-- A segment ending at `none` is the whole queue. -/
theorem lseg_none {hd : Option Ptr} : ∀ {ys : List (BitVec 32)} {h : Heap},
    lseg hd none ys h → list hd ys h
  | [], _, hs => hs
  | _ :: _, _, ⟨p, q, hp, hs⟩ => ⟨p, q, hp, sep_mono (fun _ hn => hn) (fun _ => lseg_none) hs⟩

/-- The visited prefix `ys` is a segment, the rest `zs` (`n` items) a queue at the cursor. -/
def sumInv (hd : Option Ptr) (xs : List (BitVec 32)) (s : sumLocals) (n : Nat) : Assn :=
  fun h => ∃ ys zs, xs = ys ++ zs ∧ zs.length = n ∧ s.s.toNat = (ys.map BitVec.toNat).sum ∧
    (lseg hd s.p ys ∗ list s.p zs) h

def sumPost (hd : Option Ptr) (xs : List (BitVec 32)) (e : sumExit) (s : sumLocals) : Assn :=
  ⌜e = .br5 ∧ s.s.toNat = (xs.map BitVec.toNat).sum⌝ ∗ list hd xs

/-- One iteration: the template's `step` premise. -/
theorem sum_step (hd : Option Ptr) (xs : List (BitVec 32)) (hlen : xs.length ≤ 2 ^ 32)
    (s : sumLocals) (n : Nat) :
    TotalTriple (sumInv hd xs s n) (sum.loop6.run s)
      (loopNext sum.again6 (sumInv hd xs) (sumPost hd xs) n) := by
  apply TotalTriple.of_run
  intro m h hF hdj hm hi hst
  obtain ⟨ys, zs, hxs, hn, hsum, hL, hZ, dLZ, rfl, hseg, hlist⟩ := hi
  cases zs with
  | nil =>
    obtain ⟨hp, rfl⟩ := hlist
    refine ⟨(.br5, s), m, hL ∪ Heap.empty, ?_, hdj, hm, ?_, hst⟩
    · simp [sum.loop6, zig_unfold, hp]
    · apply loopNext_exit rfl
      simp only [List.append_nil] at hxs
      subst hxs
      rw [Heap.union_empty]
      exact sep_lift.mpr ⟨⟨rfl, hsum⟩, lseg_none (hp ▸ hseg)⟩
  | cons z zs =>
    obtain ⟨p, q, hp, hN, hR, dNR, rfl, hnode, hrest⟩ := hlist
    obtain ⟨hfocus, dN⟩ := focus_mid dLZ dNR hdj
    obtain ⟨m₁, hv, hm₁, hst₁⟩ := node_val_run hnode (hm.trans hfocus) hst
    obtain ⟨m₂, hq, hm₂, hst₂⟩ := node_next_run hnode hm₁ hst₁
    -- The only arithmetic premise: the running total plus the item fits in `u64`.
    have hbound := sum_toNat_lt (k := 32) xs hlen
    have hfit : s.s.toNat + z.toNat < 2 ^ 64 := by
      subst hxs; simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons] at hbound
      omega
    have hz : (z.setWidth 64).toNat = z.toNat := toNat_setWidth_of_le (by decide)
    have hadd : Zig.add false s.s (z.setWidth 64) = pure (s.s + z.setWidth 64) :=
      add_unsigned_of_lt (by rw [hz]; exact hfit)
    refine ⟨(.rep6, { s with s := s.s + z.setWidth 64, p := q }), m₂, hL ∪ (hN ∪ hR), ?_, hdj,
      hm₂.trans hfocus.symm, ?_, hst₂⟩
    · simp only [StateT.run, pure, ExceptT.pure, ExceptT.mk] at hv hq
      simp [sum.loop6, zig_unfold, hp, Zig.optPayload, hv, hq, -Zig.add_unsigned, hadd]
    · apply loopNext_repeat rfl (n' := zs.length) (by simp at hn; omega)
      refine ⟨ys ++ [z], zs, by simp [hxs], rfl, ?_, ?_⟩
      · show (s.s + z.setWidth 64).toNat = _
        zig_range
        simp [hsum]
      · exact sep_mono (fun _ => lseg_snoc) (fun _ hr => hr)
          (sep_assoc' ⟨hL, hN ∪ hR, dLZ, rfl, hp ▸ hseg, hN, hR, dNR, rfl, hnode, hrest⟩)

/-- The generated loop of `sum`, by the template. -/
theorem sum_loop_total (hd : Option Ptr) (xs : List (BitVec 32)) (hlen : xs.length ≤ 2 ^ 32) :
    TotalTriple (list hd xs) ((Zig.loop sum.loop6 sum.again6).run { s := 0#64, p := hd })
      (fun r => sumPost hd xs r.1 r.2) := by
  loop_template (sumInv hd xs) (sumPost hd xs)
  case step => exact ⟨sum_step hd xs hlen⟩
  case entry => exact fun h hl => ⟨xs.length, [], xs, rfl, rfl, rfl, sep_lift.mpr ⟨rfl, hl⟩⟩

/-- `sum` returns the exact sum of the queue's items and leaves the queue unchanged, under the
capacity premise `xs.length ≤ 2 ^ 32`. -/
theorem sum_total (hd : Option Ptr) (xs : List (BitVec 32)) (hlen : xs.length ≤ 2 ^ 32) :
    TotalTriple (list hd xs) (sum hd)
      (fun r => ⌜r.toNat = (xs.map BitVec.toNat).sum⌝ ∗ list hd xs) := by
  apply TotalTriple.of_run
  intro m h hF hdj hm hl hst
  obtain ⟨⟨e, s'⟩, m', h', hr, hd', hm', hpost, hst'⟩ :=
    sum_loop_total hd xs hlen m h hF hdj hm hl hst
  obtain ⟨⟨rfl, hs⟩, hq⟩ := sep_lift.mp hpost
  refine ⟨s'.s, m', h', ?_, hd', hm', sep_lift.mpr ⟨hs, hq⟩, hst'⟩
  simp only [StateT.run, pure, ExceptT.pure, ExceptT.mk] at hr
  simp [sum, zig_unfold, hr]

end Lists.Queue

namespace Lists.Queue
open Zig Assn

/-- info: loop_template remaining premises (2):
  step : LoopTemplate sum.loop6 sum.again6 (sumInv hd xs) (sumPost hd xs)
  entry : ∀ (h : Heap), list hd xs h → ∃ n, sumInv hd xs { s := 0#64, p := hd } n h -/
#guard_msgs in
-- The template reports exactly the user premises on the generated queue loop, as named goals;
-- `exit` is discharged because the template's postcondition is the goal's.
example (hd : Option Ptr) (xs : List (BitVec 32)) (hlen : xs.length ≤ 2 ^ 32) :
    TotalTriple (list hd xs) ((Zig.loop sum.loop6 sum.again6).run { s := 0#64, p := hd })
      (fun r => sumPost hd xs r.1 r.2) := by
  loop_template? (sumInv hd xs) (sumPost hd xs)
  case step => exact ⟨sum_step hd xs hlen⟩
  case entry => exact fun h hl => ⟨xs.length, [], xs, rfl, rfl, rfl, sep_lift.mpr ⟨rfl, hl⟩⟩

end Lists.Queue

-- Only the standard axioms: no `sorryAx`, no `native_decide` (`Lean.ofReduceBool`).
/-- info: 'Lists.Queue.sum_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lists.Queue.sum_total
