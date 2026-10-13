import Proofs.Slices.Gen
import ZigLean.Sep.Full.AutoAll

/-!
# Separation-logic proofs about `examples/slices/slices.zig`

`bump` on the global counter, `copyWithin` with overlapping ranges, `fill`, and `reverse` (a loop
with a separation invariant). Each spec is a total triple of the full-state logic (`FTotalTriple`):
the run returns and the frame (the rest of the memory) stays unchanged. `fsym` walks the
generated code with the library's array rules (`ZigLean/Sep/Full/Arr.lean`: items, item pointers,
`@memset`, `@memmove`); the `reverse` loop is `FTotalTriple.loop_measure` with the invariant
`revInv` and the measure `revMeas`, its body walked by `fsym`. The strength log
(`tests/roadmap/strength-log/ProofsSlices.lean`) gives back the legacy statements.
-/

open Slices Zig Zig.Full FAssn

/-- The global `counter` is block 0 of `mem0 σ`. -/
abbrev counter : Ptr := ⟨some 0, 0⟩

/-- At program start, the memory owns the counter with the value 0, for every placement `σ`:
the counter's address is only known to be 4-aligned. -/
theorem counter_init (σ : Placement) :
    ∃ h hF, Heap.Disjoint h hF ∧ (mem0 σ).heap = h ∪ hF ∧ pts counter 4 (0 : BitVec 32) h := by
  obtain ⟨A, hb⟩ : ∃ A, (mem0 σ).blocks[0]? = some ⟨Enc.encode (0 : BitVec 32), 4, .global, true, A⟩ :=
    ⟨_, by simp [mem0, Mem.ofGlobals_getElem?]; rfl⟩
  have hA : A % 4 = 0 := by simpa using Mem.ofGlobals_addr_mod hb (by simp)
  obtain ⟨h, hF, hd, hm, hbytes⟩ := Mem.heap_split hb rfl
  refine ⟨h, hF, hd, hm, A, _, _, _, by simpa using hA, LawfulEnc.size_encode _,
    LawfulEnc.decode_encode _, hbytes, by simp⟩

/-- `bump` adds 1 to the counter and returns the new value. -/
theorem bump_spec (x : BitVec 32) (hx : x.toNat + 1 < 2 ^ 32) :
    FTotalTriple (up (pts counter 4 x)) bump
      (fun r => ⟪r = x + 1⟫ ⋆ up (pts counter 4 (x + 1))) := by
  fsym

/-- `@memmove` inside one slice: the `n` items from `d` on become the `n` items from `s` on, read
before the copy, also if the two ranges overlap. -/
theorem copyWithin_spec (sl : Slice) (vs : List (BitVec 32)) (d s n : BitVec 64)
    (hlen : sl.len.toNat = vs.length) (hd : d.toNat + n.toNat ≤ vs.length)
    (hs : s.toNat + n.toNat ≤ vs.length) :
    FTotalTriple (up (arr sl.ptr vs)) (copyWithin sl d s n)
      (fun _ => up (arr sl.ptr (copyItems vs d.toNat s.toNat n.toNat))) := by
  fsym

/-- `@memset` of a whole slice: every item becomes `v`. -/
theorem fill_sep (sl : Slice) (vs : List (BitVec 8)) (v : BitVec 8) (hlen : sl.len.toNat = vs.length) :
    FTotalTriple (up (arr sl.ptr vs)) (fill sl v) (fun _ => up (arr sl.ptr (List.replicate vs.length v))) := by
  fsym

/-! ## `reverse` -/

/-- The invariant of the `reverse` loop: the items before `i` and after `j` are swapped, the
others are as at the start. -/
def revInv (p : Ptr) (vs : List (BitVec 32)) (s : reverseLocals) : FAssn :=
  FAssn.ex fun ws : List (BitVec 32) =>
    ⟪ws.length = vs.length ∧ s.i.toNat + s.j.toNat + 1 = vs.length ∧
      ∀ k, k < vs.length →
        ws[k]? = if k < s.i.toNat ∨ s.j.toNat < k then vs[vs.length - 1 - k]? else vs[k]?⟫ ⋆
    up (arr p ws)

/-- The number of iterations that are left. -/
def revMeas (s : reverseLocals) : Nat := s.j.toNat + 1 - s.i.toNat

/-- One iteration with `i < j`: items `i` and `j` are swapped, `i` goes up and `j` down. -/
theorem reverse_swap (sl : Slice) (ws : List (BitVec 32)) (s : reverseLocals)
    (hlen : sl.len.toNat = ws.length) (hlt : s.i.toNat < s.j.toNat) (hj : s.j.toNat < ws.length) :
    FTotalTriple (up (arr sl.ptr ws)) ((reverse.loop15 sl).run s)
      (fun r => ⟪r.1 = .rep15 ∧ r.2.i.toNat = s.i.toNat + 1 ∧ r.2.j.toNat + 1 = s.j.toNat⟫ ⋆
        up (arr sl.ptr ((ws.set s.i.toNat ws[s.j.toNat]).set s.j.toNat ws[s.i.toNat]))) := by
  unfold reverse.loop15
  fsym

/-- The iteration with `j ≤ i`: the loop exits. -/
theorem reverse_exit (sl : Slice) (R : FAssn) (s : reverseLocals) (hge : ¬ s.i.toNat < s.j.toNat) :
    FTotalTriple R ((reverse.loop15 sl).run s) (fun r => ⟪r = (.br14, s)⟫ ⋆ R) := by
  unfold reverse.loop15
  fsym

theorem reverse_step (sl : Slice) (vs : List (BitVec 32)) (hlen : sl.len.toNat = vs.length)
    (s : reverseLocals) :
    FTotalTriple (revInv sl.ptr vs s) ((reverse.loop15 sl).run s)
      (fun r => if reverse.again15 r.1 then ⟪revMeas r.2 < revMeas s⟫ ⋆ revInv sl.ptr vs r.2
        else ⟪r.1 = .br14⟫ ⋆ up (arr sl.ptr vs.reverse)) := by
  refine FTotalTriple.ex fun ws => FTotalTriple.lift fun ⟨hwl, hij, hk⟩ => ?_
  by_cases hlt : s.i.toNat < s.j.toNat
  · have hjn : s.j.toNat < ws.length := by omega
    have hin : s.i.toNat < ws.length := by omega
    refine (reverse_swap sl ws s (by omega) hlt hjn).post fun ⟨e, t⟩ _ h => ?_
    obtain ⟨⟨he, hi1, hj1⟩, hw₂⟩ := sep_lift.mp h
    simp only at he hi1 hj1
    subst he
    simp only [reverse.again15, ↓reduceIte]
    refine sep_lift.mpr ⟨by simp only [revMeas]; omega, _, sep_lift.mpr ⟨⟨by simp [hwl], by omega, ?_⟩, hw₂⟩⟩
    intro k hkn
    simp only [hi1]
    rw [List.getElem?_set, List.getElem?_set]
    by_cases hkj : k = s.j.toNat
    · subst hkj
      simp only [↓reduceIte, List.length_set, hjn]
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)), ← List.getElem?_eq_getElem hin, hk _ (by omega),
        ite_eq_right_of_eq_false _ _ (eq_false (by omega)), show vs.length - 1 - s.j.toNat = s.i.toNat by omega]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (Ne.symm hkj))]
      by_cases hki : k = s.i.toNat
      · subst hki
        simp only [↓reduceIte, hin]
        rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)), ← List.getElem?_eq_getElem hjn, hk _ (by omega),
          ite_eq_right_of_eq_false _ _ (eq_false (by omega)), show vs.length - 1 - s.i.toNat = s.j.toNat by omega]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (Ne.symm hki)), hk k hkn]
        have : (k < s.i.toNat + 1 ∨ t.j.toNat < k) ↔ (k < s.i.toNat ∨ s.j.toNat < k) := by omega
        simp only [this]
  · refine (reverse_exit sl _ s hlt).post fun r _ h => ?_
    obtain ⟨hr, hw'⟩ := sep_lift.mp h
    subst hr
    simp only [reverse.again15, Bool.false_eq_true, ↓reduceIte]
    have : ws = vs.reverse := by
      apply List.ext_getElem?
      intro k
      by_cases hkn : k < vs.length
      · rw [hk k hkn, List.getElem?_reverse hkn]
        split
        · rfl
        · -- the middle item: `k = n - 1 - k`
          congr 1; omega
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]
    exact Full.sep_lift.mpr ⟨trivial, this ▸ hw'⟩

/-- The generated loop of `reverse`, as a rule for `fsym`: from `i = 0` and `j = n - 1` it exits
with the items in the other order. -/
theorem reverse_loop {mb : Lean.Order.MonoBind (MM reverseLocals)} (sl : Slice)
    (vs : List (BitVec 32)) (hlen : sl.len.toNat = vs.length) (s : reverseLocals)
    (hi : s.i.toNat = 0) (hj : s.j.toNat + 1 = vs.length) :
    FTotalTriple (up (arr sl.ptr vs))
      ((@Zig.loop (MM reverseLocals) _ _ mb _ (reverse.loop15 sl) reverse.again15).run s)
      (fun r => FAssn.ex fun t : reverseLocals => ⟪r = (.br14, t)⟫ ⋆ up (arr sl.ptr vs.reverse)) :=
  (FTotalTriple.loop_measure (revInv sl.ptr vs) revMeas _ (reverse_step sl vs hlen) s).pre
    (fun _ h => ⟨vs, Full.sep_lift.mpr ⟨⟨rfl, by omega, fun k hk => by
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]⟩, h⟩⟩)
    |>.post fun ⟨e, t⟩ _ h => by
      obtain ⟨he, h⟩ := Full.sep_lift.mp h
      exact ⟨t, Full.sep_lift.mpr ⟨by simp only at he; rw [he], h⟩⟩

/-- `reverse` reverses the items in place. -/
theorem reverse_spec (sl : Slice) (vs : List (BitVec 32)) (hlen : sl.len.toNat = vs.length) :
    FTotalTriple (up (arr sl.ptr vs)) (reverse sl) (fun _ => up (arr sl.ptr vs.reverse)) := by
  unfold reverse
  fsym [reverse_loop sl vs hlen]
  -- The empty slice returns before the loop: its items are their own reverse.
  obtain rfl : vs = [] := List.eq_nil_of_length_eq_zero (by simp_all)
  exact EUpd.of_imp fun _ h => h

/-! ## Non-vacuity witnesses: one item in one block

The triples are total: the return is part of the claim, so they need no liveness witness. -/

theorem pts32_pre : Witness.FAdmit (up (pts counter 4 (0 : BitVec 32))) :=
  Witness.FAdmit.up Witness.pts32 (Witness.mem1_fseq _ _ (by decide +kernel))

theorem arr32_pre : Witness.FAdmit (up (arr Witness.p0 [(0 : BitVec 32)])) :=
  Witness.FAdmit.up Witness.arr32 (Witness.mem1_fseq _ _ (by decide +kernel))

theorem arr8_pre : Witness.FAdmit (up (arr Witness.p0 [(0 : BitVec 8)])) :=
  Witness.FAdmit.up (Witness.mem1_arr1 0 (by decide +kernel)) (Witness.mem1_fseq _ _ (by decide +kernel))

nonvacuity_witness bump_spec := ⟨0, by decide, pts32_pre⟩
nonvacuity_witness copyWithin_spec := ⟨⟨Witness.p0, 1⟩, [0], 0, 0, 0, rfl, by decide, by decide, arr32_pre⟩
nonvacuity_witness fill_sep := ⟨⟨Witness.p0, 1⟩, [0], 1, rfl, arr8_pre⟩
nonvacuity_witness reverse_spec := ⟨⟨Witness.p0, 1⟩, [0], rfl, arr32_pre⟩
