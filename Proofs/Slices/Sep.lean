import Proofs.Slices.Gen
import ZigLean.Sep

/-!
# Separation-logic proofs about `examples/slices/slices.zig`

`bump` on the global counter, `copyWithin` with overlapping ranges, and `reverse` (a loop with a
separation invariant). Each spec is a `Triple`: the frame (the rest of the memory) stays
unchanged.
-/

open Slices Zig Assn

/-- The global `counter` is block 0 of `mem0`. -/
abbrev counter : Ptr := ⟨some 0, 0⟩

/-- At program start, the memory owns the counter with the value 0. -/
theorem counter_init : ∃ h hF, Heap.Disjoint h hF ∧ mem0.heap = h ∪ hF ∧ pts counter 4 (0 : BitVec 32) h := by
  have hb : mem0.blocks[0]? = some ⟨Enc.encode (0 : BitVec 32), 4, .global, true, 4096⟩ := by
    simp [mem0, Mem.ofGlobals, Mem.addGlobal, alignUp]
  obtain ⟨h, hF, hd, hm, hbytes⟩ := Mem.heap_split hb rfl
  refine ⟨h, hF, hd, hm, 4096, _, _, _, rfl, LawfulEnc.size_encode _, LawfulEnc.decode_encode _,
    hbytes, by decide⟩

/-- `bump` adds 1 to the counter and returns the new value. -/
theorem bump_spec (x : BitVec 32) (hx : x.toNat + 1 < 2 ^ 32) :
    Triple (pts counter 4 x) bump (fun r => ⌜r = x + 1⌝ ∗ pts counter 4 (x + 1)) := by
  apply Triple.of_run
  intro m hP hF hd hm hp hst
  -- `bump` reads the counter, writes it, reads it again: each step mutates memory (`recordAt`),
  -- so it runs on the previous step's output memory.
  obtain ⟨mA, hl, hmA, hstA⟩ := pts_load_run hp hm (by decide) hst
  obtain ⟨mB, hs, hstB, h', hd', hmB, hp'⟩ := pts_store_run hp hmA hd (by decide) hstA (x + 1#32)
  obtain ⟨mC, hl', hmC, hstC⟩ := pts_load_run hp' hmB (by decide) hstB
  have hov : x.uaddOverflow 1#32 = false := by
    have : x.toNat + 1 < 4294967296 := hx
    simp [BitVec.uaddOverflow]; omega
  refine ⟨x + 1, mC, h', ?_, hd', hmC, sep_lift.mpr ⟨rfl, hp'⟩, hstC⟩
  simp only [StateT.run, counter, pure, ExceptT.pure, ExceptT.mk] at hl hs hl'
  simp [bump, zig_unfold, Zig.add, hl, hs, hl', hov]

/-- `@memmove` inside one slice: the `n` items from `d` on become the `n` items from `s` on, read
before the copy, also if the two ranges overlap. -/
theorem copyWithin_spec (sl : Slice) (vs : List (BitVec 32)) (d s n : BitVec 64)
    (hlen : sl.len.toNat = vs.length) (hd : d.toNat + n.toNat ≤ vs.length)
    (hs : s.toNat + n.toNat ≤ vs.length) :
    Triple (arr sl.ptr vs) (copyWithin sl d s n)
      (fun _ => arr sl.ptr (copyItems vs d.toNat s.toNat n.toNat)) := by
  apply Triple.of_run
  intro m hP hF hdj hm hp hst
  obtain ⟨m', hr, hst', h', hd', hm', hp'⟩ := arr_memmove_run (d := d) (s := s) (n := n) (a := 4) hp
    hm hdj (by decide) (by decide) (by decide) hd hs hst
  refine ⟨(), m', h', ?_, hd', hm', hp', hst'⟩
  have hl := sl.len.isLt
  have hdo : d.uaddOverflow n = false := by simp [BitVec.uaddOverflow]; omega
  have hso : s.uaddOverflow n = false := by simp [BitVec.uaddOverflow]; omega
  have hdl : (d.toNat + n.toNat) % 18446744073709551616 ≤ sl.len.toNat := by
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hsl : (s.toNat + n.toNat) % 18446744073709551616 ≤ sl.len.toNat := by
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  have e4 : Enc.size (BitVec 32) = 4 := rfl
  rw [e4] at hr
  simp only [StateT.run, pure, ExceptT.pure, ExceptT.mk] at hr
  simp (config := { maxSteps := 1000000 }) [copyWithin, zig_unfold, Zig.add, Zig.le, BitVec.ule,
    hdo, hso, hdl, hsl, hr]

/-- `@memset` of a whole slice: every item becomes `v`. -/
theorem fill_sep (sl : Slice) (vs : List (BitVec 8)) (v : BitVec 8) (hlen : sl.len.toNat = vs.length) :
    Triple (arr sl.ptr vs) (fill sl v) (fun _ => arr sl.ptr (List.replicate vs.length v)) := by
  apply Triple.of_run
  intro m hP hF hd hm hp hst
  obtain ⟨m', hr, hst', h', hd', hm', hp'⟩ := arr_memset_run (a := 1) (n := sl.len) hp hm hd
    (by decide) (by decide) hlen hst v
  refine ⟨(), m', h', ?_, hd', hm', hp', hst'⟩
  simp only [StateT.run] at hr
  simp [fill, zig_unfold, hr]

/-! ## `reverse` -/

/-- The invariant of the `reverse` loop: the items before `i` and after `j` are swapped, the
others are as at the start. -/
def revInv (p : Ptr) (vs : List (BitVec 32)) (s : reverseLocals) : Assn := fun h =>
  ∃ ws : List (BitVec 32), arr p ws h ∧ ws.length = vs.length ∧
    s.i.toNat + s.j.toNat + 1 = vs.length ∧
    ∀ k, k < vs.length →
      ws[k]? = if k < s.i.toNat ∨ s.j.toNat < k then vs[vs.length - 1 - k]? else vs[k]?

/-- The number of iterations that are left. -/
def revMeas (s : reverseLocals) : Nat := s.j.toNat + 1 - s.i.toNat

theorem reverse_step (sl : Slice) (vs : List (BitVec 32)) (hlen : sl.len.toNat = vs.length)
    (hF : Heap) (s : reverseLocals) (m : Mem) (h : Heap) (hd : Heap.Disjoint h hF)
    (hm : m.heap = h ∪ hF) (hi : revInv sl.ptr vs s h) (hst : m.SingleThread) :
    ∃ e s' m' h', ((reverse.loop15 sl).run s).run m = pure ((e, s'), m') ∧
      Heap.Disjoint h' hF ∧ m'.heap = h' ∪ hF ∧ m'.SingleThread ∧
      (if reverse.again15 e then revInv sl.ptr vs s' h' ∧ revMeas s' < revMeas s
       else e = .br14 ∧ arr sl.ptr vs.reverse h') := by
  obtain ⟨ws, hw, hwl, hij, hk⟩ := hi
  by_cases hlt : s.i.toNat < s.j.toNat
  · have hjn : s.j.toNat < ws.length := by omega
    have hin : s.i.toNat < ws.length := by omega
    have e4 : Enc.size (BitVec 32) = 4 := rfl
    -- `reverse.loop15` reads item `i`, reads item `j`, writes item `i`, writes item `j`: each
    -- step mutates memory (`recordAt`), so it runs on the previous step's output memory.
    obtain ⟨mA, l1, hmA, hstA⟩ :=
      arr_load_run (a := 4) (i := s.i) hw hm (by decide) (by decide) (by decide) hin hst
    obtain ⟨mB, l2, hmB, hstB⟩ :=
      arr_load_run (a := 4) (i := s.j) hw hmA (by decide) (by decide) (by decide) hjn hstA
    obtain ⟨m₁, s₁, hst₁, h₁, hd₁, hm₁, hw₁⟩ :=
      arr_store_run (a := 4) (i := s.i) hw hmB hd (by decide) (by decide) (by decide) hin hstB
        ws[s.j.toNat]
    obtain ⟨m₂, s₂, hst₂, h₂, hd₂, hm₂, hw₂⟩ :=
      arr_store_run (a := 4) (i := s.j) hw₁ hm₁ hd₁ (by decide) (by decide) (by decide)
        (by simpa using hjn) hst₁ ws[s.i.toNat]
    rw [e4] at l1 l2 s₁ s₂
    simp only [StateT.run, pure, ExceptT.pure, ExceptT.mk] at l1 l2 s₁ s₂
    have hil : s.i.toNat < sl.len.toNat := by omega
    have hjl : s.j.toNat < sl.len.toNat := by omega
    have hio : s.i.uaddOverflow 1#64 = false := by simp [BitVec.uaddOverflow]; omega
    have hjo : s.j.usubOverflow 1#64 = false := by simp [BitVec.usubOverflow]; omega
    refine ⟨.rep15, { { s with i := s.i + 1#64 } with j := s.j - 1#64 }, m₂, h₂, ?_, hd₂, hm₂, hst₂,
      ?_⟩
    · simp [reverse.loop15, zig_unfold, Zig.lt, BitVec.ult, Zig.add, Zig.sub, hlt, hil, hjl, l1, l2,
        s₁, s₂, hio, hjo]
    · have hi1 : (s.i + 1#64).toNat = s.i.toNat + 1 := by
        rw [BitVec.toNat_add_of_lt (by simp; have := s.j.isLt; omega)]; simp
      have hj1 : (s.j - 1#64).toNat = s.j.toNat - 1 := by
        rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp
      simp only [reverse.again15, ↓reduceIte]
      refine ⟨⟨_, hw₂, by simp [hwl], by simp only [hi1, hj1]; omega, ?_⟩, ?_⟩
      · intro k hkn
        simp only [hi1, hj1]
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
            have : (k < s.i.toNat + 1 ∨ s.j.toNat - 1 < k) ↔ (k < s.i.toNat ∨ s.j.toNat < k) := by
              omega
            simp only [this]
      · simp only [revMeas, hi1, hj1]; omega
  · refine ⟨.br14, s, m, h, ?_, hd, hm, hst, ?_⟩
    · simp [reverse.loop15, zig_unfold, Zig.lt, BitVec.ult, hlt]
    · simp only [reverse.again15, Bool.false_eq_true, ↓reduceIte, true_and]
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
      rw [← this]; exact hw

/-- `reverse` reverses the items in place. -/
theorem reverse_spec (sl : Slice) (vs : List (BitVec 32)) (hlen : sl.len.toNat = vs.length) :
    Triple (arr sl.ptr vs) (reverse sl) (fun _ => arr sl.ptr vs.reverse) := by
  apply Triple.of_run
  intro m hP hF hd hm hp hst
  by_cases hn : vs.length = 0
  · have hv : vs = [] := List.eq_nil_of_length_eq_zero hn
    subst hv
    have h0 : sl.len = 0#64 := by apply BitVec.eq_of_toNat_eq; simp [hlen]
    refine ⟨(), m, hP, ?_, hd, hm, hp, hst⟩
    simp [reverse, zig_unfold, h0]
  · let s₀ : reverseLocals := { ({ (default : reverseLocals) with i := 0#64 }) with j := sl.len - 1#64 }
    have hj0 : (sl.len - 1#64).toNat = vs.length - 1 := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp [hlen]
    have hinit : revInv sl.ptr vs s₀ hP := by
      refine ⟨vs, hp, rfl, ?_, ?_⟩
      · simp only [s₀, hj0]; simp; omega
      · intro k hk
        have : ¬ (k < (0#64 : BitVec 64).toNat ∨ vs.length - 1 < k) := by simp; omega
        simp only [s₀, hj0]; rw [ite_eq_right_of_eq_false _ _ (eq_false this)]
    obtain ⟨e, s', m', h', hr, hd', hm', ⟨he, hpost⟩, hst'⟩ :=
      loop_sep_spec (reverse.loop15 sl) reverse.again15 (revInv sl.ptr vs) revMeas
        (fun e _ h => e = .br14 ∧ arr sl.ptr vs.reverse h) hF
        (fun s m h hd hm hi hst => reverse_step sl vs hlen hF s m h hd hm hi hst)
        s₀ m hP hd hm hinit hst
    subst he
    refine ⟨(), m', h', ?_, hd', hm', hpost, hst'⟩
    have hne : ¬ sl.len = 0#64 := by
      intro h; apply hn; rw [← hlen, h]; rfl
    have hso : sl.len.usubOverflow 1#64 = false := by
      simp [BitVec.usubOverflow]; omega
    simp only [StateT.run] at hr
    simp [reverse, zig_unfold, hne, Zig.sub, hso, hr, s₀]
