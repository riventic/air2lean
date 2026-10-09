import ZigLean.Sep.Full.Triple

/-!
# Atomic points-to (prototype, `docs/sep-full-state.md`)

Rules for `atomic_load` and `atomic_store` of a 64-bit word that the precondition owns as `apts`
(`ZigLean/Sep/Full/Res.lean`), in a sequential run (choice `0`, the only option of one thread:
the newest message, a write at the end). The atomic layout is part of the owned bytes, so:

* the op cannot hit the mixed-size policy (`locIdx` cannot throw `.unspecified`): the bytes carry
  no location, or exactly the location `(p.off, 8)` (obstruction O3);
* the op changes the layout only of the owned bytes (a new location over them), so the frame's
  tags stay;
* in a sequential run the newest message has the block's bytes (`locIdx` adds a message when they
  differ), so the op reads and writes the owned bytes like a plain access.
-/

namespace Zig
namespace Full

open FAssn Conc Conc.Proto

/-! ## The layout after `locIdx` -/

/-- The bytes `o..o+len` of block `b` carry no location, or all the location `(o, len)`. -/
def TagOk (sh : List Shape) (b o len : Nat) : Prop :=
  (∀ x, o ≤ x → x < o + len → tagOf sh b x = none) ∨
  (∀ x, o ≤ x → x < o + len → tagOf sh b x = some (o, len))

theorem shape_mem {m : Mem} {i : Nat} (hi : i < m.atomics.size) :
    ALoc.shape m.atomics[i] ∈ shapes m := by
  unfold shapes
  exact List.mem_map.mpr ⟨m.atomics[i], Array.mem_toList_iff.mpr (Array.getElem_mem hi), rfl⟩

theorem shapes_set {a : Array ALoc} {i : Nat} {l : ALoc} (hi : i < a.size)
    (hs : ALoc.shape l = ALoc.shape a[i]) :
    (a.set! i l).toList.map ALoc.shape = a.toList.map ALoc.shape := by
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    simp only [List.getElem_map, Array.getElem_toList, Array.set!_eq_setIfInBounds]
    rw [Array.getElem_setIfInBounds (by simpa using h2)]
    split
    · subst_vars; exact hs
    · rfl

/-- A location overlapping the bytes `o..o+len` of block `b` (with `TagOk`) is `(b, o, len)`. -/
theorem overlap_eq {sh : List Shape} (hw : ShapesWF sh) {b o len : Nat} (hlen : 0 < len)
    (ht : TagOk sh b o len)
    {s : Shape} (hs : s ∈ sh) (hb : s.1 = b) (h1 : o < s.2.1 + s.2.2) (h2 : s.2.1 < o + len) :
    s.2.1 = o ∧ s.2.2 = len := by
  have hpos := hw.1 s hs
  obtain ⟨x, hx1, hx2, hc⟩ : ∃ x, o ≤ x ∧ x < o + len ∧ Covers b x s := by
    by_cases ho : o ≤ s.2.1
    · exact ⟨s.2.1, ho, h2, hb, Nat.le_refl _, by omega⟩
    · exact ⟨o, Nat.le_refl _, by omega, hb, by omega, h1⟩
  have e := tagOf_of_mem hw hs hc
  rcases ht with h | h
  · rw [h _ hx1 hx2] at e; cases e
  · rw [h _ hx1 hx2] at e
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    exact ⟨e.1.symm, e.2.symm⟩

theorem pos_of_back {M : Array Msg} {c : Array Byte} (h : (M.back?.map (·.bytes)).getD #[] = c)
    (hc : 0 < c.size) : 0 < M.size := by
  rcases hm : M.size with _ | n
  · have : M.back? = none := by rw [Array.back?_eq_none_iff]; exact Array.size_eq_zero_iff.mp hm
    rw [this] at h; rw [← h] at hc; simp at hc
  · omega

/-- `locIdx` at an existing location `i`: it keeps the shape, and its newest message has the
block's bytes. -/
theorem locIdx_found' {m m₁ : Mem} {b o len li i : Nat}
    (hi : m.atomics.findIdx? (fun l => l.block == b && l.off == o) = some i)
    (hlen : (m.atomics[i]!).len = len) (hcur : 0 < (curBytes m b o len).size)
    (h : ((locIdx b o len).run m).run = some (.ok (li, m₁))) :
    li = i ∧ ∃ (M : Array Msg) (next : Nat), 0 < M.size ∧
      (M.back?.map (·.bytes)).getD #[] = curBytes m b o len ∧
      m₁ = { m with atomics := m.atomics.set! i { m.atomics[i]! with msgs := M }, nextMsg := next } := by
  unfold locIdx at h
  obtain ⟨a₁, m', hg, h₁⟩ := MemM.bind_ok h
  obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
  simp only [hi] at h₁
  split at h₁
  · rename_i hne; simp [hlen] at hne
  · split at h₁
    · rename_i hc
      obtain ⟨_, m₂, hs, h₂⟩ := MemM.bind_ok h₁
      have := MemM.set_ok hs
      subst this
      obtain ⟨rfl, rfl⟩ := MemM.pure_ok h₂
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact ⟨rfl, _, _, pos_of_back hc.1 hcur, hc.1, rfl⟩
    · obtain ⟨_, m₂, hs, h₂⟩ := MemM.bind_ok h₁
      have := MemM.set_ok hs
      subst this
      obtain ⟨rfl, rfl⟩ := MemM.pure_ok h₂
      exact ⟨rfl, _, _, by simp, by simp [curBytes], rfl⟩

/-- What `locIdx` does at bytes with `TagOk` in a well-formed layout: only the atomics change;
location `li` is at `(b, o)`, its newest message has the block's bytes; the layout gets the
location `(b, o, len)` if it was not there and stays well formed. -/
theorem locIdx_post {m m₁ : Mem} {b o len li : Nat} (hw : ShapesWF (shapes m)) (hlen : 0 < len)
    (ht : TagOk (shapes m) b o len) (hcur : (curBytes m b o len).size = len)
    (h : ((locIdx b o len).run m).run = some (.ok (li, m₁))) :
    (∃ a next, m₁ = { m with atomics := a, nextMsg := next }) ∧
    li < m₁.atomics.size ∧ (m₁.atomics[li]!).block = b ∧ (m₁.atomics[li]!).off = o ∧
    0 < (m₁.atomics[li]!).msgs.size ∧ ALoc.lastBytes (m₁.atomics[li]!) = curBytes m b o len ∧
    ShapesWF (shapes m₁) ∧
    ∀ b' x, tagOf (shapes m₁) b' x =
      if Covers b' x (b, o, len) then some (o, len) else tagOf (shapes m) b' x := by
  have hupd := locIdx_updates h
  cases hi : m.atomics.findIdx? (fun l => l.block == b && l.off == o) with
  | some i =>
    obtain ⟨hlt, hp, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp hi
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    have hmem := shape_mem hlt
    obtain ⟨-, hl⟩ := overlap_eq hw hlen ht hmem hp.1 (by
        have := hw.1 _ hmem; simp only [ALoc.shape] at this ⊢; omega)
      (by simp only [ALoc.shape]; omega)
    simp only [ALoc.shape] at hl
    have hget : m.atomics[i]! = m.atomics[i] := getElem!_pos m.atomics i hlt
    obtain ⟨rfl, M, next, hpos, hback, hm₁⟩ :=
      locIdx_found' hi (by rw [hget]; exact hl) (by omega) h
    have hsz : m₁.atomics.size = m.atomics.size := by rw [hm₁]; simp
    have hat : m₁.atomics[li]! = { m.atomics[li]! with msgs := M } := by
      rw [hm₁]
      show (m.atomics.set! li _)[li]! = _
      rw [Array.set!_eq_setIfInBounds, getElem!_pos _ li (by simpa using hlt)]
      simp
    have hsh : shapes m₁ = shapes m := by
      rw [hm₁]; exact shapes_set hlt (by simp [ALoc.shape, hget])
    refine ⟨hupd, by simp only [hsz]; exact hlt, by rw [hat, hget]; exact hp.1,
      by rw [hat, hget]; exact hp.2, by rw [hat]; exact hpos, by rw [hat]; exact hback,
      by rw [hsh]; exact hw, fun b' x => ?_⟩
    rw [hsh]
    split
    · rename_i hc
      have := tagOf_of_mem hw hmem (b := b') (x := x) (by
        simp only [ALoc.shape, hp.1, hp.2, hl]; exact hc)
      simpa [ALoc.shape, hp.2, hl] using this
    · rfl
  | none =>
    obtain ⟨rfl, hm₁⟩ := locIdx_new hi h
    -- No location overlaps the bytes: one would be `(b, o, len)`, found by `findIdx?`.
    have hno : ∀ s ∈ shapes m, s.1 = b → o < s.2.1 + s.2.2 → s.2.1 < o + len → False := by
      intro s hs hb h1 h2
      obtain ⟨ho, -⟩ := overlap_eq hw hlen ht hs hb h1 h2
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hs
      obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hl)
      have := Array.findIdx?_eq_none_iff.mp hi m.atomics[j] (Array.getElem_mem hj)
      simp only [ALoc.shape] at hb ho
      simp [hb, ho] at this
    have hsh : shapes m₁ = shapes m ++ [(b, o, len)] := by
      rw [hm₁]; simp [shapes, ALoc.shape]
    have hat : m₁.atomics[m.atomics.size]! = firstLoc m b o len := by
      rw [hm₁]; simp [firstLoc, firstMsg]
    refine ⟨hupd, by rw [hm₁]; simp, by rw [hat]; rfl, by rw [hat]; rfl,
      by rw [hat]; simp [firstLoc], by rw [hat]; simp [ALoc.lastBytes, firstLoc, firstMsg], ?_,
      fun b' x => ?_⟩
    · rw [hsh]
      refine ⟨fun s hs => ?_, ?_⟩
      · rcases List.mem_append.mp hs with h | h
        · exact hw.1 s h
        · simp at h; subst h; exact hlen
      · rw [List.pairwise_append]
        refine ⟨hw.2, List.pairwise_singleton _ _, fun s hs t ht' hst => ?_⟩
        simp at ht'; subst ht'
        by_cases h1 : o < s.2.1 + s.2.2
        · by_cases h2 : s.2.1 < o + len
          · exact (hno s hs hst h1 h2).elim
          · right; simp only; omega
        · left; simp only; omega
    · rw [hsh, tagOf_append_single]
      split
      · rename_i hc
        have : tagOf (shapes m) b' x = none := tagOf_none.mpr fun s hs hcs => by
          obtain ⟨e1, e2, e3⟩ := hc
          obtain ⟨f1, f2, f3⟩ := hcs
          simp only at e1 e2 e3
          exact hno s hs (f1.trans e1.symm) (by omega) (by omega)
        rw [this]; rfl
      · simp

end Full
end Zig
