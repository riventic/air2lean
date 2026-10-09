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

theorem shapes_set {m : Mem} {i : Nat} {l : ALoc} (hi : i < m.atomics.size)
    (hs : ALoc.shape l = ALoc.shape m.atomics[i]) :
    (m.atomics.set! i l).toList.map ALoc.shape = shapes m := by
  unfold shapes
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    simp only [List.getElem_map, Array.getElem_toList, Array.set!_eq_setIfInBounds]
    rw [Array.getElem_setIfInBounds (by simpa using h2)]
    split
    · subst_vars; exact hs
    · rfl

theorem shapes_push {m : Mem} {l : ALoc} :
    (m.atomics.push l).toList.map ALoc.shape = shapes m ++ [ALoc.shape l] := by
  simp [shapes]

/-- A location overlapping the bytes `o..o+len` of block `b` (with `TagOk`) is `(b, o, len)`. -/
theorem overlap_eq {sh : List Shape} (hw : ShapesWF sh) {b o len : Nat} (ht : TagOk sh b o len)
    {s : Shape} (hs : s ∈ sh) (hb : s.1 = b) (h1 : o < s.2.1 + s.2.2) (h2 : s.2.1 < o + len) :
    s.2.1 = o ∧ s.2.2 = len := by
  have hpos := hw.1 s hs
  have hc : Covers b (Nat.max o s.2.1) s := ⟨hb, Nat.le_max_right _ _, by omega⟩
  have e := tagOf_of_mem hw hs hc
  rcases ht with h | h
  · rw [h _ (Nat.le_max_left _ _) (by omega)] at e; cases e
  · rw [h _ (Nat.le_max_left _ _) (by omega)] at e
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    exact ⟨e.1.symm, e.2.symm⟩

/-- What `locIdx` does at bytes with `TagOk` in a well-formed layout: blocks unchanged; the
location `li` is at `(b, o)`, its newest message has the block's bytes; the layout gets the
location `(b, o, len)` (if it was not there) and stays well formed. -/
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
  unfold locIdx at h
  obtain ⟨a₁, m', hg, h₁⟩ := MemM.bind_ok h
  obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
  cases hi : a₁.atomics.findIdx? (fun l => l.block == b && l.off == o) with
  | some i =>
    obtain ⟨hlt, hp, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp hi
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    have hmem := shape_mem hlt
    obtain ⟨-, hl⟩ := overlap_eq hw ht hmem hp.1 (by
        have := hw.1 _ hmem; simp only [ALoc.shape] at this ⊢; omega)
      (by simp only [ALoc.shape]; omega)
    simp only [ALoc.shape] at hl
    have hget : a₁.atomics[i]! = a₁.atomics[i] := getElem!_pos a₁.atomics i hlt
    simp only [hi, hget, hl, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h₁
    -- Both branches: the location at `i` keeps its shape, its newest message is `cur`.
    have hcur' : curBytes a₁ b o len =
        ((a₁.blocks[b]?.map (·.bytes)).getD #[]).extract o (o + len) := rfl
    have key : ∀ (msgs : Array Msg) (next : Nat), 0 < msgs.size →
        (msgs.back?.map (·.bytes)).getD #[] = curBytes a₁ b o len →
        ((set ({ a₁ with atomics := a₁.atomics.set! i { a₁.atomics[i] with msgs }, nextMsg := next }
          : Mem) >>= fun _ => (pure i : MemM Nat)).run a₁).run = some (.ok (li, m₁)) → _ := by
      intro msgs next hpos hback hrun
      obtain ⟨_, m₂, hs, h₂⟩ := MemM.bind_ok hrun
      have := MemM.set_ok hs
      subst this
      obtain ⟨rfl, rfl⟩ := MemM.pure_ok h₂
      have hsz : (a₁.atomics.set! i { a₁.atomics[i] with msgs }).size = a₁.atomics.size := by simp
      have hat : (a₁.atomics.set! i { a₁.atomics[i] with msgs })[i]! = { a₁.atomics[i] with msgs } := by
        rw [Array.set!_eq_setIfInBounds, getElem!_pos _ i (by simpa using hlt)]
        simp
      have hsh : shapes { a₁ with atomics := a₁.atomics.set! i { a₁.atomics[i] with msgs },
          nextMsg := next } = shapes a₁ := shapes_set hlt rfl
      refine ⟨⟨_, _, rfl⟩, by rw [hsz]; exact hlt, by rw [hat]; exact hp.1, by rw [hat]; exact hp.2,
        by rw [hat]; exact hpos, by rw [hat]; exact hback, by rw [hsh]; exact hw, fun b' x => ?_⟩
      rw [hsh]
      split
      · rename_i hc
        have := tagOf_of_mem hw hmem (b := b') (x := x) (by
          simp only [ALoc.shape, hp.1, hp.2, hl]; exact hc)
        simpa [ALoc.shape, hp.2, hl] using this
      · rfl
    sorry
  | none => sorry

end Full
end Zig
