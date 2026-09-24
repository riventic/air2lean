import Proofs.Options.Gen

/-!
# Proofs about `examples/options/options.zig`

`find` returns the first index of `x` in `xs`, or `none`. `findOr` defaults to `xs.size` when
absent. `firstIndexPlusOne` panics when `x` is absent.
-/

open Options

theorem find_loop_step (xs : Array (BitVec 32)) (x : BitVec 32) (hs : xs.size < 2 ^ 64)
    (s : findLocals) (hle : s.local2.toNat ≤ xs.size)
    (hnf : ∀ j < s.local2.toNat, xs[j]! ≠ x) :
    ∃ e s', (find.loop7 xs x (Zig.len xs)).run s = pure (e, s') ∧
      (if find.again7 e then
          (s'.local2.toNat ≤ xs.size ∧ ∀ j < s'.local2.toNat, xs[j]! ≠ x) ∧
            xs.size - s'.local2.toNat < xs.size - s.local2.toNat
        else (∃ i, e = .ret (some i) ∧ i.toNat < xs.size ∧ xs[i.toNat]! = x ∧
                ∀ j < i.toNat, xs[j]! ≠ x) ∨
             (e = .br6 ∧ ∀ j < xs.size, xs[j]! ≠ x)) := by
  unfold find.loop7
  have hm : xs.size % 18446744073709551616 = xs.size := Nat.mod_eq_of_lt (by omega)
  by_cases hlt : s.local2.toNat < xs.size
  · have hget : xs[s.local2.toNat]! = xs[s.local2.toNat] := getElem!_pos xs s.local2.toNat hlt
    by_cases heq : xs[s.local2.toNat]! = x
    · have heq' : xs[s.local2.toNat] = x := by rw [← hget]; exact heq
      refine ⟨.ret (some s.local2), s, ?_, ?_⟩
      · simp [zig_unfold, Zig.len, Zig.index, hlt, hm, heq']
      · simp only [find.again7, Bool.false_eq_true, ↓reduceIte]
        exact Or.inl ⟨s.local2, rfl, hlt, heq, hnf⟩
    · have hne' : xs[s.local2.toNat] ≠ x := by rw [← hget]; exact heq
      have hinc : ¬ 18446744073709551615 ≤ s.local2.toNat := by omega
      refine ⟨.rep7, { local2 := s.local2 + 1 }, ?_, ?_⟩
      · simp [zig_unfold, Zig.len, Zig.index, hlt, hm, hne', hinc]
      · have h2 : (s.local2 + 1).toNat = s.local2.toNat + 1 := by
          rw [BitVec.toNat_add]; simp [zig_unfold]; omega
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [h2]; omega
        · rw [h2]
          intro j hj
          by_cases hjc : j < s.local2.toNat
          · exact hnf j hjc
          · have hje : j = s.local2.toNat := by omega
            subst hje
            exact heq
        · rw [h2]; omega
  · have heqsize : s.local2.toNat = xs.size := by omega
    refine ⟨.br6, s, ?_, ?_⟩
    · simp [zig_unfold, Zig.len, Zig.index, hlt, hm]
    · simp only [find.again7, Bool.false_eq_true, ↓reduceIte]
      refine Or.inr ⟨?_, ?_⟩
      · trivial
      · rw [← heqsize]
        exact hnf

/-- `find` never panics for fewer than `2 ^ 64` elements, and returns the first index of `x`
in `xs`, or `none` iff `x` is absent. -/
theorem find_spec (xs : Array (BitVec 32)) (x : BitVec 32) (hs : xs.size < 2 ^ 64) :
    ∃ r, find xs x = pure r ∧
      (∀ i, r = some i → i.toNat < xs.size ∧ xs[i.toNat]! = x ∧ ∀ j < i.toNat, xs[j]! ≠ x) ∧
      (r = none → ∀ j < xs.size, xs[j]! ≠ x) := by
  obtain ⟨⟨e, s'⟩, hrun, hpost⟩ := Zig.loop_spec (find.loop7 xs x (Zig.len xs))
    find.again7
    (fun s => s.local2.toNat ≤ xs.size ∧ ∀ j < s.local2.toNat, xs[j]! ≠ x)
    (fun s => xs.size - s.local2.toNat)
    (fun r => (∃ i, r.1 = .ret (some i) ∧ i.toNat < xs.size ∧ xs[i.toNat]! = x ∧
                 ∀ j < i.toNat, xs[j]! ≠ x) ∨
               (r.1 = .br6 ∧ ∀ j < xs.size, xs[j]! ≠ x))
    (fun s hs' => find_loop_step xs x hs s hs'.1 hs'.2)
    { local2 := 0 } (by simp)
  rcases hpost with ⟨i, hei, hib, hxi, hnf⟩ | ⟨hebr6, hnfall⟩
  · subst hei
    refine ⟨some i, ?_, ?_, ?_⟩
    · unfold find
      change Zig.loop (find.loop7 xs x (Zig.len xs)) find.again7 { local2 := 0 }
        = some (Except.ok (findExit.ret (some i), s')) at hrun
      simp only [zig_unfold]
      rw [hrun]
      simp [zig_unfold]
    · intro i2 hi2
      have hi : i = i2 := by injection hi2
      subst hi
      exact ⟨hib, hxi, hnf⟩
    · simp
  · subst hebr6
    refine ⟨none, ?_, ?_, ?_⟩
    · unfold find
      change Zig.loop (find.loop7 xs x (Zig.len xs)) find.again7 { local2 := 0 }
        = some (Except.ok (findExit.br6, s')) at hrun
      simp only [zig_unfold]
      rw [hrun]
      simp [zig_unfold]
    · simp
    · intro _
      exact hnfall

/-- `findOr` matches `find`, defaulting to `xs.size` when `x` is absent. -/
theorem findOr_spec (xs : Array (BitVec 32)) (x : BitVec 32) (hs : xs.size < 2 ^ 64) :
    ∃ r, find xs x = pure r ∧
      findOr xs x = pure (match r with | some i => i | none => BitVec.ofNat 64 xs.size) := by
  obtain ⟨r, hr, -, -⟩ := find_spec xs x hs
  refine ⟨r, hr, ?_⟩
  unfold findOr
  simp only [zig_unfold]
  rw [hr]
  cases r with
  | some i => simp [zig_unfold, Zig.optPayload]
  | none => simp [zig_unfold, Zig.len]

/-- `firstIndexPlusOne` panics (`.?` on `null`: `unwrapNull`) when `x` is absent from `xs`. -/
theorem firstIndexPlusOne_absent (xs : Array (BitVec 32)) (x : BitVec 32)
    (hs : xs.size < 2 ^ 64) (h : ∀ j < xs.size, xs[j]! ≠ x) :
    firstIndexPlusOne xs x = throw .panic := by
  obtain ⟨r, hr, hsome, -⟩ := find_spec xs x hs
  have hrn : r = none := by
    cases r with
    | none => rfl
    | some i =>
      exfalso
      obtain ⟨hib, hxi, -⟩ := hsome i rfl
      exact h i.toNat hib hxi
  subst hrn
  unfold firstIndexPlusOne
  simp only [zig_unfold]
  rw [hr]
  simp [zig_unfold]
