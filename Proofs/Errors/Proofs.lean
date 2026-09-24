import Proofs.Errors.Gen

/-!
# Proofs about `examples/errors/errors.zig`

`isDigit c` is the ASCII-digit range check; `digitSum s k` is the sum of the digit values of
the first `k` elements of `s`, as a natural number (prefix sum like `psum` in
`Proofs/Basic/Common.lean`).
-/

open Errors

/-- ASCII digit predicate on a byte, as a `Nat` range check. -/
abbrev isDigit (c : BitVec 8) : Prop := 48 ≤ c.toNat ∧ c.toNat ≤ 57

/-- Sum of the digit values of the first `k` elements, as a natural number. Only meaningful
where every one of those elements satisfies `isDigit` (elsewhere the subtraction truncates). -/
def digitSum (s : Array (BitVec 8)) (k : Nat) : Nat :=
  ((s.toList.take k).map (fun c => c.toNat - 48)).sum

theorem digitSum_succ (s : Array (BitVec 8)) (k : Nat) (hk : k < s.size) :
    digitSum s (k + 1) = digitSum s k + (s[k].toNat - 48) := by
  unfold digitSum
  rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using hk)]
  simp

theorem digitSum_le (s : Array (BitVec 8)) (k : Nat) (hk : k ≤ s.size)
    (h : ∀ i < k, isDigit s[i]!) : digitSum s k ≤ k * 9 := by
  induction k with
  | zero => simp [digitSum]
  | succ n ih =>
    have hn : n < s.size := by omega
    have hih := ih (by omega) (fun i hi => h i (by omega))
    have hd : isDigit s[n]! := h n (by omega)
    rw [getElem!_pos s n hn] at hd
    rw [digitSum_succ s n hn]
    omega

/-- `parseDigit` never panics: it returns the digit value on `'0'..'9'`, else `error.NotDigit`. -/
theorem parseDigit_spec (c : BitVec 8) :
    parseDigit c = pure (if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then
        (.ok (c - 48) : Except Zig.ErrName (BitVec 8)) else .error "NotDigit") := by
  unfold parseDigit
  by_cases hlo : c.toNat < 48
  · have hnd : ¬ (48 ≤ c.toNat ∧ c.toNat ≤ 57) := by omega
    simp [zig_unfold, hlo, hnd]
  · by_cases hhi : 57 < c.toNat
    · have hnd : ¬ (48 ≤ c.toNat ∧ c.toNat ≤ 57) := by omega
      simp [zig_unfold, hlo, hhi, hnd]
    · have hd : 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by omega
      simp [zig_unfold, hlo, hhi, hd]

/-- `digitOrZero` (`parseDigit` with `catch 0`) never panics. -/
theorem digitOrZero_spec (c : BitVec 8) :
    digitOrZero c = pure (if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then c - 48 else 0) := by
  unfold digitOrZero
  rw [parseDigit_spec]
  by_cases hd : 48 ≤ c.toNat ∧ c.toNat ≤ 57
  · simp [zig_unfold, hd, Zig.isNonErr, Zig.isErr, Zig.unwrapPayload]
  · simp [zig_unfold, hd, Zig.isNonErr, Zig.isErr, Zig.unwrapErr]

theorem sumDigits_loop_step (s : Array (BitVec 8)) (hs : s.size * 9 < 2 ^ 32)
    (l : sumDigitsLocals) (hk : l.local5.toNat ≤ s.size)
    (hall : ∀ i < l.local5.toNat, isDigit s[i]!)
    (ht : l.total.toNat = digitSum s l.local5.toNat) :
    ∃ e l', (sumDigits.loop10 s (Zig.len s)).run l = pure (e, l') ∧
      (if sumDigits.again10 e then
          (l'.local5.toNat ≤ s.size ∧ (∀ i < l'.local5.toNat, isDigit s[i]!) ∧
            l'.total.toNat = digitSum s l'.local5.toNat) ∧
            s.size - l'.local5.toNat < s.size - l.local5.toNat
        else (e = .br9 ∧ l'.total.toNat = digitSum s s.size ∧ ∀ i < s.size, isDigit s[i]!) ∨
             (e = .ret (.error "NotDigit") ∧ ¬ ∀ i < s.size, isDigit s[i]!)) := by
  unfold sumDigits.loop10
  have hm : s.size % 18446744073709551616 = s.size := Nat.mod_eq_of_lt (by omega)
  by_cases hlt : l.local5.toNat < s.size
  · have hji : s[l.local5.toNat]! = s[l.local5.toNat] := getElem!_pos s l.local5.toNat hlt
    by_cases hd : isDigit s[l.local5.toNat]
    · obtain ⟨hd1, hd2⟩ := hd
      have hpd : parseDigit s[l.local5.toNat] =
          pure (.ok (s[l.local5.toNat] - 48) : Except Zig.ErrName (BitVec 8)) := by
        rw [parseDigit_spec]; simp [hd1, hd2]
      have hov : ¬ BitVec.usubOverflow s[l.local5.toNat] (48 : BitVec 8) := by
        simp [BitVec.usubOverflow]; omega
      have hv : (s[l.local5.toNat] - 48).toNat = s[l.local5.toNat].toNat - 48 :=
        BitVec.toNat_sub_of_not_usubOverflow hov
      have hw : ((s[l.local5.toNat] - 48).setWidth 32).toNat = s[l.local5.toNat].toNat - 48 := by
        rw [BitVec.toNat_setWidth, hv]
        have := s[l.local5.toNat].isLt
        omega
      have hsum : digitSum s (l.local5.toNat + 1) =
          digitSum s l.local5.toNat + (s[l.local5.toNat].toNat - 48) :=
        digitSum_succ s l.local5.toNat hlt
      have hallsucc : ∀ i < l.local5.toNat + 1, isDigit s[i]! := by
        intro i hi
        by_cases hi' : i < l.local5.toNat
        · exact hall i hi'
        · have hie : i = l.local5.toNat := by omega
          subst hie; rw [hji]; exact ⟨hd1, hd2⟩
      have hple : digitSum s (l.local5.toNat + 1) ≤ (l.local5.toNat + 1) * 9 :=
        digitSum_le s (l.local5.toNat + 1) (by omega) hallsucc
      have hinc : ¬ 18446744073709551615 ≤ l.local5.toNat := by omega
      have hc1 : ¬ (4294967296 ≤
          l.total.toNat + (208 + s[l.local5.toNat].toNat) % 256 % 4294967296) := by omega
      refine ⟨.rep10,
        { total := l.total + (s[l.local5.toNat] - 48).setWidth 32, local5 := l.local5 + 1 },
        ?_, ?_⟩
      · simp [zig_unfold, Zig.len, Zig.index, hlt, hm, hpd, StateT.lift, hc1, hinc]
      · have h5 : (l.local5 + 1).toNat = l.local5.toNat + 1 := by
          rw [BitVec.toNat_add]; simp [zig_unfold]; omega
        have htot2 : (l.total + (s[l.local5.toNat] - 48).setWidth 32).toNat
            = l.total.toNat + ((s[l.local5.toNat] - 48).setWidth 32).toNat := by
          rw [BitVec.toNat_add]; omega
        refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
        · rw [h5]; omega
        · rw [h5]; exact hallsucc
        · rw [h5, htot2, hw, ht, hsum]
        · rw [h5]; omega
    · have hnd : ¬ (48 ≤ s[l.local5.toNat].toNat ∧ s[l.local5.toNat].toNat ≤ 57) := hd
      have hpd : parseDigit s[l.local5.toNat] =
          pure (.error "NotDigit" : Except Zig.ErrName (BitVec 8)) := by
        rw [parseDigit_spec]; simp [hnd]
      have hallnot : ¬ ∀ i < s.size, isDigit s[i]! := by
        intro hall'
        have hbad := hall' l.local5.toNat hlt
        rw [hji] at hbad
        exact hnd hbad
      refine ⟨.ret (.error "NotDigit"), l, ?_, ?_⟩
      · simp [zig_unfold, Zig.len, Zig.index, hlt, hm, hpd, Zig.unwrapErr]
      · exact Or.inr ⟨rfl, hallnot⟩
  · have heq : l.local5.toNat = s.size := by omega
    refine ⟨.br9, l, ?_, ?_⟩
    · simp [zig_unfold, Zig.len, Zig.index, hlt, hm]
    · refine Or.inl ⟨rfl, ?_, ?_⟩
      · rw [← heq]; exact ht
      · rw [← heq]; exact hall

/-- `sumDigits` never panics: it returns the digit sum when every byte is a digit, and
`error.NotDigit` on the first non-digit byte. -/
theorem sumDigits_spec (s : Array (BitVec 8)) (hs : s.size * 9 < 2 ^ 32) :
    sumDigits s = pure (if ∀ i < s.size, isDigit s[i]! then
        (.ok (BitVec.ofNat 32 (digitSum s s.size)) : Except Zig.ErrName (BitVec 32))
      else .error "NotDigit") := by
  obtain ⟨⟨e, l'⟩, hrun, hpost⟩ := Zig.loop_spec (sumDigits.loop10 s (Zig.len s))
    sumDigits.again10
    (fun l => l.local5.toNat ≤ s.size ∧ (∀ i < l.local5.toNat, isDigit s[i]!) ∧
      l.total.toNat = digitSum s l.local5.toNat)
    (fun l => s.size - l.local5.toNat)
    (fun r => (r.1 = .br9 ∧ r.2.total.toNat = digitSum s s.size ∧ ∀ i < s.size, isDigit s[i]!) ∨
              (r.1 = .ret (.error "NotDigit") ∧ ¬ ∀ i < s.size, isDigit s[i]!))
    (fun l hl => sumDigits_loop_step s hs l hl.1 hl.2.1 hl.2.2)
    { total := 0, local5 := 0 } (by simp [digitSum])
  unfold sumDigits
  simp only [StateT.run', bind, pure, StateT.bind, StateT.pure,
    ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont, ExceptT.map, Functor.map,
    modify, modifyGet, MonadState.modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, Option.bind]
  rcases hpost with ⟨he1, he2, hall⟩ | ⟨he1, hall⟩
  · subst he1
    have hlebound : digitSum s s.size < 2 ^ 32 := by
      have hle := digitSum_le s s.size (Nat.le_refl _) hall
      omega
    have htot : l'.total = BitVec.ofNat 32 (digitSum s s.size) := by
      apply BitVec.eq_of_toNat_eq
      rw [he2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlebound]
    have hchange : Zig.loop (sumDigits.loop10 s (Zig.len s)) sumDigits.again10
        { total := 0, local5 := 0 } = some (Except.ok (sumDigitsExit.br9, l')) := hrun
    rw [ite_eq_left hall, hchange]
    simp [zig_unfold, htot]
  · subst he1
    have hchange : Zig.loop (sumDigits.loop10 s (Zig.len s)) sumDigits.again10
        { total := 0, local5 := 0 } =
          some (Except.ok (sumDigitsExit.ret (.error "NotDigit"), l')) := hrun
    rw [ite_eq_right hall, hchange]
    simp [zig_unfold]
