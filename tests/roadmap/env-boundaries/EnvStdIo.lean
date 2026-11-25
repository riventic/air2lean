import ZigLean.Env.Linux

/-!
# E03: lemmas shared by the proofs about translated std I/O

Facts about the runtime terms that the std I/O translations of every Zig version use (casts of
the `read` count, the `min` cap, the step tick) and about boundary event logs. `StdIo.lean`
(0.15.2) and `ReadClose/<EnvStd16|EnvStd17>.lean` (0.16.0, 0.17.1) import this module;
`check.sh` compiles it.
-/

namespace EnvStdIo
open Zig Zig.Env

-- The casts hold for both AIR forms (`intcast_safe` and the plain `intcast`, `safe := false`):
-- `safe` decides only the error of a value out of range.
theorem intCast31 (k : Nat) (hk : k < 2 ^ 31) : ∀ {safe : Bool},
    Zig.intCast false false 31 (BitVec.ofNat 64 k) safe = pure (BitVec.ofNat 31 k) := by
  intro safe
  have h64 : (BitVec.ofNat 64 k).toNat = k := by simp; omega
  simp only [Zig.intCast, Zig.val, Bool.false_eq_true, ite_false, Zig.intLo_unsigned, Zig.intHi_unsigned, h64]
  rw [if_pos (by omega)]
  congr 1
  all_goals apply BitVec.eq_of_toNat_eq
  all_goals simp [BitVec.toNat_ofInt]
  all_goals omega

theorem setWidth31 (k : Nat) (hk : k < 2 ^ 31) :
    BitVec.setWidth 64 (BitVec.ofNat 31 k) = BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  simp <;> omega

theorem intCast64of31 (k : Nat) (hk : k < 2 ^ 31) : ∀ {safe : Bool},
    Zig.intCast false false 64 (BitVec.ofNat 31 k) safe = pure (BitVec.ofNat 64 k) := by
  intro safe
  have h31 : (BitVec.ofNat 31 k).toNat = k := by simp; omega
  simp only [Zig.intCast, Zig.val, Bool.false_eq_true, ite_false, Zig.intLo_unsigned, Zig.intHi_unsigned, h31]
  rw [if_pos (by omega)]
  congr 1
  all_goals apply BitVec.eq_of_toNat_eq
  all_goals simp [BitVec.toNat_ofInt]
  all_goals omega

theorem intCast64 (a : BitVec 64) {safe : Bool} : Zig.intCast false false 64 a safe = pure a := by
  simp only [Zig.intCast, Zig.val, Bool.false_eq_true, ite_false, Zig.intLo_unsigned, Zig.intHi_unsigned]
  rw [if_pos (by have := a.isLt; omega)]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofInt]

theorem min_cap (len : BitVec 64) :
    Zig.min false 2147479552#64 len = BitVec.ofNat 64 (min 2147479552 len.toNat) := by
  unfold Zig.min
  simp only [Bool.false_eq_true, ite_false]
  apply BitVec.eq_of_toNat_eq
  by_cases h : 2147479552 ≤ len.toNat
  · rw [if_pos (by simp [BitVec.ule]; omega)]; simp; omega
  · rw [if_neg (by simp [BitVec.ule]; omega)]; simp; omega

theorem add_ofNat (i n : Nat) (h : i + n < 2 ^ 64) :
    Zig.add false (BitVec.ofNat 64 i) (BitVec.ofNat 64 n) = pure (BitVec.ofNat 64 (i + n)) := by
  have : ¬ (BitVec.ofNat 64 i).uaddOverflow (BitVec.ofNat 64 n) := by
    simp [BitVec.uaddOverflow]; omega
  simp only [Zig.add, Bool.false_eq_true, ite_false, this]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp

/-- A loop body's step tick (`Zig.tick`) in the unfolded `StateT.run` form: it counts and does
nothing else. -/
theorem tick_apply (m : Mem) : Zig.tick m = some (.ok ((), { m with ticks := m.ticks + 1 })) := rfl

/-- Every event is a write to `h`. -/
def OnlyWrites (h : Handle) (evs : List Event) : Prop := ∀ ev ∈ evs, ∃ c, ev = .wrote h c

theorem OnlyWrites.append {h : Handle} {a b : List Event} (ha : OnlyWrites h a)
    (hb : OnlyWrites h b) : OnlyWrites h (a ++ b) := by
  intro ev hev
  rcases List.mem_append.mp hev with hev | hev
  · exact ha ev hev
  · exact hb ev hev

theorem written_append (a b : List Event) : written (a ++ b) = written a ++ written b := by
  induction a with
  | nil => rfl
  | cons ev rest ih => cases ev <;> simp [written, ih]

theorem OnlyWrites.not_closed {h : Handle} {evs : List Event} (hw : OnlyWrites h evs) :
    Event.closed h ∉ evs := by
  intro hm
  obtain ⟨_, hc⟩ := hw _ hm
  cases hc

end EnvStdIo
