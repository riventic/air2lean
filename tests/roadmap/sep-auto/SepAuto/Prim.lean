import ZigLean.Sep.Full.Auto
import ZigLean.Sep.Full.AutoPrim

/-!
# `fsym` on the primitive `Result` commands (`AutoRules.lean`, `AutoPrim.lean`)

One step rule per command, whatever the runtime-safety flag: unsigned `*` (`mul_step`, its
value as `r.toNat`, from which the closing solver also gets the word equation), signed `+`, `-`,
`*` (`add_signed_step`, `sub_signed_step`, `mul_signed_step`), an array item
(`index_step`), the payload and the error of an error union (`unwrapPayload_step`,
`unwrapErr_step`), and a caller's `Result` contract as a step rule (`result_step`). The rejected
attempts show that a step whose condition may fail (an overflow, an index past the end, an error
union that holds an error) is not taken.
-/

namespace SepAuto.Prim

open Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto

/-- A checked unsigned `*` that does not overflow: the product's value. -/
theorem mul_fits (P : FAssn) (a b : BitVec 16) (h : a.toNat * b.toNat < 2 ^ 16) :
    FTotalTriple P (StateT.lift (Zig.mul false a b) : MemM (BitVec 16))
      (fun r => ⟪r.toNat = a.toNat * b.toNat⟫ ⋆ P) := by
  fsym

/-- … plain (`safe := false`), and the word equation of the product follows from its value. -/
theorem mul_plain_eq (P : FAssn) (a b : BitVec 16) (h : a.toNat * b.toNat < 2 ^ 16) :
    FTotalTriple P (StateT.lift (Zig.mul false a b false) : MemM (BitVec 16))
      (fun r => ⟪r = a * b⟫ ⋆ P) := by
  fsym

/-- A narrowing `@intCast` in range, stated as a word equation. -/
theorem intCast_eq (P : FAssn) (a : BitVec 64) (h : a.toNat < 256) :
    FTotalTriple P (StateT.lift (Zig.intCast false false 8 a) : MemM (BitVec 8))
      (fun r => ⟪r = BitVec.ofInt 8 (Zig.val false a)⟫ ⋆ P) := by
  fsym

/-- Signed `+`, `-`, `*` without signed overflow, checked or plain. -/
theorem add_signed (P : FAssn) (a b : BitVec 32) (h : a.saddOverflow b = false) :
    FTotalTriple P (StateT.lift (Zig.add true a b) : MemM (BitVec 32)) (fun r => ⟪r = a + b⟫ ⋆ P) := by
  fsym

theorem sub_signed_plain (P : FAssn) (a b : BitVec 32) (h : a.ssubOverflow b = false) :
    FTotalTriple P (StateT.lift (Zig.sub true a b false) : MemM (BitVec 32))
      (fun r => ⟪r = a - b⟫ ⋆ P) := by
  fsym

theorem mul_signed (P : FAssn) (a b : BitVec 32) (h : a.smulOverflow b = false) :
    FTotalTriple P (StateT.lift (Zig.mul true a b) : MemM (BitVec 32)) (fun r => ⟪r = a * b⟫ ⋆ P) := by
  fsym

/-- An array item at an index below the size. -/
theorem index_lt (P : FAssn) (a : Array (BitVec 8)) (i : usize) (h : i.toNat < a.size) :
    FTotalTriple P (StateT.lift (Zig.index a i) : MemM (BitVec 8))
      (fun r => ⟪r = a[i.toNat]⟫ ⋆ P) := by
  fsym

/-- The payload and the error of an error union. -/
theorem unwrapPayload_ok (P : FAssn) (e : Except ErrName (BitVec 8)) (h : Zig.isNonErr e = true) :
    FTotalTriple P (StateT.lift (Zig.unwrapPayload e) : MemM (BitVec 8)) (fun r => ⟪e = .ok r⟫ ⋆ P) := by
  fsym

theorem unwrapErr_error (P : FAssn) (e : Except ErrName (BitVec 8)) (h : Zig.isErr e = true) :
    FTotalTriple P (StateT.lift (Zig.unwrapErr e) : MemM ErrName) (fun r => ⟪e = .error r⟫ ⋆ P) := by
  fsym

/-- A function of `Result` code with a proved contract, called from memory code. -/
@[irreducible] def succ (a : BitVec 8) : Result (BitVec 8) := Zig.add false a 1

theorem succ_contract (a : BitVec 8) :
    a.toNat < 255 → ∃ v, succ a = pure v ∧ v.toNat = a.toNat + 1 := fun h => by
  unfold succ
  exact ⟨a + 1, Auto.add_ok (by simp; omega), by rw [BitVec.toNat_add_of_lt (by simp; omega)]; simp⟩

/-- The contract as a step rule (`fsym [result_step c]`): its precondition is a side goal. -/
theorem succ_twice (P : FAssn) (a : BitVec 8) (h : a.toNat < 200) :
    FTotalTriple P (do
        let b ← (StateT.lift (succ a) : MemM (BitVec 8))
        StateT.lift (succ b))
      (fun r => ⟪r.toNat = a.toNat + 2⟫ ⋆ P) := by
  fsym [result_step (succ_contract _)]

set_option linter.unusedVariables false

/-- A signed `+` that may overflow: no step. -/
example (P : FAssn) (a b : BitVec 32) : True := by
  fail_if_success
    have : FTotalTriple P (StateT.lift (Zig.add true a b) : MemM (BitVec 32))
        (fun r => ⟪r = a + b⟫ ⋆ P) := by
      fsym
  trivial

/-- An index that may be past the end: no step. -/
example (P : FAssn) (a : Array (BitVec 8)) (i : usize) (h : i.toNat ≤ a.size) : True := by
  fail_if_success
    have : FTotalTriple P (StateT.lift (Zig.index a i) : MemM (BitVec 8))
        (fun r => ⟪r = a.getD i.toNat 0⟫ ⋆ P) := by
      fsym
  trivial

/-- An error union that may hold an error has no payload step. -/
example (P : FAssn) (e : Except ErrName (BitVec 8)) : True := by
  fail_if_success
    have : FTotalTriple P (StateT.lift (Zig.unwrapPayload e) : MemM (BitVec 8))
        (fun r => ⟪e = .ok r⟫ ⋆ P) := by
      fsym
  trivial

/-- A product that may overflow: no step. -/
example (P : FAssn) (a b : BitVec 16) : True := by
  fail_if_success
    have : FTotalTriple P (StateT.lift (Zig.mul false a b) : MemM (BitVec 16))
        (fun r => ⟪r.toNat = a.toNat * b.toNat⟫ ⋆ P) := by
      fsym
  trivial

end SepAuto.Prim
