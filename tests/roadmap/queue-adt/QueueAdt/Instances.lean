import QueueAdt.Ring
import QueueAdt.Shift
import QueueAdt.Clients

/-!
# The clients on the ring buffer and on the shifting array (P04, P06)

The client theorems of `QueueAdt/Clients.lean`, each proved once for every queue contract over
the generated operations, at the instances `ringQueue` (`QueueAdt/Ring.lean`) and `shiftQueue`
(`QueueAdt/Shift.lean`): the statements about the generated program with its own representation
predicate. Nothing is proved again here; the step counts are the declared ones (`rotateSteps`).
-/

namespace QueueAdt
open Zig Zig.Full Zig.Full.FAssn

/-- `rotate` on the ring buffer moves the front item to the back. -/
theorem ring_rotate (q : Ptr) (C : Nat) (xs : List (BitVec 32)) :
    FTotalTriple (ring q C xs) (rotate q) (fun _ => Rotated ringQueue q C xs) := by
  have hs := rotate_spec ringQueue q C xs
  rw [show rotateSteps ringQueue C xs = 0 by cases xs <;> rfl] at hs
  exact FTotalTriple.credits_zero_iff.mp hs

/-- **`pushAll` on the ring buffer, under the capacity premise** `xs.length + ys.length ≤ C`:
every item is pushed, for `ys.length + 1` credits and as many receipts. -/
theorem ring_pushAll_exact (q : Ptr) (C : Nat) (xs ys : List (BitVec 32)) (vs : Slice)
    (hlen : vs.len.toNat = ys.length) (hroom : xs.length + ys.length ≤ C) :
    FTotalTriple ((ring q C xs ⋆ up (arr vs.ptr ys)) ⋆ credits (ys.length + 1)) (pushAll q vs)
      (fun r => (⟪r = vs.len⟫ ⋆ (ring q C (xs ++ ys) ⋆ up (arr vs.ptr ys))) ⋆
        spent (ys.length + 1)) :=
  pushAll_exact ringQueue q C xs ys vs (fun _ _ _ => rfl) hlen hroom

/-- `pushAll` on the ring buffer cannot be paid with `ys.length` credits. -/
theorem ring_pushAll_not_within (q : Ptr) (C : Nat) (xs ys : List (BitVec 32)) (vs : Slice)
    (hlen : vs.len.toNat = ys.length) (hroom : xs.length + ys.length ≤ C) {m : Mem} {r rF : Res}
    (hh : Holds m r rF) (hl : (ring q C xs ⋆ up (arr vs.ptr ys)) r) (hseq : m.FSeq)
    (hc : CreditFree r rF) (Q : BitVec 64 → FAssn) :
    ¬ FTotalTriple ((ring q C xs ⋆ up (arr vs.ptr ys)) ⋆ credits ys.length) (pushAll q vs) Q :=
  pushAll_not_within ringQueue q C xs ys vs (fun _ _ _ => rfl) hlen hroom hh hl hseq hc Q

/-- A rotation of the shifting array runs one step per item: the moves of its `pop`. -/
theorem shift_rotateSteps (C : Nat) (xs : List (BitVec 16)) :
    rotateSteps shiftQueue C xs = xs.length := by
  cases xs <;> rfl

/-- **`rotateShift` on the shifting array** moves the front item to the back in exactly
`xs.length` steps. -/
theorem shift_rotate (q : Ptr) (C : Nat) (xs : List (BitVec 16)) :
    FTotalTriple (shift q C xs ⋆ credits xs.length) (rotateShift q)
      (fun _ => Rotated shiftQueue q C xs ⋆ spent xs.length) := by
  have hs := rotateShift_spec shiftQueue q C xs
  rw [shift_rotateSteps] at hs
  exact hs

end QueueAdt
