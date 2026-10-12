import Proofs.Slices.Sep

/-! Negative control: Lean must reject this file. Two reversals do not leave the items
reversed, so the proof of `reverse_twice` cannot establish the changed postcondition. -/
-- expect-error: Type mismatch

namespace MutableArrays

open Slices Zig Zig.Full FAssn

theorem reverse_twice_wrong (sl : Slice) (vs : List (BitVec 32))
    (hlen : sl.len.toNat = vs.length) :
    FTotalTriple (up (arr sl.ptr vs)) (do reverse sl; reverse sl)
      (fun _ => up (arr sl.ptr vs.reverse)) := by
  have back := reverse_spec sl vs.reverse (by simp [hlen])
  rw [List.reverse_reverse] at back
  exact FTotalTriple.bind (reverse_spec sl vs hlen) (fun _ => back)

end MutableArrays
