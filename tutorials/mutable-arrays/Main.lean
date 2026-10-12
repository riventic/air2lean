import Proofs.Slices.Sep

/-!
Mutable arrays: `reverse` of a `[]u32` slice, run twice, restores the items.

From the repository root:
  lake build Proofs.Slices.Sep
  lake env lean tutorials/mutable-arrays/Main.lean

See tutorials/mutable-arrays/README.md for the source, the exercise and the negative control.
-/

namespace MutableArrays

open Slices Zig Zig.Full FAssn

/-- Reversing a slice twice gives back its items: two `reverse_spec` triples, chained. -/
theorem reverse_twice (sl : Slice) (vs : List (BitVec 32)) (hlen : sl.len.toNat = vs.length) :
    FTotalTriple (up (arr sl.ptr vs)) (do reverse sl; reverse sl) (fun _ => up (arr sl.ptr vs)) := by
  have back := reverse_spec sl vs.reverse (by simp [hlen])
  rw [List.reverse_reverse] at back
  exact FTotalTriple.bind (reverse_spec sl vs hlen) (fun _ => back)

end MutableArrays
