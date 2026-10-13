import ZigLean.Sep.Full.AutoAll
import Proofs.Slices.Gen

/-!
Two clients of whole-array ownership: the generated public bodies of
`examples/slices/slices.zig`, walked by `fsym` with the array rules of
`ZigLean/Sep/Full/Arr.lean` (`FTotalTriple.arr_load`, `FTotalTriple.arr_store`) and the pointer
formation rule (`ptrProject_elem_of`). No generated body is copied or hand-replaced. These are
sequential memory contracts; no new exporter/source correspondence qualification is claimed.
-/

namespace ProofTools.ArrayClients

open Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto

/-- The pointer-index reader `at` returns the selected item and keeps the array. -/
theorem at_array (p : Ptr) (xs : List (BitVec 32)) (i : BitVec 64)
    (hi : i.toNat < xs.length) :
    FTotalTriple (up (arr p xs)) (Slices.«at» p i)
      (fun v => ⟪v = xs[i.toNat]⟫ ⋆ up (arr p xs)) := by
  unfold Slices.«at»
  fsym

/-- The fixed-capacity byte update `bumpAt` increments the selected item modulo 256, stores it
through `&xs[i]` and returns item 3. -/
theorem bumpAt_array (p : Ptr) (xs : List (BitVec 8)) (i : BitVec 64)
    (hlen : xs.length = 4) (hi : i.toNat < xs.length) :
    FTotalTriple (up (arr p xs)) (Slices.bumpAt p i)
      (fun v => ⟪v = (xs.set i.toNat (Zig.addWrap xs[i.toNat] 1))[3]'(by simp only [List.length_set]; omega)⟫ ⋆
        up (arr p (xs.set i.toNat (Zig.addWrap xs[i.toNat] 1)))) := by
  unfold Slices.bumpAt
  fsym

/-- The two clients in sequence, on unrelated arrays: each call's frame is the other array. -/
example (p q : Ptr) (xs : List (BitVec 8)) (ys : List (BitVec 32)) (i j : BitVec 64)
    (hlen : xs.length = 4) (hi : i.toNat < xs.length) (hj : j.toNat < ys.length) :
    FTotalTriple (up (arr p xs) ⋆ up (arr q ys))
      (Slices.bumpAt p i >>= fun _ => Slices.«at» q j)
      (fun v => ⟪v = ys[j.toNat]⟫ ⋆ (up (arr q ys) ⋆
        up (arr p (xs.set i.toNat (Zig.addWrap xs[i.toNat] 1))))) := by
  fsym [bumpAt_array p xs i hlen hi, at_array q ys j hj]

end ProofTools.ArrayClients

/-- info: 'ProofTools.ArrayClients.bumpAt_array' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ProofTools.ArrayClients.bumpAt_array
