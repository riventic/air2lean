import Proofs.Slices.Sep

/-! Exercise solution: reversing a one-item slice leaves it unchanged. -/

namespace MutableArrays

open Slices Zig Zig.Full FAssn

theorem reverse_one (sl : Slice) (x : BitVec 32) (hlen : sl.len.toNat = 1) :
    FTotalTriple (up (arr sl.ptr [x])) (reverse sl) (fun _ => up (arr sl.ptr [x])) := by
  simpa using reverse_spec sl [x] hlen

end MutableArrays
