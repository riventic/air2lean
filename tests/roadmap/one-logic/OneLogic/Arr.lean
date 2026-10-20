import ZigLean.Sep.Full.AutoAll

/-!
# Arrays in the full-state logic (`ZigLean/Sep/Full/Arr.lean`), library-only

`fsym` walks a read of item 1 and a write of item 0 of a `u32` array with the library's array
rules; the array stays whole. A split and a join are updates (`EUpd`) of the precondition.
-/

namespace OneLogic.Arr

open Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto

/-- `a[0] = a[1]`. -/
def copy10 (p : Ptr) : MemM Unit := do
  let v ← Zig.load (BitVec 32) 4 (p.elem 4 1)
  Zig.store 4 (p.elem 4 0) v

theorem copy10_spec (p : Ptr) (x y z : BitVec 32) :
    FTotalTriple (up (arr p [x, y, z])) (copy10 p) (fun _ => up (arr p [y, y, z])) := by
  unfold copy10
  fsym

/-- Split an array in two and join it again. -/
theorem split_join (p : Ptr) (xs : List (BitVec 32)) (k : Nat) (hk : k ≤ xs.length) :
    EUpd (up (arr p xs)) (up (arr p (xs.take k ++ xs.drop k))) :=
  EUpd.trans (EUpd.arr_split hk (by decide)) (by
    have := EUpd.arr_join (p := p) (xs := xs.take k) (ys := xs.drop k) (T := BitVec 32) (by decide)
    rwa [List.length_take, Nat.min_eq_left hk] at this)

end OneLogic.Arr
