import LangLongTail.VectorCasts
import ZigLean.VecCast

/-!
# L09: Zig ≤0.16 `@bitCast` with a vector side, on the retained translation

`LangLongTail.VectorCasts` is the translation of `air/vector_casts/0.16.0`. `[n]T` ↔
`@Vector(n, T)` is lane `i` = item `i` (no memory image involved, also for the padded `u24`
item); other casts reinterpret the vector's bit-packed memory image (`ZigLean.VecCast`).
`std.mem.eql` on 40-byte slices runs `mem.eqlBytes` with its vector chunks.
-/

open VectorCasts Zig

namespace VectorCastsClients

/-- `[4]u8` → `@Vector(4, u8)` → `[4]u8` is the identity, for every array. -/
theorem bytes_lanes_roundtrip (a : Vector (BitVec 8) 4) :
    (bytesToLanes a >>= lanesToBytes) = pure a := by
  simp [bytesToLanes, lanesToBytes]

/-- A padded item converts to its lane, not to the array's bytes. -/
theorem u24_item_lane (x : BitVec 24) :
    (u24ItemToLane #v[x] >>= u24LaneToItem) = pure #v[x] := by
  simp [u24ItemToLane, u24LaneToItem]

/-- Each other cast is exactly `Zig.reprCast` (the generated wrapper adds nothing). -/
theorem wordToLanes_eq (x : BitVec 32) : wordToLanes x = reprCast (Vec (BitVec 8) 4) x := by
  simp [wordToLanes, StateT.run', liftM, monadLift, MonadLift.monadLift, StateT.lift, StateT.map,
    Functor.map]
  generalize reprCast (Vec (BitVec 8) 4) x = r
  rcases r with _ | (_ | _) <;> rfl

theorem lanesToWord_eq (v : Vec (BitVec 8) 4) : lanesToWord v = reprCast (BitVec 32) v := by
  simp [lanesToWord, StateT.run', liftM, monadLift, MonadLift.monadLift, StateT.lift, StateT.map,
    Functor.map]
  generalize reprCast (BitVec 32) v = r
  rcases r with _ | (_ | _) <;> rfl

theorem intToPackedLanes_eq (x : BitVec 9) : intToPackedLanes x = reprCast (Vec (BitVec 3) 3) x := by
  simp [intToPackedLanes, StateT.run', liftM, monadLift, MonadLift.monadLift, StateT.lift,
    StateT.map, Functor.map]
  generalize reprCast (Vec (BitVec 3) 3) x = r
  rcases r with _ | (_ | _) <;> rfl

theorem packedLanesToInt_eq (v : Vec (BitVec 3) 3) : packedLanesToInt v = reprCast (BitVec 9) v := by
  simp [packedLanesToInt, StateT.run', liftM, monadLift, MonadLift.monadLift, StateT.lift,
    StateT.map, Functor.map]
  generalize reprCast (BitVec 9) v = r
  rcases r with _ | (_ | _) <;> rfl

/-- `u32` → `@Vector(4, u8)` → `u32` is the identity, for every `x` (`reprCast_int_vec_int`). -/
theorem word_lanes_roundtrip (x : BitVec 32) : (wordToLanes x >>= lanesToWord) = pure x := by
  rw [wordToLanes_eq, funext lanesToWord_eq]
  exact reprCast_int_vec_int (n := 4) (w := 8) x

/-- `u9` → `@Vector(3, u3)` → `u9`: non-byte lanes, the same round trip. -/
theorem packed_lanes_roundtrip (x : BitVec 9) : (intToPackedLanes x >>= packedLanesToInt) = pure x := by
  rw [intToPackedLanes_eq, funext packedLanesToInt_eq]
  exact reprCast_int_vec_int (n := 3) (w := 3) x

/-- Lane 0 is the low byte: `0x44332211` is lanes `0x11, 0x22, 0x33, 0x44`. -/
theorem word_lane_order :
    ((wordToLanes 0x44332211).map (·.lanes)).run = some (.ok #v[0x11, 0x22, 0x33, 0x44]) := by
  decide +kernel

/-- `@Vector(8, bool)` → `u8`: lane `i` is bit `i`. -/
theorem bool_lane_bits :
    (boolLanesToByte ⟨#v[true, false, true, true, false, false, false, true]⟩).run =
      some (.ok 0x8d) := by
  decide +kernel

/-- `std.mem.eqlBytes`'s chunk compare: equal arrays are equal, one differing lane is found. -/
theorem eqlChunk_values :
    (eqlChunk (Vector.replicate 16 7) (Vector.replicate 16 7)).run = some (.ok true) ∧
      (eqlChunk (Vector.replicate 16 7) ((Vector.replicate 16 7).set 9 8)).run = some (.ok false) := by
  decide +kernel

end VectorCastsClients
