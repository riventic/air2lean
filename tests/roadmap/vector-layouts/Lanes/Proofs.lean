import Lanes.Gen
import ZigLean.VecMem

/-!
# Lane pointers in the translated `lanes.zig`

`Lanes/Gen.lean` is the translation of the AIR that the patched Zig 0.16.0 exported from
`lanes.zig` (`air/0.16.0`, x86_64-linux baseline, LLVM backend). Its lane pointers are
bit-pointers into the vector's integer (`Zig.loadLane`/`Zig.storeLane`): `&v[5]` of
`@Vector(8, u3)` reads and writes bits 15..17 of 3 bytes, `&v[3]` of `@Vector(5, bool)` bit 3 of
1 byte. For every vector in memory at `p` (`hv`: the bytes of its image):

* `getU3_run`: `getU3(&v[5])` returns lane 5 and reads only the 3 host bytes;
* `putU3_run`, `putU3_load`: `putU3(&v[5], x)` writes the host bytes of `v` with lane 5
  replaced, and the vector loaded afterwards is `v.set 5 x`: lane 5 is `x`, every other lane is
  unchanged (`putU3_lane_ne`);
* `flipBool_run`, `flipBool_load`: `flipBool(&v[3])` negates lane 3 of a `bool` vector and keeps
  every other lane.
-/

open Zig

/-- The 3 host bytes of a `@Vector(8, u3)` at `p`: the first 3 bytes of its image. -/
private theorem u3_host {v : Vec (BitVec 3) 8} {bs : Array Byte} {o : Nat}
    (hv : bs.extract o (o + 4) = Enc.encode v) :
    bs.extract o (o + 3) = intBytes (v.packBits 3 Packed.toBits) :=
  Vec.host_of_encode (n := 8) (w := 3) id id v hv

/-- `getU3(&v[5])` reads lane 5. -/
theorem getU3_run (v : Vec (BitVec 3) 8) {m : Mem} {p : Ptr} {b : BlockId} {blk : Block}
    {o : Nat} (h : m.access p 3 1 = pure (b, blk, o))
    (hv : blk.bytes.extract o (o + 4) = Enc.encode v) (hr : NoRace m b o 3 .read) :
    (Lanes.getU3 p).run m = pure (v.lanes[(5 : Fin 8)], m.recordAt b o 3 .read) := by
  have hl := Vec.loadLane_vec (α := BitVec 3) (n := 8) (w := 3) v 5 rfl h (u3_host hv) hr
  simp only [Lanes.getU3, zig_unfold, show laneHost 8 3 = 3 from rfl,
    show ((5 : Fin 8) : Nat) * 3 = 15 from rfl] at *
  rw [hl]
  rfl

/-- `putU3(&v[5], x)` writes the 3 host bytes of `v.set 5 x` and no other byte. -/
theorem putU3_run (v : Vec (BitVec 3) 8) (x : BitVec 3) {m : Mem} {p : Ptr} {b : BlockId}
    {blk : Block} {o : Nat} (h : m.access p 3 1 = pure (b, blk, o))
    (hv : blk.bytes.extract o (o + 4) = Enc.encode v) (hK : blk.kind ≠ .constGlobal)
    (hr : NoRace m b o 3 .read) (hw : NoRace (m.recordAt b o 3 .read) b o 3 .write) :
    (Lanes.putU3 p x).run m = pure ((), ((m.recordAt b o 3 .read).recordAt b o 3 .write).write
        b blk o (intBytes ((v.set 5 x).packBits 3 Packed.toBits))) := by
  have hl := Vec.storeLane_vec (α := BitVec 3) (n := 8) (w := 3) v 5 x h (u3_host hv) hK hr hw
  simp only [Lanes.putU3, zig_unfold, show laneHost 8 3 = 3 from rfl,
    show ((5 : Fin 8) : Nat) * 3 = 15 from rfl] at *
  rw [hl]
  rfl

/-- After `putU3(&v[5], x)`, the vector in memory is `v.set 5 x`. -/
theorem putU3_load (v : Vec (BitVec 3) 8) (x : BitVec 3) {m : Mem} {p : Ptr} {b : BlockId}
    {blk : Block} {o : Nat} (h : m.access p 3 1 = pure (b, blk, o))
    (h4 : m.access p 4 4 = pure (b, blk, o))
    (hr : NoRace (((m.recordAt b o 3 .read).recordAt b o 3 .write).write b blk o
      (intBytes ((v.set 5 x).packBits 3 Packed.toBits))) b o 4 .read) :
    (load (Vec (BitVec 3) 8) 4 p).run (((m.recordAt b o 3 .read).recordAt b o 3 .write).write
        b blk o (intBytes ((v.set 5 x).packBits 3 Packed.toBits))) =
      pure (v.set 5 x, ((((m.recordAt b o 3 .read).recordAt b o 3 .write).write b blk o
        (intBytes ((v.set 5 x).packBits 3 Packed.toBits))).recordAt b o 4 .read)) :=
  Vec.load_storeLane_vec (α := BitVec 3) (n := 8) (w := 3) (fun _ => rfl) v 5 x h h4 hr

/-- `putU3(&v[5], x)` keeps every lane but 5. -/
theorem putU3_lane_ne (v : Vec (BitVec 3) 8) (x : BitVec 3) (j : Nat) (hj : j < 8) (h5 : j ≠ 5) :
    (v.set 5 x).lanes[j] = v.lanes[j] :=
  Vec.set_lane_ne v 5 x j hj (Ne.symm h5)

private theorem bool_round : ∀ c : Bool, Packed.ofBits (Packed.toBits c) = c := by decide

/-- `flipBool(&v[3])` negates lane 3 of a `@Vector(5, bool)`: it reads the host byte, then writes
the host byte of `v.set 3 !v[3]`. -/
theorem flipBool_run (v : Vec Bool 5) {m : Mem} {p : Ptr} {b : BlockId} {blk : Block} {o : Nat}
    (h : m.access p 1 1 = pure (b, blk, o))
    (hv : blk.bytes.extract o (o + 1) = Enc.encode v) (hK : blk.kind ≠ .constGlobal)
    (hr : NoRace m b o 1 .read) (hr' : NoRace (m.recordAt b o 1 .read) b o 1 .read)
    (hw : NoRace ((m.recordAt b o 1 .read).recordAt b o 1 .read) b o 1 .write) :
    (Lanes.flipBool p).run m = pure ((), ((((m.recordAt b o 1 .read).recordAt b o 1 .read).recordAt
        b o 1 .write).write b blk o
          (intBytes ((v.set 3 (!v.lanes[(3 : Fin 5)])).packBits 1 Packed.toBits)))) := by
  have hhost := Vec.host_of_encode (n := 5) (w := 1) boolBit (· == 1#1) v hv
  have hl := Vec.loadLane_vec (α := Bool) (n := 5) (w := 1) v 3 rfl h hhost hr
  have hs := Vec.storeLane_vec (α := Bool) (n := 5) (w := 1) v 3 (!v.lanes[(3 : Fin 5)])
    (access_recordAt.trans h) hhost hK hr' hw
  simp only [Lanes.flipBool, zig_unfold, show laneHost 5 1 = 1 from rfl,
    show ((3 : Fin 5) : Nat) * 1 = 3 from rfl] at *
  simp only [bool_round] at hl
  rw [hl]
  simp only [ExceptT.bindCont]
  rw [hs]
  rfl

/-- After `flipBool(&v[3])`, the vector in memory is `v` with lane 3 negated. -/
theorem flipBool_load (v : Vec Bool 5) {m : Mem} {p : Ptr} {b : BlockId} {blk : Block}
    {o : Nat} (h : m.access p 1 1 = pure (b, blk, o))
    (hr : NoRace (((((m.recordAt b o 1 .read).recordAt b o 1 .read).recordAt b o 1 .write).write
      b blk o (intBytes ((v.set 3 (!v.lanes[(3 : Fin 5)])).packBits 1 Packed.toBits)))) b o 1 .read) :
    (load (Vec Bool 5) 1 p).run ((((m.recordAt b o 1 .read).recordAt b o 1 .read).recordAt b o 1
        .write).write b blk o (intBytes ((v.set 3 (!v.lanes[(3 : Fin 5)])).packBits 1 Packed.toBits))) =
      pure (v.set 3 (!v.lanes[(3 : Fin 5)]), (((((m.recordAt b o 1 .read).recordAt b o 1 .read).recordAt
        b o 1 .write).write b blk o (intBytes ((v.set 3 (!v.lanes[(3 : Fin 5)])).packBits 1
          Packed.toBits))).recordAt b o 1 .read)) :=
  Vec.load_storeLane_vec (α := Bool) (n := 5) (w := 1) bool_round v 3 _
    (m := m.recordAt b o 1 .read) (access_recordAt.trans h) (access_recordAt.trans h) hr
