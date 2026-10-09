import Lanes.Gen

/-! The inputs and results of `lanes.zig`'s native test, as kernel-checked runs of the
functions translated from the exported AIR (`lanes_checks.py` writes this file). -/

private def memoryValue {α : Type} (r : Zig.MemM α) : Option α :=
  ((r.run {}).run.bind Except.toOption).map Prod.fst

example : (memoryValue (Lanes.u9Lane 0x0 0x0 0x0)).map BitVec.toNat = some 0 := by
  decide +kernel
example : (memoryValue (Lanes.u9Lane 0x1ff 0x0 0xaa)).map BitVec.toNat = some 11682355610111 := by
  decide +kernel
example : (memoryValue (Lanes.u9Lane 0x155 0xaa 0x1ff)).map BitVec.toNat = some 35138603668821 := by
  decide +kernel
example : (memoryValue (Lanes.u9Lane 0xffff 0x1234 0x7)).map BitVec.toNat = some 488017521151 := by
  decide +kernel
example : (memoryValue (Lanes.u3Lane 0x0 0x0)).map BitVec.toNat = some 0 := by
  decide +kernel
example : (memoryValue (Lanes.u3Lane 0x0 0x5)).map BitVec.toNat = some 84049920 := by
  decide +kernel
example : (memoryValue (Lanes.u3Lane 0x0 0x7)).map BitVec.toNat = some 117669888 := by
  decide +kernel
example : (memoryValue (Lanes.u3Lane 0x0 0xff)).map BitVec.toNat = some 117669888 := by
  decide +kernel
example : (memoryValue (Lanes.u3Lane 0xffffff 0x0)).map BitVec.toNat = some 16547839 := by
  decide +kernel
example : (memoryValue (Lanes.u3Lane 0xffffff 0x5)).map BitVec.toNat = some 100597759 := by
  decide +kernel
example : (memoryValue (Lanes.u3Lane 0xffffff 0x7)).map BitVec.toNat = some 134217727 := by
  decide +kernel
example : (memoryValue (Lanes.u3Lane 0xffffff 0xff)).map BitVec.toNat = some 134217727 := by
  decide +kernel
example : (memoryValue (Lanes.u3Lane 0x123456 0x0)).map BitVec.toNat = some 1061974 := by
  decide +kernel
example : (memoryValue (Lanes.u3Lane 0x123456 0x5)).map BitVec.toNat = some 85111894 := by
  decide +kernel
example : (memoryValue (Lanes.u3Lane 0x123456 0x7)).map BitVec.toNat = some 118731862 := by
  decide +kernel
example : (memoryValue (Lanes.u3Lane 0x123456 0xff)).map BitVec.toNat = some 118731862 := by
  decide +kernel
example : (memoryValue (Lanes.u3Lane 0xfac688 0x0)).map BitVec.toNat = some 16270984 := by
  decide +kernel
example : (memoryValue (Lanes.u3Lane 0xfac688 0x5)).map BitVec.toNat = some 100320904 := by
  decide +kernel
example : (memoryValue (Lanes.u3Lane 0xfac688 0x7)).map BitVec.toNat = some 133940872 := by
  decide +kernel
example : (memoryValue (Lanes.u3Lane 0xfac688 0xff)).map BitVec.toNat = some 133940872 := by
  decide +kernel
example : (memoryValue (Lanes.u24Lane 0x0 0x0)).map BitVec.toNat = some 1 := by
  decide +kernel
example : (memoryValue (Lanes.u24Lane 0x0 0xfedcba)).map BitVec.toNat = some 16702651 := by
  decide +kernel
example : (memoryValue (Lanes.u24Lane 0x0 0x12345678)).map BitVec.toNat = some 3430009 := by
  decide +kernel
example : (memoryValue (Lanes.u24Lane 0xabcdef12 0x0)).map BitVec.toNat = some 1 := by
  decide +kernel
example : (memoryValue (Lanes.u24Lane 0xabcdef12 0xfedcba)).map BitVec.toNat = some 16702651 := by
  decide +kernel
example : (memoryValue (Lanes.u24Lane 0xabcdef12 0x12345678)).map BitVec.toNat = some 3430009 := by
  decide +kernel
example : (memoryValue (Lanes.u24Lane 0xffffffff 0x0)).map BitVec.toNat = some 16777215 := by
  decide +kernel
example : (memoryValue (Lanes.u24Lane 0xffffffff 0xfedcba)).map BitVec.toNat = some 16702649 := by
  decide +kernel
example : (memoryValue (Lanes.u24Lane 0xffffffff 0x12345678)).map BitVec.toNat = some 3430007 := by
  decide +kernel
example : (memoryValue (Lanes.boolLane 0)).map BitVec.toNat = some 8 := by
  decide +kernel
example : (memoryValue (Lanes.boolLane 1)).map BitVec.toNat = some 9 := by
  decide +kernel
example : (memoryValue (Lanes.boolLane 2)).map BitVec.toNat = some 10 := by
  decide +kernel
example : (memoryValue (Lanes.boolLane 3)).map BitVec.toNat = some 11 := by
  decide +kernel
example : (memoryValue (Lanes.boolLane 4)).map BitVec.toNat = some 12 := by
  decide +kernel
example : (memoryValue (Lanes.boolLane 5)).map BitVec.toNat = some 13 := by
  decide +kernel
example : (memoryValue (Lanes.boolLane 6)).map BitVec.toNat = some 14 := by
  decide +kernel
example : (memoryValue (Lanes.boolLane 7)).map BitVec.toNat = some 15 := by
  decide +kernel
example : (memoryValue (Lanes.boolLane 8)).map BitVec.toNat = some 0 := by
  decide +kernel
example : (memoryValue (Lanes.boolLane 9)).map BitVec.toNat = some 1 := by
  decide +kernel
example : (memoryValue (Lanes.boolLane 10)).map BitVec.toNat = some 2 := by
  decide +kernel
example : (memoryValue (Lanes.boolLane 11)).map BitVec.toNat = some 3 := by
  decide +kernel
example : (memoryValue (Lanes.boolLane 12)).map BitVec.toNat = some 4 := by
  decide +kernel
example : (memoryValue (Lanes.boolLane 13)).map BitVec.toNat = some 5 := by
  decide +kernel
example : (memoryValue (Lanes.boolLane 14)).map BitVec.toNat = some 6 := by
  decide +kernel
example : (memoryValue (Lanes.boolLane 15)).map BitVec.toNat = some 7 := by
  decide +kernel
example : (memoryValue (Lanes.boolLane 16)).map BitVec.toNat = some 24 := by
  decide +kernel
example : (memoryValue (Lanes.boolLane 17)).map BitVec.toNat = some 25 := by
  decide +kernel
example : (memoryValue (Lanes.boolLane 18)).map BitVec.toNat = some 26 := by
  decide +kernel
example : (memoryValue (Lanes.boolLane 19)).map BitVec.toNat = some 27 := by
  decide +kernel
example : (memoryValue (Lanes.boolLane 20)).map BitVec.toNat = some 28 := by
  decide +kernel
example : (memoryValue (Lanes.boolLane 21)).map BitVec.toNat = some 29 := by
  decide +kernel
example : (memoryValue (Lanes.boolLane 22)).map BitVec.toNat = some 30 := by
  decide +kernel
example : (memoryValue (Lanes.boolLane 23)).map BitVec.toNat = some 31 := by
  decide +kernel
example : (memoryValue (Lanes.boolLane 24)).map BitVec.toNat = some 16 := by
  decide +kernel
example : (memoryValue (Lanes.boolLane 25)).map BitVec.toNat = some 17 := by
  decide +kernel
example : (memoryValue (Lanes.boolLane 26)).map BitVec.toNat = some 18 := by
  decide +kernel
example : (memoryValue (Lanes.boolLane 27)).map BitVec.toNat = some 19 := by
  decide +kernel
example : (memoryValue (Lanes.boolLane 28)).map BitVec.toNat = some 20 := by
  decide +kernel
example : (memoryValue (Lanes.boolLane 29)).map BitVec.toNat = some 21 := by
  decide +kernel
example : (memoryValue (Lanes.boolLane 30)).map BitVec.toNat = some 22 := by
  decide +kernel
example : (memoryValue (Lanes.boolLane 31)).map BitVec.toNat = some 23 := by
  decide +kernel
