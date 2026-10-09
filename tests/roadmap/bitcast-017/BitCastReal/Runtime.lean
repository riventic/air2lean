import BitCastReal.Gen

/-! Runs the translation of real Zig 0.17.0 AIR (`air/0.17.0`, patched compiler, ReleaseSafe,
x86_64-linux) and compares each result with the stock Zig 0.17.0 test in `bitcast017.zig`
(`zig test` passes natively) and the 0.17.0 behaviour tests it cites. -/

open Zig BitCastReal

private def ok {α : Type} [DecidableEq α] (name : String) (r : Zig.Result α) (v : α) : IO Unit :=
  unless r.run = some (Except.ok v) do throw (IO.userError s!"{name}: wrong result")

/-- Byte-multiple lanes: the generated 0.17 code and the ≤0.16 memory reading agree
(`Zig.BitCast.encode_ofLanes_eq_encode_array`), so a ≤0.16 byte-level fact transfers. -/
theorem bytesToInt_eq (v : Vector (BitVec 8) 4) : bytesToInt v = pure (Zig.BitCast.ofLanes v) := rfl

example (v : Vector (BitVec 8) 4) :
    bytesToInt v = pure (Zig.BitCast.ofLanes v) ∧
      (Zig.Enc.encode (Zig.BitCast.ofLanes v) : Array Zig.Byte) = Zig.Enc.encode v := by
  have h := Zig.BitCast.encode_ofLanes_eq_encode_array 1 4 (by decide) (by decide) v
  exact ⟨bytesToInt_eq v, h⟩

def main : IO Unit := do
  let v5 : Zig.Vec (BitVec 5) 4 := ⟨#v[2, 15, 25, 0]⟩
  ok "vecToInt" (vecToInt v5) 0x65e2#20
  ok "intToVec" ((intToVec 0x0cbe2#20).map (·.lanes.toList)) [2, 31, 18, 1]
  ok "vecToArray" ((vecToArray v5).map (·.toList)) [2, 14, 5, 6, 0]
  ok "boolsToInt" (boolsToInt ⟨Vector.ofFn fun i => i.val != 1⟩) 0xfffd#16
  ok "packedToBits" ((packedToBits (Zig.Packed.ofBits 0xafc9#16)).map (·.toList))
    [1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1]
  ok "paddedToInt" (paddedToInt #v[0x112233, 0x445566]) 0x445566112233#48
  ok "intToPadded" ((intToPadded 0x445566112233#48).map (·.toList)) [0x112233, 0x445566]
  ok "bytesToInt" (bytesToInt #v[0x11, 0x22, 0x33, 0x44]) 0x44332211#32
  ok "intToEnum" (intToEnum 1#8) E.b
  -- test/cases/safety/bitcast_to_enum_no_matching_tag_value.zig: `invalid enum value` panic
  unless (intToEnum 3#8).run = some (.error .panic) do
    throw (IO.userError "intToEnum 3: no invalidEnumValue panic")
  ok "enumToSigned" (enumToSigned E.c) 2#8
  IO.println "real 0.17.0 AIR bitcast translations passed"
