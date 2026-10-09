import ZigLean.BitCast

/-! `ZigLean/BitCast.lean` on the Zig 0.17.0 behaviour-test values
(`test/behavior/bitcast.zig` in the 0.17.0 source tarball; docs/bitcast-semantics.md §Evidence). -/

open Zig Zig.BitCast

-- "@bitCast vector to array with different element size": @Vector(4, u5) → [5]u4
#guard ofLanes (#v[0b00010, 0b01111, 0b11001, 0b00000] : Vector (BitVec 5) 4) = 0x65e2#20
#guard (toLanes (n := 5) (w := 4) (ofLanes (w := 5) (n := 4) (#v[0b00010, 0b01111, 0b11001, 0b00000] :
  Vector (BitVec 5) 4))).toList = [0b0010, 0b1110, 0b0101, 0b0110, 0b0000]
-- "bitcast vector to integer and back": @Vector(16, bool), lane 1 false
#guard ofBools (Vector.ofFn fun i : Fin 16 => i.val != 1) = 0b1111_1111_1111_1101#16
#guard (toBools 0xfffd#16).toList = (List.range 16).map (· != 1)
-- "@bitCast packed struct to array of bits": backing integer 0xafc9 → [16]u1
#guard (toLanes (n := 16) (w := 1) 0xafc9#16).toList =
  [1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1]
-- "@bitCast nested arrays of bool to scalar": rows concatenated, row 0 lowest
#guard ofLanes (#v[ofBools #v[true, true, false, false], ofBools #v[false, true, false, true],
  ofBools #v[true, false, true, false], ofBools #v[false, false, true, true]] :
  Vector (BitVec 4) 4) = 0b1100_0101_1010_0011#16
-- "@bitCast deeply nested arrays to scalar": [2][1][3][5]u4 → u120, flattened in order
#guard ofLanes (#v[0x1, 0x5, 0xF, 0x0, 0x4, 0xD, 0xE, 0xF, 0xE, 0x1, 0xC, 0xA, 0x7, 0xE, 0x0,
  0x0, 0x2, 0x0, 0x4, 0xF, 0xF, 0x6, 0xF, 0xB, 0x5, 0xB, 0x3, 0x7, 0x8, 0x8] :
  Vector (BitVec 4) 30) = 0x8873B_5BF6F_F4020_0E7AC_1EFED_40F51#120
-- padded elements (native probe, stock 0.17.0): [2]u24 → u48, [3]u9 → u27; 0.16 differs
#guard ofLanes (#v[0x112233, 0x445566] : Vector (BitVec 24) 2) = 0x445566112233#48
#guard ofLanes (#v[0x101, 0x0ff, 0x1aa] : Vector (BitVec 9) 3) = 0x6a9ff01#27
-- byte-multiple lanes: the ≤0.16 memory bytes are the logical integer's bytes
#guard (Enc.encode (#v[0x11, 0x22, 0x33, 0x44] : Vector (BitVec 8) 4) : Array Byte) =
  Enc.encode 0x44332211#32
-- …but not for padded lanes: [2]u24 occupies 8 bytes with an undefined byte per lane
#guard (Enc.encode (#v[0x112233, 0x445566] : Vector (BitVec 24) 2) : Array Byte) !=
  intBytes 0x445566112233#48

example : intSize 32 = 4 := by decide
example (v : Vector (BitVec 8) 4) : (Enc.encode v : Array Byte) = intBytes (ofLanes v) :=
  encode_array_eq_intBytes_ofLanes 1 4 (by decide) v

#print axioms encode_array_eq_intBytes_ofLanes
#print axioms encode_vec_eq_intBytes_ofLanes
#print axioms encode_ofLanes_eq_encode_array
#print axioms toLanes_ofLanes
#print axioms ofLanes_toLanes
#print axioms toBools_ofBools
#print axioms ofBools_toBools
#print axioms getLsbD_ofLanes
