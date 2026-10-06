import ZigLean

/-! Ordinary kernel reduction, with asymmetric bits and lane values. -/
example : Zig.bitReverse (1 : BitVec 1) = 1 := by decide
example : Zig.bitReverse (0 : BitVec 0) = 0 := by decide
example : Zig.bitReverse (1 : BitVec 3) = 4 := by decide
example : Zig.bitReverse (-4 : BitVec 3) = 1 := by decide
example : Zig.bitReverse (1 : BitVec 9) = 256 := by decide
example : Zig.bitReverse (0x1234 : BitVec 16) = 0x2c48 := by decide
example : Zig.byteSwap (0 : BitVec 0) = 0 := by decide
example : Zig.byteSwap (0x96 : BitVec 8) = 0x96 := by decide
example : Zig.byteSwap (0x1234 : BitVec 16) = 0x3412 := by decide
example : Zig.byteSwap (-32767 : BitVec 16) = 0x0180 := by decide
example : Zig.byteSwap (0x123456 : BitVec 24) = 0x563412 := by decide
example : Zig.byteSwap (0x0123456789abcdef : BitVec 64) = 0xefcdab8967452301 := by decide
example : Zig.byteSwap (0x0123456789abcdeffedcba9876543210 : BitVec 128) =
    0x1032547698badcfeefcdab8967452301 := by decide
example : (Zig.Vec.map Zig.byteSwap (⟨#v[0x1234, 0x8001, 0x00ff]⟩ : Zig.Vec (BitVec 16) 3)).lanes =
    #v[0x3412, 0x0180, 0xff00] := by decide
example : (Zig.Vec.map Zig.bitReverse (⟨#v[1, 2, 3]⟩ : Zig.Vec (BitVec 3) 3)).lanes =
    #v[4, 2, 6] := by decide
