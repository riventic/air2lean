import ZigLean

/-! General contracts for arbitrary integer widths and lane counts. -/
example {n : Nat} (a : BitVec n) : Zig.bitReverse (Zig.bitReverse a) = a :=
  Zig.bitReverse_involution a
example {n : Nat} (a : BitVec n) (h : n % 8 = 0) : Zig.byteSwap (Zig.byteSwap a) = a :=
  Zig.byteSwap_involution a h
example {n : Nat} (a : BitVec n) (b k : Nat) (hb : b < n / 8) (hk : k < 8) :
    (Zig.byteSwap a).getLsbD (8 * b + k) = a.getLsbD (8 * (n / 8 - 1 - b) + k) :=
  Zig.byteSwap_byte_bit a b k hb hk
example {n lanes : Nat} (v : Zig.Vec (BitVec n) lanes) (h : n % 8 = 0) :
    Zig.Vec.map Zig.byteSwap (Zig.Vec.map Zig.byteSwap v) = v :=
  Zig.byteSwap_vector_involution v h
example {n lanes : Nat} (v : Zig.Vec (BitVec n) lanes) :
    Zig.Vec.map Zig.bitReverse (Zig.Vec.map Zig.bitReverse v) = v :=
  Zig.bitReverse_vector_involution v
#print axioms Zig.bitReverse_bit
#print axioms Zig.bitReverse_involution
#print axioms Zig.byteSwap_bit
#print axioms Zig.byteSwap_byte_bit
#print axioms Zig.byteSwap_involution
#print axioms Zig.byteSwap_lane
#print axioms Zig.bitReverse_lane
#print axioms Zig.byteSwap_vector_involution
#print axioms Zig.bitReverse_vector_involution
