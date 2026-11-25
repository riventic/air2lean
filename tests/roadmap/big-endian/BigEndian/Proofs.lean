import BigEndian.V0_16_0.S390x.Gen
import BigEndian.V0_16_0.X64.Gen
import BigEndian.V0_17_1.S390x.Gen
import BigEndian.V0_17_1.X64.Gen
import ZigLean.EndianLemmas

/-!
# Byte order on the retained translations (T03)

`BigEndian.<V>.S390x.Gen` and `BigEndian.<V>.X64.Gen` translate the same functions of
`big_endian.zig` from the s390x-linux (big-endian) and x86_64-linux (little-endian) exports of
Zig `V` (0.16.0, 0.17.1). The AIR of one version is the same except for the profile; the
big-endian translation opens `Zig.BigEndian` and takes the `.big` bit-pointer accesses. These
facts are kernel evaluations of the translations; the native observations of
`check.sh --native <version>` agree with every line of `BigEndian.<V>.<T>.Diff`.

Up to 0.16 `@bitCast` reinterprets the memory bytes, so a cast to or from bytes observes the
byte order. From 0.17 on it is the logical bit order (`docs/bitcast-semantics.md`), the same on
both targets; the byte order shows through memory only (byte views, `extern` aggregates, bit
pointers).
-/

open Zig

namespace BigEndianClients

def runMem {α : Type} (m : Mem) (x : MemM α) : Option (Except Error α) :=
  (Prod.fst <$> x.run m).run

/-! ## Zig 0.16.0: `@bitCast` is memory reinterpretation -/

/-- `@bitCast(u32) → [4]u8`: most significant byte first on s390x, last on x86_64. -/
theorem u32ToBytes_orders_0_16 :
    (BigEndian.V0_16_0.S390x.u32ToBytes 0x01020304).run = some (.ok #v[1, 2, 3, 4]) ∧
      (BigEndian.V0_16_0.X64.u32ToBytes 0x01020304).run = some (.ok #v[4, 3, 2, 1]) := by
  decide +kernel

/-- `[4]u8 → u32` inverts it at each order. -/
theorem bytesToU32_orders_0_16 :
    (BigEndian.V0_16_0.S390x.bytesToU32 #v[1, 2, 3, 4]).run = some (.ok 0x01020304) ∧
      (BigEndian.V0_16_0.X64.bytesToU32 #v[1, 2, 3, 4]).run = some (.ok 0x04030201) := by
  decide +kernel

/-- An `f32`'s bytes are its bits' bytes (1.0 is `0x3f800000`). -/
theorem f32ToBytes_orders_0_16 :
    (BigEndian.V0_16_0.S390x.f32ToBytes ⟨0x3f800000⟩).run = some (.ok #v[0x3f, 0x80, 0, 0]) ∧
      (BigEndian.V0_16_0.X64.f32ToBytes ⟨0x3f800000⟩).run = some (.ok #v[0, 0, 0x80, 0x3f]) := by
  decide +kernel

/-- A packed struct is its backing integer: `packed struct(u16) { lo: u12, hi: u4 }` with
`lo = 0xabc`, `hi = 0xd` is `0xdabc`. -/
theorem packed16ToBytes_orders_0_16 :
    (BigEndian.V0_16_0.S390x.packed16ToBytes 0xabc 0xd).run = some (.ok #v[0xda, 0xbc]) ∧
      (BigEndian.V0_16_0.X64.packed16ToBytes 0xabc 0xd).run = some (.ok #v[0xbc, 0xda]) := by
  decide +kernel

/-- The bytes of an `extern struct { a: u16, b: u16, c: u32 }`: each field in the target's
order, at the same offsets. -/
theorem externToBytes_orders_0_16 :
    (BigEndian.V0_16_0.S390x.externToBytes 0x0102 0x0304 0xa1b2c3d4).run =
        some (.ok #v[1, 2, 3, 4, 0xa1, 0xb2, 0xc3, 0xd4]) ∧
      (BigEndian.V0_16_0.X64.externToBytes 0x0102 0x0304 0xa1b2c3d4).run =
        some (.ok #v[2, 1, 4, 3, 0xd4, 0xc3, 0xb2, 0xa1]) := by
  decide +kernel

/-- A bit-pointer store of `b` into `P = packed struct(u32) { a: u4, b: u12, c: u16 }` in memory,
then the struct's bytes: host bit 4 is in the last byte on s390x and in the first on x86_64. -/
theorem setFieldBytes_orders_0_16 :
    runMem (BigEndian.V0_16_0.S390x.mem0 .fresh) (BigEndian.V0_16_0.S390x.setFieldBytes 0 0xabc) =
        some (.ok #v[0, 0, 0xab, 0xc0]) ∧
      runMem (BigEndian.V0_16_0.X64.mem0 .fresh) (BigEndian.V0_16_0.X64.setFieldBytes 0 0xabc) =
        some (.ok #v[0xc0, 0xab, 0, 0]) := by
  decide +kernel

/-- A bit-pointer load after byte stores reads the field from the host at the target's order. -/
theorem fieldFromBytes_orders_0_16 :
    runMem (BigEndian.V0_16_0.S390x.mem0 .fresh)
        (BigEndian.V0_16_0.S390x.fieldFromBytes 0x12 0x34 0x56 0x78) = some (.ok 0x567) ∧
      runMem (BigEndian.V0_16_0.X64.mem0 .fresh)
        (BigEndian.V0_16_0.X64.fieldFromBytes 0x12 0x34 0x56 0x78) = some (.ok 0x341) := by
  decide +kernel

/-! ## Zig 0.17.1: `@bitCast` is the logical bit order -/

/-- `@bitCast(u32) → [4]u8`: element 0 is the least significant byte, on both targets. -/
theorem u32ToBytes_logical_0_17 :
    (BigEndian.V0_17_1.S390x.u32ToBytes 0x01020304).run = some (.ok #v[4, 3, 2, 1]) ∧
      (BigEndian.V0_17_1.X64.u32ToBytes 0x01020304).run = some (.ok #v[4, 3, 2, 1]) := by
  decide +kernel

/-- `[4]u8 → u32` inverts it, on both targets. -/
theorem bytesToU32_logical_0_17 :
    (BigEndian.V0_17_1.S390x.bytesToU32 #v[1, 2, 3, 4]).run = some (.ok 0x04030201) ∧
      (BigEndian.V0_17_1.X64.bytesToU32 #v[1, 2, 3, 4]).run = some (.ok 0x04030201) := by
  decide +kernel

/-- An `f32`'s bytes are its bits in logical order (1.0 is `0x3f800000`). -/
theorem f32ToBytes_logical_0_17 :
    (BigEndian.V0_17_1.S390x.f32ToBytes ⟨0x3f800000⟩).run = some (.ok #v[0, 0, 0x80, 0x3f]) ∧
      (BigEndian.V0_17_1.X64.f32ToBytes ⟨0x3f800000⟩).run = some (.ok #v[0, 0, 0x80, 0x3f]) := by
  decide +kernel

/-- A packed struct's backing integer `0xdabc` in logical order. -/
theorem packed16ToBytes_logical_0_17 :
    (BigEndian.V0_17_1.S390x.packed16ToBytes 0xabc 0xd).run = some (.ok #v[0xbc, 0xda]) ∧
      (BigEndian.V0_17_1.X64.packed16ToBytes 0xabc 0xd).run = some (.ok #v[0xbc, 0xda]) := by
  decide +kernel

/-- The memory bytes of an `extern struct { a: u16, b: u16, c: u32 }` (a byte view, as 0.17 has
no `@bitCast` of it): each field in the target's order, at the same offsets. -/
theorem externToBytes_orders_0_17 :
    runMem (BigEndian.V0_17_1.S390x.mem0 .fresh)
        (BigEndian.V0_17_1.S390x.externToBytes 0x0102 0x0304 0xa1b2c3d4) =
        some (.ok #v[1, 2, 3, 4, 0xa1, 0xb2, 0xc3, 0xd4]) ∧
      runMem (BigEndian.V0_17_1.X64.mem0 .fresh)
        (BigEndian.V0_17_1.X64.externToBytes 0x0102 0x0304 0xa1b2c3d4) =
        some (.ok #v[2, 1, 4, 3, 0xd4, 0xc3, 0xb2, 0xa1]) := by
  decide +kernel

/-- A bit-pointer store into a packed struct in memory, then its bytes, as on 0.16. -/
theorem setFieldBytes_orders_0_17 :
    runMem (BigEndian.V0_17_1.S390x.mem0 .fresh) (BigEndian.V0_17_1.S390x.setFieldBytes 0 0xabc) =
        some (.ok #v[0, 0, 0xab, 0xc0]) ∧
      runMem (BigEndian.V0_17_1.X64.mem0 .fresh) (BigEndian.V0_17_1.X64.setFieldBytes 0 0xabc) =
        some (.ok #v[0xc0, 0xab, 0, 0]) := by
  decide +kernel

/-- A bit-pointer load after byte stores, as on 0.16. -/
theorem fieldFromBytes_orders_0_17 :
    runMem (BigEndian.V0_17_1.S390x.mem0 .fresh)
        (BigEndian.V0_17_1.S390x.fieldFromBytes 0x12 0x34 0x56 0x78) = some (.ok 0x567) ∧
      runMem (BigEndian.V0_17_1.X64.mem0 .fresh)
        (BigEndian.V0_17_1.X64.fieldFromBytes 0x12 0x34 0x56 0x78) = some (.ok 0x341) := by
  decide +kernel

/-- Every big-endian integer encoding of the translation reads back (`intEncOf_lawful`): a
`u32` stored by the s390x model loads as itself. -/
example (v : BitVec 32) : (intEncOf .big 32).decode ((intEncOf .big 32).encode v) = pure v :=
  (intEncOf_lawful .big 32).decode_encode v

end BigEndianClients
