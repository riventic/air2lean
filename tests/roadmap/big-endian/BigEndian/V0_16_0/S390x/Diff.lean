import BigEndian.V0_16_0.S390x.Gen
import BigEndian.Lines

/-! The lines of `native.zig` from the translation `BigEndian.V0_16_0.S390x.Gen`. Written for
0.17.1 on x86_64-linux; the module of every other version and target is this one with the
version and target renamed (`check.sh`, `scripts/fixtures.py instance`). -/

open Zig

namespace BigEndian.V0_16_0.S390x.Diff

def impl : BigEndian.Lines.Impl where
  mem0 := BigEndian.V0_16_0.S390x.mem0 .fresh
  u32ToBytes := BigEndian.V0_16_0.S390x.u32ToBytes
  bytesToU32 := BigEndian.V0_16_0.S390x.bytesToU32
  i16ToBytes := BigEndian.V0_16_0.S390x.i16ToBytes
  u64ToHalves := BigEndian.V0_16_0.S390x.u64ToHalves
  f32ToBytes := BigEndian.V0_16_0.S390x.f32ToBytes
  bytesToF64Bits := BigEndian.V0_16_0.S390x.bytesToF64Bits
  f16ToBytes := BigEndian.V0_16_0.S390x.f16ToBytes
  packedToBytes := BigEndian.V0_16_0.S390x.packedToBytes
  packed16ToBytes := BigEndian.V0_16_0.S390x.packed16ToBytes
  setFieldBytes := BigEndian.V0_16_0.S390x.setFieldBytes
  fieldFromBytes := BigEndian.V0_16_0.S390x.fieldFromBytes
  byteOfU32 := BigEndian.V0_16_0.S390x.byteOfU32
  u16FromStoredBytes := BigEndian.V0_16_0.S390x.u16FromStoredBytes
  byteOfF64 := BigEndian.V0_16_0.S390x.byteOfF64
  externToBytes a b c := (BigEndian.V0_16_0.S390x.externToBytes a b c : MemM _)
  unionHalf := BigEndian.V0_16_0.S390x.unionHalf
  unionByte := BigEndian.V0_16_0.S390x.unionByte

def main : IO Unit := do
  for l in BigEndian.Lines.lines impl do IO.println l

end BigEndian.V0_16_0.S390x.Diff
