import BigEndian.V0_17_1.X64.Gen
import BigEndian.Lines

/-! The lines of `native.zig` from the translation `BigEndian.V0_17_1.X64.Gen`. Written for
0.17.1 on x86_64-linux; the module of every other version and target is this one with the
version and target renamed (`check.sh`, `scripts/fixtures.py instance`). -/

open Zig

namespace BigEndian.V0_17_1.X64.Diff

def impl : BigEndian.Lines.Impl where
  mem0 := BigEndian.V0_17_1.X64.mem0 .fresh
  u32ToBytes := BigEndian.V0_17_1.X64.u32ToBytes
  bytesToU32 := BigEndian.V0_17_1.X64.bytesToU32
  i16ToBytes := BigEndian.V0_17_1.X64.i16ToBytes
  u64ToHalves := BigEndian.V0_17_1.X64.u64ToHalves
  f32ToBytes := BigEndian.V0_17_1.X64.f32ToBytes
  bytesToF64Bits := BigEndian.V0_17_1.X64.bytesToF64Bits
  f16ToBytes := BigEndian.V0_17_1.X64.f16ToBytes
  packedToBytes := BigEndian.V0_17_1.X64.packedToBytes
  packed16ToBytes := BigEndian.V0_17_1.X64.packed16ToBytes
  setFieldBytes := BigEndian.V0_17_1.X64.setFieldBytes
  fieldFromBytes := BigEndian.V0_17_1.X64.fieldFromBytes
  byteOfU32 := BigEndian.V0_17_1.X64.byteOfU32
  u16FromStoredBytes := BigEndian.V0_17_1.X64.u16FromStoredBytes
  byteOfF64 := BigEndian.V0_17_1.X64.byteOfF64
  externToBytes a b c := (BigEndian.V0_17_1.X64.externToBytes a b c : MemM _)
  unionHalf := BigEndian.V0_17_1.X64.unionHalf
  unionByte := BigEndian.V0_17_1.X64.unionByte

def main : IO Unit := do
  for l in BigEndian.Lines.lines impl do IO.println l

end BigEndian.V0_17_1.X64.Diff
