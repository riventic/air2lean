import BigEndian.S390x.Gen
import BigEndian.X64.Gen

/-! T03: the generated model of `big_endian.zig` on `native.zig`'s inputs, one line per case in
`native.zig`'s format. `check.sh` prints both profiles' lines and compares them with the native
observations: `s390x` (big endian, under emulation) and `x86_64` (little endian).

    lake env lean --run tests/roadmap/big-endian/Diff.lean s390x|x86_64

(with the compiled `BigEndian.<S390x|X64>.Gen` on `LEAN_PATH`). -/

open Zig

/-- The translated functions of one profile. The two translations have the same signatures. -/
structure Impl where
  mem0 : Mem
  u32ToBytes : BitVec 32 → Result (Vector (BitVec 8) 4)
  bytesToU32 : Vector (BitVec 8) 4 → Result (BitVec 32)
  i16ToBytes : BitVec 16 → Result (Vector (BitVec 8) 2)
  u64ToHalves : BitVec 64 → Result (Vector (BitVec 32) 2)
  f32ToBytes : F32 → Result (Vector (BitVec 8) 4)
  bytesToF64Bits : Vector (BitVec 8) 8 → Result (BitVec 64)
  f16ToBytes : F16 → Result (Vector (BitVec 8) 2)
  packedToBytes : BitVec 32 → Result (Vector (BitVec 8) 4)
  packed16ToBytes : BitVec 12 → BitVec 4 → Result (Vector (BitVec 8) 2)
  setFieldBytes : BitVec 32 → BitVec 12 → MemM (Vector (BitVec 8) 4)
  fieldFromBytes : BitVec 8 → BitVec 8 → BitVec 8 → BitVec 8 → MemM (BitVec 12)
  byteOfU32 : BitVec 32 → BitVec 64 → MemM (BitVec 8)
  u16FromStoredBytes : BitVec 8 → BitVec 8 → MemM (BitVec 16)
  byteOfF64 : F64 → BitVec 64 → MemM (BitVec 8)
  vecByte : BitVec 16 → BitVec 16 → BitVec 64 → MemM (BitVec 8)
  vecLane0FromBytes : Vector (BitVec 8) 8 → MemM (BitVec 32)
  externToBytes : BitVec 16 → BitVec 16 → BitVec 32 → Result (Vector (BitVec 8) 8)
  unionHalf : BitVec 32 → MemM (BitVec 16)
  unionByte : BitVec 32 → BitVec 64 → MemM (BitVec 8)

open BigEndian.S390x in
def s390x : Impl := { mem0, u32ToBytes, bytesToU32, i16ToBytes, u64ToHalves, f32ToBytes,
  bytesToF64Bits, f16ToBytes, packedToBytes, packed16ToBytes, setFieldBytes, fieldFromBytes,
  byteOfU32, u16FromStoredBytes, byteOfF64, vecByte, vecLane0FromBytes, externToBytes, unionHalf,
  unionByte }

open BigEndian.X64 in
def x86_64 : Impl := { mem0, u32ToBytes, bytesToU32, i16ToBytes, u64ToHalves, f32ToBytes,
  bytesToF64Bits, f16ToBytes, packedToBytes, packed16ToBytes, setFieldBytes, fieldFromBytes,
  byteOfU32, u16FromStoredBytes, byteOfF64, vecByte, vecLane0FromBytes, externToBytes, unionHalf,
  unionByte }

/-- A printable result: an integer, or the items of an array. -/
class Show (α : Type) where
  show : α → String

instance {n : Nat} : Show (BitVec n) := ⟨fun v => s!" {v.toNat}"⟩
instance {α : Type} {k : Nat} [Show α] : Show (Vector α k) := ⟨fun v => String.join (v.toList.map Show.show)⟩

def resultStr {α : Type} [Show α] (r : Result α) : String :=
  match r.run with
  | some (.ok v) => Show.show v
  | some (.error e) => s!" error {repr e}"
  | none => " none"

def line {α : Type} [Show α] (name : String) (args : List String) (r : Result α) : String :=
  s!"{name}{String.join (args.map (" " ++ ·))} ->{resultStr r}"

def runMem {α : Type} (m : Mem) (x : MemM α) : Result α := do
  let (v, _) ← x.run m
  pure v

/-- The cases of `native.zig`, in its order. -/
def lines (f : Impl) : List String := Id.run do
  let run {α : Type} (x : MemM α) : Result α := runMem f.mem0 x
  let mut out : Array String := #[]
  for x in [0x01020304, 0xdeadbeef, 0, 0xffffffff, 0x80000001] do
    let xs := [toString x]
    out := out.push (line "u32ToBytes" xs (f.u32ToBytes (BitVec.ofNat 32 x)))
    out := out.push (line "packedToBytes" xs (f.packedToBytes (BitVec.ofNat 32 x)))
    out := out.push (line "unionHalf" xs (run (f.unionHalf (BitVec.ofNat 32 x))))
    for i in [0, 1, 2, 3] do
      out := out.push (line "byteOfU32" [toString x, toString i]
        (run (f.byteOfU32 (BitVec.ofNat 32 x) (BitVec.ofNat 64 i))))
      out := out.push (line "unionByte" [toString x, toString i]
        (run (f.unionByte (BitVec.ofNat 32 x) (BitVec.ofNat 64 i))))
    for v in [0, 0xabc, 0xfff] do
      out := out.push (line "setFieldBytes" [toString x, toString v]
        (run (f.setFieldBytes (BitVec.ofNat 32 x) (BitVec.ofNat 12 v))))
  for q in [[1, 2, 3, 4], [0xff, 0, 0x80, 0x7f], [0x12, 0x34, 0x56, 0x78]] do
    let b (i : Nat) : BitVec 8 := BitVec.ofNat 8 (q.getD i 0)
    let qs := q.map toString
    out := out.push (line "bytesToU32" qs (f.bytesToU32 #v[b 0, b 1, b 2, b 3]))
    out := out.push (line "fieldFromBytes" qs (run (f.fieldFromBytes (b 0) (b 1) (b 2) (b 3))))
    out := out.push (line "u16FromStoredBytes" (qs.take 2) (run (f.u16FromStoredBytes (b 0) (b 1))))
  for x in [(0 : Int), 1, -2, 0x1234, -32768] do
    out := out.push (line "i16ToBytes" [toString x] (f.i16ToBytes (BitVec.ofInt 16 x)))
  for x in [0x0102030405060708, 0xfedcba9876543210] do
    out := out.push (line "u64ToHalves" [toString x] (f.u64ToHalves (BitVec.ofNat 64 x)))
  for bits in [0x3f800000, 0xc0490fdb, 0x00000001] do
    out := out.push (line "f32ToBytes" [toString bits] (f.f32ToBytes ⟨BitVec.ofNat 32 bits⟩))
  for bits in [0x3c00, 0xc000, 0x7bff] do
    out := out.push (line "f16ToBytes" [toString bits] (f.f16ToBytes ⟨BitVec.ofNat 16 bits⟩))
  for b in [[0x3f, 0xf0, 0, 0, 0, 0, 0, 0], [1, 2, 3, 4, 5, 6, 7, 8]] do
    let v : Vector (BitVec 8) 8 := ⟨(b.map (BitVec.ofNat 8)).toArray.extract 0 8 ++
      Array.replicate (8 - b.length) 0, by simp⟩
    out := out.push (line "bytesToF64Bits" (b.map toString) (f.bytesToF64Bits v))
    out := out.push (line "vecLane0FromBytes" (b.map toString) (run (f.vecLane0FromBytes v)))
  for bits in [0x3ff0000000000000, 0x400921fb54442d18] do
    for i in [0, 1, 2, 3, 4, 5, 6, 7] do
      out := out.push (line "byteOfF64" [toString bits, toString i]
        (run (f.byteOfF64 ⟨BitVec.ofNat 64 bits⟩ (BitVec.ofNat 64 i))))
  for (a, b) in [(0x0102, 0x0304), (0xffff, 0)] do
    for i in [0, 1, 2, 3] do
      out := out.push (line "vecByte" [toString a, toString b, toString i]
        (run (f.vecByte (BitVec.ofNat 16 a) (BitVec.ofNat 16 b) (BitVec.ofNat 64 i))))
    out := out.push (line "externToBytes" [toString a, toString b, toString 0xa1b2c3d4]
      (f.externToBytes (BitVec.ofNat 16 a) (BitVec.ofNat 16 b) 0xa1b2c3d4))
  for (lo, hi) in [(0xabc, 0xd), (0, 0xf), (0xfff, 0)] do
    out := out.push (line "packed16ToBytes" [toString lo, toString hi]
      (f.packed16ToBytes (BitVec.ofNat 12 lo) (BitVec.ofNat 4 hi)))
  return out.toList

def main (args : List String) : IO UInt32 := do
  let impl ← match args with
    | ["s390x"] => pure s390x
    | ["x86_64"] => pure x86_64
    | _ => throw (IO.userError "usage: Diff.lean s390x|x86_64")
  for l in lines impl do IO.println l
  return 0
