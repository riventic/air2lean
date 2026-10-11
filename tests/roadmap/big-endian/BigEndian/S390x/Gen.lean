-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"arch8","endian":"big","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":[],"float_mode":"per-instruction","name":"abi64-be-v1","pointer_bits":64,"schema":12,"target_triple":"s390x-linux.5.10...6.19-musl","zig_version":"0.16.0"}}
import ZigLean


namespace BigEndian.S390x

open scoped Zig.BigEndian

structure U where
  bytes : Vector Zig.Byte 4
  deriving Repr, Inhabited, DecidableEq

def U.get_w (u : U) : Zig.Result (BitVec 32) := Zig.Raw.get (BitVec 32) u.bytes

def U.modify_w (g : BitVec 32 → BitVec 32) (u : U) : U :=
  ⟨Zig.Raw.set u.bytes (g (Zig.Raw.getD (Zig.Raw.get (BitVec 32) u.bytes)))⟩

def U.get_h (u : U) : Zig.Result (Vector (BitVec 16) 2) := Zig.Raw.get (Vector (BitVec 16) 2) u.bytes

def U.modify_h (g : Vector (BitVec 16) 2 → Vector (BitVec 16) 2) (u : U) : U :=
  ⟨Zig.Raw.set u.bytes (g (Zig.Raw.getD (Zig.Raw.get (Vector (BitVec 16) 2) u.bytes)))⟩

def U.get_b (u : U) : Zig.Result (Vector (BitVec 8) 4) := Zig.Raw.get (Vector (BitVec 8) 4) u.bytes

def U.modify_b (g : Vector (BitVec 8) 4 → Vector (BitVec 8) 4) (u : U) : U :=
  ⟨Zig.Raw.set u.bytes (g (Zig.Raw.getD (Zig.Raw.get (Vector (BitVec 8) 4) u.bytes)))⟩

instance : Zig.Enc U where
  size := 4
  align := 4
  encode v := v.bytes.toArray
  decode bs := pure ⟨Zig.Raw.ofArray 4 bs⟩

structure S where
  a : BitVec 16
  b : BitVec 16
  c : BitVec 32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc S where
  size := 8
  align := 4
  encode v := Zig.Enc.fields 8 [(0, Zig.Enc.encode v.a), (2, Zig.Enc.encode v.b), (4, Zig.Enc.encode v.c)]
  decode bs := do pure { a := ← Zig.Enc.decodeAt bs 0, b := ← Zig.Enc.decodeAt bs 2, c := ← Zig.Enc.decodeAt bs 4 }

structure Q where
  lo : BitVec 12
  hi : BitVec 4
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Packed Q 16 where
  toBits v := ((Zig.Packed.toBits v.lo).setWidth 16 <<< 0) ||| ((Zig.Packed.toBits v.hi).setWidth 16 <<< 12)
  ofBits b := { lo := Zig.Packed.get b 0, hi := Zig.Packed.get b 12 }

instance : Zig.Enc Q where
  size := 2
  align := 2
  encode v := Zig.Enc.encode (Zig.Packed.toBits v)
  decode bs := do
    let b : BitVec 16 ← Zig.Enc.decode bs
    Zig.Packed.ofBits? b

structure P where
  a : BitVec 4
  b : BitVec 12
  c : BitVec 16
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Packed P 32 where
  toBits v := ((Zig.Packed.toBits v.a).setWidth 32 <<< 0) ||| ((Zig.Packed.toBits v.b).setWidth 32 <<< 4) ||| ((Zig.Packed.toBits v.c).setWidth 32 <<< 16)
  ofBits b := { a := Zig.Packed.get b 0, b := Zig.Packed.get b 4, c := Zig.Packed.get b 16 }

instance : Zig.Enc P where
  size := 4
  align := 4
  encode v := Zig.Enc.encode (Zig.Packed.toBits v)
  decode bs := do
    let b : BitVec 32 ← Zig.Enc.decode bs
    Zig.Packed.ofBits? b

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ []

structure byteOfF64Locals where
  v : Zig.Ptr
  deriving Inhabited

inductive byteOfF64Exit where
  | ret (v : BitVec 8)
  | br6

def byteOfF64 (p0 : Zig.F64) (p1 : BitVec 64) : Zig.MemM (BitVec 8) := do
  let s2 ← Zig.allocStack 8 8
  let e ← ((do
    let i2 ← pure (← get).v
    Zig.store (α := Zig.F64) 8 i2 p0
    let i4 ← pure (i2)
    let i5 ← pure (Zig.lt false p1 (8 : BitVec 64))
    match ← ((do
      if i5 then (do
        pure .br6)
      else (do
        throw .outOfBounds)) : Zig.MM byteOfF64Locals byteOfF64Exit) with
    | .br6 => (do
      let i11 ← Zig.callM (Zig.load (BitVec 8) 1 (i4.elem 1 p1))
      pure (.ret i11))
    | e => pure e) : Zig.MM byteOfF64Locals byteOfF64Exit).run' { (default : byteOfF64Locals) with v := s2 }
  Zig.free s2
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure byteOfU32Locals where
  v : Zig.Ptr
  deriving Inhabited

inductive byteOfU32Exit where
  | ret (v : BitVec 8)
  | br6

def byteOfU32 (p0 : BitVec 32) (p1 : BitVec 64) : Zig.MemM (BitVec 8) := do
  let s2 ← Zig.allocStack 4 4
  let e ← ((do
    let i2 ← pure (← get).v
    Zig.store (α := BitVec 32) 4 i2 p0
    let i4 ← pure (i2)
    let i5 ← pure (Zig.lt false p1 (4 : BitVec 64))
    match ← ((do
      if i5 then (do
        pure .br6)
      else (do
        throw .outOfBounds)) : Zig.MM byteOfU32Locals byteOfU32Exit) with
    | .br6 => (do
      let i11 ← Zig.callM (Zig.load (BitVec 8) 1 (i4.elem 1 p1))
      pure (.ret i11))
    | e => pure e) : Zig.MM byteOfU32Locals byteOfU32Exit).run' { (default : byteOfU32Locals) with v := s2 }
  Zig.free s2
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure bytesToF64BitsLocals where
  deriving Inhabited

inductive bytesToF64BitsExit where
  | ret (v : BitVec 64)

def bytesToF64Bits (p0 : Vector (BitVec 8) 8) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i1 ← Zig.reprCast (Zig.F64) (p0 : Vector (BitVec 8) 8)
    let i2 ← Zig.Float.toBits? i1
    pure (.ret i2)) : Zig.M bytesToF64BitsLocals bytesToF64BitsExit).run' (default : bytesToF64BitsLocals)
  match e with
  | .ret v => pure v

structure bytesToU32Locals where
  deriving Inhabited

inductive bytesToU32Exit where
  | ret (v : BitVec 32)

def bytesToU32 (p0 : Vector (BitVec 8) 4) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← Zig.reprCast (BitVec 32) (p0 : Vector (BitVec 8) 4)
    pure (.ret i1)) : Zig.M bytesToU32Locals bytesToU32Exit).run' (default : bytesToU32Locals)
  match e with
  | .ret v => pure v

structure externToBytesLocals where
  local3 : S
  deriving Inhabited

inductive externToBytesExit where
  | ret (v : Vector (BitVec 8) 8)

def externToBytes (p0 : BitVec 16) (p1 : BitVec 16) (p2 : BitVec 32) : Zig.Result (Vector (BitVec 8) 8) := do
  let e ← ((do
    modify (fun s => { s with local3 := { s.local3 with a := p0 } })
    modify (fun s => { s with local3 := { s.local3 with b := p1 } })
    modify (fun s => { s with local3 := { s.local3 with c := p2 } })
    let i11 ← pure ((← get).local3)
    let i12 ← Zig.reprCast (Vector (BitVec 8) 8) (i11 : S)
    pure (.ret i12)) : Zig.M externToBytesLocals externToBytesExit).run' (default : externToBytesLocals)
  match e with
  | .ret v => pure v

structure f16ToBytesLocals where
  deriving Inhabited

inductive f16ToBytesExit where
  | ret (v : Vector (BitVec 8) 2)

def f16ToBytes (p0 : Zig.F16) : Zig.Result (Vector (BitVec 8) 2) := do
  let e ← ((do
    let i1 ← Zig.reprCast (Vector (BitVec 8) 2) (p0 : Zig.F16)
    pure (.ret i1)) : Zig.M f16ToBytesLocals f16ToBytesExit).run' (default : f16ToBytesLocals)
  match e with
  | .ret v => pure v

structure f32ToBytesLocals where
  deriving Inhabited

inductive f32ToBytesExit where
  | ret (v : Vector (BitVec 8) 4)

def f32ToBytes (p0 : Zig.F32) : Zig.Result (Vector (BitVec 8) 4) := do
  let e ← ((do
    let i1 ← Zig.reprCast (Vector (BitVec 8) 4) (p0 : Zig.F32)
    pure (.ret i1)) : Zig.M f32ToBytesLocals f32ToBytesExit).run' (default : f32ToBytesLocals)
  match e with
  | .ret v => pure v

structure fieldFromBytesLocals where
  p : Zig.Ptr
  deriving Inhabited

inductive fieldFromBytesExit where
  | ret (v : BitVec 12)

def fieldFromBytes (p0 : BitVec 8) (p1 : BitVec 8) (p2 : BitVec 8) (p3 : BitVec 8) : Zig.MemM (BitVec 12) := do
  let s4 ← Zig.allocStack 4 4
  let e ← ((do
    let i4 ← pure (← get).p
    Zig.store (α := P) 4 i4 (Zig.Packed.ofBits (0 : BitVec 32) : P)
    let i6 ← pure (i4)
    let i7 ← pure i6
    Zig.store (α := BitVec 8) 1 i7 p0
    let i9 ← Zig.callM (Zig.ptrProject i6 (·.elem 1 (1 : BitVec 64)))
    Zig.store (α := BitVec 8) 1 i9 p1
    let i11 ← Zig.callM (Zig.ptrProject i6 (·.elem 1 (2 : BitVec 64)))
    Zig.store (α := BitVec 8) 1 i11 p2
    let i13 ← Zig.callM (Zig.ptrProject i6 (·.elem 1 (3 : BitVec 64)))
    Zig.store (α := BitVec 8) 1 i13 p3
    let i15 ← pure i4
    let i16 ← pure (i15)
    let i17 ← Zig.loadBitsOf .big (BitVec 12) 4 4 4 i16
    pure (.ret i17)) : Zig.MM fieldFromBytesLocals fieldFromBytesExit).run' { (default : fieldFromBytesLocals) with p := s4 }
  Zig.free s4
  match e with
  | .ret v => pure v

structure i16ToBytesLocals where
  deriving Inhabited

inductive i16ToBytesExit where
  | ret (v : Vector (BitVec 8) 2)

def i16ToBytes (p0 : BitVec 16) : Zig.Result (Vector (BitVec 8) 2) := do
  let e ← ((do
    let i1 ← Zig.reprCast (Vector (BitVec 8) 2) (p0 : BitVec 16)
    pure (.ret i1)) : Zig.M i16ToBytesLocals i16ToBytesExit).run' (default : i16ToBytesLocals)
  match e with
  | .ret v => pure v

structure packed16ToBytesLocals where
  local2 : Q
  deriving Inhabited

inductive packed16ToBytesExit where
  | ret (v : Vector (BitVec 8) 2)

def packed16ToBytes (p0 : BitVec 12) (p1 : BitVec 4) : Zig.Result (Vector (BitVec 8) 2) := do
  let e ← ((do
    modify (fun s => { s with local2 := { s.local2 with lo := p0 } })
    modify (fun s => { s with local2 := { s.local2 with hi := p1 } })
    let i8 ← pure ((← get).local2)
    let i9 ← Zig.reprCast (Vector (BitVec 8) 2) (i8 : Q)
    pure (.ret i9)) : Zig.M packed16ToBytesLocals packed16ToBytesExit).run' (default : packed16ToBytesLocals)
  match e with
  | .ret v => pure v

structure packedToBytesLocals where
  deriving Inhabited

inductive packedToBytesExit where
  | ret (v : Vector (BitVec 8) 4)

def packedToBytes (p0 : BitVec 32) : Zig.Result (Vector (BitVec 8) 4) := do
  let e ← ((do
    let i1 ← Zig.Packed.ofBits? (α := P) p0
    let i2 ← Zig.reprCast (Vector (BitVec 8) 4) (i1 : P)
    pure (.ret i2)) : Zig.M packedToBytesLocals packedToBytesExit).run' (default : packedToBytesLocals)
  match e with
  | .ret v => pure v

structure setFieldBytesLocals where
  p : Zig.Ptr
  deriving Inhabited

inductive setFieldBytesExit where
  | ret (v : Vector (BitVec 8) 4)

def setFieldBytes (p0 : BitVec 32) (p1 : BitVec 12) : Zig.MemM (Vector (BitVec 8) 4) := do
  let s2 ← Zig.allocStack 4 4
  let e ← ((do
    let i2 ← pure (← get).p
    let i3 ← Zig.Packed.ofBits? (α := P) p0
    Zig.store (α := P) 4 i2 i3
    let i5 ← pure i2
    Zig.storeBitsOf .big (α := BitVec 12) 4 4 4 i5 p1
    let i7 ← pure (i2)
    let i8 ← Zig.load (Vector (BitVec 8) 4) 1 i7
    pure (.ret i8)) : Zig.MM setFieldBytesLocals setFieldBytesExit).run' { (default : setFieldBytesLocals) with p := s2 }
  Zig.free s2
  match e with
  | .ret v => pure v

structure u16FromStoredBytesLocals where
  v : Zig.Ptr
  deriving Inhabited

inductive u16FromStoredBytesExit where
  | ret (v : BitVec 16)

def u16FromStoredBytes (p0 : BitVec 8) (p1 : BitVec 8) : Zig.MemM (BitVec 16) := do
  let s2 ← Zig.allocStack 2 2
  let e ← ((do
    let i2 ← pure (← get).v
    let i3 ← pure i2
    Zig.store (α := BitVec 8) 2 i3 p0
    let i5 ← Zig.callM (Zig.ptrProject i2 (·.elem 1 (1 : BitVec 64)))
    Zig.store (α := BitVec 8) 1 i5 p1
    let i7 ← pure (i2)
    let i8 ← Zig.load (BitVec 16) 2 i7
    pure (.ret i8)) : Zig.MM u16FromStoredBytesLocals u16FromStoredBytesExit).run' { (default : u16FromStoredBytesLocals) with v := s2 }
  Zig.free s2
  match e with
  | .ret v => pure v

structure u32ToBytesLocals where
  deriving Inhabited

inductive u32ToBytesExit where
  | ret (v : Vector (BitVec 8) 4)

def u32ToBytes (p0 : BitVec 32) : Zig.Result (Vector (BitVec 8) 4) := do
  let e ← ((do
    let i1 ← Zig.reprCast (Vector (BitVec 8) 4) (p0 : BitVec 32)
    pure (.ret i1)) : Zig.M u32ToBytesLocals u32ToBytesExit).run' (default : u32ToBytesLocals)
  match e with
  | .ret v => pure v

structure u64ToHalvesLocals where
  deriving Inhabited

inductive u64ToHalvesExit where
  | ret (v : Vector (BitVec 32) 2)

def u64ToHalves (p0 : BitVec 64) : Zig.Result (Vector (BitVec 32) 2) := do
  let e ← ((do
    let i1 ← Zig.reprCast (Vector (BitVec 32) 2) (p0 : BitVec 64)
    pure (.ret i1)) : Zig.M u64ToHalvesLocals u64ToHalvesExit).run' (default : u64ToHalvesLocals)
  match e with
  | .ret v => pure v

structure unionByteLocals where
  local2 : Zig.Ptr
  deriving Inhabited

inductive unionByteExit where
  | ret (v : BitVec 8)
  | br8

def unionByte (p0 : BitVec 32) (p1 : BitVec 64) : Zig.MemM (BitVec 8) := do
  let s2 ← Zig.allocStack 4 4
  let e ← ((do
    let i2 ← pure (← get).local2
    let i3 ← pure i2
    Zig.store (α := BitVec 32) 4 i3 p0
    let i5 ← pure (i2)
    let i6 ← pure i5
    let i7 ← pure (Zig.lt false p1 (4 : BitVec 64))
    match ← ((do
      if i7 then (do
        pure .br8)
      else (do
        throw .outOfBounds)) : Zig.MM unionByteLocals unionByteExit) with
    | .br8 => (do
      let i13 ← Zig.callM (Zig.load (BitVec 8) 1 (i6.elem 1 p1))
      pure (.ret i13))
    | e => pure e) : Zig.MM unionByteLocals unionByteExit).run' { (default : unionByteLocals) with local2 := s2 }
  Zig.free s2
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure unionHalfLocals where
  local1 : Zig.Ptr
  deriving Inhabited

inductive unionHalfExit where
  | ret (v : BitVec 16)

def unionHalf (p0 : BitVec 32) : Zig.MemM (BitVec 16) := do
  let s1 ← Zig.allocStack 4 4
  let e ← ((do
    let i1 ← pure (← get).local1
    let i2 ← pure i1
    Zig.store (α := BitVec 32) 4 i2 p0
    let i4 ← pure (i1)
    let i5 ← pure i4
    let i6 ← Zig.callM (Zig.load (BitVec 16) 2 (i5.elem 2 (0 : BitVec 64)))
    pure (.ret i6)) : Zig.MM unionHalfLocals unionHalfExit).run' { (default : unionHalfLocals) with local1 := s1 }
  Zig.free s1
  match e with
  | .ret v => pure v

end BigEndian.S390x