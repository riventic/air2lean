-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.16-musl","zig_version":"0.15.2"}}
import ZigLean


namespace NanBits

structure FU where
  bytes : Vector Zig.Byte 4
  deriving Repr, Inhabited, DecidableEq

def FU.get_f (u : FU) : Zig.Result (Zig.F32) := Zig.Raw.get (Zig.F32) u.bytes

def FU.modify_f (g : Zig.F32 → Zig.F32) (u : FU) : FU :=
  ⟨Zig.Raw.set u.bytes (g (Zig.Raw.getD (Zig.Raw.get (Zig.F32) u.bytes)))⟩

def FU.get_i (u : FU) : Zig.Result (BitVec 32) := Zig.Raw.get (BitVec 32) u.bytes

def FU.modify_i (g : BitVec 32 → BitVec 32) (u : FU) : FU :=
  ⟨Zig.Raw.set u.bytes (g (Zig.Raw.getD (Zig.Raw.get (BitVec 32) u.bytes)))⟩

instance : Zig.Enc FU where
  size := 4
  align := 4
  encode v := v.bytes.toArray
  decode bs := pure ⟨Zig.Raw.ofArray 4 bs⟩

structure FS where
  f : Zig.F32
  k : BitVec 32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc FS where
  size := 8
  align := 4
  encode v := Zig.Enc.fields 8 [(0, Zig.Enc.encode v.f), (4, Zig.Enc.encode v.k)]
  decode bs := do pure { f := ← Zig.Enc.decodeAt bs 0, k := ← Zig.Enc.decodeAt bs 4 }

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ [
  -- 0: nan_bits.gnan
  ((Zig.Enc.encode (2141192193 : BitVec 32)), 4, .global),
  -- 1: nan_bits.g32
  (Zig.Enc.encode ((Zig.Float.ofBits (0 : BitVec 32) : Zig.F32) : Zig.F32), 4, .global),
  -- 2: nan_bits.g64
  (Zig.Enc.encode ((Zig.Float.ofBits (0 : BitVec 64) : Zig.F64) : Zig.F64), 8, .global)]

structure arrayCastLocals where
  deriving Inhabited

inductive arrayCastExit where
  | ret (v : BitVec 64)

def arrayCast (p0 : Zig.F32) (p1 : Zig.F32) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i2 ← pure (Zig.Float.div p0 p1)
    let i3 ← pure (#v[i2, (Zig.Float.ofBits (1065353216 : BitVec 32) : Zig.F32)] : Vector (Zig.F32) 2)
    let i4 ← Zig.reprCast (BitVec 64) (i3 : Vector (Zig.F32) 2)
    pure (.ret i4)) : Zig.M arrayCastLocals arrayCastExit).run' (default : arrayCastLocals)
  match e with
  | .ret v => pure v

structure constGlobalLocals where
  deriving Inhabited

inductive constGlobalExit where
  | ret (v : BitVec 32)

def constGlobal  : Zig.MemM (BitVec 32) := do
  let e ← ((do
    let i0 ← Zig.load (BitVec 32) 4 (⟨some 0, 0⟩ : Zig.Ptr)
    pure (.ret i0)) : Zig.MM constGlobalLocals constGlobalExit).run' (default : constGlobalLocals)
  match e with
  | .ret v => pure v

structure constStoreLocals where
  deriving Inhabited

inductive constStoreExit where
  | ret (v : BitVec 32)

def constStore  : Zig.MemM (BitVec 32) := do
  let e ← ((do
    Zig.storeBytes (⟨some 1, 0⟩ : Zig.Ptr) 4 (Zig.Enc.encode (2141192194 : BitVec 32))
    let i1 ← Zig.load (BitVec 32) 4 (⟨some 1, 0⟩ : Zig.Ptr)
    pure (.ret i1)) : Zig.MM constStoreLocals constStoreExit).run' (default : constStoreLocals)
  match e with
  | .ret v => pure v

structure copyBytesLocals where
  local3 : Zig.Ptr
  i : Zig.Ptr
  deriving Inhabited

inductive copyBytesExit where
  | ret (v : BitVec 32)
  | br17

def copyBytes (p0 : Zig.F32) (p1 : Zig.F32) : Zig.MemM (BitVec 32) := do
  let s6 ← Zig.allocStack 4 4
  let s3 ← Zig.allocStack 4 4
  let e ← ((do
    let i2 ← pure (Zig.Float.div p0 p1)
    let i3 ← pure (← get).local3
    Zig.store (α := Zig.F32) 4 i3 i2
    let i5 ← pure (i3)
    let i6 ← pure (← get).i
    Zig.store (α := BitVec 32) 4 i6 (0 : BitVec 32)
    let i8 ← pure (i6)
    let i9 ← pure (i5)
    let i10 ← pure (i8)
    let i11 ← pure (i9)
    let i12 ← Zig.callM (Zig.ptrProject i11 (·.elem 1 (4 : BitVec 64)))
    let i13 ← Zig.callM (Zig.ptrProject i10 (·.elem 1 (4 : BitVec 64)))
    let i14 ← Zig.callM (Zig.ptrLe i12 i10)
    let i15 ← Zig.callM (Zig.ptrLe i13 i9)
    let i16 ← pure (i14 || i15)
    match ← ((do
      if i16 then (do
        pure .br17)
      else (do
        throw .panic)) : Zig.MM copyBytesLocals copyBytesExit) with
    | .br17 => (do
      Zig.callM (Zig.memcpy 1 1 1 i8 i9 (4 : BitVec 64) (4 : BitVec 64))
      let i23 ← Zig.load (BitVec 32) 4 i6
      pure (.ret i23))
    | e => pure e) : Zig.MM copyBytesLocals copyBytesExit).run' { (default : copyBytesLocals) with i := s6, local3 := s3 }
  Zig.free s3
  Zig.free s6
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure finiteBitsLocals where
  deriving Inhabited

inductive finiteBitsExit where
  | ret (v : BitVec 32)

def finiteBits (p0 : Zig.F32) (p1 : Zig.F32) : Zig.MemM (BitVec 32) := do
  let e ← ((do
    let i2 ← pure (Zig.Float.div p0 p1)
    Zig.store (α := Zig.F32) 4 (⟨some 1, 0⟩ : Zig.Ptr) i2
    let i4 ← Zig.load (BitVec 32) 4 (⟨some 1, 0⟩ : Zig.Ptr)
    pure (.ret i4)) : Zig.MM finiteBitsLocals finiteBitsExit).run' (default : finiteBitsLocals)
  match e with
  | .ret v => pure v

structure reloadIsNaNLocals where
  deriving Inhabited

inductive reloadIsNaNExit where
  | ret (v : Bool)

def reloadIsNaN (p0 : Zig.F32) (p1 : Zig.F32) : Zig.MemM (Bool) := do
  let e ← ((do
    let i2 ← pure (Zig.Float.div p0 p1)
    Zig.store (α := Zig.F32) 4 (⟨some 1, 0⟩ : Zig.Ptr) i2
    let i4 ← Zig.load (Zig.F32) 4 (⟨some 1, 0⟩ : Zig.Ptr)
    let i5 ← Zig.load (Zig.F32) 4 (⟨some 1, 0⟩ : Zig.Ptr)
    let i6 ← pure (Zig.Float.ne i4 i5)
    pure (.ret i6)) : Zig.MM reloadIsNaNLocals reloadIsNaNExit).run' (default : reloadIsNaNLocals)
  match e with
  | .ret v => pure v

structure storeLoadLocals where
  deriving Inhabited

inductive storeLoadExit where
  | ret (v : BitVec 32)

def storeLoad (p0 : Zig.F32) (p1 : Zig.F32) : Zig.MemM (BitVec 32) := do
  let e ← ((do
    let i2 ← pure (Zig.Float.div p0 p1)
    Zig.store (α := Zig.F32) 4 (⟨some 1, 0⟩ : Zig.Ptr) i2
    let i4 ← Zig.load (BitVec 32) 4 (⟨some 1, 0⟩ : Zig.Ptr)
    pure (.ret i4)) : Zig.MM storeLoadLocals storeLoadExit).run' (default : storeLoadLocals)
  match e with
  | .ret v => pure v

structure storeLoad64Locals where
  deriving Inhabited

inductive storeLoad64Exit where
  | ret (v : BitVec 64)

def storeLoad64 (p0 : Zig.F64) (p1 : Zig.F64) : Zig.MemM (BitVec 64) := do
  let e ← ((do
    let i2 ← pure (Zig.Float.div p0 p1)
    Zig.store (α := Zig.F64) 8 (⟨some 2, 0⟩ : Zig.Ptr) i2
    let i4 ← Zig.load (BitVec 64) 8 (⟨some 2, 0⟩ : Zig.Ptr)
    pure (.ret i4)) : Zig.MM storeLoad64Locals storeLoad64Exit).run' (default : storeLoad64Locals)
  match e with
  | .ret v => pure v

structure structViewLocals where
  local2 : Zig.Ptr
  deriving Inhabited

inductive structViewExit where
  | ret (v : BitVec 64)

def structView (p0 : Zig.F32) (p1 : Zig.F32) : Zig.MemM (BitVec 64) := do
  let s2 ← Zig.allocStack 8 4
  let e ← ((do
    let i2 ← pure (← get).local2
    let i3 ← pure i2
    let i4 ← pure (Zig.Float.div p0 p1)
    Zig.store (α := Zig.F32) 4 i3 i4
    let i6 ← Zig.callM (Zig.ptrProject i2 (·.add 4))
    Zig.store (α := BitVec 32) 4 i6 (7 : BitVec 32)
    let i8 ← pure (i2)
    let i9 ← pure (i8)
    let i10 ← Zig.load (BitVec 64) 4 i9
    pure (.ret i10)) : Zig.MM structViewLocals structViewExit).run' { (default : structViewLocals) with local2 := s2 }
  Zig.free s2
  match e with
  | .ret v => pure v

structure sumBitsLocals where
  deriving Inhabited

inductive sumBitsExit where
  | ret (v : BitVec 32)

def sumBits (p0 : Zig.F32) (p1 : Zig.F32) : Zig.MemM (BitVec 32) := do
  let e ← ((do
    let i2 ← pure (Zig.Float.add p0 p1)
    Zig.store (α := Zig.F32) 4 (⟨some 1, 0⟩ : Zig.Ptr) i2
    let i4 ← Zig.load (BitVec 32) 4 (⟨some 1, 0⟩ : Zig.Ptr)
    pure (.ret i4)) : Zig.MM sumBitsLocals sumBitsExit).run' (default : sumBitsLocals)
  match e with
  | .ret v => pure v

structure unionViewLocals where
  local2 : FU
  deriving Inhabited

inductive unionViewExit where
  | ret (v : BitVec 32)

def unionView (p0 : Zig.F32) (p1 : Zig.F32) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i4 ← pure (Zig.Float.div p0 p1)
    modify (fun s => { s with local2 := (FU.modify_f (fun _ => i4) s.local2) })
    let i7 ← pure ((← get).local2)
    let i8 ← Zig.call (FU.get_i i7)
    pure (.ret i8)) : Zig.M unionViewLocals unionViewExit).run' (default : unionViewLocals)
  match e with
  | .ret v => pure v

structure vectorCastLocals where
  deriving Inhabited

inductive vectorCastExit where
  | ret (v : BitVec 64)

def vectorCast (p0 : Zig.F32) (p1 : Zig.F32) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i2 ← pure (Zig.Float.div p0 p1)
    let i3 ← pure ((⟨#v[i2, (Zig.Float.ofBits (1065353216 : BitVec 32) : Zig.F32)]⟩ : Zig.Vec (Zig.F32) 2))
    let i4 ← Zig.reprCast (BitVec 64) (i3 : Zig.Vec (Zig.F32) 2)
    pure (.ret i4)) : Zig.M vectorCastLocals vectorCastExit).run' (default : vectorCastLocals)
  match e with
  | .ret v => pure v

end NanBits