-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.4.19...6.13.4-musl","zig_version":"0.14.1"}}
import ZigLean


namespace PackedCasts

structure W where
  x : Zig.F32
  y : BitVec 3
  z : BitVec 29
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Packed W 64 where
  toBits v := ((Zig.Packed.toBits v.x).setWidth 64 <<< 0) ||| ((Zig.Packed.toBits v.y).setWidth 64 <<< 32) ||| ((Zig.Packed.toBits v.z).setWidth 64 <<< 35)
  ofBits b := { x := Zig.Packed.get b 0, y := Zig.Packed.get b 32, z := Zig.Packed.get b 35 }
  mask v := ((Zig.Packed.mask v.x).setWidth 64 <<< 0) ||| ((BitVec.allOnes 3).setWidth 64 <<< 32) ||| ((BitVec.allOnes 29).setWidth 64 <<< 35)

instance : Zig.Enc W where
  size := 8
  align := 8
  encode v := Zig.Packed.encodeOf .little v
  decode bs := do
    let b : BitVec 64 ← Zig.Enc.decode bs
    Zig.Packed.ofBits? b

structure Half where
  lo : BitVec 8
  hi : BitVec 8
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Packed Half 16 where
  toBits v := ((Zig.Packed.toBits v.lo).setWidth 16 <<< 0) ||| ((Zig.Packed.toBits v.hi).setWidth 16 <<< 8)
  ofBits b := { lo := Zig.Packed.get b 0, hi := Zig.Packed.get b 8 }

instance : Zig.Enc Half where
  size := 2
  align := 2
  encode v := Zig.Enc.encode (Zig.Packed.toBits v)
  decode bs := do
    let b : BitVec 16 ← Zig.Enc.decode bs
    Zig.Packed.ofBits? b

structure U where
  bytes : Vector Zig.Byte 2
  deriving Repr, Inhabited, DecidableEq

def U.get_i (u : U) : Zig.Result (BitVec 16) := Zig.PackedU.get (BitVec 16) u.bytes

def U.modify_i (g : BitVec 16 → BitVec 16) (u : U) : U :=
  ⟨Zig.PackedU.set u.bytes (g (Zig.Raw.getD (Zig.PackedU.get (BitVec 16) u.bytes)))⟩

def U.get_h (u : U) : Zig.Result (Zig.F16) := Zig.PackedU.get (Zig.F16) u.bytes

def U.modify_h (g : Zig.F16 → Zig.F16) (u : U) : U :=
  ⟨Zig.PackedU.set u.bytes (g (Zig.Raw.getD (Zig.PackedU.get (Zig.F16) u.bytes)))⟩

def U.get_p (u : U) : Zig.Result (Half) := Zig.PackedU.get (Half) u.bytes

def U.modify_p (g : Half → Half) (u : U) : U :=
  ⟨Zig.PackedU.set u.bytes (g (Zig.Raw.getD (Zig.PackedU.get (Half) u.bytes)))⟩

instance : Zig.Packed U 16 where
  toBits u := Zig.PackedU.bitsOf 16 u.bytes.toArray
  ofBits b := ⟨Zig.Raw.ofArray 2 (Zig.intBytes b)⟩
  mask u := Zig.PackedU.maskOf 16 u.bytes.toArray

instance : Zig.Enc U where
  size := 2
  align := 2
  encode v := v.bytes.toArray
  decode bs := pure ⟨Zig.Raw.ofArray 2 bs⟩

inductive Mode where
  | off
  | low
  | high
  deriving Repr, Inhabited, DecidableEq

def Mode.toBits : Mode → BitVec 2
  | .off => (0 : BitVec 2)
  | .low => (1 : BitVec 2)
  | .high => (2 : BitVec 2)

def Mode.ofInt? (v : Int) : Option Mode :=
  if v = 0 then Option.some .off else if v = 1 then Option.some .low else if v = 2 then Option.some .high else Option.none

def Mode.isNamed (_ : Mode) : Bool := true

instance : Zig.Packed Mode 2 where
  toBits := Mode.toBits
  ofBits b := (Mode.ofInt? (Zig.val false b)).getD default
  valid b := (Mode.ofInt? (Zig.val false b)).isSome

instance : Zig.Enc Mode where
  size := 1
  align := 1
  encode v := Zig.Enc.encode v.toBits
  decode bs := do
    let b : BitVec 2 ← Zig.Enc.decode bs
    match Mode.ofInt? (Zig.val false b) with
    | some v => pure v
    | none => throw .illegal

structure R where
  a : BitVec 4
  u : U
  f : Zig.F16
  on : Bool
  mode : Mode
  pad : BitVec 1
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Packed R 40 where
  toBits v := ((Zig.Packed.toBits v.a).setWidth 40 <<< 0) ||| ((Zig.Packed.toBits v.u).setWidth 40 <<< 4) ||| ((Zig.Packed.toBits v.f).setWidth 40 <<< 20) ||| ((Zig.Packed.toBits v.on).setWidth 40 <<< 36) ||| ((Zig.Packed.toBits v.mode).setWidth 40 <<< 37) ||| ((Zig.Packed.toBits v.pad).setWidth 40 <<< 39)
  ofBits b := { a := Zig.Packed.get b 0, u := Zig.Packed.get b 4, f := Zig.Packed.get b 20, on := Zig.Packed.get b 36, mode := Zig.Packed.get b 37, pad := Zig.Packed.get b 39 }
  valid b := Zig.Packed.validAt (Mode) b 37
  mask v := ((BitVec.allOnes 4).setWidth 40 <<< 0) ||| ((Zig.Packed.mask v.u).setWidth 40 <<< 4) ||| ((Zig.Packed.mask v.f).setWidth 40 <<< 20) ||| ((BitVec.allOnes 1).setWidth 40 <<< 36) ||| ((BitVec.allOnes 2).setWidth 40 <<< 37) ||| ((BitVec.allOnes 1).setWidth 40 <<< 39)

instance : Zig.Enc R where
  size := 8
  align := 8
  encode v := Zig.Packed.encodeOf .little v
  decode bs := do
    let b : BitVec 40 ← Zig.Enc.decode bs
    Zig.Packed.ofBits? b

inductive UTag where
  | i
  | h
  | p
  deriving Repr, Inhabited, DecidableEq

def UTag.toBits : UTag → BitVec 2
  | .i => (0 : BitVec 2)
  | .h => (1 : BitVec 2)
  | .p => (2 : BitVec 2)

def UTag.ofInt? (v : Int) : Option UTag :=
  if v = 0 then Option.some .i else if v = 1 then Option.some .h else if v = 2 then Option.some .p else Option.none

def UTag.isNamed (_ : UTag) : Bool := true

instance : Zig.Packed UTag 2 where
  toBits := UTag.toBits
  ofBits b := (UTag.ofInt? (Zig.val false b)).getD default
  valid b := (UTag.ofInt? (Zig.val false b)).isSome

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ [
  -- 0: packed_casts.r
  (Array.replicate (Zig.Enc.size (R)) .undef, 8, .global),
  -- 1: packed_casts.w
  (Array.replicate (Zig.Enc.size (W)) .undef, 8, .global)]

structure bytesToULocals where
  deriving Inhabited

inductive bytesToUExit where
  | ret (v : U)

def bytesToU (p0 : Vector (BitVec 8) 2) : Zig.Result (U) := do
  let e ← ((do
    let i1 ← Zig.reprCast (U) (p0 : Vector (BitVec 8) 2)
    pure (.ret i1)) : Zig.M bytesToULocals bytesToUExit).run' (default : bytesToULocals)
  match e with
  | .ret v => pure v

structure f16ToULocals where
  deriving Inhabited

inductive f16ToUExit where
  | ret (v : U)

def f16ToU (p0 : Zig.F16) : Zig.Result (U) := do
  let e ← ((do
    let i1 ← Zig.Packed.bitCast (U) (p0 : Zig.F16)
    pure (.ret i1)) : Zig.M f16ToULocals f16ToUExit).run' (default : f16ToULocals)
  match e with
  | .ret v => pure v

structure floatFieldLocals where
  local1 : R
  deriving Inhabited

inductive floatFieldExit where
  | ret (v : BitVec 40)

def floatField (p0 : Zig.F16) : Zig.Result (BitVec 40) := do
  let e ← ((do
    modify (fun s => { s with local1 := { s.local1 with a := (1 : BitVec 4) } })
    modify (fun s => { s with local1 := { s.local1 with u := (⟨Zig.PackedU.init 2 ((2 : BitVec 16) : BitVec 16)⟩ : U) } })
    modify (fun s => { s with local1 := { s.local1 with f := p0 } })
    modify (fun s => { s with local1 := { s.local1 with on := false } })
    modify (fun s => { s with local1 := { s.local1 with mode := Mode.off } })
    modify (fun s => { s with local1 := { s.local1 with pad := (0 : BitVec 1) } })
    let i15 ← pure ((← get).local1)
    let i16 ← Zig.Packed.toBits? i15
    pure (.ret i16)) : Zig.M floatFieldLocals floatFieldExit).run' (default : floatFieldLocals)
  match e with
  | .ret v => pure v

structure floatInPlaceLocals where
  deriving Inhabited

inductive floatInPlaceExit where
  | ret (v : Zig.F16)

def floatInPlace (p0 : Zig.F16) : Zig.MemM (Zig.F16) := do
  let e ← ((do
    Zig.store (α := R) 8 (⟨some 0, 0⟩ : Zig.Ptr) ({ a := (0 : BitVec 4), u := (Zig.Packed.ofBits (0 : BitVec 16) : U), f := (Zig.Float.ofBits (0 : BitVec 16) : Zig.F16), on := false, mode := Mode.off, pad := (0 : BitVec 1) } : R)
    Zig.storeBits (α := Zig.F16) 5 8 20 (⟨some 0, 0⟩ : Zig.Ptr) p0
    let i3 ← Zig.load (R) 8 (⟨some 0, 0⟩ : Zig.Ptr)
    let i4 ← pure ((i3).f)
    let i5 ← pure (Zig.Float.mul i4 (Zig.Float.ofBits (16384 : BitVec 16) : Zig.F16))
    Zig.storeBits (α := Zig.F16) 5 8 20 (⟨some 0, 0⟩ : Zig.Ptr) i5
    let i7 ← Zig.load (R) 8 (⟨some 0, 0⟩ : Zig.Ptr)
    let i8 ← pure ((i7).f)
    pure (.ret i8)) : Zig.MM floatInPlaceLocals floatInPlaceExit).run' (default : floatInPlaceLocals)
  match e with
  | .ret v => pure v

structure floatKeepsNeighboursLocals where
  deriving Inhabited

inductive floatKeepsNeighboursExit where
  | ret (v : BitVec 8)

def floatKeepsNeighbours  : Zig.MemM (BitVec 8) := do
  let e ← ((do
    Zig.store (α := R) 8 (⟨some 0, 0⟩ : Zig.Ptr) ({ a := (0 : BitVec 4), u := (Zig.Packed.ofBits (0 : BitVec 16) : U), f := (Zig.Float.ofBits (0 : BitVec 16) : Zig.F16), on := false, mode := Mode.off, pad := (0 : BitVec 1) } : R)
    Zig.storeBits (α := Bool) 5 8 36 (⟨some 0, 0⟩ : Zig.Ptr) true
    Zig.storeBits (α := Mode) 5 8 37 (⟨some 0, 0⟩ : Zig.Ptr) Mode.high
    Zig.storeBits (α := Zig.F16) 5 8 20 (⟨some 0, 0⟩ : Zig.Ptr) (Zig.Float.ofBits (49152 : BitVec 16) : Zig.F16)
    let i4 ← Zig.load (R) 8 (⟨some 0, 0⟩ : Zig.Ptr)
    let i5 ← pure ((i4).on)
    let i6 ← pure (if i5 then 1 else 0 : BitVec 1)
    let i7 ← Zig.intCast false false 8 i6 (safe := false)
    let i8 ← Zig.load (R) 8 (⟨some 0, 0⟩ : Zig.Ptr)
    let i9 ← pure ((i8).mode)
    let i10 ← pure (Mode.toBits i9)
    let i11 ← Zig.intCast false false 8 i10 (safe := false)
    let i12 ← pure (Zig.shl i11 (1 : BitVec 3))
    let i13 ← pure (i7 ||| i12)
    pure (.ret i13)) : Zig.MM floatKeepsNeighboursLocals floatKeepsNeighboursExit).run' (default : floatKeepsNeighboursLocals)
  match e with
  | .ret v => pure v

structure floatsToIntLocals where
  deriving Inhabited

inductive floatsToIntExit where
  | ret (v : BitVec 64)

def floatsToInt (p0 : Vector (Zig.F32) 2) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i1 ← Zig.reprCast (BitVec 64) (p0 : Vector (Zig.F32) 2)
    pure (.ret i1)) : Zig.M floatsToIntLocals floatsToIntExit).run' (default : floatsToIntLocals)
  match e with
  | .ret v => pure v

structure halfToF16Locals where
  deriving Inhabited

inductive halfToF16Exit where
  | ret (v : Zig.F16)

def halfToF16 (p0 : Half) : Zig.Result (Zig.F16) := do
  let e ← ((do
    let i1 ← Zig.Packed.bitCast (Zig.F16) (p0 : Half)
    pure (.ret i1)) : Zig.M halfToF16Locals halfToF16Exit).run' (default : halfToF16Locals)
  match e with
  | .ret v => pure v

structure intToFloatsLocals where
  deriving Inhabited

inductive intToFloatsExit where
  | ret (v : Vector (Zig.F32) 2)

def intToFloats (p0 : BitVec 64) : Zig.Result (Vector (Zig.F32) 2) := do
  let e ← ((do
    let i1 ← Zig.reprCast (Vector (Zig.F32) 2) (p0 : BitVec 64)
    pure (.ret i1)) : Zig.M intToFloatsLocals intToFloatsExit).run' (default : intToFloatsLocals)
  match e with
  | .ret v => pure v

structure intToRLocals where
  deriving Inhabited

inductive intToRExit where
  | ret (v : R)

def intToR (p0 : BitVec 40) : Zig.Result (R) := do
  let e ← ((do
    let i1 ← Zig.Packed.ofBits? (α := R) p0
    pure (.ret i1)) : Zig.M intToRLocals intToRExit).run' (default : intToRLocals)
  match e with
  | .ret v => pure v

structure intToVecLocals where
  deriving Inhabited

inductive intToVecExit where
  | ret (v : Zig.Vec (Zig.F32) 2)

def intToVec (p0 : BitVec 64) : Zig.Result (Zig.Vec (Zig.F32) 2) := do
  let e ← ((do
    let i1 ← Zig.reprCast (Zig.Vec (Zig.F32) 2) (p0 : BitVec 64)
    pure (.ret i1)) : Zig.M intToVecLocals intToVecExit).run' (default : intToVecLocals)
  match e with
  | .ret v => pure v

structure makeRLocals where
  local2 : R
  deriving Inhabited

inductive makeRExit where
  | ret (v : BitVec 40)

def makeR (p0 : BitVec 4) (p1 : Zig.F16) : Zig.Result (BitVec 40) := do
  let e ← ((do
    modify (fun s => { s with local2 := { s.local2 with a := p0 } })
    modify (fun s => { s with local2 := { s.local2 with u := (U.modify_h (fun _ => p1) (s.local2).u) } })
    modify (fun s => { s with local2 := { s.local2 with f := p1 } })
    modify (fun s => { s with local2 := { s.local2 with on := false } })
    modify (fun s => { s with local2 := { s.local2 with mode := Mode.low } })
    modify (fun s => { s with local2 := { s.local2 with pad := (0 : BitVec 1) } })
    let i18 ← pure ((← get).local2)
    let i19 ← Zig.Packed.toBits? i18
    pure (.ret i19)) : Zig.M makeRLocals makeRExit).run' (default : makeRLocals)
  match e with
  | .ret v => pure v

structure rToIntLocals where
  deriving Inhabited

inductive rToIntExit where
  | ret (v : BitVec 40)

def rToInt (p0 : R) : Zig.Result (BitVec 40) := do
  let e ← ((do
    let i1 ← Zig.Packed.toBits? p0
    pure (.ret i1)) : Zig.M rToIntLocals rToIntExit).run' (default : rToIntLocals)
  match e with
  | .ret v => pure v

structure setFloatLocals where
  deriving Inhabited

inductive setFloatExit where
  | ret (v : BitVec 16)

def setFloat  : Zig.MemM (BitVec 16) := do
  let e ← ((do
    Zig.store (α := R) 8 (⟨some 0, 0⟩ : Zig.Ptr) ({ a := (0 : BitVec 4), u := (Zig.Packed.ofBits (0 : BitVec 16) : U), f := (Zig.Float.ofBits (0 : BitVec 16) : Zig.F16), on := false, mode := Mode.off, pad := (0 : BitVec 1) } : R)
    Zig.storeBits (α := Zig.F16) 5 8 20 (⟨some 0, 0⟩ : Zig.Ptr) (Zig.Float.ofBits (15872 : BitVec 16) : Zig.F16)
    let i2 ← Zig.load (R) 8 (⟨some 0, 0⟩ : Zig.Ptr)
    let i3 ← pure ((i2).f)
    let i4 ← Zig.Float.toBits? i3
    pure (.ret i4)) : Zig.MM setFloatLocals setFloatExit).run' (default : setFloatLocals)
  match e with
  | .ret v => pure v

structure setUnionLocals where
  deriving Inhabited

inductive setUnionExit where
  | ret (v : BitVec 16)

def setUnion  : Zig.MemM (BitVec 16) := do
  let e ← ((do
    Zig.store (α := R) 8 (⟨some 0, 0⟩ : Zig.Ptr) ({ a := (0 : BitVec 4), u := (Zig.Packed.ofBits (0 : BitVec 16) : U), f := (Zig.Float.ofBits (0 : BitVec 16) : Zig.F16), on := false, mode := Mode.off, pad := (0 : BitVec 1) } : R)
    Zig.storeBits (α := BitVec 4) 5 8 0 (⟨some 0, 0⟩ : Zig.Ptr) (3 : BitVec 4)
    Zig.storeBits (α := U) 5 8 4 (⟨some 0, 0⟩ : Zig.Ptr) (⟨Zig.PackedU.init 2 ((4660 : BitVec 16) : BitVec 16)⟩ : U)
    let i3 ← Zig.load (R) 8 (⟨some 0, 0⟩ : Zig.Ptr)
    let i4 ← pure ((i3).u)
    let i5 ← Zig.callR (U.get_i i4)
    pure (.ret i5)) : Zig.MM setUnionLocals setUnionExit).run' (default : setUnionLocals)
  match e with
  | .ret v => pure v

structure uToBytesLocals where
  deriving Inhabited

inductive uToBytesExit where
  | ret (v : Vector (BitVec 8) 2)

def uToBytes (p0 : U) : Zig.Result (Vector (BitVec 8) 2) := do
  let e ← ((do
    let i1 ← Zig.reprCast (Vector (BitVec 8) 2) (p0 : U)
    pure (.ret i1)) : Zig.M uToBytesLocals uToBytesExit).run' (default : uToBytesLocals)
  match e with
  | .ret v => pure v

structure uToHalfLocals where
  deriving Inhabited

inductive uToHalfExit where
  | ret (v : Half)

def uToHalf (p0 : U) : Zig.Result (Half) := do
  let e ← ((do
    let i1 ← Zig.Packed.bitCast (Half) (p0 : U)
    pure (.ret i1)) : Zig.M uToHalfLocals uToHalfExit).run' (default : uToHalfLocals)
  match e with
  | .ret v => pure v

structure unionFloatViewLocals where
  deriving Inhabited

inductive unionFloatViewExit where
  | ret (v : BitVec 16)

def unionFloatView  : Zig.MemM (BitVec 16) := do
  let e ← ((do
    Zig.store (α := R) 8 (⟨some 0, 0⟩ : Zig.Ptr) ({ a := (0 : BitVec 4), u := (Zig.Packed.ofBits (0 : BitVec 16) : U), f := (Zig.Float.ofBits (0 : BitVec 16) : Zig.F16), on := false, mode := Mode.off, pad := (0 : BitVec 1) } : R)
    Zig.storeBits (α := U) 5 8 4 (⟨some 0, 0⟩ : Zig.Ptr) (⟨Zig.PackedU.init 2 ((Zig.Float.ofBits (15360 : BitVec 16) : Zig.F16) : Zig.F16)⟩ : U)
    let i2 ← Zig.load (R) 8 (⟨some 0, 0⟩ : Zig.Ptr)
    let i3 ← pure ((i2).u)
    let i4 ← Zig.callR (U.get_i i3)
    pure (.ret i4)) : Zig.MM unionFloatViewLocals unionFloatViewExit).run' (default : unionFloatViewLocals)
  match e with
  | .ret v => pure v

structure unionHalfHiLocals where
  deriving Inhabited

inductive unionHalfHiExit where
  | ret (v : BitVec 8)

def unionHalfHi  : Zig.MemM (BitVec 8) := do
  let e ← ((do
    Zig.store (α := R) 8 (⟨some 0, 0⟩ : Zig.Ptr) ({ a := (0 : BitVec 4), u := (Zig.Packed.ofBits (0 : BitVec 16) : U), f := (Zig.Float.ofBits (0 : BitVec 16) : Zig.F16), on := false, mode := Mode.off, pad := (0 : BitVec 1) } : R)
    Zig.storeBits (α := U) 5 8 4 (⟨some 0, 0⟩ : Zig.Ptr) (⟨Zig.PackedU.init 2 (({ lo := (17 : BitVec 8), hi := (34 : BitVec 8) } : Half) : Half)⟩ : U)
    let i2 ← Zig.load (R) 8 (⟨some 0, 0⟩ : Zig.Ptr)
    let i3 ← pure ((i2).u)
    let i4 ← Zig.callR (U.get_p i3)
    let i5 ← pure ((i4).hi)
    pure (.ret i5)) : Zig.MM unionHalfHiLocals unionHalfHiExit).run' (default : unionHalfHiLocals)
  match e with
  | .ret v => pure v

structure unionKeepsALocals where
  deriving Inhabited

inductive unionKeepsAExit where
  | ret (v : BitVec 4)

def unionKeepsA  : Zig.MemM (BitVec 4) := do
  let e ← ((do
    Zig.store (α := R) 8 (⟨some 0, 0⟩ : Zig.Ptr) ({ a := (0 : BitVec 4), u := (Zig.Packed.ofBits (0 : BitVec 16) : U), f := (Zig.Float.ofBits (0 : BitVec 16) : Zig.F16), on := false, mode := Mode.off, pad := (0 : BitVec 1) } : R)
    Zig.storeBits (α := BitVec 4) 5 8 0 (⟨some 0, 0⟩ : Zig.Ptr) (9 : BitVec 4)
    Zig.storeBits (α := U) 5 8 4 (⟨some 0, 0⟩ : Zig.Ptr) (⟨Zig.PackedU.init 2 ((65535 : BitVec 16) : BitVec 16)⟩ : U)
    let i3 ← Zig.load (R) 8 (⟨some 0, 0⟩ : Zig.Ptr)
    let i4 ← pure ((i3).a)
    pure (.ret i4)) : Zig.MM unionKeepsALocals unionKeepsAExit).run' (default : unionKeepsALocals)
  match e with
  | .ret v => pure v

structure vecToIntLocals where
  deriving Inhabited

inductive vecToIntExit where
  | ret (v : BitVec 64)

def vecToInt (p0 : Zig.Vec (Zig.F32) 2) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i1 ← Zig.reprCast (BitVec 64) (p0 : Zig.Vec (Zig.F32) 2)
    pure (.ret i1)) : Zig.M vecToIntLocals vecToIntExit).run' (default : vecToIntLocals)
  match e with
  | .ret v => pure v

structure wToIntLocals where
  deriving Inhabited

inductive wToIntExit where
  | ret (v : BitVec 64)

def wToInt (p0 : W) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i1 ← Zig.Packed.toBits? p0
    pure (.ret i1)) : Zig.M wToIntLocals wToIntExit).run' (default : wToIntLocals)
  match e with
  | .ret v => pure v

structure wideFloatLocals where
  deriving Inhabited

inductive wideFloatExit where
  | ret (v : Zig.F32)

def wideFloat (p0 : Zig.F32) : Zig.MemM (Zig.F32) := do
  let e ← ((do
    Zig.store (α := W) 8 (⟨some 1, 0⟩ : Zig.Ptr) ({ x := (Zig.Float.ofBits (0 : BitVec 32) : Zig.F32), y := (0 : BitVec 3), z := (0 : BitVec 29) } : W)
    Zig.storeBits (α := BitVec 3) 8 8 32 (⟨some 1, 0⟩ : Zig.Ptr) (5 : BitVec 3)
    Zig.store (α := Zig.F32) 8 (⟨some 1, 0⟩ : Zig.Ptr) p0
    Zig.storeBits (α := BitVec 29) 8 8 35 (⟨some 1, 0⟩ : Zig.Ptr) (7 : BitVec 29)
    let i5 ← Zig.load (W) 8 (⟨some 1, 0⟩ : Zig.Ptr)
    let i6 ← pure ((i5).x)
    pure (.ret i6)) : Zig.MM wideFloatLocals wideFloatExit).run' (default : wideFloatLocals)
  match e with
  | .ret v => pure v

end PackedCasts