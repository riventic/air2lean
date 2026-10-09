-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"unverified","backend":"unverified","build_mode":"unverified","cpu":"unverified","endian":"little","error_layout":"reference-model","error_set_bits":16,"error_tracing":null,"export_stage":"unverified","features":[],"float_mode":"unverified","name":"legacy-abi64-le","pointer_bits":64,"schema":11,"target_triple":"unverified","zig_version":"0.16.0"}}
import ZigLean


namespace PackedFields

structure Inner where
  b : BitVec 4
  c : BitVec 8
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Packed Inner 12 where
  toBits v := ((Zig.Packed.toBits v.b).setWidth 12 <<< 0) ||| ((Zig.Packed.toBits v.c).setWidth 12 <<< 4)
  ofBits b := { b := Zig.Packed.get b 0, c := Zig.Packed.get b 4 }

instance : Zig.Enc Inner where
  size := 2
  align := 2
  encode v := Zig.Enc.encode (Zig.Packed.toBits v)
  decode bs := do
    let b : BitVec 12 ← Zig.Enc.decode bs
    Zig.Packed.ofBits? b

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

structure Reg where
  a : BitVec 4
  inner : Inner
  s : BitVec 5
  on : Bool
  mode : Mode
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Packed Reg 24 where
  toBits v := ((Zig.Packed.toBits v.a).setWidth 24 <<< 0) ||| ((Zig.Packed.toBits v.inner).setWidth 24 <<< 4) ||| ((Zig.Packed.toBits v.s).setWidth 24 <<< 16) ||| ((Zig.Packed.toBits v.on).setWidth 24 <<< 21) ||| ((Zig.Packed.toBits v.mode).setWidth 24 <<< 22)
  ofBits b := { a := Zig.Packed.get b 0, inner := Zig.Packed.get b 4, s := Zig.Packed.get b 16, on := Zig.Packed.get b 21, mode := Zig.Packed.get b 22 }
  valid b := Zig.Packed.validAt (Mode) b 22

instance : Zig.Enc Reg where
  size := 4
  align := 4
  encode v := Zig.Enc.encode (Zig.Packed.toBits v)
  decode bs := do
    let b : BitVec 24 ← Zig.Enc.decode bs
    Zig.Packed.ofBits? b

structure Word where
  bytes : Vector Zig.Byte 4
  deriving Repr, Inhabited, DecidableEq

def Word.get_reg (u : Word) : Zig.Result (Reg) := Zig.PackedU.get (Reg) u.bytes

def Word.modify_reg (g : Reg → Reg) (u : Word) : Word :=
  ⟨Zig.PackedU.set u.bytes (g (Zig.Raw.getD (Zig.PackedU.get (Reg) u.bytes)))⟩

def Word.get_raw (u : Word) : Zig.Result (BitVec 24) := Zig.PackedU.get (BitVec 24) u.bytes

def Word.modify_raw (g : BitVec 24 → BitVec 24) (u : Word) : Word :=
  ⟨Zig.PackedU.set u.bytes (g (Zig.Raw.getD (Zig.PackedU.get (BitVec 24) u.bytes)))⟩

instance : Zig.Enc Word where
  size := 4
  align := 4
  encode v := v.bytes.toArray
  decode bs := pure ⟨Zig.Raw.ofArray 4 bs⟩

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ [
  -- 0: packed_fields.reg
  (Array.replicate (Zig.Enc.size (Reg)) .undef, 4, .global),
  -- 1: packed_fields.word
  (Array.replicate (Zig.Enc.size (Word)) .undef, 4, .global)]

structure boolOnLocals where
  deriving Inhabited

inductive boolOnExit where
  | ret (v : Bool)

def boolOn  : Zig.MemM (Bool) := do
  let e ← ((do
    let i0 ← pure (⟨some 0, 0⟩ : Zig.Ptr)
    Zig.storeBits (α := Bool) 3 4 21 i0 true
    let i2 ← Zig.loadBits (Bool) 3 4 21 i0
    pure (.ret i2)) : Zig.MM boolOnLocals boolOnExit).run' (default : boolOnLocals)
  match e with
  | .ret v => pure v

structure hostAbiLocals where
  deriving Inhabited

inductive hostAbiExit where
  | ret (v : BitVec 4)

def hostAbi  : Zig.MemM (BitVec 4) := do
  let e ← ((do
    let i0 ← pure (⟨some 0, 0⟩ : Zig.Ptr)
    Zig.storeBits (α := BitVec 4) 4 4 0 i0 (9 : BitVec 4)
    let i2 ← pure (⟨some 0, 0⟩ : Zig.Ptr)
    Zig.storeBits (α := Inner) 4 4 4 i2 (Zig.Packed.ofBits (33 : BitVec 12) : Inner)
    let i4 ← Zig.loadBits (BitVec 4) 4 4 0 i0
    pure (.ret i4)) : Zig.MM hostAbiLocals hostAbiExit).run' (default : hostAbiLocals)
  match e with
  | .ret v => pure v

structure innerCLocals where
  deriving Inhabited

inductive innerCExit where
  | ret (v : BitVec 8)

def innerC  : Zig.MemM (BitVec 8) := do
  let e ← ((do
    let i0 ← pure (⟨some 0, 0⟩ : Zig.Ptr)
    Zig.storeBits (α := BitVec 4) 3 4 0 i0 (1 : BitVec 4)
    let i2 ← pure (⟨some 0, 0⟩ : Zig.Ptr)
    let i3 ← Zig.callM (Zig.ptrProject i2 (·.add 1))
    Zig.store (α := BitVec 8) 1 i3 (171 : BitVec 8)
    let i5 ← Zig.load (BitVec 8) 1 i3
    pure (.ret i5)) : Zig.MM innerCLocals innerCExit).run' (default : innerCLocals)
  match e with
  | .ret v => pure v

structure innerCKeepsALocals where
  deriving Inhabited

inductive innerCKeepsAExit where
  | ret (v : BitVec 4)

def innerCKeepsA  : Zig.MemM (BitVec 4) := do
  let e ← ((do
    let i0 ← pure (⟨some 0, 0⟩ : Zig.Ptr)
    Zig.storeBits (α := BitVec 4) 3 4 0 i0 (1 : BitVec 4)
    let i2 ← pure (⟨some 0, 0⟩ : Zig.Ptr)
    let i3 ← Zig.callM (Zig.ptrProject i2 (·.add 1))
    Zig.store (α := BitVec 8) 1 i3 (171 : BitVec 8)
    let i5 ← Zig.loadBits (BitVec 4) 3 4 0 i0
    pure (.ret i5)) : Zig.MM innerCKeepsALocals innerCKeepsAExit).run' (default : innerCKeepsALocals)
  match e with
  | .ret v => pure v

structure innerPartialLocals where
  deriving Inhabited

inductive innerPartialExit where
  | ret (v : Inner)

def innerPartial  : Zig.MemM (Inner) := do
  let e ← ((do
    let i0 ← pure (⟨some 0, 0⟩ : Zig.Ptr)
    let i1 ← Zig.callM (Zig.ptrProject i0 (·.add 1))
    Zig.store (α := BitVec 8) 1 i1 (90 : BitVec 8)
    let i3 ← Zig.loadBits (Inner) 3 4 4 i0
    pure (.ret i3)) : Zig.MM innerPartialLocals innerPartialExit).run' (default : innerPartialLocals)
  match e with
  | .ret v => pure v

structure localUndefLocals where
  local0 : Zig.Ptr
  deriving Inhabited

inductive localUndefExit where
  | ret (v : BitVec 4)

def localUndef  : Zig.MemM (BitVec 4) := do
  let s0 ← Zig.allocStack 4 4
  let e ← ((do
    let i0 ← pure (← get).local0
    let i1 ← pure i0
    Zig.storeBits (α := BitVec 4) 3 4 0 i1 (6 : BitVec 4)
    let i3 ← pure i0
    let i4 ← pure i3
    Zig.storeUndefBits 4 3 4 4 i4
    let i6 ← Zig.loadBits (BitVec 4) 3 4 0 i1
    pure (.ret i6)) : Zig.MM localUndefLocals localUndefExit).run' { (default : localUndefLocals) with local0 := s0 }
  Zig.free s0
  match e with
  | .ret v => pure v

structure modeHighLocals where
  deriving Inhabited

inductive modeHighExit where
  | ret (v : Mode)

def modeHigh  : Zig.MemM (Mode) := do
  let e ← ((do
    let i0 ← pure (⟨some 0, 0⟩ : Zig.Ptr)
    Zig.storeBits (α := Mode) 3 4 22 i0 Mode.high
    let i2 ← Zig.loadBits (Mode) 3 4 22 i0
    pure (.ret i2)) : Zig.MM modeHighLocals modeHighExit).run' (default : modeHighLocals)
  match e with
  | .ret v => pure v

structure setALocals where
  deriving Inhabited

inductive setAExit where
  | ret (v : BitVec 4)

def setA  : Zig.MemM (BitVec 4) := do
  let e ← ((do
    let i0 ← pure (⟨some 0, 0⟩ : Zig.Ptr)
    Zig.storeBits (α := BitVec 4) 3 4 0 i0 (5 : BitVec 4)
    let i2 ← Zig.loadBits (BitVec 4) 3 4 0 i0
    pure (.ret i2)) : Zig.MM setALocals setAExit).run' (default : setALocals)
  match e with
  | .ret v => pure v

structure setInnerLocals where
  deriving Inhabited

inductive setInnerExit where
  | ret (v : Inner)

def setInner  : Zig.MemM (Inner) := do
  let e ← ((do
    let i0 ← pure (⟨some 0, 0⟩ : Zig.Ptr)
    Zig.storeBits (α := Inner) 3 4 4 i0 (Zig.Packed.ofBits (1442 : BitVec 12) : Inner)
    let i2 ← Zig.loadBits (Inner) 3 4 4 i0
    pure (.ret i2)) : Zig.MM setInnerLocals setInnerExit).run' (default : setInnerLocals)
  match e with
  | .ret v => pure v

structure signedSLocals where
  deriving Inhabited

inductive signedSExit where
  | ret (v : BitVec 5)

def signedS  : Zig.MemM (BitVec 5) := do
  let e ← ((do
    let i0 ← pure (⟨some 0, 0⟩ : Zig.Ptr)
    Zig.storeBits (α := BitVec 5) 3 4 16 i0 (-(3 : BitVec 5))
    let i2 ← Zig.loadBits (BitVec 5) 3 4 16 i0
    pure (.ret i2)) : Zig.MM signedSLocals signedSExit).run' (default : signedSLocals)
  match e with
  | .ret v => pure v

structure undefFieldLocals where
  deriving Inhabited

inductive undefFieldExit where
  | ret (v : BitVec 4)

def undefField  : Zig.MemM (BitVec 4) := do
  let e ← ((do
    let i0 ← pure (⟨some 0, 0⟩ : Zig.Ptr)
    let i1 ← pure i0
    Zig.storeBits (α := BitVec 4) 3 4 4 i1 (7 : BitVec 4)
    Zig.storeUndefBits 4 3 4 4 i1
    let i4 ← Zig.loadBits (BitVec 4) 3 4 4 i1
    pure (.ret i4)) : Zig.MM undefFieldLocals undefFieldExit).run' (default : undefFieldLocals)
  match e with
  | .ret v => pure v

structure undefKeepsALocals where
  deriving Inhabited

inductive undefKeepsAExit where
  | ret (v : BitVec 4)

def undefKeepsA  : Zig.MemM (BitVec 4) := do
  let e ← ((do
    let i0 ← pure (⟨some 0, 0⟩ : Zig.Ptr)
    Zig.storeBits (α := BitVec 4) 3 4 0 i0 (3 : BitVec 4)
    let i2 ← pure (⟨some 0, 0⟩ : Zig.Ptr)
    let i3 ← pure i2
    Zig.storeUndefBits 4 3 4 4 i3
    let i5 ← Zig.loadBits (BitVec 4) 3 4 0 i0
    pure (.ret i5)) : Zig.MM undefKeepsALocals undefKeepsAExit).run' (default : undefKeepsALocals)
  match e with
  | .ret v => pure v

structure unionBadModeLocals where
  deriving Inhabited

inductive unionBadModeExit where
  | ret (v : Mode)

def unionBadMode  : Zig.MemM (Mode) := do
  let e ← ((do
    let i0 ← pure (⟨some 1, 0⟩ : Zig.Ptr)
    Zig.store (α := BitVec 24) 4 i0 (12582912 : BitVec 24)
    let i2 ← pure (⟨some 1, 0⟩ : Zig.Ptr)
    let i3 ← pure i2
    let i4 ← Zig.loadBits (Mode) 3 4 22 i3
    pure (.ret i4)) : Zig.MM unionBadModeLocals unionBadModeExit).run' (default : unionBadModeLocals)
  match e with
  | .ret v => pure v

structure unionRawLocals where
  deriving Inhabited

inductive unionRawExit where
  | ret (v : BitVec 24)

def unionRaw  : Zig.MemM (BitVec 24) := do
  let e ← ((do
    let i0 ← pure (⟨some 1, 0⟩ : Zig.Ptr)
    Zig.store (α := BitVec 24) 4 i0 (1193046 : BitVec 24)
    let i2 ← pure (⟨some 1, 0⟩ : Zig.Ptr)
    let i3 ← pure i2
    Zig.storeBits (α := BitVec 4) 3 4 0 i3 (15 : BitVec 4)
    let i5 ← Zig.load (BitVec 24) 4 i0
    pure (.ret i5)) : Zig.MM unionRawLocals unionRawExit).run' (default : unionRawLocals)
  match e with
  | .ret v => pure v

end PackedFields