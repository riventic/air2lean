-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.19-musl","zig_version":"0.16.0"}}
import ZigLean


namespace PackedFieldsFresh

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
  -- 1: packed_fields.inner_g
  (Array.replicate (Zig.Enc.size (Inner)) .undef, 2, .global),
  -- 2: packed_fields.word
  (Array.replicate (Zig.Enc.size (Word)) .undef, 4, .global)]

structure boolOnLocals where
  deriving Inhabited

inductive boolOnExit where
  | ret (v : Bool)

def boolOn  : Zig.MemM (Bool) := do
  let e ← ((do
    Zig.storeBits (α := Bool) 3 4 21 (⟨some 0, 0⟩ : Zig.Ptr) true
    let i1 ← Zig.loadBits (Bool) 3 4 21 (⟨some 0, 0⟩ : Zig.Ptr)
    pure (.ret i1)) : Zig.MM boolOnLocals boolOnExit).run' (default : boolOnLocals)
  match e with
  | .ret v => pure v

structure bytePtrLocals where
  deriving Inhabited

inductive bytePtrExit where
  | ret (v : BitVec 8)

def bytePtr  : Zig.MemM (BitVec 8) := do
  let e ← ((do
    Zig.storeBits (α := BitVec 4) 2 2 0 (⟨some 1, 0⟩ : Zig.Ptr) (1 : BitVec 4)
    Zig.storeBits (α := BitVec 8) 2 2 4 (⟨some 1, 0⟩ : Zig.Ptr) (205 : BitVec 8)
    let i2 ← Zig.loadBits (BitVec 8) 2 2 4 (⟨some 1, 0⟩ : Zig.Ptr)
    pure (.ret i2)) : Zig.MM bytePtrLocals bytePtrExit).run' (default : bytePtrLocals)
  match e with
  | .ret v => pure v

structure hostAbiLocals where
  deriving Inhabited

inductive hostAbiExit where
  | ret (v : BitVec 4)

def hostAbi  : Zig.MemM (BitVec 4) := do
  let e ← ((do
    Zig.storeBits (α := BitVec 4) 3 4 0 (⟨some 0, 0⟩ : Zig.Ptr) (9 : BitVec 4)
    Zig.storeBits (α := BitVec 4) 3 4 4 (⟨some 0, 0⟩ : Zig.Ptr) (1 : BitVec 4)
    Zig.storeBits (α := BitVec 8) 3 4 8 (⟨some 0, 0⟩ : Zig.Ptr) (2 : BitVec 8)
    let i3 ← Zig.loadBits (BitVec 4) 3 4 0 (⟨some 0, 0⟩ : Zig.Ptr)
    pure (.ret i3)) : Zig.MM hostAbiLocals hostAbiExit).run' (default : hostAbiLocals)
  match e with
  | .ret v => pure v

structure innerCLocals where
  deriving Inhabited

inductive innerCExit where
  | ret (v : BitVec 8)

def innerC  : Zig.MemM (BitVec 8) := do
  let e ← ((do
    Zig.storeBits (α := BitVec 4) 3 4 0 (⟨some 0, 0⟩ : Zig.Ptr) (1 : BitVec 4)
    Zig.storeBits (α := BitVec 8) 3 4 8 (⟨some 0, 0⟩ : Zig.Ptr) (171 : BitVec 8)
    let i2 ← Zig.loadBits (BitVec 8) 3 4 8 (⟨some 0, 0⟩ : Zig.Ptr)
    pure (.ret i2)) : Zig.MM innerCLocals innerCExit).run' (default : innerCLocals)
  match e with
  | .ret v => pure v

structure innerCKeepsALocals where
  deriving Inhabited

inductive innerCKeepsAExit where
  | ret (v : BitVec 4)

def innerCKeepsA  : Zig.MemM (BitVec 4) := do
  let e ← ((do
    Zig.storeBits (α := BitVec 4) 3 4 0 (⟨some 0, 0⟩ : Zig.Ptr) (1 : BitVec 4)
    Zig.storeBits (α := BitVec 8) 3 4 8 (⟨some 0, 0⟩ : Zig.Ptr) (171 : BitVec 8)
    let i2 ← Zig.loadBits (BitVec 4) 3 4 0 (⟨some 0, 0⟩ : Zig.Ptr)
    pure (.ret i2)) : Zig.MM innerCKeepsALocals innerCKeepsAExit).run' (default : innerCKeepsALocals)
  match e with
  | .ret v => pure v

structure innerCKeepsAPtrLocals where
  deriving Inhabited

inductive innerCKeepsAPtrExit where
  | ret (v : BitVec 4)

def innerCKeepsAPtr (p0 : Zig.Ptr) : Zig.MemM (BitVec 4) := do
  let e ← ((do
    let i1 ← pure p0
    Zig.storeBits (α := BitVec 4) 3 4 0 i1 (1 : BitVec 4)
    let i3 ← pure p0
    let i4 ← pure i3
    Zig.storeBits (α := BitVec 8) 3 4 8 i4 (171 : BitVec 8)
    let i6 ← pure p0
    let i7 ← Zig.loadBits (BitVec 4) 3 4 0 i6
    pure (.ret i7)) : Zig.MM innerCKeepsAPtrLocals innerCKeepsAPtrExit).run' (default : innerCKeepsAPtrLocals)
  match e with
  | .ret v => pure v

structure innerCPtrLocals where
  deriving Inhabited

inductive innerCPtrExit where
  | ret (v : BitVec 8)

def innerCPtr (p0 : Zig.Ptr) : Zig.MemM (BitVec 8) := do
  let e ← ((do
    let i1 ← pure p0
    Zig.storeBits (α := BitVec 4) 3 4 0 i1 (1 : BitVec 4)
    let i3 ← pure p0
    let i4 ← pure i3
    Zig.storeBits (α := BitVec 8) 3 4 8 i4 (171 : BitVec 8)
    let i6 ← pure p0
    let i7 ← pure i6
    let i8 ← Zig.loadBits (BitVec 8) 3 4 8 i7
    pure (.ret i8)) : Zig.MM innerCPtrLocals innerCPtrExit).run' (default : innerCPtrLocals)
  match e with
  | .ret v => pure v

structure innerPartialLocals where
  deriving Inhabited

inductive innerPartialExit where
  | ret (v : Inner)

def innerPartial  : Zig.MemM (Inner) := do
  let e ← ((do
    Zig.storeBits (α := BitVec 8) 3 4 8 (⟨some 0, 0⟩ : Zig.Ptr) (90 : BitVec 8)
    let i1 ← Zig.loadBits (Inner) 3 4 4 (⟨some 0, 0⟩ : Zig.Ptr)
    pure (.ret i1)) : Zig.MM innerPartialLocals innerPartialExit).run' (default : innerPartialLocals)
  match e with
  | .ret v => pure v

structure localUndefLocals where
  r : Zig.Ptr
  deriving Inhabited

inductive localUndefExit where
  | ret (v : BitVec 4)

def localUndef  : Zig.MemM (BitVec 4) := do
  let s0 ← Zig.allocStack 4 4
  let e ← ((do
    let i0 ← pure (← get).r
    Zig.storeUndef (Reg) 4 i0
    let i2 ← pure i0
    Zig.storeBits (α := BitVec 4) 3 4 0 i2 (6 : BitVec 4)
    let i4 ← pure i0
    let i5 ← pure i4
    Zig.storeUndefBits 4 3 4 4 i5
    let i7 ← pure i0
    let i8 ← Zig.loadBits (BitVec 4) 3 4 0 i7
    pure (.ret i8)) : Zig.MM localUndefLocals localUndefExit).run' { (default : localUndefLocals) with r := s0 }
  Zig.free s0
  match e with
  | .ret v => pure v

structure modeHighLocals where
  deriving Inhabited

inductive modeHighExit where
  | ret (v : Mode)

def modeHigh  : Zig.MemM (Mode) := do
  let e ← ((do
    Zig.storeBits (α := Mode) 3 4 22 (⟨some 0, 0⟩ : Zig.Ptr) Mode.high
    let i1 ← Zig.loadBits (Mode) 3 4 22 (⟨some 0, 0⟩ : Zig.Ptr)
    pure (.ret i1)) : Zig.MM modeHighLocals modeHighExit).run' (default : modeHighLocals)
  match e with
  | .ret v => pure v

structure setALocals where
  deriving Inhabited

inductive setAExit where
  | ret (v : BitVec 4)

def setA  : Zig.MemM (BitVec 4) := do
  let e ← ((do
    Zig.storeBits (α := BitVec 4) 3 4 0 (⟨some 0, 0⟩ : Zig.Ptr) (5 : BitVec 4)
    let i1 ← Zig.loadBits (BitVec 4) 3 4 0 (⟨some 0, 0⟩ : Zig.Ptr)
    pure (.ret i1)) : Zig.MM setALocals setAExit).run' (default : setALocals)
  match e with
  | .ret v => pure v

structure setInnerLocals where
  deriving Inhabited

inductive setInnerExit where
  | ret (v : Inner)

def setInner  : Zig.MemM (Inner) := do
  let e ← ((do
    Zig.storeBits (α := BitVec 4) 3 4 4 (⟨some 0, 0⟩ : Zig.Ptr) (2 : BitVec 4)
    Zig.storeBits (α := BitVec 8) 3 4 8 (⟨some 0, 0⟩ : Zig.Ptr) (90 : BitVec 8)
    let i2 ← Zig.loadBits (Inner) 3 4 4 (⟨some 0, 0⟩ : Zig.Ptr)
    pure (.ret i2)) : Zig.MM setInnerLocals setInnerExit).run' (default : setInnerLocals)
  match e with
  | .ret v => pure v

structure setInnerPtrLocals where
  deriving Inhabited

inductive setInnerPtrExit where
  | ret (v : Inner)

def setInnerPtr (p0 : Zig.Ptr) : Zig.MemM (Inner) := do
  let e ← ((do
    let i1 ← pure p0
    let i2 ← pure i1
    Zig.storeBits (α := BitVec 4) 3 4 4 i2 (2 : BitVec 4)
    let i4 ← pure i1
    Zig.storeBits (α := BitVec 8) 3 4 8 i4 (90 : BitVec 8)
    let i6 ← pure p0
    let i7 ← Zig.loadBits (Inner) 3 4 4 i6
    pure (.ret i7)) : Zig.MM setInnerPtrLocals setInnerPtrExit).run' (default : setInnerPtrLocals)
  match e with
  | .ret v => pure v

structure signedSLocals where
  deriving Inhabited

inductive signedSExit where
  | ret (v : BitVec 5)

def signedS  : Zig.MemM (BitVec 5) := do
  let e ← ((do
    Zig.storeBits (α := BitVec 5) 3 4 16 (⟨some 0, 0⟩ : Zig.Ptr) (-(3 : BitVec 5))
    let i1 ← Zig.loadBits (BitVec 5) 3 4 16 (⟨some 0, 0⟩ : Zig.Ptr)
    pure (.ret i1)) : Zig.MM signedSLocals signedSExit).run' (default : signedSLocals)
  match e with
  | .ret v => pure v

structure undefFieldLocals where
  deriving Inhabited

inductive undefFieldExit where
  | ret (v : BitVec 4)

def undefField  : Zig.MemM (BitVec 4) := do
  let e ← ((do
    Zig.storeBits (α := BitVec 4) 3 4 4 (⟨some 0, 0⟩ : Zig.Ptr) (7 : BitVec 4)
    Zig.storeUndefBits 4 3 4 4 (⟨some 0, 0⟩ : Zig.Ptr)
    let i2 ← Zig.loadBits (BitVec 4) 3 4 4 (⟨some 0, 0⟩ : Zig.Ptr)
    pure (.ret i2)) : Zig.MM undefFieldLocals undefFieldExit).run' (default : undefFieldLocals)
  match e with
  | .ret v => pure v

structure undefKeepsALocals where
  deriving Inhabited

inductive undefKeepsAExit where
  | ret (v : BitVec 4)

def undefKeepsA  : Zig.MemM (BitVec 4) := do
  let e ← ((do
    Zig.storeBits (α := BitVec 4) 3 4 0 (⟨some 0, 0⟩ : Zig.Ptr) (3 : BitVec 4)
    Zig.storeUndefBits 4 3 4 4 (⟨some 0, 0⟩ : Zig.Ptr)
    let i2 ← Zig.loadBits (BitVec 4) 3 4 0 (⟨some 0, 0⟩ : Zig.Ptr)
    pure (.ret i2)) : Zig.MM undefKeepsALocals undefKeepsAExit).run' (default : undefKeepsALocals)
  match e with
  | .ret v => pure v

structure unionBadModeLocals where
  deriving Inhabited

inductive unionBadModeExit where
  | ret (v : Mode)

def unionBadMode  : Zig.MemM (Mode) := do
  let e ← ((do
    Zig.store (α := BitVec 24) 4 (⟨some 2, 0⟩ : Zig.Ptr) (12582912 : BitVec 24)
    let i1 ← Zig.loadBits (Mode) 3 4 22 (⟨some 2, 0⟩ : Zig.Ptr)
    pure (.ret i1)) : Zig.MM unionBadModeLocals unionBadModeExit).run' (default : unionBadModeLocals)
  match e with
  | .ret v => pure v

structure unionRawLocals where
  deriving Inhabited

inductive unionRawExit where
  | ret (v : BitVec 24)

def unionRaw  : Zig.MemM (BitVec 24) := do
  let e ← ((do
    Zig.store (α := BitVec 24) 4 (⟨some 2, 0⟩ : Zig.Ptr) (1193046 : BitVec 24)
    Zig.storeBits (α := BitVec 4) 3 4 0 (⟨some 2, 0⟩ : Zig.Ptr) (15 : BitVec 4)
    let i2 ← Zig.load (BitVec 24) 4 (⟨some 2, 0⟩ : Zig.Ptr)
    pure (.ret i2)) : Zig.MM unionRawLocals unionRawExit).run' (default : unionRawLocals)
  match e with
  | .ret v => pure v

end PackedFieldsFresh