-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_x86_64","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.19-musl","zig_version":"0.16.0"}}
import ZigLean


namespace PackedFieldsX86

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

/-- The memory at program start: block `k` is global `k`. -/
def mem0 : Zig.Mem := Zig.Mem.ofGlobals [
  -- 0: packed_fields.reg
  (Array.replicate (Zig.Enc.size (Reg)) .undef, 4, .global)]

structure hostAbiLocals where
  deriving Inhabited

inductive hostAbiExit where
  | ret (v : BitVec 4)

def hostAbi  : Zig.MemM (BitVec 4) := do
  let e ← ((do
    Zig.storeBits (α := BitVec 4) 4 4 0 (⟨some 0, 0⟩ : Zig.Ptr) (9 : BitVec 4)
    Zig.storeBits (α := BitVec 4) 4 4 4 (⟨some 0, 0⟩ : Zig.Ptr) (1 : BitVec 4)
    Zig.storeBits (α := BitVec 8) 4 4 8 (⟨some 0, 0⟩ : Zig.Ptr) (2 : BitVec 8)
    let i3 ← Zig.loadBits (BitVec 4) 4 4 0 (⟨some 0, 0⟩ : Zig.Ptr)
    pure (.ret i3)) : Zig.MM hostAbiLocals hostAbiExit).run' (default : hostAbiLocals)
  match e with
  | .ret v => pure v

end PackedFieldsX86