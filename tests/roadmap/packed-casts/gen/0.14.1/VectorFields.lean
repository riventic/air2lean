-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.4.19...6.13.4-musl","zig_version":"0.14.1"}}
import ZigLean


namespace VectorFields

structure VF where
  t : BitVec 4
  v : Zig.Vec (BitVec 4) 3
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Packed VF 16 where
  toBits v := ((Zig.Packed.toBits v.t).setWidth 16 <<< 0) ||| ((Zig.Packed.toBits v.v).setWidth 16 <<< 4)
  ofBits b := { t := Zig.Packed.get b 0, v := Zig.Packed.get b 4 }

instance : Zig.Enc VF where
  size := 2
  align := 2
  encode v := Zig.Enc.encode (Zig.Packed.toBits v)
  decode bs := do
    let b : BitVec 16 ← Zig.Enc.decode bs
    Zig.Packed.ofBits? b

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ [
  -- 0: vector_fields.vf
  (Array.replicate (Zig.Enc.size (VF)) .undef, 2, .global)]

structure lane1Locals where
  deriving Inhabited

inductive lane1Exit where
  | ret (v : BitVec 4)

def lane1 (p0 : BitVec 16) : Zig.Result (BitVec 4) := do
  let e ← ((do
    let i1 ← Zig.Packed.ofBits? (α := VF) p0
    let i2 ← pure ((i1).v)
    let i3 ← Zig.call (Zig.vindex i2.lanes (1 : BitVec 64))
    pure (.ret i3)) : Zig.M lane1Locals lane1Exit).run' (default : lane1Locals)
  match e with
  | .ret v => pure v

structure laneSumLocals where
  deriving Inhabited

inductive laneSumExit where
  | ret (v : BitVec 4)

def laneSum (p0 : BitVec 16) : Zig.MemM (BitVec 4) := do
  let e ← ((do
    let i1 ← Zig.Packed.ofBits? (α := VF) p0
    Zig.store (α := VF) 2 (⟨some 0, 0⟩ : Zig.Ptr) i1
    let i3 ← Zig.load (VF) 2 (⟨some 0, 0⟩ : Zig.Ptr)
    let i4 ← pure ((i3).v)
    let i5 ← Zig.callR (Zig.vindex i4.lanes (0 : BitVec 64))
    let i6 ← Zig.callR (Zig.vindex i4.lanes (1 : BitVec 64))
    let i7 ← pure (Zig.addWrap i5 i6)
    let i8 ← Zig.callR (Zig.vindex i4.lanes (2 : BitVec 64))
    let i9 ← pure (Zig.addWrap i7 i8)
    pure (.ret i9)) : Zig.MM laneSumLocals laneSumExit).run' (default : laneSumLocals)
  match e with
  | .ret v => pure v

structure setVectorLocals where
  local4 : Zig.Ptr
  deriving Inhabited

inductive setVectorExit where
  | ret (v : BitVec 16)

def setVector (p0 : BitVec 4) (p1 : BitVec 4) (p2 : BitVec 4) : Zig.MemM (BitVec 16) := do
  let s4 ← Zig.allocStack 2 2
  let e ← ((do
    Zig.storeBits (α := BitVec 4) 2 2 0 (⟨some 0, 0⟩ : Zig.Ptr) (10 : BitVec 4)
    let i4 ← pure (← get).local4
    let i5 ← pure i4
    Zig.storeLane (α := BitVec 4) 2 2 0 i5 p0
    let i7 ← pure i4
    Zig.storeLane (α := BitVec 4) 2 2 4 i7 p1
    let i9 ← pure i4
    Zig.storeLane (α := BitVec 4) 2 2 8 i9 p2
    let i11 ← pure (i4)
    let i12 ← Zig.load (Zig.Vec (BitVec 4) 3) 2 i11
    Zig.storeBits (α := Zig.Vec (BitVec 4) 3) 2 2 4 (⟨some 0, 0⟩ : Zig.Ptr) i12
    let i14 ← Zig.load (VF) 2 (⟨some 0, 0⟩ : Zig.Ptr)
    let i15 ← pure (Zig.Packed.toBits i14)
    pure (.ret i15)) : Zig.MM setVectorLocals setVectorExit).run' { (default : setVectorLocals) with local4 := s4 }
  Zig.free s4
  match e with
  | .ret v => pure v

end VectorFields