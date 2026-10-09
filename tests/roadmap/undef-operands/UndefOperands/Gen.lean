-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"unverified","backend":"unverified","build_mode":"unverified","cpu":"unverified","endian":"little","error_layout":"reference-model","error_set_bits":16,"error_tracing":null,"export_stage":"unverified","features":[],"float_mode":"unverified","name":"legacy-abi64-le","pointer_bits":64,"schema":11,"target_triple":"unverified","zig_version":"0.16.0"}}
import ZigLean


namespace UndefOperands

structure Rec where
  len : BitVec 8
  buf : Vector (BitVec 16) 3
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Rec where
  size := 8
  align := 2
  encode v := Zig.Enc.fields 8 [(6, Zig.Enc.encode v.len), (0, Zig.Enc.encode v.buf)]
  decode bs := do pure { len := ← Zig.Enc.decodeAt bs 6, buf := ← Zig.Enc.decodeAt bs 0 }

structure Pair where
  a : BitVec 32
  b : BitVec 32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Pair where
  size := 8
  align := 4
  encode v := Zig.Enc.fields 8 [(0, Zig.Enc.encode v.a), (4, Zig.Enc.encode v.b)]
  decode bs := do pure { a := ← Zig.Enc.decodeAt bs 0, b := ← Zig.Enc.decodeAt bs 4 }

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ [
  -- 0: undef_operands.rec
  (Zig.Enc.encode (({ len := (0 : BitVec 8), buf := (#v[(0 : BitVec 16), (0 : BitVec 16), (0 : BitVec 16)] : Vector (BitVec 16) 3) } : Rec) : Rec), 2, .global)]

structure localALocals where
  local0 : Zig.Ptr
  deriving Inhabited

inductive localAExit where
  | ret (v : BitVec 32)

def localA  : Zig.MemM (BitVec 32) := do
  let s0 ← Zig.allocStack 8 4
  let e ← ((do
    let i0 ← pure (← get).local0
    Zig.storeBytes i0 4 (Zig.writeBytes (Zig.Enc.encode (({ a := (1 : BitVec 32), b := (0#32) } : Pair) : Pair)) 4 (Array.replicate 4 .undef))
    let i2 ← pure (i0.add 0)
    let i3 ← Zig.load (BitVec 32) 4 i2
    pure (.ret i3)) : Zig.MM localALocals localAExit).run' { (default : localALocals) with local0 := s0 }
  Zig.free s0
  match e with
  | .ret v => pure v

structure localBLocals where
  local0 : Zig.Ptr
  deriving Inhabited

inductive localBExit where
  | ret (v : BitVec 32)

def localB  : Zig.MemM (BitVec 32) := do
  let s0 ← Zig.allocStack 8 4
  let e ← ((do
    let i0 ← pure (← get).local0
    Zig.storeBytes i0 4 (Zig.writeBytes (Zig.Enc.encode (({ a := (1 : BitVec 32), b := (0#32) } : Pair) : Pair)) 4 (Array.replicate 4 .undef))
    let i2 ← pure (i0.add 4)
    let i3 ← Zig.load (BitVec 32) 4 i2
    pure (.ret i3)) : Zig.MM localBLocals localBExit).run' { (default : localBLocals) with local0 := s0 }
  Zig.free s0
  match e with
  | .ret v => pure v

structure recLenLocals where
  deriving Inhabited

inductive recLenExit where
  | ret (v : BitVec 8)

def recLen  : Zig.MemM (BitVec 8) := do
  let e ← ((do
    Zig.storeBytes (⟨some 0, 0⟩ : Zig.Ptr) 2 (Zig.writeBytes (Zig.Enc.encode (({ len := (2 : BitVec 8), buf := (#v[(1 : BitVec 16), (0#16), (3 : BitVec 16)] : Vector (BitVec 16) 3) } : Rec) : Rec)) 2 (Array.replicate 2 .undef))
    let i1 ← pure ((⟨some 0, 0⟩ : Zig.Ptr).add 6)
    let i2 ← Zig.load (BitVec 8) 1 i1
    pure (.ret i2)) : Zig.MM recLenLocals recLenExit).run' (default : recLenLocals)
  match e with
  | .ret v => pure v

structure recMidLocals where
  deriving Inhabited

inductive recMidExit where
  | ret (v : BitVec 16)

def recMid  : Zig.MemM (BitVec 16) := do
  let e ← ((do
    Zig.storeBytes (⟨some 0, 0⟩ : Zig.Ptr) 2 (Zig.writeBytes (Zig.Enc.encode (({ len := (2 : BitVec 8), buf := (#v[(1 : BitVec 16), (0#16), (3 : BitVec 16)] : Vector (BitVec 16) 3) } : Rec) : Rec)) 2 (Array.replicate 2 .undef))
    let i1 ← pure ((⟨some 0, 0⟩ : Zig.Ptr).add 0)
    let i2 ← Zig.callM (Zig.load (BitVec 16) 2 (i1.elem 2 (1 : BitVec 64)))
    pure (.ret i2)) : Zig.MM recMidLocals recMidExit).run' (default : recMidLocals)
  match e with
  | .ret v => pure v

structure storePairLocals where
  deriving Inhabited

inductive storePairExit where
  | ret

def storePair (p0 : Zig.Ptr) : Zig.MemM (Unit) := do
  let e ← ((do
    Zig.storeBytes p0 4 (Zig.writeBytes (Zig.Enc.encode (({ a := (1 : BitVec 32), b := (0#32) } : Pair) : Pair)) 4 (Array.replicate 4 .undef))
    pure .ret) : Zig.MM storePairLocals storePairExit).run' (default : storePairLocals)
  match e with
  | .ret => pure ()

end UndefOperands