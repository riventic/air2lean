-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.19-musl","zig_version":"0.16.0"}}
import ZigLean


namespace PackedCasts.V0_16_0.SentinelArrays

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ []

structure intToSentAtLocals where
  local3 : Zig.Ptr
  deriving Inhabited

inductive intToSentAtExit where
  | ret (v : BitVec 8)
  | br7

def intToSentAt (p0 : BitVec 32) (p1 : BitVec 64) : Zig.MemM (BitVec 8) := do
  let s3 ← Zig.allocStack 4 1
  let e ← ((do
    let i2 ← Zig.reprCast (Vector (BitVec 8) 4) (p0 : BitVec 32)
    let i3 ← pure (← get).local3
    Zig.store (α := Vector (BitVec 8) 4) 1 i3 i2
    let i5 ← pure (i3)
    let i6 ← pure (Zig.le false p1 (3 : BitVec 64))
    match ← ((do
      if i6 then (do
        pure .br7)
      else (do
        throw .outOfBounds)) : Zig.MM intToSentAtLocals intToSentAtExit) with
    | .br7 => (do
      let i12 ← Zig.callM (Zig.checkSentinelIndex (3 : BitVec 64) p1 >>= fun _ => Zig.load (BitVec 8) 1 (i5.elem 1 p1))
      pure (.ret i12))
    | e => pure e) : Zig.MM intToSentAtLocals intToSentAtExit).run' { (default : intToSentAtLocals) with local3 := s3 }
  Zig.free s3
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] intToSentAt

structure nestedToIntLocals where
  deriving Inhabited

inductive nestedToIntExit where
  | ret (v : BitVec 64)

def nestedToInt (p0 : Vector (Vector (BitVec 8) 4) 2) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i1 ← Zig.reprCast (BitVec 64) (p0 : Vector (Vector (BitVec 8) 4) 2)
    pure (.ret i1)) : Zig.M nestedToIntLocals nestedToIntExit).run' (default : nestedToIntLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] nestedToInt

structure roundTripLocals where
  deriving Inhabited

inductive roundTripExit where
  | ret (v : BitVec 32)

def roundTrip (p0 : BitVec 32) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← Zig.reprCast (Vector (BitVec 8) 4) (p0 : BitVec 32)
    let i2 ← Zig.reprCast (BitVec 32) (i1 : Vector (BitVec 8) 4)
    pure (.ret i2)) : Zig.M roundTripLocals roundTripExit).run' (default : roundTripLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] roundTrip

structure sentInitLocals where
  local1 : Zig.Ptr
  deriving Inhabited

inductive sentInitExit where
  | ret (v : BitVec 32)

def sentInit (p0 : BitVec 8) : Zig.MemM (BitVec 32) := do
  let s1 ← Zig.allocStack 4 1
  let e ← ((do
    let i1 ← pure (← get).local1
    let i2 ← pure i1
    Zig.store (α := BitVec 8) 1 i2 p0
    let i4 ← Zig.callM (Zig.ptrProject i1 (·.elem 1 (1 : BitVec 64)))
    Zig.store (α := BitVec 8) 1 i4 (2 : BitVec 8)
    let i6 ← Zig.callM (Zig.ptrProject i1 (·.elem 1 (2 : BitVec 64)))
    Zig.store (α := BitVec 8) 1 i6 (3 : BitVec 8)
    let i8 ← Zig.callM (Zig.ptrProject i1 (·.elem 1 (3 : BitVec 64)))
    Zig.store (α := BitVec 8) 1 i8 (7 : BitVec 8)
    let i10 ← pure (i1)
    let i11 ← Zig.load (Vector (BitVec 8) 4) 1 i10
    let i12 ← Zig.reprCast (BitVec 32) (i11 : Vector (BitVec 8) 4)
    pure (.ret i12)) : Zig.MM sentInitLocals sentInitExit).run' { (default : sentInitLocals) with local1 := s1 }
  Zig.free s1
  match e with
  | .ret v => pure v

attribute [zig_run] sentInit

structure sentItem3Locals where
  local2 : Zig.Ptr
  deriving Inhabited

inductive sentItem3Exit where
  | ret (v : BitVec 8)

def sentItem3 (p0 : Vector (BitVec 8) 4) : Zig.MemM (BitVec 8) := do
  let s2 ← Zig.allocStack 4 1
  let e ← ((do
    let i1 ← Zig.reprCast (Vector (BitVec 8) 4) (p0 : Vector (BitVec 8) 4)
    let i2 ← pure (← get).local2
    Zig.store (α := Vector (BitVec 8) 4) 1 i2 i1
    let i4 ← pure (i2)
    let i5 ← Zig.callM (Zig.load (BitVec 8) 1 (i4.elem 1 (3 : BitVec 64)))
    pure (.ret i5)) : Zig.MM sentItem3Locals sentItem3Exit).run' { (default : sentItem3Locals) with local2 := s2 }
  Zig.free s2
  match e with
  | .ret v => pure v

attribute [zig_run] sentItem3

structure sentToIntLocals where
  deriving Inhabited

inductive sentToIntExit where
  | ret (v : BitVec 32)

def sentToInt (p0 : Vector (BitVec 8) 4) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← Zig.reprCast (BitVec 32) (p0 : Vector (BitVec 8) 4)
    pure (.ret i1)) : Zig.M sentToIntLocals sentToIntExit).run' (default : sentToIntLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] sentToInt

structure wideToIntLocals where
  deriving Inhabited

inductive wideToIntExit where
  | ret (v : BitVec 64)

def wideToInt (p0 : Vector (BitVec 16) 4) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i1 ← Zig.reprCast (BitVec 64) (p0 : Vector (BitVec 16) 4)
    pure (.ret i1)) : Zig.M wideToIntLocals wideToIntExit).run' (default : wideToIntLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] wideToInt

end PackedCasts.V0_16_0.SentinelArrays