-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.19-musl","zig_version":"0.16.0"}}
import ZigLean


namespace FloatLanes

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ []

structure middleLocals where
  v : Zig.Ptr
  deriving Inhabited

inductive middleExit where
  | ret (v : Zig.F80)

def middle (p0 : Zig.F80) : Zig.MemM (Zig.F80) := do
  let s1 ← Zig.allocStack 32 32
  let e ← ((do
    let i1 ← pure (← get).v
    let i2 ← pure i1
    Zig.storeLane (α := Zig.F80) 30 16 0 i2 (Zig.Float.ofBits (302226843217638866288640 : BitVec 80) : Zig.F80)
    let i4 ← pure i1
    Zig.storeLane (α := Zig.F80) 30 16 80 i4 (Zig.Float.ofBits (302242984118703362146304 : BitVec 80) : Zig.F80)
    let i6 ← pure i1
    Zig.storeLane (α := Zig.F80) 30 16 160 i6 (Zig.Float.ofBits (302247595804721789534208 : BitVec 80) : Zig.F80)
    let i8 ← pure i1
    Zig.storeLane (α := Zig.F80) 30 16 80 i8 p0
    let i10 ← pure i1
    let i11 ← Zig.loadLane (Zig.F80) 30 16 0 i10
    let i12 ← Zig.loadLane (Zig.F80) 30 16 80 i8
    let i13 ← pure (Zig.Float.add i11 i12)
    let i14 ← pure i1
    let i15 ← Zig.loadLane (Zig.F80) 30 16 160 i14
    let i16 ← pure (Zig.Float.add i13 i15)
    pure (.ret i16)) : Zig.MM middleLocals middleExit).run' { (default : middleLocals) with v := s1 }
  Zig.free s1
  match e with
  | .ret v => pure v

structure swapLocals where
  deriving Inhabited

inductive swapExit where
  | ret

def swap (p0 : Zig.Ptr) : Zig.MemM (Unit) := do
  let e ← ((do
    let i1 ← pure p0
    let i2 ← pure p0
    let i3 ← Zig.loadLane (Zig.F80) 20 16 0 i1
    let i4 ← Zig.loadLane (Zig.F80) 20 16 80 i2
    Zig.storeLane (α := Zig.F80) 20 16 0 i1 i4
    Zig.storeLane (α := Zig.F80) 20 16 80 i2 i3
    pure .ret) : Zig.MM swapLocals swapExit).run' (default : swapLocals)
  match e with
  | .ret => pure ()

end FloatLanes