-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.4.19...6.13.4-musl","zig_version":"0.14.1"}}
import ZigLean


namespace PackedCasts.V0_14_1.VoidCasts

structure emptyToIntLocals where
  deriving Inhabited

inductive emptyToIntExit where
  | ret (v : BitVec 8)

def emptyToInt (p0 : Vector (BitVec 8) 0) : Zig.Result (BitVec 8) := do
  let e ← ((do
    pure (.ret (0 : BitVec 8))) : Zig.M emptyToIntLocals emptyToIntExit).run' (default : emptyToIntLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] emptyToInt

structure intToVoidsLocals where
  deriving Inhabited

inductive intToVoidsExit where
  | ret (v : BitVec 64)

def intToVoids (p0 : BitVec 0) : Zig.Result (BitVec 64) := do
  let e ← ((do
    pure (.ret (4 : BitVec 64))) : Zig.M intToVoidsLocals intToVoidsExit).run' (default : intToVoidsLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] intToVoids

structure voidsToIntLocals where
  deriving Inhabited

inductive voidsToIntExit where
  | ret (v : BitVec 8)

def voidsToInt (p0 : Vector (Unit) 4) : Zig.Result (BitVec 8) := do
  let e ← ((do
    pure (.ret (0 : BitVec 8))) : Zig.M voidsToIntLocals voidsToIntExit).run' (default : voidsToIntLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] voidsToInt

end PackedCasts.V0_14_1.VoidCasts