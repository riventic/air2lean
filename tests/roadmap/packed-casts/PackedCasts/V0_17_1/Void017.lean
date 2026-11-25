-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...7.2-musl","zig_version":"0.17.1"}}
import ZigLean


namespace PackedCasts.V0_17_1.Void017

structure emptyToVoidLocals where
  deriving Inhabited

inductive emptyToVoidExit where
  | ret

def emptyToVoid (p0 : Vector (BitVec 8) 0) : Zig.Result (Unit) := do
  let e ← ((do
    pure .ret) : Zig.M emptyToVoidLocals emptyToVoidExit).run' (default : emptyToVoidLocals)
  match e with
  | .ret => pure ()

attribute [zig_run] emptyToVoid

structure intToVoidLocals where
  deriving Inhabited

inductive intToVoidExit where
  | ret

def intToVoid (p0 : BitVec 0) : Zig.Result (Unit) := do
  let e ← ((do
    pure .ret) : Zig.M intToVoidLocals intToVoidExit).run' (default : intToVoidLocals)
  match e with
  | .ret => pure ()

attribute [zig_run] intToVoid

structure voidToIntLocals where
  deriving Inhabited

inductive voidToIntExit where
  | ret (v : BitVec 8)

def voidToInt (p0 : Unit) : Zig.Result (BitVec 8) := do
  let e ← ((do
    pure (.ret (0 : BitVec 8))) : Zig.M voidToIntLocals voidToIntExit).run' (default : voidToIntLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] voidToInt

structure voidToVoidsLocals where
  deriving Inhabited

inductive voidToVoidsExit where
  | ret (v : BitVec 64)

def voidToVoids (p0 : Unit) : Zig.Result (BitVec 64) := do
  let e ← ((do
    pure (.ret (3 : BitVec 64))) : Zig.M voidToVoidsLocals voidToVoidsExit).run' (default : voidToVoidsLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] voidToVoids

end PackedCasts.V0_17_1.Void017