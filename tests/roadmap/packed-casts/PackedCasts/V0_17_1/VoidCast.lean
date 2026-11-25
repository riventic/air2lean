-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...7.2-musl","zig_version":"0.17.1"}}
import ZigLean


namespace PackedCasts.V0_17_1.VoidCast

structure intToVoidsLocals where
  deriving Inhabited

inductive intToVoidsExit where
  | ret (v : Vector (Unit) 4)

def intToVoids  : Zig.Result (Vector (Unit) 4) := do
  let e ← ((do
    let i0 ← (Zig.Packed.ofBits? (α := Vector (Unit) 4) ((0 : BitVec 0)) : Zig.Result (Vector (Unit) 4))
    pure (.ret i0)) : Zig.M intToVoidsLocals intToVoidsExit).run' (default : intToVoidsLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] intToVoids

structure voidToIntLocals where
  deriving Inhabited

inductive voidToIntExit where
  | ret (v : BitVec 0)

def voidToInt  : Zig.Result (BitVec 0) := do
  let e ← ((do
    let i0 ← (Zig.Packed.toBits? (()) : Zig.Result (BitVec 0))
    pure (.ret i0)) : Zig.M voidToIntLocals voidToIntExit).run' (default : voidToIntLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] voidToInt

structure voidToVoidsLocals where
  deriving Inhabited

inductive voidToVoidsExit where
  | ret (v : Vector (Unit) 4)

def voidToVoids  : Zig.Result (Vector (Unit) 4) := do
  let e ← ((do
    let i0 ← (((Zig.Packed.toBits? (()) : Zig.Result (BitVec 0)) >>= fun bits => Zig.Packed.ofBits? (α := Vector (Unit) 4) (bits)) : Zig.Result (Vector (Unit) 4))
    pure (.ret i0)) : Zig.M voidToVoidsLocals voidToVoidsExit).run' (default : voidToVoidsLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] voidToVoids

structure voidsToIntLocals where
  deriving Inhabited

inductive voidsToIntExit where
  | ret (v : BitVec 0)

def voidsToInt  : Zig.Result (BitVec 0) := do
  let e ← ((do
    let i0 ← (Zig.Packed.toBits? ((#v[(), (), (), ()] : Vector (Unit) 4)) : Zig.Result (BitVec 0))
    pure (.ret i0)) : Zig.M voidsToIntLocals voidsToIntExit).run' (default : voidsToIntLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] voidsToInt

end PackedCasts.V0_17_1.VoidCast