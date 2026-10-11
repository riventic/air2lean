-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.19-musl","zig_version":"0.16.0"}}
import ZigLean


namespace FuzzS19

inductive UTag where
  | a
  | b
  deriving Repr, Inhabited, DecidableEq

def UTag.toBits : UTag → BitVec 1
  | .a => (0 : BitVec 1)
  | .b => (1 : BitVec 1)

def UTag.ofInt? (v : Int) : Option UTag :=
  if v = 0 then Option.some .a else if v = 1 then Option.some .b else Option.none

def UTag.isNamed (_ : UTag) : Bool := true

instance : Zig.Packed UTag 1 where
  toBits := UTag.toBits
  ofBits b := (UTag.ofInt? (Zig.val false b)).getD default
  valid b := (UTag.ofInt? (Zig.val false b)).isSome

inductive U where
  | a (v : BitVec 32)
  | b (v : BitVec 32)
  | undef_a (v : BitVec 32) (written : List String)
  | undef_b (v : BitVec 32) (written : List String)
  deriving Repr, Inhabited, DecidableEq

def U.tag : U → UTag
  | .a _ => .a
  | .undef_a _ _ => .a
  | .b _ => .b
  | .undef_b _ _ => .b

def U.get_a : U → Zig.Result (BitVec 32)
  | .a v => pure v
  | .undef_a _ _ => throw .unspecified
  | _ => throw .panic

def U.modify_a (g : BitVec 32 → BitVec 32) : U → U
  | .a v => .a (g v)
  | .undef_a v w => .undef_a (g v) w
  | _ => .undef_a (g default) []

def U.setTag_a : U → U
  | .a v => .a v
  | .undef_a v w => .undef_a v w
  | _ => .undef_a default []

def U.set_a (v : BitVec 32) (_ : U) : U := .a v

def U.get_b : U → Zig.Result (BitVec 32)
  | .b v => pure v
  | .undef_b _ _ => throw .unspecified
  | _ => throw .panic

def U.modify_b (g : BitVec 32 → BitVec 32) : U → U
  | .b v => .b (g v)
  | .undef_b v w => .undef_b (g v) w
  | _ => .undef_b (g default) []

def U.setTag_b : U → U
  | .b v => .b v
  | .undef_b v w => .undef_b v w
  | _ => .undef_b default []

def U.set_b (v : BitVec 32) (_ : U) : U := .b v

structure workLocals where
  deriving Inhabited

inductive workExit where
  | ret (v : BitVec 32)

def work (p0 : BitVec 32) (p1 : BitVec 32) : Zig.Result (BitVec 32) := do
  let e ← ((do
    pure (.ret (0 : BitVec 32))) : Zig.M workLocals workExit).run' (default : workLocals)
  match e with
  | .ret v => pure v

structure entryLocals where
  deriving Inhabited

inductive entryExit where
  | ret (v : BitVec 32)

def entry (p0 : BitVec 32) (p1 : BitVec 32) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i2 ← Zig.call (work p0 p1)
    pure (.ret i2)) : Zig.M entryLocals entryExit).run' (default : entryLocals)
  match e with
  | .ret v => pure v

end FuzzS19