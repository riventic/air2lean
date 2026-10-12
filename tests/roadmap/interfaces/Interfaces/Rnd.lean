-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...7.2-musl","zig_version":"0.17.0"}}
-- air2lean-interfaces: {"ext":[{"field":"call0","type":"fn (*anyopaque, []u8) void"}],"interfaces":[{"contract":"Interfaces.RandomSpec.FillSpec","interface":"std.Random","premise":"EXT-05","struct":"Random"}]}
import ZigLean


namespace Interfaces.Rnd

structure Random where
  ptr : Zig.Ptr
  fillFn : Zig.Ptr
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Random where
  size := 16
  align := 8
  encode v := Zig.Enc.fields 16 [(0, Zig.Enc.encode v.ptr), (8, Zig.Enc.encode v.fillFn)]
  decode bs := do pure { ptr := ← Zig.Enc.decodeAt bs 0, fillFn := ← Zig.Enc.decodeAt bs 8 }

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ []

/-- The spawn targets of the program. -/
inductive Tgt where

/-- The environment's implementations of the open interfaces (`docs/interfaces.md`,
premise EXT-05): `call<i> f args` runs the environment's function at `f`, a pointer that is no
function of the program. -/
class Ext where
  /-- `fn (*anyopaque, []u8) void` -/
  call0 : Zig.Ptr → (Zig.Ptr) → (Zig.Slice) → Zig.ConcM Tgt (Unit)

/-- The closed program's environment: no function besides the program's. -/
@[reducible] def Ext.closed : Ext where
  call0 _ _ _ := throw .illegal

structure Random_bytesLocals where
  deriving Inhabited

inductive Random_bytesExit where
  | ret

def Random_bytes [Ext] (p0 : Random) (p1 : Zig.Slice) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i2 ← pure ((p0).fillFn)
    let i3 ← pure ((p0).ptr)
    let _i4 ← (Zig.callC (Zig.extCall (Ext.call0 i2 i3 p1)))
    pure .ret) : Zig.CM Tgt Random_bytesLocals Random_bytesExit).run' (default : Random_bytesLocals)
  match e with
  | .ret => pure ()

structure rollLocals where
  b : Zig.Ptr
  deriving Inhabited

inductive rollExit where
  | ret (v : BitVec 8)

def roll [Ext] (p0 : Random) : Zig.ConcM Tgt (BitVec 8) := do
  let s1 ← Zig.allocStack 1 1
  let e ← ((do
    let i1 ← pure (← get).b
    Zig.storeUndef (Vector (BitVec 8) 1) 1 i1
    let i3 ← pure (⟨i1, (1 : BitVec 64)⟩ : Zig.Slice)
    let _i4 ← Zig.callC (Random_bytes p0 i3)
    let i5 ← Zig.callMC (Zig.load (BitVec 8) 1 (i1.elem 1 (0 : BitVec 64)))
    let i6 ← Zig.rem false i5 (6 : BitVec 8)
    let i7 ← Zig.add false i6 (1 : BitVec 8)
    pure (.ret i7)) : Zig.CM Tgt rollLocals rollExit).run' { (default : rollLocals) with b := s1 }
  Zig.free s1
  match e with
  | .ret v => pure v

/-- Runs a spawn target (`Zig.Sched.run`). -/
def dispatch [Ext] : Tgt → Zig.ConcM Tgt Unit :=
  fun t => nomatch t

end Interfaces.Rnd