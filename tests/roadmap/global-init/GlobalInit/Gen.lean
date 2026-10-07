-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"unverified","backend":"unverified","build_mode":"unverified","cpu":"unverified","endian":"little","error_layout":"reference-model","error_set_bits":16,"error_tracing":null,"export_stage":"unverified","features":[],"float_mode":"unverified","name":"legacy-abi64-le","pointer_bits":64,"schema":11,"target_triple":"unverified","zig_version":"0.16.0"}}
import ZigLean


namespace GlobalInit

/-- External initial state: the initial value of each `extern` global, which this program does not define. Fields follow block (initialization) order. Contract: the external definition holds a valid encoding of the field's type before the program starts; any other assumption about external storage is a hypothesis on this value. -/
structure ExternInit where
  /-- Block 0: `global_init.counter` (`var`, writable). -/
  counter : BitVec 32
  /-- Block 1: `global_init.limit` (`const`, read-only). -/
  limit : BitVec 32

/-- The memory at program start: block `k` is global `k`. Blocks are added in order; an `extern` block holds its `ext` field, never a default. -/
def mem0 (ext : ExternInit) : Zig.Mem := Zig.Mem.ofGlobals [
  -- 0: global_init.counter (extern: initial value `ext.counter`)
  (Zig.Enc.encode (ext.counter : BitVec 32), 4, .global),
  -- 1: global_init.limit (extern: initial value `ext.limit`)
  (Zig.Enc.encode (ext.limit : BitVec 32), 4, .constGlobal),
  -- 2: global_init.scratch
  (Array.replicate (Zig.Enc.size (BitVec 32)) .undef, 4, .global)]

structure bumpLocals where
  deriving Inhabited

inductive bumpExit where
  | ret (v : BitVec 32)

def bump  : Zig.MemM (BitVec 32) := do
  let e ← ((do
    let i0 ← Zig.load (BitVec 32) 4 (⟨some 0, 0⟩ : Zig.Ptr)
    let i1 ← Zig.add false i0 (1 : BitVec 32)
    Zig.store (α := BitVec 32) 4 (⟨some 0, 0⟩ : Zig.Ptr) i1
    let i3 ← Zig.load (BitVec 32) 4 (⟨some 0, 0⟩ : Zig.Ptr)
    pure (.ret i3)) : Zig.MM bumpLocals bumpExit).run' (default : bumpLocals)
  match e with
  | .ret v => pure v

structure readLimitLocals where
  deriving Inhabited

inductive readLimitExit where
  | ret (v : BitVec 32)

def readLimit  : Zig.MemM (BitVec 32) := do
  let e ← ((do
    let i0 ← Zig.load (BitVec 32) 4 (⟨some 1, 0⟩ : Zig.Ptr)
    pure (.ret i0)) : Zig.MM readLimitLocals readLimitExit).run' (default : readLimitLocals)
  match e with
  | .ret v => pure v

structure readScratchLocals where
  deriving Inhabited

inductive readScratchExit where
  | ret (v : BitVec 32)

def readScratch  : Zig.MemM (BitVec 32) := do
  let e ← ((do
    let i0 ← Zig.load (BitVec 32) 4 (⟨some 2, 0⟩ : Zig.Ptr)
    pure (.ret i0)) : Zig.MM readScratchLocals readScratchExit).run' (default : readScratchLocals)
  match e with
  | .ret v => pure v

structure setScratchLocals where
  deriving Inhabited

inductive setScratchExit where
  | ret (v : BitVec 32)

def setScratch (p0 : BitVec 32) : Zig.MemM (BitVec 32) := do
  let e ← ((do
    Zig.store (α := BitVec 32) 4 (⟨some 2, 0⟩ : Zig.Ptr) p0
    let i2 ← Zig.load (BitVec 32) 4 (⟨some 2, 0⟩ : Zig.Ptr)
    pure (.ret i2)) : Zig.MM setScratchLocals setScratchExit).run' (default : setScratchLocals)
  match e with
  | .ret v => pure v

end GlobalInit