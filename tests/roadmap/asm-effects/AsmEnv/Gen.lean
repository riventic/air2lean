-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...7.2-musl","zig_version":"0.17.0"}}
import ZigLean


namespace AsmEnv

opaque airAsmFx_2096841937 (i0 : BitVec 64) (r0 : Array Zig.Byte) : BitVec 64 × BitVec 64 × BitVec 64 × Array Zig.Byte

opaque airAsmFx_2696465393 (i0 : BitVec 8) (i1 : BitVec 64) : BitVec 64 × BitVec 64 × Array Zig.Byte

opaque airAsm_1506351414 (i0 : BitVec 64) : BitVec 64

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ []

structure copyLocals where
  d : Zig.Ptr
  s : Zig.Ptr
  c : BitVec 64
  deriving Inhabited

inductive copyExit where
  | ret

def copy (p0 : Zig.Ptr) (p1 : Zig.Ptr) (p2 : BitVec 64) : Zig.MemM (Unit) := do
  let e ← ((do
    modify (fun s => { s with d := p0 })
    modify (fun s => { s with s := p1 })
    modify (fun s => { s with c := p2 })
    let a9o0 ← pure ((← get).d)
    let a9o1 ← pure ((← get).s)
    let a9o2 ← pure ((← get).c)
    Zig.Asm.guard [(a9o0, (a9o2).toNat), (a9o1, (a9o2).toNat)]
    let a9r0 ← Zig.callM (Zig.Asm.readRegion a9o1 ((a9o2).toNat))
    let a9 := airAsmFx_2096841937 a9o2 a9r0
    Zig.callM (Zig.Asm.writeRegion a9o0 ((a9o2).toNat) a9.2.2.2)
    modify (fun s => { s with d := (Zig.Asm.movePtr a9o0 a9.1) })
    modify (fun s => { s with s := (Zig.Asm.movePtr a9o1 a9.2.1) })
    modify (fun s => { s with c := a9.2.2.1 })
    pure .ret) : Zig.MM copyLocals copyExit).run' (default : copyLocals)
  match e with
  | .ret => pure ()

structure ticksLocals where
  deriving Inhabited

inductive ticksExit where
  | ret (v : BitVec 64)

def ticks  : Zig.MemM (BitVec 64) := do
  let e ← ((do
    let i0 ← Zig.callM (Zig.Asm.envWord 64 >>= fun e0 => pure (e0))
    pure (.ret i0)) : Zig.MM ticksLocals ticksExit).run' (default : ticksLocals)
  match e with
  | .ret v => pure v

structure elapsedLocals where
  deriving Inhabited

inductive elapsedExit where
  | ret (v : BitVec 64)

def elapsed  : Zig.MemM (BitVec 64) := do
  let e ← ((do
    let i0 ← Zig.callM (ticks )
    let i1 ← Zig.callM (ticks )
    let i2 ← pure (Zig.subWrap i1 i0)
    pure (.ret i2)) : Zig.MM elapsedLocals elapsedExit).run' (default : elapsedLocals)
  match e with
  | .ret v => pure v

structure fillLocals where
  d : Zig.Ptr
  c : BitVec 64
  deriving Inhabited

inductive fillExit where
  | ret

def fill (p0 : Zig.Ptr) (p1 : BitVec 64) (p2 : BitVec 8) : Zig.MemM (Unit) := do
  let e ← ((do
    modify (fun s => { s with d := p0 })
    modify (fun s => { s with c := p1 })
    let a7o0 ← pure ((← get).d)
    let a7o1 ← pure ((← get).c)
    let a7 := airAsmFx_2696465393 p2 a7o1
    Zig.callM (Zig.Asm.writeRegion a7o0 ((a7o1).toNat) a7.2.2)
    modify (fun s => { s with d := (Zig.Asm.movePtr a7o0 a7.1) })
    modify (fun s => { s with c := a7.2.1 })
    pure .ret) : Zig.MM fillLocals fillExit).run' (default : fillLocals)
  match e with
  | .ret => pure ()

structure loadmLocals where
  deriving Inhabited

inductive loadmExit where
  | ret (v : BitVec 64)

def loadm (p0 : Zig.Ptr) : Zig.MemM (BitVec 64) := do
  let e ← ((do
    let i1 ← Zig.load (BitVec 64) 8 p0
    let i2 ← pure (airAsm_1506351414 i1)
    pure (.ret i2)) : Zig.MM loadmLocals loadmExit).run' (default : loadmLocals)
  match e with
  | .ret v => pure v

structure rand64Locals where
  v : BitVec 64
  f : BitVec 8
  deriving Inhabited

inductive rand64Exit where
  | ret (v : BitVec 64)

def rand64 (p0 : Zig.Ptr) : Zig.MemM (BitVec 64) := do
  let e ← ((do
    modify (fun s => { s with v := (0#64) })
    modify (fun s => { s with f := (0#8) })
    let a5 ← Zig.callM (Zig.Asm.envWord 64 >>= fun e0 => Zig.Asm.envWord 8 >>= fun e1 => pure (e0, e1))
    modify (fun s => { s with v := a5.1 })
    modify (fun s => { s with f := a5.2 })
    let i6 ← pure ((← get).f)
    Zig.store (α := BitVec 8) 1 p0 i6
    let i8 ← pure ((← get).v)
    pure (.ret i8)) : Zig.MM rand64Locals rand64Exit).run' (default : rand64Locals)
  match e with
  | .ret v => pure v

structure randomLocals where
  deriving Inhabited

inductive randomExit where
  | ret (v : BitVec 64)

def random  : Zig.MemM (BitVec 64) := do
  let e ← ((do
    let i0 ← Zig.callM (Zig.Asm.envWord 64 >>= fun e0 => pure (e0))
    pure (.ret i0)) : Zig.MM randomLocals randomExit).run' (default : randomLocals)
  match e with
  | .ret v => pure v

end AsmEnv