-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"unverified","backend":"unverified","build_mode":"unverified","cpu":"unverified","endian":"little","error_layout":"reference-model","error_set_bits":16,"error_tracing":null,"export_stage":"unverified","features":[],"float_mode":"unverified","name":"legacy-abi64-le","pointer_bits":64,"schema":11,"target_triple":"unverified","zig_version":"0.16.0"}}
import ZigLean


namespace AsmEffects

opaque airAsmFx_2072205809 (i0 : BitVec 64) (i1 : BitVec 64) : BitVec 64

opaque airAsmFx_1655126372 : Unit

opaque airAsmFx_2360474586 (i0 : BitVec 32) : BitVec 32

opaque airAsmFx_2840265087 (i0 : BitVec 32) : BitVec 32

opaque airAsmFx_2229968081 (i0 : BitVec 64) : BitVec 64

opaque airAsmFx_3102165980 (i0 : BitVec 32) (i1 : BitVec 32) : BitVec 32 × BitVec 32

/-- The memory at program start: block `k` is global `k`. -/
def mem0 : Zig.Mem := Zig.Mem.ofGlobals []

structure addrLocals where
  local2 : BitVec 64
  deriving Inhabited

inductive addrExit where
  | ret (v : BitVec 64)

def addr (p0 : BitVec 64) (p1 : BitVec 64) : Zig.Result (BitVec 64) := do
  let e ← ((do
    modify (fun s => { s with local2 := p0 })
    let a4o0 ← pure ((← get).local2)
    let a4 := airAsmFx_2072205809 p1 a4o0
    modify (fun s => { s with local2 := a4 })
    let i5 ← pure ((← get).local2)
    pure (.ret i5)) : Zig.M addrLocals addrExit).run' (default : addrLocals)
  match e with
  | .ret v => pure v

structure barrierLocals where
  deriving Inhabited

inductive barrierExit where
  | ret

def barrier  : Zig.Result (Unit) := do
  let e ← ((do
    let _i0 ← pure (airAsmFx_1655126372)
    pure .ret) : Zig.M barrierLocals barrierExit).run' (default : barrierLocals)
  match e with
  | .ret => pure ()

structure incLocalLocals where
  local1 : BitVec 32
  deriving Inhabited

inductive incLocalExit where
  | ret (v : BitVec 32)

def incLocal (p0 : BitVec 32) : Zig.Result (BitVec 32) := do
  let e ← ((do
    modify (fun s => { s with local1 := p0 })
    let a3o0 ← pure ((← get).local1)
    let a3 := airAsmFx_2360474586 a3o0
    modify (fun s => { s with local1 := a3 })
    let i4 ← pure ((← get).local1)
    pure (.ret i4)) : Zig.M incLocalLocals incLocalExit).run' (default : incLocalLocals)
  match e with
  | .ret v => pure v

structure incmLocals where
  deriving Inhabited

inductive incmExit where
  | ret

def incm (p0 : Zig.Ptr) : Zig.MemM (Unit) := do
  let e ← ((do
    let a1o0 ← Zig.load (BitVec 32) 4 p0
    let a1 := airAsmFx_2840265087 a1o0
    Zig.store (α := BitVec 32) 4 p0 a1
    pure .ret) : Zig.MM incmLocals incmExit).run' (default : incmLocals)
  match e with
  | .ret => pure ()

structure setmLocals where
  deriving Inhabited

inductive setmExit where
  | ret

def setm (p0 : Zig.Ptr) (p1 : BitVec 64) : Zig.MemM (Unit) := do
  let e ← ((do
    let a2 := airAsmFx_2229968081 p1
    Zig.store (α := BitVec 64) 8 p0 a2
    pure .ret) : Zig.MM setmLocals setmExit).run' (default : setmLocals)
  match e with
  | .ret => pure ()

structure swapmLocals where
  deriving Inhabited

inductive swapmExit where
  | ret

def swapm (p0 : Zig.Ptr) (p1 : Zig.Ptr) : Zig.MemM (Unit) := do
  let e ← ((do
    Zig.Asm.guard [(p0, 4), (p1, 4)]
    let a2o0 ← Zig.load (BitVec 32) 4 p0
    let a2o1 ← Zig.load (BitVec 32) 4 p1
    let a2 := airAsmFx_3102165980 a2o0 a2o1
    Zig.store (α := BitVec 32) 4 p0 a2.1
    Zig.store (α := BitVec 32) 4 p1 a2.2
    pure .ret) : Zig.MM swapmLocals swapmExit).run' (default : swapmLocals)
  match e with
  | .ret => pure ()

end AsmEffects