-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...7.2-musl","zig_version":"0.17.0"}}
import ZigLean


namespace Counted

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ []

structure downLocals where
  i : BitVec 32
  deriving Inhabited

inductive downExit where
  | ret
  | br6
  | br4
  | rep5

def down.again5 : downExit → Bool
  | .rep5 => true
  | _ => false

def down.loop5 (p0 : Zig.Ptr) : Zig.MM downLocals downExit := do
  Zig.callM Zig.tick
  match ← ((do
    let i7 ← pure ((← get).i)
    let i8 ← pure (Zig.gt false i7 (0 : BitVec 32))
    if i8 then (do
      let i10 ← Zig.load (BitVec 64) 8 p0
      let i11 ← Zig.add false i10 (3 : BitVec 64)
      Zig.store (α := BitVec 64) 8 p0 i11
      let i13 ← pure ((← get).i)
      let i14 ← Zig.sub false i13 (1 : BitVec 32)
      modify (fun s => { s with i := i14 })
      pure .br6)
    else (do
      pure .br4)) : Zig.MM downLocals downExit) with
  | .br6 => (do
    pure .rep5)
  | e => pure e

def down (p0 : Zig.Ptr) (p1 : BitVec 32) : Zig.MemM (Unit) := do
  let e ← ((do
    modify (fun s => { s with i := p1 })
    match ← ((do
      Zig.loop (down.loop5 p0) down.again5) : Zig.MM downLocals downExit) with
    | .br4 => (do
      pure .ret)
    | e => pure e) : Zig.MM downLocals downExit).run' (default : downLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure lenCountLocals where
  i : BitVec 64
  deriving Inhabited

inductive lenCountExit where
  | ret
  | br6
  | br4
  | rep5

def lenCount.again5 : lenCountExit → Bool
  | .rep5 => true
  | _ => false

def lenCount.loop5 (p0 : Zig.Ptr) (p1 : Zig.Slice) : Zig.MM lenCountLocals lenCountExit := do
  Zig.callM Zig.tick
  match ← ((do
    let i7 ← pure ((← get).i)
    let i8 ← pure p1.len
    let i9 ← pure (i7)
    let i10 ← pure (i8)
    let i11 ← pure (Zig.lt false i9 i10)
    if i11 then (do
      let i13 ← Zig.load (BitVec 64) 8 p0
      let i14 ← Zig.add false i13 (1 : BitVec 64)
      Zig.store (α := BitVec 64) 8 p0 i14
      let i16 ← pure ((← get).i)
      let i17 ← Zig.add false i16 (1 : BitVec 64)
      modify (fun s => { s with i := i17 })
      pure .br6)
    else (do
      pure .br4)) : Zig.MM lenCountLocals lenCountExit) with
  | .br6 => (do
    pure .rep5)
  | e => pure e

def lenCount (p0 : Zig.Ptr) (p1 : Zig.Slice) : Zig.MemM (Unit) := do
  let e ← ((do
    modify (fun s => { s with i := (0 : BitVec 64) })
    match ← ((do
      Zig.loop (lenCount.loop5 p0 p1) lenCount.again5) : Zig.MM lenCountLocals lenCountExit) with
    | .br4 => (do
      pure .ret)
    | e => pure e) : Zig.MM lenCountLocals lenCountExit).run' (default : lenCountLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure pairAtLocals where
  i : BitVec 32
  deriving Inhabited

inductive pairAtExit where
  | ret
  | br6
  | br4
  | rep5

def pairAt.again5 : pairAtExit → Bool
  | .rep5 => true
  | _ => false

def pairAt.loop5 (p0 : Zig.Ptr) (p1 : BitVec 32) : Zig.MM pairAtLocals pairAtExit := do
  Zig.callM Zig.tick
  match ← ((do
    let i7 ← pure ((← get).i)
    let i8 ← pure (Zig.lt false i7 p1)
    if i8 then (do
      let i10 ← pure p0
      let i11 ← Zig.load (BitVec 64) 8 i10
      let i12 ← Zig.add false i11 (1 : BitVec 64)
      Zig.store (α := BitVec 64) 8 i10 i12
      let i14 ← Zig.callM (Zig.ptrProject p0 (·.elem 8 (1 : BitVec 64)))
      let i15 ← Zig.load (BitVec 64) 8 i14
      let i16 ← Zig.add false i15 (2 : BitVec 64)
      Zig.store (α := BitVec 64) 8 i14 i16
      let i18 ← pure ((← get).i)
      let i19 ← Zig.add false i18 (1 : BitVec 32)
      modify (fun s => { s with i := i19 })
      pure .br6)
    else (do
      pure .br4)) : Zig.MM pairAtLocals pairAtExit) with
  | .br6 => (do
    pure .rep5)
  | e => pure e

def pairAt (p0 : Zig.Ptr) (p1 : BitVec 32) : Zig.MemM (Unit) := do
  let e ← ((do
    modify (fun s => { s with i := (0 : BitVec 32) })
    match ← ((do
      Zig.loop (pairAt.loop5 p0 p1) pairAt.again5) : Zig.MM pairAtLocals pairAtExit) with
    | .br4 => (do
      pure .ret)
    | e => pure e) : Zig.MM pairAtLocals pairAtExit).run' (default : pairAtLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure readBoundLocals where
  i : BitVec 32
  deriving Inhabited

inductive readBoundExit where
  | ret
  | br6
  | br4
  | rep5

def readBound.again5 : readBoundExit → Bool
  | .rep5 => true
  | _ => false

def readBound.loop5 (p0 : Zig.Ptr) (p1 : Zig.Ptr) : Zig.MM readBoundLocals readBoundExit := do
  Zig.callM Zig.tick
  match ← ((do
    let i7 ← pure ((← get).i)
    let i8 ← Zig.load (BitVec 32) 4 p1
    let i9 ← pure (Zig.lt false i7 i8)
    if i9 then (do
      let i11 ← Zig.load (BitVec 64) 8 p0
      let i12 ← Zig.add false i11 (1 : BitVec 64)
      Zig.store (α := BitVec 64) 8 p0 i12
      let i14 ← pure ((← get).i)
      let i15 ← Zig.add false i14 (1 : BitVec 32)
      modify (fun s => { s with i := i15 })
      pure .br6)
    else (do
      pure .br4)) : Zig.MM readBoundLocals readBoundExit) with
  | .br6 => (do
    pure .rep5)
  | e => pure e

def readBound (p0 : Zig.Ptr) (p1 : Zig.Ptr) : Zig.MemM (Unit) := do
  let e ← ((do
    modify (fun s => { s with i := (0 : BitVec 32) })
    match ← ((do
      Zig.loop (readBound.loop5 p0 p1) readBound.again5) : Zig.MM readBoundLocals readBoundExit) with
    | .br4 => (do
      pure .ret)
    | e => pure e) : Zig.MM readBoundLocals readBoundExit).run' (default : readBoundLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure triLocals where
  i : BitVec 32
  deriving Inhabited

inductive triExit where
  | ret
  | br6
  | br4
  | rep5

def tri.again5 : triExit → Bool
  | .rep5 => true
  | _ => false

def tri.loop5 (p0 : Zig.Ptr) (p1 : BitVec 32) : Zig.MM triLocals triExit := do
  Zig.callM Zig.tick
  match ← ((do
    let i7 ← pure ((← get).i)
    let i8 ← pure (Zig.lt false i7 p1)
    if i8 then (do
      let i10 ← Zig.load (BitVec 64) 8 p0
      let i11 ← pure ((← get).i)
      let i12 ← Zig.intCast false false 64 i11 (safe := false)
      let i13 ← Zig.add false i10 i12
      Zig.store (α := BitVec 64) 8 p0 i13
      let i15 ← pure ((← get).i)
      let i16 ← Zig.add false i15 (1 : BitVec 32)
      modify (fun s => { s with i := i16 })
      pure .br6)
    else (do
      pure .br4)) : Zig.MM triLocals triExit) with
  | .br6 => (do
    pure .rep5)
  | e => pure e

def tri (p0 : Zig.Ptr) (p1 : BitVec 32) : Zig.MemM (Unit) := do
  let e ← ((do
    modify (fun s => { s with i := (0 : BitVec 32) })
    match ← ((do
      Zig.loop (tri.loop5 p0 p1) tri.again5) : Zig.MM triLocals triExit) with
    | .br4 => (do
      pure .ret)
    | e => pure e) : Zig.MM triLocals triExit).run' (default : triLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure upLeLocals where
  i : BitVec 32
  deriving Inhabited

inductive upLeExit where
  | ret
  | br6
  | br4
  | rep5

def upLe.again5 : upLeExit → Bool
  | .rep5 => true
  | _ => false

def upLe.loop5 (p0 : Zig.Ptr) (p1 : BitVec 32) : Zig.MM upLeLocals upLeExit := do
  Zig.callM Zig.tick
  match ← ((do
    let i7 ← pure ((← get).i)
    let i8 ← pure (Zig.le false i7 p1)
    if i8 then (do
      let i10 ← Zig.load (BitVec 64) 8 p0
      let i11 ← Zig.add false i10 (1 : BitVec 64)
      Zig.store (α := BitVec 64) 8 p0 i11
      let i13 ← pure ((← get).i)
      let i14 ← Zig.add false i13 (1 : BitVec 32)
      modify (fun s => { s with i := i14 })
      pure .br6)
    else (do
      pure .br4)) : Zig.MM upLeLocals upLeExit) with
  | .br6 => (do
    pure .rep5)
  | e => pure e

def upLe (p0 : Zig.Ptr) (p1 : BitVec 32) : Zig.MemM (Unit) := do
  let e ← ((do
    modify (fun s => { s with i := (0 : BitVec 32) })
    match ← ((do
      Zig.loop (upLe.loop5 p0 p1) upLe.again5) : Zig.MM upLeLocals upLeExit) with
    | .br4 => (do
      pure .ret)
    | e => pure e) : Zig.MM upLeLocals upLeExit).run' (default : upLeLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure upNeLocals where
  i : BitVec 32
  deriving Inhabited

inductive upNeExit where
  | ret
  | br6
  | br4
  | rep5

def upNe.again5 : upNeExit → Bool
  | .rep5 => true
  | _ => false

def upNe.loop5 (p0 : Zig.Ptr) (p1 : BitVec 32) : Zig.MM upNeLocals upNeExit := do
  Zig.callM Zig.tick
  match ← ((do
    let i7 ← pure ((← get).i)
    let i8 ← pure (i7 != p1)
    if i8 then (do
      let i10 ← Zig.load (BitVec 64) 8 p0
      let i11 ← Zig.add false i10 (1 : BitVec 64)
      Zig.store (α := BitVec 64) 8 p0 i11
      let i13 ← pure ((← get).i)
      let i14 ← Zig.add false i13 (1 : BitVec 32)
      modify (fun s => { s with i := i14 })
      pure .br6)
    else (do
      pure .br4)) : Zig.MM upNeLocals upNeExit) with
  | .br6 => (do
    pure .rep5)
  | e => pure e

def upNe (p0 : Zig.Ptr) (p1 : BitVec 32) : Zig.MemM (Unit) := do
  let e ← ((do
    modify (fun s => { s with i := (0 : BitVec 32) })
    match ← ((do
      Zig.loop (upNe.loop5 p0 p1) upNe.again5) : Zig.MM upNeLocals upNeExit) with
    | .br4 => (do
      pure .ret)
    | e => pure e) : Zig.MM upNeLocals upNeExit).run' (default : upNeLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

end Counted