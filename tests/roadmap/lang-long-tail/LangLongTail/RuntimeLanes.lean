-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.16-musl","zig_version":"0.15.2"}}
import ZigLean


namespace RuntimeLanes

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ []

structure fillSumLocals where
  v : Zig.Ptr
  i : BitVec 64
  deriving Inhabited

inductive fillSumExit where
  | ret (v : BitVec 9)
  | br12 (v : Bool)
  | br22
  | br7
  | br5
  | rep6

def fillSum.again6 : fillSumExit → Bool
  | .rep6 => true
  | _ => false

def fillSum.loop6 (p0 : BitVec 64) (i1 : Zig.Ptr) : Zig.MM fillSumLocals fillSumExit := do
  match ← ((do
    let i8 ← pure ((← get).i)
    let i9 ← pure (i8)
    let i10 ← pure (p0)
    let i11 ← pure (Zig.lt false i9 i10)
    match ← ((do
      if i11 then (do
        let i14 ← pure ((← get).i)
        let i15 ← pure (i14)
        let i16 ← pure (Zig.lt false i15 (4 : BitVec 64))
        pure (.br12 i16))
      else (do
        pure (.br12 false))) : Zig.MM fillSumLocals fillSumExit) with
    | .br12 v12 => (do
      if v12 then (do
        let i20 ← pure ((← get).i)
        let i21 ← pure (Zig.lt false i20 (4 : BitVec 64))
        match ← ((do
          if i21 then (do
            pure .br22)
          else (do
            throw .outOfBounds)) : Zig.MM fillSumLocals fillSumExit) with
        | .br22 => (do
          let i27 ← pure ((← get).i)
          let i28 ← Zig.mul false i27 (100 : BitVec 64)
          let i29 ← Zig.add false i28 (7 : BitVec 64)
          let i30 ← Zig.intCast false false 9 i29
          Zig.storeLaneAt (α := BitVec 9) 4 5 8 i1 i20 i30
          let i32 ← pure ((← get).i)
          let i33 ← Zig.add false i32 (1 : BitVec 64)
          modify (fun s => { s with i := i33 })
          pure .br7)
        | e => pure e)
      else (do
        pure .br5))
    | e => pure e) : Zig.MM fillSumLocals fillSumExit) with
  | .br7 => (do
    pure .rep6)
  | e => pure e

def fillSum (p0 : BitVec 64) : Zig.MemM (BitVec 9) := do
  let s1 ← Zig.allocStack 8 8
  let e ← ((do
    let i1 ← pure (← get).v
    Zig.store (α := Zig.Vec (BitVec 9) 4) 8 i1 ((⟨#v[(1 : BitVec 9), (1 : BitVec 9), (1 : BitVec 9), (1 : BitVec 9)]⟩) : Zig.Vec (BitVec 9) 4)
    modify (fun s => { s with i := (0 : BitVec 64) })
    match ← ((do
      Zig.loop (fillSum.loop6 p0 i1) fillSum.again6) : Zig.MM fillSumLocals fillSumExit) with
    | .br5 => (do
      let i38 ← Zig.load (Zig.Vec (BitVec 9) 4) 8 i1
      let i39 ← Zig.callR (Zig.vindex i38.lanes (0 : BitVec 64))
      let i40 ← Zig.load (Zig.Vec (BitVec 9) 4) 8 i1
      let i41 ← Zig.callR (Zig.vindex i40.lanes (1 : BitVec 64))
      let i42 ← pure (Zig.addWrap i39 i41)
      let i43 ← Zig.load (Zig.Vec (BitVec 9) 4) 8 i1
      let i44 ← Zig.callR (Zig.vindex i43.lanes (2 : BitVec 64))
      let i45 ← pure (Zig.addWrap i42 i44)
      let i46 ← Zig.load (Zig.Vec (BitVec 9) 4) 8 i1
      let i47 ← Zig.callR (Zig.vindex i46.lanes (3 : BitVec 64))
      let i48 ← pure (Zig.addWrap i45 i47)
      pure (.ret i48))
    | e => pure e) : Zig.MM fillSumLocals fillSumExit).run' { (default : fillSumLocals) with v := s1 }
  Zig.free s1
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure setBoolLocals where
  deriving Inhabited

inductive setBoolExit where
  | ret
  | br4

def setBool (p0 : Zig.Ptr) (p1 : BitVec 64) (p2 : Bool) : Zig.MemM (Unit) := do
  let e ← ((do
    let i3 ← pure (Zig.lt false p1 (5 : BitVec 64))
    match ← ((do
      if i3 then (do
        pure .br4)
      else (do
        throw .outOfBounds)) : Zig.MM setBoolLocals setBoolExit) with
    | .br4 => (do
      Zig.storeLaneAt (α := Bool) 5 1 1 p0 p1 p2
      pure .ret)
    | e => pure e) : Zig.MM setBoolLocals setBoolExit).run' (default : setBoolLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure setF80Locals where
  deriving Inhabited

inductive setF80Exit where
  | ret
  | br4

def setF80 (p0 : Zig.Ptr) (p1 : BitVec 64) (p2 : Zig.F80) : Zig.MemM (Unit) := do
  let e ← ((do
    let i3 ← pure (Zig.lt false p1 (2 : BitVec 64))
    match ← ((do
      if i3 then (do
        pure .br4)
      else (do
        throw .outOfBounds)) : Zig.MM setF80Locals setF80Exit) with
    | .br4 => (do
      Zig.storeLaneAt (α := Zig.F80) 2 20 32 p0 p1 p2
      pure .ret)
    | e => pure e) : Zig.MM setF80Locals setF80Exit).run' (default : setF80Locals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure setU24Locals where
  deriving Inhabited

inductive setU24Exit where
  | ret
  | br4

def setU24 (p0 : Zig.Ptr) (p1 : BitVec 64) (p2 : BitVec 24) : Zig.MemM (Unit) := do
  let e ← ((do
    let i3 ← pure (Zig.lt false p1 (3 : BitVec 64))
    match ← ((do
      if i3 then (do
        pure .br4)
      else (do
        throw .outOfBounds)) : Zig.MM setU24Locals setU24Exit) with
    | .br4 => (do
      Zig.storeLaneAt (α := BitVec 24) 3 9 16 p0 p1 p2
      pure .ret)
    | e => pure e) : Zig.MM setU24Locals setU24Exit).run' (default : setU24Locals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure setU9Locals where
  deriving Inhabited

inductive setU9Exit where
  | ret
  | br4

def setU9 (p0 : Zig.Ptr) (p1 : BitVec 64) (p2 : BitVec 9) : Zig.MemM (Unit) := do
  let e ← ((do
    let i3 ← pure (Zig.lt false p1 (4 : BitVec 64))
    match ← ((do
      if i3 then (do
        pure .br4)
      else (do
        throw .outOfBounds)) : Zig.MM setU9Locals setU9Exit) with
    | .br4 => (do
      Zig.storeLaneAt (α := BitVec 9) 4 5 8 p0 p1 p2
      pure .ret)
    | e => pure e) : Zig.MM setU9Locals setU9Exit).run' (default : setU9Locals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

end RuntimeLanes