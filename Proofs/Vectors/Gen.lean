import ZigLean


namespace Vectors

/-- The memory at program start: block `k` is global `k`. -/
def mem0 : Zig.Mem := Zig.Mem.ofGlobals []

structure addToLocals where
  deriving Inhabited

inductive addToExit where
  | ret

def addTo (p0 : Zig.Ptr) (p1 : Zig.Vec (BitVec 32) 4) : Zig.MemM (Unit) := do
  let e ← ((do
    let i2 ← Zig.load (Zig.Vec (BitVec 32) 4) 16 p0
    let i3 ← pure (Zig.Vec.map2 Zig.addWrap i2 p1)
    Zig.store (α := Zig.Vec (BitVec 32) 4) 16 p0 i3
    pure .ret) : Zig.MM addToLocals addToExit).run' (default : addToLocals)
  match e with
  | .ret => pure ()

structure andLanesLocals where
  deriving Inhabited

inductive andLanesExit where
  | ret (v : BitVec 32)

def andLanes (p0 : Zig.Vec (BitVec 32) 4) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← pure (Zig.Vec.reduce (· &&& ·) p0)
    pure (.ret i1)) : Zig.M andLanesLocals andLanesExit).run' (default : andLanesLocals)
  match e with
  | .ret v => pure v

structure checkedAddLocals where
  deriving Inhabited

inductive checkedAddExit where
  | ret (v : Zig.Vec (BitVec 32) 4)

def checkedAdd (p0 : Zig.Vec (BitVec 32) 4) (p1 : Zig.Vec (BitVec 32) 4) : Zig.Result (Zig.Vec (BitVec 32) 4) := do
  let e ← ((do
    let i2 ← Zig.Vec.map2M (Zig.add false) p0 p1
    pure (.ret i2)) : Zig.M checkedAddLocals checkedAddExit).run' (default : checkedAddLocals)
  match e with
  | .ret v => pure v

structure fDotLocals where
  deriving Inhabited

inductive fDotExit where
  | ret (v : Zig.F32)

def fDot (p0 : Zig.Vec (Zig.F32) 4) (p1 : Zig.Vec (Zig.F32) 4) : Zig.Result (Zig.F32) := do
  let e ← ((do
    let i2 ← pure (Zig.Vec.map2 Zig.Float.mul p0 p1)
    let i3 ← pure (Zig.Vec.reduce Zig.Float.add i2)
    pure (.ret i3)) : Zig.M fDotLocals fDotExit).run' (default : fDotLocals)
  match e with
  | .ret v => pure v

structure fMaxLocals where
  deriving Inhabited

inductive fMaxExit where
  | ret (v : Zig.F32)

def fMax (p0 : Zig.Vec (Zig.F32) 4) : Zig.Result (Zig.F32) := do
  let e ← ((do
    let i1 ← Zig.Vec.reduceM Zig.Float.maxChk p0
    pure (.ret i1)) : Zig.M fMaxLocals fMaxExit).run' (default : fMaxLocals)
  match e with
  | .ret v => pure v

structure fMinLocals where
  deriving Inhabited

inductive fMinExit where
  | ret (v : Zig.F32)

def fMin (p0 : Zig.Vec (Zig.F32) 4) : Zig.Result (Zig.F32) := do
  let e ← ((do
    let i1 ← Zig.Vec.reduceM Zig.Float.minChk p0
    pure (.ret i1)) : Zig.M fMinLocals fMinExit).run' (default : fMinLocals)
  match e with
  | .ret v => pure v

structure interleaveLocals where
  deriving Inhabited

inductive interleaveExit where
  | ret (v : Zig.Vec (BitVec 32) 4)

def interleave (p0 : Zig.Vec (BitVec 32) 4) (p1 : Zig.Vec (BitVec 32) 4) : Zig.Result (Zig.Vec (BitVec 32) 4) := do
  let e ← ((do
    let i2 ← pure ((⟨#v[p0.lanes[0]!, p1.lanes[0]!, p0.lanes[1]!, p1.lanes[3]!]⟩ : Zig.Vec (BitVec 32) 4))
    pure (.ret i2)) : Zig.M interleaveLocals interleaveExit).run' (default : interleaveLocals)
  match e with
  | .ret v => pure v

structure maxLaneLocals where
  deriving Inhabited

inductive maxLaneExit where
  | ret (v : BitVec 32)

def maxLane (p0 : Zig.Vec (BitVec 32) 4) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← pure (Zig.Vec.reduce (Zig.max true) p0)
    pure (.ret i1)) : Zig.M maxLaneLocals maxLaneExit).run' (default : maxLaneLocals)
  match e with
  | .ret v => pure v

structure minLaneLocals where
  deriving Inhabited

inductive minLaneExit where
  | ret (v : BitVec 32)

def minLane (p0 : Zig.Vec (BitVec 32) 4) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← pure (Zig.Vec.reduce (Zig.min true) p0)
    pure (.ret i1)) : Zig.M minLaneLocals minLaneExit).run' (default : minLaneLocals)
  match e with
  | .ret v => pure v

structure orLanesLocals where
  deriving Inhabited

inductive orLanesExit where
  | ret (v : BitVec 32)

def orLanes (p0 : Zig.Vec (BitVec 32) 4) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← pure (Zig.Vec.reduce (· ||| ·) p0)
    pure (.ret i1)) : Zig.M orLanesLocals orLanesExit).run' (default : orLanesLocals)
  match e with
  | .ret v => pure v

structure pickLocals where
  deriving Inhabited

inductive pickExit where
  | ret (v : Zig.Vec (BitVec 32) 4)

def pick (p0 : Zig.Vec (Bool) 4) (p1 : Zig.Vec (BitVec 32) 4) (p2 : Zig.Vec (BitVec 32) 4) : Zig.Result (Zig.Vec (BitVec 32) 4) := do
  let e ← ((do
    let i3 ← pure (Zig.Vec.select p0 p1 p2)
    pure (.ret i3)) : Zig.M pickLocals pickExit).run' (default : pickLocals)
  match e with
  | .ret v => pure v

structure reverseLocals where
  deriving Inhabited

inductive reverseExit where
  | ret (v : Zig.Vec (BitVec 32) 4)

def reverse (p0 : Zig.Vec (BitVec 32) 4) : Zig.Result (Zig.Vec (BitVec 32) 4) := do
  let e ← ((do
    let i1 ← pure ((⟨#v[p0.lanes[3]!, p0.lanes[2]!, p0.lanes[1]!, p0.lanes[0]!]⟩ : Zig.Vec (BitVec 32) 4))
    pure (.ret i1)) : Zig.M reverseLocals reverseExit).run' (default : reverseLocals)
  match e with
  | .ret v => pure v

structure satAddLocals where
  deriving Inhabited

inductive satAddExit where
  | ret (v : Zig.Vec (BitVec 32) 4)

def satAdd (p0 : Zig.Vec (BitVec 32) 4) (p1 : Zig.Vec (BitVec 32) 4) : Zig.Result (Zig.Vec (BitVec 32) 4) := do
  let e ← ((do
    let i2 ← pure (Zig.Vec.map2 (Zig.addSat false) p0 p1)
    pure (.ret i2)) : Zig.M satAddLocals satAddExit).run' (default : satAddLocals)
  match e with
  | .ret v => pure v

structure splatAddLocals where
  deriving Inhabited

inductive splatAddExit where
  | ret (v : Zig.Vec (BitVec 32) 4)

def splatAdd (p0 : Zig.Vec (BitVec 32) 4) (p1 : BitVec 32) : Zig.Result (Zig.Vec (BitVec 32) 4) := do
  let e ← ((do
    let i2 ← pure (Zig.Vec.splat p1)
    let i3 ← pure (Zig.Vec.map2 Zig.addWrap p0 i2)
    pure (.ret i3)) : Zig.M splatAddLocals splatAddExit).run' (default : splatAddLocals)
  match e with
  | .ret v => pure v

structure twiceInMemLocals where
  acc : Zig.Ptr
  deriving Inhabited

inductive twiceInMemExit where
  | ret (v : Zig.Vec (BitVec 32) 4)

def twiceInMem (p0 : Zig.Vec (BitVec 32) 4) : Zig.MemM (Zig.Vec (BitVec 32) 4) := do
  let s1 ← Zig.allocStack 16 16
  let e ← ((do
    let i1 ← pure (← get).acc
    Zig.store (α := Zig.Vec (BitVec 32) 4) 16 i1 p0
    let _i3 ← Zig.callM (addTo i1 p0)
    let i4 ← Zig.load (Zig.Vec (BitVec 32) 4) 16 i1
    pure (.ret i4)) : Zig.MM twiceInMemLocals twiceInMemExit).run' { (default : twiceInMemLocals) with acc := s1 }
  Zig.free s1
  match e with
  | .ret v => pure v

structure uDotWrapLocals where
  deriving Inhabited

inductive uDotWrapExit where
  | ret (v : BitVec 32)

def uDotWrap (p0 : Zig.Vec (BitVec 32) 4) (p1 : Zig.Vec (BitVec 32) 4) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i2 ← pure (Zig.Vec.map2 Zig.mulWrap p0 p1)
    let i3 ← pure (Zig.Vec.reduce Zig.addWrap i2)
    pure (.ret i3)) : Zig.M uDotWrapLocals uDotWrapExit).run' (default : uDotWrapLocals)
  match e with
  | .ret v => pure v

structure uMinLaneLocals where
  deriving Inhabited

inductive uMinLaneExit where
  | ret (v : BitVec 32)

def uMinLane (p0 : Zig.Vec (BitVec 32) 4) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← pure (Zig.Vec.reduce (Zig.min false) p0)
    pure (.ret i1)) : Zig.M uMinLaneLocals uMinLaneExit).run' (default : uMinLaneLocals)
  match e with
  | .ret v => pure v

structure xorLanesLocals where
  deriving Inhabited

inductive xorLanesExit where
  | ret (v : BitVec 32)

def xorLanes (p0 : Zig.Vec (BitVec 32) 4) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← pure (Zig.Vec.reduce (· ^^^ ·) p0)
    pure (.ret i1)) : Zig.M xorLanesLocals xorLanesExit).run' (default : xorLanesLocals)
  match e with
  | .ret v => pure v

end Vectors