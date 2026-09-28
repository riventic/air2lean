import ZigLean


namespace Vectors

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

end Vectors