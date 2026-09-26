import ZigLean


namespace Floats

structure celsiusLocals where
  deriving Inhabited

inductive celsiusExit where
  | ret (v : Option (Zig.F32))
  | br2 (v : Option (Zig.F32))

def celsius (p0 : Zig.F32) : Zig.Result (Option (Zig.F32)) := do
  let e ← ((do
    match ← ((do
      let i3 ← pure (Zig.Float.lt p0 (Zig.Float.ofBits (0 : BitVec 32) : Zig.F32))
      if i3 then (do
        pure (.br2 none))
      else (do
        let i6 ← pure (Zig.Float.sub p0 (Zig.Float.ofBits (1133024051 : BitVec 32) : Zig.F32))
        let i7 ← pure (some i6)
        pure (.br2 i7))) : Zig.M celsiusLocals celsiusExit) with
    | .br2 v2 => (do
      pure (.ret v2))
    | e => pure e) : Zig.M celsiusLocals celsiusExit).run' (default : celsiusLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure clampLocals where
  deriving Inhabited

inductive clampExit where
  | ret (v : Zig.F32)
  | br4 (v : Zig.F32)
  | br7 (v : Zig.F32)

def clamp (p0 : Zig.F32) (p1 : Zig.F32) (p2 : Zig.F32) : Zig.Result (Zig.F32) := do
  let e ← ((do
    match ← ((do
      let i5 ← pure (Zig.Float.lt p0 p1)
      if i5 then (do
        pure (.br4 p1))
      else (do
        match ← ((do
          let i9 ← pure (Zig.Float.gt p0 p2)
          if i9 then (do
            pure (.br7 p2))
          else (do
            pure (.br7 p0))) : Zig.M clampLocals clampExit) with
        | .br7 v7 => (do
          pure (.br4 v7))
        | e => pure e)) : Zig.M clampLocals clampExit) with
    | .br4 v4 => (do
      pure (.ret v4))
    | e => pure e) : Zig.M clampLocals clampExit).run' (default : clampLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure dotLocals where
  s : Zig.F64
  local6 : BitVec 64
  deriving Inhabited

inductive dotExit where
  | ret (v : Zig.F64)
  | br14
  | br20
  | br17
  | rep18

def dot.again18 : dotExit → Bool
  | .rep18 => true
  | _ => false

def dot.loop18 (p0 : Array (Zig.F64)) (p1 : Array (Zig.F64)) (i9 : BitVec 64) : Zig.M dotLocals dotExit := do
  let i19 ← pure ((← get).local6)
  match ← ((do
    let i21 ← pure (i19)
    let i22 ← pure (i9)
    let i23 ← pure (Zig.lt false i21 i22)
    if i23 then (do
      let i24 ← Zig.call (Zig.index p0 i19)
      let i26 ← Zig.call (Zig.index p1 i19)
      let i29 ← pure ((← get).s)
      let i31 ← pure (Zig.Float.mul i24 i26)
      let i33 ← pure (Zig.Float.add i29 i31)
      modify (fun s => { s with s := i33 })
      pure .br20)
    else (do
      pure .br17)) : Zig.M dotLocals dotExit) with
  | .br20 => (do
    let i40 ← Zig.add false i19 (1 : BitVec 64)
    modify (fun s => { s with local6 := i40 })
    pure .rep18)
  | e => pure e

def dot (p0 : Array (Zig.F64)) (p1 : Array (Zig.F64)) : Zig.Result (Zig.F64) := do
  let e ← ((do
    modify (fun s => { s with s := (Zig.Float.ofBits (0 : BitVec 64) : Zig.F64) })
    modify (fun s => { s with local6 := (0 : BitVec 64) })
    let i9 ← pure (Zig.len p0)
    let i10 ← pure (Zig.len p1)
    let i11 ← pure (i9 == i10)
    match ← ((do
      if i11 then (do
        pure .br14)
      else (do
        throw .panic)) : Zig.M dotLocals dotExit) with
    | .br14 => (do
      match ← ((do
        Zig.loop (dot.loop18 p0 p1 i9) dot.again18) : Zig.M dotLocals dotExit) with
      | .br17 => (do
        let i44 ← pure ((← get).s)
        pure (.ret i44))
      | e => pure e)
    | e => pure e) : Zig.M dotLocals dotExit).run' (default : dotLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure hypot2Locals where
  deriving Inhabited

inductive hypot2Exit where
  | ret (v : Zig.F64)

def hypot2 (p0 : Zig.F64) (p1 : Zig.F64) : Zig.Result (Zig.F64) := do
  let e ← ((do
    let i3 ← pure (Zig.Float.mul p0 p0)
    let i5 ← pure (Zig.Float.mul p1 p1)
    let i7 ← pure (Zig.Float.add i3 i5)
    let i8 ← pure (Zig.Float.sqrt i7)
    pure (.ret i8)) : Zig.M hypot2Locals hypot2Exit).run' (default : hypot2Locals)
  match e with
  | .ret v => pure v

structure isNanLocals where
  deriving Inhabited

inductive isNanExit where
  | ret (v : Bool)

def isNan (p0 : Zig.F64) : Zig.Result (Bool) := do
  let e ← ((do
    let i2 ← pure (Zig.Float.ne p0 p0)
    pure (.ret i2)) : Zig.M isNanLocals isNanExit).run' (default : isNanLocals)
  match e with
  | .ret v => pure v

structure lerpLocals where
  deriving Inhabited

inductive lerpExit where
  | ret (v : Zig.F64)

def lerp (p0 : Zig.F64) (p1 : Zig.F64) (p2 : Zig.F64) : Zig.Result (Zig.F64) := do
  let e ← ((do
    let i4 ← pure (Zig.Float.sub p1 p0)
    let i6 ← pure (Zig.Float.mul i4 p2)
    let i8 ← pure (Zig.Float.add p0 i6)
    pure (.ret i8)) : Zig.M lerpLocals lerpExit).run' (default : lerpLocals)
  match e with
  | .ret v => pure v

end Floats