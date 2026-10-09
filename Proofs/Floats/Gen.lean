import ZigLean


namespace Floats

structure celsiusLocals where
  deriving Inhabited

inductive celsiusExit where
  | ret (v : Option (Zig.F32))
  | br1 (v : Option (Zig.F32))

def celsius (p0 : Zig.F32) : Zig.Result (Option (Zig.F32)) := do
  let e ← ((do
    match ← ((do
      let i2 ← pure (Zig.Float.lt p0 (Zig.Float.ofBits (0 : BitVec 32) : Zig.F32))
      if i2 then (do
        pure (.br1 none))
      else (do
        let i5 ← pure (Zig.Float.sub p0 (Zig.Float.ofBits (1133024051 : BitVec 32) : Zig.F32))
        let i6 ← pure (some i5)
        pure (.br1 i6))) : Zig.M celsiusLocals celsiusExit) with
    | .br1 v1 => (do
      pure (.ret v1))
    | e => pure e) : Zig.M celsiusLocals celsiusExit).run' (default : celsiusLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure clampLocals where
  deriving Inhabited

inductive clampExit where
  | ret (v : Zig.F32)
  | br3 (v : Zig.F32)
  | br7 (v : Zig.F32)

def clamp (p0 : Zig.F32) (p1 : Zig.F32) (p2 : Zig.F32) : Zig.Result (Zig.F32) := do
  let e ← ((do
    match ← ((do
      let i4 ← pure (Zig.Float.lt p0 p1)
      if i4 then (do
        pure (.br3 p1))
      else (do
        match ← ((do
          let i8 ← pure (Zig.Float.gt p0 p2)
          if i8 then (do
            pure (.br7 p2))
          else (do
            pure (.br7 p0))) : Zig.M clampLocals clampExit) with
        | .br7 v7 => (do
          pure (.br3 v7))
        | e => pure e)) : Zig.M clampLocals clampExit) with
    | .br3 v3 => (do
      pure (.ret v3))
    | e => pure e) : Zig.M clampLocals clampExit).run' (default : clampLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure dotLocals where
  s : Zig.F64
  local4 : BitVec 64
  deriving Inhabited

inductive dotExit where
  | ret (v : Zig.F64)
  | br9
  | br17
  | br14
  | rep15

def dot.again15 : dotExit → Bool
  | .rep15 => true
  | _ => false

def dot.loop15 (p0 : Array (Zig.F64)) (p1 : Array (Zig.F64)) (i6 : BitVec 64) : Zig.M dotLocals dotExit := do
  let i16 ← pure ((← get).local4)
  match ← ((do
    let i18 ← pure (i16)
    let i19 ← pure (i6)
    let i20 ← pure (Zig.lt false i18 i19)
    if i20 then (do
      let i22 ← Zig.call (Zig.index p0 i16)
      let i23 ← Zig.call (Zig.index p1 i16)
      let i24 ← pure ((← get).s)
      let i25 ← pure (Zig.Float.mul i22 i23)
      let i26 ← pure (Zig.Float.add i24 i25)
      modify (fun s => { s with s := i26 })
      pure .br17)
    else (do
      pure .br14)) : Zig.M dotLocals dotExit) with
  | .br17 => (do
    let i30 ← Zig.add false i16 (1 : BitVec 64)
    modify (fun s => { s with local4 := i30 })
    pure .rep15)
  | e => pure e

def dot (p0 : Array (Zig.F64)) (p1 : Array (Zig.F64)) : Zig.Result (Zig.F64) := do
  let e ← ((do
    modify (fun s => { s with s := (Zig.Float.ofBits (0 : BitVec 64) : Zig.F64) })
    modify (fun s => { s with local4 := (0 : BitVec 64) })
    let i6 ← pure (Zig.len p0)
    let i7 ← pure (Zig.len p1)
    let i8 ← pure (i6 == i7)
    match ← ((do
      if i8 then (do
        pure .br9)
      else (do
        throw .panic)) : Zig.M dotLocals dotExit) with
    | .br9 => (do
      match ← ((do
        Zig.loop (dot.loop15 p0 p1 i6) dot.again15) : Zig.M dotLocals dotExit) with
      | .br14 => (do
        let i33 ← pure ((← get).s)
        pure (.ret i33))
      | e => pure e)
    | e => pure e) : Zig.M dotLocals dotExit).run' (default : dotLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure fitnessLocals where
  s : Zig.F64
  local6 : BitVec 64
  deriving Inhabited

inductive fitnessExit where
  | ret (v : Zig.F64)
  | br11
  | br19
  | br16
  | rep17

def fitness.again17 : fitnessExit → Bool
  | .rep17 => true
  | _ => false

def fitness.loop17 (p0 : Array (Zig.F64)) (p1 : Array (Zig.F64)) (p2 : Zig.F64) (p3 : Zig.F64) (i8 : BitVec 64) : Zig.M fitnessLocals fitnessExit := do
  let i18 ← pure ((← get).local6)
  match ← ((do
    let i20 ← pure (i18)
    let i21 ← pure (i8)
    let i22 ← pure (Zig.lt false i20 i21)
    if i22 then (do
      let i24 ← Zig.call (Zig.index p0 i18)
      let i25 ← Zig.call (Zig.index p1 i18)
      let i26 ← pure (Zig.Float.sub i24 p2)
      let i27 ← pure ((← get).s)
      let i28 ← pure (Zig.Float.mul i25 i24)
      let i29 ← pure (Zig.Float.mul i26 i26)
      let i30 ← pure (Zig.Float.mul p3 i29)
      let i31 ← pure (Zig.Float.sub i28 i30)
      let i32 ← pure (Zig.Float.add i27 i31)
      modify (fun s => { s with s := i32 })
      pure .br19)
    else (do
      pure .br16)) : Zig.M fitnessLocals fitnessExit) with
  | .br19 => (do
    let i36 ← Zig.add false i18 (1 : BitVec 64)
    modify (fun s => { s with local6 := i36 })
    pure .rep17)
  | e => pure e

def fitness (p0 : Array (Zig.F64)) (p1 : Array (Zig.F64)) (p2 : Zig.F64) (p3 : Zig.F64) : Zig.Result (Zig.F64) := do
  let e ← ((do
    modify (fun s => { s with s := (Zig.Float.ofBits (0 : BitVec 64) : Zig.F64) })
    modify (fun s => { s with local6 := (0 : BitVec 64) })
    let i8 ← pure (Zig.len p0)
    let i9 ← pure (Zig.len p1)
    let i10 ← pure (i8 == i9)
    match ← ((do
      if i10 then (do
        pure .br11)
      else (do
        throw .panic)) : Zig.M fitnessLocals fitnessExit) with
    | .br11 => (do
      match ← ((do
        Zig.loop (fitness.loop17 p0 p1 p2 p3 i8) fitness.again17) : Zig.M fitnessLocals fitnessExit) with
      | .br16 => (do
        let i39 ← pure ((← get).s)
        pure (.ret i39))
      | e => pure e)
    | e => pure e) : Zig.M fitnessLocals fitnessExit).run' (default : fitnessLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure hypot2Locals where
  deriving Inhabited

inductive hypot2Exit where
  | ret (v : Zig.F64)

def hypot2 (p0 : Zig.F64) (p1 : Zig.F64) : Zig.Result (Zig.F64) := do
  let e ← ((do
    let i2 ← pure (Zig.Float.mul p0 p0)
    let i3 ← pure (Zig.Float.mul p1 p1)
    let i4 ← pure (Zig.Float.add i2 i3)
    let i5 ← pure (Zig.Float.sqrt i4)
    pure (.ret i5)) : Zig.M hypot2Locals hypot2Exit).run' (default : hypot2Locals)
  match e with
  | .ret v => pure v

structure isNanLocals where
  deriving Inhabited

inductive isNanExit where
  | ret (v : Bool)

def isNan (p0 : Zig.F64) : Zig.Result (Bool) := do
  let e ← ((do
    let i1 ← pure (Zig.Float.ne p0 p0)
    pure (.ret i1)) : Zig.M isNanLocals isNanExit).run' (default : isNanLocals)
  match e with
  | .ret v => pure v

structure lerpLocals where
  deriving Inhabited

inductive lerpExit where
  | ret (v : Zig.F64)

def lerp (p0 : Zig.F64) (p1 : Zig.F64) (p2 : Zig.F64) : Zig.Result (Zig.F64) := do
  let e ← ((do
    let i3 ← pure (Zig.Float.sub p1 p0)
    let i4 ← pure (Zig.Float.mul i3 p2)
    let i5 ← pure (Zig.Float.add p0 i4)
    pure (.ret i5)) : Zig.M lerpLocals lerpExit).run' (default : lerpLocals)
  match e with
  | .ret v => pure v

end Floats