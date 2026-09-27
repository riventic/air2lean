import ZigLean


namespace Basic

structure Job where
  duration : BitVec 32
  due : BitVec 32
  weight : BitVec 8
  deriving Repr, Inhabited, DecidableEq

structure absDiffLocals where
  deriving Inhabited

inductive absDiffExit where
  | ret (v : BitVec 32)
  | br2

def absDiff (p0 : BitVec 32) (p1 : BitVec 32) : Zig.Result (BitVec 32) := do
  let e ← ((do
    match ← ((do
      let i3 ← pure (Zig.gt true p0 p1)
      if i3 then (do
        let i5 ← Zig.sub true p0 p1
        let i6 ← Zig.intCast true false 32 i5
        pure (.ret i6))
      else (do
        pure .br2)) : Zig.M absDiffLocals absDiffExit) with
    | .br2 => (do
      let i9 ← Zig.sub true p1 p0
      let i10 ← Zig.intCast true false 32 i9
      pure (.ret i10))
    | e => pure e) : Zig.M absDiffLocals absDiffExit).run' (default : absDiffLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure clampAddLocals where
  deriving Inhabited

inductive clampAddExit where
  | ret (v : BitVec 16)

def clampAdd (p0 : BitVec 16) (p1 : BitVec 16) : Zig.Result (BitVec 16) := do
  let e ← ((do
    let i2 ← pure (Zig.addSat false p0 p1)
    pure (.ret i2)) : Zig.M clampAddLocals clampAddExit).run' (default : clampAddLocals)
  match e with
  | .ret v => pure v

structure classifyLocals where
  deriving Inhabited

inductive classifyExit where
  | ret (v : BitVec 8)
  | br1 (v : BitVec 8)

def classify (p0 : BitVec 8) : Zig.Result (BitVec 8) := do
  let e ← ((do
    match ← ((do
      if p0 == (0 : BitVec 8) then (do
        pure (.br1 (0 : BitVec 8)))
      else (do
        if (Zig.le false (1 : BitVec 8) p0 && Zig.le false p0 (9 : BitVec 8)) then (do
          pure (.br1 (1 : BitVec 8)))
        else (do
          pure (.br1 (2 : BitVec 8))))) : Zig.M classifyLocals classifyExit) with
    | .br1 v1 => (do
      pure (.ret v1))
    | e => pure e) : Zig.M classifyLocals classifyExit).run' (default : classifyLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure scaleLocals where
  deriving Inhabited

inductive scaleExit where
  | ret (v : BitVec 32)

def scale (p0 : BitVec 32) (p1 : BitVec 8) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i2 ← Zig.intCast false false 32 p1
    let i3 ← Zig.mul false p0 i2
    pure (.ret i3)) : Zig.M scaleLocals scaleExit).run' (default : scaleLocals)
  match e with
  | .ret v => pure v

structure sumLocals where
  total : BitVec 64
  local3 : BitVec 64
  deriving Inhabited

inductive sumExit where
  | ret (v : BitVec 64)
  | br9
  | br6
  | rep7

def sum.again7 : sumExit → Bool
  | .rep7 => true
  | _ => false

def sum.loop7 (p0 : Array (BitVec 32)) (i5 : BitVec 64) : Zig.M sumLocals sumExit := do
  let i8 ← pure ((← get).local3)
  match ← ((do
    let i10 ← pure (i8)
    let i11 ← pure (i5)
    let i12 ← pure (Zig.lt false i10 i11)
    if i12 then (do
      let i14 ← Zig.call (Zig.index p0 i8)
      let i15 ← pure ((← get).total)
      let i16 ← Zig.intCast false false 64 i14
      let i17 ← Zig.add false i15 i16
      modify (fun s => { s with total := i17 })
      pure .br9)
    else (do
      pure .br6)) : Zig.M sumLocals sumExit) with
  | .br9 => (do
    let i21 ← Zig.add false i8 (1 : BitVec 64)
    modify (fun s => { s with local3 := i21 })
    pure .rep7)
  | e => pure e

def sum (p0 : Array (BitVec 32)) : Zig.Result (BitVec 64) := do
  let e ← ((do
    modify (fun s => { s with total := (0 : BitVec 64) })
    modify (fun s => { s with local3 := (0 : BitVec 64) })
    let i5 ← pure (Zig.len p0)
    match ← ((do
      Zig.loop (sum.loop7 p0 i5) sum.again7) : Zig.M sumLocals sumExit) with
    | .br6 => (do
      let i24 ← pure ((← get).total)
      pure (.ret i24))
    | e => pure e) : Zig.M sumLocals sumExit).run' (default : sumLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure tardinessLocals where
  deriving Inhabited

inductive tardinessExit where
  | ret (v : BitVec 32)
  | br2 (v : BitVec 32)

def tardiness (p0 : BitVec 32) (p1 : BitVec 32) : Zig.Result (BitVec 32) := do
  let e ← ((do
    match ← ((do
      let i3 ← pure (Zig.gt false p0 p1)
      if i3 then (do
        let i5 ← Zig.sub false p0 p1
        pure (.br2 i5))
      else (do
        pure (.br2 (0 : BitVec 32)))) : Zig.M tardinessLocals tardinessExit) with
    | .br2 v2 => (do
      pure (.ret v2))
    | e => pure e) : Zig.M tardinessLocals tardinessExit).run' (default : tardinessLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure weightedTardinessLocals where
  deriving Inhabited

inductive weightedTardinessExit where
  | ret (v : BitVec 32)

def weightedTardiness (p0 : Job) (p1 : BitVec 32) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i2 ← pure ((p0).duration)
    let i3 ← Zig.add false p1 i2
    let i4 ← pure ((p0).due)
    let i5 ← Zig.call (tardiness i3 i4)
    let i6 ← pure ((p0).weight)
    let i7 ← Zig.intCast false false 32 i6
    let i8 ← Zig.mul false i5 i7
    pure (.ret i8)) : Zig.M weightedTardinessLocals weightedTardinessExit).run' (default : weightedTardinessLocals)
  match e with
  | .ret v => pure v

structure totalWeightedTardinessLocals where
  t : BitVec 32
  cost : BitVec 64
  i : BitVec 64
  deriving Inhabited

inductive totalWeightedTardinessExit where
  | ret (v : BitVec 64)
  | br20
  | br35
  | br9
  | br7
  | rep8

def totalWeightedTardiness.again8 : totalWeightedTardinessExit → Bool
  | .rep8 => true
  | _ => false

def totalWeightedTardiness.loop8 (p0 : Array (Job)) : Zig.M totalWeightedTardinessLocals totalWeightedTardinessExit := do
  match ← ((do
    let i10 ← pure ((← get).i)
    let i11 ← pure (Zig.len p0)
    let i12 ← pure (i10)
    let i13 ← pure (i11)
    let i14 ← pure (Zig.lt false i12 i13)
    if i14 then (do
      let i16 ← pure ((← get).cost)
      let i17 ← pure ((← get).i)
      let i18 ← pure (Zig.len p0)
      let i19 ← pure (Zig.lt false i17 i18)
      match ← ((do
        if i19 then (do
          pure .br20)
        else (do
          throw .outOfBounds)) : Zig.M totalWeightedTardinessLocals totalWeightedTardinessExit) with
      | .br20 => (do
        let i25 ← Zig.call (Zig.index p0 i17)
        let i26 ← pure ((← get).t)
        let i27 ← Zig.call (weightedTardiness i25 i26)
        let i28 ← Zig.intCast false false 64 i27
        let i29 ← Zig.add false i16 i28
        modify (fun s => { s with cost := i29 })
        let i31 ← pure ((← get).t)
        let i32 ← pure ((← get).i)
        let i33 ← pure (Zig.len p0)
        let i34 ← pure (Zig.lt false i32 i33)
        match ← ((do
          if i34 then (do
            pure .br35)
          else (do
            throw .outOfBounds)) : Zig.M totalWeightedTardinessLocals totalWeightedTardinessExit) with
        | .br35 => (do
          let i40 ← Zig.call (Zig.index p0 i32)
          let i41 ← pure ((i40).duration)
          let i42 ← Zig.add false i31 i41
          modify (fun s => { s with t := i42 })
          let i44 ← pure ((← get).i)
          let i45 ← Zig.add false i44 (1 : BitVec 64)
          modify (fun s => { s with i := i45 })
          pure .br9)
        | e => pure e)
      | e => pure e)
    else (do
      pure .br7)) : Zig.M totalWeightedTardinessLocals totalWeightedTardinessExit) with
  | .br9 => (do
    pure .rep8)
  | e => pure e

def totalWeightedTardiness (p0 : Array (Job)) : Zig.Result (BitVec 64) := do
  let e ← ((do
    modify (fun s => { s with t := (0 : BitVec 32) })
    modify (fun s => { s with cost := (0 : BitVec 64) })
    modify (fun s => { s with i := (0 : BitVec 64) })
    match ← ((do
      Zig.loop (totalWeightedTardiness.loop8 p0) totalWeightedTardiness.again8) : Zig.M totalWeightedTardinessLocals totalWeightedTardinessExit) with
    | .br7 => (do
      let i50 ← pure ((← get).cost)
      pure (.ret i50))
    | e => pure e) : Zig.M totalWeightedTardinessLocals totalWeightedTardinessExit).run' (default : totalWeightedTardinessLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

end Basic