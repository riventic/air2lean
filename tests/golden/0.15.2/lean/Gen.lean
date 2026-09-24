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
  | br3

def absDiff (p0 : BitVec 32) (p1 : BitVec 32) : Zig.Result (BitVec 32) := do
  let e ← ((do
    match ← ((do
      let i4 ← pure (Zig.gt true p0 p1)
      if i4 then (do
        let i6 ← Zig.sub true p0 p1
        let i8 ← Zig.intCast true false 32 i6
        pure (.ret i8))
      else (do
        pure .br3)) : Zig.M absDiffLocals absDiffExit) with
    | .br3 => (do
      let i14 ← Zig.sub true p1 p0
      let i16 ← Zig.intCast true false 32 i14
      pure (.ret i16))
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
    let i3 ← pure (Zig.addSat false p0 p1)
    pure (.ret i3)) : Zig.M clampAddLocals clampAddExit).run' (default : clampAddLocals)
  match e with
  | .ret v => pure v

structure classifyLocals where
  deriving Inhabited

inductive classifyExit where
  | ret (v : BitVec 8)
  | br2 (v : BitVec 8)

def classify (p0 : BitVec 8) : Zig.Result (BitVec 8) := do
  let e ← ((do
    match ← ((do
      if p0 == (0 : BitVec 8) then (do
        pure (.br2 (0 : BitVec 8)))
      else (do
        if (Zig.le false (1 : BitVec 8) p0 && Zig.le false p0 (9 : BitVec 8)) then (do
          pure (.br2 (1 : BitVec 8)))
        else (do
          pure (.br2 (2 : BitVec 8))))) : Zig.M classifyLocals classifyExit) with
    | .br2 v2 => (do
      pure (.ret v2))
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
    let i3 ← Zig.intCast false false 32 p1
    let i4 ← Zig.mul false p0 i3
    pure (.ret i4)) : Zig.M scaleLocals scaleExit).run' (default : scaleLocals)
  match e with
  | .ret v => pure v

structure sumLocals where
  total : BitVec 64
  local5 : BitVec 64
  deriving Inhabited

inductive sumExit where
  | ret (v : BitVec 64)
  | br12
  | br9
  | rep10

def sum.again10 : sumExit → Bool
  | .rep10 => true
  | _ => false

def sum.loop10 (p0 : Array (BitVec 32)) (i8 : BitVec 64) : Zig.M sumLocals sumExit := do
  let i11 ← pure ((← get).local5)
  match ← ((do
    let i13 ← pure (i11)
    let i14 ← pure (i8)
    let i15 ← pure (Zig.lt false i13 i14)
    if i15 then (do
      let i16 ← Zig.call (Zig.index p0 i11)
      let i19 ← pure ((← get).total)
      let i20 ← Zig.intCast false false 64 i16
      let i22 ← Zig.add false i19 i20
      modify (fun s => { s with total := i22 })
      pure .br12)
    else (do
      pure .br9)) : Zig.M sumLocals sumExit) with
  | .br12 => (do
    let i29 ← Zig.add false i11 (1 : BitVec 64)
    modify (fun s => { s with local5 := i29 })
    pure .rep10)
  | e => pure e

def sum (p0 : Array (BitVec 32)) : Zig.Result (BitVec 64) := do
  let e ← ((do
    modify (fun s => { s with total := (0 : BitVec 64) })
    modify (fun s => { s with local5 := (0 : BitVec 64) })
    let i8 ← pure (Zig.len p0)
    match ← ((do
      Zig.loop (sum.loop10 p0 i8) sum.again10) : Zig.M sumLocals sumExit) with
    | .br9 => (do
      let i33 ← pure ((← get).total)
      pure (.ret i33))
    | e => pure e) : Zig.M sumLocals sumExit).run' (default : sumLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure tardinessLocals where
  deriving Inhabited

inductive tardinessExit where
  | ret (v : BitVec 32)
  | br3 (v : BitVec 32)

def tardiness (p0 : BitVec 32) (p1 : BitVec 32) : Zig.Result (BitVec 32) := do
  let e ← ((do
    match ← ((do
      let i4 ← pure (Zig.gt false p0 p1)
      if i4 then (do
        let i6 ← Zig.sub false p0 p1
        pure (.br3 i6))
      else (do
        pure (.br3 (0 : BitVec 32)))) : Zig.M tardinessLocals tardinessExit) with
    | .br3 v3 => (do
      pure (.ret v3))
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
    let i3 ← pure ((p0).duration)
    let i5 ← Zig.add false p1 i3
    let i8 ← pure ((p0).due)
    let i10 ← Zig.call (tardiness i5 i8)
    let i12 ← pure ((p0).weight)
    let i14 ← Zig.intCast false false 32 i12
    let i15 ← Zig.mul false i10 i14
    pure (.ret i15)) : Zig.M weightedTardinessLocals weightedTardinessExit).run' (default : weightedTardinessLocals)
  match e with
  | .ret v => pure v

structure totalWeightedTardinessLocals where
  t : BitVec 32
  cost : BitVec 64
  i : BitVec 64
  deriving Inhabited

inductive totalWeightedTardinessExit where
  | ret (v : BitVec 64)
  | br33
  | br52
  | br15
  | br13
  | rep14

def totalWeightedTardiness.again14 : totalWeightedTardinessExit → Bool
  | .rep14 => true
  | _ => false

def totalWeightedTardiness.loop14 (p0 : Array (Job)) : Zig.M totalWeightedTardinessLocals totalWeightedTardinessExit := do
  match ← ((do
    let i17 ← pure ((← get).i)
    let i19 ← pure (Zig.len p0)
    let i20 ← pure (i17)
    let i21 ← pure (i19)
    let i22 ← pure (Zig.lt false i20 i21)
    if i22 then (do
      let i25 ← pure ((← get).cost)
      let i27 ← pure ((← get).i)
      let i29 ← pure (Zig.len p0)
      let i30 ← pure (Zig.lt false i27 i29)
      match ← ((do
        if i30 then (do
          pure .br33)
        else (do
          throw .panic)) : Zig.M totalWeightedTardinessLocals totalWeightedTardinessExit) with
      | .br33 => (do
        let i36 ← Zig.call (Zig.index p0 i27)
        let i37 ← pure ((← get).t)
        let i39 ← Zig.call (weightedTardiness i36 i37)
        let i40 ← Zig.intCast false false 64 i39
        let i42 ← Zig.add false i25 i40
        modify (fun s => { s with cost := i42 })
        let i45 ← pure ((← get).t)
        let i46 ← pure ((← get).i)
        let i48 ← pure (Zig.len p0)
        let i49 ← pure (Zig.lt false i46 i48)
        match ← ((do
          if i49 then (do
            pure .br52)
          else (do
            throw .panic)) : Zig.M totalWeightedTardinessLocals totalWeightedTardinessExit) with
        | .br52 => (do
          let i55 ← Zig.call (Zig.index p0 i46)
          let i57 ← pure ((i55).duration)
          let i59 ← Zig.add false i45 i57
          modify (fun s => { s with t := i59 })
          let i65 ← pure ((← get).i)
          let i67 ← Zig.add false i65 (1 : BitVec 64)
          modify (fun s => { s with i := i67 })
          pure .br15)
        | e => pure e)
      | e => pure e)
    else (do
      pure .br13)) : Zig.M totalWeightedTardinessLocals totalWeightedTardinessExit) with
  | .br15 => (do
    pure .rep14)
  | e => pure e

def totalWeightedTardiness (p0 : Array (Job)) : Zig.Result (BitVec 64) := do
  let e ← ((do
    modify (fun s => { s with t := (0 : BitVec 32) })
    modify (fun s => { s with cost := (0 : BitVec 64) })
    modify (fun s => { s with i := (0 : BitVec 64) })
    match ← ((do
      Zig.loop (totalWeightedTardiness.loop14 p0) totalWeightedTardiness.again14) : Zig.M totalWeightedTardinessLocals totalWeightedTardinessExit) with
    | .br13 => (do
      let i74 ← pure ((← get).cost)
      pure (.ret i74))
    | e => pure e) : Zig.M totalWeightedTardinessLocals totalWeightedTardinessExit).run' (default : totalWeightedTardinessLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

end Basic