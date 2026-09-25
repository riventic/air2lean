import ZigLean


namespace Options

structure findLocals where
  local2 : BitVec 64
  deriving Inhabited

inductive findExit where
  | ret (v : Option (BitVec 64))
  | br17
  | br9
  | br6
  | rep7

def find.again7 : findExit → Bool
  | .rep7 => true
  | _ => false

def find.loop7 (p0 : Array (BitVec 32)) (p1 : BitVec 32) (i5 : BitVec 64) : Zig.M findLocals findExit := do
  let i8 ← pure ((← get).local2)
  match ← ((do
    let i10 ← pure (i8)
    let i11 ← pure (i5)
    let i12 ← pure (Zig.lt false i10 i11)
    if i12 then (do
      let i13 ← Zig.call (Zig.index p0 i8)
      match ← ((do
        let i18 ← pure (i13 == p1)
        if i18 then (do
          let i20 ← pure (some i8)
          pure (.ret i20))
        else (do
          pure .br17)) : Zig.M findLocals findExit) with
      | .br17 => (do
        pure .br9)
      | e => pure e)
    else (do
      pure .br6)) : Zig.M findLocals findExit) with
  | .br9 => (do
    let i29 ← Zig.add false i8 (1 : BitVec 64)
    modify (fun s => { s with local2 := i29 })
    pure .rep7)
  | e => pure e

def find (p0 : Array (BitVec 32)) (p1 : BitVec 32) : Zig.Result (Option (BitVec 64)) := do
  let e ← ((do
    modify (fun s => { s with local2 := (0 : BitVec 64) })
    let i5 ← pure (Zig.len p0)
    match ← ((do
      Zig.loop (find.loop7 p0 p1 i5) find.again7) : Zig.M findLocals findExit) with
    | .br6 => (do
      pure (.ret none))
    | e => pure e) : Zig.M findLocals findExit).run' (default : findLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure findOrLocals where
  deriving Inhabited

inductive findOrExit where
  | ret (v : BitVec 64)
  | br3 (v : BitVec 64)

def findOr (p0 : Array (BitVec 32)) (p1 : BitVec 32) : Zig.Result (BitVec 64) := do
  let e ← ((do
    match ← ((do
      let i5 ← Zig.call (find p0 p1)
      let i6 ← pure ((i5).isSome)
      if i6 then (do
        let i7 ← Zig.optPayload i5
        pure (.br3 i7))
      else (do
        let i10 ← pure (Zig.len p0)
        pure (.br3 i10))) : Zig.M findOrLocals findOrExit) with
    | .br3 v3 => (do
      pure (.ret v3))
    | e => pure e) : Zig.M findOrLocals findOrExit).run' (default : findOrLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure firstIndexPlusOneLocals where
  deriving Inhabited

inductive firstIndexPlusOneExit where
  | ret (v : BitVec 64)
  | br8

def firstIndexPlusOne (p0 : Array (BitVec 32)) (p1 : BitVec 32) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i3 ← Zig.call (find p0 p1)
    let i5 ← pure ((i3).isSome)
    match ← ((do
      if i5 then (do
        pure .br8)
      else (do
        throw .panic)) : Zig.M firstIndexPlusOneLocals firstIndexPlusOneExit) with
    | .br8 => (do
      let i11 ← Zig.optPayload i3
      let i13 ← Zig.add false i11 (1 : BitVec 64)
      pure (.ret i13))
    | e => pure e) : Zig.M firstIndexPlusOneLocals firstIndexPlusOneExit).run' (default : firstIndexPlusOneLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

end Options