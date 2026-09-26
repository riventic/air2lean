import ZigLean


namespace Options

structure findLocals where
  local2 : BitVec 64
  deriving Inhabited

inductive findExit where
  | ret (v : Option (BitVec 64))
  | br14
  | br8
  | br5
  | rep6

def find.again6 : findExit → Bool
  | .rep6 => true
  | _ => false

def find.loop6 (p0 : Array (BitVec 32)) (p1 : BitVec 32) (i4 : BitVec 64) : Zig.M findLocals findExit := do
  let i7 ← pure ((← get).local2)
  match ← ((do
    let i9 ← pure (i7)
    let i10 ← pure (i4)
    let i11 ← pure (Zig.lt false i9 i10)
    if i11 then (do
      let i13 ← Zig.call (Zig.index p0 i7)
      match ← ((do
        let i15 ← pure (i13 == p1)
        if i15 then (do
          let i17 ← pure (some i7)
          pure (.ret i17))
        else (do
          pure .br14)) : Zig.M findLocals findExit) with
      | .br14 => (do
        pure .br8)
      | e => pure e)
    else (do
      pure .br5)) : Zig.M findLocals findExit) with
  | .br8 => (do
    let i22 ← Zig.add false i7 (1 : BitVec 64)
    modify (fun s => { s with local2 := i22 })
    pure .rep6)
  | e => pure e

def find (p0 : Array (BitVec 32)) (p1 : BitVec 32) : Zig.Result (Option (BitVec 64)) := do
  let e ← ((do
    modify (fun s => { s with local2 := (0 : BitVec 64) })
    let i4 ← pure (Zig.len p0)
    match ← ((do
      Zig.loop (find.loop6 p0 p1 i4) find.again6) : Zig.M findLocals findExit) with
    | .br5 => (do
      pure (.ret none))
    | e => pure e) : Zig.M findLocals findExit).run' (default : findLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure findOrLocals where
  deriving Inhabited

inductive findOrExit where
  | ret (v : BitVec 64)
  | br2 (v : BitVec 64)

def findOr (p0 : Array (BitVec 32)) (p1 : BitVec 32) : Zig.Result (BitVec 64) := do
  let e ← ((do
    match ← ((do
      let i3 ← Zig.call (find p0 p1)
      let i4 ← pure ((i3).isSome)
      if i4 then (do
        let i6 ← Zig.optPayload i3
        pure (.br2 i6))
      else (do
        let i8 ← pure (Zig.len p0)
        pure (.br2 i8))) : Zig.M findOrLocals findOrExit) with
    | .br2 v2 => (do
      pure (.ret v2))
    | e => pure e) : Zig.M findOrLocals findOrExit).run' (default : findOrLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure firstIndexPlusOneLocals where
  deriving Inhabited

inductive firstIndexPlusOneExit where
  | ret (v : BitVec 64)
  | br4

def firstIndexPlusOne (p0 : Array (BitVec 32)) (p1 : BitVec 32) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i2 ← Zig.call (find p0 p1)
    let i3 ← pure ((i2).isSome)
    match ← ((do
      if i3 then (do
        pure .br4)
      else (do
        throw .panic)) : Zig.M firstIndexPlusOneLocals firstIndexPlusOneExit) with
    | .br4 => (do
      let i9 ← Zig.optPayload i2
      let i10 ← Zig.add false i9 (1 : BitVec 64)
      pure (.ret i10))
    | e => pure e) : Zig.M firstIndexPlusOneLocals firstIndexPlusOneExit).run' (default : firstIndexPlusOneLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

end Options