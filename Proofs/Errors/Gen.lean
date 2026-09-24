import ZigLean


namespace Errors

structure parseDigitLocals where
  deriving Inhabited

inductive parseDigitExit where
  | ret (v : Except Zig.ErrName (BitVec 8))
  | br4 (v : Bool)
  | br2

def parseDigit (p0 : BitVec 8) : Zig.Result (Except Zig.ErrName (BitVec 8)) := do
  let e ← ((do
    match ← ((do
      let i3 ← pure (Zig.lt false p0 (48 : BitVec 8))
      match ← ((do
        if i3 then (do
          pure (.br4 true))
        else (do
          let i6 ← pure (Zig.gt false p0 (57 : BitVec 8))
          pure (.br4 i6))) : Zig.M parseDigitLocals parseDigitExit) with
      | .br4 v4 => (do
        if v4 then (do
          pure (.ret (.error "NotDigit" : Except Zig.ErrName (BitVec 8))))
        else (do
          pure .br2))
      | e => pure e) : Zig.M parseDigitLocals parseDigitExit) with
    | .br2 => (do
      let i14 ← Zig.sub false p0 (48 : BitVec 8)
      let i16 ← pure ((.ok i14) : Except Zig.ErrName (BitVec 8))
      pure (.ret i16))
    | e => pure e) : Zig.M parseDigitLocals parseDigitExit).run' (default : parseDigitLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure digitOrZeroLocals where
  deriving Inhabited

inductive digitOrZeroExit where
  | ret (v : BitVec 8)
  | br2 (v : BitVec 8)

def digitOrZero (p0 : BitVec 8) : Zig.Result (BitVec 8) := do
  let e ← ((do
    match ← ((do
      let i4 ← Zig.call (parseDigit p0)
      let i5 ← pure (Zig.isNonErr i4)
      if i5 then (do
        let i6 ← Zig.call (Zig.unwrapPayload i4)
        pure (.br2 i6))
      else (do
        let _i8 ← Zig.call (Zig.unwrapErr i4)
        pure (.br2 (0 : BitVec 8)))) : Zig.M digitOrZeroLocals digitOrZeroExit) with
    | .br2 v2 => (do
      pure (.ret v2))
    | e => pure e) : Zig.M digitOrZeroLocals digitOrZeroExit).run' (default : digitOrZeroLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure sumDigitsLocals where
  total : BitVec 32
  local5 : BitVec 64
  deriving Inhabited

inductive sumDigitsExit where
  | ret (v : Except Zig.ErrName (BitVec 32))
  | br12
  | br9
  | rep10

def sumDigits.again10 : sumDigitsExit → Bool
  | .rep10 => true
  | _ => false

def sumDigits.loop10 (p0 : Array (BitVec 8)) (i8 : BitVec 64) : Zig.M sumDigitsLocals sumDigitsExit := do
  let i11 ← pure ((← get).local5)
  match ← ((do
    let i13 ← pure (i11)
    let i14 ← pure (i8)
    let i15 ← pure (Zig.lt false i13 i14)
    if i15 then (do
      let i16 ← Zig.call (Zig.index p0 i11)
      let i19 ← pure ((← get).total)
      let i21 ← Zig.call (parseDigit i16)
      match i21 with
      | .error _ => (do
        let i22 ← Zig.call (Zig.unwrapErr i21)
        let i24 ← pure ((.error i22) : Except Zig.ErrName (BitVec 32))
        pure (.ret i24))
      | .ok v26 => (do
        let i27 ← Zig.intCast false false 32 v26
        let i29 ← Zig.add false i19 i27
        modify (fun s => { s with total := i29 })
        pure .br12))
    else (do
      pure .br9)) : Zig.M sumDigitsLocals sumDigitsExit) with
  | .br12 => (do
    let i36 ← Zig.add false i11 (1 : BitVec 64)
    modify (fun s => { s with local5 := i36 })
    pure .rep10)
  | e => pure e

def sumDigits (p0 : Array (BitVec 8)) : Zig.Result (Except Zig.ErrName (BitVec 32)) := do
  let e ← ((do
    modify (fun s => { s with total := (0 : BitVec 32) })
    modify (fun s => { s with local5 := (0 : BitVec 64) })
    let i8 ← pure (Zig.len p0)
    match ← ((do
      Zig.loop (sumDigits.loop10 p0 i8) sumDigits.again10) : Zig.M sumDigitsLocals sumDigitsExit) with
    | .br9 => (do
      let i40 ← pure ((← get).total)
      let i42 ← pure ((.ok i40) : Except Zig.ErrName (BitVec 32))
      pure (.ret i42))
    | e => pure e) : Zig.M sumDigitsLocals sumDigitsExit).run' (default : sumDigitsLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

end Errors