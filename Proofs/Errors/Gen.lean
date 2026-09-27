import ZigLean


namespace Errors

structure parseDigitLocals where
  deriving Inhabited

inductive parseDigitExit where
  | ret (v : Except Zig.ErrName (BitVec 8))
  | br3 (v : Bool)
  | br1

def parseDigit (p0 : BitVec 8) : Zig.Result (Except Zig.ErrName (BitVec 8)) := do
  let e ← ((do
    match ← ((do
      let i2 ← pure (Zig.lt false p0 (48 : BitVec 8))
      match ← ((do
        if i2 then (do
          pure (.br3 true))
        else (do
          let i6 ← pure (Zig.gt false p0 (57 : BitVec 8))
          pure (.br3 i6))) : Zig.M parseDigitLocals parseDigitExit) with
      | .br3 v3 => (do
        if v3 then (do
          pure (.ret (.error "NotDigit" : Except Zig.ErrName (BitVec 8))))
        else (do
          pure .br1))
      | e => pure e) : Zig.M parseDigitLocals parseDigitExit) with
    | .br1 => (do
      let i11 ← Zig.sub false p0 (48 : BitVec 8)
      let i12 ← pure ((.ok i11) : Except Zig.ErrName (BitVec 8))
      pure (.ret i12))
    | e => pure e) : Zig.M parseDigitLocals parseDigitExit).run' (default : parseDigitLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure digitOrZeroLocals where
  deriving Inhabited

inductive digitOrZeroExit where
  | ret (v : BitVec 8)
  | br1 (v : BitVec 8)

def digitOrZero (p0 : BitVec 8) : Zig.Result (BitVec 8) := do
  let e ← ((do
    match ← ((do
      let i2 ← Zig.call (parseDigit p0)
      let i3 ← pure (Zig.isNonErr i2)
      if i3 then (do
        let i5 ← Zig.call (Zig.unwrapPayload i2)
        pure (.br1 i5))
      else (do
        let _i7 ← Zig.call (Zig.unwrapErr i2)
        pure (.br1 (0 : BitVec 8)))) : Zig.M digitOrZeroLocals digitOrZeroExit) with
    | .br1 v1 => (do
      pure (.ret v1))
    | e => pure e) : Zig.M digitOrZeroLocals digitOrZeroExit).run' (default : digitOrZeroLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure sumDigitsLocals where
  total : BitVec 32
  local3 : BitVec 64
  deriving Inhabited

inductive sumDigitsExit where
  | ret (v : Except Zig.ErrName (BitVec 32))
  | br9
  | br6
  | rep7

def sumDigits.again7 : sumDigitsExit → Bool
  | .rep7 => true
  | _ => false

def sumDigits.loop7 (p0 : Array (BitVec 8)) (i5 : BitVec 64) : Zig.M sumDigitsLocals sumDigitsExit := do
  let i8 ← pure ((← get).local3)
  match ← ((do
    let i10 ← pure (i8)
    let i11 ← pure (i5)
    let i12 ← pure (Zig.lt false i10 i11)
    if i12 then (do
      let i14 ← Zig.call (Zig.index p0 i8)
      let i15 ← pure ((← get).total)
      let i16 ← Zig.call (parseDigit i14)
      match i16 with
      | .error _ => (do
        let i18 ← Zig.call (Zig.unwrapErr i16)
        let i19 ← pure ((.error i18) : Except Zig.ErrName (BitVec 32))
        pure (.ret i19))
      | .ok v17 => (do
        let i21 ← Zig.intCast false false 32 v17
        let i22 ← Zig.add false i15 i21
        modify (fun s => { s with total := i22 })
        pure .br9))
    else (do
      pure .br6)) : Zig.M sumDigitsLocals sumDigitsExit) with
  | .br9 => (do
    let i26 ← Zig.add false i8 (1 : BitVec 64)
    modify (fun s => { s with local3 := i26 })
    pure .rep7)
  | e => pure e

def sumDigits (p0 : Array (BitVec 8)) : Zig.Result (Except Zig.ErrName (BitVec 32)) := do
  let e ← ((do
    modify (fun s => { s with total := (0 : BitVec 32) })
    modify (fun s => { s with local3 := (0 : BitVec 64) })
    let i5 ← pure (Zig.len p0)
    match ← ((do
      Zig.loop (sumDigits.loop7 p0 i5) sumDigits.again7) : Zig.M sumDigitsLocals sumDigitsExit) with
    | .br6 => (do
      let i29 ← pure ((← get).total)
      let i30 ← pure ((.ok i29) : Except Zig.ErrName (BitVec 32))
      pure (.ret i30))
    | e => pure e) : Zig.M sumDigitsLocals sumDigitsExit).run' (default : sumDigitsLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

end Errors