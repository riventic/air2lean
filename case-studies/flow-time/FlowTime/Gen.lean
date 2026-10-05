import ZigLean


namespace FlowTime

structure timestamp32Locals where
  deriving Inhabited

inductive timestamp32Exit where
  | ret (v : Except Zig.ErrName (BitVec 32))
  | br7 (v : Bool)
  | br2 (v : Except Zig.ErrName (BitVec 32))
  | br4

def timestamp32 (p0 : BitVec 32) (p1 : BitVec 32) : Zig.Result (Except Zig.ErrName (BitVec 32)) := do
  let e ← ((do
    match ← ((do
      let i3 ← pure (Zig.addWithOverflow false p0 p1)
      match ← ((do
        let i5 ← pure ((i3).2)
        let i6 ← pure (i5 != (0 : BitVec 1))
        match ← ((do
          if i6 then (do
            pure (.br7 true))
          else (do
            let i10 ← pure ((i3).1)
            let i11 ← pure (i10 == (4294967295 : BitVec 32))
            pure (.br7 i11))) : Zig.M timestamp32Locals timestamp32Exit) with
        | .br7 v7 => (do
          if v7 then (do
            pure (.br2 (.error "TimeOverflow" : Except Zig.ErrName (BitVec 32))))
          else (do
            pure .br4))
        | e => pure e) : Zig.M timestamp32Locals timestamp32Exit) with
      | .br4 => (do
        let i16 ← pure ((i3).1)
        let i17 ← pure ((.ok i16) : Except Zig.ErrName (BitVec 32))
        pure (.br2 i17))
      | e => pure e) : Zig.M timestamp32Locals timestamp32Exit) with
    | .br2 v2 => (do
      pure (.ret v2))
    | e => pure e) : Zig.M timestamp32Locals timestamp32Exit).run' (default : timestamp32Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure timestamp64Locals where
  deriving Inhabited

inductive timestamp64Exit where
  | ret (v : Except Zig.ErrName (BitVec 64))
  | br7 (v : Bool)
  | br2 (v : Except Zig.ErrName (BitVec 64))
  | br4

def timestamp64 (p0 : BitVec 64) (p1 : BitVec 64) : Zig.Result (Except Zig.ErrName (BitVec 64)) := do
  let e ← ((do
    match ← ((do
      let i3 ← pure (Zig.addWithOverflow false p0 p1)
      match ← ((do
        let i5 ← pure ((i3).2)
        let i6 ← pure (i5 != (0 : BitVec 1))
        match ← ((do
          if i6 then (do
            pure (.br7 true))
          else (do
            let i10 ← pure ((i3).1)
            let i11 ← pure (i10 == (18446744073709551615 : BitVec 64))
            pure (.br7 i11))) : Zig.M timestamp64Locals timestamp64Exit) with
        | .br7 v7 => (do
          if v7 then (do
            pure (.br2 (.error "TimeOverflow" : Except Zig.ErrName (BitVec 64))))
          else (do
            pure .br4))
        | e => pure e) : Zig.M timestamp64Locals timestamp64Exit) with
      | .br4 => (do
        let i16 ← pure ((i3).1)
        let i17 ← pure ((.ok i16) : Except Zig.ErrName (BitVec 64))
        pure (.br2 i17))
      | e => pure e) : Zig.M timestamp64Locals timestamp64Exit) with
    | .br2 v2 => (do
      pure (.ret v2))
    | e => pure e) : Zig.M timestamp64Locals timestamp64Exit).run' (default : timestamp64Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

end FlowTime