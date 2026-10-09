import ZigLean


namespace DivCeil

structure divCeilI13Locals where
  deriving Inhabited

inductive divCeilI13Exit where
  | ret (v : BitVec 13)
  | br5
  | br11

def divCeilI13 (p0 : BitVec 13) (p1 : BitVec 13) : Zig.Result (BitVec 13) := do
  let e ← ((do
    let i2 ← pure (p0 != (-(4096 : BitVec 13)))
    let i3 ← pure (p1 != (-(1 : BitVec 13)))
    let i4 ← pure (i2 || i3)
    match ← ((do
      if i4 then (do
        pure .br5)
      else (do
        throw .overflow)) : Zig.M divCeilI13Locals divCeilI13Exit) with
    | .br5 => (do
      let i10 ← pure (p1 != (0 : BitVec 13))
      match ← ((do
        if i10 then (do
          pure .br11)
        else (do
          throw .divByZero)) : Zig.M divCeilI13Locals divCeilI13Exit) with
      | .br11 => (do
        let i16 ← Zig.divCeil true p0 p1
        pure (.ret i16))
      | e => pure e)
    | e => pure e) : Zig.M divCeilI13Locals divCeilI13Exit).run' (default : divCeilI13Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure divCeilI32Locals where
  deriving Inhabited

inductive divCeilI32Exit where
  | ret (v : BitVec 32)
  | br5
  | br11

def divCeilI32 (p0 : BitVec 32) (p1 : BitVec 32) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i2 ← pure (p0 != (-(2147483648 : BitVec 32)))
    let i3 ← pure (p1 != (-(1 : BitVec 32)))
    let i4 ← pure (i2 || i3)
    match ← ((do
      if i4 then (do
        pure .br5)
      else (do
        throw .overflow)) : Zig.M divCeilI32Locals divCeilI32Exit) with
    | .br5 => (do
      let i10 ← pure (p1 != (0 : BitVec 32))
      match ← ((do
        if i10 then (do
          pure .br11)
        else (do
          throw .divByZero)) : Zig.M divCeilI32Locals divCeilI32Exit) with
      | .br11 => (do
        let i16 ← Zig.divCeil true p0 p1
        pure (.ret i16))
      | e => pure e)
    | e => pure e) : Zig.M divCeilI32Locals divCeilI32Exit).run' (default : divCeilI32Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure divCeilI64Locals where
  deriving Inhabited

inductive divCeilI64Exit where
  | ret (v : BitVec 64)
  | br5
  | br11

def divCeilI64 (p0 : BitVec 64) (p1 : BitVec 64) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i2 ← pure (p0 != (-(9223372036854775808 : BitVec 64)))
    let i3 ← pure (p1 != (-(1 : BitVec 64)))
    let i4 ← pure (i2 || i3)
    match ← ((do
      if i4 then (do
        pure .br5)
      else (do
        throw .overflow)) : Zig.M divCeilI64Locals divCeilI64Exit) with
    | .br5 => (do
      let i10 ← pure (p1 != (0 : BitVec 64))
      match ← ((do
        if i10 then (do
          pure .br11)
        else (do
          throw .divByZero)) : Zig.M divCeilI64Locals divCeilI64Exit) with
      | .br11 => (do
        let i16 ← Zig.divCeil true p0 p1
        pure (.ret i16))
      | e => pure e)
    | e => pure e) : Zig.M divCeilI64Locals divCeilI64Exit).run' (default : divCeilI64Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure divCeilI8Locals where
  deriving Inhabited

inductive divCeilI8Exit where
  | ret (v : BitVec 8)
  | br5
  | br11

def divCeilI8 (p0 : BitVec 8) (p1 : BitVec 8) : Zig.Result (BitVec 8) := do
  let e ← ((do
    let i2 ← pure (p0 != (-(128 : BitVec 8)))
    let i3 ← pure (p1 != (-(1 : BitVec 8)))
    let i4 ← pure (i2 || i3)
    match ← ((do
      if i4 then (do
        pure .br5)
      else (do
        throw .overflow)) : Zig.M divCeilI8Locals divCeilI8Exit) with
    | .br5 => (do
      let i10 ← pure (p1 != (0 : BitVec 8))
      match ← ((do
        if i10 then (do
          pure .br11)
        else (do
          throw .divByZero)) : Zig.M divCeilI8Locals divCeilI8Exit) with
      | .br11 => (do
        let i16 ← Zig.divCeil true p0 p1
        pure (.ret i16))
      | e => pure e)
    | e => pure e) : Zig.M divCeilI8Locals divCeilI8Exit).run' (default : divCeilI8Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure divCeilU32Locals where
  deriving Inhabited

inductive divCeilU32Exit where
  | ret (v : BitVec 32)
  | br3

def divCeilU32 (p0 : BitVec 32) (p1 : BitVec 32) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i2 ← pure (p1 != (0 : BitVec 32))
    match ← ((do
      if i2 then (do
        pure .br3)
      else (do
        throw .divByZero)) : Zig.M divCeilU32Locals divCeilU32Exit) with
    | .br3 => (do
      let i8 ← Zig.divCeil false p0 p1
      pure (.ret i8))
    | e => pure e) : Zig.M divCeilU32Locals divCeilU32Exit).run' (default : divCeilU32Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure divCeilU64Locals where
  deriving Inhabited

inductive divCeilU64Exit where
  | ret (v : BitVec 64)
  | br3

def divCeilU64 (p0 : BitVec 64) (p1 : BitVec 64) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i2 ← pure (p1 != (0 : BitVec 64))
    match ← ((do
      if i2 then (do
        pure .br3)
      else (do
        throw .divByZero)) : Zig.M divCeilU64Locals divCeilU64Exit) with
    | .br3 => (do
      let i8 ← Zig.divCeil false p0 p1
      pure (.ret i8))
    | e => pure e) : Zig.M divCeilU64Locals divCeilU64Exit).run' (default : divCeilU64Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure divCeilU8Locals where
  deriving Inhabited

inductive divCeilU8Exit where
  | ret (v : BitVec 8)
  | br3

def divCeilU8 (p0 : BitVec 8) (p1 : BitVec 8) : Zig.Result (BitVec 8) := do
  let e ← ((do
    let i2 ← pure (p1 != (0 : BitVec 8))
    match ← ((do
      if i2 then (do
        pure .br3)
      else (do
        throw .divByZero)) : Zig.M divCeilU8Locals divCeilU8Exit) with
    | .br3 => (do
      let i8 ← Zig.divCeil false p0 p1
      pure (.ret i8))
    | e => pure e) : Zig.M divCeilU8Locals divCeilU8Exit).run' (default : divCeilU8Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

end DivCeil