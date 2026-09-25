import ZigLean


namespace Recursion

structure factLocals where
  deriving Inhabited

inductive factExit where
  | ret (v : BitVec 32)
  | br2

mutual

def fact (p0 : BitVec 32) : Zig.Result (BitVec 32) := do
  let e ← ((do
    match ← ((do
      let i3 ← pure (p0 == (0 : BitVec 32))
      if i3 then (do
        pure (.ret (1 : BitVec 32)))
      else (do
        pure .br2)) : Zig.M factLocals factExit) with
    | .br2 => (do
      let i9 ← Zig.sub false p0 (1 : BitVec 32)
      let i11 ← Zig.call (fact i9)
      let i13 ← Zig.mul false p0 i11
      pure (.ret i13))
    | e => pure e) : Zig.M factLocals factExit).run' (default : factLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic
partial_fixpoint

end

structure gcdLocals where
  deriving Inhabited

inductive gcdExit where
  | ret (v : BitVec 32)
  | br3
  | br13

mutual

def gcd (p0 : BitVec 32) (p1 : BitVec 32) : Zig.Result (BitVec 32) := do
  let e ← ((do
    match ← ((do
      let i4 ← pure (p1 == (0 : BitVec 32))
      if i4 then (do
        pure (.ret p0))
      else (do
        pure .br3)) : Zig.M gcdLocals gcdExit) with
    | .br3 => (do
      let i10 ← pure (p1 != (0 : BitVec 32))
      match ← ((do
        if i10 then (do
          pure .br13)
        else (do
          throw .divByZero)) : Zig.M gcdLocals gcdExit) with
      | .br13 => (do
        let i16 ← Zig.rem false p0 p1
        let i18 ← Zig.call (gcd p1 i16)
        pure (.ret i18))
      | e => pure e)
    | e => pure e) : Zig.M gcdLocals gcdExit).run' (default : gcdLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic
partial_fixpoint

end

structure isOddLocals where
  deriving Inhabited

inductive isOddExit where
  | ret (v : Bool)
  | br2

structure isEvenLocals where
  deriving Inhabited

inductive isEvenExit where
  | ret (v : Bool)
  | br2

mutual

def isOdd (p0 : BitVec 32) : Zig.Result (Bool) := do
  let e ← ((do
    match ← ((do
      let i3 ← pure (p0 == (0 : BitVec 32))
      if i3 then (do
        pure (.ret false))
      else (do
        pure .br2)) : Zig.M isOddLocals isOddExit) with
    | .br2 => (do
      let i9 ← Zig.sub false p0 (1 : BitVec 32)
      let i11 ← Zig.call (isEven i9)
      pure (.ret i11))
    | e => pure e) : Zig.M isOddLocals isOddExit).run' (default : isOddLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic
partial_fixpoint

def isEven (p0 : BitVec 32) : Zig.Result (Bool) := do
  let e ← ((do
    match ← ((do
      let i3 ← pure (p0 == (0 : BitVec 32))
      if i3 then (do
        pure (.ret true))
      else (do
        pure .br2)) : Zig.M isEvenLocals isEvenExit) with
    | .br2 => (do
      let i9 ← Zig.sub false p0 (1 : BitVec 32)
      let i11 ← Zig.call (isOdd i9)
      pure (.ret i11))
    | e => pure e) : Zig.M isEvenLocals isEvenExit).run' (default : isEvenLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic
partial_fixpoint

end

end Recursion