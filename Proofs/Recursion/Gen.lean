import ZigLean


namespace Recursion

structure factLocals where
  deriving Inhabited

inductive factExit where
  | ret (v : BitVec 32)
  | br1

mutual

def fact (p0 : BitVec 32) : Zig.Result (BitVec 32) := do
  let e ← ((do
    match ← ((do
      let i2 ← pure (p0 == (0 : BitVec 32))
      if i2 then (do
        pure (.ret (1 : BitVec 32)))
      else (do
        pure .br1)) : Zig.M factLocals factExit) with
    | .br1 => (do
      let i6 ← Zig.sub false p0 (1 : BitVec 32)
      let i7 ← Zig.call (fact i6)
      let i8 ← Zig.mul false p0 i7
      pure (.ret i8))
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
  | br2
  | br8

mutual

def gcd (p0 : BitVec 32) (p1 : BitVec 32) : Zig.Result (BitVec 32) := do
  let e ← ((do
    match ← ((do
      let i3 ← pure (p1 == (0 : BitVec 32))
      if i3 then (do
        pure (.ret p0))
      else (do
        pure .br2)) : Zig.M gcdLocals gcdExit) with
    | .br2 => (do
      let i7 ← pure (p1 != (0 : BitVec 32))
      match ← ((do
        if i7 then (do
          pure .br8)
        else (do
          throw .divByZero)) : Zig.M gcdLocals gcdExit) with
      | .br8 => (do
        let i13 ← Zig.rem false p0 p1
        let i14 ← Zig.call (gcd p1 i13)
        pure (.ret i14))
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
  | br1

structure isEvenLocals where
  deriving Inhabited

inductive isEvenExit where
  | ret (v : Bool)
  | br1

mutual

def isOdd (p0 : BitVec 32) : Zig.Result (Bool) := do
  let e ← ((do
    match ← ((do
      let i2 ← pure (p0 == (0 : BitVec 32))
      if i2 then (do
        pure (.ret false))
      else (do
        pure .br1)) : Zig.M isOddLocals isOddExit) with
    | .br1 => (do
      let i6 ← Zig.sub false p0 (1 : BitVec 32)
      let i7 ← Zig.call (isEven i6)
      pure (.ret i7))
    | e => pure e) : Zig.M isOddLocals isOddExit).run' (default : isOddLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic
partial_fixpoint

def isEven (p0 : BitVec 32) : Zig.Result (Bool) := do
  let e ← ((do
    match ← ((do
      let i2 ← pure (p0 == (0 : BitVec 32))
      if i2 then (do
        pure (.ret true))
      else (do
        pure .br1)) : Zig.M isEvenLocals isEvenExit) with
    | .br1 => (do
      let i6 ← Zig.sub false p0 (1 : BitVec 32)
      let i7 ← Zig.call (isOdd i6)
      pure (.ret i7))
    | e => pure e) : Zig.M isEvenLocals isEvenExit).run' (default : isEvenLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic
partial_fixpoint

end

end Recursion