/-!
# Zig runtime semantics

Generated code imports this file. It defines the effect monad and one Lean function per
AIR operation in the air2lean subset.

* Integers are `BitVec n`. Signedness is not in the type: each operation takes `s : Bool`
  (`true` = signed), which the translator reads from the AIR type.
* Every check that Zig does in `Debug` / `ReleaseSafe` becomes `throw`. In `ReleaseFast`
  the same cases are illegal behaviour, so a proof of "never throws" covers both modes.
-/

namespace Zig

inductive Error where
  | overflow
  | outOfBounds
  | divByZero
  | unreachable
  | panic
  deriving Repr, DecidableEq, Inhabited

/-- `none` = the computation does not terminate. `some (.error e)` = safety panic. -/
abbrev Result (α : Type) := ExceptT Error Option α

/-- Function body monad. `σ` holds the function's stack locals (`var`). -/
abbrev M (σ α : Type) := StateT σ Result α

abbrev usize := BitVec 64
abbrev isize := BitVec 64

/-! ## Arithmetic -/

section Arith
variable {n : Nat}

@[inline] def add (s : Bool) (a b : BitVec n) : Result (BitVec n) :=
  if (if s then a.saddOverflow b else a.uaddOverflow b) then throw .overflow else pure (a + b)

@[inline] def sub (s : Bool) (a b : BitVec n) : Result (BitVec n) :=
  if (if s then a.ssubOverflow b else a.usubOverflow b) then throw .overflow else pure (a - b)

@[inline] def mul (s : Bool) (a b : BitVec n) : Result (BitVec n) :=
  if (if s then a.smulOverflow b else a.umulOverflow b) then throw .overflow else pure (a * b)

@[inline] def neg (s : Bool) (a : BitVec n) : Result (BitVec n) := sub s 0 a

/-- `@divTrunc`, and `/` on unsigned integers. -/
@[inline] def divTrunc (s : Bool) (a b : BitVec n) : Result (BitVec n) :=
  if b = 0 then throw .divByZero
  else if s then (if a.sdivOverflow b then throw .overflow else pure (a.sdiv b))
  else pure (a.udiv b)

/-- `@divFloor`. -/
@[inline] def divFloor (s : Bool) (a b : BitVec n) : Result (BitVec n) :=
  if b = 0 then throw .divByZero
  else if s then (if a.sdivOverflow b then throw .overflow
                  else pure (.ofInt n (Int.fdiv a.toInt b.toInt)))
  else pure (a.udiv b)

/-- `@divExact`: the remainder must be zero. -/
@[inline] def divExact (s : Bool) (a b : BitVec n) : Result (BitVec n) := do
  let q ← divTrunc s a b
  if q * b = a then pure q else throw .panic

/-- `@rem`, and `%` on unsigned integers. The result has the sign of `a`. -/
@[inline] def rem (s : Bool) (a b : BitVec n) : Result (BitVec n) :=
  if b = 0 then throw .divByZero
  else if s then (if b.toInt < 0 then throw .panic else pure (a.srem b))
  else pure (a.umod b)

/-- `@mod`. The result has the sign of `b`. -/
@[inline] def mod (s : Bool) (a b : BitVec n) : Result (BitVec n) :=
  if b = 0 then throw .divByZero
  else if s then (if b.toInt < 0 then throw .panic else pure (a.smod b))
  else pure (a.umod b)

@[inline] def addWrap (a b : BitVec n) : BitVec n := a + b
@[inline] def subWrap (a b : BitVec n) : BitVec n := a - b
@[inline] def mulWrap (a b : BitVec n) : BitVec n := a * b

/-- Clamp a mathematical integer into the range of an `n`-bit type. -/
def clamp (s : Bool) (n : Nat) (v : Int) : BitVec n :=
  let lo : Int := if s then -(2 ^ (n - 1)) else 0
  let hi : Int := if s then 2 ^ (n - 1) - 1 else 2 ^ n - 1
  .ofInt n (max lo (min hi v))

@[inline] def val (s : Bool) (a : BitVec n) : Int := if s then a.toInt else a.toNat

@[inline] def addSat (s : Bool) (a b : BitVec n) : BitVec n := clamp s n (val s a + val s b)
@[inline] def subSat (s : Bool) (a b : BitVec n) : BitVec n := clamp s n (val s a - val s b)
@[inline] def mulSat (s : Bool) (a b : BitVec n) : BitVec n := clamp s n (val s a * val s b)

/-- `@addWithOverflow` and friends: `(wrapped result, overflow bit)`. -/
@[inline] def addWithOverflow (s : Bool) (a b : BitVec n) : BitVec n × BitVec 1 :=
  (a + b, if (if s then a.saddOverflow b else a.uaddOverflow b) then 1 else 0)
@[inline] def subWithOverflow (s : Bool) (a b : BitVec n) : BitVec n × BitVec 1 :=
  (a - b, if (if s then a.ssubOverflow b else a.usubOverflow b) then 1 else 0)
@[inline] def mulWithOverflow (s : Bool) (a b : BitVec n) : BitVec n × BitVec 1 :=
  (a * b, if (if s then a.smulOverflow b else a.umulOverflow b) then 1 else 0)

@[inline] def min (s : Bool) (a b : BitVec n) : BitVec n :=
  if (if s then a.sle b else a.ule b) then a else b
@[inline] def max (s : Bool) (a b : BitVec n) : BitVec n :=
  if (if s then a.sle b else a.ule b) then b else a

/-! ## Bits -/

@[inline] def shl {m : Nat} (a : BitVec n) (b : BitVec m) : BitVec n := a <<< b.toNat

/-- `<<|` saturates when set bits would be shifted out. -/
@[inline] def shlSat {m : Nat} (s : Bool) (a : BitVec n) (b : BitVec m) : BitVec n :=
  clamp s n (val s a * 2 ^ b.toNat)

@[inline] def shr {m : Nat} (s : Bool) (a : BitVec n) (b : BitVec m) : BitVec n :=
  if s then a.sshiftRight b.toNat else a >>> b.toNat

/-- `@shlExact`: no set bit may be shifted out. -/
@[inline] def shlExact {m : Nat} (s : Bool) (a : BitVec n) (b : BitVec m) : Result (BitVec n) :=
  let r := a <<< b.toNat
  if shr s r b = a then pure r else throw .overflow

/-- `@shrExact`: no set bit may be shifted out. -/
@[inline] def shrExact {m : Nat} (s : Bool) (a : BitVec n) (b : BitVec m) : Result (BitVec n) :=
  let r := shr s a b
  if r <<< b.toNat = a then pure r else throw .overflow

/-! ## Comparisons -/

@[inline] def lt (s : Bool) (a b : BitVec n) : Bool := if s then a.slt b else a.ult b
@[inline] def le (s : Bool) (a b : BitVec n) : Bool := if s then a.sle b else a.ule b
@[inline] def gt (s : Bool) (a b : BitVec n) : Bool := lt s b a
@[inline] def ge (s : Bool) (a b : BitVec n) : Bool := le s b a

/-! ## Casts -/

/-- `@intCast`: the value must fit in the target type. -/
@[inline] def intCast (s₁ s₂ : Bool) (m : Nat) (a : BitVec n) : Result (BitVec m) :=
  let v := val s₁ a
  let lo : Int := if s₂ then -(2 ^ (m - 1)) else 0
  let hi : Int := if s₂ then 2 ^ (m - 1) - 1 else 2 ^ m - 1
  if lo ≤ v ∧ v ≤ hi then pure (.ofInt m v) else throw .overflow

/-- `@truncate`: keep the low `m` bits. -/
@[inline] def trunc (m : Nat) (a : BitVec n) : BitVec m := a.setWidth m

end Arith

/-! ## Slices -/

/-- Read-only slice element. Out of range ⇒ `outOfBounds`. -/
@[inline] def index {α : Type} (a : Array α) (i : usize) : Result α :=
  if h : i.toNat < a.size then pure a[i.toNat] else throw .outOfBounds

@[inline] def len {α : Type} (a : Array α) : usize := BitVec.ofNat 64 a.size

/-! ## Control flow -/

/-- An AIR `loop`: run `body` until it returns an exit that is not `repeat` for this loop. -/
def loop {σ ε : Type} (body : M σ ε) (again : ε → Bool) : M σ ε := do
  let e ← body
  if again e then loop body again else pure e
partial_fixpoint

/-- Lift a call to another translated function into the caller's monad. -/
@[inline] def call {σ α : Type} (r : Result α) : M σ α := StateT.lift r

end Zig
