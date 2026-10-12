import ZigLean.Sep.Full.Try
import ZigLean.Sep.Full.Auto

/-!
# Error unions and optionals through pointers (`ZigLean/Sep/Full/Try.lean`), library-only

Programs in the shape the translator emits for pointer-form `try`, `catch`, `if (x) |*p|` and
result locations of `E!T` and `?T`: `fsym` walks them with the `@[fsym]` rules of `Full/Try`,
nothing given.
-/

namespace OneLogic.Try

open Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto

/-- `error{Bad, Other}`, a literal as in generated code. -/
local notation "dom" => (⟨#["Bad", "Other"], by decide, by decide⟩ : ErrorDomain)

/-- `(p.* catch 0)` through the payload pointer: `try` in pointer form. -/
def readOr (p : Ptr) : MemM (BitVec 8) := do
  Zig.loadDiscardBytes 4 2 p
  match ← Zig.finiteTryPayloadPtr dom (BitVec 8) 2 p with
  | .error _ => pure 0
  | .ok q => Zig.load (BitVec 8) 1 q

theorem readOr_ok (p : Ptr) (x : BitVec 8) :
    FTotalTriple (up (pts p 2 (Except.ok x : Except ErrName (BitVec 8)))) (readOr p)
      (fun r => ⟪r = x⟫ ⋆ up (pts p 2 (Except.ok x : Except ErrName (BitVec 8)))) := by
  unfold readOr
  fsym

theorem readOr_err (p : Ptr) :
    FTotalTriple (up (pts p 2 (Except.error "Bad" : Except ErrName (BitVec 8)))) (readOr p)
      (fun r => ⟪r = 0⟫ ⋆ up (pts p 2 (Except.error "Bad" : Except ErrName (BitVec 8)))) := by
  unfold readOr
  fsym

/-- The error of `p.*` (`catch |e|`). -/
def errOf (p : Ptr) : MemM ErrName := Zig.finiteErrCodeAt dom (BitVec 8) 2 p

theorem errOf_spec (p : Ptr) :
    FTotalTriple (up (pts p 2 (Except.error "Other" : Except ErrName (BitVec 8)))) (errOf p)
      (fun r => ⟪r = "Other"⟫ ⋆ up (pts p 2 (Except.error "Other" : Except ErrName (BitVec 8)))) := by
  unfold errOf
  fsym

/-- `if (p.*) |*v| v.* +%= 1 else |_| {}`: the whole union loaded with its error set, the
payload through the payload pointer. -/
def bump (p : Ptr) : MemM Unit := do
  let u ← (letI : Enc (Except ErrName (BitVec 8)) := errorUnionEnc dom inferInstance;
    Zig.load (Except ErrName (BitVec 8)) 2 p)
  if Zig.isNonErr u then
    let q ← Zig.ptrProject p (errPayloadPtr (BitVec 8))
    let v ← Zig.load (BitVec 8) 1 q
    Zig.store 1 q (Zig.addWrap v 1)
  else pure ()

theorem bump_spec (p : Ptr) (x : BitVec 8) :
    FTotalTriple (up (pts p 2 (Except.ok x : Except ErrName (BitVec 8)))) (bump p)
      (fun _ => up (pts p 2 (Except.ok (x + 1) : Except ErrName (BitVec 8)))) := by
  unfold bump
  fsym

/-- A result location `p.* = y` of `E!u8`: the error code set to 0, then the payload. -/
def setOk (p : Ptr) (y : BitVec 8) : MemM Unit := do
  let q ← Zig.errSetOk (BitVec 8) 2 p
  Zig.store 1 q y

theorem setOk_spec (p : Ptr) (u : Except ErrName (BitVec 8)) (y : BitVec 8) :
    FTotalTriple (up (pts p 2 u)) (setOk p y)
      (fun _ => up (pts p 2 (Except.ok y : Except ErrName (BitVec 8)))) := by
  unfold setOk
  fsym

/-- A result location `p.* = y` of `?u16`: the flag byte set, then the payload. -/
def setSome (p : Ptr) (y : BitVec 16) : MemM Unit := do
  let q ← Zig.optSetSome (BitVec 16) p
  Zig.store 2 q y

theorem setSome_spec (p : Ptr) (o : Option (BitVec 16)) (y : BitVec 16) :
    FTotalTriple (up (pts p 2 o)) (setSome p y) (fun _ => up (pts p 2 (some y))) := by
  unfold setSome
  fsym

/-- `if (p.*) |*v| v.* else 0` for `?u16`. -/
def getOr (p : Ptr) : MemM (BitVec 16) := do
  if ← Zig.optIsSome (BitVec 16) p then Zig.load (BitVec 16) 2 p else pure 0

theorem getOr_some (p : Ptr) (x : BitVec 16) :
    FTotalTriple (up (pts p 2 (some x))) (getOr p) (fun r => ⟪r = x⟫ ⋆ up (pts p 2 (some x))) := by
  unfold getOr
  fsym

theorem getOr_none (p : Ptr) :
    FTotalTriple (up (pts p 2 (none : Option (BitVec 16)))) (getOr p)
      (fun r => ⟪r = 0⟫ ⋆ up (pts p 2 (none : Option (BitVec 16)))) := by
  unfold getOr
  fsym

/-- `if (p.*) |*v| v.* +%= 1` for `?u16`. -/
def incSome (p : Ptr) : MemM Unit := do
  if ← Zig.optIsSome (BitVec 16) p then
    let v ← Zig.load (BitVec 16) 2 p
    Zig.store 2 p (Zig.addWrap v 1)
  else pure ()

theorem incSome_spec (p : Ptr) (x : BitVec 16) :
    FTotalTriple (up (pts p 2 (some x))) (incSome p) (fun _ => up (pts p 2 (some (x + 1)))) := by
  unfold incSome
  fsym

/-- `p.* != null` for `?error{Bad, Other}`. -/
def hasErr (p : Ptr) : MemM Bool := Zig.optionalErrorIsSome dom 2 p

theorem hasErr_spec (p : Ptr) (o : Option ErrName) :
    FTotalTriple (up (@pts (Option ErrName) (optionalErrorEnc dom) p 2 o)) (hasErr p)
      (fun r => ⟪r = o.isSome⟫ ⋆ up (@pts (Option ErrName) (optionalErrorEnc dom) p 2 o)) := by
  unfold hasErr
  fsym

end OneLogic.Try
