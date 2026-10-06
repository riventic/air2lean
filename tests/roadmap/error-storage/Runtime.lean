import ZigLean.Mem.Lemmas
import ZigLean.Mem.Alloc

open Zig

deriving instance DecidableEq for Except

def domain : ErrorDomain := ⟨#["Alpha", "Beta", "Gamma"], by decide, by decide⟩
def otherDomain : ErrorDomain := ⟨#["Beta", "Other"], by decide, by decide⟩
def alpha : FiniteError domain := ⟨"Alpha", by unfold domain; decide⟩
def beta : FiniteError domain := ⟨"Beta", by unfold domain; decide⟩

example : Enc.size (FiniteError domain) = 2 := rfl
example : Enc.size (Option (FiniteError domain)) = 2 := rfl
example (x : FiniteError domain) : Enc.decode (Enc.encode x) = pure x := LawfulEnc.decode_encode x
example (x : Option (FiniteError domain)) : Enc.decode (Enc.encode x) = pure x := LawfulEnc.decode_encode x
example : Enc.encode alpha ≠ Enc.encode beta := by
  intro h
  have := finiteError_encode_injective domain h
  have := congrArg Subtype.val this
  contradiction

-- The same LawfulEnc instances instantiate load_store_same and load_store_other.
-- Here a symbolic array update proves the neighboring element's bytes are untouched.
example (bytes : Array Byte) (hsize : 6 ≤ bytes.size) (x : Option (FiniteError domain)) :
    (writeBytes bytes 2 (Enc.encode x)).extract 4 6 = bytes.extract 4 6 := by
  apply extract_writeBytes_disjoint bytes 2 (Enc.encode x) 4 2
  · rw [LawfulEnc.size_encode x]; change 2 + 2 ≤ bytes.size; omega
  · omega
  · left; rw [LawfulEnc.size_encode x]; exact Nat.le_refl _

private def value (action : MemM α) : Option (Except Error α) :=
  (action.run {}).run.map (·.map Prod.fst)
private def require [DecidableEq α] [Repr α] (label : String) (got expected : α) : IO Unit := do
  unless got = expected do throw (IO.userError s!"{label}: {reprStr got} != {reprStr expected}")

private def slots : MemM (Option ErrName × Option ErrName × Option ErrName) :=
  letI : Enc (Option ErrName) := optionalErrorEnc domain
  do
    let p ← alloc .heap 6 2
    store 2 p (some "Gamma" : Option ErrName)
    store 2 (p.add 2) (none : Option ErrName)
    store 2 (p.add 4) (some "Beta" : Option ErrName)
    store 2 (p.add 2) (some "Alpha" : Option ErrName)
    store 2 p (none : Option ErrName)
    pure (← load (Option ErrName) 2 p, ← load (Option ErrName) 2 (p.add 2), ← load (Option ErrName) 2 (p.add 4))

private def standalone : MemM ErrName :=
  letI : Enc ErrName := errorEnc domain
  do
    let p ← alloc .heap 2 2
    store 2 p "Alpha"
    store 2 p "Beta"
    load ErrName 2 p

private def invalidStored : MemM ErrName :=
  letI : Enc ErrName := errorEnc domain
  do
    let p ← alloc .heap 2 2
    store 2 p "Other"
    load ErrName 2 p

def main : IO Unit := do
  require "slot frame and overwrite" (value slots) (some (.ok (none, some "Alpha", some "Beta")))
  require "standalone overwrite" (value standalone) (some (.ok "Beta"))
  require "foreign name cannot roundtrip" (value invalidStored) (some (.error .unspecified))
  require "standalone rejects zero" ((errorEnc domain).decode #[.int 0, .int 0]).run (some (.error .unspecified))
  require "optional zero" ((optionalErrorEnc domain).decode #[.int 0, .int 0]).run (some (.ok none))
  require "partial error" ((errorEnc domain).decode #[.errFrag "Alpha" 0]).run (some (.error .unspecified))
  require "mixed names" ((errorEnc domain).decode #[.errFrag "Alpha" 0, .errFrag "Beta" 1]).run (some (.error .unspecified))
  require "swapped fragments" ((errorEnc domain).decode #[.errFrag "Alpha" 1, .errFrag "Alpha" 0]).run (some (.error .unspecified))
  require "foreign domain" ((errorEnc otherDomain).decode (errBytes (some "Alpha"))).run (some (.error .unspecified))
  require "shared name stable across domains" ((errorEnc otherDomain).decode ((errorEnc domain).encode "Beta")).run (some (.ok "Beta"))
  require "no numeric ordinal invented" ((errorEnc domain).decode #[.int 1, .int 0]).run (some (.error .unspecified))
  let nested := Enc.optionWith (optionalErrorEnc domain)
  for v in #[none, some none, some (some "Alpha")] do
    require "nested optional roundtrip" (nested.decode (nested.encode v)).run (some (.ok v))
  require "nested optional flag size" nested.size 4
  let vec := Enc.vectorWith 3 (optionalErrorEnc domain)
  let input : Vector (Option ErrName) 3 := ⟨#[none, some "Alpha", some "Beta"], rfl⟩
  require "array dictionary size" vec.size 6
  require "array dictionary identity" (vec.decode (vec.encode input)).run (some (.ok input))
  let union := errorUnionEnc domain (errorEnc domain)
  require "error-union error identity" (union.decode (union.encode (.error "Beta"))).run (some (.ok (.error "Beta")))
  require "error-union payload identity" (union.decode (union.encode (.ok "Alpha"))).run (some (.ok (.ok "Alpha")))
  require "error-union foreign identity" (union.decode (union.encode (.error "Other"))).run (some (.error .unspecified))
