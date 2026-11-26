
/-! The translation of `aligncast.zig` (`check.sh` appends this file to each version's fresh
translation, namespace `AlignCast`): `@alignCast` with runtime safety off. Every cast gives
`.illegal` for a misaligned operand and its value for an aligned one; a null operand passes the
alignment check, and the cast's own null rule decides. A failing row raises
`illegal-behavior case …`. -/

open Zig AlignCast

namespace AlignCases

/-- `none` for a result, the error otherwise. -/
def errOf {α : Type} (x : MemM α) : Option Error :=
  match ((x.run (mem0 .fresh)).map Prod.fst).run with
  | some (.error e) => some e
  | _ => none

def check (name : String) (got : Option Error) (want : Option Error) : IO Unit :=
  unless got == want do
    throw (IO.userError s!"illegal-behavior case {name}: got {repr got}, want {repr want}")

/-- `cast` on a pointer `off` bytes into a fresh 16-byte block of alignment 8. -/
def onPtr (off : Nat) {α : Type} (cast : Ptr → MemM α) : Option Error :=
  errOf (do let p ← alloc .heap 16 8; cast (p.add off))

def cases : IO Unit := do
  -- (name, the cast on a pointer, the error of the cast on null).
  let shapes : List (String × (Ptr → MemM Unit) × Option (Option Error)) := [
    ("ptrToPtr", fun p => discard (ptrToPtr p), none),
    ("optToPtr", fun p => discard (optToPtr (some p)), some (errOf (optToPtr none))),
    ("optToOpt", fun p => discard (optToOpt (some p)), some (errOf (optToOpt none))),
    ("optAlign", fun p => discard (optAlign (some p)), some (errOf (optAlign none))),
    ("ptrToOpt", fun p => discard (ptrToOpt p), none),
    ("manyOptToMany", fun p => discard (manyOptToMany (some p)), some (errOf (manyOptToMany none))),
    ("cToPtr", fun p => discard (cToPtr p), some (errOf (cToPtr Ptr.null))),
    ("cToC", fun p => discard (cToC p), some (errOf (cToC Ptr.null))),
    ("optToC", fun p => discard (optToC (some p)), some (errOf (optToC none))),
    ("cToOpt", fun p => discard (cToOpt p), some (errOf (cToOpt Ptr.null))),
    ("zeroToPtr", fun p => discard (zeroToPtr p), some (errOf (zeroToPtr Ptr.null))),
    ("sliceAlign", fun p => discard (sliceAlign ⟨p, 4⟩), none)]
  -- The casts whose null operand is itself illegal (to a pointer that cannot be null).
  let nullIllegal := ["optToPtr", "manyOptToMany", "cToPtr", "zeroToPtr"]
  for (name, cast, null) in shapes do
    check s!"{name} aligned" (onPtr 0 cast) none
    check s!"{name} aligned at 8" (onPtr 8 cast) none
    for off in [1, 2, 4, 7, 9, 12] do
      check s!"{name} misaligned by {off}" (onPtr off cast) (some .illegal)
    if let some got := null then
      check s!"{name} null" got (if nullIllegal.contains name then some .illegal else none)
  -- No stricter alignment: no check, only the unwrap.
  check "optSame at 1" (onPtr 1 fun p => discard (optSame (some p))) none
  check "optSame null" (errOf (optSame none)) (some .illegal)

end AlignCases

def main : IO Unit := do
  AlignCases.cases
  IO.println "illegal-behavior alignment casts passed"
