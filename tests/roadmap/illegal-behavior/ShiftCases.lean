
/-! The translation of `shiftguard.zig` (`check.sh` appends this file to each version's fresh
translation, namespace `ShiftGuard`): shifts of a 24-bit integer, with Sema's shift-amount check
on some paths only. For an amount of 24 or more, a shift without the check gives `.illegal` and
a shift with it gives the check's `.overflow`; for a smaller amount every shift gives its value.
A failing row raises `illegal-behavior case …`. -/

open Zig ShiftGuard

namespace ShiftCases

def check {α : Type} [BEq α] [Repr α] (name : String) (got : Result α) (want : Except Error α) :
    IO Unit :=
  let same := match got.run, want with
    | some (.ok a), .ok b => a == b
    | some (.error a), .error b => a == b
    | _, _ => false
  unless same do
    throw (IO.userError s!"illegal-behavior case {name}: got {repr got.run}, want {repr want}")

def cases : IO Unit := do
  for xn in [0, 1, 0x800001, 0xABCDEF, 0xFFFFFF] do
    let x : BitVec 24 := BitVec.ofNat 24 xn
    for cn in [0:32] do
      let c : BitVec 5 := BitVec.ofNat 5 cn
      let row := s!"{xn} by {cn}"
      let shl : BitVec 24 := x <<< cn
      let sar : BitVec 24 := x.sshiftRight cn
      -- What a shift gives: with Sema's check, and without it.
      let checked {α : Type} (v : α) : Except Error α := if cn < 24 then .ok v else .error .overflow
      let unchecked {α : Type} (v : α) : Except Error α := if cn < 24 then .ok v else .error .illegal
      check s!"mixed unchecked {row}" (mixed x c true) (unchecked shl)
      check s!"mixed checked {row}" (mixed x c false) (checked shl)
      check s!"mixedShr unchecked {row}" (mixedShr x c true) (unchecked sar)
      check s!"mixedShr checked {row}" (mixedShr x c false) (checked sar)
      check s!"checkedFirst unchecked {row}" (checkedFirst x c true) (checked (shl <<< cn))
      check s!"checkedFirst checked {row}" (checkedFirst x c false) (checked shl)
      check s!"safe {row}" (safe x c) (checked (shl >>> cn))
      check s!"unsafeOnly {row}" (unsafeOnly x c) (unchecked shl)
      -- The first shift (by `c`) has the check; the second one (by `d`) has none.
      for dn in [0, 23, 24, 31] do
        check s!"otherCount {row} then {dn}" (otherCount x c (BitVec.ofNat 5 dn))
          (if cn ≥ 24 then .error .overflow else if dn < 24 then .ok (shl <<< dn)
            else .error .illegal)

end ShiftCases

def main : IO Unit := do
  ShiftCases.cases
  IO.println "illegal-behavior shift guards passed"
