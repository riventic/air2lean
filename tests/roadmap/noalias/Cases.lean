import Gen

/-! The generated functions of `na.zig` (`Gen.lean`): a call that accesses memory through a
`noalias` parameter and through another pointer, one access a write, is `.illegal`; the same
call with disjoint pointers, or with only reads, returns its value. A failing row raises
`noalias case …`. -/

open Zig Noalias

namespace NoaliasCases

def run {α : Type} (x : MemM α) : Option (Except Error α) :=
  ((x.run (mem0 .fresh)).map Prod.fst).run

def check {α : Type} [BEq α] [Repr α] (name : String) (got : Option (Except Error α))
    (want : Except Error α) : IO Unit :=
  unless got.any (fun g => match g, want with
      | .ok a, .ok b => a == b
      | .error a, .error b => a == b
      | _, _ => false) do
    throw (IO.userError s!"noalias case {name}: got {repr got}, want {repr want}")

def main : IO Unit := do
  -- `copy(buf[shift..], buf, n)`: overlapping for `shift < n`.
  check "shiftCopy overlap 1 2" (run (shiftCopy 1 2)) (.error .illegal)
  check "shiftCopy overlap 4 8" (run (shiftCopy 4 8)) (.error .illegal)
  check "shiftCopy disjoint 8 8" (run (shiftCopy 8 8)) (.ok 8)
  check "shiftCopy disjoint 12 4" (run (shiftCopy 12 4)) (.ok 4)
  check "shiftCopy empty 0 0" (run (shiftCopy 0 0)) (.ok 16)
  check "twoBuffers 4" (run (twoBuffers 4)) (.ok 4)
  -- `swap(&x, &x)`: both `noalias`, the same pointer, writes.
  check "swapSelf same" (run (swapSelf true)) (.error .illegal)
  check "swapSelf distinct" (run (swapSelf false)) (.ok 21)
  -- Two `noalias` reads of the same pointer: no write, legal.
  check "sumSelf" (run sumSelf) (.ok 42)
  -- A `noalias` write and a read through another parameter.
  check "bumpOther same" (run (bumpOther true)) (.error .illegal)
  check "bumpOther distinct" (run (bumpOther false)) (.ok 7)
  -- The violation is found at once: a later overflow or a callee's safety panic does not
  -- take its place.
  check "overflowAfterOverlap same" (run (overflowAfterOverlap true)) (.error .illegal)
  check "overflowAfterOverlap distinct" (run (overflowAfterOverlap false)) (.error .overflow)
  check "panicAfterOverlap same" (run (panicAfterOverlap true)) (.error .illegal)
  check "panicAfterOverlap distinct" (run (panicAfterOverlap false)) (.error .unreachable)
  IO.println "noalias cases passed"

end NoaliasCases

def main : IO Unit := NoaliasCases.main
