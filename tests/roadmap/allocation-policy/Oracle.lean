import Proofs.Lists.Policy

/-! Lean-only M03 checks of the general policy: failure oracles, the live-heap budget, the
list-to-oracle embedding, the uncapped model default and a large translated fixture. These
cases have no native counterpart (`TestAllocator` keeps the harness cap and finite list). -/

open Zig

private def require (ok : Bool) (msg : String) : IO Unit :=
  unless ok do throw (IO.userError msg)

private def outcomes (P : AllocPolicy) (sizes : List Nat) : Option (List Bool × Mem) :=
  match ((releaseAttempts sizes 1).run { allocPolicy := P }).run with
  | some (.ok r) => some r
  | _ => none

private def checkAttempts (name : String) (P : AllocPolicy) (sizes : List Nat)
    (expected : List Bool) : IO Unit := do
  match outcomes P sizes with
  | some (oks, final) =>
    require (oks == expected && final.allocs == sizes.length && final.liveHeapBytes == 0)
      s!"{name}: outcome, attempt count or cleanup mismatch: {oks}"
  | none => throw (IO.userError s!"{name}: modeled error")
  IO.println s!"ok {name}"

/-- Three live 8-byte requests under a 20-byte budget, then one after a free. -/
private def budgetRun : MemM (List Bool) := do
  let p ← rawAlloc 8 1
  let q ← rawAlloc 8 1
  let r ← rawAlloc 8 1
  if let some p := p then rawFree p 8
  let s ← rawAlloc 8 1
  pure [p.isSome, q.isSome, r.isSome, s.isSome]

/-- `appendEach` over the translated `append` from an empty list header; returns the outcomes
and the final items. -/
private def appendRun (vs : List (BitVec 32)) : MemM (List Bool × List (BitVec 32)) := do
  let p ← alloc .stack 24 8
  store 8 p ({ items := ⟨zeroAllocPtr 4, 0⟩, capacity := 0 } : Lists.array_list_Aligned_u32_null)
  let rs ← Lists.appendEach p {} vs
  let l ← load Lists.array_list_Aligned_u32_null 8 p
  let items ← (List.range l.items.len.toNat).mapM fun i => load (BitVec 32) 4 (l.items.ptr.elem 4 (BitVec.ofNat 64 i))
  pure (rs.map (·.isOk), items)

def main : IO Unit := do
  let byIndex : AllocPolicy := { fails := fun i _ => i % 2 == 0 }
  checkAttempts "oracle-even-indices" byIndex [8, 8, 8, 8, 8, 8] [false, true, false, true, false, true]
  checkAttempts "oracle-by-size" { fails := fun _ n => 16 < n } [8, 32, 16, 17] [true, false, true, false]
  checkAttempts "oracle-all" { fails := fun _ _ => true } [8, 8, 8] [false, false, false]
  -- The finite-list policy and its oracle form agree, attempt by attempt.
  let listPolicy : AllocPolicy := { maxBytes := 32, failures := [1, 3] }
  let sizes := [8, 8, 40, 8, 32, 33]
  require ((outcomes listPolicy sizes).map (·.1) == (outcomes listPolicy.asOracle sizes).map (·.1))
    "list policy and its oracle form disagree"
  checkAttempts "list-as-oracle" listPolicy.asOracle sizes [true, false, false, false, true, false]
  -- The budget bounds live heap bytes, so a free makes room again.
  match ((budgetRun.run { allocPolicy := { budget := some 20 } }).run) with
  | some (.ok (oks, final)) =>
    require (oks == [true, true, false, true] && final.liveHeapBytes == 16) s!"budget mismatch: {oks}"
  | _ => throw (IO.userError "budget: modeled error")
  IO.println "ok budget"
  -- The model default has no fixed cap; the harness cap is an explicit choice.
  checkAttempts "default-uncapped" {} [maxAllocBytes + 1] [true]
  checkAttempts "harness-cap" AllocPolicy.harness [maxAllocBytes + 1] [false]
  -- A translated client: `dupe` of a 1 MiB + 1 byte slice, beyond the old fixed cap.
  let n := maxAllocBytes + 1
  let large (P : AllocPolicy) : Option (Except ErrName Slice × Nat) :=
    match ((do
        let src ← alloc .global n 1
        let r ← Lists.dupe {} ⟨src, BitVec.ofNat 64 n⟩
        pure (r, (← get).liveHeapBytes)).run { Lists.mem0 with allocPolicy := P }).run with
    | some (.ok r) => some r.1
    | _ => none
  match large {} with
  | some (.ok s, live) => require (s.len.toNat == n && live == n) "large dupe: wrong result"
  | _ => throw (IO.userError "large dupe failed under the default policy")
  match large .harness with
  | some (.error "OutOfMemory", 0) => pure ()
  | _ => throw (IO.userError "large dupe must fail under the harness cap")
  IO.println "ok large-dupe"
  -- Several failures in one run of the translated `append` loop: each failure is reported
  -- and leaves the list unchanged, so exactly the successful values remain.
  let vs : List (BitVec 32) := [1, 2, 3, 4, 5, 6, 7, 8]
  match ((appendRun vs).run { Lists.mem0 with allocPolicy := { fails := fun i _ => i < 3 } }).run with
  | some (.ok ((oks, items), _)) =>
    require (oks == [false, false, false, true, true, true, true, true] && items == [4, 5, 6, 7, 8])
      s!"append loop mismatch: {oks} {items}"
  | _ => throw (IO.userError "append loop: modeled error")
  IO.println "ok append-loop-several-failures"
