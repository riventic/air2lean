/-! Architecture audit (concurrency): exhaustive schedule enumeration of the litmus fixtures.
Appended to the translation of `litmus.zig` (namespace `Litmus`) by `check.sh`. Every oracle
prefix is enumerated depth-first (each choice ranges over the options `runTrace` reports), so
the printed outcome set is exactly the model's set at this fuel; `none` is out of fuel. With
`seed := k`, every combination of the first `k` choices is enumerated separately (each with
its own cap), so an early choice (such as `Group.async`'s outcome) is not starved by the cap. -/

namespace Litmus.Enumerate

def render : Zig.Sched.Out (Except Zig.ErrName (BitVec 32)) → String
  | none => "none(out of fuel)"
  | some (.error e) => s!"error({repr e})"
  | some (.ok (.ok v, _)) => s!"ok({v.toNat})"
  | some (.ok (.error e, _)) => s!"err({e})"

/-- Next oracle prefix in depth-first order that keeps the first `keep` choices, or `none` when
exhausted. -/
partial def next (keep : Nat) (pre opts : Array Nat) : Option (Array Nat) :=
  let rec go (i : Nat) : Option (Array Nat) :=
    if i ≤ keep then none else
    let j := i - 1
    let c := pre.getD j 0
    if c + 1 < opts[j]! then some (((Array.range j).map fun x => pre.getD x 0).push (c + 1))
    else go j
  go opts.size

def runOne (fuel : Nat) (main : Zig.ConcM Tgt (Except Zig.ErrName (BitVec 32))) (pre : Array Nat) :
    String × Array Nat :=
  let (r, opts) := Zig.Sched.runTrace ⟨.any, .available⟩ dispatch fuel (fun i => pre.getD i 0) main mem0
  (render r, opts)

/-- Every combination of the first `depth` choices. -/
partial def seeds (fuel depth : Nat) (main : Zig.ConcM Tgt (Except Zig.ErrName (BitVec 32))) :
    Array (Array Nat) :=
  let rec grow (pre : Array Nat) : Array (Array Nat) :=
    if pre.size ≥ depth then #[pre] else
    let opts := (runOne fuel main pre).2
    if pre.size < opts.size then
      (Array.range opts[pre.size]!).foldl (fun acc c => acc ++ grow (pre.push c)) #[]
    else #[pre]
  grow #[]

partial def enumerate (fuel cap : Nat) (main : Zig.ConcM Tgt (Except Zig.ErrName (BitVec 32)))
    (seed : Array Nat) (acc : Array (String × Nat)) : Array (String × Nat) × Nat × Bool :=
  let rec loop (pre : Array Nat) (runs : Nat) (acc : Array (String × Nat)) :
      Array (String × Nat) × Nat × Bool :=
    if runs ≥ cap then (acc, runs, false) else
    let (s, opts) := runOne fuel main pre
    let acc := match acc.findIdx? (·.1 == s) with
      | some i => acc.modify i fun (k, n) => (k, n + 1)
      | none => acc.push (s, 1)
    match next seed.size pre opts with
    | some p => loop p (runs + 1) acc
    | none => (acc, runs + 1, true)
  loop seed 0 acc

def report (name : String) (main : Zig.ConcM Tgt (Except Zig.ErrName (BitVec 32)))
    (fuel : Nat := 20) (cap : Nat := 2000) (seed : Nat := 0) : IO Unit := do
  let mut acc := #[]
  let mut runs := 0
  let mut done := true
  for pre in seeds fuel seed main do
    let (a, r, d) := enumerate fuel cap main pre acc
    acc := a; runs := runs + r; done := done && d
  let outs := acc.toList.map fun (k, n) => s!"{k}x{n}"
  IO.println s!"{name}: fuel={fuel} runs={runs} exhaustive={done} outcomes={outs}"

end Litmus.Enumerate

open Litmus.Enumerate in
def main : IO Unit := do
  report "lbRelaxed" Litmus.lbRelaxed
  report "mpAllRelaxed" Litmus.mpAllRelaxed
  report "futexEarly" (Litmus.futexEarly ⟨⟩)
  report "groupGate" (Litmus.groupGate ⟨⟩) (cap := 300) (seed := 4)
  report "stackLifetime" Litmus.stackLifetime (fuel := 14)
