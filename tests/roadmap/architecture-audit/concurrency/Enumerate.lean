/-! Architecture audit (concurrency): exhaustive schedule enumeration of the litmus fixtures.
Appended to the translation of `litmus.zig` (namespace `Litmus`) by `check.sh`. Every oracle
prefix is enumerated depth-first (each choice ranges over the options `runTrace` reports), so
the printed outcome set is exactly the model's set at this fuel; `none` is out of fuel. -/

namespace Litmus.Enumerate

def render : Zig.Sched.Out (Except Zig.ErrName (BitVec 32)) → String
  | none => "none(out of fuel)"
  | some (.error e) => s!"error({repr e})"
  | some (.ok (.ok v, _)) => s!"ok({v.toNat})"
  | some (.ok (.error e, _)) => s!"err({e})"

/-- Next oracle prefix in depth-first order, or `none` when exhausted. -/
partial def next (pre opts : Array Nat) : Option (Array Nat) :=
  let rec go (i : Nat) : Option (Array Nat) :=
    if i = 0 then none else
    let j := i - 1
    let c := pre.getD j 0
    if c + 1 < opts[j]! then some (((Array.range j).map fun x => pre.getD x 0).push (c + 1))
    else go j
  go opts.size

partial def enumerate (fuel cap : Nat) (main : Zig.ConcM Tgt (Except Zig.ErrName (BitVec 32))) :
    Array (String × Nat) × Nat × Bool :=
  let rec loop (pre : Array Nat) (runs : Nat) (acc : Array (String × Nat)) :
      Array (String × Nat) × Nat × Bool :=
    if runs ≥ cap then (acc, runs, false) else
    let (r, opts) := Zig.Sched.runTrace dispatch fuel (fun i => pre.getD i 0) main mem0
    let s := render r
    let acc := match acc.findIdx? (·.1 == s) with
      | some i => acc.modify i fun (k, n) => (k, n + 1)
      | none => acc.push (s, 1)
    match next pre opts with
    | some p => loop p (runs + 1) acc
    | none => (acc, runs + 1, true)
  loop #[] 0 #[]

def report (name : String) (main : Zig.ConcM Tgt (Except Zig.ErrName (BitVec 32)))
    (fuel : Nat := 20) (cap : Nat := 2000) : IO Unit := do
  let (acc, runs, done) := enumerate fuel cap main
  let outs := acc.toList.map fun (k, n) => s!"{k}x{n}"
  IO.println s!"{name}: fuel={fuel} runs={runs} exhaustive={done} outcomes={outs}"

end Litmus.Enumerate

open Litmus.Enumerate in
def main : IO Unit := do
  report "lbRelaxed" Litmus.lbRelaxed
  report "mpAllRelaxed" Litmus.mpAllRelaxed
  report "futexEarly" (Litmus.futexEarly ⟨⟩)
  report "groupGate" (Litmus.groupGate ⟨⟩)
  report "stackLifetime" Litmus.stackLifetime (fuel := 14)
