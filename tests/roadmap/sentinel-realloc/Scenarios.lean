-- Shared sentinel-reallocation observations; appended after the imports by `check.sh` and
-- `Model.lean`'s composition. Each line matches `native.zig`'s output exactly.
namespace SentinelReallocScenarios
open Zig

structure Ops where
  make : BitVec 64 → MemM (Except ErrName Slice)
  append : Slice → BitVec 8 → MemM (Except ErrName Slice)
  resize : Slice → BitVec 64 → MemM (Except ErrName Slice)
  release : Slice → MemM Unit

/-- The ZigLean model functions (`Zig.appendSentinel`, `Allocator.reallocSentinel`). -/
def model : Ops where
  make n := Allocator.allocSentinel {} n 0
  append s c := appendSentinel {} s c 0
  resize s n := Allocator.reallocSentinel {} s n 0
  release s := Allocator.freeSentinel {} 1 s

inductive Op where
  | append (c : Nat)
  | resize (n : Nat)

private def hex2 (v : BitVec 8) : String :=
  let d := Nat.toDigits 16 v.toNat
  String.ofList (if d.length < 2 then '0' :: d else d)

private def hexAt (s : Slice) (lo hi : Nat) : MemM String := do
  let mut out := ""
  for i in [lo:hi] do
    out := out ++ hex2 (← load (BitVec 8) 1 (s.ptr.add i))
  pure (if out.isEmpty then "-" else out)

private def liveCount (m : Mem) : Nat := (m.blocks.filter (fun b => b.live && b.kind == .heap)).size

/-- Fill `n` payload bytes with `a, b, ...`, apply `op`, read only defined bytes, release. -/
private def scenario (ops : Ops) (n : Nat) (op : Op) :
    MemM (Bool × Nat × String × String × Nat × Nat) := do
  match ← ops.make (BitVec.ofNat 64 n) with
  | .error _ => throw .illegal
  | .ok s0 =>
    for i in [:n] do store 1 (s0.ptr.add i) (BitVec.ofNat 8 (0x61 + i))
    let r ← match op with
      | .append c => ops.append s0 (BitVec.ofNat 8 c)
      | .resize k => ops.resize s0 (BitVec.ofNat 64 k)
    let (ok, s) ← match r with
      | .ok g => pure (true, g)
      | .error e => if e == "OutOfMemory" then pure (false, s0) else throw .illegal
    let defined := match op with
      | .append _ => if ok then s.len.toNat else n
      | .resize _ => Nat.min n s.len.toNat
    let payload ← hexAt s 0 defined
    let term ← hexAt s s.len.toNat (s.len.toNat + 1)
    let m ← get
    ops.release s
    pure (ok, s.len.toNat, payload, term, m.allocs, liveCount m)

private def runOne (ops : Ops) (name : String) (cap : Nat) (failures : List Nat) (n : Nat)
    (op : Op) : IO Unit := do
  let m0 : Mem := { allocPolicy := { maxBytes := cap, failures } }
  match ((scenario ops n op).run m0).run with
  | some (.ok ((ok, len, payload, term, allocs, live), final)) =>
    IO.println s!"{name} {if ok then "ok" else "oom"} {len} {payload} {term} {allocs} {live} {liveCount final}"
  | _ => throw (IO.userError s!"sentinel realloc scenario failed: {name}")

def run (ops : Ops) : IO Unit := do
  runOne ops "append" 64 [] 3 (.append 0x64)
  runOne ops "append-empty" 64 [] 0 (.append 0x78)
  runOne ops "append-fail" 64 [1] 3 (.append 0x64)
  runOne ops "append-cap" 4 [] 3 (.append 0x64)
  runOne ops "shrink" 64 [] 4 (.resize 2)
  runOne ops "shrink-empty" 64 [] 3 (.resize 0)
  runOne ops "grow" 64 [] 2 (.resize 4)
  runOne ops "same" 64 [] 2 (.resize 2)
  runOne ops "resize-fail" 64 [1] 4 (.resize 2)

end SentinelReallocScenarios
