import ZigLean.Mem.Thread

/-! T04 weak ordering: the model's outcomes of the litmus tests of `litmus.zig`, and the check of
native observations against them (`docs/weak-ordering.md`).

`outcomes t` runs test `t` on the model's own atomics (`Zig.atomicLoadAt`, `Zig.atomicStoreAt`,
`ZigLean/Mem/Thread.lean`): every interleaving of the threads' operations, and at each operation
every option the model offers (which message a load reads, where a store goes in modification
order). Threads are made with `Thread.fork` after the cells are zero, as `std.Thread.spawn`
does. The set of final registers is the model's outcome set: by construction it contains every
outcome of a run of the generated code that executes these operations.

`lake env lean --run tests/roadmap/weak-ordering/Litmus.lean FILE...` reads observation files
(`litmus <test> <variant> rounds <n> <outcome>:<count> ...`) and fails unless

* every test of `tests` has exactly one line per file, and
* every observed outcome is a model outcome, except an outcome of a test whose `shape` the
  translator rejects (`lb`: the relaxed load-buffering shape, `checkLoadBuffering`, premise
  ORD-02): such an outcome is printed as `rejected shape`, never as a match.

It also prints, per test, the model outcomes that no file observed (`unobserved`): the model may
allow more than the hardware shows (no global SC order, `docs/std-models.md` §Thread model). -/

open Zig

namespace Weak

inductive LOp where
  | st (loc : Nat) (v : Nat) (ord : AtomicOrder)
  | ld (loc : Nat) (reg : Nat) (ord : AtomicOrder)

structure Test where
  name : String
  variant : String
  regs : Nat
  threads : List (List LOp)
  /-- The translator rejects this shape (`checkLoadBuffering`): its outcomes are not claims. -/
  rejectedShape : Bool := false

def x : Nat := 0
def y : Nat := 1
open AtomicOrder in
/-- `litmus.zig`'s `tests`, in its order. -/
def tests : List Test := [
  { name := "mp", variant := "relaxed", regs := 2, threads :=
      [[.st x 1 relaxed, .st y 1 relaxed], [.ld y 0 relaxed, .ld x 1 relaxed]] },
  { name := "mp", variant := "release_acquire", regs := 2, threads :=
      [[.st x 1 relaxed, .st y 1 release], [.ld y 0 acquire, .ld x 1 relaxed]] },
  { name := "sb", variant := "relaxed", regs := 2, threads :=
      [[.st x 1 relaxed, .ld y 0 relaxed], [.st y 1 relaxed, .ld x 1 relaxed]] },
  { name := "sb", variant := "seq_cst", regs := 2, threads :=
      [[.st x 1 seqCst, .ld y 0 seqCst], [.st y 1 seqCst, .ld x 1 seqCst]] },
  { name := "lb", variant := "relaxed", regs := 2, rejectedShape := true, threads :=
      [[.ld x 0 relaxed, .st y 1 relaxed], [.ld y 1 relaxed, .st x 1 relaxed]] },
  { name := "corr", variant := "relaxed", regs := 2, threads :=
      [[.st x 1 relaxed, .st x 2 relaxed], [.ld x 0 relaxed, .ld x 1 relaxed]] },
  { name := "wrc", variant := "release_acquire", regs := 3, threads :=
      [[.st x 1 release], [.ld x 0 acquire, .st y 1 release], [.ld y 1 acquire, .ld x 2 relaxed]] },
  { name := "iriw", variant := "relaxed", regs := 4, threads :=
      [[.st x 1 relaxed], [.st y 1 relaxed], [.ld x 0 relaxed, .ld y 1 relaxed],
       [.ld y 2 relaxed, .ld x 3 relaxed]] },
  { name := "iriw", variant := "acquire", regs := 4, threads :=
      [[.st x 1 relaxed], [.st y 1 relaxed], [.ld x 0 acquire, .ld y 1 acquire],
       [.ld y 2 acquire, .ld x 3 acquire]] }]

def cell (loc : Nat) : Ptr := ⟨some loc, 0⟩

/-- The options of `op` for thread `t` (`loadCount`/`storeCount`). -/
def optionCount (m : Mem) (t : ThreadId) : LOp → Nat
  | .st loc _ ord => storeCount 32 ord 4 (cell loc) { m with current := t }
  | .ld loc _ ord => loadCount 32 ord 4 (cell loc) { m with current := t }

/-- Option `c` of `op` for thread `t`: the next memory and registers, or none if it throws. -/
def step (m : Mem) (regs : Array Nat) (t : ThreadId) (c : Nat) : LOp → Option (Mem × Array Nat)
  | .st loc v ord =>
    match ((atomicStoreAt (n := 32) c ord 4 (cell loc) (BitVec.ofNat 32 v)).run
        { m with current := t }).run with
    | some (.ok ((), m')) => some (m', regs)
    | _ => none
  | .ld loc reg ord =>
    match ((atomicLoadAt (n := 32) c ord 4 (cell loc)).run { m with current := t }).run with
    | some (.ok (v, m')) => some (m', regs.set! reg v.toNat)
    | _ => none

/-- Every final register file of the remaining programs `progs` (thread `k + 1` runs
`progs[k]`), from `m`, over every interleaving and every option. An operation that throws ends
that branch with `none` in the result (the test then fails: litmus code never throws). -/
partial def explore (m : Mem) (regs : Array Nat) (progs : List (List LOp)) :
    List (Option (Array Nat)) :=
  if progs.all (·.isEmpty) then [some regs] else
  (progs.zipIdx.filterMap fun (ops, k) => ops.head?.map (·, k)).flatMap fun (op, k) =>
    let t := k + 1
    (List.range (optionCount m t op)).flatMap fun c =>
      match step m regs t c op with
      | some (m', regs') => explore m' regs' (progs.set k (progs[k]!.tail))
      | none => [none]

/-- The model's outcomes of `t`, as digit strings (register order), or an error. -/
def outcomes (t : Test) : Except String (List String) := do
  let cells : List (Array Byte × Nat × BlockKind) :=
    [(Array.replicate 4 (.int 0), 4, .global), (Array.replicate 4 (.int 0), 4, .global)]
  let m0 := Mem.ofGlobals .fresh cells
  -- Spawn the threads (main thread 0 forks 1..n), as `std.Thread.spawn` after the zeroing.
  let mut m := m0
  for _ in t.threads do
    match (Thread.fork.run m).run with
    | some (.ok (_, m')) => m := m'
    | _ => throw s!"{t.name} {t.variant}: fork failed"
  let results := explore m (Array.replicate t.regs 0) t.threads
  if results.any (·.isNone) then throw s!"{t.name} {t.variant}: a model operation threw"
  let strs := results.filterMap id |>.map fun rs =>
    String.join (rs.toList.map fun r => toString (Nat.min r 2))
  return strs.eraseDups

/-- The forbidden outcomes that the model's atomics must exclude (checked when this file is
elaborated): message passing through a release/acquire pair, read-read coherence, no load
buffering (no promises), and release/acquire causality (WRC). -/
def forbidden : List (String × String × String) := [
  ("mp", "release_acquire", "10"), ("corr", "relaxed", "21"), ("corr", "relaxed", "20"),
  ("corr", "relaxed", "10"), ("lb", "relaxed", "11"), ("wrc", "release_acquire", "110")]

#guard forbidden.all fun (n, v, o) =>
  match tests.find? (fun t => t.name == n && t.variant == v) with
  | some t => match outcomes t with
    | .ok os => !os.contains o && !os.isEmpty
    | .error _ => false
  | none => false

def key (t : Test) : String := s!"{t.name} {t.variant}"

/-- `litmus <test> <variant> rounds <n> <outcome>:<count> ...` → (key, outcomes with counts). -/
def parseLine (line : String) : Option (String × List (String × Nat)) :=
  match line.trimAscii.toString.splitOn " " with
  | "litmus" :: name :: variant :: "rounds" :: _ :: rest =>
    let pairs := rest.filterMap fun p => match p.splitOn ":" with
      | [o, c] => c.toNat?.map (o, ·)
      | _ => none
    if pairs.length == rest.length then some (s!"{name} {variant}", pairs) else none
  | _ => none

def main (files : List String) : IO UInt32 := do
  if files.isEmpty then
    IO.eprintln "usage: Litmus.lean FILE..."
    return 2
  let mut bad : List String := []
  let mut model : List (Test × List String) := []
  for t in tests do
    match outcomes t with
    | .ok os => model := model ++ [(t, os)]
    | .error e => bad := bad ++ [e]
  let mut seen : List (String × String) := []
  for file in files do
    let lines := ((← IO.FS.readFile file).splitOn "\n").filter (·.startsWith "litmus ")
    for (t, os) in model do
      match lines.filterMap parseLine |>.filter (·.1 == key t) with
      | [(_, obs)] =>
        for (o, c) in obs do
          seen := seen ++ [(key t, o)]
          if os.contains o then
            IO.println s!"match {file}: {key t} {o} ({c} rounds)"
          else if t.rejectedShape then
            IO.println s!"rejected shape (not a match) {file}: {key t} {o} ({c} rounds): \
              the translator rejects this load-buffering shape (premise ORD-02)"
          else
            bad := bad ++ [s!"{file}: {key t}: outcome {o} ({c} rounds) is not a model outcome \
              {os}"]
      | [] => bad := bad ++ [s!"{file}: no line for {key t}"]
      | _ => bad := bad ++ [s!"{file}: more than one line for {key t}"]
    let known := lines.filterMap parseLine |>.map (·.1)
    for k in known do
      unless model.any (key ·.1 == k) do bad := bad ++ [s!"{file}: unknown test {k}"]
  for (t, os) in model do
    let unobserved := os.filter fun o => !seen.contains (key t, o)
    IO.println s!"model {key t}: {os}{if unobserved.isEmpty then "" else s!" (unobserved: {unobserved})"}"
  if bad.isEmpty then
    IO.println s!"weak ordering: {files.length} file(s), every observed outcome is a model outcome"
    return 0
  for b in bad do IO.eprintln s!"error: {b}"
  return 1

end Weak

def main (args : List String) : IO UInt32 := Weak.main args
