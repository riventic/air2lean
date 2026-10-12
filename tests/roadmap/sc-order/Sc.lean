import ZigLean.Mem.Thread

/-! C10: what the model's atomics (`ZigLean/Mem/Thread.lean`) can and cannot separate between
relaxed, release/acquire and `seq_cst` (`docs/research/C10.md`).

`modelOutcomes t` is the model's outcome set of litmus test `t` of `sc.zig`: every interleaving
and, at each operation, every option the model offers (the harness of
`tests/roadmap/weak-ordering/Litmus.lean`). `scOutcomes t` is the outcome set of the sequential
interleavings of the same operations over a plain store: for a test whose operations are all
`seq_cst`, it is RC11's outcome set (every access is in the total SC order, which then agrees
with program order and reads-from).

The `#guard`s record the facts the research rests on:

* the model contains every sequentially consistent outcome (it over-approximates);
* it contains outcomes that RC11 forbids for the all-`seq_cst` tests (`sb`: both loads 0; `2+2w`:
  both locations end with the first thread's value; `iriw`: the readers disagree on the order of
  the writes), which is premise ORD-03; and
* its outcome set for `seq_cst` equals that for release/acquire, so a litmus proof cannot tell the
  two apart.

`lake env lean --run tests/roadmap/sc-order/Sc.lean FILE...` also checks observation files
(`sc.zig`): every observed outcome must be a model outcome, and for an all-`seq_cst` test also an
SC outcome (a hardware outcome outside it would be a miscompilation or a harness error). -/

open Zig

namespace Sc

inductive LOp where
  | st (loc : Nat) (v : Nat) (ord : AtomicOrder)
  | ld (loc : Nat) (reg : Nat) (ord : AtomicOrder)
  deriving Inhabited

structure Test where
  name : String
  variant : String
  regs : Nat
  /-- The registers are the final values of x and y (the last message of each location). -/
  final : Bool := false
  /-- Every operation is `seq_cst`: RC11's outcomes are the SC interleavings. -/
  allSc : Bool := false
  threads : List (List LOp)
  deriving Inhabited

def x : Nat := 0
def y : Nat := 1
open AtomicOrder in
/-- `sc.zig`'s `tests`, in its order. -/
def tests : List Test := [
  { name := "sb", variant := "relaxed", regs := 2, threads :=
      [[.st x 1 relaxed, .ld y 0 relaxed], [.st y 1 relaxed, .ld x 1 relaxed]] },
  { name := "sb", variant := "release_acquire", regs := 2, threads :=
      [[.st x 1 release, .ld y 0 acquire], [.st y 1 release, .ld x 1 acquire]] },
  { name := "sb", variant := "seq_cst", regs := 2, allSc := true, threads :=
      [[.st x 1 seqCst, .ld y 0 seqCst], [.st y 1 seqCst, .ld x 1 seqCst]] },
  { name := "sb", variant := "mixed", regs := 2, threads :=
      [[.st x 1 seqCst, .ld y 0 seqCst], [.st y 1 release, .ld x 1 acquire]] },
  { name := "2+2w", variant := "relaxed", regs := 2, final := true, threads :=
      [[.st x 1 relaxed, .st y 2 relaxed], [.st y 1 relaxed, .st x 2 relaxed]] },
  { name := "2+2w", variant := "release", regs := 2, final := true, threads :=
      [[.st x 1 release, .st y 2 release], [.st y 1 release, .st x 2 release]] },
  { name := "2+2w", variant := "seq_cst", regs := 2, final := true, allSc := true, threads :=
      [[.st x 1 seqCst, .st y 2 seqCst], [.st y 1 seqCst, .st x 2 seqCst]] },
  { name := "iriw", variant := "acquire", regs := 4, threads :=
      [[.st x 1 release], [.st y 1 release], [.ld x 0 acquire, .ld y 1 acquire],
       [.ld y 2 acquire, .ld x 3 acquire]] },
  { name := "iriw", variant := "seq_cst", regs := 4, allSc := true, threads :=
      [[.st x 1 seqCst], [.st y 1 seqCst], [.ld x 0 seqCst, .ld y 1 seqCst],
       [.ld y 2 seqCst, .ld x 3 seqCst]] }]

def cell (loc : Nat) : Ptr := ⟨some loc, 0⟩

def optionCount (m : Mem) (t : ThreadId) : LOp → Nat
  | .st loc _ ord => storeCount 32 ord 4 (cell loc) { m with current := t }
  | .ld loc _ ord => loadCount 32 ord 4 (cell loc) { m with current := t }

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

/-- The registers after the final reads of x and y: the main thread's option 0 is the newest
message, the last in modification order. -/
def finalRegs (m : Mem) : Option (Array Nat) := do
  let (m1, vx) ← step m #[0, 0] 0 0 (.ld x 0 .seqCst)
  let (_, vs) ← step m1 vx 0 0 (.ld y 1 .seqCst)
  pure vs

partial def explore (final : Bool) (m : Mem) (regs : Array Nat) (progs : List (List LOp)) :
    List (Option (Array Nat)) :=
  if progs.all (·.isEmpty) then
    if final then [finalRegs m] else [some regs]
  else
  (progs.zipIdx.filterMap fun (ops, k) => ops.head?.map (·, k)).flatMap fun (op, k) =>
    let t := k + 1
    (List.range (optionCount m t op)).flatMap fun c =>
      match step m regs t c op with
      | some (m', regs') => explore final m' regs' (progs.set k (progs[k]!.tail))
      | none => [none]

def digits (rs : Array Nat) : String := String.join (rs.toList.map fun r => toString (Nat.min r 2))

/-- The model's outcomes of `t`, as digit strings (register order), or an error. -/
def modelOutcomes (t : Test) : Except String (List String) := do
  let cells : List (Array Byte × Nat × BlockKind) :=
    [(Array.replicate 4 (.int 0), 4, .global), (Array.replicate 4 (.int 0), 4, .global)]
  let mut m := Mem.ofGlobals .fresh cells
  for _ in t.threads do
    match (Thread.fork.run m).run with
    | some (.ok (_, m')) => m := m'
    | _ => throw s!"{t.name} {t.variant}: fork failed"
  let results := explore t.final m (Array.replicate t.regs 0) t.threads
  if results.any (·.isNone) then throw s!"{t.name} {t.variant}: a model operation threw"
  return (results.filterMap id |>.map digits).eraseDups

/-- Sequentially consistent interleavings over a plain store `(x, y)`. -/
partial def scExplore (final : Bool) (mem : Array Nat) (regs : Array Nat) (progs : List (List LOp)) :
    List (Array Nat) :=
  if progs.all (·.isEmpty) then [if final then mem else regs] else
  (progs.zipIdx.filterMap fun (ops, k) => ops.head?.map (·, k)).flatMap fun (op, k) =>
    let rest := progs.set k (progs[k]!.tail)
    match op with
    | .st loc v _ => scExplore final (mem.set! loc v) regs rest
    | .ld loc reg _ => scExplore final mem (regs.set! reg mem[loc]!) rest

def scOutcomes (t : Test) : List String :=
  (scExplore t.final #[0, 0] (Array.replicate t.regs 0) t.threads |>.map digits).eraseDups

def find (n v : String) : Test :=
  (tests.find? fun t => t.name == n && t.variant == v).getD (tests.head!)

def model (n v : String) : List String := (modelOutcomes (find n v)).toOption.getD []

-- The model over-approximates SC: every interleaving outcome is a model outcome.
#guard tests.all fun t => (scOutcomes t).all fun o => (model t.name t.variant).contains o

-- ORD-03, with counterexamples: RC11 forbids these outcomes for the all-`seq_cst` tests (each is
-- absent from the interleavings), and the model produces them.
#guard [("sb", "00"), ("2+2w", "11"), ("iriw", "1010")].all fun (n, o) =>
  !(scOutcomes (find n "seq_cst")).contains o && (model n "seq_cst").contains o

-- Release/acquire (release stores for `2+2w`, and `sb` mixed with one non-`seq_cst` thread)
-- genuinely allow them in RC11, and the model agrees: only the `seq_cst` variants have too many.
#guard [("sb", "release_acquire", "00"), ("2+2w", "release", "11"), ("iriw", "acquire", "1010"),
    ("sb", "mixed", "00")].all fun (n, v, o) => (model n v).contains o

-- The model cannot tell `seq_cst` from release/acquire: equal outcome sets.
#guard model "sb" "seq_cst" == model "sb" "release_acquire"
#guard model "iriw" "seq_cst" == model "iriw" "acquire"
#guard model "2+2w" "seq_cst" == model "2+2w" "release"

def key (t : Test) : String := s!"{t.name} {t.variant}"

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
    IO.eprintln "usage: Sc.lean FILE..."
    return 2
  let mut bad : List String := []
  for file in files do
    let lines := ((← IO.FS.readFile file).splitOn "\n").filter (·.startsWith "litmus ")
    for t in tests do
      match modelOutcomes t with
      | .error e => bad := bad ++ [e]
      | .ok os =>
        match lines.filterMap parseLine |>.filter (·.1 == key t) with
        | [(_, obs)] =>
          for (o, c) in obs do
            let sc := (scOutcomes t).contains o
            if !os.contains o then
              bad := bad ++ [s!"{file}: {key t}: outcome {o} ({c} rounds) is not a model outcome {os}"]
            else if t.allSc && !sc then
              bad := bad ++ [s!"{file}: {key t}: outcome {o} ({c} rounds) is not sequentially \
                consistent"]
            else
              IO.println s!"match {file}: {key t} {o} ({c} rounds){if sc then "" else " [not SC]"}"
        | [] => bad := bad ++ [s!"{file}: no line for {key t}"]
        | _ => bad := bad ++ [s!"{file}: more than one line for {key t}"]
  for t in tests do
    IO.println s!"{key t}: model {(modelOutcomes t).toOption.getD []} sc {scOutcomes t}"
  if bad.isEmpty then
    IO.println s!"sc order: {files.length} file(s) pass"
    return 0
  for b in bad do IO.eprintln s!"error: {b}"
  return 1

end Sc

def main (args : List String) : IO UInt32 := Sc.main args
