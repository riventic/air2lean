import Lean

namespace DiffTest

/-- The total number of executions attempted for one input, including probes. -/
def scheduleCap : Nat := 2000

private def cappedLine : String := "{\"fail\":\"Zig.Error.capped\"}"
private def illegalLine : String := "{\"fail\":\"Zig.Error.illegal\"}"

/-- The next leaf of the original depth-first enumeration. -/
private partial def nextSchedule (pre opts : Array Nat) : Option (Array Nat) :=
  let rec next (i : Nat) : Option (Array Nat) :=
    if i = 0 then none else
    let j := i - 1
    let c := pre.getD j 0
    if c + 1 < opts[j]! then
      some (((Array.range j).map fun x => pre.getD x 0).push (c + 1))
    else next j
  next opts.size

/-- Append zero-suffix alternatives after `pre`, in increasing choice-index order.
The limits constrain only probes; omitted alternatives remain in the DFS fallback. -/
partial def scheduleProbePrefixes (frontierCap prefixCap : Nat) (pre opts : Array Nat)
    (pending : List (Array Nat)) : List (Array Nat) :=
  let rec choices (j c : Nat) (pending : List (Array Nat)) : List (Array Nat) :=
    if pending.length >= frontierCap || j >= opts.size || j >= prefixCap then pending
    else if c < opts[j]! then
      let p := ((Array.range j).map fun x => pre.getD x 0).push c
      choices j (c + 1) (pending ++ [p])
    else choices (j + 1) 1 pending
  choices pre.size 1 pending

/-- Search first with a bounded FIFO of sparse oracle prefixes, then resume the original DFS.
Every execution uses the same total cap. Probe exhaustion, a full queue, or a long prefix
never establishes exhaustion: only the original DFS may return the first result as a mismatch.
A matching execution wins; otherwise an observed data race wins over a cap or mismatch. -/
partial def searchSchedulesWith (cap probeRuns frontierCap prefixCap : Nat)
    (run : (Nat → Nat) → String × Array Nat) (zig : String) : String :=
  let rememberRace (race : Option String) (line : String) :=
    race.orElse fun _ => if line == illegalLine then some line else none
  let rec dfs (pre : Array Nat) (runs : Nat) (first : String) (race : Option String) : String :=
    if runs >= cap then race.getD cappedLine else
    let (line, opts) := run fun i => pre.getD i 0
    if line == zig then line else
    let race := rememberRace race line
    match nextSchedule pre opts with
    | some p => dfs p (runs + 1) first race
    | none => race.getD first
  if cap = 0 then cappedLine else
  let (line, opts) := run fun _ => 0
  if line == zig then line else
  let first := line
  let race := rememberRace none line
  let originalNext := nextSchedule #[] opts
  let rec probes (pending : List (Array Nat)) (runs : Nat) (race : Option String) : String :=
    if runs >= cap then race.getD cappedLine else
    if runs >= probeRuns || pending.isEmpty then
      match originalNext with
      | some p => dfs p runs first race
      | none => race.getD first
    else match pending with
      | [] => race.getD first
      | p :: rest =>
        let (line, opts) := run fun i => p.getD i 0
        if line == zig then line else
        let race := rememberRace race line
        probes (scheduleProbePrefixes frontierCap prefixCap p opts rest) (runs + 1) race
  match originalNext with
  | none => race.getD first
  | some _ => probes (scheduleProbePrefixes frontierCap prefixCap #[] opts []) 1 race

/-- At most 256 probe executions (including the initial zero oracle), 128 pending prefixes,
and 4096 choices per stored prefix. The shared total execution budget remains 2000. -/
def searchSchedules (run : (Nat → Nat) → String × Array Nat) (zig : String) : String :=
  searchSchedulesWith scheduleCap 256 128 4096 run zig

end DiffTest
