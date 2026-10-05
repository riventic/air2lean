import Outcome

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
  let rec choices (j c pendingCount : Nat) (pending : List (Array Nat)) : List (Array Nat) :=
    if pendingCount >= frontierCap || j >= opts.size || j >= prefixCap then pending
    else if c < opts[j]! then
      let p := ((Array.range j).map fun x => pre.getD x 0).push c
      choices j (c + 1) (pendingCount + 1) (pending ++ [p])
    else choices (j + 1) 1 pendingCount pending
  choices pre.size 1 pending.length pending

/-- Search first with a bounded FIFO of sparse oracle prefixes, then resume the original DFS.
Every execution uses the same total cap. Probe exhaustion, a full queue, or a long prefix
never establishes exhaustion: only the original DFS may return the first result as a mismatch.
A matching execution wins; otherwise an observed data race wins over a cap or mismatch.
Typed observations retain the selected execution and all encountered no-result branches. -/
partial def searchObservationsWith (cap probeRuns frontierCap prefixCap fuel : Nat)
    (run : (Nat → Nat) → DiffOutcome.Observation × Array Nat)
    (zig : String) : DiffOutcome.Observation :=
  let annotate (out : DiffOutcome.Observation) (pre opts : Array Nat) (runs : Nat) :=
    { out with search := some {
        schedulePrefix := pre
        options := opts
        runs := runs
        fuel := fuel
        cap := cap } }
  let finish (out : DiffOutcome.Observation) (runs : Nat)
      (status : DiffOutcome.SearchStatus) (bounded : Bool) :=
    { out with search := some { (out.search.getD {}) with
        runs := runs
        status := status
        sawNoResult := bounded } }
  let capped (out : DiffOutcome.Observation) :=
    { out with line := cappedLine, kind := .searchCap }
  let rememberRace (race : Option DiffOutcome.Observation) (out : DiffOutcome.Observation) :=
    race.orElse fun _ => if out.kind == .illegal then some out else none
  let rec dfs (pre : Array Nat) (runs : Nat) (first : DiffOutcome.Observation)
      (race : Option DiffOutcome.Observation) (last : DiffOutcome.Observation)
      (bounded : Bool) : DiffOutcome.Observation :=
    if runs >= cap then finish (race.getD (capped last)) runs .capped bounded else
    let (raw, opts) := run fun i => pre.getD i 0
    let out := annotate raw pre opts (runs + 1)
    let bounded := bounded || out.kind == .boundedNoResult
    if out.line == zig then finish out (runs + 1) .witness bounded else
    let race := rememberRace race out
    match nextSchedule pre opts with
    | some p => dfs p (runs + 1) first race out bounded
    | none => finish (race.getD first) (runs + 1)
        (if bounded then .bounded else .exhausted) bounded
  if cap = 0 then
    finish (capped (annotate DiffOutcome.noResult #[] #[] 0)) 0 .capped false
  else
  let (raw, opts) := run fun _ => 0
  let out := annotate raw #[] opts 1
  let bounded := out.kind == .boundedNoResult
  if out.line == zig then finish out 1 .witness bounded else
  let first := out
  let race := rememberRace none out
  let originalNext := nextSchedule #[] opts
  let rec probes (pending : List (Array Nat)) (runs : Nat)
      (race : Option DiffOutcome.Observation) (last : DiffOutcome.Observation)
      (bounded : Bool) : DiffOutcome.Observation :=
    if runs >= cap then finish (race.getD (capped last)) runs .capped bounded else
    if runs >= probeRuns || pending.isEmpty then
      match originalNext with
      | some p => dfs p runs first race last bounded
      | none => finish (race.getD first) runs (if bounded then .bounded else .exhausted) bounded
    else match pending with
      | [] => finish (race.getD first) runs (if bounded then .bounded else .exhausted) bounded
      | p :: rest =>
        let (raw, opts) := run fun i => p.getD i 0
        let out := annotate raw p opts (runs + 1)
        let bounded := bounded || out.kind == .boundedNoResult
        if out.line == zig then finish out (runs + 1) .witness bounded else
        let race := rememberRace race out
        probes (scheduleProbePrefixes frontierCap prefixCap p opts rest) (runs + 1) race out bounded
  match originalNext with
  | none => finish (race.getD first) 1 (if bounded then .bounded else .exhausted) bounded
  | some _ => probes (scheduleProbePrefixes frontierCap prefixCap #[] opts []) 1 race out bounded

/-- At most 256 probe executions (including the initial zero oracle), 128 pending prefixes,
and 4096 choices per stored prefix. The shared total execution budget remains 2000. -/
def searchObservations (fuel : Nat)
    (run : (Nat → Nat) → DiffOutcome.Observation × Array Nat)
    (zig : String) : DiffOutcome.Observation :=
  searchObservationsWith scheduleCap 256 128 4096 fuel run zig

/-- Legacy string fixtures exercise the same typed FIFO/DFS implementation. -/
def searchSchedulesWith (cap probeRuns frontierCap prefixCap : Nat)
    (run : (Nat → Nat) → String × Array Nat) (zig : String) : String :=
  let observe := fun oracle =>
    let (line, opts) := run oracle
    let out : DiffOutcome.Observation := {
      line := line
      kind := if line == illegalLine then .illegal else .value }
    (out, opts)
  (searchObservationsWith cap probeRuns frontierCap prefixCap 0 observe zig).line

def searchSchedules (run : (Nat → Nat) → String × Array Nat) (zig : String) : String :=
  searchSchedulesWith scheduleCap 256 128 4096 run zig

end DiffTest
