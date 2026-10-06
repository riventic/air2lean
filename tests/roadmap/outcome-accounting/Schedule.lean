import Schedules
open DiffOutcome DiffTest

-- `panic!` in the zero-budget callback needs a fallback type inhabitant;
-- the callback must remain unreachable, as checked by the empty execution list.
private instance : Inhabited Observation := ⟨noResult⟩

private def require (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)

private def value (n : Nat) : Observation := { line := "{\"ok\":" ++ toString n ++ "}", kind := .value }

private def finite (o : Nat → Nat) : Observation × Array Nat :=
  (value (o 0 % 3), #[3])

private def rejects {α : Type} (r : Except String α) : Bool :=
  match r with | .error _ => true | .ok _ => false

private def request (mode : String) (extra : List (String × Lean.Json) := []) : Lean.Json :=
  let base : List (String × Lean.Json) := [("schema", Lean.toJson (1 : Nat)), ("mode", .str mode),
    ("example", .str "threads"), ("function", .str "claimOnce"),
    ("input", .arr #[]), ("fuel", Lean.toJson (0 : Nat)),
    ("node_cap", Lean.toJson (1 : Nat)), ("prefix_cap", Lean.toJson (4096 : Nat))]
  Lean.Json.mkObj (base.filter (fun pair => !extra.any (fun item => item.1 == pair.1)) ++ extra)

private def rejectsIO (action : IO α) : IO Bool := do
  try
    let _ ← action
    pure false
  catch _ => pure true

/-- Source tests for bounded enumeration and strict replay, separate from matching search. -/
def checkScheduleProtocol : IO Unit := do
  -- A bounded reader must continue after short reads and validate bytes before decoding.
  let buffer ← IO.mkRef ({ data := "abc".toUTF8 } : IO.FS.Stream.Buffer)
  let stream := IO.FS.Stream.ofBuffer buffer
  let short := { stream with read := fun count => stream.read (min count 1) }
  require ((← ScheduleCLI.readRequest short 3) == "abc") "partial stream reads mistaken for EOF"
  let oversized ← IO.mkRef ({ data := "abcd".toUTF8 } : IO.FS.Stream.Buffer)
  require (← rejectsIO (ScheduleCLI.readRequest (IO.FS.Stream.ofBuffer oversized) 3))
    "oversized stream was accepted"
  let badUtf8 ← IO.mkRef ({ data := ByteArray.empty.push 255 } : IO.FS.Stream.Buffer)
  require (← rejectsIO (ScheduleCLI.readRequest (IO.FS.Stream.ofBuffer badUtf8) 3))
    "invalid UTF-8 accepted"
  let empty ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  require ((← ScheduleCLI.readRequest (IO.FS.Stream.ofBuffer empty) 0) == "")
    "empty zero-limit stream rejected"
  let all := enumerateSchedules 3 1 finite
  require (all.executions.size == 3 && all.outcomes.size == 3 &&
    !all.nodeCapReached && !all.prefixCapReached) "enumeration stopped at an observed outcome or falsely capped"
  require (all.executions.map (·.«prefix») == #[#[0], #[1], #[2]]) "enumeration order differs"
  for e in all.executions do
    match replaySchedule 1 finite e.«prefix» with
    | .error err => throw (IO.userError err)
    | .ok replay => require (replay.observation.line == e.observation.line &&
        replay.options == e.options && replay.traceComplete) "enumerated execution did not replay"
  let capped := enumerateSchedules 2 1 finite
  require (capped.executions.size == 2 && capped.nodeCapReached) "node cap did not count actual executions"
  let zero := enumerateSchedules 0 1 (fun _ => panic! "zero cap ran oracle")
  require (zero.executions.isEmpty && zero.nodeCapReached) "zero node cap was not explicit"
  let narrow := enumerateSchedules 20 0 finite
  require (narrow.executions.size == 1 && narrow.prefixCapReached &&
    !narrow.executions[0]!.traceComplete && narrow.executions[0]!.choiceCount == 1 &&
    narrow.executions[0]!.«prefix».isEmpty) "zero prefix cap hid truncation"
  let bounded := enumerateSchedules 4 1 (fun o =>
    (if o 0 == 0 then value 0 else noResult, #[2]))
  require (bounded.executions.size == 2 && bounded.sawNoResult && bounded.outcomes.size == 2 &&
    !bounded.nodeCapReached) "no-result branch disappeared from enumeration"
  let duplicates := enumerateSchedules 4 1 (fun _ => (value 7, #[3]))
  require (duplicates.executions.size == 3 && duplicates.outcomes.size == 1) "outcome deduplication lost executions"
  require (rejects (replaySchedule 1 finite #[]) &&
    rejects (replaySchedule 2 finite #[0, 0]) &&
    rejects (replaySchedule 1 finite #[3]) &&
    rejects (replaySchedule 0 finite #[0])) "invalid replay prefix accepted"
  require (rejects (replaySchedule 1 (fun _ => (value 0, #[0])) #[1])) "zero-option choice wrapped silently"
  match replaySchedule 1 (fun _ => (value 0, #[0])) #[0] with
  | .error e => throw (IO.userError e)
  | .ok _ => pure ()
  -- Variable-depth branches require a full trace, even where zeros were implicit during DFS.
  let tree := fun o => if o 0 == 0 then (value 0, #[2]) else (value (1 + o 1 % 2), #[2, 2])
  let varied := enumerateSchedules 10 2 tree
  require (varied.executions.map (·.«prefix») == #[#[0], #[1, 0], #[1, 1]]) "variable-depth DFS trace differs"
  require (rejects (replaySchedule 2 tree #[1])) "missing default-zero suffix accepted as strict replay"
  -- The public CLI rejects malformed binding requests before emitting replay success.
  require (← rejectsIO (ScheduleCLI.execute (request "enumerate" [("surprise", .null)]))) "unknown CLI field accepted"
  require (← rejectsIO (ScheduleCLI.execute (request "enumerate" [("prefix", .arr #[])]))) "enumeration accepted replay-only prefix"
  require (← rejectsIO (ScheduleCLI.execute (request "replay" [("prefix", .arr #[]),
    ("expected", Lean.Json.mkObj [("kind", .str "value")])]))) "incorrect expected replay kind accepted"
  for (key, invalid) in [("schema", Lean.toJson (2 : Nat)),
      ("fuel", Lean.toJson (100001 : Nat)), ("node_cap", Lean.toJson (2001 : Nat)),
      ("prefix_cap", Lean.toJson (4097 : Nat)), ("fuel", Lean.toJson true),
      ("input", Lean.Json.str "wrong shape"), ("mode", Lean.Json.str "matching")] do
    require (← rejectsIO (ScheduleCLI.execute (request "enumerate" [(key, invalid)])))
      s!"malformed or excessive {key} accepted"
  require (← rejectsIO (ScheduleCLI.execute (request "replay" [("prefix", .arr #[]),
    ("node_cap", Lean.toJson (0 : Nat))]))) "zero-budget replay accepted"
  require (← rejectsIO (ScheduleCLI.execute (request "replay" [("prefix", .arr #[Lean.toJson true])])))
    "non-natural replay choice accepted"
  require (← rejectsIO (ScheduleCLI.execute (request "replay" [("prefix", .arr #[]),
    ("expected", Lean.Json.mkObj [("options", Lean.toJson (#[1] : Array Nat))])])) )
    "incorrect expected replay options accepted"
  -- Fuel zero flows through the real generated program/dispatch registry as bounded no-result.
  let run ← DiffConcurrent.runner "threads" "claimOnce" (.arr #[]) 0
  require ((run (fun _ => 0)).1.kind == .boundedNoResult) "request fuel did not reach generated scheduler"

#eval checkScheduleProtocol
