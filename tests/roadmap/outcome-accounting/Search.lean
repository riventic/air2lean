import Diff
open DiffOutcome DiffTest

def checkSearch : IO Unit := do
  let result := searchObservations scheduleFuel (fun o =>
    if o 0 = 0 then ({
      line := "{\"ok\":1}"
      kind := .value }, #[2]) else (noResult, #[])) "{\"ok\":2}"
  unless result.kind == .value && (result.search.getD {}).status == .bounded &&
      (result.search.getD {}).sawNoResult do throw (IO.userError "unmatched bounded branch was not retained")
  let witness := searchObservations scheduleFuel (fun o =>
    if o 0 = 0 then (noResult, #[2]) else ({
      line := "{\"ok\":2}"
      kind := .value }, #[])) "{\"ok\":2}"
  unless witness.kind == .value && (witness.search.getD {}).status == .witness do
    throw (IO.userError "valid schedule witness lost")
  let capped := searchObservations scheduleFuel (fun _ => ({
      line := "{\"ok\":1}"
      kind := .value }, #[scheduleCap + 1])) "{\"ok\":2}"
  unless capped.kind == .searchCap && (capped.search.getD {}).status == .capped do
    throw (IO.userError "schedule cap mislabeled")

  -- An omitted probe queue must retain bounded history through the original DFS.
  let fallback := searchObservationsWith 8 4 0 4 scheduleFuel (fun o =>
    if o 0 = 0 then (noResult, #[3]) else ({
      line := if o 0 = 2 then "{\"ok\":2}" else "{\"ok\":1}"
      kind := .value }, #[3])) "{\"ok\":2}"
  let evidence := fallback.search.getD {}
  unless fallback.kind == .value && evidence.status == .witness &&
      evidence.sawNoResult && evidence.runs == 3 &&
      evidence.schedulePrefix == #[2] && evidence.options == #[3] &&
      evidence.fuel == scheduleFuel && evidence.cap == 8 do
    throw (IO.userError "DFS fallback lost selected witness or bounded history")
  -- A race selected at the shared cap keeps the race's trace, not the last probe's.
  let raceCap := searchObservationsWith 2 4 4 4 scheduleFuel (fun o =>
    if o 0 = 0 then (failure .illegal, #[3]) else (noResult, #[3])) "absent"
  let raceEvidence := raceCap.search.getD {}
  unless raceCap.kind == .illegal && raceEvidence.status == .capped &&
      raceEvidence.sawNoResult && raceEvidence.runs == 2 &&
      raceEvidence.schedulePrefix == #[] && raceEvidence.options == #[3] do
    throw (IO.userError "race-cap selection lost typed history")

#eval checkSearch
