import Diff
open DiffOutcome DiffTest

def checkSearch : IO Unit := do
  let result := searchSchedules (fun o =>
    if o 0 = 0 then (⟨"{\"ok\":1}", .value⟩, #[2]) else (noResult, #[])) "{\"ok\":2}"
  unless result.kind == .value && (result.search.getD {}).status == .bounded &&
      (result.search.getD {}).sawNoResult do throw (IO.userError "unmatched bounded branch was not retained")
  let witness := searchSchedules (fun o =>
    if o 0 = 0 then (noResult, #[2]) else (⟨"{\"ok\":2}", .value⟩, #[])) "{\"ok\":2}"
  unless witness.kind == .value && (witness.search.getD {}).status == .witness do
    throw (IO.userError "valid schedule witness lost")
  let capped := searchSchedules (fun _ => (⟨"{\"ok\":1}", .value⟩, #[scheduleCap + 1])) "{\"ok\":2}"
  unless capped.kind == .searchCap && (capped.search.getD {}).status == .capped do
    throw (IO.userError "schedule cap mislabeled")

#eval checkSearch
