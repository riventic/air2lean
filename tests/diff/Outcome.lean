import Lean.Data.Json
import ZigLean.Basic

/-! Test-runner observations, not new runtime semantics or proof claims. -/
namespace DiffOutcome
open Lean (Json)

inductive Kind where
  | value | errorReturn | modelPanic | illegal | unspecified | deadlock
  | boundedNoResult | searchCap | inputFailure | nativeHarnessFailure
  deriving BEq, DecidableEq, Repr

def Kind.tag : Kind → String
  | .value => "value"
  | .errorReturn => "error_return"
  | .modelPanic => "model_panic"
  | .illegal => "illegal"
  | .unspecified => "unspecified"
  | .deadlock => "deadlock"
  | .boundedNoResult => "bounded_no_result"
  | .searchCap => "search_cap"
  | .inputFailure => "input_failure"
  | .nativeHarnessFailure => "native_harness_failure"

/-- Classify source error unions from their values, before payload rendering. -/
class ReturnedError (α : Type) where
  isError : α → Bool
instance (priority := low) : ReturnedError α where
  isError _ := false
instance [ReturnedError α] : ReturnedError (Except Zig.ErrName α) where
  isError | .error _ => true | .ok a => ReturnedError.isError a
instance [ReturnedError α] : ReturnedError (Option α) where
  isError | none => false | some a => ReturnedError.isError a

def valueKind [ReturnedError α] (a : α) : Kind :=
  if ReturnedError.isError a then .errorReturn else .value

def errorKind : Zig.Error → Kind
  | .illegal => .illegal
  | .unspecified => .unspecified
  | .deadlock => .deadlock
  | .overflow | .outOfBounds | .divByZero | .unreachable | .panic => .modelPanic

inductive SearchStatus where
  | witness | exhausted | capped | bounded
  deriving BEq, DecidableEq, Repr

def SearchStatus.tag : SearchStatus → String
  | .witness => "witness"
  | .exhausted => "exhausted"
  | .capped => "capped"
  | .bounded => "bounded"

structure Search where
  schedulePrefix : Array Nat := #[]
  options : Array Nat := #[]
  runs : Nat := 0
  fuel : Nat := 0
  cap : Nat := 0
  status : SearchStatus := .exhausted
  sawNoResult : Bool := false

structure Observation where
  line : String
  kind : Kind
  search : Option Search := none

def Observation.metadata (o : Observation) : Json :=
  let fields := [("schema", Lean.toJson (1 : Nat)), ("kind", Json.str o.kind.tag),
    ("legacy_line", Json.str o.line)]
  Json.mkObj (fields ++ match o.search with
    | none => []
    | some s => [("search", Json.mkObj [
        ("prefix", Lean.toJson s.schedulePrefix), ("options", Lean.toJson s.options),
        ("runs", Lean.toJson s.runs), ("fuel", Lean.toJson s.fuel),
        ("cap", Lean.toJson s.cap), ("status", Json.str s.status.tag),
        ("saw_no_result", Lean.toJson s.sawNoResult)])])

/-- Keep legacy wire shapes; `none` is deliberately not classified as proven divergence. -/
def noResult : Observation := {
  line := "{\"diverge\":true}"
  kind := .boundedNoResult }
def failure (e : Zig.Error) : Observation :=
  {
    line := "{\"fail\":\"" ++ reprStr e ++ "\"}"
    kind := errorKind e }
/-- Partial schedule search needs a nonempty result type; this witness makes no
termination claim and uses the existing bounded no-result observation. -/
instance : Nonempty Observation := ⟨noResult⟩
end DiffOutcome
