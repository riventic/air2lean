import Lean

/-! Stable diagnostic vocabulary. Messages are display text, never classifiers. -/
namespace Air2Lean.Diagnostics
open Lean

inductive Code where
  | cliArguments | inputRead | inputLimit | jsonSyntax | airDecode
  | exporterUnsupported | optimizedUnsupported | canonicalFailure | normalizationFailure
  | structureFailure | typeFailure | globalFailure | memoryFailure | instructionFailure
  | constantFailure | signatureFailure | modelFailure | programFailure | profileFailure
  | duplicateFunction | calleeMissing | calleeBlocked | calleeAmbiguous | prerequisiteSkipped
  deriving BEq, Repr

def Code.text : Code → String
  | .cliArguments => "CLI_ARGUMENTS"
  | .inputRead => "INPUT_READ"
  | .inputLimit => "INPUT_LIMIT"
  | .jsonSyntax => "JSON_SYNTAX"
  | .airDecode => "AIR_DECODE"
  | .exporterUnsupported => "EXPORTER_UNSUPPORTED"
  | .optimizedUnsupported => "OPTIMIZED_UNSUPPORTED"
  | .canonicalFailure => "CANONICAL_FAILURE"
  | .normalizationFailure => "NORMALIZATION_FAILURE"
  | .structureFailure => "STRUCTURE_FAILURE"
  | .typeFailure => "TYPE_FAILURE"
  | .globalFailure => "GLOBAL_FAILURE"
  | .memoryFailure => "MEMORY_FAILURE"
  | .instructionFailure => "INSTRUCTION_FAILURE"
  | .constantFailure => "CONSTANT_FAILURE"
  | .signatureFailure => "SIGNATURE_FAILURE"
  | .modelFailure => "MODEL_FAILURE"
  | .programFailure => "PROGRAM_FAILURE"
  | .profileFailure => "PROFILE_FAILURE"
  | .duplicateFunction => "DUPLICATE_FUNCTION"
  | .calleeMissing => "CALLEE_MISSING"
  | .calleeBlocked => "CALLEE_BLOCKED"
  | .calleeAmbiguous => "CALLEE_AMBIGUOUS"
  | .prerequisiteSkipped => "PREREQUISITE_SKIPPED"

inductive Phase where
  | cli | input | decode | canonicalize | normalize | check | program | profile
  deriving BEq, Repr
def Phase.text : Phase → String
  | .cli => "cli" | .input => "input" | .decode => "decode"
  | .canonicalize => "canonicalize" | .normalize => "normalize"
  | .check => "check" | .program => "program" | .profile => "profile"

inductive Category where
  | malformedInput | unsupportedSemantics | validationFailure | resourceLimit | ioFailure | skipped
  deriving BEq, Repr
def Category.text : Category → String
  | .malformedInput => "malformed_input"
  | .unsupportedSemantics => "unsupported_semantics"
  | .validationFailure => "validation_failure"
  | .resourceLimit => "resource_limit"
  | .ioFailure => "io_failure"
  | .skipped => "skipped_prerequisite"

inductive IdSpace where
  | unavailable | exported | canonical
  deriving BEq, Repr
def IdSpace.text : IdSpace → String
  | .unavailable => "unavailable" | .exported => "exported" | .canonical => "canonical"

structure Anchor where
  idSpace : IdSpace := .unavailable
  instruction : Option Nat := none
  typeId : Option Nat := none
  globalId : Option Nat := none
  nearestDbgLine : Option Nat := none
  deriving Repr

structure Diagnostic where
  code : Code
  phase : Phase
  category : Category
  message : String
  messageTruncated : Bool := false
  file : Option String := none
  function : Option String := none
  anchor : Anchor := {}
  dependencyChain : Array String := #[]
  prerequisites : Array String := #[]
  /-- A legacy validation boundary can retain its first error; disclose that loss. -/
  firstErrorInUnit : Bool := false
  deriving Repr

/-- Convert an existing validator at a known boundary, without interpreting its text. -/
def capture (context : Diagnostic) (result : Except String α) : Except Diagnostic α :=
  result.mapError fun message => { context with message, firstErrorInUnit := true }

/-- Compatibility rendering preserves the original validator message. -/
def Diagnostic.render (d : Diagnostic) : String := d.message

def Diagnostic.toJson (d : Diagnostic) : Json := Json.mkObj [
  ("code", Lean.toJson d.code.text), ("phase", Lean.toJson d.phase.text),
  ("category", Lean.toJson d.category.text), ("message", Lean.toJson (d.message.take 2048).toString),
  ("message_truncated", Lean.toJson (d.messageTruncated || decide (d.message.length > 2048))),
  ("file", Lean.toJson d.file), ("function", Lean.toJson d.function),
  ("anchor", Json.mkObj [("id_space", Lean.toJson d.anchor.idSpace.text),
    ("instruction", Lean.toJson d.anchor.instruction), ("type", Lean.toJson d.anchor.typeId),
    ("global", Lean.toJson d.anchor.globalId), ("nearest_dbg_line", Lean.toJson d.anchor.nearestDbgLine)]),
  ("source_span", Json.null), ("source_span_status", Lean.toJson "unavailable_in_AIR"),
  ("dependency_chain", Lean.toJson d.dependencyChain),
  ("dependency_scope", Lean.toJson "selected_normalized_direct_calls_and_spawn_workers"),
  ("prerequisites", Lean.toJson d.prerequisites), ("first_error_in_unit", Lean.toJson d.firstErrorInUnit)]

structure Log where
  limit : Nat := 256
  items : Array Diagnostic := #[]
  observed : Nat := 0
  failed : Bool := false
  complete : Bool := true
  truncated : Bool := false
  payloadBytes : Nat := 0

def Log.add (log : Log) (d : Diagnostic) : Log :=
  let d := { d with message := (d.message.take 2048).toString,
    messageTruncated := d.messageTruncated || decide (d.message.length > 2048) }
  if log.items.size ≥ log.limit then
    { log with observed := log.observed + 1, failed := log.failed || (d.category != .skipped),
      complete := false, truncated := true }
  else
    let bytes := d.toJson.compress.utf8ByteSize
    let fits := log.payloadBytes + bytes ≤ 1024 * 1024
    { log with
      observed := log.observed + 1
      failed := log.failed || (d.category != .skipped)
      complete := log.complete && !d.firstErrorInUnit && fits
      truncated := log.truncated || !fits
      payloadBytes := if fits then log.payloadBytes + bytes else log.payloadBytes
      items := if fits then log.items.push d else log.items }

def Log.record (log : Log) (d : Diagnostic) (result : Except String α) : Log :=
  match capture d result with
  | .ok _ => log
  | .error diagnostic => log.add diagnostic

def skipped (file : String) (function : Option String) (phase : Phase)
    (prerequisite : String) : Diagnostic :=
  { code := .prerequisiteSkipped, phase, category := .skipped,
    message := "not inspected: prerequisite failed", file := some file, function,
    prerequisites := #[prerequisite], firstErrorInUnit := true }

end Air2Lean.Diagnostics
