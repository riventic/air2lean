import Lean
import Std.Data.HashMap
import Std.Data.HashSet

/-! Stable diagnostic vocabulary. Messages are display text, never classifiers. -/
namespace Air2Lean.Diagnostics
open Lean

inductive Code where
  | cliArguments | inputRead | inputLimit | jsonSyntax | airDecode
  | exporterUnsupported | optimizedUnsupported | canonicalFailure | normalizationFailure
  | structureFailure | typeFailure | globalFailure | memoryFailure | instructionFailure
  | constantFailure | signatureFailure | modelFailure | programFailure | profileFailure
  | duplicateFunction | calleeMissing | calleeBlocked | calleeAmbiguous | calleeExternUnbound
  | prerequisiteSkipped
  | volatileAccess | packedLayout | paddedAtomic | asmVolatileEffect
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
  | .calleeExternUnbound => "CALLEE_EXTERN_UNBOUND"
  | .prerequisiteSkipped => "PREREQUISITE_SKIPPED"
  | .volatileAccess => "VOLATILE_ACCESS"
  | .packedLayout => "PACKED_LAYOUT"
  | .paddedAtomic => "PADDED_ATOMIC"
  | .asmVolatileEffect => "ASM_VOLATILE_EFFECT"

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

/-- A Zig source location from the exporter's additive `src`/`column` provenance. `line` is
1-based and absolute; `column` is the 1-based column of the statement's `dbg_stmt`. -/
structure SourceSpan where
  file : String
  module : String
  line : Nat
  column : Option Nat := none
  /-- `statement`: the nearest preceding `dbg_stmt` of the instruction's inline scope;
  `declaration`: the function's declaration line (no statement location applies). -/
  granularity : String
  deriving BEq, Repr

def SourceSpan.toJson (s : SourceSpan) : Json := Json.mkObj [
  ("file", Lean.toJson s.file), ("module", Lean.toJson s.module),
  ("line", Lean.toJson s.line), ("column", Lean.toJson s.column)]

/-- One unit's resolvable locations, keyed by instruction ID in each ID space. -/
structure SpanIndex where
  declaration : Option SourceSpan := none
  exported : Std.HashMap Nat SourceSpan := {}
  canonical : Std.HashMap Nat SourceSpan := {}

def SpanIndex.resolve (index : SpanIndex) (anchor : Anchor) : Option SourceSpan :=
  match anchor.instruction, anchor.idSpace with
  | some id, .exported => index.exported[id]?
  | some id, .canonical => index.canonical[id]?
  | some _, .unavailable => none
  | none, _ => index.declaration

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
  /-- Fatal malformed input: inspection of this unit (or of the run) stopped here, and no
  later phase of it ran. Distinct from independent blockers, which never stop siblings. -/
  fatal : Bool := false
  span : Option SourceSpan := none
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
  ("source_span", (d.span.map SourceSpan.toJson).getD Json.null),
  ("source_span_status", Lean.toJson ((d.span.map (·.granularity)).getD "unavailable_in_AIR")),
  ("dependency_chain", Lean.toJson d.dependencyChain),
  ("dependency_scope", Lean.toJson "selected_normalized_direct_calls_and_spawn_workers"),
  ("prerequisites", Lean.toJson d.prerequisites), ("first_error_in_unit", Lean.toJson d.firstErrorInUnit),
  ("fatal", Lean.toJson d.fatal)]

def maxMessageChars : Nat := 2048
def maxPayloadBytes : Nat := 1024 * 1024

structure Log where
  limit : Nat := 256
  /-- Retained diagnostics per unit (input file), so one unit cannot exhaust the report. -/
  unitLimit : Nat := 64
  items : Array Diagnostic := #[]
  observed : Nat := 0
  failed : Bool := false
  complete : Bool := true
  truncated : Bool := false
  /-- The total count or payload bound is reached: no further diagnostic can be retained.
  A per-unit cap truncates only its unit and leaves siblings reportable. -/
  exhausted : Bool := false
  payloadBytes : Nat := 0
  /-- Retained and dropped diagnostic counts per unit. -/
  retained : Std.HashMap String Nat := {}
  dropped : Std.HashMap String Nat := {}
  /-- Registered unit locations; `add` attaches a span to diagnostics anchored in a unit. -/
  spans : Std.HashMap String SpanIndex := {}
  /-- Function and canonical instruction of every program-phase diagnostic, retained or
  dropped, so a later boundary can avoid reporting the same call site twice. -/
  programAnchors : Std.HashSet (String × Nat) := {}

def Log.add (log : Log) (d : Diagnostic) : Log :=
  let d := { d with
    message := (d.message.take maxMessageChars).toString
    messageTruncated := d.messageTruncated || decide (d.message.length > maxMessageChars)
    span := d.span <|> do
      let file ← d.file
      (← log.spans[file]?).resolve d.anchor }
  let log := { log with
    observed := log.observed + 1
    failed := log.failed || (d.category != .skipped)
    programAnchors := match d.phase, d.function, d.anchor.idSpace, d.anchor.instruction with
      | .program, some function, .canonical, some instruction => log.programAnchors.insert (function, instruction)
      | _, _, _, _ => log.programAnchors }
  let unit := d.file.getD ""
  let drop (log : Log) (exhausted : Bool) : Log :=
    { log with
      complete := false
      truncated := true
      exhausted := log.exhausted || exhausted
      dropped := log.dropped.insert unit (log.dropped.getD unit 0 + 1) }
  if log.items.size ≥ log.limit then drop log true
  else if log.retained.getD unit 0 ≥ log.unitLimit then drop log false
  else
    let bytes := d.toJson.compress.utf8ByteSize
    if log.payloadBytes + bytes > maxPayloadBytes then drop log true
    else
      { log with
        complete := log.complete && !d.firstErrorInUnit
        payloadBytes := log.payloadBytes + bytes
        retained := log.retained.insert unit (log.retained.getD unit 0 + 1)
        items := log.items.push d }

/-- Units that lost diagnostics to a cap, sorted by file. -/
def Log.cappedUnits (log : Log) : Array (String × Nat) :=
  log.dropped.toArray.qsort (fun a b => a.1 < b.1)

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
