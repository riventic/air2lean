import Lean.Data.Json
import Std.Data.HashSet

/-! Target/build metadata is an input contract, not a binary correspondence theorem.
Admitted: the little-endian memory model with 64-bit pointers (x86_64-linux, aarch64-macos) or
32-bit pointers (wasm32-freestanding, wasm32-wasi; `ZigLean/Mem/Width.lean`), and the 64-bit
big-endian model (s390x-linux; `ZigLean/Endian.lean`). Schema 12 makes the facts mandatory;
schemas 1–11 retain the explicitly named, unverified legacy 64-bit little-endian profile. -/
namespace Air2Lean

open Lean (Json)

structure BuildProfile where
  name : String
  schema : Nat
  zigVersion : String
  targetTriple : String := "unverified"
  pointerBits : Nat := 64
  endian : String := "little"
  abi : String := "unverified"
  backend : String := "unverified"
  cpu : String := "unverified"
  features : Array String := #[]
  buildMode : String := "unverified"
  floatMode : String := "unverified"
  errorSetBits : Nat := 16
  errorLayout : String := "reference-model"
  errorTracing : Option Bool := none
  exportStage : String := "unverified"
  deriving BEq, Repr

namespace BuildProfile

/-- The value of every profile field that a schema 1–11 file leaves unnamed. -/
def unverified : String := "unverified"
def legacyName : String := "legacy-abi64-le"
def currentName : String := "abi64-le-v1"
/-- The big-endian model profile (T03). The exporter writes `currentName` as the raw
`profile.name` of every target; the translator names a qualified big-endian profile by its byte
order, so a generated header and `--profile` distinguish the two models. -/
def bigEndianName : String := "abi64-be-v1"

/-- The profile's byte order is big endian (`profile.endian`). -/
def isBigEndian (p : BuildProfile) : Bool := p.endian == "big"

private def strField (j : Json) (k : String) : Except String String := do
  let v ← ((j.getObjVal? k).bind Json.getStr?).mapError fun e => s!"profile.{k}: {e}"
  unless !v.isEmpty do throw s!"profile.{k}: must not be empty"
  pure v

private def natField (j : Json) (k : String) : Except String Nat :=
  ((j.getObjVal? k).bind Json.getNat?).mapError fun e => s!"profile.{k}: {e}"

/-- The build mode in its 0.16.0 spelling. Zig 0.17.0 renamed `std.builtin.OptimizeMode` to
`std.lang.Optimize` with the tags `debug`, `safe`, `fast`, `small`; the exporter writes the tag
name. A 0.17.0 profile may carry either spelling, older ones only their own, and the parsed
profile always holds the 0.16.0 spelling. -/
def canonicalBuildMode (zigVersion mode : String) : Except String String :=
  let renamed := if zigVersion == "0.17.0" then
      [("debug", "Debug"), ("safe", "ReleaseSafe"), ("fast", "ReleaseFast"), ("small", "ReleaseSmall")].lookup mode
    else none
  match renamed with
  | some m => pure m
  | none =>
    if ["Debug", "ReleaseSafe", "ReleaseFast", "ReleaseSmall"].contains mode then pure mode
    else throw s!"unsupported profile.build_mode '{mode}'"

private abbrev Collect := StateM (Array String)

private def report (message : String) : Collect Unit := modify (·.push message)

/-- The value of a check, or `none` after recording its error. -/
private def take? (result : Except String α) : Collect (Option α) :=
  match result with
  | .ok value => pure (some value)
  | .error message => do report message; pure none

/-- Central fail-closed schema policy, collecting every independent violation in the order
`parse` reports them; a check that needs a failed field is skipped. Legacy schemas cannot
carry a schema-12 profile. An unsupported schema or a missing/non-object `profile` is
structural: it yields no profile. Otherwise invalid fields keep their legacy defaults, so the
returned profile is a best-effort placeholder whenever any violation was recorded. -/
def collect (j : Json) (schema : Nat) (zigVersion : String) : Collect (Option BuildProfile) := do
  unless 1 ≤ schema && schema ≤ 12 do
    report s!"unsupported AIR schema {schema} (supported: 1–12)"
    return none
  if let .ok endian := j.getObjVal? "target_endian" then
    if let some endian ← take? endian.getStr? then
      -- Big endian needs a schema-12 profile of a qualified big-endian target (below).
      unless endian == "little" || (endian == "big" && schema == 12) do
        report s!"target_endian '{endian}' is outside the little-endian memory model"
  if schema < 12 then
    if (j.getObjVal? "profile").toOption.isSome then
      report "profile metadata requires AIR schema 12"
      return none
    return some { name := legacyName, schema, zigVersion }
  let some p ← take? ((j.getObjVal? "profile").mapError fun _ => "schema 12 requires 'profile' metadata")
    | return none
  let some fields ← take? (p.getObj? |>.mapError fun e => s!"profile: {e}") | return none
  let allowed := ["name", "target_triple", "pointer_bits", "endian", "abi", "zig_version",
    "backend", "cpu", "features", "build_mode", "float_mode", "error_set_bits",
    "error_layout", "error_tracing", "export_stage"]
  for (key, _) in fields.toArray do
    unless allowed.contains key do report s!"unsupported profile field '{key}'"
  let name ← take? (strField p "name")
  if let some name := name then
    unless name == currentName do report s!"unsupported profile '{name}' (want '{currentName}')"
  let targetTriple ← take? (strField p "target_triple")
  let pointerBits ← take? (natField p "pointer_bits")
  if let some pointerBits := pointerBits then
    unless pointerBits == 64 || pointerBits == 32 do
      report s!"profile.pointer_bits {pointerBits} is outside the 32/64-bit memory model"
  let endian ← take? (strField p "endian")
  if let some endian := endian then
    unless endian == "little" || endian == "big" do
      report s!"profile.endian '{endian}' is outside the little/big-endian memory model"
  let abi ← take? (strField p "abi")
  if let some triple := targetTriple then
    -- Zig triples have arch-os-abi components (version suffixes are permitted).
    match triple.splitOn "-" with
    | [arch, os, tripleAbi] =>
      if let some abi := abi then
        unless !arch.isEmpty && !os.isEmpty && (tripleAbi.splitOn ".").head! == abi do
          report "profile.target_triple: empty component or ABI differs from profile.abi"
      let osName := (os.splitOn ".").head!
      let native := (arch == "x86_64" && osName == "linux") || (arch == "aarch64" && osName == "macos")
      let wasm := arch == "wasm32" && (osName == "freestanding" || osName == "wasi")
      let big := arch == "s390x" && osName == "linux"
      if !(native || wasm || big) then
        report "profile.target_triple: outside the x86_64-linux/aarch64-macos/s390x-linux/wasm32-freestanding/wasm32-wasi model ABI scope"
      else
        if let some pointerBits := pointerBits then
          unless pointerBits == (if wasm then 32 else 64) do
            report s!"profile.pointer_bits {pointerBits} differs from the {arch} target's \
              {if wasm then 32 else 64}-bit pointer width"
        let targetEndian := if big then "big" else "little"
        if let some endian := endian then
          unless endian == targetEndian do
            report s!"profile.endian '{endian}' differs from the {arch} target's {targetEndian}-endian byte order"
    | _ => report "profile.target_triple: expected arch-os-abi"
  if let (.ok te, some endian) := (j.getObjVal? "target_endian", endian) then
    unless (match te.getStr? with | .ok s => s == endian | .error _ => false) do
      report "target_endian differs from profile.endian"
  if let some profileVersion ← take? (strField p "zig_version") then
    unless profileVersion == zigVersion do
      report "profile.zig_version differs from top-level zig_version"
  let backend ← take? (strField p "backend")
  -- The big-endian bit-pointer host is the `(bits + 7) / 8`-byte integer of the LLVM backend
  -- (`Zig.loadBitsOf`), and its vector lanes are LLVM's; no other backend targets s390x.
  if let (some "big", some backend) := (endian, backend) then
    unless backend == "stage2_llvm" do
      report s!"profile.backend '{backend}' is outside the big-endian model (stage2_llvm only)"
  let cpu ← take? (strField p "cpu")
  let features ← take? do
    let fs ← ((p.getObjVal? "features").bind Json.getArr?).mapError fun e => s!"profile.features: {e}"
    fs.mapM fun f => f.getStr? |>.mapError fun e => s!"profile.features: {e}"
  let mut seen : Std.HashSet String := {}
  for f in features.getD #[] do
    unless !f.isEmpty && !seen.contains f do report "profile.features: empty or duplicate feature"
    seen := seen.insert f
  let buildMode ← take? (do canonicalBuildMode zigVersion (← strField p "build_mode"))
  let floatMode ← take? (strField p "float_mode")
  if let some floatMode := floatMode then
    unless floatMode == "per-instruction" do
      report "profile.float_mode: expected 'per-instruction'; optimized AIR remains unsupported"
  -- `Zcu.errorSetBits`: `log2(--error-limit) + 1` (16 by default), 0 for `--error-limit 0`.
  -- The error model is parameterized by this width (`ZigLean/Mem/ErrWidth.lean`); only the
  -- default 16 bits has native evidence (`docs/profiles.md` §Error-code width).
  let errorSetBits ← take? (natField p "error_set_bits")
  if let some errorSetBits := errorSetBits then
    unless 0 < errorSetBits && errorSetBits ≤ 32 do
      report s!"profile.error_set_bits {errorSetBits} is outside the 1..32-bit error model \
        (`--error-limit 0` has no error storage; the error integer is at most u32)"
  let errorLayout ← take? (strField p "error_layout")
  if let some errorLayout := errorLayout then
    unless errorLayout == "type-table" do report "profile.error_layout: expected 'type-table'"
  let errorTracing ← take? (((p.getObjVal? "error_tracing").bind Json.getBool?).mapError
    fun e => s!"profile.error_tracing: {e}")
  let exportStage ← take? (strField p "export_stage")
  if let some exportStage := exportStage then
    unless exportStage == "analyzed-air" do
      report "profile.export_stage: only 'analyzed-air' is supported; binary correspondence is unqualified"
  let base : BuildProfile := { name := legacyName, schema, zigVersion }
  return some {
    name := if endian == some "big" then bigEndianName else name.getD base.name
    schema
    zigVersion
    targetTriple := targetTriple.getD base.targetTriple
    pointerBits := pointerBits.getD base.pointerBits
    endian := endian.getD base.endian
    abi := abi.getD base.abi
    backend := backend.getD base.backend
    cpu := cpu.getD base.cpu
    features := features.getD base.features
    buildMode := buildMode.getD base.buildMode
    floatMode := floatMode.getD base.floatMode
    errorSetBits := errorSetBits.getD base.errorSetBits
    errorLayout := errorLayout.getD base.errorLayout
    errorTracing
    exportStage := exportStage.getD base.exportStage
  }

/-- Fail-fast form of `collect`: its first violation. -/
def parse (j : Json) (schema : Nat) (zigVersion : String) : Except String BuildProfile :=
  match (collect j schema zigVersion).run #[] with
  | (some p, #[]) => .ok p
  | (_, errors) => .error (errors[0]?.getD "invalid profile metadata")

/-- Serialized in generated source and proof reports. Legacy assumptions remain explicit. -/
def toJson (p : BuildProfile) : Json :=
  Json.mkObj [("name", .str p.name), ("schema", Lean.toJson p.schema),
    ("zig_version", .str p.zigVersion), ("target_triple", .str p.targetTriple),
    ("pointer_bits", Lean.toJson p.pointerBits), ("endian", .str p.endian),
    ("abi", .str p.abi), ("backend", .str p.backend), ("cpu", .str p.cpu),
    ("features", .arr (p.features.map Json.str)), ("build_mode", .str p.buildMode),
    ("float_mode", .str p.floatMode), ("error_set_bits", Lean.toJson p.errorSetBits),
    ("error_layout", .str p.errorLayout), ("error_tracing", Lean.toJson p.errorTracing), ("export_stage", .str p.exportStage)]

/-- The (build mode, backend) pairs that `assurance/build-modes.json` qualifies. -/
def qualifiedBuilds : List (String × String) := [("ReleaseSafe", "stage2_llvm")]

def qualified (p : BuildProfile) : Bool := qualifiedBuilds.contains (p.buildMode, p.backend)

/-- Admission (deny by default): a legacy profile needs `--profile legacy-abi64-le`, and a
current profile (either byte order) outside `qualifiedBuilds` needs
`--allow-unqualified-build-mode`, which the generated header records (`Air2Lean/Main.lean`). -/
def admit (p : BuildProfile) (expected : Option String) (allowUnqualified : Bool) :
    Except String Unit := do
  if p.name == legacyName && expected != some legacyName then
    throw s!"AIR schema {p.schema} has no target profile: translating it assumes an \
      unverified 64-bit little-endian ABI; pass --profile {legacyName} to accept that \
      assumption explicitly (docs/profiles.md)"
  if p.name != legacyName && !p.qualified && !allowUnqualified then
    throw s!"build mode {p.buildMode} with backend {p.backend} is not qualified \
      (docs/build-modes.md); only {qualifiedBuilds} AIR is translated by default. \
      Pass --allow-unqualified-build-mode to translate it anyway; the generated header \
      records the opt-in"

/-- Exact agreement includes schema, Zig version, CPU feature order, and all build facts.
Every differing field of every profile is a separate violation, after a selected-name
mismatch; the agreed (first) profile must then pass `admit`. Their order matches the fail-fast
`checkProgram`. -/
def programViolations (profiles : Array BuildProfile) (expected : Option String := none)
    (allowUnqualified : Bool := false) : Array String := Id.run do
  let some first := profiles[0]? | return #["no AIR profiles supplied"]
  let mut errors := #[]
  if let some expected := expected then
    unless first.name == expected do
      errors := errors.push s!"selected profile '{expected}' differs from input profile '{first.name}'"
  let fields := (first.toJson.getObj?).toOption.getD {}
  for p in profiles do
    unless p == first do
      let current := p.toJson
      for (key, value) in fields.toArray do
        let other := current.getObjValD key
        unless value == other do
          errors := errors.push s!"mixed AIR profiles: field '{key}' differs ({value.compress} vs {other.compress})"
  if let .error e := admit first expected allowUnqualified then errors := errors.push e
  return errors

def checkProgram (profiles : Array BuildProfile) (expected : Option String := none)
    (allowUnqualified : Bool := false) : Except String BuildProfile := do
  let some first := profiles[0]? | throw "no AIR profiles supplied"
  if let some error := (programViolations profiles expected allowUnqualified)[0]? then throw error
  pure first

end BuildProfile
end Air2Lean
