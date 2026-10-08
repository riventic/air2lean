import Lean.Data.Json
import Std.Data.HashSet

/-! Target/build metadata is an input contract, not a binary correspondence theorem.
Only the existing 64-bit little-endian memory model is admitted. Schema 12 makes the
facts mandatory; schemas 1–11 retain the explicitly named, unverified legacy profile. -/
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

def legacyName : String := "legacy-abi64-le"
def currentName : String := "abi64-le-v1"

private def strField (j : Json) (k : String) : Except String String := do
  let v ← ((j.getObjVal? k).bind Json.getStr?).mapError fun e => s!"profile.{k}: {e}"
  unless !v.isEmpty do throw s!"profile.{k}: must not be empty"
  pure v

private def natField (j : Json) (k : String) : Except String Nat :=
  ((j.getObjVal? k).bind Json.getNat?).mapError fun e => s!"profile.{k}: {e}"

/-- Central fail-closed schema policy. Legacy schemas cannot carry a schema-12 profile. -/
def parse (j : Json) (schema : Nat) (zigVersion : String) : Except String BuildProfile := do
  unless 1 ≤ schema && schema ≤ 12 do
    throw s!"unsupported AIR schema {schema} (supported: 1–12)"
  if let .ok endian := j.getObjVal? "target_endian" then
    let endian ← endian.getStr?
    unless endian == "little" do
      throw s!"target_endian '{endian}' is outside the little-endian memory model"
  if schema < 12 then
    if (j.getObjVal? "profile").toOption.isSome then
      throw "profile metadata requires AIR schema 12"
    return { name := legacyName, schema, zigVersion }
  let p ← (j.getObjVal? "profile").mapError fun _ => "schema 12 requires 'profile' metadata"
  let fields ← p.getObj? |>.mapError fun e => s!"profile: {e}"
  let allowed := ["name", "target_triple", "pointer_bits", "endian", "abi", "zig_version",
    "backend", "cpu", "features", "build_mode", "float_mode", "error_set_bits",
    "error_layout", "error_tracing", "export_stage"]
  for (key, _) in fields.toArray do
    unless allowed.contains key do throw s!"unsupported profile field '{key}'"
  let name ← strField p "name"
  unless name == currentName do throw s!"unsupported profile '{name}' (want '{currentName}')"
  let targetTriple ← strField p "target_triple"
  let pointerBits ← natField p "pointer_bits"
  unless pointerBits == 64 do
    throw s!"profile.pointer_bits {pointerBits} is outside the 64-bit memory model"
  let endian ← strField p "endian"
  unless endian == "little" do
    throw s!"profile.endian '{endian}' is outside the little-endian memory model"
  let abi ← strField p "abi"
  -- Zig triples have arch-os-abi components (version suffixes are permitted).
  let [arch, os, tripleAbi] := targetTriple.splitOn "-"
    | throw "profile.target_triple: expected arch-os-abi"
  unless !arch.isEmpty && !os.isEmpty && (tripleAbi.splitOn ".").head! == abi do
    throw "profile.target_triple: empty component or ABI differs from profile.abi"
  let osName := (os.splitOn ".").head!
  unless (arch == "x86_64" && osName == "linux") ||
      (arch == "aarch64" && osName == "macos") do
    throw "profile.target_triple: outside the x86_64-linux/aarch64-macos model ABI scope"
  let profileVersion ← strField p "zig_version"
  unless profileVersion == zigVersion do
    throw "profile.zig_version differs from top-level zig_version"
  let backend ← strField p "backend"
  let cpu ← strField p "cpu"
  let fs ← ((p.getObjVal? "features").bind Json.getArr?).mapError fun e => s!"profile.features: {e}"
  let features ← fs.mapM fun f => f.getStr? |>.mapError fun e => s!"profile.features: {e}"
  let mut seen : Std.HashSet String := {}
  for f in features do
    unless !f.isEmpty && !seen.contains f do throw "profile.features: empty or duplicate feature"
    seen := seen.insert f
  let buildMode ← strField p "build_mode"
  unless ["Debug", "ReleaseSafe", "ReleaseFast", "ReleaseSmall"].contains buildMode do
    throw s!"unsupported profile.build_mode '{buildMode}'"
  let floatMode ← strField p "float_mode"
  unless floatMode == "per-instruction" do
    throw "profile.float_mode: expected 'per-instruction'; optimized AIR remains unsupported"
  -- `Zcu.errorSetBits`: `log2(--error-limit) + 1` (16 by default), 0 for `--error-limit 0`.
  -- The error model is parameterized by this width (`ZigLean/Mem/ErrWidth.lean`); only the
  -- default 16 bits has native evidence (`docs/profiles.md` §Error-code width).
  let errorSetBits ← natField p "error_set_bits"
  unless 0 < errorSetBits && errorSetBits ≤ 32 do
    throw s!"profile.error_set_bits {errorSetBits} is outside the 1..32-bit error model \
      (`--error-limit 0` has no error storage; the error integer is at most u32)"
  let errorLayout ← strField p "error_layout"
  unless errorLayout == "type-table" do throw "profile.error_layout: expected 'type-table'"
  let tracing ← ((p.getObjVal? "error_tracing").bind Json.getBool?).mapError
    fun e => s!"profile.error_tracing: {e}"
  let errorTracing := some tracing
  let exportStage ← strField p "export_stage"
  unless exportStage == "analyzed-air" do
    throw "profile.export_stage: only 'analyzed-air' is supported; binary correspondence is unqualified"
  return {
    name
    schema
    zigVersion
    targetTriple
    pointerBits
    endian
    abi
    backend
    cpu
    features
    buildMode
    floatMode
    errorSetBits
    errorLayout
    errorTracing
    exportStage
  }

/-- Serialized in generated source and proof reports. Legacy assumptions remain explicit. -/
def toJson (p : BuildProfile) : Json :=
  Json.mkObj [("name", .str p.name), ("schema", Lean.toJson p.schema),
    ("zig_version", .str p.zigVersion), ("target_triple", .str p.targetTriple),
    ("pointer_bits", Lean.toJson p.pointerBits), ("endian", .str p.endian),
    ("abi", .str p.abi), ("backend", .str p.backend), ("cpu", .str p.cpu),
    ("features", .arr (p.features.map Json.str)), ("build_mode", .str p.buildMode),
    ("float_mode", .str p.floatMode), ("error_set_bits", Lean.toJson p.errorSetBits),
    ("error_layout", .str p.errorLayout), ("error_tracing", Lean.toJson p.errorTracing), ("export_stage", .str p.exportStage)]

/-- Exact agreement includes schema, Zig version, CPU feature order, and all build facts. -/
def checkProgram (profiles : Array BuildProfile) (expected : Option String := none) :
    Except String BuildProfile := do
  let some first := profiles[0]? | throw "no AIR profiles supplied"
  if let some expected := expected then
    unless first.name == expected do
      throw s!"selected profile '{expected}' differs from input profile '{first.name}'"
  for p in profiles do
    unless p == first do
      let fields ← first.toJson.getObj?
      let current := p.toJson
      for (key, value) in fields.toArray do
        let other := current.getObjValD key
        unless value == other do
          throw s!"mixed AIR profiles: field '{key}' differs ({value.compress} vs {other.compress})"
  pure first

end BuildProfile
end Air2Lean
