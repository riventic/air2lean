/-!
# Dialect: the version and target facts of one translation

The translator's single registry of Zig versions (`ZigVersion`) and qualified targets
(`Target`), and the `Dialect` record that `Dialect.ofProfile` (`Air2Lean/Air/Profile.lean`)
derives from a validated `BuildProfile`: the Zig version, target, pointer width, byte order,
error width, backend and build mode of a program. `Normalize`, `Check`, `Emit` and the profile
validation ask the dialect (or one of the per-version facts below) instead of comparing version
strings or target names. `scripts/version-literals.py` rejects a Zig version literal anywhere else
in `Air2Lean/`, and checks this registry against `compatibility.json`.

To add a Zig version: add a constructor, its spelling in `ZigVersion.toString` and its place in
`ZigVersion.all`; every fact below is an exhaustive match, so Lean then lists each decision the
new version needs (`PLAN.md` §Zig version support).
-/

namespace Air2Lean

/-- A Zig compiler whose AIR the translator reads. -/
inductive ZigVersion where
  | v0_14_1 | v0_15_2 | v0_16_0 | v0_17_0
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace ZigVersion

/-- Every supported version, newest first (the order of `--help` and diagnostics). -/
def all : List ZigVersion := [.v0_17_0, .v0_16_0, .v0_15_2, .v0_14_1]

/-- The version as the exporter writes `zig_version`. -/
def toString : ZigVersion → String
  | v0_14_1 => "0.14.1"
  | v0_15_2 => "0.15.2"
  | v0_16_0 => "0.16.0"
  | v0_17_0 => "0.17.0"

instance : ToString ZigVersion := ⟨ZigVersion.toString⟩

/-- The supported version spelled `s`, if any. -/
def ofString? (s : String) : Option ZigVersion := all.find? (·.toString == s)

/-- `@bitCast` semantics (`docs/bitcast-semantics.md`, `Air2Lean/BitCast.lean`). -/
inductive BitCast where
  /-- Up to 0.16.0: a reinterpretation of the in-memory representation. -/
  | memory
  /-- From 0.17.0: the logical bit order (arrays and vectors element 0 lowest, no padding). -/
  | logical
  deriving DecidableEq, Repr, Inhabited

def bitCast : ZigVersion → BitCast
  | v0_14_1 | v0_15_2 | v0_16_0 => .memory
  | v0_17_0 => .logical

/-- The compiler_rt float routines whose results differ by version (`docs/floats.md`
§Per-version differences; `--float-semantics compiler-rt`). -/
inductive CompilerRt where
  /-- Before 0.16.0: the `f128` square root rounds through `f64`, a subnormal `f128` quotient
  flushes to zero, and the `f80` floor/ceil extension is the legacy one. -/
  | legacy
  /-- 0.16.0: the correctly rounded square root and the 0.16.0 quotient (`Float.divRt016`). -/
  | v016
  /-- 0.17.0: as 0.16.0, and `f80` `@trunc` keeps a pseudo-denormal (`Float.truncRt017Chk`). -/
  | v017
  deriving DecidableEq, Repr, Inhabited

def compilerRt : ZigVersion → CompilerRt
  | v0_14_1 | v0_15_2 => .legacy
  | v0_16_0 => .v016
  | v0_17_0 => .v017

/-- The AIR tag spelling (`Air2Lean/Air/Canon.lean`'s `versionTags`): 0.17.0 renamed and split
tags, which are read back in the 0.16.0 spelling. -/
inductive AirTags where
  | base
  | v017
  deriving DecidableEq, Repr, Inhabited

def airTags : ZigVersion → AirTags
  | v0_14_1 | v0_15_2 | v0_16_0 => .base
  | v0_17_0 => .v017

/-- The type `i0` exists (0.17.0 removed it; one in a 0.17.0 file is a malformed export). -/
def hasI0 : ZigVersion → Bool
  | v0_14_1 | v0_15_2 | v0_16_0 => true
  | v0_17_0 => false

/-- A generic function instance is named `<name>__func_<n>` (0.17.0) instead of
`<name>__anon_<n>` (`Air2Lean/Air/Anon.lean`'s `funcInstances017`). -/
def funcInstanceNames : ZigVersion → Bool
  | v0_14_1 | v0_15_2 | v0_16_0 => false
  | v0_17_0 => true

/-- The exporter's `build_mode` tags that name `std.builtin.OptimizeMode` differently: 0.17.0
renamed it `std.lang.Optimize` with the tags `debug`, `safe`, `fast`, `small`. Each pair is
(this version's tag, the 0.16.0 spelling). -/
def buildModeRenames : ZigVersion → List (String × String)
  | v0_14_1 | v0_15_2 | v0_16_0 => []
  | v0_17_0 => [("debug", "Debug"), ("safe", "ReleaseSafe"), ("fast", "ReleaseFast"), ("small", "ReleaseSmall")]

/-- Comptime lane pointers into bit-packed vectors have native evidence
(`tests/roadmap/vector-layouts`), so `normalize` models them as bit-pointers; 0.17.0 has none
yet. -/
def lanePtrEvidence : ZigVersion → Bool
  | v0_14_1 | v0_15_2 | v0_16_0 => true
  | v0_17_0 => false

/-- The versions with `lanePtrEvidence`, newest first. -/
def lanePtrVersions : List ZigVersion := all.filter (·.lanePtrEvidence)

/-- `Thread.spawn`'s `SpawnConfig` layout was audited for the fallible spawn policy
(`docs/spawn-failure.md`). -/
def spawnConfigAudited : ZigVersion → Bool
  | v0_14_1 | v0_15_2 | v0_16_0 | v0_17_0 => true

/-- `Io.Group` exists, and its caller fallback is audited for the fallible spawn policy. -/
def ioGroup : ZigVersion → Bool
  | v0_14_1 | v0_15_2 => false
  | v0_16_0 | v0_17_0 => true

end ZigVersion

/-- A byte order. -/
inductive Endian where
  | little | big
  deriving DecidableEq, Repr, Inhabited

/-- The spelling of `profile.endian` (`std.builtin.Endian`'s tag). -/
def Endian.toString : Endian → String
  | .little => "little"
  | .big => "big"

instance : ToString Endian := ⟨Endian.toString⟩

def Endian.ofString? : String → Option Endian
  | "little" => some .little
  | "big" => some .big
  | _ => none

/-- A target that the memory model admits: the architecture and OS components of the Zig
triple, with the pointer width and byte order the model takes for it (`docs/profiles.md`). -/
structure Target where
  arch : String
  os : String
  pointerBits : Nat
  endian : Endian
  deriving Repr, BEq

/-- The qualified targets: 64-bit little endian (`ZigLean/Mem`), 64-bit big endian
(`ZigLean/Endian.lean`) and 32-bit little endian (`ZigLean/Mem/Width.lean`). -/
def Target.qualified : List Target := [
  ⟨"x86_64", "linux", 64, .little⟩, ⟨"aarch64", "macos", 64, .little⟩,
  ⟨"s390x", "linux", 64, .big⟩,
  ⟨"wasm32", "freestanding", 32, .little⟩, ⟨"wasm32", "wasi", 32, .little⟩]

/-- The qualified target of an architecture and OS name, if any. -/
def Target.find? (arch os : String) : Option Target :=
  Target.qualified.find? fun t => t.arch == arch && t.os == os

/-- `x86_64-linux/aarch64-macos/…`, for diagnostics. -/
def Target.scope : String :=
  "/".intercalate (Target.qualified.map fun t => s!"{t.arch}-{t.os}")

/-- The LLVM code generator, whose layouts (bit-packed vector lanes, the big-endian bit-pointer
host) the model follows. -/
def Target.llvmBackend : String := "stage2_llvm"

/-- The facts of one translation, derived from its validated build profile
(`Dialect.ofProfile`). A legacy (schema < 12) profile has the unverified 64-bit little-endian
facts: no architecture, an `unverified` backend and build mode, 16-bit errors. -/
structure Dialect where
  version : ZigVersion
  /-- The target architecture (`x86_64`, `aarch64`, `s390x`, `wasm32`); empty for a legacy
  profile, whose reference model is x86_64 (`Air2Lean/AsmAllowlist.lean`). -/
  arch : String := ""
  /-- The pointer size in bytes (`Zig.PtrWidth.bytes`): 8, or 4 on wasm32. -/
  ptrBytes : Nat := 8
  endian : Endian := .little
  /-- `error_set_bits` (`--error-limit`): the width of every stored error code. -/
  errorSetBits : Nat := 16
  /-- The code generator (`stage2_llvm`, `stage2_x86_64`, …); `unverified` for a legacy profile. -/
  backend : String := "unverified"
  /-- The build mode in its 0.16.0 spelling (`Debug`, `ReleaseSafe`, …); `unverified` for a
  legacy profile. -/
  buildMode : String := "unverified"
  deriving Repr, Inhabited, BEq

namespace Dialect

/-- The dialect of a hand-built function: `version` with the legacy profile's facts. -/
def ofVersion (version : ZigVersion) : Dialect := { version }

def bigEndian (d : Dialect) : Bool := d.endian == .big

def ptrBits (d : Dialect) : Nat := d.ptrBytes * 8

def bitCast (d : Dialect) : ZigVersion.BitCast := d.version.bitCast

/-- Runtime safety checks are on (`Debug`, `ReleaseSafe`); `none` for an unverified build mode. -/
def safety (d : Dialect) : Option Bool :=
  match d.buildMode with
  | "Debug" | "ReleaseSafe" => some true
  | "ReleaseFast" | "ReleaseSmall" => some false
  | _ => none

/-- The backend bit-packs vector lanes in memory (`ZigLean/Vec.lean`'s `Vec.packedEnc`,
`tests/roadmap/vector-layouts`); other backends lay lanes out differently. -/
def packedVectorLanes (d : Dialect) : Bool := d.backend == Target.llvmBackend

/-- `normalize` makes a comptime lane pointer into a bit-packed vector a bit-pointer into the
vector's integer (`lanePtrLayout`): LLVM's layout, checked natively only on x86_64 and aarch64
and only for the versions with `ZigVersion.lanePtrEvidence`. -/
def lanePtrBitPtrs (d : Dialect) : Bool :=
  d.packedVectorLanes && d.version.lanePtrEvidence && ["x86_64", "aarch64"].contains d.arch

/-- The backends whose `lowerPtr` measures an `eu_payload` base with the error union type
instead of its payload: `codegen/llvm.zig` (Zig 0.14.1–0.17.0) and `codegen/wasm/CodeGen.zig`
(observed in 0.16.0). `Check.lean`'s `checkLlvmPayloadConstant` fails closed for them. -/
def euPayloadMisplacedBackends : List String := [Target.llvmBackend, "stage2_wasm"]

def misplacesEuPayload (d : Dialect) : Bool := euPayloadMisplacedBackends.contains d.backend

end Dialect

end Air2Lean
