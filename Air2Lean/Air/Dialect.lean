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

/-- The error for a `zig_version` outside `all`. -/
def unsupported (s : String) : String :=
  s!"unsupported zig_version '{s}' (supported: {", ".intercalate (all.map toString)})"

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

/-- How a target lowers the float ops whose lowering differs between targets (`docs/floats.md`
§Targets), at its baseline CPU (`-mcpu=baseline`, the CPU of the native differential test). -/
inductive FloatRules where
  /-- The reference (x86_64-linux): `f80` on the x87 and `@mulAdd` through compiler_rt (no FMA
  instruction). The targets without rules of their own (s390x, wasm32) keep it. -/
  | reference
  /-- aarch64 (premise MTH-04): soft-float `f80` (`Zig.Float.softF80Chk`; `__divxf3`; before
  0.16.0, `@sqrt` through `f64`) and the fused `fmadd` for `@mulAdd` on `f32`/`f64`. With
  `fusedF16` (`fullfp16` in the baseline CPU: aarch64-macos `apple_m1`) also on `f16`; without
  it (aarch64-linux `generic`) LLVM promotes an `f16` `@mulAdd` to an `f32` `fmadd` and rounds
  back, the reference rule. -/
  | aarch64 (fusedF16 : Bool)
  deriving DecidableEq, Repr, Inhabited

/-- A target that the memory model admits: the architecture and OS components of the Zig
triple, with the ABI facts that the model takes for it (`docs/profiles.md`). Integer and float
sizes and alignments are the same on every qualified target (`Zig.intSize`/`Zig.intAlign`;
`f80` and `f128` are 16/16); the exporter writes `c_longdouble` as the float of
`longDoubleBits` bits. -/
structure Target where
  arch : String
  os : String
  pointerBits : Nat
  endian : Endian
  /-- `c_longdouble` (Zig's `cTypeBitSize(.longdouble)`). -/
  longDoubleBits : Nat
  floatRules : FloatRules := .reference
  /-- The widest atomic integer in bits (Zig's `max_atomic_bits` at the baseline CPU: x86_64
  has no `cx16`). The checker rejects a wider one. -/
  atomicBits : Nat
  /-- The Zig versions whose AIR is accepted for this target. aarch64-linux: those with a native
  probe record (`tests/roadmap/aarch64-abi/expected/<version>/`, `docs/aarch64-abi.md`). -/
  versions : List ZigVersion := ZigVersion.all
  /-- The accepted ABI components of the triple; empty: any. -/
  abis : List String := []
  deriving Repr, BEq

/-- The qualified targets: 64-bit little endian (`ZigLean/Mem`), 64-bit big endian
(`ZigLean/Endian.lean`) and 32-bit little endian (`ZigLean/Mem/Width.lean`). s390x and wasm32
reject every atomic op (`Check.lean`). The two aarch64 targets are qualified separately
(`docs/aarch64-abi.md`). -/
def Target.qualified : List Target := [
  { arch := "x86_64", os := "linux", pointerBits := 64, endian := .little, longDoubleBits := 80,
    atomicBits := 64 },
  { arch := "aarch64", os := "macos", pointerBits := 64, endian := .little, longDoubleBits := 64,
    floatRules := .aarch64 (fusedF16 := true), atomicBits := 128 },
  { arch := "aarch64", os := "linux", pointerBits := 64, endian := .little, longDoubleBits := 128,
    floatRules := .aarch64 (fusedF16 := false), atomicBits := 128,
    versions := [.v0_16_0, .v0_15_2, .v0_14_1], abis := ["gnu"] },
  { arch := "s390x", os := "linux", pointerBits := 64, endian := .big, longDoubleBits := 128,
    atomicBits := 64 },
  { arch := "wasm32", os := "freestanding", pointerBits := 32, endian := .little,
    longDoubleBits := 128, atomicBits := 32 },
  { arch := "wasm32", os := "wasi", pointerBits := 32, endian := .little, longDoubleBits := 128,
    atomicBits := 32 }]

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
  /-- The target OS (`linux`, `macos`, …); empty for a legacy profile. -/
  os : String := ""
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
  /-- `--assume-no-libc`: the program is linked without libc, so the `long double` libm routines
  of a target whose `c_longdouble` is `f128` (`sqrtl`, `fmal`, `floorl`, …) are compiler_rt's.
  The AIR profile records no `link_libc` fact; without this opt-in the checker rejects the `f128`
  ops that call them (`docs/floats.md` §Targets). -/
  noLibc : Bool := false
  deriving Repr, Inhabited, BEq

namespace Dialect

/-- The dialect of a hand-built function: `version` with the legacy profile's facts. -/
def ofVersion (version : ZigVersion) : Dialect := { version }

def bigEndian (d : Dialect) : Bool := d.endian == .big

def bitCast (d : Dialect) : ZigVersion.BitCast := d.version.bitCast

/-- The qualified target; `none` for a legacy profile (the x86_64 reference model). -/
def target? (d : Dialect) : Option Target := Target.find? d.arch d.os

/-- The target's float rules; the reference for a legacy profile. -/
def floatRules (d : Dialect) : FloatRules := (d.target?.map (·.floatRules)).getD .reference

/-- The backend bit-packs vector lanes in memory (`ZigLean/Vec.lean`'s `Vec.packedEnc`,
`tests/roadmap/vector-layouts`); other backends lay lanes out differently. -/
def packedVectorLanes (d : Dialect) : Bool := d.backend == Target.llvmBackend

/-- The architectures with native lane-pointer evidence (`tests/roadmap/vector-layouts`). -/
def lanePtrArchs : List String := ["x86_64", "aarch64"]

/-- `normalize` makes a comptime lane pointer into a bit-packed vector a bit-pointer into the
vector's integer (`lanePtrLayout`): LLVM's layout, checked natively only on `lanePtrArchs`
and only for the versions with `ZigVersion.lanePtrEvidence`. -/
def lanePtrBitPtrs (d : Dialect) : Bool :=
  d.packedVectorLanes && d.version.lanePtrEvidence && lanePtrArchs.contains d.arch

/-- The backends whose `lowerPtr` measures an `eu_payload` base with the error union type
instead of its payload: `codegen/llvm.zig` (Zig 0.14.1–0.17.0) and `codegen/wasm/CodeGen.zig`
(observed in 0.16.0). `Check.lean`'s `checkLlvmPayloadConstant` fails closed for them. -/
def euPayloadMisplacedBackends : List String := [Target.llvmBackend, "stage2_wasm"]

def misplacesEuPayload (d : Dialect) : Bool := euPayloadMisplacedBackends.contains d.backend

end Dialect

end Air2Lean
