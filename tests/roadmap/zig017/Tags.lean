import Air2Lean.Air.Normalize
import ZigLean

/-! Zig 0.17.0 tag-table and `@divCeil` regressions. Run: `lake env lean --run
tests/roadmap/zig017/Tags.lean`. Synthetic checks against the 0.16.0/0.17.0 `src/Air.zig` tag
delta (`docs/zig-0.17-delta.md` §(a)); not compiler output. -/
open Air2Lean Air2Lean.Raw

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

/-- `src/Air.zig` `Inst.Tag`: 0.17.0 members absent from 0.16.0, and the reverse. -/
private def added017 : List String :=
  ["div_ceil", "div_ceil_optimized", "bit_cast", "bit_cast_safe", "ptr_cast", "ptr_from_int",
   "int_from_ptr", "error_cast", "error_from_int", "int_from_error", "union_from_enum", "int_cast",
   "int_cast_safe", "agg_field_val", "array_to_vector", "spirv_runtime_array_len"]
private def removed017 : List String :=
  ["bitcast", "bool_and", "bool_or", "intcast", "intcast_safe", "struct_field_val"]

/-- LLVM's lowering (`codegen/llvm/FuncGen.zig` `airDivCeil`): truncating quotient plus one when
the remainder is nonzero and has the divisor's sign. -/
private def reference (s : Bool) (a b : BitVec 8) : Option Int :=
  let x := if s then a.toInt else a.toNat
  let y := if s then b.toInt else b.toNat
  if y = 0 then none else
  let q := x.tdiv y
  let r := x - q * y
  let c := q + (if r ≠ 0 && (decide (r > 0) == decide (y > 0)) then 1 else 0)
  if s && (c < -128 || c > 127) then none else some c

private def asInt (s : Bool) (v : BitVec 8) : Int := if s then v.toInt else v.toNat

def main : IO Unit := do
  -- Every tag delta is classified: renamed/split tags alias to a 0.16.0 tag, the rest reach the
  -- tag table or a stable rejection.
  for tag in added017 do
    require ((tagsOnly017.contains tag)) s!"0.17.0 tag {tag} is not version-gated"
    for v in ["0.14.1", "0.15.2", "0.16.0"] do
      require ((versionTagReason? v tag).isSome) s!"{tag} accepted in {v}"
    require ((versionTagReason? "0.17.0" tag).isNone) s!"{tag} rejected in 0.17.0"
  for tag in removed017 do
    require ((versionTagReason? "0.17.0" tag).isSome) s!"removed {tag} accepted in 0.17.0"
    require ((versionTagReason? "0.16.0" tag).isNone) s!"{tag} rejected in 0.16.0"
  require (tagsOnly017.length == added017.length) "tagsOnly017 differs from the Air.zig delta"
  for (new, old) in tagAliases017 do
    require (removed017.contains old) s!"{new} aliases {old}, which 0.17.0 still has"
  require (supportedVersions.contains "0.17.0" && supportedVersions.contains "0.16.0")
    "0.17.0 must be supported alongside 0.16.0"
  -- Build-mode spelling: 0.17.0's tags map to the version-independent spelling.
  for (new, old) in [("debug", "Debug"), ("safe", "ReleaseSafe"), ("fast", "ReleaseFast"),
      ("small", "ReleaseSmall")] do
    require (BuildProfile.canonicalBuildMode "0.17.0" new == .ok old) s!"0.17.0 {new}"
    require (BuildProfile.canonicalBuildMode "0.17.0" old == .ok old) s!"0.17.0 {old}"
    require ((BuildProfile.canonicalBuildMode "0.16.0" new).toOption.isNone) s!"0.16.0 {new}"
  -- `Zig.divCeil` against the reference on every 8-bit operand pair, both signednesses.
  let mut cases := 0
  for s in [false, true] do
    for i in [0:256] do
      for j in [0:256] do
        let a := BitVec.ofNat 8 i
        let b := BitVec.ofNat 8 j
        let got := (Zig.divCeil s a b).run
        match reference s a b, got with
        | some c, some (.ok q) => require (asInt s q == c) s!"divCeil {s} {i} {j}: {asInt s q} ≠ {c}"
        | none, some (.error e) =>
          require (if b = 0 then e == .divByZero else e == .overflow) s!"divCeil {s} {i} {j}: wrong error"
        | _, _ => throw (IO.userError s!"divCeil {s} {i} {j}: defined/undefined mismatch")
        cases := cases + 1
  IO.println s!"Zig 0.17.0 tag and divCeil regressions passed ({cases} divCeil cases)"
