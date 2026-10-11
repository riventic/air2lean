-- air2lean AIR semantics certificate (docs/air-semantics.md). Generated; do not edit.
import Air2Lean.SemView
import Proofs.Basic.Gen

set_option linter.unusedSimpArgs false

namespace Basic.AirCert

open Air2Lean Air2Lean.Sem

/-! Certified: `basic.absDiff`, `basic.clampAdd`, `basic.classify`, `basic.scale`, `basic.sum`, `basic.tardiness`

Outside the certificate fragment:

* `basic.totalWeightedTardiness`: a slice parameter whose items are not integers or `bool`
* `basic.weightedTardiness`: a parameter that is not an integer, bool, plain pointer or slice
-/

/-- The decoded canonical AIR of `basic.absDiff`. -/
def air_absDiff : Func :=
{ dialect := { version := Air2Lean.ZigVersion.v0_15_2, arch := "", os := "", ptrBytes := 8, endian := Air2Lean.Endian.little, errorSetBits := 16, backend := "unverified", buildMode := "unverified", noLibc := false }, name := "basic.absDiff",
  params := #[0, 0], ret := 1,
  types := #[(.int true 32), (.int false 32), .void, .bool, .noreturn],
  layouts := #[{ size := (some 4), align := (some 4), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 4), align := (some 4), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 0), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 1), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := none, align := none, offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }],
  globals := #[],
  body := #[⟨0, 0, (.arg 0)⟩,
    ⟨1, 0, (.arg 1)⟩,
    ⟨12, 2, (.line 2)⟩,
    ⟨2, 2, (.block #[⟨3, 3, (.cmp .gt (.inst 0) (.inst 1))⟩,
    ⟨4, 4, (.condBr (.inst 3) #[⟨13, 2, (.line 2)⟩,
    ⟨5, 0, (.arith .sub .checked (.inst 0) (.inst 1))⟩,
    ⟨14, 2, (.line 2)⟩,
    ⟨6, 1, (.intCast (.inst 5))⟩,
    ⟨15, 2, (.line 2)⟩,
    ⟨7, 4, (.ret (.inst 6))⟩] #[⟨8, 4, (.br 2 .void)⟩])⟩])⟩,
    ⟨16, 2, (.line 3)⟩,
    ⟨9, 0, (.arith .sub .checked (.inst 1) (.inst 0))⟩,
    ⟨17, 2, (.line 3)⟩,
    ⟨10, 1, (.intCast (.inst 9))⟩,
    ⟨18, 2, (.line 3)⟩,
    ⟨11, 4, (.ret (.inst 10))⟩] }

/-- The decoded canonical AIR of `basic.clampAdd`. -/
def air_clampAdd : Func :=
{ dialect := { version := Air2Lean.ZigVersion.v0_15_2, arch := "", os := "", ptrBytes := 8, endian := Air2Lean.Endian.little, errorSetBits := 16, backend := "unverified", buildMode := "unverified", noLibc := false }, name := "basic.clampAdd",
  params := #[0, 0], ret := 0,
  types := #[(.int false 16), .void, .noreturn],
  layouts := #[{ size := (some 2), align := (some 2), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 0), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := none, align := none, offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }],
  globals := #[],
  body := #[⟨0, 0, (.arg 0)⟩,
    ⟨1, 0, (.arg 1)⟩,
    ⟨4, 1, (.line 2)⟩,
    ⟨2, 0, (.arith .add .sat (.inst 0) (.inst 1))⟩,
    ⟨5, 1, (.line 2)⟩,
    ⟨3, 2, (.ret (.inst 2))⟩] }

/-- The decoded canonical AIR of `basic.classify`. -/
def air_classify : Func :=
{ dialect := { version := Air2Lean.ZigVersion.v0_15_2, arch := "", os := "", ptrBytes := 8, endian := Air2Lean.Endian.little, errorSetBits := 16, backend := "unverified", buildMode := "unverified", noLibc := false }, name := "basic.classify",
  params := #[0], ret := 0,
  types := #[(.int false 8), .void, .noreturn],
  layouts := #[{ size := (some 1), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 0), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := none, align := none, offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }],
  globals := #[],
  body := #[⟨0, 0, (.arg 0)⟩,
    ⟨7, 1, (.line 2)⟩,
    ⟨1, 0, (.block #[⟨2, 2, (.switchBr (.inst 0) #[{ items := #[(.int 0 (0 : Int))], ranges := #[], body := #[⟨4, 2, (.br 1 (.int 0 (0 : Int)))⟩] }, { items := #[], ranges := #[((.int 0 (1 : Int)), (.int 0 (9 : Int)))], body := #[⟨5, 2, (.br 1 (.int 0 (1 : Int)))⟩] }] #[⟨3, 2, (.br 1 (.int 0 (2 : Int)))⟩])⟩])⟩,
    ⟨8, 1, (.line 2)⟩,
    ⟨6, 2, (.ret (.inst 1))⟩] }

/-- The decoded canonical AIR of `basic.scale`. -/
def air_scale : Func :=
{ dialect := { version := Air2Lean.ZigVersion.v0_15_2, arch := "", os := "", ptrBytes := 8, endian := Air2Lean.Endian.little, errorSetBits := 16, backend := "unverified", buildMode := "unverified", noLibc := false }, name := "basic.scale",
  params := #[0, 1], ret := 0,
  types := #[(.int false 32), (.int false 8), .void, .noreturn],
  layouts := #[{ size := (some 4), align := (some 4), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 1), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 0), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := none, align := none, offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }],
  globals := #[],
  body := #[⟨0, 0, (.arg 0)⟩,
    ⟨1, 1, (.arg 1)⟩,
    ⟨5, 2, (.line 2)⟩,
    ⟨2, 0, (.intCast (.inst 1))⟩,
    ⟨3, 0, (.arith .mul .checked (.inst 0) (.inst 2))⟩,
    ⟨6, 2, (.line 2)⟩,
    ⟨4, 3, (.ret (.inst 3))⟩] }

/-- The decoded canonical AIR of `basic.sum`. -/
def air_sum : Func :=
{ dialect := { version := Air2Lean.ZigVersion.v0_15_2, arch := "", ptrBytes := 8, endian := Air2Lean.Endian.little, errorSetBits := 16, backend := "unverified", buildMode := "unverified" }, name := "basic.sum",
  params := #[0], ret := 1,
  types := #[(.ptr "slice" true 8), (.int false 64), .void, (.ptr "one" false 1), (.ptr "one" false 5), (.int false 64), .noreturn, .bool, (.int false 32)],
  layouts := #[{ size := (some 16), align := (some 8), offsets := #[], ptrAlign := (some 4), sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 8), align := (some 8), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 0), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 8), align := (some 8), offsets := #[], ptrAlign := (some 8), sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 8), align := (some 8), offsets := #[], ptrAlign := (some 8), sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 8), align := (some 8), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := none, align := none, offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 1), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 4), align := (some 4), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }],
  globals := #[],
  body := #[⟨0, 0, (.arg 0)⟩,
    ⟨26, 2, (.line 2)⟩,
    ⟨1, 3, .alloc⟩,
    ⟨2, 2, (.store (.inst 1) (.int 1 (0 : Int)))⟩,
    ⟨27, 2, (.dbg (some "total") (some (.inst 1)))⟩,
    ⟨3, 4, .alloc⟩,
    ⟨4, 2, (.store (.inst 3) (.int 5 (0 : Int)))⟩,
    ⟨28, 2, (.line 3)⟩,
    ⟨5, 5, (.sliceLen (.inst 0))⟩,
    ⟨6, 2, (.block #[⟨7, 6, (.loop #[⟨8, 5, (.load (.inst 3))⟩,
    ⟨9, 2, (.block #[⟨10, 1, (.bitcast (.inst 8))⟩,
    ⟨11, 1, (.bitcast (.inst 5))⟩,
    ⟨12, 7, (.cmp .lt (.inst 10) (.inst 11))⟩,
    ⟨13, 6, (.condBr (.inst 12) #[⟨14, 8, (.sliceElemVal (.inst 0) (.inst 8))⟩,
    ⟨29, 2, (.dbg (some "x") (some (.inst 14)))⟩,
    ⟨30, 2, (.line 3)⟩,
    ⟨15, 1, (.load (.inst 1))⟩,
    ⟨16, 1, (.intCast (.inst 14))⟩,
    ⟨31, 2, (.line 3)⟩,
    ⟨17, 1, (.arith .add .checked (.inst 15) (.inst 16))⟩,
    ⟨18, 2, (.store (.inst 1) (.inst 17))⟩,
    ⟨32, 2, (.line 3)⟩,
    ⟨33, 2, (.dbg none none)⟩,
    ⟨19, 6, (.br 9 .void)⟩] #[⟨20, 6, (.br 6 .void)⟩])⟩])⟩,
    ⟨21, 5, (.arith .add .checked (.inst 8) (.int 5 (1 : Int)))⟩,
    ⟨22, 2, (.store (.inst 3) (.inst 21))⟩,
    ⟨23, 6, (.repeat 7)⟩])⟩])⟩,
    ⟨34, 2, (.line 4)⟩,
    ⟨24, 1, (.load (.inst 1))⟩,
    ⟨35, 2, (.line 4)⟩,
    ⟨25, 6, (.ret (.inst 24))⟩] }

/-- The decoded canonical AIR of `basic.tardiness`. -/
def air_tardiness : Func :=
{ dialect := { version := Air2Lean.ZigVersion.v0_15_2, arch := "", os := "", ptrBytes := 8, endian := Air2Lean.Endian.little, errorSetBits := 16, backend := "unverified", buildMode := "unverified", noLibc := false }, name := "basic.tardiness",
  params := #[0, 0], ret := 0,
  types := #[(.int false 32), .void, .bool, .noreturn],
  layouts := #[{ size := (some 4), align := (some 4), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 0), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 1), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := none, align := none, offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }],
  globals := #[],
  body := #[⟨0, 0, (.arg 0)⟩,
    ⟨1, 0, (.arg 1)⟩,
    ⟨9, 1, (.line 2)⟩,
    ⟨2, 0, (.block #[⟨3, 2, (.cmp .gt (.inst 0) (.inst 1))⟩,
    ⟨4, 3, (.condBr (.inst 3) #[⟨10, 1, (.line 2)⟩,
    ⟨5, 0, (.arith .sub .checked (.inst 0) (.inst 1))⟩,
    ⟨6, 3, (.br 2 (.inst 5))⟩] #[⟨7, 3, (.br 2 (.int 0 (0 : Int)))⟩])⟩])⟩,
    ⟨11, 1, (.line 2)⟩,
    ⟨8, 3, (.ret (.inst 2))⟩] }


/-- The items of `basic.sum`'s slice parameters, by their `arg` instruction. -/
def view_sum (a0 : Array (BitVec 32)) : InstId → Option (Array Value) :=
  fun k => if k = 0 then some (a0.map (fun x => (Value.int false 32 x))) else none

/-- The item type of each viewed slice. -/
def viewTy_sum : InstId → TyId :=
  fun k => if k = 0 then 8 else 0

theorem air_sum_body : air_sum.body =
  #[⟨0, 0, (.arg 0)⟩,
    ⟨26, 2, (.line 2)⟩,
    ⟨1, 3, .alloc⟩,
    ⟨2, 2, (.store (.inst 1) (.int 1 (0 : Int)))⟩,
    ⟨27, 2, (.dbg (some "total") (some (.inst 1)))⟩,
    ⟨3, 4, .alloc⟩,
    ⟨4, 2, (.store (.inst 3) (.int 5 (0 : Int)))⟩,
    ⟨28, 2, (.line 3)⟩,
    ⟨5, 5, (.sliceLen (.inst 0))⟩,
    ⟨6, 2, (.block #[⟨7, 6, (.loop #[⟨8, 5, (.load (.inst 3))⟩,
    ⟨9, 2, (.block #[⟨10, 1, (.bitcast (.inst 8))⟩,
    ⟨11, 1, (.bitcast (.inst 5))⟩,
    ⟨12, 7, (.cmp .lt (.inst 10) (.inst 11))⟩,
    ⟨13, 6, (.condBr (.inst 12) #[⟨14, 8, (.sliceElemVal (.inst 0) (.inst 8))⟩,
    ⟨29, 2, (.dbg (some "x") (some (.inst 14)))⟩,
    ⟨30, 2, (.line 3)⟩,
    ⟨15, 1, (.load (.inst 1))⟩,
    ⟨16, 1, (.intCast (.inst 14))⟩,
    ⟨31, 2, (.line 3)⟩,
    ⟨17, 1, (.arith .add .checked (.inst 15) (.inst 16))⟩,
    ⟨18, 2, (.store (.inst 1) (.inst 17))⟩,
    ⟨32, 2, (.line 3)⟩,
    ⟨33, 2, (.dbg none none)⟩,
    ⟨19, 6, (.br 9 .void)⟩] #[⟨20, 6, (.br 6 .void)⟩])⟩])⟩,
    ⟨21, 5, (.arith .add .checked (.inst 8) (.int 5 (1 : Int)))⟩,
    ⟨22, 2, (.store (.inst 3) (.inst 21))⟩,
    ⟨23, 6, (.repeat 7)⟩])⟩])⟩,
    ⟨34, 2, (.line 4)⟩,
    ⟨24, 1, (.load (.inst 1))⟩,
    ⟨35, 2, (.line 4)⟩,
    ⟨25, 6, (.ret (.inst 24))⟩] := rfl
theorem air_sum_types : air_sum.types = #[(.ptr "slice" true 8), (.int false 64), .void, (.ptr "one" false 1), (.ptr "one" false 5), (.int false 64), .noreturn, .bool, (.int false 32)] := rfl
theorem air_sum_layouts : air_sum.layouts = #[{ size := (some 16), align := (some 8), offsets := #[], ptrAlign := (some 4), sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 8), align := (some 8), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 0), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 8), align := (some 8), offsets := #[], ptrAlign := (some 8), sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 8), align := (some 8), offsets := #[], ptrAlign := (some 8), sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 8), align := (some 8), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := none, align := none, offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 1), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 4), align := (some 4), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }] := rfl
theorem air_sum_params : air_sum.params = #[0] := rfl

/-- The generated exits of `basic.sum` as AIR exits. -/
def enc_sum : Basic.sumExit → Exit
  | .ret v => .ret (Value.int false 64 v)
  | .br9 => .br 9 .void
  | .br6 => .br 6 .void
  | .rep7 => .rep 7

theorem sum_loop7_body (call : Oracle) (a0 : Array (BitVec 32)) (p0 : Zig.Slice) (hs0 : a0.size = p0.len.toNat) (args : List Value) (env : Env) (st : Frame) (x5 : BitVec 64)
    (h0 : env 0 = some (0, (Value.slice p0))) (h5 : env 5 = some (5, (Value.int false 64 x5))) (h1 : env 1 = some (3, .cell 1)) (h3 : env 3 = some (4, .cell 3)) (s : Basic.sumLocals) (m : Zig.Mem) :
    ((execBody ⟨air_sum, args, call, (view_sum a0)⟩ (Array.toList #[⟨8, 5, (.load (.inst 3))⟩,
    ⟨9, 2, (.block #[⟨10, 1, (.bitcast (.inst 8))⟩,
    ⟨11, 1, (.bitcast (.inst 5))⟩,
    ⟨12, 7, (.cmp .lt (.inst 10) (.inst 11))⟩,
    ⟨13, 6, (.condBr (.inst 12) #[⟨14, 8, (.sliceElemVal (.inst 0) (.inst 8))⟩,
    ⟨29, 2, (.dbg (some "x") (some (.inst 14)))⟩,
    ⟨30, 2, (.line 3)⟩,
    ⟨15, 1, (.load (.inst 1))⟩,
    ⟨16, 1, (.intCast (.inst 14))⟩,
    ⟨31, 2, (.line 3)⟩,
    ⟨17, 1, (.arith .add .checked (.inst 15) (.inst 16))⟩,
    ⟨18, 2, (.store (.inst 1) (.inst 17))⟩,
    ⟨32, 2, (.line 3)⟩,
    ⟨33, 2, (.dbg none none)⟩,
    ⟨19, 6, (.br 9 .void)⟩] #[⟨20, 6, (.br 6 .void)⟩])⟩])⟩,
    ⟨21, 5, (.arith .add .checked (.inst 8) (.int 5 (1 : Int)))⟩,
    ⟨22, 2, (.store (.inst 3) (.inst 21))⟩,
    ⟨23, 6, (.repeat 7)⟩]) env).run (Frame.setCell (Frame.setCell st 1 (some (Value.int false 64 s.total))) 3 (some (Value.int false 64 s.local3)))).run m =
      (fun r => ((enc_sum r.1, (Frame.setCell (Frame.setCell st 1 (some (Value.int false 64 r.2.total))) 3 (some (Value.int false 64 r.2.local3)))), m)) <$> (Basic.sum.loop7 a0 x5).run s := by
  conv => rhs; rw [Basic.sum.loop7]
  simp only [air_sum_body, air_sum_types, air_sum_layouts, air_sum_params, air_sem, enc_sum, execFuncV, view_sum, len_of_size hs0, hs0, h0, h5, h1, h3, Env.val, Frame.cell]
  all_goals repeat (first
    | rfl
    | (refine bind_congr fun _ => ?_))

theorem sum_loop7_comm (call : Oracle) (a0 : Array (BitVec 32)) (p0 : Zig.Slice) (hs0 : a0.size = p0.len.toNat) (args : List Value) (env : Env) (st : Frame) (x5 : BitVec 64)
    (h0 : env 0 = some (0, (Value.slice p0))) (h5 : env 5 = some (5, (Value.int false 64 x5))) (h1 : env 1 = some (3, .cell 1)) (h3 : env 3 = some (4, .cell 3)) (s : Basic.sumLocals) (m : Zig.Mem) :
    ((execLoop ⟨air_sum, args, call, (view_sum a0)⟩ 7 #[⟨8, 5, (.load (.inst 3))⟩,
    ⟨9, 2, (.block #[⟨10, 1, (.bitcast (.inst 8))⟩,
    ⟨11, 1, (.bitcast (.inst 5))⟩,
    ⟨12, 7, (.cmp .lt (.inst 10) (.inst 11))⟩,
    ⟨13, 6, (.condBr (.inst 12) #[⟨14, 8, (.sliceElemVal (.inst 0) (.inst 8))⟩,
    ⟨29, 2, (.dbg (some "x") (some (.inst 14)))⟩,
    ⟨30, 2, (.line 3)⟩,
    ⟨15, 1, (.load (.inst 1))⟩,
    ⟨16, 1, (.intCast (.inst 14))⟩,
    ⟨31, 2, (.line 3)⟩,
    ⟨17, 1, (.arith .add .checked (.inst 15) (.inst 16))⟩,
    ⟨18, 2, (.store (.inst 1) (.inst 17))⟩,
    ⟨32, 2, (.line 3)⟩,
    ⟨33, 2, (.dbg none none)⟩,
    ⟨19, 6, (.br 9 .void)⟩] #[⟨20, 6, (.br 6 .void)⟩])⟩])⟩,
    ⟨21, 5, (.arith .add .checked (.inst 8) (.int 5 (1 : Int)))⟩,
    ⟨22, 2, (.store (.inst 3) (.inst 21))⟩,
    ⟨23, 6, (.repeat 7)⟩] env).run (Frame.setCell (Frame.setCell st 1 (some (Value.int false 64 s.total))) 3 (some (Value.int false 64 s.local3)))).run m =
      (fun r => (mapRes enc_sum (fun s : Basic.sumLocals => (Frame.setCell (Frame.setCell st 1 (some (Value.int false 64 s.total))) 3 (some (Value.int false 64 s.local3)))) r, m)) <$> (Zig.loop (Basic.sum.loop7 a0 x5) Basic.sum.again7).run s := by
  unfold execLoop
  exact loop_comm_pure _ _ (Exit.again 7) Basic.sum.again7 enc_sum (fun s : Basic.sumLocals => (Frame.setCell (Frame.setCell st 1 (some (Value.int false 64 s.total))) 3 (some (Value.int false 64 s.local3))))
    (fun s m => sum_loop7_body call a0 p0 hs0 args env st x5 h0 h5 h1 h3 s m)
    (by intro e; cases e <;> rfl) s m

theorem sum_loop7_exits (a0 : Array (BitVec 32)) (p0 : Zig.Slice) (hs0 : a0.size = p0.len.toNat) (x5 : BitVec 64) (s : Basic.sumLocals) (r : Basic.sumExit × Basic.sumLocals)
    (hr : ((Zig.loop (Basic.sum.loop7 a0 x5) Basic.sum.again7).run s).run = some (.ok r)) :
    Exit.again 7 (enc_sum r.1) = false ∧ exitOk [6] [] (enc_sum r.1) = true := by
  let env : Env := (Env.set (Env.set (Env.set (Env.set (fun _ => none) 0 0 (Value.slice p0)) 5 5 (Value.int false 64 x5)) 1 3 (.cell 1)) 3 4 (.cell 3))
  exact ok_transfer_pure (F := fun s : Basic.sumLocals => (Frame.setCell (Frame.setCell ({} : Frame) 1 (some (Value.int false 64 s.total))) 3 (some (Value.int false 64 s.local3))))
    (fun m => sum_loop7_comm (fun _ _ => StateT.lift stuck) a0 p0 hs0 [] env {} x5 (by simp [env, Env.set]) (by simp [env, Env.set]) (by simp [env, Env.set]) (by simp [env, Env.set]) s m)
    (execLoop_ok _ 7 _ env [6] [] (by simp [wfBody, wfInst, wfCases])) r hr

theorem sum_loop7 (call : Oracle) (a0 : Array (BitVec 32)) (args : List Value) (env : Env) (st : Frame) (B : Array Inst)
    (hB : B = #[⟨8, 5, (.load (.inst 3))⟩,
    ⟨9, 2, (.block #[⟨10, 1, (.bitcast (.inst 8))⟩,
    ⟨11, 1, (.bitcast (.inst 5))⟩,
    ⟨12, 7, (.cmp .lt (.inst 10) (.inst 11))⟩,
    ⟨13, 6, (.condBr (.inst 12) #[⟨14, 8, (.sliceElemVal (.inst 0) (.inst 8))⟩,
    ⟨29, 2, (.dbg (some "x") (some (.inst 14)))⟩,
    ⟨30, 2, (.line 3)⟩,
    ⟨15, 1, (.load (.inst 1))⟩,
    ⟨16, 1, (.intCast (.inst 14))⟩,
    ⟨31, 2, (.line 3)⟩,
    ⟨17, 1, (.arith .add .checked (.inst 15) (.inst 16))⟩,
    ⟨18, 2, (.store (.inst 1) (.inst 17))⟩,
    ⟨32, 2, (.line 3)⟩,
    ⟨33, 2, (.dbg none none)⟩,
    ⟨19, 6, (.br 9 .void)⟩] #[⟨20, 6, (.br 6 .void)⟩])⟩])⟩,
    ⟨21, 5, (.arith .add .checked (.inst 8) (.int 5 (1 : Int)))⟩,
    ⟨22, 2, (.store (.inst 3) (.inst 21))⟩,
    ⟨23, 6, (.repeat 7)⟩])
    (h0 : env 0 = some (0, Value.slice (Value.toSlice (env.val 0)))) (h5 : env 5 = some (5, (Value.int false 64 (Value.toBV 64 (env.val 5))))) (h1 : env 1 = some (3, .cell 1)) (h3 : env 3 = some (4, .cell 3)) (hs0 : a0.size = (Value.toSlice (env.val 0)).len.toNat)
    (hc1 : st.cells 1 = some (Value.int false 64 (Value.toBV 64 (st.cell 1)))) (hc3 : st.cells 3 = some (Value.int false 64 (Value.toBV 64 (st.cell 3)))) :
    (execLoop ⟨air_sum, args, call, (view_sum a0)⟩ 7 B env).run st =
      StateT.lift (mapRes enc_sum (fun s : Basic.sumLocals => (Frame.setCell (Frame.setCell st 1 (some (Value.int false 64 s.total))) 3 (some (Value.int false 64 s.local3)))) <$>
        (Zig.loop (Basic.sum.loop7 a0 (Value.toBV 64 (env.val 5))) Basic.sum.again7).run { (default : Basic.sumLocals) with total := (Value.toBV 64 (st.cell 1)), local3 := (Value.toBV 64 (st.cell 3)) }) := by
  subst hB
  have e : (Frame.setCell (Frame.setCell st 1 (some (Value.int false 64 { (default : Basic.sumLocals) with total := (Value.toBV 64 (st.cell 1)), local3 := (Value.toBV 64 (st.cell 3)) }.total))) 3 (some (Value.int false 64 { (default : Basic.sumLocals) with total := (Value.toBV 64 (st.cell 1)), local3 := (Value.toBV 64 (st.cell 3)) }.local3))) = st := by
    dsimp only
    rw [Frame.setCell_eq _ _ _ hc1, Frame.setCell_eq _ _ _ hc3]
  conv => lhs; rw [← e]
  apply StateT.ext; intro m
  rw [lift_map_run]
  exact sum_loop7_comm call a0 (Value.toSlice (env.val 0)) hs0 args env st (Value.toBV 64 (env.val 5)) h0 h5 h1 h3 { (default : Basic.sumLocals) with total := (Value.toBV 64 (st.cell 1)), local3 := (Value.toBV 64 (st.cell 3)) } m

/-- `basic.sum` run with the items of its slices as a view equals the generated definition. -/
theorem sum_view (call : Oracle) (p0 : Zig.Slice) (a0 : Array (BitVec 32)) (hs0 : a0.size = p0.len.toNat) (m : Zig.Mem) :
    (execFuncV call (view_sum a0) air_sum [Value.slice p0]).run m =
      (fun v => ((Value.int false 64 v), m)) <$> Basic.sum a0 := by
  conv => rhs; rw [Basic.sum]
  simp only [air_sum_body, air_sum_types, air_sum_layouts, air_sum_params, air_sem, enc_sum, execFuncV, view_sum, len_of_size hs0, hs0, sum_loop7, Env.val, Frame.cell]
  all_goals repeat (first
    | rfl
    | (refine bind_congr_ok _ _ (fun r hr => sum_loop7_exits a0 p0 hs0 _ _ r hr) ?_
       rintro ⟨e, s⟩ ⟨h1, h2⟩
       cases e <;> simp (config := { failIfUnchanged := false }) only [air_sum_body, air_sum_types, air_sum_layouts, air_sum_params, air_sem, enc_sum, execFuncV, view_sum, len_of_size hs0, hs0, Env.val, Frame.cell, Exit.again, exitOk] at h1 h2 ⊢)
    | (refine bind_congr fun _ => ?_))

/-- `basic.sum`, called with the items its caller read (`Zig.readSlice`, from `m`): the AIR
semantics has the generated definition's values and errors, and its memory is `m` up to read
entries of the running thread (`UpToReads`). -/
theorem sum_step (call : Oracle) (p0 : Zig.Slice) (m : Zig.Mem) (hwf : m.ClockWf)
    (a0 : Array (BitVec 32)) (m0 : Zig.Mem)
    (r0 : ((Zig.readSlice (BitVec 32) 4 p0).run m).run = some (.ok (a0, m0))) :
    RelR (fun p q => p.1 = q.1 ∧ UpToReads m p.2 ∧ q.2 = m)
      ((execFunc call air_sum [Value.slice p0]).run m)
      ((fun v => ((Value.int false 64 v), m)) <$> Basic.sum a0) := by
  obtain ⟨v0, hs0, -⟩ := holds_of_readSlice (f := air_sum) (t := 8) (a := 4)
    (fun x => (Value.int false 32 x)) r0 hwf (fun q al => by simp only [air_sum, air_sem])
    (fun size al h => by
      simp only [air_sum, air_sem, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      decide)
  rw [← sum_view call p0 a0 hs0 m]
  refine execFunc_view m air_sum _ call (view_sum a0) viewTy_sum
    (by simp only [roBody, roNested, roCases, roInst, argAt, air_sum, air_sem, view_sum, viewTy_sum,
      List.find?_cons, List.find?_nil, cond_true, cond_false, Option.isSome_some])
    ⟨by simp [Value.noPtr], ?_⟩
  intro k items idx t hk ha
  simp only [view_sum] at hk
  split at hk
  · cases hk
    subst_vars
    rw [show argAt air_sum 0 = some (0, 0) from rfl] at ha
    cases ha
    exact ⟨p0, 4, rfl, rfl, v0, by simp [Value.noPtr]⟩
  all_goals cases hk

/-- The functions certified through a view of their slices, by fully qualified name. -/
def views : Table := [
  ("basic.sum", air_sum)]

/-- The certified functions, by fully qualified name. -/
def table : Table := [
  ("basic.absDiff", air_absDiff),
  ("basic.clampAdd", air_clampAdd),
  ("basic.classify", air_classify),
  ("basic.scale", air_scale),
  ("basic.tardiness", air_tardiness)]

/-- The generated definitions as a call oracle (arguments decoded by type). -/
def gen : Oracle
  | "basic.absDiff", args =>
    StateT.lift ((fun v => (Value.int false 32 v)) <$> Basic.absDiff ((args.getD 0 .void).toBV 32) ((args.getD 1 .void).toBV 32))
  | "basic.clampAdd", args =>
    StateT.lift ((fun v => (Value.int false 16 v)) <$> Basic.clampAdd ((args.getD 0 .void).toBV 16) ((args.getD 1 .void).toBV 16))
  | "basic.classify", args =>
    StateT.lift ((fun v => (Value.int false 8 v)) <$> Basic.classify ((args.getD 0 .void).toBV 8))
  | "basic.scale", args =>
    StateT.lift ((fun v => (Value.int false 32 v)) <$> Basic.scale ((args.getD 0 .void).toBV 32) ((args.getD 1 .void).toBV 8))
  | "basic.tardiness", args =>
    StateT.lift ((fun v => (Value.int false 32 v)) <$> Basic.tardiness ((args.getD 0 .void).toBV 32) ((args.getD 1 .void).toBV 32))
  | _, _ => StateT.lift stuck

/-- `basic.absDiff`: the AIR semantics of the decoded function (under any call oracle) equals the generated definition. -/
theorem absDiff_step (call : Oracle) (p0 : BitVec 32) (p1 : BitVec 32) (m : Zig.Mem) :
    (execFunc call air_absDiff [(Value.int true 32 p0), (Value.int true 32 p1)]).run m =
      (fun v => ((Value.int false 32 v), m)) <$> Basic.absDiff p0 p1 := by
  conv => rhs; rw [Basic.absDiff]
  simp only [air_absDiff, air_sem]

theorem absDiff_fix (args : List Value)
    (h : argsOk air_absDiff air_absDiff.params.toList args = true) :
    execFunc gen air_absDiff args = gen "basic.absDiff" args := by
  replace h : argsOk air_absDiff [0, 0] args = true := h
  obtain ⟨v0, args, rfl, h0, h⟩ := argsOk_cons h
  obtain ⟨v1, args, rfl, h1, h⟩ := argsOk_cons h
  obtain rfl := argsOk_nil h
  replace h0 : valOk (.int true 32) v0 = true := h0
  rw [valOk_int h0]
  replace h1 : valOk (.int true 32) v1 = true := h1
  rw [valOk_int h1]
  funext m
  show (execFunc gen air_absDiff _).run m = (gen _ _).run m
  rw [absDiff_step gen (v0.toBV 32) (v1.toBV 32)]
  simp only [gen, air_sem]

/-- `basic.clampAdd`: the AIR semantics of the decoded function (under any call oracle) equals the generated definition. -/
theorem clampAdd_step (call : Oracle) (p0 : BitVec 16) (p1 : BitVec 16) (m : Zig.Mem) :
    (execFunc call air_clampAdd [(Value.int false 16 p0), (Value.int false 16 p1)]).run m =
      (fun v => ((Value.int false 16 v), m)) <$> Basic.clampAdd p0 p1 := by
  conv => rhs; rw [Basic.clampAdd]
  simp only [air_clampAdd, air_sem]

theorem clampAdd_fix (args : List Value)
    (h : argsOk air_clampAdd air_clampAdd.params.toList args = true) :
    execFunc gen air_clampAdd args = gen "basic.clampAdd" args := by
  replace h : argsOk air_clampAdd [0, 0] args = true := h
  obtain ⟨v0, args, rfl, h0, h⟩ := argsOk_cons h
  obtain ⟨v1, args, rfl, h1, h⟩ := argsOk_cons h
  obtain rfl := argsOk_nil h
  replace h0 : valOk (.int false 16) v0 = true := h0
  rw [valOk_int h0]
  replace h1 : valOk (.int false 16) v1 = true := h1
  rw [valOk_int h1]
  funext m
  show (execFunc gen air_clampAdd _).run m = (gen _ _).run m
  rw [clampAdd_step gen (v0.toBV 16) (v1.toBV 16)]
  simp only [gen, air_sem]

/-- `basic.classify`: the AIR semantics of the decoded function (under any call oracle) equals the generated definition. -/
theorem classify_step (call : Oracle) (p0 : BitVec 8) (m : Zig.Mem) :
    (execFunc call air_classify [(Value.int false 8 p0)]).run m =
      (fun v => ((Value.int false 8 v), m)) <$> Basic.classify p0 := by
  conv => rhs; rw [Basic.classify]
  simp only [air_classify, air_sem]

theorem classify_fix (args : List Value)
    (h : argsOk air_classify air_classify.params.toList args = true) :
    execFunc gen air_classify args = gen "basic.classify" args := by
  replace h : argsOk air_classify [0] args = true := h
  obtain ⟨v0, args, rfl, h0, h⟩ := argsOk_cons h
  obtain rfl := argsOk_nil h
  replace h0 : valOk (.int false 8) v0 = true := h0
  rw [valOk_int h0]
  funext m
  show (execFunc gen air_classify _).run m = (gen _ _).run m
  rw [classify_step gen (v0.toBV 8)]
  simp only [gen, air_sem]

/-- `basic.scale`: the AIR semantics of the decoded function (under any call oracle) equals the generated definition. -/
theorem scale_step (call : Oracle) (p0 : BitVec 32) (p1 : BitVec 8) (m : Zig.Mem) :
    (execFunc call air_scale [(Value.int false 32 p0), (Value.int false 8 p1)]).run m =
      (fun v => ((Value.int false 32 v), m)) <$> Basic.scale p0 p1 := by
  conv => rhs; rw [Basic.scale]
  simp only [air_scale, air_sem]

theorem scale_fix (args : List Value)
    (h : argsOk air_scale air_scale.params.toList args = true) :
    execFunc gen air_scale args = gen "basic.scale" args := by
  replace h : argsOk air_scale [0, 1] args = true := h
  obtain ⟨v0, args, rfl, h0, h⟩ := argsOk_cons h
  obtain ⟨v1, args, rfl, h1, h⟩ := argsOk_cons h
  obtain rfl := argsOk_nil h
  replace h0 : valOk (.int false 32) v0 = true := h0
  rw [valOk_int h0]
  replace h1 : valOk (.int false 8) v1 = true := h1
  rw [valOk_int h1]
  funext m
  show (execFunc gen air_scale _).run m = (gen _ _).run m
  rw [scale_step gen (v0.toBV 32) (v1.toBV 8)]
  simp only [gen, air_sem]

/-- `basic.tardiness`: the AIR semantics of the decoded function (under any call oracle) equals the generated definition. -/
theorem tardiness_step (call : Oracle) (p0 : BitVec 32) (p1 : BitVec 32) (m : Zig.Mem) :
    (execFunc call air_tardiness [(Value.int false 32 p0), (Value.int false 32 p1)]).run m =
      (fun v => ((Value.int false 32 v), m)) <$> Basic.tardiness p0 p1 := by
  conv => rhs; rw [Basic.tardiness]
  simp only [air_tardiness, air_sem]

theorem tardiness_fix (args : List Value)
    (h : argsOk air_tardiness air_tardiness.params.toList args = true) :
    execFunc gen air_tardiness args = gen "basic.tardiness" args := by
  replace h : argsOk air_tardiness [0, 0] args = true := h
  obtain ⟨v0, args, rfl, h0, h⟩ := argsOk_cons h
  obtain ⟨v1, args, rfl, h1, h⟩ := argsOk_cons h
  obtain rfl := argsOk_nil h
  replace h0 : valOk (.int false 32) v0 = true := h0
  rw [valOk_int h0]
  replace h1 : valOk (.int false 32) v1 = true := h1
  rw [valOk_int h1]
  funext m
  show (execFunc gen air_tardiness _).run m = (gen _ _).run m
  rw [tardiness_step gen (v0.toBV 32) (v1.toBV 32)]
  simp only [gen, air_sem]

/-- The generated program satisfies every certified function's AIR equation. -/
theorem gen_fixpoint : Fixpoint gen table :=
  ⟨absDiff_fix, clampAdd_fix, classify_fix, scale_fix, tardiness_fix, trivial⟩

/-- The AIR semantics of the certified program (`Sem.run`, the least fixpoint) is below the
generated program: every terminating AIR behaviour is the generated definition's. -/
theorem run_le_gen : Lean.Order.PartialOrder.rel (run (progOf table)) gen :=
  run_le_of_table gen_fixpoint

/-- `basic.absDiff` makes no certified call: its AIR semantics equals the generated definition. -/
theorem absDiff_run (p0 : BitVec 32) (p1 : BitVec 32) (m : Zig.Mem) :
    (run (progOf table) "basic.absDiff" [(Value.int true 32 p0), (Value.int true 32 p1)]).run m =
      (fun v => ((Value.int false 32 v), m)) <$> Basic.absDiff p0 p1 := by
  rw [run_of_lookup (by rfl)]
  exact absDiff_step _ p0 p1 m

theorem absDiff_complete (p0 : BitVec 32) (p1 : BitVec 32) (m : Zig.Mem) :
    Lean.Order.PartialOrder.rel ((fun v => ((Value.int false 32 v), m)) <$> Basic.absDiff p0 p1)
      ((run (progOf table) "basic.absDiff" [(Value.int true 32 p0), (Value.int true 32 p1)]).run m) :=
  rel_of_eq (absDiff_run p0 p1 m).symm

/-- `basic.clampAdd` makes no certified call: its AIR semantics equals the generated definition. -/
theorem clampAdd_run (p0 : BitVec 16) (p1 : BitVec 16) (m : Zig.Mem) :
    (run (progOf table) "basic.clampAdd" [(Value.int false 16 p0), (Value.int false 16 p1)]).run m =
      (fun v => ((Value.int false 16 v), m)) <$> Basic.clampAdd p0 p1 := by
  rw [run_of_lookup (by rfl)]
  exact clampAdd_step _ p0 p1 m

theorem clampAdd_complete (p0 : BitVec 16) (p1 : BitVec 16) (m : Zig.Mem) :
    Lean.Order.PartialOrder.rel ((fun v => ((Value.int false 16 v), m)) <$> Basic.clampAdd p0 p1)
      ((run (progOf table) "basic.clampAdd" [(Value.int false 16 p0), (Value.int false 16 p1)]).run m) :=
  rel_of_eq (clampAdd_run p0 p1 m).symm

/-- `basic.classify` makes no certified call: its AIR semantics equals the generated definition. -/
theorem classify_run (p0 : BitVec 8) (m : Zig.Mem) :
    (run (progOf table) "basic.classify" [(Value.int false 8 p0)]).run m =
      (fun v => ((Value.int false 8 v), m)) <$> Basic.classify p0 := by
  rw [run_of_lookup (by rfl)]
  exact classify_step _ p0 m

theorem classify_complete (p0 : BitVec 8) (m : Zig.Mem) :
    Lean.Order.PartialOrder.rel ((fun v => ((Value.int false 8 v), m)) <$> Basic.classify p0)
      ((run (progOf table) "basic.classify" [(Value.int false 8 p0)]).run m) :=
  rel_of_eq (classify_run p0 m).symm

/-- `basic.scale` makes no certified call: its AIR semantics equals the generated definition. -/
theorem scale_run (p0 : BitVec 32) (p1 : BitVec 8) (m : Zig.Mem) :
    (run (progOf table) "basic.scale" [(Value.int false 32 p0), (Value.int false 8 p1)]).run m =
      (fun v => ((Value.int false 32 v), m)) <$> Basic.scale p0 p1 := by
  rw [run_of_lookup (by rfl)]
  exact scale_step _ p0 p1 m

theorem scale_complete (p0 : BitVec 32) (p1 : BitVec 8) (m : Zig.Mem) :
    Lean.Order.PartialOrder.rel ((fun v => ((Value.int false 32 v), m)) <$> Basic.scale p0 p1)
      ((run (progOf table) "basic.scale" [(Value.int false 32 p0), (Value.int false 8 p1)]).run m) :=
  rel_of_eq (scale_run p0 p1 m).symm

/-- `basic.tardiness` makes no certified call: its AIR semantics equals the generated definition. -/
theorem tardiness_run (p0 : BitVec 32) (p1 : BitVec 32) (m : Zig.Mem) :
    (run (progOf table) "basic.tardiness" [(Value.int false 32 p0), (Value.int false 32 p1)]).run m =
      (fun v => ((Value.int false 32 v), m)) <$> Basic.tardiness p0 p1 := by
  rw [run_of_lookup (by rfl)]
  exact tardiness_step _ p0 p1 m

theorem tardiness_complete (p0 : BitVec 32) (p1 : BitVec 32) (m : Zig.Mem) :
    Lean.Order.PartialOrder.rel ((fun v => ((Value.int false 32 v), m)) <$> Basic.tardiness p0 p1)
      ((run (progOf table) "basic.tardiness" [(Value.int false 32 p0), (Value.int false 32 p1)]).run m) :=
  rel_of_eq (tardiness_run p0 p1 m).symm

end Basic.AirCert
