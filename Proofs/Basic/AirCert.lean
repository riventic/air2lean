-- air2lean AIR semantics certificate (docs/air-semantics.md). Generated; do not edit.
import Air2Lean.Sem
import Proofs.Basic.Gen

namespace Basic.AirCert

open Air2Lean Air2Lean.Sem

/-! Certified: `basic.absDiff`, `basic.clampAdd`, `basic.classify`, `basic.scale`, `basic.tardiness`

Outside the certificate fragment:

* `basic.sum`: a parameter that is not an integer or bool
* `basic.totalWeightedTardiness`: a parameter that is not an integer or bool
* `basic.weightedTardiness`: a parameter that is not an integer or bool
-/

/-- The decoded canonical AIR of `basic.absDiff`. -/
def air_absDiff : Func :=
{ dialect := { version := Air2Lean.ZigVersion.v0_15_2, arch := "", os := "", ptrBytes := 8, endian := Air2Lean.Endian.little, errorSetBits := 16, backend := "unverified", buildMode := "unverified" }, name := "basic.absDiff",
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
{ dialect := { version := Air2Lean.ZigVersion.v0_15_2, arch := "", os := "", ptrBytes := 8, endian := Air2Lean.Endian.little, errorSetBits := 16, backend := "unverified", buildMode := "unverified" }, name := "basic.clampAdd",
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
{ dialect := { version := Air2Lean.ZigVersion.v0_15_2, arch := "", os := "", ptrBytes := 8, endian := Air2Lean.Endian.little, errorSetBits := 16, backend := "unverified", buildMode := "unverified" }, name := "basic.classify",
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
{ dialect := { version := Air2Lean.ZigVersion.v0_15_2, arch := "", os := "", ptrBytes := 8, endian := Air2Lean.Endian.little, errorSetBits := 16, backend := "unverified", buildMode := "unverified" }, name := "basic.scale",
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

/-- The decoded canonical AIR of `basic.tardiness`. -/
def air_tardiness : Func :=
{ dialect := { version := Air2Lean.ZigVersion.v0_15_2, arch := "", os := "", ptrBytes := 8, endian := Air2Lean.Endian.little, errorSetBits := 16, backend := "unverified", buildMode := "unverified" }, name := "basic.tardiness",
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
