-- air2lean AIR semantics certificate (docs/air-semantics.md). Generated; do not edit.
import Air2Lean.Sem
import Proofs.Vectors.Gen

set_option linter.unusedSimpArgs false

namespace Vectors.AirCert

open Air2Lean Air2Lean.Sem

/-! Certified: `vectors.sMod`, `vectors.sRem`

Outside the certificate fragment:

* `vectors.addTo`: a parameter that is not an integer, bool, plain pointer or slice
* `vectors.andLanes`: a parameter that is not an integer, bool, plain pointer or slice
* `vectors.checkedAdd`: a parameter that is not an integer, bool, plain pointer or slice
* `vectors.fDot`: a parameter that is not an integer, bool, plain pointer or slice
* `vectors.fMax`: a parameter that is not an integer, bool, plain pointer or slice
* `vectors.fMin`: a parameter that is not an integer, bool, plain pointer or slice
* `vectors.interleave`: a parameter that is not an integer, bool, plain pointer or slice
* `vectors.maxLane`: a parameter that is not an integer, bool, plain pointer or slice
* `vectors.minLane`: a parameter that is not an integer, bool, plain pointer or slice
* `vectors.orLanes`: a parameter that is not an integer, bool, plain pointer or slice
* `vectors.pick`: a parameter that is not an integer, bool, plain pointer or slice
* `vectors.reverse`: a parameter that is not an integer, bool, plain pointer or slice
* `vectors.satAdd`: a parameter that is not an integer, bool, plain pointer or slice
* `vectors.splatAdd`: a parameter that is not an integer, bool, plain pointer or slice
* `vectors.twiceInMem`: a parameter that is not an integer, bool, plain pointer or slice
* `vectors.uDotWrap`: a parameter that is not an integer, bool, plain pointer or slice
* `vectors.uMinLane`: a parameter that is not an integer, bool, plain pointer or slice
* `vectors.vAbs`: a parameter that is not an integer, bool, plain pointer or slice
* `vectors.vBits`: a parameter that is not an integer, bool, plain pointer or slice
* `vectors.vDiv`: a parameter that is not an integer, bool, plain pointer or slice
* `vectors.vLess`: a parameter that is not an integer, bool, plain pointer or slice
* `vectors.vMinMax`: a parameter that is not an integer, bool, plain pointer or slice
* `vectors.vMod`: a parameter that is not an integer, bool, plain pointer or slice
* `vectors.vNarrow`: a parameter that is not an integer, bool, plain pointer or slice
* `vectors.vNeg`: a parameter that is not an integer, bool, plain pointer or slice
* `vectors.vOverflow`: a parameter that is not an integer, bool, plain pointer or slice
* `vectors.vShift`: a parameter that is not an integer, bool, plain pointer or slice
* `vectors.vToFloat`: a parameter that is not an integer, bool, plain pointer or slice
* `vectors.xorLanes`: a parameter that is not an integer, bool, plain pointer or slice
-/

/-- The decoded canonical AIR of `vectors.sMod`. -/
def air_sMod : Func :=
{ zigVersion := "0.16.0", name := "vectors.sMod",
  params := #[0, 0], ret := 0,
  types := #[(.int true 32), .void, .bool, .noreturn, (.other "fn () noreturn")],
  layouts := #[{ size := (some 4), align := (some 4), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 0), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 1), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := none, align := none, offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := none, align := none, offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }],
  globals := #[],
  errorSetBits := 16,
  body := #[⟨0, 0, (.arg 0)⟩,
    ⟨1, 0, (.arg 1)⟩,
    ⟨10, 1, (.line 2)⟩,
    ⟨2, 2, (.cmp .ne (.inst 1) (.int 0 (0 : Int)))⟩,
    ⟨3, 1, (.block #[⟨4, 3, (.condBr (.inst 2) #[⟨5, 3, (.br 3 .void)⟩] #[⟨6, 3, (.call (.func "debug.FullPanic((function 'defaultPanic')).divideByZero" true none) #[])⟩,
    ⟨7, 3, .unreach⟩])⟩])⟩,
    ⟨8, 0, (.div .mod (.inst 0) (.inst 1))⟩,
    ⟨11, 1, (.line 2)⟩,
    ⟨9, 3, (.ret (.inst 8))⟩] }

/-- The decoded canonical AIR of `vectors.sRem`. -/
def air_sRem : Func :=
{ zigVersion := "0.16.0", name := "vectors.sRem",
  params := #[0, 0], ret := 0,
  types := #[(.int true 32), .void, .bool, .noreturn, (.other "fn () noreturn")],
  layouts := #[{ size := (some 4), align := (some 4), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 0), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 1), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := none, align := none, offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := none, align := none, offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }],
  globals := #[],
  errorSetBits := 16,
  body := #[⟨0, 0, (.arg 0)⟩,
    ⟨1, 0, (.arg 1)⟩,
    ⟨10, 1, (.line 2)⟩,
    ⟨2, 2, (.cmp .ne (.inst 1) (.int 0 (0 : Int)))⟩,
    ⟨3, 1, (.block #[⟨4, 3, (.condBr (.inst 2) #[⟨5, 3, (.br 3 .void)⟩] #[⟨6, 3, (.call (.func "debug.FullPanic((function 'defaultPanic')).divideByZero" true none) #[])⟩,
    ⟨7, 3, .unreach⟩])⟩])⟩,
    ⟨8, 0, (.div .rem (.inst 0) (.inst 1))⟩,
    ⟨11, 1, (.line 2)⟩,
    ⟨9, 3, (.ret (.inst 8))⟩] }

/-- The certified functions, by fully qualified name. -/
def table : Table := [
  ("vectors.sMod", air_sMod),
  ("vectors.sRem", air_sRem)]

/-- The generated definitions as a call oracle (arguments decoded by type). -/
def gen : Oracle
  | "vectors.sMod", args =>
    StateT.lift ((fun v => (Value.int true 32 v)) <$> Vectors.sMod ((args.getD 0 .void).toBV 32) ((args.getD 1 .void).toBV 32))
  | "vectors.sRem", args =>
    StateT.lift ((fun v => (Value.int true 32 v)) <$> Vectors.sRem ((args.getD 0 .void).toBV 32) ((args.getD 1 .void).toBV 32))
  | _, _ => StateT.lift stuck

theorem callee_0 : panicOf? "debug.FullPanic((function 'defaultPanic')).divideByZero" = some .divByZero := rfl

/-- `vectors.sMod`: the AIR semantics of the decoded function (under any call oracle) equals the generated definition. -/
theorem sMod_step (call : Oracle) (p0 : BitVec 32) (p1 : BitVec 32) (m : Zig.Mem) :
    (execFunc call air_sMod [(Value.int true 32 p0), (Value.int true 32 p1)]).run m =
      (fun v => ((Value.int true 32 v), m)) <$> Vectors.sMod p0 p1 := by
  conv => rhs; rw [Vectors.sMod]
  simp only [air_sMod, air_sem, callee_0]

theorem sMod_fix (args : List Value)
    (h : argsOk air_sMod air_sMod.params.toList args = true) :
    execFunc gen air_sMod args = gen "vectors.sMod" args := by
  replace h : argsOk air_sMod [0, 0] args = true := h
  obtain ⟨v0, args, rfl, h0, h⟩ := argsOk_cons h
  obtain ⟨v1, args, rfl, h1, h⟩ := argsOk_cons h
  obtain rfl := argsOk_nil h
  replace h0 : valOk (.int true 32) v0 = true := h0
  rw [valOk_int h0]
  replace h1 : valOk (.int true 32) v1 = true := h1
  rw [valOk_int h1]
  funext m
  show (execFunc gen air_sMod _).run m = (gen _ _).run m
  rw [sMod_step gen (v0.toBV 32) (v1.toBV 32)]
  simp only [gen, air_sem]

/-- `vectors.sRem`: the AIR semantics of the decoded function (under any call oracle) equals the generated definition. -/
theorem sRem_step (call : Oracle) (p0 : BitVec 32) (p1 : BitVec 32) (m : Zig.Mem) :
    (execFunc call air_sRem [(Value.int true 32 p0), (Value.int true 32 p1)]).run m =
      (fun v => ((Value.int true 32 v), m)) <$> Vectors.sRem p0 p1 := by
  conv => rhs; rw [Vectors.sRem]
  simp only [air_sRem, air_sem, callee_0]

theorem sRem_fix (args : List Value)
    (h : argsOk air_sRem air_sRem.params.toList args = true) :
    execFunc gen air_sRem args = gen "vectors.sRem" args := by
  replace h : argsOk air_sRem [0, 0] args = true := h
  obtain ⟨v0, args, rfl, h0, h⟩ := argsOk_cons h
  obtain ⟨v1, args, rfl, h1, h⟩ := argsOk_cons h
  obtain rfl := argsOk_nil h
  replace h0 : valOk (.int true 32) v0 = true := h0
  rw [valOk_int h0]
  replace h1 : valOk (.int true 32) v1 = true := h1
  rw [valOk_int h1]
  funext m
  show (execFunc gen air_sRem _).run m = (gen _ _).run m
  rw [sRem_step gen (v0.toBV 32) (v1.toBV 32)]
  simp only [gen, air_sem]

/-- The generated program satisfies every certified function's AIR equation. -/
theorem gen_fixpoint : Fixpoint gen table :=
  ⟨sMod_fix, sRem_fix, trivial⟩

/-- The AIR semantics of the certified program (`Sem.run`, the least fixpoint) is below the
generated program: every terminating AIR behaviour is the generated definition's. -/
theorem run_le_gen : Lean.Order.PartialOrder.rel (run (progOf table)) gen :=
  run_le_of_table gen_fixpoint

/-- `vectors.sMod` makes no certified call: its AIR semantics equals the generated definition. -/
theorem sMod_run (p0 : BitVec 32) (p1 : BitVec 32) (m : Zig.Mem) :
    (run (progOf table) "vectors.sMod" [(Value.int true 32 p0), (Value.int true 32 p1)]).run m =
      (fun v => ((Value.int true 32 v), m)) <$> Vectors.sMod p0 p1 := by
  rw [run_of_lookup (by rfl)]
  exact sMod_step _ p0 p1 m

theorem sMod_complete (p0 : BitVec 32) (p1 : BitVec 32) (m : Zig.Mem) :
    Lean.Order.PartialOrder.rel ((fun v => ((Value.int true 32 v), m)) <$> Vectors.sMod p0 p1)
      ((run (progOf table) "vectors.sMod" [(Value.int true 32 p0), (Value.int true 32 p1)]).run m) :=
  rel_of_eq (sMod_run p0 p1 m).symm

/-- `vectors.sRem` makes no certified call: its AIR semantics equals the generated definition. -/
theorem sRem_run (p0 : BitVec 32) (p1 : BitVec 32) (m : Zig.Mem) :
    (run (progOf table) "vectors.sRem" [(Value.int true 32 p0), (Value.int true 32 p1)]).run m =
      (fun v => ((Value.int true 32 v), m)) <$> Vectors.sRem p0 p1 := by
  rw [run_of_lookup (by rfl)]
  exact sRem_step _ p0 p1 m

theorem sRem_complete (p0 : BitVec 32) (p1 : BitVec 32) (m : Zig.Mem) :
    Lean.Order.PartialOrder.rel ((fun v => ((Value.int true 32 v), m)) <$> Vectors.sRem p0 p1)
      ((run (progOf table) "vectors.sRem" [(Value.int true 32 p0), (Value.int true 32 p1)]).run m) :=
  rel_of_eq (sRem_run p0 p1 m).symm

end Vectors.AirCert
