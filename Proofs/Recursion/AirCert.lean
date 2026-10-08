-- air2lean AIR semantics certificate (docs/air-semantics.md). Generated; do not edit.
import Air2Lean.Sem
import Proofs.Recursion.Gen

namespace Recursion.AirCert

open Air2Lean Air2Lean.Sem

/-! Certified: `recursion.fact`, `recursion.gcd`, `recursion.isEven`, `recursion.isOdd`

Outside the certificate fragment:

(none)
-/

/-- The decoded canonical AIR of `recursion.fact`. -/
def air_fact : Func :=
{ zigVersion := "0.15.2", name := "recursion.fact",
  params := #[0], ret := 0,
  types := #[(.int false 32), .void, .bool, .noreturn, (.other "fn (u32) callconv(.c) u32")],
  layouts := #[{ size := (some 4), align := (some 4), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 0), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 1), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := none, align := none, offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := none, align := none, offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }],
  globals := #[],
  errorSetBits := 16,
  body := #[⟨0, 0, (.arg 0)⟩,
    ⟨10, 1, (.line 2)⟩,
    ⟨1, 1, (.block #[⟨2, 2, (.cmp .eq (.inst 0) (.int 0 (0 : Int)))⟩,
    ⟨3, 3, (.condBr (.inst 2) #[⟨11, 1, (.line 2)⟩,
    ⟨4, 3, (.ret (.int 0 (1 : Int)))⟩] #[⟨5, 3, (.br 1 .void)⟩])⟩])⟩,
    ⟨12, 1, (.line 3)⟩,
    ⟨6, 0, (.arith .sub .checked (.inst 0) (.int 0 (1 : Int)))⟩,
    ⟨13, 1, (.line 3)⟩,
    ⟨7, 0, (.call (.func "recursion.fact" false none) #[(.inst 6)])⟩,
    ⟨14, 1, (.line 3)⟩,
    ⟨8, 0, (.arith .mul .checked (.inst 0) (.inst 7))⟩,
    ⟨15, 1, (.line 3)⟩,
    ⟨9, 3, (.ret (.inst 8))⟩] }

/-- The decoded canonical AIR of `recursion.gcd`. -/
def air_gcd : Func :=
{ zigVersion := "0.15.2", name := "recursion.gcd",
  params := #[0, 0], ret := 0,
  types := #[(.int false 32), .void, .bool, .noreturn, (.other "fn () noreturn"), (.other "fn (u32, u32) callconv(.c) u32")],
  layouts := #[{ size := (some 4), align := (some 4), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 0), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 1), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := none, align := none, offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := none, align := none, offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := none, align := none, offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }],
  globals := #[],
  errorSetBits := 16,
  body := #[⟨0, 0, (.arg 0)⟩,
    ⟨1, 0, (.arg 1)⟩,
    ⟨16, 1, (.line 2)⟩,
    ⟨2, 1, (.block #[⟨3, 2, (.cmp .eq (.inst 1) (.int 0 (0 : Int)))⟩,
    ⟨4, 3, (.condBr (.inst 3) #[⟨17, 1, (.line 2)⟩,
    ⟨5, 3, (.ret (.inst 0))⟩] #[⟨6, 3, (.br 2 .void)⟩])⟩])⟩,
    ⟨18, 1, (.line 3)⟩,
    ⟨7, 2, (.cmp .ne (.inst 1) (.int 0 (0 : Int)))⟩,
    ⟨8, 1, (.block #[⟨9, 3, (.condBr (.inst 7) #[⟨10, 3, (.br 8 .void)⟩] #[⟨11, 3, (.call (.func "debug.FullPanic((function 'defaultPanic')).divideByZero" true none) #[])⟩,
    ⟨12, 3, .unreach⟩])⟩])⟩,
    ⟨13, 0, (.div .rem (.inst 0) (.inst 1))⟩,
    ⟨19, 1, (.line 3)⟩,
    ⟨14, 0, (.call (.func "recursion.gcd" false none) #[(.inst 1), (.inst 13)])⟩,
    ⟨20, 1, (.line 3)⟩,
    ⟨15, 3, (.ret (.inst 14))⟩] }

/-- The decoded canonical AIR of `recursion.isEven`. -/
def air_isEven : Func :=
{ zigVersion := "0.15.2", name := "recursion.isEven",
  params := #[0], ret := 1,
  types := #[(.int false 32), .bool, .void, .noreturn, (.other "fn (u32) callconv(.c) bool")],
  layouts := #[{ size := (some 4), align := (some 4), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 1), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 0), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := none, align := none, offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := none, align := none, offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }],
  globals := #[],
  errorSetBits := 16,
  body := #[⟨0, 0, (.arg 0)⟩,
    ⟨9, 2, (.line 2)⟩,
    ⟨1, 2, (.block #[⟨2, 1, (.cmp .eq (.inst 0) (.int 0 (0 : Int)))⟩,
    ⟨3, 3, (.condBr (.inst 2) #[⟨10, 2, (.line 2)⟩,
    ⟨4, 3, (.ret (.bool true))⟩] #[⟨5, 3, (.br 1 .void)⟩])⟩])⟩,
    ⟨11, 2, (.line 3)⟩,
    ⟨6, 0, (.arith .sub .checked (.inst 0) (.int 0 (1 : Int)))⟩,
    ⟨12, 2, (.line 3)⟩,
    ⟨7, 1, (.call (.func "recursion.isOdd" false none) #[(.inst 6)])⟩,
    ⟨13, 2, (.line 3)⟩,
    ⟨8, 3, (.ret (.inst 7))⟩] }

/-- The decoded canonical AIR of `recursion.isOdd`. -/
def air_isOdd : Func :=
{ zigVersion := "0.15.2", name := "recursion.isOdd",
  params := #[0], ret := 1,
  types := #[(.int false 32), .bool, .void, .noreturn, (.other "fn (u32) callconv(.c) bool")],
  layouts := #[{ size := (some 4), align := (some 4), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 1), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 0), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := none, align := none, offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := none, align := none, offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }],
  globals := #[],
  errorSetBits := 16,
  body := #[⟨0, 0, (.arg 0)⟩,
    ⟨9, 2, (.line 2)⟩,
    ⟨1, 2, (.block #[⟨2, 1, (.cmp .eq (.inst 0) (.int 0 (0 : Int)))⟩,
    ⟨3, 3, (.condBr (.inst 2) #[⟨10, 2, (.line 2)⟩,
    ⟨4, 3, (.ret (.bool false))⟩] #[⟨5, 3, (.br 1 .void)⟩])⟩])⟩,
    ⟨11, 2, (.line 3)⟩,
    ⟨6, 0, (.arith .sub .checked (.inst 0) (.int 0 (1 : Int)))⟩,
    ⟨12, 2, (.line 3)⟩,
    ⟨7, 1, (.call (.func "recursion.isEven" false none) #[(.inst 6)])⟩,
    ⟨13, 2, (.line 3)⟩,
    ⟨8, 3, (.ret (.inst 7))⟩] }

/-- The certified functions, by fully qualified name. -/
def table : Table := [
  ("recursion.fact", air_fact),
  ("recursion.gcd", air_gcd),
  ("recursion.isEven", air_isEven),
  ("recursion.isOdd", air_isOdd)]

/-- The generated definitions as a call oracle (arguments decoded by type). -/
def gen : Oracle
  | "recursion.fact", args =>
    StateT.lift ((fun v => (Value.int false 32 v)) <$> Recursion.fact ((args.getD 0 .void).toBV 32))
  | "recursion.gcd", args =>
    StateT.lift ((fun v => (Value.int false 32 v)) <$> Recursion.gcd ((args.getD 0 .void).toBV 32) ((args.getD 1 .void).toBV 32))
  | "recursion.isEven", args =>
    StateT.lift ((fun v => (Value.bool v)) <$> Recursion.isEven ((args.getD 0 .void).toBV 32))
  | "recursion.isOdd", args =>
    StateT.lift ((fun v => (Value.bool v)) <$> Recursion.isOdd ((args.getD 0 .void).toBV 32))
  | _, _ => StateT.lift stuck

theorem callee_0 : panicOf? "recursion.fact" = none := rfl
theorem callee_1 : panicOf? "debug.FullPanic((function 'defaultPanic')).divideByZero" = some .divByZero := rfl
theorem callee_2 : panicOf? "recursion.gcd" = none := rfl
theorem callee_3 : panicOf? "recursion.isOdd" = none := rfl
theorem callee_4 : panicOf? "recursion.isEven" = none := rfl

/-- `recursion.fact`: the AIR semantics of the decoded function, with the generated program answering its calls, equals the generated definition. -/
theorem fact_step (p0 : BitVec 32) (m : Zig.Mem) :
    (execFunc gen air_fact [(Value.int false 32 p0)]).run m =
      (fun v => ((Value.int false 32 v), m)) <$> Recursion.fact p0 := by
  conv => rhs; rw [Recursion.fact]
  simp only [air_fact, air_sem, callee_0, gen]

theorem fact_fix (args : List Value)
    (h : argsOk air_fact air_fact.params.toList args = true) :
    execFunc gen air_fact args = gen "recursion.fact" args := by
  replace h : argsOk air_fact [0] args = true := h
  obtain ⟨v0, args, rfl, h0, h⟩ := argsOk_cons h
  obtain rfl := argsOk_nil h
  replace h0 : valOk (.int false 32) v0 = true := h0
  rw [valOk_int h0]
  funext m
  show (execFunc gen air_fact _).run m = (gen _ _).run m
  rw [fact_step (v0.toBV 32)]
  simp only [gen, air_sem]

/-- `recursion.gcd`: the AIR semantics of the decoded function, with the generated program answering its calls, equals the generated definition. -/
theorem gcd_step (p0 : BitVec 32) (p1 : BitVec 32) (m : Zig.Mem) :
    (execFunc gen air_gcd [(Value.int false 32 p0), (Value.int false 32 p1)]).run m =
      (fun v => ((Value.int false 32 v), m)) <$> Recursion.gcd p0 p1 := by
  conv => rhs; rw [Recursion.gcd]
  simp only [air_gcd, air_sem, callee_1, callee_2, gen]

theorem gcd_fix (args : List Value)
    (h : argsOk air_gcd air_gcd.params.toList args = true) :
    execFunc gen air_gcd args = gen "recursion.gcd" args := by
  replace h : argsOk air_gcd [0, 0] args = true := h
  obtain ⟨v0, args, rfl, h0, h⟩ := argsOk_cons h
  obtain ⟨v1, args, rfl, h1, h⟩ := argsOk_cons h
  obtain rfl := argsOk_nil h
  replace h0 : valOk (.int false 32) v0 = true := h0
  rw [valOk_int h0]
  replace h1 : valOk (.int false 32) v1 = true := h1
  rw [valOk_int h1]
  funext m
  show (execFunc gen air_gcd _).run m = (gen _ _).run m
  rw [gcd_step (v0.toBV 32) (v1.toBV 32)]
  simp only [gen, air_sem]

/-- `recursion.isEven`: the AIR semantics of the decoded function, with the generated program answering its calls, equals the generated definition. -/
theorem isEven_step (p0 : BitVec 32) (m : Zig.Mem) :
    (execFunc gen air_isEven [(Value.int false 32 p0)]).run m =
      (fun v => ((Value.bool v), m)) <$> Recursion.isEven p0 := by
  conv => rhs; rw [Recursion.isEven]
  simp only [air_isEven, air_sem, callee_3, gen]

theorem isEven_fix (args : List Value)
    (h : argsOk air_isEven air_isEven.params.toList args = true) :
    execFunc gen air_isEven args = gen "recursion.isEven" args := by
  replace h : argsOk air_isEven [0] args = true := h
  obtain ⟨v0, args, rfl, h0, h⟩ := argsOk_cons h
  obtain rfl := argsOk_nil h
  replace h0 : valOk (.int false 32) v0 = true := h0
  rw [valOk_int h0]
  funext m
  show (execFunc gen air_isEven _).run m = (gen _ _).run m
  rw [isEven_step (v0.toBV 32)]
  simp only [gen, air_sem]

/-- `recursion.isOdd`: the AIR semantics of the decoded function, with the generated program answering its calls, equals the generated definition. -/
theorem isOdd_step (p0 : BitVec 32) (m : Zig.Mem) :
    (execFunc gen air_isOdd [(Value.int false 32 p0)]).run m =
      (fun v => ((Value.bool v), m)) <$> Recursion.isOdd p0 := by
  conv => rhs; rw [Recursion.isOdd]
  simp only [air_isOdd, air_sem, callee_4, gen]

theorem isOdd_fix (args : List Value)
    (h : argsOk air_isOdd air_isOdd.params.toList args = true) :
    execFunc gen air_isOdd args = gen "recursion.isOdd" args := by
  replace h : argsOk air_isOdd [0] args = true := h
  obtain ⟨v0, args, rfl, h0, h⟩ := argsOk_cons h
  obtain rfl := argsOk_nil h
  replace h0 : valOk (.int false 32) v0 = true := h0
  rw [valOk_int h0]
  funext m
  show (execFunc gen air_isOdd _).run m = (gen _ _).run m
  rw [isOdd_step (v0.toBV 32)]
  simp only [gen, air_sem]

/-- The generated program satisfies every certified function's AIR equation. -/
theorem gen_fixpoint : Fixpoint gen table :=
  ⟨fact_fix, gcd_fix, isEven_fix, isOdd_fix, trivial⟩

/-- The AIR semantics of the certified program (`Sem.run`, the least fixpoint) is below the
generated program: every terminating AIR behaviour is the generated definition's. -/
theorem run_le_gen : Lean.Order.PartialOrder.rel (run (progOf table)) gen :=
  run_le_of_table gen_fixpoint

/-- `recursion.fact` calls certified functions: every terminating AIR run is the generated definition's. -/
theorem fact_sound (p0 : BitVec 32) (m : Zig.Mem) :
    Lean.Order.PartialOrder.rel ((run (progOf table) "recursion.fact" [(Value.int false 32 p0)]).run m)
      ((fun v => ((Value.int false 32 v), m)) <$> Recursion.fact p0) := by
  have h : Lean.Order.PartialOrder.rel ((run (progOf table) "recursion.fact" [(Value.int false 32 p0)]).run m)
      ((gen "recursion.fact" [(Value.int false 32 p0)]).run m) := run_le_gen "recursion.fact" [(Value.int false 32 p0)] m
  simp only [gen, air_sem] at h
  exact h

/-- `recursion.gcd` calls certified functions: every terminating AIR run is the generated definition's. -/
theorem gcd_sound (p0 : BitVec 32) (p1 : BitVec 32) (m : Zig.Mem) :
    Lean.Order.PartialOrder.rel ((run (progOf table) "recursion.gcd" [(Value.int false 32 p0), (Value.int false 32 p1)]).run m)
      ((fun v => ((Value.int false 32 v), m)) <$> Recursion.gcd p0 p1) := by
  have h : Lean.Order.PartialOrder.rel ((run (progOf table) "recursion.gcd" [(Value.int false 32 p0), (Value.int false 32 p1)]).run m)
      ((gen "recursion.gcd" [(Value.int false 32 p0), (Value.int false 32 p1)]).run m) := run_le_gen "recursion.gcd" [(Value.int false 32 p0), (Value.int false 32 p1)] m
  simp only [gen, air_sem] at h
  exact h

/-- `recursion.isEven` calls certified functions: every terminating AIR run is the generated definition's. -/
theorem isEven_sound (p0 : BitVec 32) (m : Zig.Mem) :
    Lean.Order.PartialOrder.rel ((run (progOf table) "recursion.isEven" [(Value.int false 32 p0)]).run m)
      ((fun v => ((Value.bool v), m)) <$> Recursion.isEven p0) := by
  have h : Lean.Order.PartialOrder.rel ((run (progOf table) "recursion.isEven" [(Value.int false 32 p0)]).run m)
      ((gen "recursion.isEven" [(Value.int false 32 p0)]).run m) := run_le_gen "recursion.isEven" [(Value.int false 32 p0)] m
  simp only [gen, air_sem] at h
  exact h

/-- `recursion.isOdd` calls certified functions: every terminating AIR run is the generated definition's. -/
theorem isOdd_sound (p0 : BitVec 32) (m : Zig.Mem) :
    Lean.Order.PartialOrder.rel ((run (progOf table) "recursion.isOdd" [(Value.int false 32 p0)]).run m)
      ((fun v => ((Value.bool v), m)) <$> Recursion.isOdd p0) := by
  have h : Lean.Order.PartialOrder.rel ((run (progOf table) "recursion.isOdd" [(Value.int false 32 p0)]).run m)
      ((gen "recursion.isOdd" [(Value.int false 32 p0)]).run m) := run_le_gen "recursion.isOdd" [(Value.int false 32 p0)] m
  simp only [gen, air_sem] at h
  exact h

end Recursion.AirCert
