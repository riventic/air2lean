-- air2lean AIR semantics certificate (docs/air-semantics.md). Generated; do not edit.
import Air2Lean.Sem
import Proofs.Errors.Gen

set_option linter.unusedSimpArgs false

namespace Errors.AirCert

open Air2Lean Air2Lean.Sem

/-! Certified: `errors.digitOrZero`, `errors.parseDigit`

Outside the certificate fragment:

* `errors.sumDigits`: a function with a slice parameter that reads memory other than through its items (`Sem.roBody`)
-/

/-- The decoded canonical AIR of `errors.digitOrZero`. -/
def air_digitOrZero : Func :=
{ dialect := { version := Air2Lean.ZigVersion.v0_15_2, arch := "", ptrBytes := 8, endian := Air2Lean.Endian.little, errorSetBits := 16, backend := "unverified", buildMode := "unverified" }, name := "errors.digitOrZero",
  params := #[0], ret := 0,
  types := #[(.int false 8), .void, (.errorUnion 6 0), (.other "fn (u8) error{NotDigit}!u8"), .bool, .noreturn, (.errorSet (some #["NotDigit"]))],
  layouts := #[{ size := (some 1), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 0), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 4), align := (some 2), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := none, align := none, offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 1), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := none, align := none, offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 2), align := (some 2), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }],
  globals := #[],
  body := #[⟨0, 0, (.arg 0)⟩,
    ⟨10, 1, (.line 2)⟩,
    ⟨1, 0, (.block #[⟨11, 1, (.line 2)⟩,
    ⟨2, 2, (.call (.func "errors.parseDigit" false none) #[(.inst 0)])⟩,
    ⟨3, 4, (.isNonErr (.inst 2))⟩,
    ⟨4, 5, (.condBr (.inst 3) #[⟨5, 0, (.errPayload (.inst 2))⟩,
    ⟨6, 5, (.br 1 (.inst 5))⟩] #[⟨7, 6, (.errCode (.inst 2))⟩,
    ⟨8, 5, (.br 1 (.int 0 (0 : Int)))⟩])⟩])⟩,
    ⟨12, 1, (.line 2)⟩,
    ⟨9, 5, (.ret (.inst 1))⟩] }

/-- The decoded canonical AIR of `errors.parseDigit`. -/
def air_parseDigit : Func :=
{ dialect := { version := Air2Lean.ZigVersion.v0_15_2, arch := "", ptrBytes := 8, endian := Air2Lean.Endian.little, errorSetBits := 16, backend := "unverified", buildMode := "unverified" }, name := "errors.parseDigit",
  params := #[0], ret := 1,
  types := #[(.int false 8), (.errorUnion 5 0), .void, .bool, .noreturn, (.errorSet (some #["NotDigit"]))],
  layouts := #[{ size := (some 1), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 4), align := (some 2), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 0), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 1), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := none, align := none, offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 2), align := (some 2), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }],
  globals := #[],
  body := #[⟨0, 0, (.arg 0)⟩,
    ⟨14, 2, (.line 2)⟩,
    ⟨1, 2, (.block #[⟨2, 3, (.cmp .lt (.inst 0) (.int 0 (48 : Int)))⟩,
    ⟨3, 3, (.block #[⟨4, 4, (.condBr (.inst 2) #[⟨5, 4, (.br 3 (.bool true))⟩] #[⟨6, 3, (.cmp .gt (.inst 0) (.int 0 (57 : Int)))⟩,
    ⟨7, 4, (.br 3 (.inst 6))⟩])⟩])⟩,
    ⟨8, 4, (.condBr (.inst 3) #[⟨15, 2, (.line 2)⟩,
    ⟨9, 4, (.ret (.errUnionErr 1 "NotDigit"))⟩] #[⟨10, 4, (.br 1 .void)⟩])⟩])⟩,
    ⟨16, 2, (.line 3)⟩,
    ⟨11, 0, (.arith .sub .checked (.inst 0) (.int 0 (48 : Int)))⟩,
    ⟨17, 2, (.line 3)⟩,
    ⟨12, 1, (.wrapErrPayload (.inst 11))⟩,
    ⟨13, 4, (.ret (.inst 12))⟩] }

theorem callee_0 : panicOf? "errors.parseDigit" = none := rfl

/-- The certified functions, by fully qualified name. -/
def table : Table := [
  ("errors.digitOrZero", air_digitOrZero),
  ("errors.parseDigit", air_parseDigit)]

/-- The generated definitions as a call oracle (arguments decoded by type). -/
def gen : Oracle
  | "errors.digitOrZero", args =>
    StateT.lift ((fun v => (Value.int false 8 v)) <$> Errors.digitOrZero ((args.getD 0 .void).toBV 8))
  | "errors.parseDigit", args =>
    StateT.lift ((fun v => (Value.ofExcept (fun x => (Value.int false 8 x)) v)) <$> Errors.parseDigit ((args.getD 0 .void).toBV 8))
  | _, _ => StateT.lift stuck

/-- `errors.digitOrZero`: the AIR semantics of the decoded function, with the generated program answering its calls, equals the generated definition. -/
theorem digitOrZero_step (p0 : BitVec 8) (m : Zig.Mem) :
    (execFunc gen air_digitOrZero [(Value.int false 8 p0)]).run m =
      (fun v => ((Value.int false 8 v), m)) <$> Errors.digitOrZero p0 := by
  conv => rhs; rw [Errors.digitOrZero]
  simp only [air_digitOrZero, air_sem, callee_0, gen]

theorem digitOrZero_fix (args : List Value)
    (h : argsOk air_digitOrZero air_digitOrZero.params.toList args = true) :
    execFunc gen air_digitOrZero args = gen "errors.digitOrZero" args := by
  replace h : argsOk air_digitOrZero [0] args = true := h
  obtain ⟨v0, args, rfl, h0, h⟩ := argsOk_cons h
  obtain rfl := argsOk_nil h
  replace h0 : valOk (.int false 8) v0 = true := h0
  rw [valOk_int h0]
  funext m
  show (execFunc gen air_digitOrZero _).run m = (gen _ _).run m
  rw [digitOrZero_step (v0.toBV 8)]
  simp only [gen, air_sem]

/-- `errors.parseDigit`: the AIR semantics of the decoded function (under any call oracle) equals the generated definition. -/
theorem parseDigit_step (call : Oracle) (p0 : BitVec 8) (m : Zig.Mem) :
    (execFunc call air_parseDigit [(Value.int false 8 p0)]).run m =
      (fun v => ((Value.ofExcept (fun x => (Value.int false 8 x)) v), m)) <$> Errors.parseDigit p0 := by
  conv => rhs; rw [Errors.parseDigit]
  simp only [air_parseDigit, air_sem]

theorem parseDigit_fix (args : List Value)
    (h : argsOk air_parseDigit air_parseDigit.params.toList args = true) :
    execFunc gen air_parseDigit args = gen "errors.parseDigit" args := by
  replace h : argsOk air_parseDigit [0] args = true := h
  obtain ⟨v0, args, rfl, h0, h⟩ := argsOk_cons h
  obtain rfl := argsOk_nil h
  replace h0 : valOk (.int false 8) v0 = true := h0
  rw [valOk_int h0]
  funext m
  show (execFunc gen air_parseDigit _).run m = (gen _ _).run m
  rw [parseDigit_step gen (v0.toBV 8)]
  simp only [gen, air_sem]

/-- The generated program satisfies every certified function's AIR equation. -/
theorem gen_fixpoint : Fixpoint gen table :=
  ⟨digitOrZero_fix, parseDigit_fix, trivial⟩

/-- The AIR semantics of the certified program (`Sem.run`, the least fixpoint) is below the
generated program: every terminating AIR behaviour is the generated definition's. -/
theorem run_le_gen : Lean.Order.PartialOrder.rel (run (progOf table)) gen :=
  run_le_of_table gen_fixpoint

/-- `errors.parseDigit` makes no certified call: its AIR semantics equals the generated definition. -/
theorem parseDigit_run (p0 : BitVec 8) (m : Zig.Mem) :
    (run (progOf table) "errors.parseDigit" [(Value.int false 8 p0)]).run m =
      (fun v => ((Value.ofExcept (fun x => (Value.int false 8 x)) v), m)) <$> Errors.parseDigit p0 := by
  rw [run_of_lookup (by rfl)]
  exact parseDigit_step _ p0 m

theorem parseDigit_complete (p0 : BitVec 8) (m : Zig.Mem) :
    Lean.Order.PartialOrder.rel ((fun v => ((Value.ofExcept (fun x => (Value.int false 8 x)) v), m)) <$> Errors.parseDigit p0)
      ((run (progOf table) "errors.parseDigit" [(Value.int false 8 p0)]).run m) :=
  rel_of_eq (parseDigit_run p0 m).symm

/-- `errors.digitOrZero`: every terminating AIR run is the generated definition's. -/
theorem digitOrZero_sound (p0 : BitVec 8) (m : Zig.Mem) :
    Lean.Order.PartialOrder.rel ((run (progOf table) "errors.digitOrZero" [(Value.int false 8 p0)]).run m)
      ((fun v => ((Value.int false 8 v), m)) <$> Errors.digitOrZero p0) := by
  have h : Lean.Order.PartialOrder.rel ((run (progOf table) "errors.digitOrZero" [(Value.int false 8 p0)]).run m)
      ((gen "errors.digitOrZero" [(Value.int false 8 p0)]).run m) := run_le_gen "errors.digitOrZero" [(Value.int false 8 p0)] m
  simp only [gen, air_sem] at h
  exact h

/-- `errors.digitOrZero`'s certified callees, answered by the given functions. -/
def calls_digitOrZero (g_parseDigit : BitVec 8 → Zig.Result (Except Zig.ErrName (BitVec 8))) : Oracle
  | "errors.parseDigit", args =>
    if argsOk air_parseDigit air_parseDigit.params.toList args then
      StateT.lift ((fun v => (Value.ofExcept (fun x => (Value.int false 8 x)) v)) <$> g_parseDigit ((args.getD 0 .void).toBV 8))
    else StateT.lift stuck
  | _, _ => StateT.lift stuck

/-- `errors.digitOrZero`: the generated definition terminates only as the AIR does: it is below `run`. -/
theorem digitOrZero_complete (p0 : BitVec 8) (m : Zig.Mem) :
    Lean.Order.PartialOrder.rel ((fun v => ((Value.int false 8 v), m)) <$> Errors.digitOrZero p0)
      ((run (progOf table) "errors.digitOrZero" [(Value.int false 8 p0)]).run m) := by
  rw [run_of_lookup (by rfl)]
  apply Lean.Order.PartialOrder.rel_trans (y := (execFunc (calls_digitOrZero Errors.parseDigit) air_digitOrZero [(Value.int false 8 p0)]).run m)
  · apply rel_of_eq
    conv => lhs; rw [Errors.digitOrZero]
    simp only [air_sem, air_digitOrZero, calls_digitOrZero, air_parseDigit, callee_0]
  · apply execFunc_le
    intro name args m'
    show Lean.Order.PartialOrder.rel (((calls_digitOrZero Errors.parseDigit) name args).run m') ((run (progOf table) name args).run m')
    unfold calls_digitOrZero
    split
    · split
      · rename_i h
        replace h : argsOk air_parseDigit [0] args = true := h
        obtain ⟨v0, args, rfl, h0, h⟩ := argsOk_cons h
        obtain rfl := argsOk_nil h
        replace h0 : valOk (.int false 8) v0 = true := h0
        rw [valOk_int h0]
        have := parseDigit_complete (v0.toBV 8) m'
        simp only [air_sem] at this ⊢
        exact this
      · exact Lean.Order.FlatOrder.rel.bot
    · exact Lean.Order.FlatOrder.rel.bot

/-- `errors.digitOrZero`: its AIR semantics equals the generated definition. -/
theorem digitOrZero_eq (p0 : BitVec 8) (m : Zig.Mem) :
    (run (progOf table) "errors.digitOrZero" [(Value.int false 8 p0)]).run m =
      (fun v => ((Value.int false 8 v), m)) <$> Errors.digitOrZero p0 :=
  Lean.Order.PartialOrder.rel_antisymm (digitOrZero_sound p0 m) (digitOrZero_complete p0 m)

end Errors.AirCert
