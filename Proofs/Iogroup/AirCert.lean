-- air2lean AIR semantics certificate (docs/air-semantics.md). Generated; do not edit.
import Air2Lean.Sem
import Proofs.Iogroup.Gen

namespace Iogroup.AirCert

open Air2Lean Air2Lean.Sem

/-! Certified: `debug.assert`

Outside the certificate fragment:

* `Io.Mutex.lock`: a concurrent function (`Zig.ConcM`)
* `Io.Mutex.lockUncancelable`: a concurrent function (`Zig.ConcM`)
* `Io.Mutex.tryLock`: a concurrent function (`Zig.ConcM`)
* `Io.Mutex.unlock`: a concurrent function (`Zig.ConcM`)
* `iogroup.add`: a concurrent function (`Zig.ConcM`)
* `iogroup.groupConcurrent`: a concurrent function (`Zig.ConcM`)
* `iogroup.groupCounter`: a concurrent function (`Zig.ConcM`)
-/

/-- The decoded canonical AIR of `debug.assert`. -/
def air_debug_assert : Func :=
{ zigVersion := "0.16.0", name := "debug.assert",
  params := #[0], ret := 1,
  types := #[.bool, .void, .noreturn, (.other "fn () noreturn")],
  layouts := #[{ size := (some 1), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 0), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := none, align := none, offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := none, align := none, offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }],
  globals := #[],
  errorSetBits := 16,
  body := #[⟨0, 0, (.arg 0)⟩,
    ⟨8, 1, (.line 3)⟩,
    ⟨1, 1, (.block #[⟨2, 0, (.not (.inst 0))⟩,
    ⟨3, 2, (.condBr (.inst 2) #[⟨9, 1, (.line 3)⟩,
    ⟨4, 2, (.call (.func "debug.FullPanic((function 'defaultPanic')).reachedUnreachable" true none) #[])⟩,
    ⟨5, 2, .unreach⟩] #[⟨6, 2, (.br 1 .void)⟩])⟩])⟩,
    ⟨7, 2, (.ret .void)⟩] }

/-- The certified functions, by fully qualified name. -/
def table : Table := [
  ("debug.assert", air_debug_assert)]

/-- The generated definitions as a call oracle (arguments decoded by type). -/
def gen : Oracle
  | "debug.assert", args =>
    StateT.lift ((fun v => Value.void) <$> Iogroup.debug_assert ((args.getD 0 .void).toBool))
  | _, _ => StateT.lift stuck

theorem callee_0 : panicOf? "debug.FullPanic((function 'defaultPanic')).reachedUnreachable" = some .unreachable := rfl

/-- `debug.assert`: the AIR semantics of the decoded function (under any call oracle) equals the generated definition. -/
theorem debug_assert_step (call : Oracle) (p0 : Bool) (m : Zig.Mem) :
    (execFunc call air_debug_assert [(Value.bool p0)]).run m =
      (fun v => (Value.void, m)) <$> Iogroup.debug_assert p0 := by
  conv => rhs; rw [Iogroup.debug_assert]
  simp only [air_debug_assert, air_sem, callee_0]

theorem debug_assert_fix (args : List Value)
    (h : argsOk air_debug_assert air_debug_assert.params.toList args = true) :
    execFunc gen air_debug_assert args = gen "debug.assert" args := by
  replace h : argsOk air_debug_assert [0] args = true := h
  obtain ⟨v0, args, rfl, h0, h⟩ := argsOk_cons h
  obtain rfl := argsOk_nil h
  replace h0 : valOk .bool v0 = true := h0
  rw [valOk_bool h0]
  funext m
  show (execFunc gen air_debug_assert _).run m = (gen _ _).run m
  rw [debug_assert_step gen v0.toBool]
  simp only [gen, air_sem]

/-- The generated program satisfies every certified function's AIR equation. -/
theorem gen_fixpoint : Fixpoint gen table :=
  ⟨debug_assert_fix, trivial⟩

/-- The AIR semantics of the certified program (`Sem.run`, the least fixpoint) is below the
generated program: every terminating AIR behaviour is the generated definition's. -/
theorem run_le_gen : Lean.Order.PartialOrder.rel (run (progOf table)) gen :=
  run_le_of_table gen_fixpoint

/-- `debug.assert` makes no certified call: its AIR semantics equals the generated definition. -/
theorem debug_assert_run (p0 : Bool) (m : Zig.Mem) :
    (run (progOf table) "debug.assert" [(Value.bool p0)]).run m =
      (fun v => (Value.void, m)) <$> Iogroup.debug_assert p0 := by
  rw [run_of_lookup (by rfl)]
  exact debug_assert_step _ p0 m

theorem debug_assert_complete (p0 : Bool) (m : Zig.Mem) :
    Lean.Order.PartialOrder.rel ((fun v => (Value.void, m)) <$> Iogroup.debug_assert p0)
      ((run (progOf table) "debug.assert" [(Value.bool p0)]).run m) :=
  rel_of_eq (debug_assert_run p0 m).symm

end Iogroup.AirCert
