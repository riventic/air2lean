-- air2lean AIR semantics certificate (docs/air-semantics.md). Generated; do not edit.
import Air2Lean.Sem
import Proofs.Threads.Gen

namespace Threads.AirCert

open Air2Lean Air2Lean.Sem

/-! Certified: `threads.writeFlag`

Outside the certificate fragment:

* `atomic.Value(threads.Phase).init`: a parameter that is not an integer, bool or plain pointer
* `atomic.Value(u32).init`: a return type that is not an integer, bool, plain pointer or void
* `threads.bump`: a concurrent function (`Zig.ConcM`)
* `threads.claim`: a concurrent function (`Zig.ConcM`)
* `threads.claimOnce`: a concurrent function (`Zig.ConcM`)
* `threads.disjoint`: a concurrent function (`Zig.ConcM`)
* `threads.parallelCounter`: a concurrent function (`Zig.ConcM`)
* `threads.race`: a concurrent function (`Zig.ConcM`)
* `threads.swapFlag`: a concurrent function (`Zig.ConcM`)
* `threads.xchgRace`: a concurrent function (`Zig.ConcM`)
-/

/-- The decoded canonical AIR of `threads.writeFlag`. -/
def air_writeFlag : Func :=
{ zigVersion := "0.16.0", name := "threads.writeFlag",
  params := #[0], ret := 1,
  types := #[(.ptr "one" false 8), .void, (.ptr "one" false 0), (.ptr "one" true 0), (.ptr "one" false 5), (.ptr "one" false 6), (.int false 32), .noreturn, (.struct "threads.RaceCtx" "auto" #[("flag", 5), ("val", 6)])],
  layouts := #[{ size := (some 8), align := (some 8), offsets := #[], ptrAlign := (some 8), sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 0), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 8), align := (some 8), offsets := #[], ptrAlign := (some 8), sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 8), align := (some 8), offsets := #[], ptrAlign := (some 8), sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 8), align := (some 8), offsets := #[], ptrAlign := (some 8), sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 8), align := (some 8), offsets := #[], ptrAlign := (some 4), sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 4), align := (some 4), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := none, align := none, offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 16), align := (some 8), offsets := #[0, 8], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }],
  globals := #[],
  errorSetBits := 16,
  body := #[⟨0, 0, (.arg 0)⟩,
    ⟨7, 1, (.line 2)⟩,
    ⟨1, 4, (.fieldPtr (.inst 0) 0)⟩,
    ⟨2, 5, (.load (.inst 1))⟩,
    ⟨8, 1, (.line 2)⟩,
    ⟨3, 5, (.fieldPtr (.inst 0) 1)⟩,
    ⟨4, 6, (.load (.inst 3))⟩,
    ⟨5, 1, (.store (.inst 2) (.inst 4))⟩,
    ⟨6, 7, (.ret .void)⟩] }

/-- The certified functions, by fully qualified name. -/
def table : Table := [
  ("threads.writeFlag", air_writeFlag)]

/-- The generated definitions as a call oracle (arguments decoded by type). -/
def gen : Oracle
  | "threads.writeFlag", args =>
    (fun v => Value.void) <$> Threads.writeFlag ((args.getD 0 .void).toPtr)
  | _, _ => StateT.lift stuck


/-- `threads.writeFlag`: the AIR semantics of the decoded function (under any call oracle) equals the generated definition. -/
theorem writeFlag_step (call : Oracle) (p0 : Zig.Ptr) (m : Zig.Mem) :
    (execFunc call air_writeFlag [(Value.ptr p0)]).run m =
      (fun r => (Value.void, r.2)) <$> (Threads.writeFlag p0).run m := by
  conv => rhs; rw [Threads.writeFlag]
  simp only [air_writeFlag, air_sem]

theorem writeFlag_fix (args : List Value)
    (h : argsOk air_writeFlag air_writeFlag.params.toList args = true) :
    execFunc gen air_writeFlag args = gen "threads.writeFlag" args := by
  replace h : argsOk air_writeFlag [0] args = true := h
  obtain ⟨v0, args, rfl, h0, h⟩ := argsOk_cons h
  obtain rfl := argsOk_nil h
  replace h0 : valOk (.ptr "one" false 8) v0 = true := h0
  rw [valOk_ptr h0]
  funext m
  show (execFunc gen air_writeFlag _).run m = (gen _ _).run m
  rw [writeFlag_step gen v0.toPtr]
  simp only [gen, air_sem]

/-- The generated program satisfies every certified function's AIR equation. -/
theorem gen_fixpoint : Fixpoint gen table :=
  ⟨writeFlag_fix, trivial⟩

/-- The AIR semantics of the certified program (`Sem.run`, the least fixpoint) is below the
generated program: every terminating AIR behaviour is the generated definition's. -/
theorem run_le_gen : Lean.Order.PartialOrder.rel (run (progOf table)) gen :=
  run_le_of_table gen_fixpoint

/-- `threads.writeFlag` makes no certified call: its AIR semantics equals the generated definition. -/
theorem writeFlag_run (p0 : Zig.Ptr) (m : Zig.Mem) :
    (run (progOf table) "threads.writeFlag" [(Value.ptr p0)]).run m =
      (fun r => (Value.void, r.2)) <$> (Threads.writeFlag p0).run m := by
  rw [run_of_lookup (by rfl)]
  exact writeFlag_step _ p0 m

theorem writeFlag_complete (p0 : Zig.Ptr) (m : Zig.Mem) :
    Lean.Order.PartialOrder.rel ((fun r => (Value.void, r.2)) <$> (Threads.writeFlag p0).run m)
      ((run (progOf table) "threads.writeFlag" [(Value.ptr p0)]).run m) :=
  rel_of_eq (writeFlag_run p0 m).symm

end Threads.AirCert
