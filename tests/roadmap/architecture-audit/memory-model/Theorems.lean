-- Appended to the fresh `MemModel` translation of memmodel.zig (check.sh). Each statement is a
-- theorem about the model that the native ReleaseSafe build of the same source violates
-- (native: addrOfLocal is a stack address, eqVsAddr is 3, crossDistance is 8, overAlign panics
-- "incorrect alignment"). `native_decide` evaluates the closed term; any proof method gives
-- the same answer, because the model's addresses are fixed.
private def okIs (x : Zig.MemM α) (p : α → Bool) : Bool :=
  match (x.run' MemModel.mem0).run with
  | some (.ok v) => p v
  | _ => false

theorem addrOfLocal_is_4096 : okIs MemModel.addrOfLocal (· == 4096) = true := by native_decide
theorem eqVsAddr_is_1 : okIs MemModel.eqVsAddr (· == 1) = true := by native_decide
theorem crossDistance_is_9 : okIs MemModel.crossDistance (· == 9) = true := by native_decide
theorem overAlign_never_panics : okIs MemModel.overAlign (· == 2) = true := by native_decide
