-- Appended to the fresh `MemModel` translation of memmodel.zig (check.sh). Kernel checks
-- (`decide +kernel`, no `native_decide`) that the address-dependent results of MM-1/MM-2 are
-- no longer theorems: `mem0` takes the placement `σ` of every block (`Zig.Placement`), and two
-- valid placements give different results, so none of the old statements holds for every `σ`.
-- The placements below satisfy only what Zig guarantees (`Zig.Mem.placeOk`); natively the
-- addresses are the stack frame's.

/-- The placement that puts block `b` at `a` for each `(b, a)`, every other block fresh. -/
def placeAtK (as : List (Nat × Nat)) : Zig.Placement :=
  ⟨fun b => (as.find? (·.1 == b)).map (·.2)⟩

/-- The result of `x` from `mem0 σ`, if it returns. -/
def okAt (σ : Zig.Placement) (x : Zig.MemM α) : Option (Except Zig.Error α) :=
  (x.run' (MemModel.mem0 σ)).run

-- MM-1: `@intFromPtr` of a local is the placement's address, not a constant.
theorem addrOfLocal_fresh : okAt .fresh MemModel.addrOfLocal = some (.ok 4096) := by
  decide +kernel
theorem addrOfLocal_high : okAt (placeAtK [(0, 8192)]) MemModel.addrOfLocal = some (.ok 8192) := by
  decide +kernel
/-- `addrOfLocal = 4096` (the old `addrOfLocal_is_4096`) is not provable for all placements. -/
theorem addrOfLocal_not_4096 :
    ¬ ∀ σ, okAt σ MemModel.addrOfLocal = some (.ok 4096) := fun h => by
  have := (h (placeAtK [(0, 8192)])).symm.trans addrOfLocal_high
  simp at this

-- MM-1: the distance of two locals is the placement's; the native frame's (8, adjacent) is one of
-- them, so the old `crossDistance = 9` is not provable.
theorem crossDistance_adjacent :
    okAt (placeAtK [(0, 8192), (1, 8200)]) MemModel.crossDistance = some (.ok 8) := by
  decide +kernel
theorem crossDistance_not_9 :
    ¬ ∀ σ, okAt σ MemModel.crossDistance = some (.ok 9) := fun h => by
  have := (h (placeAtK [(0, 8192), (1, 8200)])).symm.trans crossDistance_adjacent
  simp at this

-- MM-1: the order of two locals is the placement's.
theorem crossOrder_lt : okAt .fresh MemModel.crossOrder = some (.ok true) := by decide +kernel
theorem crossOrder_gt :
    okAt (placeAtK [(0, 8192), (1, 4096)]) MemModel.crossOrder = some (.ok false) := by
  decide +kernel

-- MM-2: the over-aligning `@alignCast` panics when the placement does not give the extra
-- alignment, as natively. The old `overAlign_never_panics` is not provable.
theorem overAlign_misaligned :
    okAt (placeAtK [(0, 4097)]) MemModel.overAlign = some (.error .panic) := by
  decide +kernel
theorem overAlign_may_panic :
    ¬ ∀ σ, okAt σ MemModel.overAlign = some (.ok 2) := fun h => by
  have := (h (placeAtK [(0, 4097)])).symm.trans overAlign_misaligned
  simp at this

-- MM-4: `==` compares addresses: two pointers from the same integer are equal also when a block
-- now covers the address (native: 3). Checked under two placements, one where the callee's
-- buffer covers the address.
theorem eqVsAddr_fresh : okAt .fresh MemModel.eqVsAddr = some (.ok 3) := by decide +kernel
theorem eqVsAddr_covered :
    okAt (placeAtK [(0, 8192), (1, 8256)]) MemModel.eqVsAddr = some (.ok 3) := by
  decide +kernel

/-- info: 'addrOfLocal_not_4096' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms addrOfLocal_not_4096
