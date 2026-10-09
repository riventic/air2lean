import ZigLean

/-! Fail-open emitter placeholders (docs/architecture-audit/memory-model.md, MM-6).

`Air2Lean/Emit.lean` writes `(panic! "air2lean: …")` (17 sites) and `pure default` (2 sites)
where it assumes `Check.lean` already rejected the input. In the logic, `panic! msg` is
`default`, and `default : Zig.MemM α` is a successful return of `default` with the memory
unchanged. A checker gap therefore yields a translation whose theorems treat the unsupported
operation as a no-op that succeeds, not as an error. (`default : Zig.Result α` is
`.error .overflow`, which is wrong in the other direction: an arbitrary error.) -/

theorem panic_is_default (msg : String) :
    (panic! msg : Zig.MemM (BitVec 8)) = (default : Zig.MemM (BitVec 8)) := by rfl

theorem default_memM_succeeds (m : Zig.Mem) :
    ((default : Zig.MemM (BitVec 8)).run m).run = some (.ok (0, m)) := by rfl

theorem panic_memM_succeeds (msg : String) (m : Zig.Mem) :
    (((panic! msg : Zig.MemM (BitVec 8))).run m).run = some (.ok (0, m)) := by rfl

theorem default_result_is_overflow :
    (default : Zig.Result (BitVec 8)).run = some (.error .overflow) := by rfl

/-- A placeholder pointer value is the provenance-free address 0. -/
theorem panic_ptr_is_null (msg : String) : (panic! msg : Zig.Ptr) = ⟨none, 0⟩ := by rfl
