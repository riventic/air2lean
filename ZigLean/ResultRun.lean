import ZigLean.Basic

/-!
# `Result` values from their `run`

Facts about bytes and loads are stated as `x.run = some (.ok a)` (a `Zig.Result` that succeeded
with `a`). The proofs then need `x = pure a`, to rewrite `x` in a goal. The two are definitionally
equal, but a bare `have h' : x = pure a := h` makes the elaborator unify them by unfolding
`ExceptT.run` on the whole term of `x`: for `x := intOfBytes 32 (bs.extract 20 24)` this took 0.7 to
2 s per use, growing with the context (Threadsync.WaitGroup `tally_decode`, 5.7 s for four uses,
`docs/perf-budgets.md`). These lemmas state the step once, at a variable `x`, so a use is
instantaneous.
-/

namespace Zig

theorem Result.eq_pure_of_run {α : Type} {x : Result α} {a : α} (h : x.run = some (.ok a)) :
    x = pure a := h

theorem Result.run_of_eq_pure {α : Type} {x : Result α} {a : α} (h : x = pure a) :
    x.run = some (.ok a) := by rw [h]; rfl

theorem Result.run_eq_some_ok {α : Type} {x : Result α} {a : α} :
    x.run = some (.ok a) ↔ x = pure a :=
  ⟨Result.eq_pure_of_run, Result.run_of_eq_pure⟩

end Zig
