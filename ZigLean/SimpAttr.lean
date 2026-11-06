import Lean.Meta.Tactic.Simp.RegisterCommand

/-- Simp set that unfolds the `StateT`/`ExceptT`/`Option` layers of generated code down to plain
values. Use it as `simp [zig_unfold, …]`. The lemmas are added in `ZigLean.Simp`: a simp set
can only get attributes in a file after the one that declares it. -/
register_simp_attr zig_unfold

/-- Simp set of the definitions a kernel-computed run unfolds: every executable declaration of
generated code (the translator tags each function, loop body, recursive member by `eq_def`,
model wrapper and `dispatch`), `Zig.loop` (tagged in `ZigLean.Simp`) and the models that hold a
loop (tagged where they are defined: `Zig.osUnfairLockC`, `ZigLean.Conc.Call`). A run witness
uses it as
`iterate n (simp (config := { singlePass := true, unfoldPartialApp := true }) only [zig_run])`
and then `decide +kernel`, naming no generated declaration (docs/proof-automation.md, kernel-run
witnesses). Its rewrites unfold loops and recursive groups without end: use it only with
`singlePass`, and never mix it into `zig_unfold`. -/
register_simp_attr zig_run
