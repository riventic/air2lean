import Lean.Meta.Tactic.Simp.RegisterCommand

/-- Simp set that unfolds the `StateT`/`ExceptT`/`Option` layers of generated code down to plain
values. Use it as `simp [zig_unfold, …]`. The lemmas are added in `ZigLean.Simp`: a simp set
can only get attributes in a file after the one that declares it. -/
register_simp_attr zig_unfold
