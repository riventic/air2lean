import Lean

/-! The simp set that normalizes `Air2Lean.Sem` on a concrete function (`Air2Lean/Sem.lean`'s
certificate lemmas, `docs/air-semantics.md`). Declared apart from its use: an attribute is
usable only in a module after the one that declares it. -/

register_simp_attr air_sem
