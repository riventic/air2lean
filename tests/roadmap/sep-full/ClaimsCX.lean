import ZigLean.Sep.Full.Claims

/-!
# Byte-range claims: regressions (`docs/sep-full-state.md` §Byte-range claims)

1. `overlap_invalid`: a resource that holds two overlapping claims of the root world has an
   invalid ghost state (byte 32 of block 0 would hold the whole fraction twice).
2. `arena_nodes_disjoint`: the obstruction scenario of decision O1 (`docs/alloc-arena.md`) is
   impossible: two arena nodes `[x, x+64)` and `[x+32, x+96)` carved by one child allocator out of
   one buffer, each with the child's claim (tagged with the child's active tag `t`), cannot be
   held together in any memory.

Kernel-checked; the expected axioms are `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Zig.Full.ClaimsCX

open Zig Zig.Full Zig.Full.FAssn

/-- **Two overlapping claims are invalid.** -/
theorem overlap_invalid {r : Res} (h : (bclaim 0 0 64 ⋆ bclaim 0 32 96) r) : ¬ r.gh.Valid := by
  intro hv
  obtain ⟨r₁, r₂, -, rfl, ⟨-, -, g1⟩, ⟨-, -, g2⟩⟩ := h
  have h1 := (hv.2.2.1.1 0 32).1.2.2 1
  simp only [Ghost.add_cl, g1, g2, Ghost.atCl, if_true, ECell.onRange,
    show (0 ≤ 32 ∧ 32 < 64) = True by decide, show (32 ≤ 32 ∧ 32 < 96) = True by decide, and_self,
    if_true, ECell.total, ECell.shareT_none, ECell.share, ECell.add, Frac.add, Frac.one] at h1
  revert h1; grind

/-- **The O1 obstruction is impossible**: nodes `[x, x+64)` and `[x+32, x+96)` of one buffer,
both claimed in the child's active world `t`. -/
theorem arena_nodes_disjoint {m : Mem} {r rF : Res} {R : FAssn} {p : Ptr} {x : Nat} {t : STag}
    (hh : Holds m r rF) (h : (pclaim p x (x + 64) t ⋆ (pclaim p (x + 32) (x + 96) t ⋆ R)) r)
    (ha : Act r.gh.ls t) : False := by
  have := hh.pclaim_disjoint h ha
  omega

end Zig.Full.ClaimsCX

#print axioms Zig.Full.ClaimsCX.overlap_invalid
#print axioms Zig.Full.ClaimsCX.arena_nodes_disjoint
