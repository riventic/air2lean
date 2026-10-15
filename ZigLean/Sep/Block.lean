import ZigLean.Sep.Triple
import ZigLean.Sep.Base.Block

/-!
# `alloc` and `free` triples (legacy logic)

The legacy `Triple` rules of `alloc` and `free`. Their run lemmas (`alloc_run`, `free_run`) and
`Mem.SameThreads` are vocabulary of both logics (`ZigLean/Sep/Base/Block.lean`). This module is
deleted with the legacy layer (`docs/proof-framework.md`).
-/

namespace Zig

open Assn

theorem Triple.alloc (kind : BlockKind) (size align : Nat) (ha : 0 < align)
    (hk : kind.mappedLo = 0 := by first | rfl | simp_all [BlockKind.mappedLo]) :
    Triple emp (alloc kind size align) (fun p => Assn.ex fun A =>
      ⌜p.off = 0 ∧ A % align = 0⌝ ∗ bytesAt p A size kind (Array.replicate size .undef)) :=
  fun m hP _ hd hm hp hst => by
    cases hroom : m.allocOk kind size align
    · rw [alloc_run_noRoom m hroom]; try trivial
    obtain ⟨p, m', h', hr, h0, hd', hm', -, hst', -, A, hA, hb, -⟩ :=
      alloc_run hd hm kind size align ha hroom hst hk
    have hP0 : hP = Heap.empty := hp
    subst hP0
    simp only [Heap.empty_union] at hd' hm'
    rw [hr]
    exact ⟨h', hd', hm', ⟨A, sep_lift.mpr ⟨⟨h0, hA⟩, hb⟩⟩, hst'⟩

theorem Triple.free {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte} (hS : bs.size = S)
    (h0 : p.off = 0)
    (hpos : 0 < S) (hK : K ≠ .constGlobal := by decide) :
    Triple (bytesAt p A S K bs) (free p) (fun _ => emp) :=
  Triple.of_run fun _ _ hF hd hm hb hst => by
    obtain ⟨m', hr, hm', hst', -⟩ := free_run hb hm hd hS h0 hpos hst hK
    exact ⟨(), m', Heap.empty, hr, (Heap.disjoint_empty hF).symm, hm', rfl, hst'⟩

end Zig
