import ZigLean.Sep.Full.Toy
import ZigLean.Sep.Full.Logic
import ZigLean.Sep.Full.AutoAttr

/-!
# Blocks in the full-state logic (`docs/proof-framework.md`, library `Full/Block`)

Step rules for `fsym` about making and ending blocks:

* `FTotalTriple.free`: `free` of a whole block (its bytes and its full extent `bext`) returns and
  leaves nothing (total).
* `FTriple.alloc`, `FTriple.allocStack`: a new block of `size > 0` bytes: its bytes (undefined),
  its full extent and an aligned address. These are partial: `alloc` throws `.stackOverflow`
  when the address space has no room (`Mem.roomFor`, premise STK-01), which a partial triple
  counts as no result. A total rule needs the room as a resource of the precondition: that
  resource does not exist yet (docs/proof-framework.md: "stack room").
-/

namespace Zig
namespace Full

open FAssn

/-- `free` returns from every memory that holds a whole block with its full extent. -/
theorem FReturns.free {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte} {b : BlockId}
    (hpb : p.block = some b) (hS : bs.size = S) (h0 : p.off = 0) (hpos : 0 < S) :
    FReturns (up (bytesAt p A S K bs) ⋆ bext b S K) (Zig.free p) := by
  intro m r rF hh hp hs
  have hcells : ∀ h, bytesAt p A S K bs h → ∀ l c, h l = some c → l.1 = b ∧ c.size = S ∧ c.kind = K := by
    intro h hb l c hc
    obtain ⟨b', hb', -, hl⟩ := hb
    rw [hpb] at hb'; cases hb'
    rw [hl l] at hc
    split at hc
    · rename_i hin; cases hc; exact ⟨hin.1, rfl, rfl⟩
    · cases hc
  have hP := upE_fix (E := fun x => if x = b then some (S, K) else none)
    (SizeFree.of_pinned fun h hp l c hc => by simp [(hcells h hp l c hc).1])
    (fun h hp l c S' K' hc hE => by
      obtain ⟨e, hs', hk⟩ := hcells h hp l c hc
      simp only [e, ite_true, Option.some.injEq, Prod.mk.injEq] at hE
      exact ⟨hE.1 ▸ hs', hE.2 ▸ hk⟩) hh (up_sep_bext hp)
  obtain ⟨m', hr, -⟩ := free_run hP (hh.fix.heap_exact hh.fix_exact hh.fix_exactF)
    (FHeap.erase_disjoint (FHeap.fix_disjoint hh.disj)) hS h0 hpos hs.1
  exact ⟨(), m', hr⟩

/-- **`free` of a whole block** (total): its bytes and its full extent go. -/
@[fsym] theorem FTotalTriple.free {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte}
    {b : BlockId} (hpb : p.block = some b) (hS : bs.size = S) (h0 : p.off = 0) (hpos : 0 < S) :
    FTotalTriple (up (bytesAt p A S K bs) ⋆ bext b S K) (Zig.free p) (fun _ => emp) :=
  ⟨FTriple.free' hpb hS h0 hpos, FReturns.free hpb hS h0 hpos⟩

/-- **`alloc` of `size > 0` bytes** (partial: no room is a stack overflow): the bytes, the full
extent of the new block and an aligned address. -/
@[fsym] theorem FTriple.alloc (kind : BlockKind) (size align : Nat) (ha : 0 < align)
    (hpos : 0 < size) (hk : kind.mappedLo = 0) :
    FTriple emp (Zig.alloc kind size align) (fun p => FAssn.ex fun A : Nat => FAssn.ex fun b : BlockId =>
      ⟪p.block = some b ∧ p.off = 0 ∧ A % align = 0⟫ ⋆
        (up (bytesAt p A size kind (Array.replicate size .undef)) ⋆ bext b size kind)) :=
  FTriple.alloc' kind size align ha hpos hk

/-- **The stack block of an escaping local** (`allocStack`, partial as `FTriple.alloc`). -/
@[fsym] theorem FTriple.allocStack (size align : Nat) (ha : 0 < align) (hpos : 0 < size) :
    FTriple emp (Zig.allocStack size align) (fun p => FAssn.ex fun A : Nat => FAssn.ex fun b : BlockId =>
      ⟪p.block = some b ∧ p.off = 0 ∧ A % align = 0⟫ ⋆
        (up (bytesAt p A size .stack (Array.replicate size .undef)) ⋆ bext b size .stack)) :=
  FTriple.alloc .stack size align ha hpos rfl

end Full
end Zig
