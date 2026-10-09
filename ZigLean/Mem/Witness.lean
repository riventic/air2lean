import ZigLean.Mem.Lemmas
import ZigLean.Witness

/-!
# Concrete memories for claim witnesses

`nonvacuity_witness` and `liveness_witness` (`ZigLean/Witness.lean`) ask for concrete arguments
that satisfy a theorem's premises. `Witness.mem1 bs` is a memory with one live block `0` that
holds the bytes `bs` at address 4096 (aligned to every power of two up to 4096), one thread and
an empty footprint, and `Witness.p0` points to its first byte. Facts about a concrete memory,
such as `(mem1 bs).access p0 4 4 = pure (0, blk bs, 0)`, are closed by evaluation
(`with_unfolding_all rfl` or `decide +kernel`), which the kernel checks.
-/

namespace Zig.Witness

/-- The block of `mem1 bs`. -/
def blk (bs : Array Byte) (kind : BlockKind := .heap) : Block :=
  { bytes := bs, align := 16, kind, live := true, addr := 4096 }

/-- One live block `0` with the bytes `bs` at address 4096; nothing else allocated. -/
def mem1 (bs : Array Byte) (kind : BlockKind := .heap) : Mem :=
  { blocks := #[blk bs kind], nextAddr := 4096 + bs.size + 1 }

/-- Two live blocks: `0` with the bytes `bs₁` at address 4096 and `1` with `bs₂` at 8192. -/
def mem2 (bs₁ bs₂ : Array Byte) (k₁ k₂ : BlockKind := .heap) : Mem :=
  { blocks := #[blk bs₁ k₁, { blk bs₂ k₂ with addr := 8192 }], nextAddr := 8192 + bs₂.size + 1 }

/-- The first byte of block `0`. -/
def p0 : Ptr := ⟨some 0, 0⟩

/-- The first byte of block `1`. -/
def p1 : Ptr := ⟨some 1, 0⟩

/-- A declared error domain with the one error `A`. -/
def domA : ErrorDomain := ⟨#["A"], by decide, by decide⟩

theorem mem1_access {bs : Array Byte} {kind : BlockKind} {o n a : Nat} (hn : o + n ≤ bs.size)
    (ha : (4096 + o) % a = 0) :
    (mem1 bs kind).access (p0.add o) n a = pure (0, blk bs kind, o) := by
  have hle : ((o : Int) + n) ≤ (bs.size : Int) := by omega
  simp [Mem.access, mem1, p0, Ptr.add, blk, hle, ha]

theorem mem1_noRace (bs : Array Byte) (kind : BlockKind) (b o n : Nat) (k : AccessKind) :
    NoRace (mem1 bs kind) b o n k :=
  noRace_of_singleThread (singleThread_empty rfl Nat.zero_lt_one) b o n k

end Zig.Witness
