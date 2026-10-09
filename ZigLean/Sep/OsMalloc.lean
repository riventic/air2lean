import ZigLean.Os.Malloc
import ZigLean.Sep.Alloc

/-!
# Separation-logic rules for macOS `malloc`/`free` (premise OSM-02; proof-only)

The rules of the libc allocator model (`ZigLean/Os/Malloc.lean`, `docs/os-threads.md`). A
`malloc` gives a new heap block that nothing else owns, of at least the requested size and
16-byte aligned, or `null` and no bytes, for every failure policy and every slack
(`Triple.malloc`). `free` takes back the whole block (`Triple.mfree`); `free(null)` does nothing.
A `free` of a dead block — a double free — is `.illegal` (`Os.Darwin.free_dead`), as are the
kernel-checked cases below. The module is not imported by `ZigLean.lean`:
`lake build ZigLean.Sep.OsMalloc`.
-/

namespace Zig

open Assn Os

/-- What `malloc(n)` returns: `null` and no bytes, or a block of `S ≥ n` undefined bytes at a
16-byte-aligned address, owned from offset 0. -/
def mallocPost (n : Nat) : Option Ptr → Assn
  | none => emp
  | some p => fun h => p.off = 0 ∧ ∃ S A, n ≤ S ∧ A % Darwin.mallocAlign = 0 ∧
      bytesAt p A S .heap (Array.replicate S .undef) h

theorem Os.Darwin.malloc_eq (env : Env) (n : BitVec 64) (m : Mem) :
    (Darwin.malloc env n).run m =
      (rawAlloc (n.toNat + env.mallocSlack m.allocs n.toNat) Darwin.mallocAlign).run m := rfl

theorem Triple.malloc (env : Env) (n : BitVec 64) :
    Triple emp (Darwin.malloc env n) (mallocPost n.toNat) :=
  Triple.of_run fun m hP hF hd hm hp hst => by
    have hP0 : hP = Heap.empty := hp
    subst hP0
    obtain ⟨r, m', hr, hst', -, hpost⟩ :=
      rawAlloc_run hd hm (n.toNat + env.mallocSlack m.allocs n.toNat) Darwin.mallocAlign
        (by decide) hst
    rw [← Darwin.malloc_eq] at hr
    cases r with
    | none => exact ⟨none, m', Heap.empty, hr, hd, hpost, rfl, hst'⟩
    | some p =>
      obtain ⟨h0, h', hd', hm', -, A, hA, hb, -⟩ := hpost
      simp only [Heap.empty_union] at hd' hm'
      exact ⟨some p, m', h', hr, hd', hm', ⟨h0, _, A, Nat.le_add_right _ _, hA, hb⟩, hst'⟩

/-- An owned whole heap block is what `free` looks up. -/
theorem Os.Darwin.heapBlockAt_of {m : Mem} {h hF : Heap} {p : Ptr} {A S : Nat} {bs : Array Byte}
    (hb : bytesAt p A S .heap bs h) (hm : m.heap = h ∪ hF) (hS : bs.size = S) (h0 : p.off = 0)
    (hpos : 0 < S) :
    ∃ blk, (Darwin.heapBlockAt p).run m = pure (blk, m) ∧ blk.bytes.size = S := by
  obtain ⟨b, blk, hacc, hK, hsz⟩ := heapBlock_access hb hm hS hpos
  obtain ⟨hpb, hblk, hl, -⟩ := access_eq hacc
  exact ⟨blk, by simp [Darwin.heapBlockAt, zig_unfold, hpb, hblk, hl, hK, h0], hsz⟩

theorem Triple.mfree {p : Ptr} {A S : Nat} {bs : Array Byte} (hS : bs.size = S) (h0 : p.off = 0)
    (hpos : 0 < S) : Triple (bytesAt p A S .heap bs) (Darwin.free (some p)) (fun _ => emp) :=
  Triple.of_run fun m _ hF hd hm hb hst => by
    obtain ⟨blk, hblk, hsz⟩ := Darwin.heapBlockAt_of hb hm hS h0 hpos
    obtain ⟨m', hr, hm', hst', -⟩ := poisonFree_run hb hm hd hS h0 hpos hst
    refine ⟨(), m', Heap.empty, ?_, (Heap.disjoint_empty hF).symm, hm', rfl, hst'⟩
    simp only [StateT.run] at hblk hr
    simp [Darwin.free, zig_unfold, hblk, hsz, hr]

theorem Triple.mfreeNull : Triple emp (Darwin.free none) (fun _ => emp) :=
  Triple.of_run fun m _ hF hd hm hp hst => ⟨(), m, Heap.empty, rfl, hp ▸ hd, hp ▸ hm, rfl, hst⟩

/-- `free` of a pointer into a dead block (a double free, a free after a free) is `.illegal`. -/
theorem Os.Darwin.free_dead {m : Mem} {p : Ptr} {b : BlockId} {blk : Block} (hb : p.block = some b)
    (hblk : m.blocks[b]? = some blk) (hl : blk.live = false) :
    ((Darwin.free (some p)).run m).run = some (.error .illegal) := by
  simp [Darwin.free, Darwin.heapBlockAt, zig_unfold, hb, hblk, hl, ExceptT.run]

/-- `free` of a pointer that is not at offset 0 of its block is `.illegal`. -/
theorem Os.Darwin.free_inner {m : Mem} {p : Ptr} (h0 : p.off ≠ 0) :
    ((Darwin.free (some p)).run m).run = some (.error .illegal) := by
  simp only [Darwin.free, Darwin.heapBlockAt]
  cases hb : p.block with
  | none => simp [zig_unfold, ExceptT.run]
  | some b =>
    cases hblk : m.blocks[b]? with
    | none => simp [zig_unfold, hblk, ExceptT.run]
    | some blk => simp [zig_unfold, hblk, h0, ExceptT.run]

/-! ## Kernel-checked examples (`aarch64-macos`) -/

namespace OsMallocExamples

def isIllegal {α : Type} (c : MemM α) : Bool :=
  match (c.run {}).run with
  | some (.error .illegal) => true
  | _ => false

def returns {α : Type} (c : MemM α) : Bool :=
  match (c.run {}).run with
  | some (.ok _) => true
  | _ => false

def malloc8 : MemM Ptr := do
  match ← Darwin.malloc Env.example 8 with
  | some p => pure p
  | none => throw .panic

/-- A store into a fresh block returns. -/
example : returns (do let p ← malloc8; store 1 (p.add 7) (1 : BitVec 8)) = true := by decide +kernel

/-- A double free is illegal. -/
example : isIllegal (do let p ← malloc8; Darwin.free (some p); Darwin.free (some p)) = true := by
  decide +kernel

/-- Use after free is illegal. -/
example : isIllegal (do let p ← malloc8; Darwin.free (some p); load (BitVec 8) 1 p) = true := by
  decide +kernel

/-- Freeing an inner pointer, or a stack block, is illegal. -/
example : isIllegal (do let p ← malloc8; Darwin.free (some (p.add 1))) = true := by decide +kernel
example : isIllegal (do let p ← alloc .stack 8 8; Darwin.free (some p)) = true := by decide +kernel

end OsMallocExamples

end Zig
