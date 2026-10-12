import ZigLean.Sep.Full.ThreadOwned

/-!
# Facts of a concurrent proof that do not depend on its protocol

Lemmas that every concurrent client proof needs, once, generic in the spawn shape, the block, its
size and the encoding width (CLAUDE.md "Build generic, prove individual items"). A client's own
invariant supplies the premises (who spawned which thread, which block holds which object).

- **Threads**: a thread that spawned no thread has joined all its threads (`joinedAll_of_spawners`,
  `joinedAll_of_main`, the end of a spawned thread in `Proto.QKid`); a clock below `main`'s, while
  `main` is the only thread, is below every thread's (`allLe_of_one`).
- **Blocks**: `Mem.BlkOk m b S a K` (block `b` live with `S` bytes of kind `K` at an address that is
  a multiple of `a`); its cells are live (`BlkOk.heap`), and a memory with the same cell at one of
  its bytes has the same block (`BlkOk.keep`). In the full-state logic a thread that holds the
  block's full extent (`bext`) in its part pins the block in every memory that holds the parts
  (`FOwned.blkOf`), so the block's facts need not be kept by every step of the protocol.
- **Encodings**: a lawful encoding decodes from the front of its own bytes
  (`LawfulEnc.decode_extract`); its size is `LawfulEnc.size_encode` (`size_encode_u32` at 32 bits).
-/

namespace Zig
namespace Full

open FAssn Conc Proto

/-! ## Threads -/

/-- A thread that spawned no thread has joined all its threads. -/
theorem joinedAll_of_spawners {m : Mem} {u : ThreadId} (h : ∀ r ∈ m.threads, r.spawner ≠ u) :
    joinedAll u m :=
  fun r hr hs => absurd hs (h r hr)

/-- `main` spawned every thread: every other thread has joined all its threads. -/
theorem joinedAll_of_main {m : Mem} {u : ThreadId} (h : ∀ r ∈ m.threads, r.spawner = 0)
    (hu : 0 < u) : joinedAll u m :=
  joinedAll_of_spawners fun r hr e => by rw [h r hr] at e; exact Nat.ne_of_lt hu e

/-- `main` spawned every thread, by the records' indices. -/
theorem spawners_of_getElem {m : Mem}
    (h : ∀ i (hi : i < m.threads.size), (m.threads[i]'hi).spawner = 0) :
    ∀ r ∈ m.threads, r.spawner = 0 := fun r hr => by
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hr
  exact h i hi

/-- While `main` is the only thread, a clock below `main`'s is below every thread's. -/
theorem allLe_of_one {m : Mem} {c : VClock} (h1 : m.threads.size = 1)
    (h : VClock.le c (m.clocks[0]!) = true) : AllLe m c := fun u hu => by
  rw [h1] at hu
  obtain rfl : u = 0 := by omega
  exact h

end Full

/-! ## Blocks -/

/-- Block `b` is live with `S` bytes of kind `K`, at an address that is a multiple of `a`. -/
def Mem.BlkOk (m : Mem) (b : BlockId) (S a : Nat) (K : BlockKind) : Prop :=
  ∃ blk, m.blocks[b]? = some blk ∧ blk.live = true ∧ blk.bytes.size = S ∧ blk.addr % a = 0 ∧
    blk.kind = K

namespace Mem.BlkOk

variable {m m' : Mem} {b : BlockId} {S a : Nat} {K : BlockKind}

/-- The cell of byte `x` of the block. -/
theorem cell (hb : m.BlkOk b S a K) {x : Nat} (hx : x < S) (hlo : K.mappedLo ≤ x) :
    ∃ blk, m.blocks[b]? = some blk ∧ ∃ h : x < blk.bytes.size,
      m.heap (b, x) = some ⟨blk.bytes[x]'h, blk.addr, blk.bytes.size, blk.kind⟩ := by
  obtain ⟨blk, hblk, hl, hs, -, hk⟩ := hb
  refine ⟨blk, hblk, by omega, ?_⟩
  simp only [Mem.heap, hblk]
  rw [dite_eq_left_of_eq_true (eq_true ⟨hl, by omega, by rw [hk]; exact hlo⟩)]

/-- Byte `x` of the block is live. -/
theorem heap (hb : m.BlkOk b S a K) {x : Nat} (hx : x < S) (hlo : K.mappedLo ≤ x) :
    m.heap (b, x) ≠ none := by
  obtain ⟨blk, _, hx', h⟩ := hb.cell hx hlo
  rw [h]; simp

/-- **The same cell at one byte: the same block.** A cell has the block's address, size and kind. -/
theorem keep (hb : m.BlkOk b S a K) {x : Nat} (hx : x < S) (hlo : K.mappedLo ≤ x)
    (h : m'.heap (b, x) = m.heap (b, x)) : m'.BlkOk b S a K := by
  obtain ⟨blk, hblk, hl, hs, ha, hk⟩ := hb
  have hc : m.heap (b, x) = some ⟨blk.bytes[x]'(by omega), blk.addr, blk.bytes.size, blk.kind⟩ := by
    simp only [Mem.heap, hblk]
    rw [dite_eq_left_of_eq_true (eq_true ⟨hl, by omega, by rw [hk]; exact hlo⟩)]
  rw [hc] at h
  obtain ⟨blk', hblk', hl', hx', he⟩ := Mem.heap_some h
  simp only [Cell.mk.injEq] at he
  obtain ⟨-, hA, hS, hK⟩ := he
  exact ⟨blk', hblk', by simpa using hl', by rw [← hS, hs], by rw [← hA, ha], by rw [← hK, hk]⟩

end Mem.BlkOk

namespace Full

open FAssn

/-- **A part that holds a block's full extent pins the block**: in every memory that holds the
parts, the block is live with the extent's size and kind (`Holds.bauth`). -/
theorem FOwned.blkOf {own : ThreadId → Res} {rO : Res} {m : Mem} {t : ThreadId}
    (ho : FOwned own rO m) (ht : t < m.threads.size) {b : BlockId} {S : Nat} {K : BlockKind}
    {R : FAssn} (h : (bext b S K ⋆ R) (own t)) :
    ∃ blk, m.blocks[b]? = some blk ∧ blk.live = true ∧ blk.bytes.size = S ∧ blk.kind = K := by
  obtain ⟨rR, -, -, hh⟩ := ho.part ht
  obtain ⟨blk, hb, hl, hs, hk, -⟩ := hh.bauth (b := b) (S := S) (K := K) (q := Frac.one) h
  exact ⟨blk, hb, hl, hs, hk⟩

/-! ## Encodings -/

/-- A lawful encoding decodes from the front of its own bytes. -/
theorem _root_.Zig.LawfulEnc.decode_extract {T : Type} [Enc T] [LawfulEnc T] (v : T) :
    Enc.decode ((Enc.encode v).extract 0 (0 + Enc.size T)) = (pure v : Result T) := by
  rw [Nat.zero_add, ← LawfulEnc.size_encode v, Array.extract_size]
  exact LawfulEnc.decode_encode v

end Full
end Zig
