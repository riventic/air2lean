import ZigLean.Sep.Full.AtomicRules
import ZigLean.Sep.Full.Witness

/-!
# A `wpts` header word has a thread rule after memory reuse (kernel-checked, MM-21)

The arena's `free` and `resize` are thread triples (`CTriple`): each atomic op on a node's header
word runs by the op's thread rule. `HeaderTagCX.lean` shows that a node the child has just granted
has no `apts` header, only a `wpts` one (an owned word under any atomic location). This file is
the arena's reuse scenario for the `size` word (`Node.loadBuf`'s relaxed `@atomicLoad` of
`node.size`): the `wpts` thread rule holds there (`tests/roadmap/sep-full/MixedSizeCX.lean` is the
same scenario for a plain word, with the racing counterpart).

A `FixedBufferAllocator` child hands out 8-aligned blocks of one buffer, block 0 here (32 bytes).
Before, a client ran a 16-byte atomic op on bytes `0..16`, so the location `(0, 0, 16)` stays.
The child then granted bytes `0..8` to thread 1 and the node at offset 8 to thread 0 (the arena);
thread 1 wrote its bytes and thread 0 has not joined it. The arena's 64-bit atomic load of the
node's `size` word (offset 8) is a mixed-size access. Every recorded access to the bytes it shares
with the stale location (`8..16`) happened before it, so `retireAt` retires the location
(`ALoc.overAt`, MM-21) and the load reads the word (`size_load_reads`). Before MM-21 the model
asked that of thread 1's bytes `0..8` too, and the load threw `.unspecified`.

* `size_load_rule`: the `wpts` thread rule of the typed load (`FTTriple.atomicLoadAsW`), for any
  packed 64-bit type whose bits `0` are valid (the arena's `Node.Size` among them), holds in this
  memory: the load reads `ofBits 0` and leaves an `apts` word.

Kernel-checked; the expected axioms are `propext`, `Classical.choice`, `Quot.sound` at most.
-/

namespace Zig.Full.HeaderMixCX

open Zig Zig.Full

/-- The buffer: 32 zero bytes. -/
def blk : Block :=
  { bytes := Array.replicate 32 (.int 0), align := 8, kind := .heap, live := true, addr := 4096 }

/-- The stale location: a 16-byte atomic object over bytes `0..16`, from before both grants. -/
def loc : ALoc :=
  { block := 0, off := 0, len := 16,
    msgs := #[{ id := 0, bytes := Array.replicate 16 (.int 0), clock := #[], relClock := #[] }] }

/-- Thread 1's plain write of its grant, bytes `0..8`. -/
def wr : FootprintEntry := { tid := 1, clock := #[0, 1], block := 0, off := 0, len := 8, kind := .write }

/-- Thread 0 (the arena) runs; thread 1 is not joined. -/
def m : Mem :=
  { blocks := #[blk], current := 0, clocks := #[#[1], #[0, 1]],
    threads := #[{ spawner := 0, joined := true }, { spawner := 0, joined := false }],
    footprint := #[wr], atomics := #[loc], nextMsg := 1 }

/-- The node's `size` word, at offset 8. -/
def N : Ptr := ⟨some 0, 8⟩

/-- **The load of the `size` word reads it**: the stale location is retired, the new one is the
word's. -/
theorem size_load_reads :
    (match ((Zig.atomicLoadAt (n := 64) 0 .relaxed 8 N).run m).run with
      | some (.ok (v, m')) => v == 0 && m'.atomics.size == 1 && (m'.atomics[0]!).off == 8 &&
          (m'.atomics[0]!).len == 8
      | _ => false) = true := by
  decide +kernel

/-- Thread 0's bytes: the word, `8..16` of block 0. -/
def hP : Heap := fun l => if l.1 = 0 ∧ 8 ≤ l.2 ∧ l.2 < 16 then m.heap l else none

/-- The frame: the other bytes (thread 1's grant and the rest of the buffer). -/
def hF : Heap := fun l => if l.1 = 0 ∧ 8 ≤ l.2 ∧ l.2 < 16 then none else m.heap l

theorem heap_word : ∀ x < 16, 8 ≤ x → m.heap (0, x) = some ⟨.int 0, 4096, 32, .heap⟩ := by
  decide

theorem tag_word : ∀ x < 16, 8 ≤ x → tagOf (shapes m) 0 x = some (0, 16) := by decide

/-- Thread 0 owns the `size` word `N ↦ 0` (a `wpts`: its constraint is the stale location). -/
theorem word : wpts N 0 ⟨FHeap.ofHeap (shapes m) hP, Know.none, Ghost.unit⟩ := by
  refine ⟨4096, 32, .heap, Array.replicate 8 (.int 0), some (0, 16), by decide, by decide, rfl,
    rfl, rfl, rfl, 0, rfl, by decide, fun ⟨b, x⟩ => ?_⟩
  have hp8 : N.off.toNat = 8 := rfl
  simp only [FHeap.ofHeap, hP, hp8, Array.size_replicate]
  by_cases hc : b = 0 ∧ 8 ≤ x ∧ x < 16
  · obtain ⟨rfl, hx8, hx⟩ := hc
    have hz : ∀ i < 8, Byte.int (0 : BitVec 8) = (Array.replicate 8 (Byte.int (0 : BitVec 8)))[i]! := by
      decide
    simp [hx8, hx, heap_word x hx hx8, tag_word x hx hx8]
    exact hz (x - 8) (by omega)
  · simp only [hc, ite_false, Option.map_none]

theorem holds : Holds m ⟨FHeap.ofHeap (shapes m) hP, Know.none, Ghost.unit⟩
    ⟨FHeap.ofHeap (shapes m) hF, Know.none, Ghost.exts (heapExts m hF)⟩ := by
  refine holds_ofHeap (fun l => ?_) (funext fun l => ?_)
  · simp only [hP, hF]; split <;> simp
  · simp only [Heap.union_apply, hP, hF]; split <;> simp

theorem fconc : m.FConc := by
  refine ⟨by decide, ⟨by simp [shapes, m, loc, ALoc.shape], by simp [shapes, m, loc, ALoc.shape]⟩,
    fun b b' blk' blk'' hne h1 h2 _ => ?_, fun b blk' h _ => ?_⟩
  · have hb : b = 0 := by
      rcases b with _ | b
      · rfl
      · simp [m] at h1
    have hb' : b' = 0 := by
      rcases b' with _ | b'
      · rfl
      · simp [m] at h2
    exact (hne (hb.trans hb'.symm)).elim
  · rcases b with _ | b
    · simp only [m, List.getElem?_toArray, List.getElem?_cons_zero, Option.some.injEq] at h
      subst h; decide
    · simp [m] at h

/-- Thread 0 owns the word: thread 1's write touches none of its bytes. -/
theorem owns : m.Owns m.current (FHeap.ofHeap (shapes m) hP).erase := by
  rw [FHeap.ofHeap_erase]
  intro e he hc
  have : e = wr := by simpa [m] using he
  subst this
  rcases hc with ⟨x, -, hx2, hx⟩ | hb
  · exact (hx (by simp only [wr] at hx2; simp [hP, wr]; omega)).elim
  · simp [m, wr] at hb

/-- **The `wpts` header word's thread rule holds here**: for any packed 64-bit type whose bits
`0` are valid, the typed load of the `size` word from `wpts N 0` is the rule's postcondition: it
reads `ofBits 0` and leaves an `apts` word over the frame. -/
theorem size_load_rule (α : Type) [Packed α 64] (hv : Packed.valid (α := α) 0 = true) :
    match ((Zig.atomicLoadAs α 0 .relaxed 8 N).run m).run with
    | some (.ok (w, m')) => ∃ r',
        Holds m' r' ⟨FHeap.ofHeap (shapes m) hF, Know.none, Ghost.exts (heapExts m hF)⟩ ∧
        w = Packed.ofBits 0 ∧ apts N 0 r'
    | _ => False := by
  have h := FTTriple.atomicLoadAsW (α := α) N 0 .relaxed hv m _ _ holds word fconc owns
  have hint := size_load_reads
  generalize hr : ((Zig.atomicLoadAt (n := 64) 0 .relaxed 8 N).run m).run = res at hint
  rcases res with _ | (e | ⟨v, m₁⟩)
  · simp at hint
  · simp at hint
  · have hv0 : v = 0 := by simp at hint; exact hint.1.1.1
    subst hv0
    have hrun : ((Zig.atomicLoadAs α 0 .relaxed 8 N).run m).run =
        some (.ok (Packed.ofBits 0, m₁)) := by
      unfold Zig.atomicLoadAs
      rw [StateT.run_bind, ExceptT.run_bind, hr]
      simp only [Packed.ofBits?]
      simp
      have hv' : Packed.valid (α := α) 0#64 = true := hv
      exact ⟨.ok (Packed.ofBits 0), by simp only [hv', ↓reduceIte]; rfl, rfl⟩
    rw [hrun] at h ⊢
    obtain ⟨r', hh', hq, -⟩ := h
    obtain ⟨hw, hap⟩ := Full.sep_lift.mp hq
    exact ⟨r', hh', hw, hap⟩

end Zig.Full.HeaderMixCX

#print axioms Zig.Full.HeaderMixCX.size_load_reads
#print axioms Zig.Full.HeaderMixCX.size_load_rule
