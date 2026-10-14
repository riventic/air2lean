import ZigLean.Sep.Full.Atomic
import ZigLean.Sep.Full.Witness

/-!
# Why the arena's header words must be `apts` in a thread (kernel-checked failure scenario)

The arena's `free` and `resize` are thread triples (`CTriple`): each atomic op on a node's header
word runs by the op's thread rule, which takes an `apts` word. `HeaderTagCX.lean` shows that a node
the child has just granted has no `apts` header, only a `wpts` one (an owned word under any atomic
location). This file shows that a `wpts` header word has no thread rule for the load of the
`size` word (`Node.loadBuf`'s relaxed `@atomicLoad` of `node.size`), whatever the packed
type it is read as and whatever the postcondition, so a `wpts` header cannot replace the `apts`
one (`tests/roadmap/sep-full/AtomicRetireCX.lean` is the same scenario for a plain word):

A `FixedBufferAllocator` child hands out 8-aligned blocks of one buffer, block 0 here (32 bytes).
Before, a client ran a 16-byte atomic op on bytes `0..16`, so the location `(0, 0, 16)` stays.
The child then granted bytes `0..8` to thread 1 and the node at offset 8 to thread 0 (the arena);
thread 1 wrote its bytes and thread 0 has not joined it. The arena's 64-bit atomic load of the
node's `size` word (offset 8) is a mixed-size access whose overlapping location has an access that
did not happen before it, so it throws `.unspecified` (`size_load_throws`), although thread 0 owns
the word (`word`, `owns`). Natively the load is harmless: the model is conservative here
(fail closed), and the open item of `docs/alloc-arena.md` (the mixed-size atomic model).

* `size_load_no_thread_rule`: no thread triple with precondition `wpts N 0` holds for the typed
  atomic load at `N`, for any packed 64-bit type (the arena's `Node.Size` among them).

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

theorem size_load_throwsB :
    (match ((Zig.atomicLoadAt (n := 64) 0 .relaxed 8 N).run m).run with
      | some (.error .unspecified) => true
      | _ => false) = true := by
  decide +kernel

/-- **The load of the `size` word throws `.unspecified`** in this memory. -/
theorem size_load_throws :
    ((Zig.atomicLoadAt (n := 64) 0 .relaxed 8 N).run m).run = some (.error .unspecified) := by
  have h := size_load_throwsB
  revert h
  generalize ((Zig.atomicLoadAt (n := 64) 0 .relaxed 8 N).run m).run = res
  rcases res with _ | (e | x)
  · simp
  · cases e <;> simp
  · simp

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

/-- **No thread rule for a `wpts` header word**: whatever the packed type and the postcondition,
the thread triple of the `size` word's atomic load from `wpts N 0` is false. -/
theorem size_load_no_thread_rule (α : Type) [Packed α 64] (Q : α → FAssn) :
    ¬ FTTriple (wpts N 0) (Zig.atomicLoadAs α 0 .relaxed 8 N) Q := by
  intro h
  have := h m _ _ holds word fconc owns
  have e : ((Zig.atomicLoadAs α 0 .relaxed 8 N).run m).run = some (.error .unspecified) := by
    unfold Zig.atomicLoadAs
    rw [StateT.run_bind, ExceptT.run_bind, size_load_throws]
    rfl
  rw [e] at this
  cases this

end Zig.Full.HeaderMixCX

#print axioms Zig.Full.HeaderMixCX.size_load_throws
#print axioms Zig.Full.HeaderMixCX.size_load_no_thread_rule
