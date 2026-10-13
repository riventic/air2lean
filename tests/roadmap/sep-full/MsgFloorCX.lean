import ZigLean.Sep.Full.Atomic
import ZigLean.Sep.Full.Witness

/-!
# An owned atomic word can still offer an old message: regression (`docs/sep-threads.md`, S4)

`CTriple` (`ZigLean/Sep/Full/Conc.lean`) resumes a thread at an atomic op's oracle pick with
**every** choice `c < count m₂` (as `Proto.Step` does). The thread rules of the atomic ops on an
owned word (`FTTriple.atomicLoad`, ...) are proved for choice `0`, the newest message. They give
every choice only if an owned word offers one message: the newest message of the word's location
happened before the owner (the floor, `floorPos`, is the newest position).

`Mem.FConc` and `Mem.Owns` do not say that. Ownership (`Mem.Owns`) speaks of the recorded
accesses (`Mem.footprint`), and nothing ties a location's messages to them. Block 0 holds the
word `1`; its location `(0, 0, 8)` has the messages `0` (clock `#[]`) and `1` (thread 1's clock
`#[0, 5]`); thread 0 runs with clock `#[3]`, and the footprint is empty, so thread 0 owns the
word (`apts p 1`). Thread 0's floor at the location is position `0`: the load offers both messages
(`count_two`), and choice `1` reads the old value `0` (`reads_old`).

* `no_ctriple`: so the atomic load as a call (an oracle pick, then the load with the choice)
  has no `CTriple` with precondition `apts p 1` that returns `1`, although its choice `0` does
  (`reads_new`; `FTTriple.atomicLoad`).
* `fseq`: the memory is a sequential one (`Mem.FSeq`), so the coverage is not a consequence of
  `FSeq` either: a sequential reading takes choice `0` only and does not need it.

The fix (S4, coordinator ruling (a)): a memory invariant that covers every message of a location
by the recorded accesses to its bytes; with it an owner's floor is the newest message.

Kernel-checked; the expected axioms are `propext`, `Classical.choice`, `Quot.sound` at most.
-/

namespace Zig.MsgFloorCX

open Zig Zig.Full Zig.Sched

/-- The word `1`, little-endian. -/
def one : Array Byte := #[.int 1, .int 0, .int 0, .int 0, .int 0, .int 0, .int 0, .int 0]

/-- Block 0: the word `1`. -/
def blk : Block := { bytes := one, align := 8, kind := .heap, live := true, addr := 4096 }

/-- The word's location: the message `0` from before thread 1, then thread 1's `1`. -/
def loc : ALoc :=
  { block := 0, off := 0, len := 8,
    msgs := #[{ id := 0, bytes := Array.replicate 8 (.int 0), clock := #[], relClock := #[] },
      { id := 1, bytes := one, clock := #[0, 5], relClock := #[], writer := some 1 }] }

/-- Thread 0 runs; thread 1 is not joined; no access is recorded. -/
def m : Mem :=
  { blocks := #[blk], current := 0, clocks := #[#[3], #[0, 5]],
    threads := #[{ spawner := 0, joined := true }, { spawner := 0, joined := false }],
    atomics := #[loc], nextMsg := 2 }

/-- The word at offset 0. -/
def p : Ptr := ⟨some 0, 0⟩

/-- The atomic load as a call: the oracle's pick, then the load with that choice
(`atomicLoadC` normalized). -/
def load : ConcM Unit (BitVec 64) :=
  (ConcM.sync (.pick (loadCount 64 .relaxed 8 p)) : ConcM Unit Nat) >>= fun c =>
    ConcM.liftMem (Zig.atomicLoadAt (n := 64) c .relaxed 8 p)

/-- **The owned word offers two messages.** -/
theorem count_two : loadCount 64 .relaxed 8 p m = 2 := by decide +kernel

theorem reads_oldB :
    (match ((Zig.atomicLoadAt (n := 64) 1 .relaxed 8 p).run m).run with
      | some (.ok (v, _)) => v == 0
      | _ => false) = true := by
  decide +kernel

/-- **Choice `1` reads the old message `0`.** -/
theorem reads_old : ∃ m', ((Zig.atomicLoadAt (n := 64) 1 .relaxed 8 p).run m).run =
    some (.ok (0, m')) := by
  have h := reads_oldB
  revert h
  generalize ((Zig.atomicLoadAt (n := 64) 1 .relaxed 8 p).run m).run = res
  rcases res with _ | (e | ⟨v, m'⟩)
  · simp
  · simp
  · intro h; simp only [beq_iff_eq] at h; subst h; exact ⟨m', rfl⟩

/-- Choice `0` reads the word, `1`. -/
theorem reads_new :
    (match ((Zig.atomicLoadAt (n := 64) 0 .relaxed 8 p).run m).run with
      | some (.ok (v, _)) => v == 1
      | _ => false) = true := by
  decide +kernel

/-- Thread 0's bytes: the word. -/
def hP : Heap := fun l => if l.1 = 0 ∧ l.2 < 8 then m.heap l else none

/-- The frame: nothing else. -/
def hF : Heap := fun l => if l.1 = 0 ∧ l.2 < 8 then none else m.heap l

theorem heap_word : ∀ x < 8, m.heap (0, x) = some ⟨one[x]!, 4096, 8, .heap⟩ := by decide

theorem tag_word : ∀ x < 8, tagOf (shapes m) 0 x = some (0, 8) := by decide

/-- Thread 0's bytes are the atomic word `p ↦ₐ 1`. -/
theorem word : apts p 1 ⟨FHeap.ofHeap (shapes m) hP, Know.none, Ghost.unit⟩ := by
  refine ⟨4096, 8, .heap, one, by decide, by decide, rfl, rfl, rfl, rfl, 0, rfl, by decide,
    fun ⟨b, x⟩ => ?_⟩
  have hp0 : p.off.toNat = 0 := rfl
  simp only [FHeap.ofHeap, hP, hp0, Nat.zero_add, Nat.zero_le, true_and, Nat.sub_zero]
  by_cases hc : b = 0 ∧ x < 8
  · obtain ⟨rfl, hx⟩ := hc
    simp [hx, heap_word x hx, tag_word x hx, one]
  · have : ¬ (b = 0 ∧ x < one.size) := by simpa [one] using hc
    simp [hc, this]

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

/-- The memory is even a sequential one: no access is recorded. So the coverage of the messages
does not follow from `Mem.FSeq` (nor from `Mem.FConc`). -/
theorem fseq : m.FSeq := ⟨⟨singleThread_empty rfl (by decide)⟩, fconc.2.1, fconc.2.2⟩

/-- No access is recorded: thread 0 owns the word. -/
theorem owns : m.Owns m.current (FHeap.ofHeap (shapes m) hP).erase :=
  Witness.owns_of_footprint rfl _ _

/-- **No `CTriple` of the atomic load from an owned word that returns its value**: resumed in
the same memory with choice `1`, the load reads `0`. -/
theorem no_ctriple : ¬ CTriple (apts p 1) load (fun w => ⟪w = 1⟫ ⋆ apts p 1) := by
  intro h
  have hr := h 1 m _ _ holds word fconc owns
  change CTriple.Run _ m _ (.sync (.pick (loadCount 64 .relaxed 8 p)) m fun c m' =>
    .leaf ((Zig.atomicLoadAt (n := 64) c .relaxed 8 p).run m')) at hr
  obtain ⟨-, r', hh', hc', ho', -, hk⟩ := CTriple.Run.sync_iff.mp hr
  have h1 := hk m _ rfl hh' hc' ho' (1 : Nat)
    (show (1 : Nat) < loadCount 64 .relaxed 8 p m ∨ _ by rw [count_two]; exact .inl (by decide))
  obtain ⟨m', e⟩ := reads_old
  rw [show (Zig.atomicLoadAt (n := 64) 1 .relaxed 8 p).run m = ExceptT.mk (some (.ok (0, m')))
    from e] at h1
  obtain ⟨r'', -, hq, -⟩ := CTriple.Run.ok_iff.mp h1
  exact absurd (Iff.mp Zig.Full.sep_lift hq).1 (by decide : ¬ ((0 : BitVec 64) = 1))

end Zig.MsgFloorCX

#print axioms Zig.MsgFloorCX.count_two
#print axioms Zig.MsgFloorCX.reads_old
#print axioms Zig.MsgFloorCX.no_ctriple
#print axioms Zig.MsgFloorCX.fseq
