import ZigLean.Sep.Full.Atomic
import ZigLean.Sep.Full.Witness

/-!
# Mixed-size atomics after memory reuse: regression (MM-21, `docs/sep-threads.md` S1 step 5)

An atomic location is one `(block, offset, size)`. An atomic op over bytes of a location of
another offset or size is a mixed-size access: `retireAt` retires the old location when every
recorded access to the bytes **the op shares with it** happened before the op (`ALoc.overAt`),
and throws `.unspecified` otherwise. Before MM-21 it asked that of **every** byte of the old
location (`ALoc.over`), which rejected allocator reuse, a correct program (LLVM's memory model is
per byte; the old object's other bytes belong to other objects after the reuse).

Block 0 has 16 bytes; `(0, 0, 16)` is an atomic location (a 16-byte atomic op before thread 1
was spawned, the memory then freed and handed out again). Thread 0 owns bytes `0..8` (their tag
constraint is that location: a `wpts` word); thread 1 has not been joined.

* `mArena`, the reuse case: thread 1 owns bytes `8..16` and plainly wrote them.
  `arena_old`: the old check rejects the load (it threw `.unspecified`); `arena_new`: the
  per-byte check passes; `arena_reads`: thread 0's 64-bit load at offset 0 retires the location
  and reads the word; `arena_rule`: the `wpts` thread rule (`FTTriple.atomicLoadW`) holds in this
  memory (it was refuted there before MM-21).
* `mRace`, a genuine mixed-size race: thread 1 did a 16-byte atomic access to the location
  concurrently. `race_new`: the per-byte check rejects; `race_throws`: the load stays
  `.unspecified`; `race_unowned`: thread 0 does not own the word there, so no thread rule covers
  this memory.
* `seq_reads`: once thread 0 joined thread 1, the load reads the word.

Kernel-checked; the expected axioms are `propext`, `Classical.choice`, `Quot.sound` at most.
-/

namespace Zig.MixedSizeCX

open Zig Zig.Full

/-- 16 zero bytes. -/
def blk : Block :=
  { bytes := Array.replicate 16 (.int 0), align := 8, kind := .heap, live := true, addr := 4096 }

/-- The 16-byte location over the block, from before thread 1. -/
def loc : ALoc :=
  { block := 0, off := 0, len := 16,
    msgs := #[{ id := 0, bytes := Array.replicate 16 (.int 0), clock := #[], relClock := #[] }] }

/-- Thread 1's plain write of its bytes `8..16`. -/
def wr : FootprintEntry := { tid := 1, clock := #[0, 1], block := 0, off := 8, len := 8, kind := .write }

/-- Thread 1's 16-byte atomic access to the old location. -/
def at16 : FootprintEntry :=
  { tid := 1, clock := #[0, 1], block := 0, off := 0, len := 16, kind := .atomicWrite }

/-- Thread 0 runs; thread 1 is not joined. -/
def mk (fp : Array FootprintEntry) : Mem :=
  { blocks := #[blk], current := 0, clocks := #[#[1], #[0, 1]],
    threads := #[{ spawner := 0, joined := true }, { spawner := 0, joined := false }],
    footprint := fp, atomics := #[loc], nextMsg := 1 }

def mArena : Mem := mk #[wr]
def mRace : Mem := mk #[at16]

/-- The word at offset 0. -/
def p : Ptr := ⟨some 0, 0⟩

/-- The check before MM-21: every access to any byte of an overlapping location. -/
def oldOk (m : Mem) (b o len : Nat) : Bool :=
  m.atomics.all fun l => !l.hits b o len || l.over m (m.clocks[m.current]!)

/-- The check of `retireAt`: every access to a byte the op shares with an overlapping location. -/
def newOk (m : Mem) (b o len : Nat) : Bool :=
  m.atomics.all fun l => !l.hits b o len || l.overAt m (m.clocks[m.current]!) b o len

theorem arena_old : oldOk mArena 0 0 8 = false := by decide +kernel
theorem arena_new : newOk mArena 0 0 8 = true := by decide +kernel
theorem race_new : newOk mRace 0 0 8 = false := by decide +kernel

/-- **The reuse case reads**: the load retires the location and reads the word. -/
theorem arena_reads :
    (match ((Zig.atomicLoadAt (n := 64) 0 .relaxed 8 p).run mArena).run with
      | some (.ok (v, m')) => v == 0 && m'.atomics.size == 1 && (m'.atomics[0]!).len == 8
      | _ => false) = true := by
  decide +kernel

theorem race_throwsB :
    (match ((Zig.atomicLoadAt (n := 64) 0 .relaxed 8 p).run mRace).run with
      | some (.error .unspecified) => true
      | _ => false) = true := by
  decide +kernel

/-- **A genuine mixed-size race throws** `.unspecified`. -/
theorem race_throws :
    ((Zig.atomicLoadAt (n := 64) 0 .relaxed 8 p).run mRace).run = some (.error .unspecified) := by
  have h := race_throwsB
  revert h
  generalize ((Zig.atomicLoadAt (n := 64) 0 .relaxed 8 p).run mRace).run = res
  rcases res with _ | (e | x)
  · simp
  · cases e <;> simp
  · simp

/-- Thread 0's bytes: `0..8` of block 0. -/
def hP (m : Mem) : Heap := fun l => if l.1 = 0 ∧ l.2 < 8 then m.heap l else none

/-- The frame: the other bytes (thread 1's). -/
def hF (m : Mem) : Heap := fun l => if l.1 = 0 ∧ l.2 < 8 then none else m.heap l

theorem heap_word : ∀ x < 8, mArena.heap (0, x) = some ⟨.int 0, 4096, 16, .heap⟩ := by decide

theorem tag_word : ∀ x < 8, tagOf (shapes mArena) 0 x = some (0, 16) := by decide

/-- Thread 0's bytes are the word `p ↦ 0`, with the constraint of the 16-byte location. -/
theorem word : wpts p 0 ⟨FHeap.ofHeap (shapes mArena) (hP mArena), Know.none, Ghost.unit⟩ := by
  refine ⟨4096, 16, .heap, Array.replicate 8 (.int 0), some (0, 16), by decide, by decide, rfl,
    rfl, rfl, rfl, 0, rfl, by decide, fun ⟨b, x⟩ => ?_⟩
  have hp0 : p.off.toNat = 0 := rfl
  simp only [FHeap.ofHeap, hP, hp0, Array.size_replicate, Nat.zero_add, Nat.zero_le, true_and,
    Nat.sub_zero]
  by_cases hc : b = 0 ∧ x < 8
  · obtain ⟨rfl, hx⟩ := hc
    simp [hx, heap_word x hx, tag_word x hx]
  · simp [hc]

theorem holds : Holds mArena ⟨FHeap.ofHeap (shapes mArena) (hP mArena), Know.none, Ghost.unit⟩
    ⟨FHeap.ofHeap (shapes mArena) (hF mArena), Know.none, Ghost.exts (heapExts mArena (hF mArena))⟩ := by
  refine holds_ofHeap (fun l => ?_) (funext fun l => ?_)
  · simp only [hP, hF]; split <;> simp
  · simp only [Heap.union_apply, hP, hF]; split <;> simp

theorem fconc : mArena.FConc := by
  refine ⟨by decide, ⟨by simp [shapes, mArena, mk, loc, ALoc.shape],
    by simp [shapes, mArena, mk, loc, ALoc.shape]⟩, fun b b' blk' blk'' hne h1 h2 _ => ?_,
    fun b blk' h _ => ?_⟩
  · have hb : b = 0 := by
      rcases b with _ | b
      · rfl
      · simp [mArena, mk] at h1
    have hb' : b' = 0 := by
      rcases b' with _ | b'
      · rfl
      · simp [mArena, mk] at h2
    exact (hne (hb.trans hb'.symm)).elim
  · rcases b with _ | b
    · simp only [mArena, mk, List.getElem?_toArray, List.getElem?_cons_zero, Option.some.injEq] at h
      subst h; decide
    · simp [mArena, mk] at h

/-- Thread 0 owns the word: thread 1's write touches none of its bytes. -/
theorem owns : mArena.Owns mArena.current (FHeap.ofHeap (shapes mArena) (hP mArena)).erase := by
  rw [FHeap.ofHeap_erase]
  intro e he hc
  have : e = wr := by simpa [mArena, mk] using he
  subst this
  rcases hc with ⟨x, hx1, -, hx⟩ | hb
  · exact (hx (by simp only [wr] at hx1; simp [hP, wr]; omega)).elim
  · simp [mArena, mk, wr] at hb

/-- **The `wpts` thread rule holds in the reuse memory**: the load's run is the rule's
postcondition (before MM-21 the load threw here, and no thread triple from `wpts p 0` held). -/
theorem arena_rule : ∃ m' r',
    ((Zig.atomicLoadAt (n := 64) 0 .relaxed 8 p).run mArena).run = some (.ok (0, m')) ∧
    Holds m' r'
      ⟨FHeap.ofHeap (shapes mArena) (hF mArena), Know.none, Ghost.exts (heapExts mArena (hF mArena))⟩ ∧
    apts p 0 r' := by
  have h := FTTriple.atomicLoadW p 0 .relaxed mArena _ _ holds word fconc owns
  have hreads := arena_reads
  generalize ((Zig.atomicLoadAt (n := 64) 0 .relaxed 8 p).run mArena).run = res at h hreads ⊢
  rcases res with _ | (e | ⟨v, m'⟩)
  · simp at hreads
  · simp at hreads
  · obtain ⟨r', hh', hq, -⟩ := h
    obtain ⟨hv, hap⟩ := Full.sep_lift.mp hq
    exact ⟨m', r', by rw [hv], hh', hap⟩

/-- **In the race memory thread 0 does not own the word**: thread 1's atomic access to its bytes
did not happen before thread 0. -/
theorem race_unowned (h : Heap) (hw : h (0, 0) ≠ none) : ¬ mRace.Owns mRace.current h := by
  intro ho
  have h1 := ho at16 (by simp [mRace, mk]) (.inl ⟨0, by decide, by decide, hw⟩)
  have h2 : VClock.le at16.clock (mRace.clocks[mRace.current]!) = false := by decide +kernel
  rw [h2] at h1
  cases h1

/-- The reuse memory once thread 0 joined thread 1 (its clock is past the write). -/
def mj : Mem :=
  { mArena with clocks := #[#[1, 1], #[0, 1]],
                threads := #[{ spawner := 0, joined := true }, { spawner := 0, joined := true }] }

/-- **Sequentially** (every access happened before) the load reads the word too. -/
theorem seq_reads :
    (match ((Zig.atomicLoadAt (n := 64) 0 .relaxed 8 p).run mj).run with
      | some (.ok (v, m')) => v == 0 && m'.atomics.size == 1 && (m'.atomics[0]!).len == 8
      | _ => false) = true := by
  decide +kernel

end Zig.MixedSizeCX

#print axioms Zig.MixedSizeCX.arena_old
#print axioms Zig.MixedSizeCX.arena_new
#print axioms Zig.MixedSizeCX.race_new
#print axioms Zig.MixedSizeCX.arena_reads
#print axioms Zig.MixedSizeCX.race_throws
#print axioms Zig.MixedSizeCX.arena_rule
#print axioms Zig.MixedSizeCX.race_unowned
#print axioms Zig.MixedSizeCX.seq_reads
