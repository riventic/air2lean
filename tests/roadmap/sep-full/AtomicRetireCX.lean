import ZigLean.Sep.Full.Atomic
import ZigLean.Sep.Full.Witness

/-!
# A mixed-size atomic access is no thread rule: regression (`docs/sep-threads.md`, S1 step 5)

The sequential atomic rules (`FTriple.atomicLoadW`, `atomicStoreW`, ...) take any owned word
(`wpts`, whatever its tag constraint): a location over it of another offset or size is retired,
since in one thread every access to it happened before (`locIdx_noErr_single`). In a concurrent
memory that is false, so the `wpts` rules have no thread versions; the thread rules take an
`apts` word, which no location of another offset or size overlaps (`apts_layout`).

Block 0 has 16 bytes; `(0, 0, 16)` is an atomic location (a 16-byte atomic op before thread 1
was spawned). Thread 0 owns bytes `0..8` (their tag constraint is that location: a `wpts` word),
thread 1 owns bytes `8..16` and wrote them; thread 0 has not joined it. Thread 0's 64-bit atomic
load at offset 0 is a mixed-size access whose overlapping location has an access that did not
happen before it (`ALoc.over` is false), so `retireAt` throws `.unspecified`.

* `concurrent_throws`: the load throws `.unspecified`.
* `w_load_no_thread_rule`: so no thread triple with precondition `wpts p 0` holds for the load,
  whatever its postcondition: the memory holds the word and the rest as the frame, is `FConc`,
  and thread 0 owns the word (`Mem.Owns`); a thread triple allows only `.stackOverflow`.
* `seq_reads`: the same memory once thread 1's write happened before thread 0 (thread 0 joined
  it): the load retires the location and reads the word, as the sequential rule says.

Kernel-checked; the expected axioms are `propext`, `Classical.choice`, `Quot.sound` at most.
-/

namespace Zig.AtomicRetireCX

open Zig Zig.Full

/-- 16 zero bytes. -/
def blk : Block :=
  { bytes := Array.replicate 16 (.int 0), align := 8, kind := .heap, live := true, addr := 4096 }

/-- The 16-byte location over the block, from before thread 1. -/
def loc : ALoc :=
  { block := 0, off := 0, len := 16,
    msgs := #[{ id := 0, bytes := Array.replicate 16 (.int 0), clock := #[], relClock := #[] }] }

/-- Thread 1's plain write of bytes `8..16`. -/
def wr : FootprintEntry := { tid := 1, clock := #[0, 1], block := 0, off := 8, len := 8, kind := .write }

/-- Thread 0 runs; thread 1 is not joined. -/
def m : Mem :=
  { blocks := #[blk], current := 0, clocks := #[#[1], #[0, 1]],
    threads := #[{ spawner := 0, joined := true }, { spawner := 0, joined := false }],
    footprint := #[wr], atomics := #[loc], nextMsg := 1 }

/-- The word at offset 0. -/
def p : Ptr := ⟨some 0, 0⟩

theorem concurrent_throwsB :
    (match ((Zig.atomicLoadAt (n := 64) 0 .relaxed 8 p).run m).run with
      | some (.error .unspecified) => true
      | _ => false) = true := by
  decide +kernel

/-- **Concurrently** the 64-bit load at offset 0 throws `.unspecified`. -/
theorem concurrent_throws :
    ((Zig.atomicLoadAt (n := 64) 0 .relaxed 8 p).run m).run = some (.error .unspecified) := by
  have h := concurrent_throwsB
  revert h
  generalize ((Zig.atomicLoadAt (n := 64) 0 .relaxed 8 p).run m).run = res
  rcases res with _ | (e | x)
  · simp
  · cases e <;> simp
  · simp

/-- Thread 0's bytes: `0..8` of block 0. -/
def hP : Heap := fun l => if l.1 = 0 ∧ l.2 < 8 then m.heap l else none

/-- The frame: the other bytes (thread 1's). -/
def hF : Heap := fun l => if l.1 = 0 ∧ l.2 < 8 then none else m.heap l

theorem heap_word : ∀ x < 8, m.heap (0, x) = some ⟨.int 0, 4096, 16, .heap⟩ := by decide

theorem tag_word : ∀ x < 8, tagOf (shapes m) 0 x = some (0, 16) := by decide

/-- Thread 0's bytes are the word `p ↦ 0`, with the constraint of the 16-byte location. -/
theorem word : wpts p 0 ⟨FHeap.ofHeap (shapes m) hP, Know.none, Ghost.unit⟩ := by
  refine ⟨4096, 16, .heap, Array.replicate 8 (.int 0), some (0, 16), by decide, by decide, rfl,
    rfl, rfl, rfl, 0, rfl, by decide, fun ⟨b, x⟩ => ?_⟩
  have hp0 : p.off.toNat = 0 := rfl
  simp only [FHeap.ofHeap, hP, hp0, Array.size_replicate, Nat.zero_add, Nat.zero_le, true_and,
    Nat.sub_zero]
  by_cases hc : b = 0 ∧ x < 8
  · obtain ⟨rfl, hx⟩ := hc
    simp [hx, heap_word x hx, tag_word x hx]
  · simp [hc]

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
  rcases hc with ⟨x, hx1, -, hx⟩ | hb
  · exact (hx (by simp only [wr] at hx1; simp [hP, wr]; omega)).elim
  · simp [m, wr] at hb

/-- **No thread rule for a `wpts` word**: whatever the postcondition, the thread triple of the
load from `wpts p 0` is false. -/
theorem w_load_no_thread_rule (Q : BitVec 64 → FAssn) :
    ¬ FTTriple (wpts p 0) (Zig.atomicLoadAt (n := 64) 0 .relaxed 8 p) Q := by
  intro h
  have := h m _ _ holds word fconc owns
  rw [concurrent_throws] at this
  cases this

/-- The same memory after thread 0 joined thread 1 (its clock is past the write). -/
def mj : Mem :=
  { m with clocks := #[#[1, 1], #[0, 1]],
           threads := #[{ spawner := 0, joined := true }, { spawner := 0, joined := true }] }

/-- **Sequentially** (every access happened before) the load retires the location and reads the
word. -/
theorem seq_reads :
    (match ((Zig.atomicLoadAt (n := 64) 0 .relaxed 8 p).run mj).run with
      | some (.ok (v, m')) => v == 0 && m'.atomics.size == 1 && (m'.atomics[0]!).len == 8
      | _ => false) = true := by
  decide +kernel

end Zig.AtomicRetireCX

#print axioms Zig.AtomicRetireCX.concurrent_throws
#print axioms Zig.AtomicRetireCX.w_load_no_thread_rule
#print axioms Zig.AtomicRetireCX.seq_reads
