import ZigLean.Sep.Full.Const
import ZigLean.Sep.Full.Thread
import ZigLean.Sep.Full.Strength

/-!
# A `const` read records an access on the frame's bytes: no thread `cload` (S1 task 4)

`FTotalTriple.cload` reads a `const` global from knowledge alone (`cpts`, owns nothing). The
bytes it reads may belong to the frame: `cbytesAt_intro` hands out the knowledge and keeps the
bytes, and the frame of a thread step is any resource the memory holds. `Zig.load` records a
`.read` footprint entry on the bytes it reads, and `FStepIn` (the step relation of `FTTriple`)
allows a new entry only if it touches no byte of the frame. So the thread version of `cload`
is false as stated, whatever the postcondition, and an invariant about `const` blocks in
`FConc`/`FOwned` alone does not repair it: the step relation itself rejects the read.

Block 0 is a live 1-byte `const` global (address 4096). One thread, empty footprint. The thread
holds `cpts p 1 0` (knowledge only); the frame owns the byte.

* `holds`, `fconc`, `owns`: every premise of `FTTriple` holds at `m`.
* `run_records`: the load returns `0` and records an entry on byte `(0, 0)`.
* `cload_no_thread_rule`: no thread triple with precondition `cpts p 1 0` holds for the load.

Kernel-checked; the expected axioms are `propext`, `Classical.choice`, `Quot.sound` at most.
-/

namespace Zig.ConstReadCX

open Zig Zig.Full

/-- One `const` byte. -/
def blk : Block :=
  { bytes := #[.int 0], align := 1, kind := .constGlobal, live := true, addr := 4096 }

/-- One thread, nothing recorded. -/
def m : Mem :=
  { blocks := #[blk], current := 0, clocks := #[#[1]],
    threads := #[{ spawner := 0, joined := true }] }

def p : Ptr := ⟨some 0, 0⟩

/-- The knowledge `cpts p 1 0` is made of. -/
def kc : Know := cknow 0 4096 0 #[.int 0]

/-- The thread's resource: the knowledge, no bytes. -/
def rC : Res := ⟨FHeap.empty, kc, Ghost.unit⟩

/-- The frame: every byte (here the `const` byte). -/
noncomputable def rF : Res := ⟨FHeap.ofHeap (shapes m) m.heap, Know.none, Ghost.exts (heapExts m m.heap)⟩

theorem hc : cpts p 1 (0 : BitVec 8) rC :=
  ⟨4096, #[.int 0], by decide, rfl, rfl, rfl, rfl, 0, rfl, by decide, rfl⟩

theorem holds : Holds m rC rF := by
  have h0 := holds_ofHeap (m := m) (hP := fun _ => none) (hF := m.heap) (fun _ => .inl rfl)
    (funext fun l => by simp [Heap.union_apply])
  have h1 := Holds.addKnow (k := kc)
    (Mem.kn_const (m := m) (b := 0) (blk := blk) rfl rfl rfl fun i hi => by
      simp only [List.size_toArray, List.length_cons, List.length_nil] at hi
      have : i = 0 := by omega
      subst this; rfl) h0
  have e : FHeap.ofHeap (shapes m) (fun _ => none) = FHeap.empty := funext fun _ => rfl
  simp only [e, Know.none_union] at h1
  exact h1

theorem fconc : m.FConc := by
  refine ⟨by decide, ⟨by simp [shapes, m], by simp [shapes, m]⟩,
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

theorem owns : m.Owns m.current rC.heap.erase := fun e he => by simp [m] at he

theorem run_recordsB :
    (match ((Zig.load (BitVec 8) 1 p).run m).run with
      | some (.ok (v, m')) =>
        v == 0 && m'.footprint.any fun e => e.block == 0 && e.off == 0 && e.len == 1
      | _ => false) = true := by
  decide +kernel

/-- **The load succeeds and records an access on the `const` byte.** -/
theorem run_records : ∃ m', ((Zig.load (BitVec 8) 1 p).run m).run = some (.ok (0, m')) ∧
    ∃ e ∈ m'.footprint, e.block = 0 ∧ e.off = 0 ∧ e.len = 1 := by
  have h := run_recordsB
  revert h
  generalize ((Zig.load (BitVec 8) 1 p).run m).run = res
  rcases res with _ | (e | ⟨v, m'⟩)
  · simp
  · simp
  · intro h
    simp only [Bool.and_eq_true, beq_iff_eq, Array.any_eq_true] at h
    obtain ⟨hv, i, hi, ⟨hb, ho⟩, hl⟩ := h
    subst hv
    exact ⟨m', rfl, _, Array.getElem_mem hi, hb, ho, hl⟩

/-- **No thread rule for a `const` read from knowledge**: whatever the postcondition, the thread
triple of the load from `cpts p 1 0` is false (the frame owns the byte the load records). -/
theorem cload_no_thread_rule (Q : BitVec 8 → FAssn) :
    ¬ FTTriple (cpts p 1 (0 : BitVec 8)) (Zig.load (BitVec 8) 1 p) Q := by
  intro h
  have ht := h m rC rF holds hc fconc owns
  obtain ⟨m', hrun, e, he, hb, ho, hl⟩ := run_records
  rw [hrun] at ht
  obtain ⟨-, -, -, -, -, hst⟩ := ht
  rcases hst.fp e he with ⟨e₀, he₀, -⟩ | ⟨-, hT, -⟩
  · simp [m] at he₀
  · apply hT
    refine ⟨0, by omega, by omega, ?_⟩
    simp only [rF, FHeap.ofHeap_erase, hb]
    decide

end Zig.ConstReadCX

#print axioms Zig.ConstReadCX.run_records
#print axioms Zig.ConstReadCX.cload_no_thread_rule
