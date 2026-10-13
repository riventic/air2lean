import ZigLean.Sep.Full.Const
import ZigLean.Sep.Full.Thread
import ZigLean.Sep.Full.Strength
import ZigLean.External

/-!
# A `const` read records nothing: the thread `cload` rule (MM-20)

Before MM-20 a load of a `const` global recorded a `.read` footprint entry like any load. The
bytes it reads may belong to the frame (`cbytesAt_intro` hands out the knowledge and keeps the
bytes), and `FStepIn` (the step relation of `FTTriple`) allows a new entry only if it touches no
byte of the frame, so no thread version of `cload` held: for the memory below, every thread
triple with precondition `cpts p 1 0` for the load was false (kernel-checked counterexample
`cload_no_thread_rule`, `codex/csl-s1-const` 08f34cd8e).

MM-20 changes the model, not the logic: no step ever records a write to a `const` global (a
write access to one throws `.illegal` before recording), so a read of one races with nothing, and
it records nothing (`recordAccessIn`). The same memory and resources now give:

* `run_unchanged`: the load returns `0` and leaves the memory exactly as it was;
* `cload_thread`: the thread rule `FTTotalTriple.cload` holds, here at the old counterexample's
  memory, resource and frame (every premise of `FTTriple` holds there: `holds`, `fconc`,
  `owns`), with the frame's step relation `FStepIn` met;
* `write_claim_illegal`, `read_claim_records_nothingB`, `write_kind_load_illegal`: the other
  recording paths that reach a `const` global keep "no write is ever recorded on one" (an
  external model's write claim, a `loadBytes` with a write kind) or record nothing (a read claim).

Block 0 is a live 1-byte `const` global (address 4096). One thread, empty footprint.

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

/-- The run, computed by the kernel: the value `0`, no footprint entry, the clock unchanged. -/
theorem run_unchangedB :
    (match ((Zig.load (BitVec 8) 1 p).run m).run with
      | some (.ok (v, m')) => v == 0 && m'.footprint.isEmpty && m'.clocks == m.clocks
      | _ => false) = true := by
  decide +kernel

/-- **A `const` load changes nothing** (`Zig.load_const`). -/
theorem run_unchanged : (Zig.load (BitVec 8) 1 p).run m = pure (0, m) :=
  Zig.load_const (b := 0) (blk := blk) (o := 0) (by decide +kernel) (by decide +kernel) rfl

/-- **The thread rule for a `const` read from knowledge**, at the old counterexample: the load
succeeds with `0`, the knowledge stays, and the step is an `FStepIn` of the frame that owns the
byte. -/
theorem cload_thread :
    match ((Zig.load (BitVec 8) 1 p).run m).run with
    | none => True
    | some (.error e) => e = .stackOverflow
    | some (.ok (v, m')) => ∃ r', Holds m' r' rF ∧ (⟪v = 0⟫ ⋆ cpts p 1 (0 : BitVec 8)) r' ∧
        m'.FConc ∧ m'.Owns m'.current r'.heap.erase ∧ FStepIn rF.heap.erase m m' :=
  (FTTotalTriple.cload (p := p) (a := 1) (v := (0 : BitVec 8)) (by decide)).1 m rC rF holds hc
    fconc owns

/-- An external model's write claim of a `const` global throws `.illegal` before recording. -/
theorem write_claim_illegal : ((External.claim p .write).run m).run = some (.error .illegal) := by
  decide +kernel

/-- A read claim of a `const` global records nothing. -/
theorem read_claim_records_nothingB :
    (match ((External.claim p .read).run m).run with
      | some (.ok ((), m')) => m'.footprint.isEmpty && m'.clocks == m.clocks
      | _ => false) = true := by
  decide +kernel

/-- A `loadBytes` with a write kind on a `const` global throws `.illegal` before recording. -/
theorem write_kind_load_illegal :
    ((Zig.loadBytes p 1 1 .write).run m).run = some (.error .illegal) := by
  decide +kernel

end Zig.ConstReadCX

#print axioms Zig.ConstReadCX.run_unchanged
#print axioms Zig.ConstReadCX.cload_thread
#print axioms Zig.ConstReadCX.write_claim_illegal
