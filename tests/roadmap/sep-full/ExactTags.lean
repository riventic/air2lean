import ZigLean.Sep.Full.Atomic

/-!
# Why atomic tags are constraints (regression, `docs/sep-full-state.md` §Atomic tags)

The full-state logic first read a resource's atomic tags exactly: a memory held `r` and the frame
`rF` only if each owned byte's tag was the location over it in the memory (`HoldsExact`, the
old `Holds`). Then no atomic op on bytes owned as plain (`up`) bytes has a triple
(`no_plain_atomic_triple`): a location over those bytes **and the frame's** (here a 16-byte one;
`u128` atomics are in the subset) is retired by the op (`retireAt`, memory reused for another
object), so the frame's tags change, and no resource after the op holds with the same frame.

The logic now reads a tag `some t` as a constraint, "the location over the byte is `t` or
none" (`TagSat`, `FMatch`): a retire only removes locations, so every frame constraint stays
true. The same store from the same plain bytes has a triple (`plain_atomic_triple`), whose
postcondition is an `apts`.
-/

namespace Zig.Full.CX
open FAssn

/-- The old `Holds`: the memory's full heap, tags included, is exactly the union. -/
structure HoldsExact (m : Mem) (r rF : Res) : Prop where
  disj : FHeap.Disjoint r.heap rF.heap
  heap : m.fheap = r.heap ∪ rF.heap
  know : Know.Sub r.know m.kn
  knowF : Know.Sub rF.know m.kn
  ghost : Ghost.Ok r.gh rF.gh

/-- The old `FTriple`, over `HoldsExact`. -/
def FTripleExact {α : Type} (P : FAssn) (c : MemM α) (Q : α → FAssn) : Prop :=
  ∀ m r rF, HoldsExact m r rF → P r → m.FSeq →
    match (c.run m).run with
    | none => True
    | some (.error _) => False
    | some (.ok (v, m')) => ∃ r', HoldsExact m' r' rF ∧ Q v r' ∧ m'.FSeq

def z8 : Array Byte := Array.replicate 8 (.int 0)
def blk0 : Block := { bytes := Array.replicate 16 (.int 0), align := 16, kind := .heap, live := true, addr := 16 }
def msg0 : Msg := Msg.mk 0 (Array.replicate 16 (.int 0)) #[] #[] none none
def loc0 : ALoc := ALoc.mk 0 0 16 #[msg0]
/-- One 16-byte block whose bytes carry one 16-byte atomic location. -/
def m0 : Mem := { blocks := #[blk0], atomics := #[loc0], nextMsg := 1 }
def p8 : Ptr := ⟨some 0, 8⟩
def run1 := ((atomicStoreAt (n := 64) 0 .relaxed 8 p8 0).run m0).run
theorem run1_shapes : (run1.map fun r => r.map fun x => shapes x.2) = some (.ok [(0, 8, 8)]) := by
  decide +kernel
theorem run1_heap : (run1.map fun r => r.map fun x => x.2.heap (0, 0)) =
    some (.ok (some ⟨.int 0, 16, 16, .heap⟩)) := by
  decide +kernel

/-- The owned half and the frame half of `m0`'s block. -/
def r : Res := ⟨fun l => if l.1 = 0 ∧ 8 ≤ l.2 then m0.fheap l else none, Know.none, Ghost.unit⟩
def rF : Res := ⟨fun l => if l.1 = 0 ∧ l.2 < 8 then m0.fheap l else none, Know.none, Ghost.unit⟩

theorem ok_unit : Ghost.Ok Ghost.unit Ghost.unit := (GOk.unit {}).1

theorem m0_heap (l : Loc) : m0.heap l = if l.1 = 0 ∧ l.2 < 16 then some ⟨.int 0, 16, 16, .heap⟩ else none := by
  obtain ⟨b, o⟩ := l
  simp only [Mem.heap, m0, blk0]
  rcases b with _ | b
  · by_cases ho : o < 16 <;> simp [ho, BlockKind.mappedLo]
  · simp

theorem holds0 : HoldsExact m0 r rF := by
  refine ⟨fun l => ?_, funext fun l => ?_, Know.sub_none _, Know.sub_none _, by simpa [r, rF] using ok_unit⟩
  · by_cases h : 8 ≤ l.2
    · right; show (if l.1 = 0 ∧ l.2 < 8 then _ else none) = none; rw [if_neg (by omega)]
    · left; show (if l.1 = 0 ∧ 8 ≤ l.2 then _ else none) = none; rw [if_neg (by omega)]
  · obtain ⟨b, o⟩ := l
    show m0.fheap (b, o) = ((if b = 0 ∧ 8 ≤ o then m0.fheap (b, o) else none).or
      (if b = 0 ∧ o < 8 then m0.fheap (b, o) else none))
    by_cases h1 : b = 0
    · by_cases h2 : 8 ≤ o
      · rw [if_pos ⟨h1, h2⟩, if_neg (by omega)]; cases m0.fheap (b, o) <;> rfl
      · rw [if_neg (by omega), if_pos ⟨h1, by omega⟩]; rfl
    · simp [Mem.fheap, m0_heap, h1]

theorem seq0 : m0.FSeq := by
  refine ⟨⟨⟨by decide, by simp [m0]⟩⟩, ⟨by simp [shapes, m0, loc0, ALoc.shape], by simp [shapes, m0, loc0, ALoc.shape]⟩, ?_, fun b blk hb _ => ?_⟩
  · intro b b' blk blk' hne hb hb' _
    simp only [m0] at hb hb'
    rcases b with _ | b <;> rcases b' with _ | b' <;> simp at hb hb' hne
  · simp only [m0] at hb
    rcases b with _ | b <;> simp at hb
    subst hb; simp [blk0]

theorem pre0 : up (bytesAt p8 16 16 .heap z8) r := by
  refine ⟨⟨0, rfl, by decide, fun l => ?_⟩, rfl, rfl⟩
  obtain ⟨b, o⟩ := l
  show ((if b = 0 ∧ 8 ≤ o then m0.fheap (b, o) else none).map (·.cell)) = _
  simp only [Mem.fheap, m0_heap, p8, z8]
  by_cases hb : b = 0
  · subst hb
    by_cases ho : 8 ≤ o
    · by_cases ho' : o < 16
      · simp [ho, ho', getElem!_def, show o - 8 < 8 by omega]
      · simp [ho, ho']
    · simp [ho]
  · simp [hb]

/-- **With exact tags, no atomic rule for plainly owned bytes.** An 8-byte atomic store into
bytes that the precondition owns as plain (`up`) bytes has no postcondition: a 16-byte location
over them and the frame's bytes is retired, so the frame's atomic tags change. -/
theorem no_plain_atomic_triple (Q : Unit → FAssn) :
    ¬ FTripleExact (up (bytesAt p8 16 16 .heap z8)) (atomicStoreAt (n := 64) 0 .relaxed 8 p8 0) Q := by
  intro h
  have hF : rF.heap (0, 0) = some ⟨⟨.int 0, 16, 16, .heap⟩, some (0, 16)⟩ := by
    show (if (0 : Nat) = 0 ∧ (0 : Nat) < 8 then m0.fheap (0, 0) else none) = _
    rw [if_pos ⟨rfl, by decide⟩]
    simp only [Mem.fheap, m0_heap]
    rfl
  have hx := h m0 r rF holds0 pre0 seq0
  have hs := run1_shapes
  have hc := run1_heap
  unfold run1 at hs hc
  revert hx hs hc
  generalize ((atomicStoreAt (n := 64) 0 .relaxed 8 p8 0).run m0).run = x
  rcases x with _ | _ | ⟨⟨⟩, m'⟩
  · intro _ hs; cases hs
  · intro _ hs; cases hs
  intro hx hs hc
  simp only [Option.map_some, Except.map, Option.some.injEq, Except.ok.injEq] at hs hc
  obtain ⟨r', hh, -, -⟩ := hx
  have e := congrFun hh.heap (0, 0)
  have hr' : r'.heap (0, 0) = none := by
    rcases hh.disj (0, 0) with x | x
    · exact x
    · rw [hF] at x; cases x
  rw [FHeap.union_apply, hr', hF, Option.none_or] at e
  simp [Mem.fheap, hs, hc, tagOf, Covers] at e

/-- **With tag constraints, the store has a triple**: the plain bytes, unconstrained, are a word
for an atomic op (`wpts_of_up`, `FTriple.untag`), and afterwards an `apts`. -/
theorem plain_atomic_triple :
    FTriple (up (bytesAt p8 16 16 .heap z8)) (atomicStoreAt (n := 64) 0 .relaxed 8 p8 0)
      (fun _ => apts p8 0) :=
  FTriple.untag (fun _ h => wpts_of_up (v := 0) (by decide) (by decide) rfl rfl h)
    (FTriple.atomicStoreW p8 0 0 .relaxed)

end Zig.Full.CX

-- `ci.yml` (Full-state separation logic) requires only the standard axioms.
#print axioms Zig.Full.CX.no_plain_atomic_triple
#print axioms Zig.Full.CX.plain_atomic_triple
