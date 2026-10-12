import Proofs.Pointers.Gen
import ZigLean.VC

/-!
# Result-existence and total VCs (P05)

`vc_gen` on `TotalTriple pre (f xs) post` and `Returns pre (f xs)` goals: the same generated
obligations as for the partial `Triple`, with every memory call required to have a total
contract (`MemProgram.AllTotal`, `ZigLean/VC/Total.lean`). A `Returns` goal asks exactly the
result-existence obligations: safety, memory ownership and sizes, and callee preconditions; its
postcondition obligation is `True` and is closed at once. A memory call with only a partial
(`Triple`) contract refuses a total goal.
-/

open Zig Zig.VC Assn

namespace VcTotal

/-- Total correctness of the generated `addTo`: the obligations of the partial contract, and the
run returns. -/
theorem addTo_total (p : Ptr) (delta : BitVec 32) (old : BitVec 64)
    (fits : old.toNat + (delta.setWidth 64).toNat < 2 ^ 64) :
    TotalTriple (pts p 8 old) (Pointers.addTo p delta)
      (fun _ => pts p 8 (old + delta.setWidth 64)) := by
  vc_gen
  case memory_1 => decide
  case safety_1 => decide
  case safety_2 => exact fits
  case memory_2 => decide
  case memory_4 => exact stored1

/-- info: vc_gen obligations for `Pointers.addTo` (4 open of 6):
  [memory_1] memory: loaded type has positive size
    heap : Heap
    pre : pts p 8 old heap
    ⊢ 0 < Enc.size (BitVec 64)
  [safety_1] safety: unsigned cast widens
    heap : Heap
    pre : pts p 8 old heap
    ⊢ 32 ≤ 64
  [safety_2] safety: unsigned addition does not overflow
    heap : Heap
    pre : pts p 8 old heap
    ⊢ old.toNat + (BitVec.setWidth 64 delta).toNat < 2 ^ 64
  [memory_2] memory: stored type has positive size
    heap : Heap
    pre : pts p 8 old heap
    ⊢ 0 < Enc.size (BitVec 64)
  [memory_3] memory: owned cell for the store (closed by hypothesis)
    heap : Heap
    pre : pts p 8 old heap
    ⊢ ∃ old, pts p 8 old heap
  [memory_4] memory: postcondition (closed by trivial)
    heap : Heap
    pre : pts p 8 old heap
    heap1 : Heap
    stored1 : pts p 8 (old + BitVec.setWidth 64 delta) heap1
    ⊢ True
vc-report {"function":"Pointers.addTo","obligations":[{"case":"memory_1","closed_by":null,"given":["heap : Heap","pre : pts p 8 old heap"],"goal":"0 < Enc.size (BitVec 64)","kind":"memory","label":"loaded type has positive size"},{"case":"safety_1","closed_by":null,"given":["heap : Heap","pre : pts p 8 old heap"],"goal":"32 ≤ 64","kind":"safety","label":"unsigned cast widens"},{"case":"safety_2","closed_by":null,"given":["heap : Heap","pre : pts p 8 old heap"],"goal":"old.toNat + (BitVec.setWidth 64 delta).toNat < 2 ^ 64","kind":"safety","label":"unsigned addition does not overflow"},{"case":"memory_2","closed_by":null,"given":["heap : Heap","pre : pts p 8 old heap"],"goal":"0 < Enc.size (BitVec 64)","kind":"memory","label":"stored type has positive size"},{"case":"memory_3","closed_by":"hypothesis","given":["heap : Heap","pre : pts p 8 old heap"],"goal":"∃ old, pts p 8 old heap","kind":"memory","label":"owned cell for the store"},{"case":"memory_4","closed_by":"trivial","given":["heap : Heap","pre : pts p 8 old heap","heap1 : Heap","stored1 : pts p 8 (old + BitVec.setWidth 64 delta) heap1"],"goal":"True","kind":"memory","label":"postcondition"}],"status":"obligations"} -/
#guard_msgs in
/-- Result existence: exactly the safety and memory obligations, no functional one. -/
theorem addTo_returns (p : Ptr) (delta : BitVec 32) (old : BitVec 64)
    (fits : old.toNat + (delta.setWidth 64).toNat < 2 ^ 64) :
    Returns (pts p 8 old) (Pointers.addTo p delta) := by
  vc_gen?
  case memory_1 => decide
  case safety_1 => decide
  case safety_2 => exact fits
  case memory_2 => decide

/-! ## A partial callee refuses a total goal -/

/-- A partial contract of `addTo` (it says nothing about divergence). -/
theorem addTo_partial (p : Ptr) :
    Triple (Assn.ex fun old : BitVec 64 => ⌜old.toNat + 1 < 2 ^ 64⌝ ∗ pts p 8 old)
      (Pointers.addTo p 1) (fun _ => Assn.ex fun v : BitVec 64 => pts p 8 v) :=
  Triple.ex fun old => Triple.lift fun fits =>
    (addTo_total p 1 old (by simpa using fits)).toPartial.conseq (fun _ h => h) (fun _ _ h => ⟨_, h⟩)

attribute [vc_contract] addTo_partial

/-- A caller of `addTo` (in the generated shape). -/
def bumpOnce (p : Ptr) : MemM Unit := do
  Pointers.addTo p 1

/-- The partial contract gives the caller's partial triple (extraction succeeds). -/
example (p : Ptr) (old : BitVec 64) (fits : old.toNat + 1 < 2 ^ 64) :
    Triple (pts p 8 old) (bumpOnce p) (fun _ => Assn.ex fun v : BitVec 64 => pts p 8 v) := by
  vc_gen
  all_goals first | exact ⟨old, sep_lift.mpr ⟨fits, pre⟩⟩ | exact summary1

/-- error: vc_gen: a total or result-existence goal needs a total contract (`TotalTriple`) for every memory call of `VcTotal.bumpOnce`; these calls have none:
  TotalTriple (ex fun old => ⌜old.toNat + 1 < 2 ^ 64⌝ ∗ pts p 8 old) (Pointers.addTo p 1#32) fun x =>
    ex fun v => pts p 8 v -/
#guard_msgs in
/-- It refuses the caller's total triple: `AllTotal` asks the callee's `TotalTriple`, which a
partial contract does not provide. -/
example (p : Ptr) (old : BitVec 64) :
    TotalTriple (pts p 8 old) (bumpOnce p) (fun _ => Assn.ex fun v : BitVec 64 => pts p 8 v) := by
  vc_gen

/-- error: vc_gen: a total or result-existence goal needs a total contract (`TotalTriple`) for every memory call of `VcTotal.bumpOnce`; these calls have none:
  TotalTriple (ex fun old => ⌜old.toNat + 1 < 2 ^ 64⌝ ∗ pts p 8 old) (Pointers.addTo p 1#32) fun x =>
    ex fun v => pts p 8 v -/
#guard_msgs in
example (p : Ptr) (old : BitVec 64) : Returns (pts p 8 old) (bumpOnce p) := by
  vc_gen

end VcTotal

/-- info: 'VcTotal.addTo_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms VcTotal.addTo_total
