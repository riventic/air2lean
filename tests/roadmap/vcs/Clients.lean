import ZigLean.VC
import Proofs.Pointers.Gen

namespace VCClients

open Zig Assn VC

-- Ghost values annotate reads/writes; they do not change eval's runtime behavior.
def addToProgram (p : Ptr) (delta : BitVec 32) (old : BitVec 64) : MemProgram Unit :=
  .bind (.read p 8 old) fun loaded =>
  .bind (.lift (.widen delta 64)) fun widened =>
  .bind (.lift (.add loaded widened)) fun sum =>
  .write p 8 loaded sum

def addToPre (p : Ptr) (delta : BitVec 32) (old : BitVec 64) : Assn := fun h =>
  pts p 8 old h ∧ old.toNat + (delta.setWidth 64).toNat < 2 ^ 64

-- This kernel-checked equality links the proof AST to actual committed generated code.
theorem addTo_source (p : Ptr) (delta : BitVec 32) (old : BitVec 64) :
    (addToProgram p delta old).eval = Pointers.addTo p delta := by
  funext m
  simp [addToProgram, MemProgram.eval, ResultProgram.eval, Pointers.addTo, zig_unfold]

-- The generated obligation exposes positive size, ownership, widening, overflow, and
-- the heap postcondition. Neither the intermediate memories nor an invariant is guessed.
theorem addTo_obligations (p : Ptr) (delta : BitVec 32) (old : BitVec 64) :
    MemProgram.obligation (addToPre p delta old) (addToProgram p delta old)
      (fun _ => pts p 8 (old + delta.setWidth 64)) := by
  intro h ⟨hp, hb⟩
  exact ⟨by decide, hp, by decide, hb, by decide, hp, fun _ hp' => hp'⟩

theorem addTo_spec (p : Ptr) (delta : BitVec 32) (old : BitVec 64) :
    Triple (addToPre p delta old) (Pointers.addTo p delta)
      (fun _ => pts p 8 (old + delta.setWidth 64)) := by
  rw [← addTo_source p delta old]
  exact MemProgram.verify (addTo_obligations p delta old)

-- A separate client resource is preserved by the existing separation frame rule.
example (p : Ptr) (delta : BitVec 32) (old : BitVec 64) (R : Assn) :
    Triple (addToPre p delta old ∗ R) (Pointers.addTo p delta)
      (fun _ => pts p 8 (old + delta.setWidth 64) ∗ R) :=
  (addTo_spec p delta old).frame

def swapSelfProgram (p : Ptr) (old : BitVec 32) : MemProgram Unit :=
  .bind (.read p 4 old) fun x =>
  .bind (.read p 4 x) fun y =>
  .bind (.write p 4 x y) fun _ =>
  .write p 4 y x

theorem swapSelf_source (p : Ptr) (old : BitVec 32) :
    (swapSelfProgram p old).eval = Pointers.swap p p := by
  funext m
  simp [swapSelfProgram, MemProgram.eval, Pointers.swap, zig_unfold]

-- Compare the explicit intermediate-memory proof in Proofs/Pointers/Sep.lean:
-- the client proof here is the computed VC and its soundness theorem.
theorem swapSelf_obligations (p : Ptr) (old : BitVec 32) :
    MemProgram.obligation (pts p 4 old) (swapSelfProgram p old) (fun _ => pts p 4 old) := by
  intro h hp
  exact ⟨by decide, hp, by decide, hp, by decide, hp,
    fun _ hp' => ⟨by decide, hp', fun _ hp'' => hp''⟩⟩

theorem swapSelf_spec (p : Ptr) (old : BitVec 32) :
    Triple (pts p 4 old) (Pointers.swap p p) (fun _ => pts p 4 old) := by
  rw [← swapSelf_source p old]
  exact MemProgram.verify (swapSelf_obligations p old)

end VCClients
