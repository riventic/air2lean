import ZigLean.VC.Mem

open Zig Assn VC

-- The constructor's encoding dictionary is retained even without an active Enc instance.
example (T : Type) (enc : Enc T) (p : Ptr) (alignment : Nat) (old : T) :
    (@MemProgram.read T enc p alignment old).eval = @Zig.load T enc alignment p := rfl

example (T : Type) (enc : Enc T) (p : Ptr) (alignment : Nat) (old : T)
    (Q : T → Assn) (h : Heap) :
    MemProgram.vc (@MemProgram.read T enc p alignment old) Q h ↔
      0 < @Enc.size T enc ∧ @pts T enc p alignment old h ∧ Q old h := Iff.rfl

example (T : Type) (enc : Enc T) (lawful : @LawfulEnc T enc)
    (p : Ptr) (alignment : Nat) (old value : T) :
    (@MemProgram.write T enc lawful p alignment old value).eval =
      @Zig.store T enc alignment p value := rfl

-- Ownership and a positive access size are generated rather than assumed by the AST.
example (p : Ptr) (old : BitVec 32) (Q : BitVec 32 → Assn) (h : Heap) :
    MemProgram.vc (.read p 4 old) Q h ↔ 0 < Enc.size (BitVec 32) ∧ pts p 4 old h ∧ Q old h :=
  Iff.rfl

example (p : Ptr) (old value : BitVec 32) (Q : Unit → Assn) (h : Heap) :
    MemProgram.vc (.write p 4 old value) Q h ↔
      0 < Enc.size (BitVec 32) ∧ pts p 4 old h ∧ ∀ h', pts p 4 value h' → Q () h' := Iff.rfl

-- A fabricated functional/memory postcondition cannot ignore an actual output heap.
example (p : Ptr) (old value : BitVec 32) (h h' : Heap) (hp' : pts p 4 value h') :
    ¬ MemProgram.vc (.write p 4 old value) (fun _ _ => False) h := by
  intro hvc
  exact hvc.2.2 h' hp'

-- A lifted arithmetic operation keeps the owned heap; overflow is still an obligation.
example (h : Heap) :
    ¬ MemProgram.vc (.lift (.add (255#8) (1#8))) (fun _ _ => True) h := by
  simp only [MemProgram.vc, ResultProgram.vc] <;> decide

-- A lifted Zig error-union return follows its own memory postcondition.
example (h : Heap) (Q : Except ErrName Nat → Assn) :
    MemProgram.vc (.lift (.ret (Except.error "Empty" : Except ErrName Nat))) Q h ↔
      Q (Except.error "Empty") h := Iff.rfl

-- Checked modular calls expose, rather than erase, the callee-to-client entailment.
example (P : Assn) (c : MemM Unit) (S Q : Unit → Assn) (hc : Triple P c S) (h : Heap) :
    MemProgram.vc (.call "callee" c P S hc) Q h ↔
      P h ∧ ∀ value h', S value h' → Q value h' := Iff.rfl

-- Raw loops have no AST constructor; a user must provide an explicit proved call contract.
example : True := by
  fail_if_success
    have : MemProgram Unit := MemProgram.loop
  trivial

-- Annotation is explicit: neither the invariant nor the variant is synthesized.
private def exitBody : MM Unit Bool := fun _ => pure (false, ())

example (P : Assn) :
    MemProgram.obligation P
      (MemProgram.annotatedLoop exitBody id (fun _ => P) (fun _ => 0)
        (fun e _ h => e = false ∧ P h)
        (fun _ _ m h hd hm hp hs =>
          ⟨false, (), m, h, rfl, hd, hm, hs, by simpa using hp⟩) ())
      (fun result h => result.1 = false ∧ P h) := by
  intro h hp
  exact ⟨hp, fun _ _ hpost => hpost⟩
