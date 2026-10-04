import ZigLean.Sep.Total

open Zig Assn

private def diverge : MemM Unit := fun _ => ExceptT.mk none
private def safetyPanic : MemM Unit := throw Error.panic

-- This is intentional partial-correctness behavior, including a false postcondition.
example (P : Assn) : Triple P diverge (fun _ _ => False) := by
  intro m hP hF hd hm hp hs
  trivial

-- Any actual admissible input witnesses that divergence cannot have a total triple.
example (P : Assn) (Q : Unit → Assn) (m : Mem) (hP hF : Heap)
    (hd : Heap.Disjoint hP hF) (hm : m.heap = hP ∪ hF) (hp : P hP) (hs : m.Seq) :
    ¬ TotalTriple P diverge Q := by
  intro ht
  obtain ⟨v, m', hQ, hr, _⟩ := ht m hP hF hd hm hp hs
  change none = some (Except.ok (v, m')) at hr
  cases hr

-- A safety panic likewise cannot have a successful-result witness.
example (P : Assn) (Q : Unit → Assn) (m : Mem) (hP hF : Heap)
    (hd : Heap.Disjoint hP hF) (hm : m.heap = hP ∪ hF) (hp : P hP) (hs : m.Seq) :
    ¬ TotalTriple P safetyPanic Q := by
  intro ht
  obtain ⟨v, m', hQ, hr, _⟩ := ht m hP hF hd hm hp hs
  change some (Except.error Error.panic) = some (Except.ok (v, m')) at hr
  cases hr

-- Total triples expose both ordinary correctness and the explicit return witness.
example (P : Assn) (c : MemM Unit) (Q : Unit → Assn) (ht : TotalTriple P c Q) :
    Triple P c Q ∧ Returns P c := ⟨ht.toPartial, ht.returns⟩

example (P : Assn) (c : MemM Unit) (Q : Unit → Assn)
    (ht : Triple P c Q) (hr : Returns P c) : TotalTriple P c Q :=
  TotalTriple.of_partial ht hr

-- Returned Zig errors are values, and do satisfy total correctness.
example (P : Assn) :
    TotalTriple P (pure (.error "OutOfMemory") : MemM (Except ErrName Unit)) (fun _ => P) :=
  TotalTriple.ret (Q := fun _ => P) (Except.error "OutOfMemory" : Except ErrName Unit)

-- A real loop terminates because the locals' countdown strictly decreases.
private def countdown : MM Nat Bool := fun n => pure (n != 0, n - 1)

example (P : Assn) (n : Nat) :
    TotalTriple P ((Zig.loop countdown id).run n) (fun r h => r.1 = false ∧ P h) := by
  have ht := TotalTriple.loop_ghost countdown id
    (fun s k h => s = k ∧ P h) (fun e _ h => e = false ∧ P h)
    (fun hF s k m h hd hm hi hs => by
      obtain ⟨rfl, hp⟩ := hi
      cases s with
      | zero =>
        exact ⟨false, 0, m, h, rfl, hd, hm, hs, by simpa using hp⟩
      | succ s =>
        refine ⟨true, s, m, h, rfl, hd, hm, hs, ?_⟩
        exact ⟨s, Nat.lt_succ_self s, rfl, hp⟩)
    n n
  exact ht.conseq (fun _ hp => ⟨rfl, hp⟩) (fun _ _ hp => hp)
