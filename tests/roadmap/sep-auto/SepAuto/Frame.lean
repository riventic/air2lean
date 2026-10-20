import ZigLean.Sep.Full.Auto

/-!
# Frame inference of `fsym` (`docs/proof-automation.md`)

The scenarios of the retired `sep_normalize`/`sep_frame` regressions, in the full-state logic: a
caller's rule (`fsym [rule]`) about part of the precondition is framed, the frame is found in any
order and with repeated atoms, `emp` is a unit, and 32 atoms are matched in order and out of
order. Rejected: a resource counted twice, a frame dropped from the postcondition, a rule about
another command, a different encoding instance. A store rule's implicit pointer is fixed by the
command before its precondition is matched, and a framed total step stays total.
-/

namespace SepAuto.Frame

open Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto

set_option linter.unusedVariables false

/-- The frame is inferred, with its repeated atoms and `emp`. -/
theorem repeated (P Q R : FAssn) (c : MemM Unit) (rule : FTotalTriple P c (fun _ => Q)) :
    FTotalTriple ((R ⋆ emp) ⋆ (P ⋆ R)) c (fun _ => R ⋆ (R ⋆ Q)) := by
  fsym [rule]

/-- A rule about nothing frames everything, in any order. -/
theorem all_frame (P Q : FAssn) (c : MemM Unit) (rule : FTotalTriple emp c (fun _ => emp)) :
    FTotalTriple (P ⋆ Q) c (fun _ => Q ⋆ P) := by
  fsym [rule]

/-- A rule about the whole precondition. -/
theorem whole (P : FAssn) (c : MemM Unit) (rule : FTotalTriple P c (fun _ => P)) :
    FTotalTriple P c (fun _ => P) := by
  fsym [rule]

/-- 32 atoms (16, twice) matched in order, the 33rd framed. -/
theorem ordered32 (A B C D E F G H I J K L M N O P R : FAssn) (c : MemM Unit)
    (rule : FTotalTriple
      (A ⋆ B ⋆ C ⋆ D ⋆ E ⋆ F ⋆ G ⋆ H ⋆ I ⋆ J ⋆ K ⋆ L ⋆ M ⋆ N ⋆ O ⋆ P ⋆
       A ⋆ B ⋆ C ⋆ D ⋆ E ⋆ F ⋆ G ⋆ H ⋆ I ⋆ J ⋆ K ⋆ L ⋆ M ⋆ N ⋆ O ⋆ P)
      c (fun _ => emp)) :
    FTotalTriple
      (A ⋆ B ⋆ C ⋆ D ⋆ E ⋆ F ⋆ G ⋆ H ⋆ I ⋆ J ⋆ K ⋆ L ⋆ M ⋆ N ⋆ O ⋆ P ⋆
       A ⋆ B ⋆ C ⋆ D ⋆ E ⋆ F ⋆ G ⋆ H ⋆ I ⋆ J ⋆ K ⋆ L ⋆ M ⋆ N ⋆ O ⋆ P ⋆ R)
      c (fun _ => R) := by
  fsym [rule]

/-- 16 atoms matched in reverse order, two framed. -/
theorem reordered (A B C D E F G H I J K L M N O P R S : FAssn) (c : MemM Unit)
    (rule : FTotalTriple (A ⋆ B ⋆ C ⋆ D ⋆ E ⋆ F ⋆ G ⋆ H ⋆ I ⋆ J ⋆ K ⋆ L ⋆ M ⋆ N ⋆ O ⋆ P)
      c (fun _ => emp)) :
    FTotalTriple (R ⋆ P ⋆ O ⋆ N ⋆ M ⋆ L ⋆ K ⋆ J ⋆ I ⋆ H ⋆ G ⋆ F ⋆ E ⋆ D ⋆ C ⋆ B ⋆ A ⋆ S)
      c (fun _ => S ⋆ R) := by
  fsym [rule]

/-- A frame atom with a non-default encoding instance is kept as it is. -/
theorem enc_frame (T : Type) [Enc T] (e : Enc T) (p : Ptr) (v : T) (P : FAssn)
    (c : MemM Unit) (rule : FTotalTriple P c (fun _ => P)) :
    FTotalTriple (P ⋆ up (@pts T e p 4 v)) c (fun _ => P ⋆ up (@pts T e p 4 v)) := by
  fsym [rule]

/-- A store rule's pointer is fixed by the command: the other cell with the same value is framed. -/
theorem store_ptr (p q : Ptr) (old w : BitVec 32) :
    FTotalTriple (up (pts q 4 old) ⋆ up (pts p 4 old)) (Zig.store 4 p w)
      (fun _ => up (pts q 4 old) ⋆ up (pts p 4 w)) := by
  fsym

/-- Two stores: the second runs from the first's result. -/
theorem two_stores (p : Ptr) (old first last : BitVec 32) :
    FTotalTriple (up (pts p 4 old)) (Zig.store 4 p first >>= fun _ => Zig.store 4 p last)
      (fun _ => up (pts p 4 last)) := by
  fsym

/-- A framed total step is total (the frame rule of the logic, `FTotalTriple.frame`). -/
theorem total_frame (p : Ptr) (x w : BitVec 32) (R : FAssn) :
    FTotalTriple (up (pts p 4 x) ⋆ R) (Zig.store 4 p w) (fun _ => up (pts p 4 w) ⋆ R) :=
  (FTotalTriple.store (by decide) w).frame

/-! ## Rejected attempts -/

/-- One resource cannot be counted twice. -/
example (P : FAssn) (c : MemM Unit) (rule : FTotalTriple (P ⋆ P) c (fun _ => emp)) : True := by
  fail_if_success
    have : FTotalTriple P c (fun _ => emp) := by fsym [rule]
  trivial

/-- 16 atoms cannot meet 32 required occurrences. -/
example (A B C D E F G H I J K L M N O P : FAssn) (c : MemM Unit)
    (rule : FTotalTriple
      (A ⋆ B ⋆ C ⋆ D ⋆ E ⋆ F ⋆ G ⋆ H ⋆ I ⋆ J ⋆ K ⋆ L ⋆ M ⋆ N ⋆ O ⋆ P ⋆
       A ⋆ B ⋆ C ⋆ D ⋆ E ⋆ F ⋆ G ⋆ H ⋆ I ⋆ J ⋆ K ⋆ L ⋆ M ⋆ N ⋆ O ⋆ P)
      c (fun _ => emp)) : True := by
  fail_if_success
    have : FTotalTriple (A ⋆ B ⋆ C ⋆ D ⋆ E ⋆ F ⋆ G ⋆ H ⋆ I ⋆ J ⋆ K ⋆ L ⋆ M ⋆ N ⋆ O ⋆ P)
        c (fun _ => emp) := by
      fsym [rule]
  trivial

/-- A frame cannot disappear from the postcondition. -/
example (P R : FAssn) (c : MemM Unit) (rule : FTotalTriple P c (fun _ => P)) : True := by
  fail_if_success
    have : FTotalTriple (P ⋆ R) c (fun _ => P) := by fsym [rule]
  trivial

/-- An owned cell cannot disappear either. -/
example (p q : Ptr) (x y : BitVec 32) : True := by
  fail_if_success
    have : FTotalTriple (up (pts p 4 x) ⋆ up (pts q 4 y)) (Zig.load (BitVec 32) 4 p)
        (fun _ => up (pts p 4 x)) := by fsym
  trivial

/-- A rule about another command is not used. -/
example (P : FAssn) (c d : MemM Unit) (rule : FTotalTriple P c (fun _ => P)) : True := by
  fail_if_success
    have : FTotalTriple P d (fun _ => P) := by fsym [rule]
  trivial

/-- Distinct encoding instances are not substituted for each other. -/
example (T : Type) (e₁ e₂ : Enc T) (p : Ptr) (v : T) (c : MemM Unit)
    (rule : FTotalTriple (up (@pts T e₁ p 4 v)) c (fun _ => up (@pts T e₁ p 4 v))) : True := by
  fail_if_success
    have : FTotalTriple (up (@pts T e₂ p 4 v)) c (fun _ => up (@pts T e₂ p 4 v)) := by
      fsym [rule]
  trivial

end SepAuto.Frame
