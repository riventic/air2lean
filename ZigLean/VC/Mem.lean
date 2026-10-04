import ZigLean.VC.Result
import ZigLean.Sep.Loop

/-!
# Loop-free verification conditions for framed memory programs

The AST generates primitive access/ownership requirements and postcondition entailments,
then composes them backwards through bind. `sound` connects the generated assertion to the
existing partial `Triple`; a proved modular call may itself be partial. Read/write size
requirements are obligations, not constructor proofs. Frames are preserved by `Triple`.
-/

namespace Zig.VC

open Assn

inductive MemProgram : Type → Type 1 where
  | ret {α : Type} (value : α) : MemProgram α
  | read {T : Type} [Enc T] (pointer : Ptr) (alignment : Nat) (old : T) : MemProgram T
  | write {T : Type} [Enc T] [LawfulEnc T]
      (pointer : Ptr) (alignment : Nat) (old value : T) : MemProgram Unit
  | lift {α : Type} (program : ResultProgram α) : MemProgram α
  | call {α : Type} (label : String) (action : MemM α) (pre : Assn) (post : α → Assn)
      (checked : Triple pre action post) : MemProgram α
  | bind {α β : Type} (first : MemProgram α) (next : α → MemProgram β) : MemProgram β
  | branch {α : Type} (condition : Bool) (yes no : MemProgram α) : MemProgram α

namespace MemProgram

def eval {α : Type} : MemProgram α → MemM α
  | .ret value => pure value
  | .read pointer alignment _ => Zig.load _ alignment pointer
  | .write pointer alignment _ value => Zig.store alignment pointer value
  | .lift program => StateT.lift program.eval
  | .call _ action _ _ _ => action
  | .bind first next => eval first >>= fun value => eval (next value)
  | .branch condition yes no => if condition then eval yes else eval no

def vc {α : Type} (program : MemProgram α) (post : α → Assn) : Assn :=
  match program with
  | .ret value => post value
  | .read (T := T) pointer alignment old => fun h =>
      0 < Enc.size T ∧ pts pointer alignment old h ∧ post old h
  | .write (T := T) pointer alignment old value => fun h =>
      0 < Enc.size T ∧ pts pointer alignment old h ∧
        ∀ h', pts pointer alignment value h' → post () h'
  | .lift program => fun h => program.vc (fun value => post value h)
  | .call _ _ pre summary _ => fun h =>
      pre h ∧ ∀ value h', summary value h' → post value h'
  | .bind first next => vc first (fun value => vc (next value) post)
  | .branch condition yes no => if condition then vc yes post else vc no post

theorem sound {α : Type} (program : MemProgram α) :
    ∀ post, Triple (vc program post) (eval program) post := by
  induction program with
  | ret value =>
    intro post
    exact Triple.ret value
  | read pointer alignment old =>
    intro post
    apply Triple.of_run
    intro m hP hF hd hm hp hs
    obtain ⟨m', hr, hm', hs'⟩ := pts_load_run hp.2.1 hm hp.1 hs
    exact ⟨old, m', hP, hr, hd, hm', hp.2.2, hs'⟩
  | write pointer alignment old value =>
    intro post
    apply Triple.of_run
    intro m hP hF hd hm hp hs
    obtain ⟨m', hr, hs', h', hd', hm', hp'⟩ := pts_store_run hp.2.1 hm hd hp.1 hs value
    exact ⟨(), m', h', hr, hd', hm', hp.2.2 h' hp', hs'⟩
  | lift program =>
    intro post
    apply Triple.of_run
    intro m hP hF hd hm hp hs
    obtain ⟨value, hr, hpost⟩ := program.sound _ hp
    refine ⟨value, m, hP, ?_, hd, hm, hpost, hs⟩
    simp only [eval, StateT.run, StateT.lift, hr, pure_bind]
  | call label action pre summary checked =>
    intro post m hP hF hd hm hp hs
    have hrun := checked m hP hF hd hm hp.1 hs
    split at hrun
    · trivial
    · exact hrun
    · obtain ⟨hQ, hd', hm', hq, hs'⟩ := hrun
      exact ⟨hQ, hd', hm', hp.2 _ _ hq, hs'⟩
  | bind first next ihFirst ihNext =>
    intro post
    exact Triple.bind (ihFirst _) (fun value => ihNext value post)
  | branch condition yes no ihYes ihNo =>
    intro post
    cases condition with
    | false => exact ihNo post
    | true => exact ihYes post

/-- These are generated assertions to establish, not runtime counterexamples. -/
def obligation {α : Type} (pre : Assn) (program : MemProgram α) (post : α → Assn) : Prop :=
  ∀ h, pre h → vc program post h

theorem verify {α : Type} {pre : Assn} {program : MemProgram α} {post : α → Assn}
    (proof : obligation pre program post) : Triple pre (eval program) post :=
  (sound program post).conseq proof (fun _ _ hp => hp)

/-- A loop can only enter through explicit invariant/variant annotations and a proved
iteration contract. Its client VC is the checked summary's pre/post entailment. -/
def annotatedLoop {σ ε : Type} (body : MM σ ε) (again : ε → Bool)
    (invariant : σ → Assn) (variant : σ → Nat) (post : ε → σ → Assn)
    (step : ∀ hF s m h, Heap.Disjoint h hF → m.heap = h ∪ hF → invariant s h → m.Seq →
      ∃ e s' m' h', (body.run s).run m = pure ((e, s'), m') ∧
        Heap.Disjoint h' hF ∧ m'.heap = h' ∪ hF ∧ m'.Seq ∧
        (if again e then invariant s' h' ∧ variant s' < variant s else post e s' h'))
    (initial : σ) : MemProgram (ε × σ) :=
  .call "annotated loop" ((Zig.loop body again).run initial) (invariant initial)
    (fun result => post result.1 result.2) (Triple.of_run fun m hP hF hd hm hi hs => by
      obtain ⟨e, s', m', h', hr, hd', hm', hp, hs'⟩ :=
        loop_sep_spec body again invariant variant post hF (step hF) initial m hP hd hm hi hs
      exact ⟨(e, s'), m', h', hr, hd', hm', hp, hs'⟩)

end MemProgram

end Zig.VC
