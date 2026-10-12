import ZigLean.VC.Mem
import ZigLean.Sep.Total

/-!
# Result-existence obligations for memory programs (P05)

`MemProgram.sound` gives the partial `Triple`, because a modular memory call may be partial. The
generated VC already holds every obligation a loop-free memory program needs to return: the
ownership and positive size of each access, the arithmetic safety of each lifted operation, and
each callee's precondition. What it cannot supply is the callee's own return. So:

* `MemProgram.AllTotal p`: every memory call of `p` (in both arms of every branch) has a
  `TotalTriple` contract. Everything else in the AST returns when its VC holds.
* `MemProgram.sound_total`: under `AllTotal`, the same VC gives the `TotalTriple`: the run returns
  (`pure`), with the postcondition and the frame. No new obligation is added and none is dropped.
* `total_intro` / `returns_intro`: the entry rules of `vc_gen` for `TotalTriple pre (f xs) post`
  and `Returns pre (f xs)` goals. A `Returns` goal asks the VC with the postcondition `True`: the
  result-existence obligations alone (safety, memory, callee preconditions), with no functional
  obligation.

`vc_gen` discharges `AllTotal` by unfolding the extracted program. A memory call that only has
a partial (`Triple`) contract leaves `AllTotal` unproved, and the goal is refused: a partial
contract never yields a total claim.
-/

namespace Zig.VC

open Assn

namespace MemProgram

/-- Every memory call has a total contract (both arms of every branch). -/
def AllTotal : {α : Type} → MemProgram α → Prop
  | _, .call _ action pre post _ => TotalTriple pre action post
  | _, .bind first next => AllTotal first ∧ ∀ value, AllTotal (next value)
  | _, .branch _ yes no => AllTotal yes ∧ AllTotal no
  | _, _ => True

/-- With total callees, the generated VC gives total correctness. -/
theorem sound_total {α : Type} (program : MemProgram α) (hall : AllTotal program) :
    ∀ post, TotalTriple (vc program post) (eval program) post := by
  induction program with
  | ret value =>
    intro post
    exact TotalTriple.ret (Q := post) value
  | read pointer alignment old =>
    intro post m hP hF hd hm hp hs
    obtain ⟨m', hr, hm', hs'⟩ := pts_load_run hp.2.1 hm hp.1 hs
    exact ⟨old, m', hP, hr, hd, hm', hp.2.2, hs'⟩
  | write pointer alignment old value =>
    intro post m hP hF hd hm hp hs
    obtain ⟨m', hr, hs', h', hd', hm', hp'⟩ := pts_store_run hp.2.1 hm hd hp.1 hs value
    exact ⟨(), m', h', hr, hd', hm', hp.2.2 h' hp', hs'⟩
  | load pointer alignment =>
    intro post m hP hF hd hm hp hs
    obtain ⟨old, hpts, hpost⟩ := hp.2
    obtain ⟨m', hr, hm', hs'⟩ := pts_load_run hpts hm hp.1 hs
    exact ⟨old, m', hP, hr, hd, hm', hpost, hs'⟩
  | store pointer alignment value =>
    intro post m hP hF hd hm hp hs
    obtain ⟨old, hpts⟩ := hp.2.1
    obtain ⟨m', hr, hs', h', hd', hm', hp'⟩ := pts_store_run hpts hm hd hp.1 hs value
    exact ⟨(), m', h', hr, hd', hm', hp.2.2 h' hp', hs'⟩
  | lift program =>
    intro post m hP hF hd hm hp hs
    obtain ⟨value, hr, hpost⟩ := program.sound _ hp
    refine ⟨value, m, hP, ?_, hd, hm, hpost, hs⟩
    simp only [eval, StateT.run, StateT.lift, hr, pure_bind]
  | call label action pre summary checked =>
    intro post m hP hF hd hm hp hs
    obtain ⟨v, m', hQ, hr, hd', hm', hq, hs'⟩ := (hall : TotalTriple pre action summary) m hP hF hd hm hp.1 hs
    exact ⟨v, m', hQ, hr, hd', hm', hp.2 _ _ hq, hs'⟩
  | bind first next ihFirst ihNext =>
    intro post
    exact TotalTriple.bind (ihFirst hall.1 _) (fun value => ihNext value (hall.2 value) post)
  | branch condition yes no ihYes ihNo =>
    intro post
    cases condition with
    | false => exact ihNo hall.2 post
    | true => exact ihYes hall.1 post

end MemProgram

/-- The entry rule of `vc_gen` for a total memory contract. -/
theorem total_intro {α : Type} {program : MemProgram α} {action : MemM α} {pre : Assn}
    {post : α → Assn} (source : program.eval = action) (hall : MemProgram.AllTotal program)
    (generated : MemProgram.obligation pre program post) : TotalTriple pre action post :=
  source ▸ (MemProgram.sound_total program hall post).conseq generated (fun _ _ hp => hp)

/-- The entry rule of `vc_gen` for result existence: the VC with the postcondition `True`. -/
theorem returns_intro {α : Type} {program : MemProgram α} {action : MemM α} {pre : Assn}
    (source : program.eval = action) (hall : MemProgram.AllTotal program)
    (generated : MemProgram.obligation pre program (fun _ _ => True)) : Returns pre action :=
  (total_intro source hall generated).returns

end Zig.VC
