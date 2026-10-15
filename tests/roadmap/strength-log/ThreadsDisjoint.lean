import Proofs.Threads.Disjoint

/-!
Strength log for retiring `Disjoint.lean`'s direct legacy witness import. The all-schedules
statements are unchanged, including the spawn-policy and stack-overflow premises. The thread
triple's existing non-vacuity and liveness companions still use `FTTAdmit` and `FTTLive`.
-/

open Zig Zig.Conc Threads Threads.Disjoint

namespace StrengthLog.ThreadsDisjoint

example (a b : BitVec 32) (env : Env) (henv : env.spawn = .available) {σ : Placement}
    {fuel : Nat} {o : Nat → Nat} {v : Except ErrName (BitVec 32)} {m : Mem}
    (h : (Sched.run env dispatch fuel o (disjoint a b) (mem0 σ)).run = some (.ok (v, m))) :
    v = .ok (a + b) :=
  disjoint_spec env henv h

example (a b : BitVec 32) (env : Env) (henv : env.spawn = .available) {σ : Placement}
    {fuel : Nat} {o : Nat → Nat} {e : Error} :
    e ≠ .stackOverflow → (Sched.run env dispatch fuel o (disjoint a b) (mem0 σ)).run ≠ some (.error e) :=
  disjoint_safe env henv

example : ∃ σ, Zig.Witness.okVal
    (Sched.run ⟨.any, .available⟩ dispatch 1000 (fun _ => 0) (disjoint 1 2) (mem0 σ)) = some 3 :=
  disjoint_completes

end StrengthLog.ThreadsDisjoint
