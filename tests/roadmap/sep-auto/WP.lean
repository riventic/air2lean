import ZigLean.Sep.Full.AutoWP

/-!
# `fsym` on a thread's run in a protocol (`Proto.WP`, the `WP` backend)

A run of thread `t` of any protocol `P`, from a context where `t` owns its part (`FOwned`):
`MemM` segments walked by the thread backend with their posts inferred (each segment's
precondition is the context's assertion about the part, the next one's is the previous post),
the final post from the segments' facts.
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Full Zig.Full.FAssn

namespace SepAuto.WP

attribute [local irreducible] Proto.WP

/-- **Two segments**: a store, then a load of the word the thread owns; the load reads the
store's value (the first segment's inferred post is the second's precondition). -/
theorem two_segments {Tgt γ : Type} (P : Proto Tgt γ) (hpart : P.Partial) (t : ThreadId)
    (G : ThreadId → γ) (m : Mem) (n : Nat) (own : ThreadId → Res) (rO : Res) (q : Ptr)
    (v : BitVec 32) (ho : FOwned own rO m) (hc : m.current = t) (htl : t < m.threads.size)
    (hp : up (pts q 4 v) (own t)) :
    P.WP t (ConcM.liftMem (store (α := BitVec 32) 4 q 7) >>= fun _ =>
        ConcM.liftMem (load (BitVec 32) 4 q))
      (fun w _ _ _ => w = 7) G m n := by
  fsym

/-- **Steps of a concurrent body** (`callMC`, `callRC`: one rule form, `ConcM.liftMem`): a field
pointer whose run the caller's lemma gives (`WP.liftMem_pure`), then a pure step
(`WP.liftMem_liftR`). -/
theorem body_steps {Tgt γ : Type} (P : Proto Tgt γ) (t : ThreadId)
    (G : ThreadId → γ) (m : Mem) (n : Nat) (p : Ptr)
    (hproj : (ptrProject p (·.add 8)).run m = pure (p.add 8, m)) :
    P.WP t (((do
        let q ← callMC (ptrProject p (·.add 8))
        let k ← callRC (Zig.add false (1 : BitVec 32) 2)
        pure (q, k)) : CM Tgt Unit (Ptr × BitVec 32)).run ())
      (fun r _ m' _ => r.1.1 = p.add 8 ∧ m' = m) G m n := by
  fsym [WP.liftMem_pure hproj rfl]

end SepAuto.WP
