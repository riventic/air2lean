import ZigLean.Sep.Full.AutoAll

/-!
# Thread-local lifetime knowledge in protocol walks

`freeBlocks` and `tlsExit` retain dead-block knowledge in the thread's full-state part. A
partial protocol can use it to show a read cannot return. The rule must leave ordinary live
loads available when an unrelated dead block is framed, and must reject strict protocols.
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Full Zig.Full.FAssn

namespace SepAuto.WPTls

attribute [local irreducible] Proto.WP

/-- A partial protocol's read through its own dead-block knowledge cannot return. -/
theorem dead_read {Tgt γ T : Type} [Enc T] (P : Proto Tgt γ) (hs : P.strict = false)
    (t : ThreadId) (G : ThreadId → γ) (m : Mem) (n : Nat) (own : ThreadId → Res) (rO : Res)
    (p : Ptr) (b a : Nat) (R : FAssn) (ho : FOwned own rO m)
    (htl : t < m.threads.size) (hp : (dead b ⋆ R) (own t)) (hpb : p.block = some b) :
    P.WP t (ConcM.liftMem (load T a p)) (fun _ _ _ _ => False) G m n := by
  fsym

/-- Unrelated dead knowledge must not select the negative rule for a valid live load. -/
theorem live_with_dead {Tgt γ : Type} (P : Proto Tgt γ) (hs : P.strict = false)
    (t : ThreadId) (G : ThreadId → γ) (m : Mem) (n : Nat) (own : ThreadId → Res) (rO : Res)
    (p : Ptr) (b c : BlockId) (v : BitVec 32) (hpb : p.block = some b) (hbc : b ≠ c)
    (ho : FOwned own rO m) (hc : m.current = t) (htl : t < m.threads.size)
    (hp : (dead c ⋆ up (pts p 4 v)) (own t)) :
    P.WP t (ConcM.liftMem (load (BitVec 32) 4 p)) (fun w _ _ _ => w = v) G m n := by
  fsym

/-- The negative read is justified by freeing full owned instance extents, not a raw-memory
deadness premise. The same resource continues through the free and the read. -/
theorem free_then_read {Tgt γ T : Type} [Enc T] (P : Proto Tgt γ) (hs : P.strict = false)
    (t : ThreadId) (G : ThreadId → γ) (m : Mem) (n : Nat) (own : ThreadId → Res) (rO : Res)
    (b a : Nat) (R : FAssn) (ho : FOwned own rO m) (hc : m.current = t)
    (htl : t < m.threads.size) (hp : (tlsDying [b] ⋆ R) (own t)) :
    P.WP t (ConcM.liftMem (freeBlocks [b]) >>= fun _ =>
        ConcM.liftMem (load T a ⟨some b, 0⟩))
      (fun _ _ _ _ => False) G m n := by
  fsym [FTTriple.freeBlocks_dead [b], tlsDead]

/-- A thread exit frees the instances in its own record and transfers their deadness to the
next step, which cannot read the ended instance. -/
theorem exit_then_read {Tgt γ T : Type} [Enc T] (P : Proto Tgt γ) (hs : P.strict = false)
    (t : ThreadId) (G : ThreadId → γ) (m : Mem) (n : Nat) (own : ThreadId → Res) (rO : Res)
    (b a : Nat) (R : FAssn) (ho : FOwned own rO m) (hc : m.current = t)
    (htl : t < m.threads.size) (hids : (m.tlsOf t).toList.map (·.2) = [b])
    (hp : (tlsDying [b] ⋆ R) (own t)) :
    P.WP t (ConcM.liftMem tlsExit >>= fun _ => ConcM.liftMem (load T a ⟨some b, 0⟩))
      (fun _ _ _ _ => False) G m n := by
  fsym [hids, tlsDead]

set_option linter.unusedVariables false in
/-- The no-return rule cannot establish safety for a strict protocol. -/
example {Tgt γ T : Type} [Enc T] (P : Proto Tgt γ) (hs : P.strict = true)
    (t : ThreadId) (G : ThreadId → γ) (m : Mem) (n : Nat) (own : ThreadId → Res) (rO : Res)
    (p : Ptr) (b a : Nat) (R : FAssn) (ho : FOwned own rO m)
    (htl : t < m.threads.size) (hp : (dead b ⋆ R) (own t)) (hpb : p.block = some b) : True := by
  fail_if_success
    have : P.WP t (ConcM.liftMem (load T a p)) (fun _ _ _ _ => False) G m n := by
      fsym
  trivial

end SepAuto.WPTls
