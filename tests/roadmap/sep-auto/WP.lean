import ZigLean.Sep.Full.AutoWP
import ZigLean.Sep.Full.ThreadCall
import ZigLean.Sep.Full.Local

/-!
# `fsym` on a thread's run in a protocol (`Proto.WP`, the `WP` backend)

A run of thread `t` of any protocol `P`, from a context where `t` owns its part (`FOwned`):
`MemM` segments walked by the thread backend with their posts inferred (each segment's
precondition is the context's assertion about the part, the next one's is the previous post),
the final post from the segments' facts. A call of a concurrent function known only by its
contract (`CTriple`) is the caller's rule `WP.call_fowned` (`Full/ThreadCall.lean`).
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

/-- **Checked arithmetic on a symbolic word** (`WP.liftMem_add`, `WP.liftMem_sub`): the bound
from the context, the value as a fact (no overflow branch, also in strict mode). -/
theorem checked_steps {Tgt γ : Type} (P : Proto Tgt γ) (t : ThreadId)
    (G : ThreadId → γ) (m : Mem) (n : Nat) (a : BitVec 32) (ha : a.toNat < 10) :
    P.WP t (ConcM.liftMem (StateT.lift (Zig.add false a 1)) >>= fun b =>
        ConcM.liftMem (StateT.lift (Zig.sub false b 1)))
      (fun r _ _ _ => r.toNat = a.toNat) G m n := by
  fsym

/-- **Branches of a run** (`if` between segments): each branch's segments, the post a disjunction
proved by one of its sides. -/
theorem branch_runs {Tgt γ : Type} (P : Proto Tgt γ) (hpart : P.Partial) (t : ThreadId)
    (G : ThreadId → γ) (m : Mem) (n : Nat) (own : ThreadId → Res) (rO : Res) (q : Ptr)
    (v : BitVec 32) (b : Bool) (ho : FOwned own rO m) (hc : m.current = t)
    (htl : t < m.threads.size) (hp : up (pts q 4 v) (own t)) :
    P.WP t (ConcM.liftMem (if b then store (α := BitVec 32) 4 q 7 else pure ()) >>= fun _ =>
        ConcM.liftMem (load (BitVec 32) 4 q))
      (fun w _ _ _ => w = 7 ∨ w = v) G m n := by
  fsym

/-- A function of the thread whose branches end in different states. -/
def setIfZero (q : Ptr) : MemM Unit := do
  let w ← load (BitVec 32) 4 q
  if w = 0 then store (α := BitVec 32) 4 q 7 else pure ()

/-- **A segment whose branches end in different states** (`joinPosts`): its post is the join of
the branches' (`∃ b, if b then … else …`); the next segment starts from each. -/
theorem branch_states {Tgt γ : Type} (P : Proto Tgt γ) (hpart : P.Partial) (t : ThreadId)
    (G : ThreadId → γ) (m : Mem) (n : Nat) (own : ThreadId → Res) (rO : Res) (q : Ptr)
    (v : BitVec 32) (ho : FOwned own rO m) (hc : m.current = t) (htl : t < m.threads.size)
    (hp : up (pts q 4 v) (own t)) :
    P.WP t (ConcM.liftMem (setIfZero q) >>= fun _ => ConcM.liftMem (load (BitVec 32) 4 q))
      (fun w _ _ _ => w = 7 ∨ w ≠ 0) G m n := by
  fsym

/-- **A call of a concurrent function by its contract** (`WP.call_fowned`): a function `f` known
only by a `CTriple` on the thread's part, called by thread `t` of every protocol whose invariant
keeps the parts (`hinv`) and is local to them (`hloc`) and that counts no turns. The contract is
the caller's rule; the call's precondition is the context's assertion about the part. -/
theorem call_contract {Tgt γ : Type} (P : Proto Tgt γ) (t : ThreadId)
    (res : γ → Res) (set : γ → Res → γ) (hres : ∀ g r, res (set g r) = r) (hcost : P.cost = none)
    (hinv : ∀ G m, P.inv G m → t < m.threads.size ∧ ∃ rO, FOwned (fun u => res (G u)) rO m)
    (hloc : ∀ G m m' rO rR r', P.inv G m →
      sepN m.threads.size (partsBut (fun u => res (G u)) t) rR →
      FOwned (upd (fun u => res (G u)) t r') rO m' →
      FStepIn (FHeap.erase (rR.heap ∪ rO.heap)) { m with current := t } m' →
      P.inv (upd G t (set (G t) r')) m')
    (q : Ptr) (f : ConcM Tgt Unit)
    (hf : CTriple (up (pts q 4 (0 : BitVec 32))) f (fun _ => up (pts q 4 (1 : BitVec 32))))
    (G : ThreadId → γ) (m : Mem) (n : Nat) (hi : P.inv G m) (hc : m.current = t)
    (hp : up (pts q 4 (0 : BitVec 32)) (res (G t))) :
    P.WP t f (fun _ _ m' _ => m'.current = t) G m n := by
  fsym [WP.call_fowned (Q := fun _ _ m' _ => m'.current = t) hf hcost hres hinv hloc
    (fun _ _ _ _ _ _ _ _ _ _ _ hs _ => hs.current)]

/-- **A thread's own stack block and its fields** (`main` before its spawn): the allocation in the
plain mode (`FTriple.allocStackDrop`), then field pointers (`ptrProject`, the block's size from
its extent: `Reaches.bauth`) and stores at byte offsets of the block's bytes (`storeBytesAt`, the
offsets as generated code writes them; the closed sizes of the bytes written evaluated). Each
command is a segment of the thread's part (`WP.liftMem_fowned`), the next one's precondition the
previous one's inferred post. -/
theorem block_fields {Tgt γ : Type} (P : Proto Tgt γ) (hpart : P.Partial) (t : ThreadId)
    (G : ThreadId → γ) (m : Mem) (n : Nat) (own : ThreadId → Res) (rO : Res)
    (ho : FOwned own rO m) (hc : m.current = t) (htl : t < m.threads.size) (hp : plain (own t)) :
    P.WP t (ConcM.liftMem (allocStack 16 8) >>= fun p =>
        ConcM.liftMem (store 8 p (⟨⟩ : Io)) >>= fun _ =>
        ConcM.liftMem (ptrProject p (·.add 8)) >>= fun q =>
        ConcM.liftMem (store (α := BitVec 32) 4 q 5) >>= fun _ =>
        ConcM.liftMem (ptrProject p (·.add 12)) >>= fun q' =>
        ConcM.liftMem (store (α := BitVec 32) 4 q' 6))
      (fun _ _ m' _ => m'.current = t) G m n := by
  fsym [FTriple.allocStackDrop]

end SepAuto.WP
