import ZigLean.Sep.Full.AutoWP
import ZigLean.Sep.Full.LockSteps

/-!
# `fsym` applies a lock holder's step itself (`FLock.Fits.wp_hold`, ledger #70)

A toy lock (`FLock.prod`) whose resource is two words: `p` holds thread 0's place, `p + 4` a
constant. For every protocol that has the lock (`FLock.Fits`), the holder's loads and stores are
walked by `fsym`'s `WP` backend with `hF.wp_hold (g' := …)` as the caller's rule, the holder's new
place (the ghost transition `g'`) as its argument:

- the segment's precondition is the lock's resource (`hpa` fixes it), its post is inferred, and
  `hR` (the resource at the new place, an assertion at the holder's resource) is proved after the
  segment from the post's atoms (rewritten by provable equations of their values, reordered);
- `hU` (the protocol's `U` at the new place) is the protocol's lemma (`hUs`), applied backwards to
  the side goal (its premises side goals again);
- a rule for every `MemM` step applies only completely, after the other rules: of the two places
  given, the one whose `hR` holds is taken (`hold_incr`);
- a caller's lemma with an arithmetic conclusion gives a fact of a hypothesis (`hb`, the bound of
  a place from the protocol's shape `Sh`): the checked `+ 1` of the loaded value does not
  overflow (`hold_add`).
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Full Zig.Full.FAssn Zig.Full.FLock

namespace SepAuto.WPHold

attribute [local irreducible] Proto.WP

/-- The words. -/
def p : Ptr := ⟨some 0, 0⟩

/-- The lock's resource: thread 0's place, and a constant. -/
def R (X : ThreadId → Nat) : FAssn :=
  up (pts p 4 (BitVec.ofNat 32 (X 0))) ⋆ up (pts (p.add 4) 4 (7 : BitVec 32))

abbrev L : FLock (FLG × Nat) := FLock.prod 0 8 R

/-- A holder at place `x` with the resource `rL`. -/
def gH (x : Nat) (rL : Res) : FLG × Nat := (⟨.holds, rnil, rL⟩, x)

variable {Tgt : Type} {K : FPrim (FLG × Nat)} {P : Proto Tgt (FLG × Nat)}
  {U : (ThreadId → FLG × Nat) → Res → Mem → Prop} {ok : FLG × Nat → Prop}

/-- **A holder's load**: its value, the place kept. -/
theorem hold_load (hF : L.Fits K P U ok) (hpart : P.Partial)
    (hUs : ∀ (G : ThreadId → FLG × Nat) t x x' rL r rX (m m' : Mem), U (upd G t (gH x rL)) rX m →
      m'.threads = m.threads → U (upd (upd G t (gH x rL)) t (gH x' r)) rX m')
    (t : ThreadId) (x : Nat) (rL : Res) (G : ThreadId → FLG × Nat) (m : Mem) (d : Nat)
    (hi : P.inv (upd G t (gH x rL)) m) (hc : m.current = t) :
    P.WP t (ConcM.liftMem (load (BitVec 32) 4 p)) (fun v _ m' _ => m'.current = t ∧
      v = BitVec.ofNat 32 (upd (fun u => (G u).2) t x 0) ∧
      ∃ rQ, P.inv (upd G t (gH x rQ)) m') G m d := by
  fsym [hF.wp_hold (g' := gH x), hUs]

/-- **Loads, then a store to the next place**: the loads keep thread 0's place, the store moves it
to `x + 1` (the other place's `hR` fails: the rule is not taken). -/
theorem hold_incr (hF : L.Fits K P U ok) (hpart : P.Partial)
    (hUs : ∀ (G : ThreadId → FLG × Nat) t x x' rL r rX (m m' : Mem), U (upd G t (gH x rL)) rX m →
      m'.threads = m.threads → U (upd (upd G t (gH x rL)) t (gH x' r)) rX m')
    (x : Nat) (rL : Res) (G : ThreadId → FLG × Nat) (m : Mem) (d : Nat)
    (hi : P.inv (upd G 0 (gH x rL)) m) (hc : m.current = 0) :
    P.WP 0 (ConcM.liftMem (load (BitVec 32) 4 p) >>= fun a =>
        ConcM.liftMem (load (BitVec 32) 4 (p.add 4)) >>= fun b =>
        ConcM.liftMem (store 4 p (a + 1)) >>= fun _ => pure b)
      (fun b _ m' _ => b = 7 ∧ m'.current = 0 ∧ ∃ rQ, P.inv (upd G 0 (gH (x + 1) rQ)) m') G m d := by
  fsym [hF.wp_hold (g' := gH x), hF.wp_hold (g' := gH (x + 1)), hUs]

/-- **A checked increment by the holder**, whose bound is a fact of the protocol's shape `Sh`
(the forward lemma `hb`). -/
theorem hold_add (hF : L.Fits K P U ok) (hpart : P.Partial) (Sh : (ThreadId → Nat) → Prop)
    (hb : ∀ X, Sh X → X 0 ≤ 4)
    (hUs : ∀ (G : ThreadId → FLG × Nat) t x x' rL r rX (m m' : Mem), U (upd G t (gH x rL)) rX m →
      m'.threads = m.threads → U (upd (upd G t (gH x rL)) t (gH x' r)) rX m')
    (x : Nat) (rL : Res) (G : ThreadId → FLG × Nat) (m : Mem) (d : Nat)
    (hsh : Sh (upd (fun u => (G u).2) 0 x))
    (hi : P.inv (upd G 0 (gH x rL)) m) (hc : m.current = 0) :
    P.WP 0 (ConcM.liftMem (load (BitVec 32) 4 p) >>= fun a =>
        ConcM.liftMem (StateT.lift (Zig.add false a 1)) >>= fun b =>
        ConcM.liftMem (store 4 p b))
      (fun _ _ m' _ => m'.current = 0 ∧ ∃ rQ, P.inv (upd G 0 (gH (x + 1) rQ)) m') G m d := by
  fsym [hF.wp_hold (g' := gH x), hF.wp_hold (g' := gH (x + 1)), hUs, hb]

end SepAuto.WPHold

namespace SepAuto.WPHold

/-- A one-place resource pool, independently of any mutex implementation or protocol. -/
def poolR (A : FAssn) (X : ThreadId → Bool) : FAssn := if X 0 then A else emp

abbrev poolL (A : FAssn) : FLock (FLG × Bool) := FLock.prod 0 8 (poolR A)

def gPool (b : Bool) (rp rh : Res) : FLG × Bool := (⟨.holds, rp, rh⟩, b)

/-- Returning an arbitrary complete resource to the pool preserves the invariant. -/
theorem return_payload (A : FAssn) (G : ThreadId → FLG × Bool) (rX r : Res) (m : Mem)
    (hi : (poolL A).Inv (upd G 0 (gPool false r rnil)) rX m) (ha : A r) :
    (poolL A).Inv (upd (upd G 0 (gPool false r rnil)) 0 (gPool true rnil r)) rX m := by
  refine hi.repartition rfl ?_ ?_ (fun hn => (hn rfl).elim) (fun hn => (hn rfl).elim) ?_
  · exact (rnil_rsum r).trans (rsum_rnil r).symm
  · exact (FHeap.disjoint_empty r.heap).symm
  · intro _
    simpa [poolL, FLock.prod, poolR, gPool, upd] using ha

/-- Taking the resource reverses the split without changing any byte, knowledge or ghost. -/
theorem take_payload (A : FAssn) (G : ThreadId → FLG × Bool) (rX r : Res) (m : Mem)
    (hi : (poolL A).Inv (upd G 0 (gPool true rnil r)) rX m) :
    A r ∧ (poolL A).Inv (upd (upd G 0 (gPool true rnil r)) 0 (gPool false r rnil)) rX m := by
  constructor
  · simpa [poolL, FLock.prod, poolR, gPool, upd] using hi.res 0 rfl
  · refine hi.repartition rfl ?_ ?_ (fun hn => (hn rfl).elim) (fun hn => (hn rfl).elim) ?_
    · exact (rsum_rnil r).trans (rnil_rsum r).symm
    · exact FHeap.disjoint_empty r.heap
    · intro _
      exact ⟨rfl, rfl, rfl⟩

/-- A store can supply the protected counter's post while framing an arbitrary full resource.
`fsym` performs the primitive walk and the complete resource's new split. -/
theorem return_store (A : FAssn) (p : Ptr) :
    FTTriple (A ⋆ up (pts p 4 (0 : BitVec 32))) (store 4 p (1 : BitVec 32))
      (fun _ => emp ⋆ (up (pts p 4 (1 : BitVec 32)) ⋆ A)) := by
  fsym

theorem take_store (A : FAssn) (p : Ptr) :
    FTTriple (up (pts p 4 (1 : BitVec 32)) ⋆ A) (store 4 p (0 : BitVec 32))
      (fun _ => A ⋆ up (pts p 4 (0 : BitVec 32))) := by
  fsym

/-- The framed resource cannot be duplicated while changing its ownership split. -/
theorem reject_duplicate_payload (A : FAssn) (p : Ptr) : True := by
  fail_if_success
    have : FTTriple (A ⋆ up (pts p 4 (0 : BitVec 32))) (store 4 p (1 : BitVec 32))
        (fun _ => A ⋆ (up (pts p 4 (1 : BitVec 32)) ⋆ A)) := by fsym
  trivial

/-- Nor can it disappear during a transfer. -/
theorem reject_dropped_payload (A : FAssn) (p : Ptr) : True := by
  fail_if_success
    have : FTTriple (A ⋆ up (pts p 4 (0 : BitVec 32))) (store 4 p (1 : BitVec 32))
        (fun _ => up (pts p 4 (1 : BitVec 32))) := by fsym
  trivial

/-- Equal empty heaps do not permit dropping a resource's nonempty knowledge. This control
uses the invariant rule itself, independently of the primitive store controls. -/
theorem reject_dropped_knowledge (G : ThreadId → FLG × Bool) (rX r : Res) (m : Mem)
    (hh : r.heap = FHeap.empty) (hk : r.know ≠ Know.none) (hg : r.gh = Ghost.unit)
    (hi : (poolL emp).Inv (upd G 0 (gPool false r rnil)) rX m) : True := by
  fail_if_success
    have : (poolL emp).Inv (upd (upd G 0 (gPool false r rnil)) 0 (gPool true rnil rnil)) rX m := by
      refine hi.repartition rfl ?_ (FHeap.disjoint_empty _) (fun hn => (hn rfl).elim)
        (fun hn => (hn rfl).elim) (fun _ => ⟨rfl, rfl, rfl⟩)
      simp [rsum, hh, hg, Ne.symm hk]
  trivial

/-- Equal empty heaps and knowledge do not permit dropping ghost resources either. -/
theorem reject_dropped_ghost (G : ThreadId → FLG × Bool) (rX r : Res) (m : Mem)
    (hh : r.heap = FHeap.empty) (hk : r.know = Know.none) (hg : r.gh ≠ Ghost.unit)
    (hi : (poolL emp).Inv (upd G 0 (gPool false r rnil)) rX m) : True := by
  fail_if_success
    have : (poolL emp).Inv (upd (upd G 0 (gPool false r rnil)) 0 (gPool true rnil rnil)) rX m := by
      refine hi.repartition rfl ?_ (FHeap.disjoint_empty _) (fun hn => (hn rfl).elim)
        (fun hn => (hn rfl).elim) (fun _ => ⟨rfl, rfl, rfl⟩)
      simp [rsum, hh, hk, Ne.symm hg]
  trivial

end SepAuto.WPHold
