import ZigLean.Sep.Full.AutoWP
import ZigLean.Sep.Full.LockSteps

open Zig Zig.Conc Zig.Conc.Proto Zig.Full Zig.Full.FAssn Zig.Full.FLock

namespace SepAuto.WPHold

attribute [local irreducible] Proto.WP

def p : Ptr := ⟨some 0, 0⟩

def R (X : ThreadId → Nat) : FAssn :=
  up (pts p 4 (BitVec.ofNat 32 (X 0))) ⋆ up (pts (p.add 4) 4 (7 : BitVec 32))

abbrev L : FLock (FLG × Nat) := FLock.prod 0 8 R

def gH (x : Nat) (rL : Res) : FLG × Nat := (⟨.holds, rnil, rL⟩, x)

variable {Tgt : Type} {K : FPrim (FLG × Nat)} {P : Proto Tgt (FLG × Nat)}
  {U : (ThreadId → FLG × Nat) → Res → Mem → Prop} {ok : FLG × Nat → Prop}

theorem hold_load (hF : L.Fits K P U ok) (hpart : P.Partial)
    (hUs : ∀ (G : ThreadId → FLG × Nat) t x x' rL r rX (m m' : Mem), U (upd G t (gH x rL)) rX m →
      m'.threads = m.threads → U (upd (upd G t (gH x rL)) t (gH x' r)) rX m')
    (t : ThreadId) (x : Nat) (rL : Res) (G : ThreadId → FLG × Nat) (m : Mem) (d : Nat)
    (hi : P.inv (upd G t (gH x rL)) m) (hc : m.current = t) :
    P.WP t (ConcM.liftMem (load (BitVec 32) 4 p)) (fun v _ m' _ => m'.current = t ∧
      v = BitVec.ofNat 32 (upd (fun u => (G u).2) t x 0) ∧
      ∃ rQ, P.inv (upd G t (gH x rQ)) m') G m d := by
  set_option trace.fsym true in
  fsym [hF.wp_hold (g' := gH x), hUs]

theorem hold_incr (hF : L.Fits K P U ok) (hpart : P.Partial)
    (hUs : ∀ (G : ThreadId → FLG × Nat) t x x' rL r rX (m m' : Mem), U (upd G t (gH x rL)) rX m →
      m'.threads = m.threads → U (upd (upd G t (gH x rL)) t (gH x' r)) rX m')
    (x : Nat) (rL : Res) (G : ThreadId → FLG × Nat) (m : Mem) (d : Nat)
    (hi : P.inv (upd G 0 (gH x rL)) m) (hc : m.current = 0) :
    P.WP 0 (ConcM.liftMem (load (BitVec 32) 4 p) >>= fun a =>
        ConcM.liftMem (load (BitVec 32) 4 (p.add 4)) >>= fun b =>
        ConcM.liftMem (store 4 p (a + 1)) >>= fun _ => pure b)
      (fun b _ m' _ => b = 7 ∧ m'.current = 0 ∧ ∃ rQ, P.inv (upd G 0 (gH (x + 1) rQ)) m') G m d := by
  set_option trace.fsym true in
  fsym [hF.wp_hold (g' := gH x), hF.wp_hold (g' := gH (x + 1)), hUs]

end SepAuto.WPHold
