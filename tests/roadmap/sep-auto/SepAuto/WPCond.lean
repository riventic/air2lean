import ZigLean.Sep.Full.AutoWP
import ZigLean.Sep.Full.Cond

/-!
# `fsym` calls a condition implementation outside or holding the mutex

The same condition contract applies in either phase. The post retains the exact initial
ghost value and arbitrary assertions about both complete resource components, including
knowledge and ghosts. The regression supplies only the contract of the implementation.
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Full

namespace SepAuto.WPCond

attribute [local irreducible] Proto.WP

/-- Both allowed signal phases keep the complete caller part and holder resource. -/
theorem signal_preserves {Tgt γ : Type} (ci : CondImpl Tgt)
    {L : FLock γ} {C : FCond γ} {P : Proto Tgt γ}
    {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}
    (hC : L.Fits (C.prim L) P U ok) (hcost : P.cost = none)
    (t : ThreadId) (g : γ) (hgx : C.ph g = .out)
    (hgo : L.ph g = .out ∨ L.ph g = .holds) (hsx : C.sx g)
    (A B : FAssn) (ha : A (L.part g)) (hb : B (L.held g))
    (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hseen : ∀ G₁ rX m₁, G₁ t = g → U G₁ rX m₁ → ∀ u i jr sn e,
      C.ph (G₁ u) = .reg i jr sn e →
      VClock.le (C.S.hist m₁)[jr]!.clock (m₁.clocks[t]!) = true)
    (hi : P.inv (upd G t g) m) :
    P.WP t (ci.signal C.S.ptr io) (fun _ G' m' d' =>
      d' < d ∧ m'.current = t ∧ P.inv (upd G' t g) m' ∧
      A (L.part g) ∧ B (L.held g) ∧
      ∀ u i jr sn e, C.ph (G' u) = .reg i jr sn e → C.Signalled m') G m d := by
  fsym [ci.signal_wp hC hcost]

end SepAuto.WPCond
