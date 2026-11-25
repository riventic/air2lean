import Proofs.Sync.Cases
import ZigLean.Sep.Full.Event
import ZigLean.Sep.Full.AutoWP
import ZigLean.Sep.Full.LockSteps

/-!
# The event contract for the Zig 0.17.1 Sync profile

`Io.Event`'s `waitUncancelable` and `set` in the actual Zig 0.17.1 Linux translation
(`Proofs/Sync/Gen/V0_17_1/H_6c696e7578/Gen.lean`), walked with the rules of the futex event
(`ZigLean/Sep/Full/Event.lean`) as `Proofs/Sync/Event.lean` walks the public translation's: the
per-item obligation of this case, for its client proofs (`Proofs/Sync/HandoffCases.lean`). The
0.16.0 Linux case is the public translation (`Sync.ioEvent`).
-/

open Zig Zig.Conc Zig.Full Zig.Conc.Proto

namespace Sync.CaseContracts.V0_17_1.H_6c696e7578

open Sync.Gen.V0_17_1.H_6c696e7578

theorem event_dec : ∀ b : BitVec 32, (b = 0 ∨ b = 1 ∨ b = 2) →
    ∃ r, (Packed.ofBits? (α := Io_Event) b).run = some (.ok r) := by
  rintro b (rfl | rfl | rfl) <;> exact ⟨_, rfl⟩

/-- Closed decoder equations remain available after the walk splits a returned enum value. -/
theorem event_decode0 :
    (Packed.ofBits? (α := Io_Event) 0#32).run = some (.ok .unset) := rfl

theorem event_decode1 :
    (Packed.ofBits? (α := Io_Event) 1#32).run = some (.ok .waiting) := rfl

theorem event_decode2 :
    (Packed.ofBits? (α := Io_Event) 2#32).run = some (.ok .is_set) := rfl

attribute [local fsym_arith] event_decode0 event_decode1 event_decode2

theorem event_of0 {r : Io_Event} (h : (Packed.ofBits? (α := Io_Event) 0).run = some (.ok r)) :
    r = .unset := by
  simp only [BitVec.ofNat_eq_ofNat] at h
  rw [event_decode0] at h; cases h; rfl

theorem event_of1 {r : Io_Event} (h : (Packed.ofBits? (α := Io_Event) 1).run = some (.ok r)) :
    r = .waiting := by
  simp only [BitVec.ofNat_eq_ofNat] at h
  rw [event_decode1] at h; cases h; rfl

theorem event_of2 {r : Io_Event} (h : (Packed.ofBits? (α := Io_Event) 2).run = some (.ok r)) :
    r = .is_set := by
  simp only [BitVec.ofNat_eq_ofNat] at h
  rw [event_decode2] at h; cases h; rfl

section
variable {γ : Type} {L : FLock γ} {E : FEvent γ} {P : Proto Tgt γ}
  {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}

attribute [local irreducible] Proto.WP

/-- `Io.Event.set` (as `Sync.ioEvent_set_wp`). -/
theorem event_set_wp (hE : L.Fits (E.prim L) P U ok) (hcost : P.cost = none)
    {p : Ptr} (hp : p = E.W.ptr) (t : ThreadId) (g : γ) (hgx : E.ph g = .out)
    (hgo : L.ph g = .out ∨ L.ph g = .gone) (hsx : E.sx g) (io : Io) (G : ThreadId → γ) (m : Mem)
    (d : Nat) (hi : P.inv (upd G t g) m) :
    P.WP t (Io_Event_set p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧ E.IsSet m' ∧
      P.inv (upd G' t (E.set g .sd)) m') G m d := by
  subst hp
  fsym [FEvent.wp_xchgAs (g := g) hE (v := Io_Event.is_set) rfl event_dec,
    FEvent.wp_wake (g := E.set g .sw) hE,
    hE.lph, E.ph_set, E.set_set, event_of0, event_of1, event_of2]

/-- The set's resource contract (as `Sync.ioEvent_set_wp_resource`). -/
theorem event_set_wp_resource (hE : L.Fits (E.prim L) P U ok) (hcost : P.cost = none)
    {p : Ptr} (hp : p = E.W.ptr) (t : ThreadId) (g : γ) (hgx : E.ph g = .out)
    (hgo : L.ph g = .out ∨ L.ph g = .gone) (hsx : E.sx g)
    (_ : E.GoneUnjoined L P t g) (io : Io) (G : ThreadId → γ) (m : Mem)
    (d : Nat) (_ : anyPart t (L.part g)) (hi : P.inv (upd G t g) m) :
    P.WP t (Io_Event_set p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧ E.IsSet m' ∧
      ∃ r', keepPart t (L.part g) r' ∧ P.inv (upd G' t (L.setPart (E.set g .sd) r')) m')
      G m d := by
  refine WP.mono ?_ (event_set_wp hE hcost hp t g hgx hgo hsx io G m d hi)
  rintro _ G' m' d' ⟨hd, hc, hs, hi'⟩
  exact ⟨hd, hc, hs, L.part g, rfl, by rw [FEvent.setPart_set_self hE]; exact hi'⟩

/-- `waitUncancelable`'s loop invariant: `t` is a waiter at `w1`. -/
def waitInv (P : Proto Tgt γ) (E : FEvent γ) (t : ThreadId) (g : γ) (D : Nat)
    (_ : Io_Event_waitUncancelableLocals) (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ m.current = t ∧ P.inv (upd G t (E.set g .w1)) m

/-- `waitUncancelable`'s loop ends when the event is set: `t` is out. -/
def waitPost (P : Proto Tgt γ) (E : FEvent γ) (t : ThreadId) (g : γ) (D : Nat)
    (r : Io_Event_waitUncancelableExit × Io_Event_waitUncancelableLocals) (G : ThreadId → γ)
    (m : Mem) (d : Nat) : Prop :=
  r.1 = .ret ∧ d < D ∧ m.current = t ∧ E.IsSet m ∧ E.Synced t m ∧ P.inv (upd G t g) m

/-- One repeat of `waitUncancelable`'s loop: the futex wait, then an acquire load. -/
theorem event_wait_body (hE : L.Fits (E.prim L) P U ok) (hcost : P.cost = none)
    (t : ThreadId) (g : γ) (hgx : E.ph g = .out) (hgo : L.ph g = .out)
    (hu : 0 < (L.part g).gh.ac.frag .unmetered) (D : Nat) (io : Io)
    (hlive : ∀ G₁ m₁, E.ph (G₁ t) = .w1 → L.ph (G₁ t) = .away → P.inv G₁ m₁ → ¬ E.IsSet m₁ →
      P.Live t G₁ m₁)
    (s : Io_Event_waitUncancelableLocals) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (h : waitInv P E t g D s G m d) :
    P.WP t ((Io_Event_waitUncancelable.loop17 E.W.ptr io).run s) (fun r G' m' d' =>
      if Io_Event_waitUncancelable.again17 r.1 then waitInv P E t g D r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : Io_Event_waitUncancelableLocals) => 0) s)
      else waitPost P E t g D r G' m' d') G m d := by
  fsym [hE.wp_tick_unmetered (g := E.set g .w1),
    FEvent.wp_wait (g := E.set g .w1) hE (ε := Io_Event) (e := .waiting) (by decide),
    FEvent.wp_loadAs (g := E.set g .w1) hE event_dec (.inr (E.ph_set g .w1)),
    hE.lpart, hE.lph, E.ph_set, E.set_set,
    FEvent.set_of hgx, event_of0, event_of1, event_of2,
    waitInv, waitPost, Io_Event_waitUncancelable.again17]

/-- `Io.Event.waitUncancelable` (as `Sync.ioEvent_wait_wp_unmetered`). -/
theorem event_wait_wp_unmetered (hE : L.Fits (E.prim L) P U ok) (hcost : P.cost = none)
    {p : Ptr} (hp : p = E.W.ptr) (t : ThreadId) (g : γ) (hgx : E.ph g = .out)
    (hgo : L.ph g = .out) (hwx : E.wx g) (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hone : ∀ u, u ≠ t → ¬ (E.ph (G u)).Waiting)
    (hhb : ∀ j < (E.W.hist m).size, (E.W.hist m)[j]!.Val (1 : BitVec 32) →
      VClock.le (E.W.hist m)[j]!.clock (m.clocks[t]!) = true)
    (hlive : ∀ G₁ m₁, E.ph (G₁ t) = .w1 → L.ph (G₁ t) = .away → P.inv G₁ m₁ → ¬ E.IsSet m₁ →
      P.Live t G₁ m₁)
    (hu : 0 < (L.part g).gh.ac.frag .unmetered) (hi : P.inv (upd G t g) m) :
    P.WP t (Io_Event_waitUncancelable p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      E.IsSet m' ∧ E.Synced t m' ∧ P.inv (upd G' t g) m') G m d := by
  subst hp
  have hi0 := hE.enterWait hgx hgo hwx hone hhb hi
  fsym [FEvent.wp_casAs (g := E.set g .w0) hE
      (exp := Io_Event.unset) (new := .waiting) rfl rfl event_dec,
    WP.loop _ _ (waitInv P E t g d) (fun _ => 0) (waitPost P E t g d)
      (event_wait_body hE hcost t g hgx hgo hu d io hlive),
    hE.lph, E.ph_set, E.set_set, FEvent.set_of hgx, event_of0, event_of1, event_of2,
    waitInv, waitPost, Io_Event_waitUncancelable.again17]

/-- The wait's resource contract (as `Sync.ioEvent_wait_wp_resource`). -/
theorem event_wait_wp_resource (hE : L.Fits (E.prim L) P U ok) (hcost : P.cost = none)
    {p : Ptr} (hp : p = E.W.ptr) (t : ThreadId) (g : γ) (hgx : E.ph g = .out)
    (hgo : L.ph g = .out) (hwx : E.wx g) (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hone : ∀ u, u ≠ t → ¬ (E.ph (G u)).Waiting)
    (hhb : ∀ j < (E.W.hist m).size, (E.W.hist m)[j]!.Val (1 : BitVec 32) →
      VClock.le (E.W.hist m)[j]!.clock (m.clocks[t]!) = true)
    (hlive : ∀ G₁ m₁, E.ph (G₁ t) = .w1 → L.ph (G₁ t) = .away → P.inv G₁ m₁ → ¬ E.IsSet m₁ →
      P.Live t G₁ m₁)
    (hu : payUnmetered t (L.part g)) (hi : P.inv (upd G t g) m) :
    P.WP t (Io_Event_waitUncancelable p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      E.IsSet m' ∧ E.Synced t m' ∧ ∃ r', keepPart t (L.part g) r' ∧
        P.inv (upd G' t (L.setPart g r')) m') G m d := by
  refine WP.mono ?_ (event_wait_wp_unmetered hE hcost hp t g hgx hgo hwx io G m d
    hone hhb hlive hu hi)
  rintro _ G' m' d' ⟨hd, hc, hs, hy, hi'⟩
  exact ⟨hd, hc, hs, hy, L.part g, rfl, by simpa only [L.setPart_self] using hi'⟩

end

/-- This profile's translated `Io.Event` satisfies the general event contract. -/
def event : EventImpl Tgt where
  wait := Io_Event_waitUncancelable
  set := Io_Event_set
  wait_pre := payUnmetered
  wait_post := keepPart
  wait_plain_pre _ _ := payUnmetered_plain
  wait_plain_post _ _ _ _ hr := hr
  wait_wp_resource := event_wait_wp_resource
  set_pre := anyPart
  set_post := keepPart
  set_unmetered_pre _ _ _ := trivial
  set_unmetered_post _ _ _ _ hr := hr
  set_wp_resource := event_set_wp_resource

end Sync.CaseContracts.V0_17_1.H_6c696e7578
