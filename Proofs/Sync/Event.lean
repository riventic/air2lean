import Proofs.Sync.Gen
import ZigLean.Sep.Full.Event
import ZigLean.Sep.Full.AutoWP
import ZigLean.Sep.Full.LockSteps

/-!
# `Io.Event` of `examples/sync` as an event (`EventImpl`)

The per-item obligation of `Io.Event` (Zig 0.16.0's std code; 0.17.0 translates to the same code)
in this program's generated code: `waitUncancelable` and `set` walked with the rules of the
futex event (`ZigLean/Sep/Full/Event.lean`), for every protocol that has the event next to a lock.
The wait's `fsym` walk pays each loop tick from a positive unmetered caller fragment while
preserving the complete caller part. The unticked setter needs no payment admission.
-/

open Zig Zig.Conc Zig.Full Zig.Conc.Proto

namespace Sync

theorem ioEvent_dec : ∀ b : BitVec 32, (b = 0 ∨ b = 1 ∨ b = 2) →
    ∃ r, (Packed.ofBits? (α := Io_Event) b).run = some (.ok r) := by
  rintro b (rfl | rfl | rfl) <;> exact ⟨_, rfl⟩

/-- Closed decoder equations remain available after the walk splits a returned enum value. -/
theorem ioEvent_decode0 :
    (Packed.ofBits? (α := Io_Event) 0).run = some (.ok .unset) := rfl

theorem ioEvent_decode1 :
    (Packed.ofBits? (α := Io_Event) 1).run = some (.ok .waiting) := rfl

theorem ioEvent_decode2 :
    (Packed.ofBits? (α := Io_Event) 2).run = some (.ok .is_set) := rfl

attribute [local fsym_arith] ioEvent_decode0 ioEvent_decode1 ioEvent_decode2

theorem ioEvent_of0 {r : Io_Event} (h : (Packed.ofBits? (α := Io_Event) 0).run = some (.ok r)) :
    r = .unset := by
  rw [ioEvent_decode0] at h; cases h; rfl

theorem ioEvent_of1 {r : Io_Event} (h : (Packed.ofBits? (α := Io_Event) 1).run = some (.ok r)) :
    r = .waiting := by
  rw [ioEvent_decode1] at h; cases h; rfl

theorem ioEvent_of2 {r : Io_Event} (h : (Packed.ofBits? (α := Io_Event) 2).run = some (.ok r)) :
    r = .is_set := by
  rw [ioEvent_decode2] at h; cases h; rfl

section
variable {γ : Type} {L : FLock γ} {E : FEvent γ} {P : Proto Tgt γ}
  {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}

attribute [local irreducible] Proto.WP

/-- `Io.Event.set` by a thread out of the event's and the lock's code. -/
theorem ioEvent_set_wp (hE : L.Fits (E.prim L) P U ok) (hcost : P.cost = none)
    {p : Ptr} (hp : p = E.W.ptr) (t : ThreadId) (g : γ) (hgx : E.ph g = .out)
    (hgo : L.ph g = .out) (hsx : E.sx g) (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hi : P.inv (upd G t g) m) :
    P.WP t (Io_Event_set p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧ E.IsSet m' ∧
      P.inv (upd G' t g) m') G m d := by
  subst hp
  fsym [FEvent.wp_xchgAs (g := g) hE (v := Io_Event.is_set) rfl ioEvent_dec,
    FEvent.wp_wake (g := E.set g .sw) hE,
    hE.lph, E.ph_set, E.set_set, FEvent.set_of hgx, ioEvent_of0, ioEvent_of1, ioEvent_of2]

/-- `waitUncancelable`'s loop invariant: `t` is a waiter at `w1`. -/
def waitInv (P : Proto Tgt γ) (E : FEvent γ) (t : ThreadId) (g : γ) (D : Nat)
    (_ : Io_Event_waitUncancelableLocals) (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ m.current = t ∧ P.inv (upd G t (E.set g .w1)) m

/-- `waitUncancelable`'s loop ends when the event is set: `t` is out. -/
def waitPost (P : Proto Tgt γ) (E : FEvent γ) (t : ThreadId) (g : γ) (D : Nat)
    (r : Io_Event_waitUncancelableExit × Io_Event_waitUncancelableLocals) (G : ThreadId → γ)
    (m : Mem) (d : Nat) : Prop :=
  r.1 = .ret ∧ d < D ∧ m.current = t ∧ E.IsSet m ∧ P.inv (upd G t g) m

/-- One repeat of `waitUncancelable`'s loop: the futex wait, then an acquire load. -/
theorem wait_body (hE : L.Fits (E.prim L) P U ok) (hcost : P.cost = none)
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
    FEvent.wp_loadAs (g := E.set g .w1) hE ioEvent_dec, hE.lpart, hE.lph, E.ph_set, E.set_set,
    FEvent.set_of hgx, ioEvent_of0, ioEvent_of1, ioEvent_of2,
    waitInv, waitPost, Io_Event_waitUncancelable.again17]

/-- **`Io.Event.waitUncancelable`** by a thread out of the event's and the lock's code, as the
only waiter (`hone`, `hhb`): it returns when the event is set. -/
theorem ioEvent_wait_wp_unmetered (hE : L.Fits (E.prim L) P U ok) (hcost : P.cost = none)
    {p : Ptr} (hp : p = E.W.ptr) (t : ThreadId) (g : γ) (hgx : E.ph g = .out)
    (hgo : L.ph g = .out) (hwx : E.wx g) (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hone : ∀ u, u ≠ t → E.ph (G u) = .out ∨ E.ph (G u) = .sw)
    (hhb : ∀ j < (E.W.hist m).size, (E.W.hist m)[j]!.Val (1 : BitVec 32) →
      VClock.le (E.W.hist m)[j]!.clock (m.clocks[t]!) = true)
    (hlive : ∀ G₁ m₁, E.ph (G₁ t) = .w1 → L.ph (G₁ t) = .away → P.inv G₁ m₁ → ¬ E.IsSet m₁ →
      P.Live t G₁ m₁)
    (hu : 0 < (L.part g).gh.ac.frag .unmetered) (hi : P.inv (upd G t g) m) :
    P.WP t (Io_Event_waitUncancelable p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      E.IsSet m' ∧ P.inv (upd G' t g) m') G m d := by
  subst hp
  have hi0 := hE.enterWait hgx hgo hwx hone hhb hi
  fsym [FEvent.wp_casAs (g := E.set g .w0) hE
      (exp := Io_Event.unset) (new := .waiting) rfl rfl ioEvent_dec,
    WP.loop _ _ (waitInv P E t g d) (fun _ => 0) (waitPost P E t g d)
      (wait_body hE hcost t g hgx hgo hu d io hlive),
    hE.lph, E.ph_set, E.set_set, FEvent.set_of hgx, ioEvent_of0, ioEvent_of1, ioEvent_of2,
    waitInv, waitPost, Io_Event_waitUncancelable.again17]

/-- The existing Plain rule specializes the actual unmetered wait proof. -/
theorem ioEvent_wait_wp (hE : L.Fits (E.prim L) P U ok) (hcost : P.cost = none)
    {p : Ptr} (hp : p = E.W.ptr) (t : ThreadId) (g : γ) (hgx : E.ph g = .out)
    (hgo : L.ph g = .out) (hwx : E.wx g) (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hone : ∀ u, u ≠ t → E.ph (G u) = .out ∨ E.ph (G u) = .sw)
    (hhb : ∀ j < (E.W.hist m).size, (E.W.hist m)[j]!.Val (1 : BitVec 32) →
      VClock.le (E.W.hist m)[j]!.clock (m.clocks[t]!) = true)
    (hlive : ∀ G₁ m₁, E.ph (G₁ t) = .w1 → L.ph (G₁ t) = .away → P.inv G₁ m₁ → ¬ E.IsSet m₁ →
      P.Live t G₁ m₁)
    (hplain : (L.part g).Plain) (hi : P.inv (upd G t g) m) :
    P.WP t (Io_Event_waitUncancelable p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      E.IsSet m' ∧ P.inv (upd G' t g) m') G m d :=
  ioEvent_wait_wp_unmetered hE hcost hp t g hgx hgo hwx io G m d hone hhb hlive hplain.2 hi

/-- The unbounded wait loop preserves the whole caller part, including stack resources,
using its actual positive unmetered fragment at each entry. -/
def ioEvent_waitResources : CallerResources where
  pre _ r := 0 < r.gh.ac.frag .unmetered
  during _ r r' := r' = r
  post _ r r' := r' = r
  plain_pre _ _ hp := hp.2
  plain_post _ _ _ _ hr := hr

/-- `set` contains no tick and preserves every caller part without a payment guard. -/
def ioEvent_setResources : CallerResources where
  pre _ _ := True
  during _ r r' := r' = r
  post _ r r' := r' = r
  plain_pre _ _ _ := True.intro
  plain_post _ _ _ _ hr := hr

/-- The wait's resource contract uses the exact part retained by its unmetered proof. -/
theorem ioEvent_wait_wp_resource (hE : L.Fits (E.prim L) P U ok) (hcost : P.cost = none)
    {p : Ptr} (hp : p = E.W.ptr) (t : ThreadId) (g : γ) (hgx : E.ph g = .out)
    (hgo : L.ph g = .out) (hwx : E.wx g) (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hone : ∀ u, u ≠ t → E.ph (G u) = .out ∨ E.ph (G u) = .sw)
    (hhb : ∀ j < (E.W.hist m).size, (E.W.hist m)[j]!.Val (1 : BitVec 32) →
      VClock.le (E.W.hist m)[j]!.clock (m.clocks[t]!) = true)
    (hlive : ∀ G₁ m₁, E.ph (G₁ t) = .w1 → L.ph (G₁ t) = .away → P.inv G₁ m₁ → ¬ E.IsSet m₁ →
      P.Live t G₁ m₁)
    (hu : ioEvent_waitResources.pre t (L.part g)) (hi : P.inv (upd G t g) m) :
    P.WP t (Io_Event_waitUncancelable p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      E.IsSet m' ∧ ∃ r', ioEvent_waitResources.post t (L.part g) r' ∧
        P.inv (upd G' t (L.setPart g r')) m') G m d := by
  refine WP.mono ?_ (ioEvent_wait_wp_unmetered hE hcost hp t g hgx hgo hwx io G m d
    hone hhb hlive hu hi)
  rintro _ G' m' d' ⟨hd, hc, hs, hi'⟩
  exact ⟨hd, hc, hs, L.part g, rfl, by simpa only [L.setPart_self] using hi'⟩

/-- The resource contract exposes the unchanged unticked setter proof. -/
theorem ioEvent_set_wp_resource (hE : L.Fits (E.prim L) P U ok) (hcost : P.cost = none)
    {p : Ptr} (hp : p = E.W.ptr) (t : ThreadId) (g : γ) (hgx : E.ph g = .out)
    (hgo : L.ph g = .out) (hsx : E.sx g) (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (_hpre : ioEvent_setResources.pre t (L.part g)) (hi : P.inv (upd G t g) m) :
    P.WP t (Io_Event_set p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧ E.IsSet m' ∧
      ∃ r', ioEvent_setResources.post t (L.part g) r' ∧
        P.inv (upd G' t (L.setPart g r')) m') G m d := by
  refine WP.mono ?_ (ioEvent_set_wp hE hcost hp t g hgx hgo hsx io G m d hi)
  rintro _ G' m' d' ⟨hd, hc, hs, hi'⟩
  exact ⟨hd, hc, hs, L.part g, rfl, by simpa only [L.setPart_self] using hi'⟩

end

/-- **`Io.Event` is an event** (`EventImpl`) in this program. -/
def ioEvent : EventImpl Tgt where
  wait := Io_Event_waitUncancelable
  set := Io_Event_set
  wait_resources := ioEvent_waitResources
  set_resources := ioEvent_setResources
  wait_wp_resource := ioEvent_wait_wp_resource
  set_wp_resource := ioEvent_set_wp_resource

end Sync
