import Proofs.Sync.Gen
import ZigLean.Sep.Full.Event

/-!
# `Io.Event` of `examples/sync` as an event (`EventImpl`)

The per-item obligation of `Io.Event` (Zig 0.16.0's std code; 0.17.0 translates to the same code)
in this program's generated code: `waitUncancelable` and `set` walked with the rules of the
futex event (`ZigLean/Sep/Full/Event.lean`), for every protocol that has the event next to a lock.
-/

open Zig Zig.Conc Zig.Full Zig.Conc.Proto

namespace Sync

theorem ioEvent_dec : ∀ b : BitVec 32, (b = 0 ∨ b = 1 ∨ b = 2) →
    ∃ r, (Packed.ofBits? (α := Io_Event) b).run = some (.ok r) := by
  rintro b (rfl | rfl | rfl) <;> exact ⟨_, rfl⟩

theorem ioEvent_of0 {r : Io_Event} (h : (Packed.ofBits? (α := Io_Event) 0).run = some (.ok r)) :
    r = .unset := by
  have : (Packed.ofBits? (α := Io_Event) 0).run = some (.ok .unset) := rfl
  rw [this] at h; cases h; rfl

theorem ioEvent_of1 {r : Io_Event} (h : (Packed.ofBits? (α := Io_Event) 1).run = some (.ok r)) :
    r = .waiting := by
  have : (Packed.ofBits? (α := Io_Event) 1).run = some (.ok .waiting) := rfl
  rw [this] at h; cases h; rfl

theorem ioEvent_of2 {r : Io_Event} (h : (Packed.ofBits? (α := Io_Event) 2).run = some (.ok r)) :
    r = .is_set := by
  have : (Packed.ofBits? (α := Io_Event) 2).run = some (.ok .is_set) := rfl
  rw [this] at h; cases h; rfl

section
variable {γ : Type} {L : FLock γ} {E : FEvent γ} {P : Proto Tgt γ}
  {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}

/-- `Io.Event.set` by a thread out of the event's and the lock's code. -/
theorem ioEvent_set_wp (hE : E.Fits L P U ok) (hP : L.FitsOn P U ok) (hcost : P.cost = none)
    {p : Ptr} (hp : p = E.W.ptr) (t : ThreadId) (g : γ) (hgx : E.ph g = .out)
    (hgo : L.ph g = .out) (hok : ok g) (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hi : P.inv (upd G t g) m) :
    P.WP t (Io_Event_set p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧ E.IsSet m' ∧
      P.inv (upd G' t g) m') G m d := by
  subst hp
  unfold Io_Event_set
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  rw [StateT.run_bind]
  refine WP.bind (FEvent.wp_xchgAs hE hP rfl ioEvent_dec hgx hgo hok hi
    fun k hk G₁ m₁ o r hc₁ ho3 hd hs hcase => ?_)
  rcases hcase with ⟨rfl, hi₁⟩ | ⟨ho, hi₁⟩
  · obtain rfl := ioEvent_of1 hd
    simp only [StateT.run_bind, StateT.run_pure, pure_bind, bind_assoc]
    refine WP.bind (FEvent.wp_wake hE hP (by decide) (E.ph_set _ _) (by rw [hE.lph]; exact hgo)
      ((hE.ok_e _ _).mpr hok) hi₁ fun k₂ hk₂ G₂ m₂ hc₂ hs₂ hi₂ => ?_)
    rw [E.set_set, FEvent.set_of hgx] at hi₂
    exact WP.pure' (WP.pure' ⟨by omega, hc₂, hs₂, hi₂⟩)
  · rw [FEvent.set_of hgx] at hi₁
    rcases ho3 with rfl | rfl | rfl
    · obtain rfl := ioEvent_of0 hd
      exact WP.pure' (WP.pure' ⟨by omega, hc₁, hs, hi₁⟩)
    · exact absurd rfl ho
    · obtain rfl := ioEvent_of2 hd
      exact WP.pure' (WP.pure' ⟨by omega, hc₁, hs, hi₁⟩)

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
theorem wait_body (hE : E.Fits L P U ok) (hP : L.FitsOn P U ok) (hcost : P.cost = none)
    (t : ThreadId) (g : γ) (hgx : E.ph g = .out) (hgo : L.ph g = .out) (hok : ok g) (D : Nat)
    (io : Io)
    (hlive : ∀ G₁ m₁, E.ph (G₁ t) = .w1 → L.ph (G₁ t) = .away → P.inv G₁ m₁ → ¬ E.IsSet m₁ →
      P.Live t G₁ m₁)
    (s : Io_Event_waitUncancelableLocals) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (h : waitInv P E t g D s G m d) :
    P.WP t ((Io_Event_waitUncancelable.loop17 E.W.ptr io).run s) (fun r G' m' d' =>
      if Io_Event_waitUncancelable.again17 r.1 then waitInv P E t g D r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : Io_Event_waitUncancelableLocals) => 0) s)
      else waitPost P E t g D r G' m' d') G m d := by
  obtain ⟨hD, -, hi⟩ := h
  have hg1 : E.ph (E.set g .w1) = .w1 := E.ph_set _ _
  have hgo1 : L.ph (E.set g .w1) = .out := by rw [hE.lph]; exact hgo
  have hok1 := (hE.ok_e g .w1).mpr hok
  unfold Io_Event_waitUncancelable.loop17
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  refine WP.bind (FEvent.wp_wait hE hP (by decide) hg1 hgo1 hok1 hi hlive
    fun k hk G₁ m₁ hc₁ hi₁ => ?_)
  refine WP.bind (FEvent.wp_loadAs hE hP ioEvent_dec (.inr hg1) hgo1 hok1 hi₁
    fun k₂ hk₂ G₂ m₂ b r hc₂ hd hcase => ?_)
  rcases hcase with ⟨-, h0, -⟩ | ⟨rfl, hi₂⟩ | ⟨rfl, hs, hi₂⟩
  · rw [hg1] at h0; cases h0
  · obtain rfl := ioEvent_of1 hd
    rw [E.set_set] at hi₂
    refine WP.pure' ?_
    simp only [Io_Event_waitUncancelable.again17, ↓reduceIte]
    exact ⟨⟨by omega, hc₂, hi₂⟩, .inl (by omega)⟩
  · obtain rfl := ioEvent_of2 hd
    rw [E.set_set, FEvent.set_of hgx] at hi₂
    exact WP.pure' ⟨rfl, by omega, hc₂, hs, hi₂⟩

/-- **`Io.Event.waitUncancelable`** by a thread out of the event's and the lock's code, as the
only waiter (`hone`, `hhb`): it returns when the event is set. -/
theorem ioEvent_wait_wp (hE : E.Fits L P U ok) (hP : L.FitsOn P U ok) (hcost : P.cost = none)
    {p : Ptr} (hp : p = E.W.ptr) (t : ThreadId) (g : γ) (hgx : E.ph g = .out)
    (hgo : L.ph g = .out) (hok : ok g) (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hone : ∀ u, u ≠ t → E.ph (G u) = .out ∨ E.ph (G u) = .sw)
    (hhb : ∀ j < (E.W.hist m).size, (E.W.hist m)[j]!.Val (1 : BitVec 32) →
      VClock.le (E.W.hist m)[j]!.clock (m.clocks[t]!) = true)
    (hlive : ∀ G₁ m₁, E.ph (G₁ t) = .w1 → L.ph (G₁ t) = .away → P.inv G₁ m₁ → ¬ E.IsSet m₁ →
      P.Live t G₁ m₁)
    (hi : P.inv (upd G t g) m) :
    P.WP t (Io_Event_waitUncancelable p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      E.IsSet m' ∧ P.inv (upd G' t g) m') G m d := by
  subst hp
  have hi0 := hE.enter hP hgx hgo hok hone hhb hi
  have hg0 : E.ph (E.set g .w0) = .w0 := E.ph_set _ _
  have hgo0 : L.ph (E.set g .w0) = .out := by rw [hE.lph]; exact hgo
  have hok0 := (hE.ok_e g .w0).mpr hok
  have hloop : ∀ G₃ m₃ d₃, waitInv P E t g d default G₃ m₃ d₃ →
      P.WP t ((loop (Io_Event_waitUncancelable.loop17 E.W.ptr io)
        Io_Event_waitUncancelable.again17).run default) (waitPost P E t g d) G₃ m₃ d₃ :=
    fun G₃ m₃ d₃ h₃ => WP.loop _ _ (waitInv P E t g d) (fun _ => 0) (waitPost P E t g d)
      (wait_body hE hP hcost t g hgx hgo hok d io hlive) default G₃ m₃ d₃ h₃
  unfold Io_Event_waitUncancelable
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  refine WP.bind (FEvent.wp_casAs hE hP rfl rfl ioEvent_dec hg0 hgo0 hok0 hi0
    fun k hk G₁ m₁ hc₁ => ⟨fun hi₁ => ?_, fun b r hd hcase => ?_⟩)
  · rw [E.set_set] at hi₁
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind]
    refine WP.mono ?_ (hloop G₁ m₁ k ⟨by omega, hc₁, hi₁⟩)
    rintro ⟨e, s'⟩ G' m' d' ⟨rfl, hd', hc', hs', hi'⟩
    exact WP.pure' ⟨hd', hc', hs', hi'⟩
  · simp only [Option.isSome_some, ↓reduceIte, StateT.run_bind, bind_assoc]
    refine WP.bind (WP.callRC (fun e he => by cases he) fun a ha => ?_)
    cases ha
    rcases hcase with ⟨rfl, hi₁⟩ | ⟨rfl, hs, hi₁⟩
    · obtain rfl := ioEvent_of1 hd
      rw [E.set_set] at hi₁
      simp only [StateT.run_pure, pure_bind]
      refine WP.mono ?_ (hloop G₁ m₁ k ⟨by omega, hc₁, hi₁⟩)
      rintro ⟨e, s'⟩ G' m' d' ⟨rfl, hd', hc', hs', hi'⟩
      exact WP.pure' ⟨hd', hc', hs', hi'⟩
    · obtain rfl := ioEvent_of2 hd
      rw [E.set_set, FEvent.set_of hgx] at hi₁
      simp only [StateT.run_pure, pure_bind]
      exact WP.pure' (WP.pure' ⟨by omega, hc₁, hs, hi₁⟩)

end

/-- **`Io.Event` is an event** (`EventImpl`) in this program. -/
def ioEvent : EventImpl Tgt where
  wait := Io_Event_waitUncancelable
  set := Io_Event_set
  wait_wp := ioEvent_wait_wp
  set_wp := ioEvent_set_wp

end Sync
