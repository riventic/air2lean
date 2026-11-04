import Proofs.Sync.IoMutex
import ZigLean.Sep.Full.Cond
import ZigLean.Sep.Full.LockSteps
import ZigLean.Sep.Full.AutoWP
import ZigLean.VersionGate

/-!
# `Io.Condition` of `examples/sync` as a condition (`CondImpl`)

The per-item obligation of `Io.Condition` (Zig 0.16.0's std code; 0.17.0 inlines the
uncancelable loops of `waitInner` into `waitUncancelable`) in this program's generated code:
`waitUncancelable` and `signal` walked with the rules of the futex-epoch condition
(`ZigLean/Sep/Full/Cond.lean`), with the program's `Io.Mutex` (`ioMutex`), for every protocol
that has the condition next to its mutex. The wait is walked once per translation
(`ZigLean.VersionGate`); `ioCond` is version-neutral.
-/

open Zig Zig.Conc Zig.Full Zig.Conc.Proto

namespace Sync

-- Unification must not unfold `WP` into the program (as in `Proofs/Sync/RwLock.lean`).
attribute [local irreducible] Proto.WP

/-! ## The state's values

Stated for a value `b` of the state with a hypothesis, so that the walks keep `b` abstract (a
literal state would let the kernel evaluate the packed fields). -/

theorem condS_of (b : BitVec 32) :
    (Packed.ofBits? (α := Io_Condition_State) b).run = some (.ok (Packed.ofBits b)) := rfl

theorem condS_dec : ∀ b : BitVec 32, (b = 0 ∨ b = 1 ∨ b = 0x10001) →
    ∃ r, (Packed.ofBits? (α := Io_Condition_State) b).run = some (.ok r) :=
  fun b _ => ⟨_, condS_of b⟩

theorem condS_eq {b : BitVec 32} {r : Io_Condition_State}
    (h : (Packed.ofBits? (α := Io_Condition_State) b).run = some (.ok r)) : r = Packed.ofBits b := by
  rw [condS_of] at h; cases h; rfl

theorem condS_bits {b : BitVec 32} (hb : b = 0 ∨ b = 1 ∨ b = 0x10001) :
    Packed.toBits (Packed.ofBits b : Io_Condition_State) = b := by
  rcases hb with rfl | rfl | rfl <;> decide +kernel

theorem condS_bits1 : Packed.toBits (Packed.ofBits (1 : BitVec 32) : Io_Condition_State) = 1 :=
  condS_bits (.inr (.inl rfl))

/-- A signaller's new state after `(1, 0)`: `(1, 1)`. -/
theorem condS_sig {b : BitVec 32} (h : b = 1) :
    Packed.toBits (Io_Condition_State.mk (Packed.ofBits b : Io_Condition_State).waiters 1) =
      0x10001 := by
  subst h; decide +kernel

/-- The existing one-waiter state has no signal before the signaller's addition. -/
theorem condS_signals_zero {v : Io_Condition_State}
    (hv : v = Packed.ofBits (1 : BitVec 32)) : v.signals.toNat = 0 := by
  rw [hv]
  rfl

/-- The checked addition in the one-waiter branch produces exactly one signal. -/
theorem condS_signal_value {v : Io_Condition_State} {r : BitVec 16}
    (hr : r.toNat = v.signals.toNat + 1)
    (hv : v = Packed.ofBits (1 : BitVec 32)) : r = 1 := by
  apply BitVec.eq_of_toNat_eq
  calc
    r.toNat = v.signals.toNat + 1 := hr
    _ = (1 : BitVec 16).toNat := by rw [condS_signals_zero hv]; rfl

/-- The waiter's new state after `(1, 1)`: `(0, 0)`. -/
theorem condS_take {b : BitVec 32} (h : b = 0x10001) :
    Packed.toBits (Io_Condition_State.mk ((Packed.ofBits b : Io_Condition_State).waiters - 1)
      ((Packed.ofBits b : Io_Condition_State).signals - 1)) = 0 := by
  subst h; decide +kernel

theorem condS_add1 {b : BitVec 32} (h : b = 1) :
    (add false (Packed.ofBits b : Io_Condition_State).signals (1 : BitVec 16)).run =
      some (.ok 1) := by
  subst h
  cases h : (add false (Packed.ofBits (1 : BitVec 32) : Io_Condition_State).signals
    (1 : BitVec 16)).run with
  | none =>
    exact absurd h (by
      simp [add]; split <;> simp [throw, throwThe, MonadExceptOf.throw, ExceptT.mk, pure,
        ExceptT.pure, ExceptT.run])
  | some r =>
    cases r with
    | error e => exact absurd h (add_one_noErr (by decide) e)
    | ok v =>
      have := add_one_ok h (by decide)
      rw [show v = 1 from BitVec.eq_of_toNat_eq (by rw [this]; decide)]

theorem condS_subW {b : BitVec 32} (h : b = 0x10001) :
    (sub false (Packed.ofBits b : Io_Condition_State).waiters (1 : BitVec 16)).run =
    some (.ok ((Packed.ofBits b : Io_Condition_State).waiters - 1)) := by
  subst h; rfl

theorem condS_subS {b : BitVec 32} (h : b = 0x10001) :
    (sub false (Packed.ofBits b : Io_Condition_State).signals (1 : BitVec 16)).run =
    some (.ok ((Packed.ofBits b : Io_Condition_State).signals - 1)) := by
  subst h; rfl

theorem condS_gtWS {b : BitVec 32} (hb : b = 0 ∨ b = 1 ∨ b = 0x10001) :
    gt false (Packed.ofBits b : Io_Condition_State).waiters
      (Packed.ofBits b : Io_Condition_State).signals = decide (b = 1) := by
  rcases hb with rfl | rfl | rfl <;> decide +kernel

theorem condS_gtS {b : BitVec 32} (hb : b = 1 ∨ b = 0x10001) :
    gt false (Packed.ofBits b : Io_Condition_State).signals 0 = decide (b = 0x10001) := by
  rcases hb with rfl | rfl <;> decide +kernel

theorem condS_lt0 {b : BitVec 32} (h : b = 0) :
    lt false (Packed.ofBits b : Io_Condition_State).waiters (65535 : BitVec 16) = true := by
  subst h; decide +kernel

theorem debugAssert_true : (debug_assert true).run = some (.ok ()) := rfl


section
variable {γ : Type} {L : FLock γ} {C : FCond γ} {P : Proto Tgt γ}
  {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}

/-! ## `signal` -/

/-- `signal`'s loop invariant: `t` read the state value `b`; a value other than `(1, 0)` means a
registered waiter was signalled. -/
def sigInv (P : Proto Tgt γ) (C : FCond γ) (t : ThreadId) (g : γ) (D : Nat)
    (s : Io_Condition_signalLocals) (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ m.current = t ∧ P.inv (upd G t g) m ∧
    ((s.prev_state = Packed.ofBits (0 : BitVec 32) ∧
        ∀ u i jr sn e, C.ph (G u) = .reg i jr sn e → C.Signalled m) ∨
      s.prev_state = Packed.ofBits (1 : BitVec 32) ∨
      (s.prev_state = Packed.ofBits (0x10001 : BitVec 32) ∧
        ∀ u i jr sn e, C.ph (G u) = .reg i jr sn e → C.Signalled m))

/-- The explicit alternatives are exactly the original finite existential invariant. -/
theorem sigInv_iff_exists (P : Proto Tgt γ) (C : FCond γ) (t : ThreadId) (g : γ) (D : Nat)
    (s : Io_Condition_signalLocals) (G : ThreadId → γ) (m : Mem) (d : Nat) :
    sigInv P C t g D s G m d ↔
      d < D ∧ m.current = t ∧ P.inv (upd G t g) m ∧
        ∃ b : BitVec 32, s.prev_state = Packed.ofBits b ∧
          (b = 0 ∨ b = 1 ∨ b = 0x10001) ∧
          (b ≠ 1 → ∀ u i jr sn e, C.ph (G u) = .reg i jr sn e → C.Signalled m) := by
  constructor
  · rintro ⟨hd, hc, hi, hs⟩
    refine ⟨hd, hc, hi, ?_⟩
    rcases hs with ⟨hp, hs⟩ | hp | ⟨hp, hs⟩
    · exact ⟨0, hp, .inl rfl, fun _ => hs⟩
    · exact ⟨1, hp, .inr (.inl rfl), fun h => (h rfl).elim⟩
    · exact ⟨0x10001, hp, .inr (.inr rfl), fun _ => hs⟩
  · rintro ⟨hd, hc, hi, b, hp, hb, hs⟩
    refine ⟨hd, hc, hi, ?_⟩
    rcases hb with rfl | rfl | rfl
    · exact .inl ⟨hp, hs (by decide)⟩
    · exact .inr (.inl hp)
    · exact .inr (.inr ⟨hp, hs (by decide)⟩)

/-- `signal`'s loop ends with `t` out and a registered waiter signalled. -/
def sigPost (P : Proto Tgt γ) (C : FCond γ) (t : ThreadId) (g : γ) (D : Nat)
    (r : Io_Condition_signalExit × Io_Condition_signalLocals) (G : ThreadId → γ) (m : Mem)
    (d : Nat) : Prop :=
  (r.1 = .ret ∨ r.1 = .br10) ∧ d < D ∧ m.current = t ∧ P.inv (upd G t g) m ∧
    ∀ u i jr sn e, C.ph (G u) = .reg i jr sn e → C.Signalled m

theorem sig_body (hC : L.Fits (C.prim L) P U ok) (hcost : P.cost = none)
    (t : ThreadId) (g : γ) (hgx : C.ph g = .out)
    (hgo : L.ph g = .out ∨ L.ph g = .holds) (hsx : C.sx g)
    (hu : 0 < (L.part g).gh.ac.frag .unmetered) (D : Nat)
    (io : Io)
    (hseen : ∀ G₁ rX m₁, G₁ t = g → U G₁ rX m₁ → ∀ u i jr sn e, C.ph (G₁ u) = .reg i jr sn e →
      VClock.le (C.S.hist m₁)[jr]!.clock (m₁.clocks[t]!) = true)
    (s : Io_Condition_signalLocals) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (h : sigInv P C t g D s G m d) :
    P.WP t ((Io_Condition_signal.loop11 C.S.ptr io).run s) (fun r G' m' d' =>
      if Io_Condition_signal.again11 r.1 then sigInv P C t g D r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : Io_Condition_signalLocals) => 0) s)
      else sigPost P C t g D r G' m' d') G m d := by
  fsym [hC.wp_tick_unmetered_exact (t := t) (g := g), hC.lpart,
    FCond.wp_signalAs hC condS_dec, FCond.wp_bump hC, FCond.wp_wakeEp hC,
    hC.wp_projE (t := t), condS_eq, condS_bits, condS_sig, condS_signal_value, condS_add1, condS_gtWS,
    C.ph_set, hC.lph, C.set_set, FCond.set_of, (FCond.set_of hgx), FCond.ptr_ep,
    FCond.Signalled, FCond.lastS,
    (fun (m : Mem) => Word.hist_congr (W := C.S) (m := m) (m' := m.ticked) rfl rfl),
    sigInv, sigPost, Io_Condition_signal.again11]

/-- **`Io.Condition.signal`** outside or holding the mutex, preserving its complete resource,
after every registration (`hseen`). -/
theorem ioCond_signal_wp_unmetered (hC : L.Fits (C.prim L) P U ok) (hcost : P.cost = none)
    {p : Ptr} (hp : p = C.S.ptr) (t : ThreadId) (g : γ) (hgx : C.ph g = .out)
    (hgo : L.ph g = .out ∨ L.ph g = .holds) (hsx : C.sx g)
    (hu : 0 < (L.part g).gh.ac.frag .unmetered)
    (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hseen : ∀ G₁ rX m₁, G₁ t = g → U G₁ rX m₁ → ∀ u i jr sn e, C.ph (G₁ u) = .reg i jr sn e →
      VClock.le (C.S.hist m₁)[jr]!.clock (m₁.clocks[t]!) = true)
    (hi : P.inv (upd G t g) m) :
    P.WP t (Io_Condition_signal p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      P.inv (upd G' t g) m' ∧ ∀ u i jr sn e, C.ph (G' u) = .reg i jr sn e → C.Signalled m')
      G m d := by
  fsym [FCond.wp_sloadAs hC condS_dec, condS_eq,
    WP.loop _ _ (sigInv P C t g d) (fun _ => 0) (sigPost P C t g d)
      (sig_body hC hcost t g hgx hgo hsx hu d io hseen),
    sigInv, sigPost]

/-- The signal contract checks its registration floor at the actual intermediate part.
This implementation's proved singleton profile identifies that part with the original one. -/
theorem ioCond_signal_wp_resource (hC : L.Fits (C.prim L) P U ok) (hcost : P.cost = none)
    {p : Ptr} (hp : p = C.S.ptr) (t : ThreadId) (g : γ) (hgx : C.ph g = .out)
    (hgo : L.ph g = .out ∨ L.ph g = .holds) (hsx : C.sx g)
    (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hu : payUnmetered t (L.part g))
    (hseen : ∀ rᵢ, keepPart t (L.part g) rᵢ → ∀ G₁ rX m₁,
      G₁ t = L.setPart g rᵢ → U G₁ rX m₁ → ∀ u i jr sn e,
      C.ph (G₁ u) = .reg i jr sn e →
        VClock.le (C.S.hist m₁)[jr]!.clock (m₁.clocks[t]!) = true)
    (hi : P.inv (upd G t g) m) :
    P.WP t (Io_Condition_signal p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ r', keepPart t (L.part g) r' ∧
        P.inv (upd G' t (L.setPart g r')) m' ∧
        ∀ u i jr sn e, C.ph (G' u) = .reg i jr sn e → C.Signalled m') G m d := by
  have hseenExact : ∀ G₁ rX m₁, G₁ t = g → U G₁ rX m₁ → ∀ u i jr sn e,
      C.ph (G₁ u) = .reg i jr sn e →
        VClock.le (C.S.hist m₁)[jr]!.clock (m₁.clocks[t]!) = true := by
    intro G₁ rX m₁ ht hU
    exact hseen (L.part g) rfl G₁ rX m₁ (by simpa only [L.setPart_self] using ht) hU
  refine WP.mono ?_ (ioCond_signal_wp_unmetered hC hcost hp t g hgx hgo hsx hu
    io G m d hseenExact hi)
  rintro _ G' m' d' ⟨hd, hc, hi', hsig⟩
  exact ⟨hd, hc, L.part g, rfl, by simpa only [L.setPart_self] using hi', hsig⟩

/-! ## `wait`

The waiter's ghost value after its `unlock`: `gR g i jr sn e` (registered, out of the lock's
code). -/

/-- The waiter registered, out of the lock's code. -/
abbrev gR (L : FLock γ) (C : FCond γ) (g : γ) (i jr : Nat) (sn : Bool) (e : BitVec 32) : γ :=
  C.set (L.set g .out rnil) (.reg i jr sn e)

theorem gR_ph {g : γ} {i jr : Nat} {sn : Bool} {e : BitVec 32} :
    C.ph (gR L C g i jr sn e) = .reg i jr sn e := C.ph_set _ _

theorem gR_lph (hC : L.Fits (C.prim L) P U ok) {g : γ} {i jr : Nat} {sn : Bool}
    {e : BitVec 32} : L.ph (gR L C g i jr sn e) = .out := by rw [hC.lph, L.ph_set]

theorem gR_set {g : γ} {i jr : Nat} {sn sn' : Bool} {e : BitVec 32} :
    C.set (gR L C g i jr sn e) (.reg i jr sn' e) = gR L C g i jr sn' e := C.set_set _ _ _

/-- After the waiter took the signal: `g` out of the lock's code. -/
theorem gR_out (hC : L.Fits (C.prim L) P U ok) {g : γ} (hgx : C.ph g = .out) {i jr : Nat}
    {sn : Bool} {e : BitVec 32} : C.set (gR L C g i jr sn e) .out = L.set g .out rnil := by
  show C.set (C.set (L.set g .out rnil) (.reg i jr sn e)) .out = _
  rw [C.set_set, FCond.set_of (by rw [hC.ph_l]; exact hgx)]

theorem gR_ok (hC : L.Fits (C.prim L) P U ok) {g : γ} (hgx : C.ph g = .out) (hok : ok g)
    {i jr : Nat} {sn : Bool} {e : BitVec 32} : ok (gR L C g i jr sn e) := by
  have h0 : C.set (L.set g .out rnil) .out = L.set g .out rnil :=
    FCond.set_of (by rw [hC.ph_l]; exact hgx)
  rw [hC.ok_calm _ _ .out rfl rfl, h0]; exact (hC.ok_set _ _ _).mpr hok

theorem bits32 (e : BitVec 32) : (Packed.toBits e).setWidth 32 = e := by
  simp [Packed.toBits]

end

when_defined Io_Condition_waitInner

section
variable {γ : Type} {L : FLock γ} {C : FCond γ} {P : Proto Tgt γ}
  {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}

/-- The inner loop's invariant: `t` registered (`sn`: it loaded the next epoch write), the state
value it read, and its epoch value `e` while it has not seen the signal. -/
def inv56 (P : Proto Tgt γ) (L : FLock γ) (C : FCond γ) (t : ThreadId) (g : γ) (i jr : Nat)
    (e : BitVec 32) (D : Nat) (s : Io_Condition_waitInnerLocals) (G : ThreadId → γ) (m : Mem)
    (d : Nat) : Prop :=
  d < D ∧ m.current = t ∧
    ((s.prev_state = Packed.ofBits (1 : BitVec 32) ∧ s.epoch = e ∧
        P.inv (upd G t (gR L C g i jr false e)) m) ∨
      (s.prev_state = Packed.ofBits (0x10001 : BitVec 32) ∧ s.epoch = e ∧
        P.inv (upd G t (gR L C g i jr false e)) m) ∨
      (s.prev_state = Packed.ofBits (0x10001 : BitVec 32) ∧
        P.inv (upd G t (gR L C g i jr true e)) m))

/-- The alternatives are exactly the original existential invariant. -/
theorem inv56_iff_exists (P : Proto Tgt γ) (L : FLock γ) (C : FCond γ) (t : ThreadId)
    (g : γ) (i jr : Nat) (e : BitVec 32) (D : Nat) (s : Io_Condition_waitInnerLocals)
    (G : ThreadId → γ) (m : Mem) (d : Nat) :
    inv56 P L C t g i jr e D s G m d ↔
      d < D ∧ m.current = t ∧ ∃ (sn : Bool) (b : BitVec 32), s.prev_state = Packed.ofBits b ∧
        ((b = 1 ∧ sn = false) ∨ b = 0x10001) ∧ (sn = false → s.epoch = e) ∧
        P.inv (upd G t (gR L C g i jr sn e)) m := by
  constructor
  · rintro ⟨hd, hc, hs⟩
    refine ⟨hd, hc, ?_⟩
    rcases hs with ⟨hp, he, hi⟩ | ⟨hp, he, hi⟩ | ⟨hp, hi⟩
    · exact ⟨false, 1, hp, .inl ⟨rfl, rfl⟩, fun _ => he, hi⟩
    · exact ⟨false, 0x10001, hp, .inr rfl, fun _ => he, hi⟩
    · exact ⟨true, 0x10001, hp, .inr rfl, (by intro h; cases h), hi⟩
  · rintro ⟨hd, hc, sn, b, hp, hb, he, hi⟩
    refine ⟨hd, hc, ?_⟩
    rcases hb with ⟨rfl, rfl⟩ | rfl
    · exact .inl ⟨hp, he rfl, hi⟩
    · cases sn with
      | false => exact .inr (.inl ⟨hp, he rfl, hi⟩)
      | true => exact .inr (.inr ⟨hp, hi⟩)

/-- The inner loop ends with no signal to take (`br55`), or with `t` holding the mutex again. -/
def post56 (P : Proto Tgt γ) (L : FLock γ) (C : FCond γ) (t : ThreadId) (g : γ) (i jr : Nat)
    (e : BitVec 32) (D : Nat) (r : Io_Condition_waitInnerExit × Io_Condition_waitInnerLocals)
    (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ m.current = t ∧
  ((r.1 = .br55 ∧ r.2.epoch = e ∧ P.inv (upd G t (gR L C g i jr false e)) m) ∨
    (r.1 = .ret (.ok ()) ∧ ∃ rL, P.inv (upd G t (L.set g .holds rL)) m))

theorem loop56_body (hC : L.Fits (C.prim L) P U ok) (hcost : P.cost = none)
    (hLc : L.c = ioMutex.c) (t : ThreadId) (g : γ) (hgx : C.ph g = .out) (hok : ok g)
    (hu : 0 < (L.part g).gh.ac.frag .unmetered)
    (i jr : Nat) (e : BitVec 32) (D : Nat) (io : Io) (s : Io_Condition_waitInnerLocals)
    (G : ThreadId → γ) (m : Mem) (d : Nat) (h : inv56 P L C t g i jr e D s G m d) :
    P.WP t ((Io_Condition_waitInner.loop56 C.S.ptr io L.ptr).run s) (fun r G' m' d' =>
      if Io_Condition_waitInner.again56 r.1 then inv56 P L C t g i jr e D r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : Io_Condition_waitInnerLocals) => 0) s)
      else post56 P L C t g i jr e D r G' m' d') G m d := by
  fsym [hC.wp_tick_unmetered (t := t) (g := gR L C g i jr _ e),
    ioMutexCode.lock_wp_unmetered hC hcost (g := L.set g .out rnil)
      (hg := L.ph_set g .out rnil)
      (hok := (hC.ok_set g .out rnil).mpr hok),
    (fun {G : ThreadId → γ} {m : Mem} {d : Nat}
        {Q : BitVec 16 → (ThreadId → γ) → Mem → Nat → Prop}
        (v : Io_Condition_State) (hv : v = Packed.ofBits (0x10001 : BitVec 32)) =>
      WP.liftMem_pure (P := P) (t := t) (G := G) (m := m) (m' := m) (n := d) (Q := Q)
        (x := StateT.lift (sub false v.waiters (1 : BitVec 16)))
        (v := v.waiters - 1) (by
          have hs : sub false v.waiters (1 : BitVec 16) = pure (v.waiters - 1) := by
            rw [hv]; exact condS_subW rfl
          simp only [StateT.run_lift, hs, pure_bind]) rfl),
    (fun {G : ThreadId → γ} {m : Mem} {d : Nat}
        {Q : BitVec 16 → (ThreadId → γ) → Mem → Nat → Prop}
        (v : Io_Condition_State) (hv : v = Packed.ofBits (0x10001 : BitVec 32)) =>
      WP.liftMem_pure (P := P) (t := t) (G := G) (m := m) (m' := m) (n := d) (Q := Q)
        (x := StateT.lift (sub false v.signals (1 : BitVec 16)))
        (v := v.signals - 1) (by
          have hs : sub false v.signals (1 : BitVec 16) = pure (v.signals - 1) := by
            rw [hv]; exact condS_subS rfl
          simp only [StateT.run_lift, hs, pure_bind]) rfl),
    FCond.wp_consumeAs (α := Io_Condition_State) hC condS_dec
      (t := t) (i := i) (jr := jr) (e := e)
      (g := gR L C g i jr _ e) (hg := gR_ph) (hgo := gR_lph hC) (exp := s.prev_state)
      (new := { waiters := s.prev_state.waiters - 1, signals := s.prev_state.signals - 1 }),
    condS_eq, condS_bits, condS_take,
    condS_subW, condS_subS, condS_gtS, gR_ph, gR_lph hC, gR_set, gR_out hC hgx,
    gR_ok hC hgx hok, gR, hC.lpart, hC.lph, L.part_set, L.ph_set, L.set_set,
    C.ph_set, C.set_set, FCond.set_of hgx, inv56, post56, Io_Condition_waitInner.again56]

/-- The outer loop's invariant: `t` registered, before the signal, with its epoch value `e`. -/
def inv23 (P : Proto Tgt γ) (L : FLock γ) (C : FCond γ) (t : ThreadId) (g : γ) (i jr : Nat)
    (e : BitVec 32) (D : Nat) (s : Io_Condition_waitInnerLocals) (G : ThreadId → γ) (m : Mem)
    (d : Nat) : Prop :=
  d < D ∧ m.current = t ∧ s.epoch = e ∧ P.inv (upd G t (gR L C g i jr false e)) m

/-- The outer loop ends with `t` holding the mutex again. -/
def post23 (P : Proto Tgt γ) (L : FLock γ) (g : γ) (t : ThreadId) (D : Nat)
    (r : Io_Condition_waitInnerExit × Io_Condition_waitInnerLocals) (G : ThreadId → γ) (m : Mem)
    (d : Nat) : Prop :=
  d < D ∧ r.1 = .ret (.ok ()) ∧ m.current = t ∧ ∃ rL, P.inv (upd G t (L.set g .holds rL)) m

theorem loop23_body (hC : L.Fits (C.prim L) P U ok) (hcost : P.cost = none)
    (hLc : L.c = ioMutex.c) (t : ThreadId) (g : γ) (hgx : C.ph g = .out) (hok : ok g)
    (hu : 0 < (L.part g).gh.ac.frag .unmetered)
    (i jr : Nat) (e : BitVec 32) (D : Nat) (io : Io)
    (hlive : ∀ G₁ m₁, (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) → L.ph (G₁ t) = .away →
      P.inv G₁ m₁ → ¬ C.Signalled m₁ → P.Live t G₁ m₁)
    (s : Io_Condition_waitInnerLocals) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (h : inv23 P L C t g i jr e D s G m d) :
    P.WP t ((Io_Condition_waitInner.loop23 C.S.ptr io L.ptr true).run s) (fun r G' m' d' =>
      if Io_Condition_waitInner.again23 r.1 then inv23 P L C t g i jr e D r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : Io_Condition_waitInnerLocals) => 0) s)
      else post23 P L g t D r G' m' d') G m d := by
  have hwaitLive : ∀ G₁ m₁, C.ph (G₁ t) = C.ph (gR L C g i jr false e) →
      L.ph (G₁ t) = .away → P.inv G₁ m₁ → ¬ C.Signalled m₁ → P.Live t G₁ m₁ := by
    intro G₁ m₁ hph haway hi hnot
    exact hlive G₁ m₁ ⟨i, jr, e, by simpa only [gR_ph] using hph⟩ haway hi hnot
  fsym [hC.wp_tick_unmetered (t := t) (g := gR L C g i jr false e),
    hC.wp_projE (t := t) (G₀ := upd _ t (gR L C g i jr false e)),
    FCond.wp_waitEp (ε := BitVec 32) (w := 32) hC (t := t) (io := io)
      (e' := e) (i := i) (jr := jr) (e := e) (g := gR L C g i jr false e)
      (bits32 e) (hlive := hwaitLive),
    FCond.wp_loadEp hC (t := t) (i := i) (jr := jr) (e := e)
      (g := gR L C g i jr false e),
    FCond.wp_loadSAs (α := Io_Condition_State) hC condS_dec
      (t := t) (i := i) (jr := jr) (e := e) (g := gR L C g i jr _ e)
      (hg := gR_ph) (hgo := gR_lph hC),
    WP.loop _ _ (inv56 P L C t g i jr e d) (fun _ => 0) (post56 P L C t g i jr e d)
      (loop56_body hC hcost hLc t g hgx hok hu i jr e d io),
    condS_eq, gR_ph, gR_lph hC, gR_set, gR, hC.lpart, hC.lph, L.part_set, L.ph_set,
    C.ph_set, C.set_set, FCond.ptr_ep, inv23, post23, Io_Condition_waitInner.again23]

/-- `waitInner(…, true)` (uncancelable) by the mutex's holder, out of the condition's code: it
returns `ok`, holding the mutex again. -/
theorem waitInner_wp (hC : L.Fits (C.prim L) P U ok) (hcost : P.cost = none)
    (hLc : L.c = ioMutex.c) (t : ThreadId) (g : γ) (hgx : C.ph g = .out)
    (hgh : L.ph g = .holds) (hok : ok g)
    (hu : 0 < (L.part g).gh.ac.frag .unmetered) (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hone : ∀ u, u ≠ t → C.ph (G u) = .out)
    (hhb : ∀ j < (C.Ep.hist m).size, VClock.le (C.Ep.hist m)[j]!.clock (m.clocks[t]!) = true)
    (hent : ∀ rX, U (upd G t g) rX m → C.Inv L (upd G t (C.set g .en)) m →
      U (upd G t (C.set g .en)) rX m)
    (hlive : ∀ G₁ m₁, (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) → L.ph (G₁ t) = .away →
      P.inv G₁ m₁ → ¬ C.Signalled m₁ → P.Live t G₁ m₁)
    (hi : P.inv (upd G t g) m) :
    P.WP t (Io_Condition_waitInner C.S.ptr io L.ptr true) (fun r G' m' d' => d' < d ∧
      r = .ok () ∧ m'.current = t ∧ ∃ rL, P.inv (upd G' t (L.set g .holds rL)) m') G m d := by
  have hi0 := hC.enterEn hgx hgh hone hhb hent hi
  fsym [FCond.wp_ldEp hC (t := t) (g := C.set g .en),
    FCond.wp_regAs (α := Io_Condition_State) hC (t := t)
      (v := Packed.ofBits (1 : BitVec 32)) (g := C.set g (.ld _ _))
      (hg := C.ph_set g _) (hgh := by rw [hC.lph]; exact hgh)
      condS_bits1 ⟨_, condS_of 0⟩,
    hC.wp_projE (t := t) (G₀ := upd _ t (C.set g .en)),
    ioMutex.unlock_wp hC hcost rfl hLc t (C.set g (.reg _ _ false _))
      (by rw [hC.lph]; exact hgh)
      ((hC.ok_calm g (.reg _ _ false _) .out rfl rfl).mpr
        (by simpa only [FCond.set_of hgx] using hok)),
    WP.loop _ _ (inv23 P L C t g _ _ _ d) (fun _ => 0) (post23 P L g t d)
      (loop23_body hC hcost hLc t g hgx hok hu _ _ _ d io hlive),
    (fun {G : ThreadId → γ} {m : Mem} {d : Nat}
        {Q : Unit → (ThreadId → γ) → Mem → Nat → Prop} =>
      WP.liftMem_pure (P := P) (t := t) (G := G) (m := m) (m' := m) (n := d) (Q := Q)
        (x := StateT.lift (debug_assert
          (lt false (Packed.ofBits (0 : BitVec 32) : Io_Condition_State).waiters
            (65535 : BitVec 16)))) (v := ()) (by
          have hs : debug_assert
              (lt false (Packed.ofBits (0 : BitVec 32) : Io_Condition_State).waiters
                (65535 : BitVec 16)) = pure () := by
            rw [condS_lt0 (b := (0 : BitVec 32)) rfl]
            exact debugAssert_true
          simp only [StateT.run_lift, hs, pure_bind]) rfl),
    condS_eq, gR_ph, gR_lph hC, gR,
    hC.lpart, hC.lph, hC.ph_l, hC.set_l, hC.ok_calm, hC.ok_set,
    L.part_set, L.ph_set, L.set_set, C.ph_set, C.set_set, FCond.set_of hgx,
    FCond.ptr_ep, inv23, post23]

/-- **`Io.Condition.waitUncancelable`** of Zig 0.16.0 (`waitInner(…, true)`). -/
theorem ioCond_wait_wp_v016 (hC : L.Fits (C.prim L) P U ok)
    (hcost : P.cost = none) {p q : Ptr} (hp : p = C.S.ptr) (hq : q = L.ptr) (hLc : L.c = ioMutex.c)
    (t : ThreadId) (g : γ) (hgx : C.ph g = .out) (hgh : L.ph g = .holds) (hok : ok g)
    (hu : 0 < (L.part g).gh.ac.frag .unmetered) (io : Io)
    (G : ThreadId → γ) (m : Mem) (d : Nat) (hone : ∀ u, u ≠ t → C.ph (G u) = .out)
    (hhb : ∀ j < (C.Ep.hist m).size, VClock.le (C.Ep.hist m)[j]!.clock (m.clocks[t]!) = true)
    (hent : ∀ rX, U (upd G t g) rX m → C.Inv L (upd G t (C.set g .en)) m →
      U (upd G t (C.set g .en)) rX m)
    (hlive : ∀ G₁ m₁, (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) → L.ph (G₁ t) = .away →
      P.inv G₁ m₁ → ¬ C.Signalled m₁ → P.Live t G₁ m₁)
    (hi : P.inv (upd G t g) m) :
    P.WP t (Io_Condition_waitUncancelable p io q) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ rL, P.inv (upd G' t (L.set g .holds rL)) m') G m d := by
  subst hp hq
  fsym [waitInner_wp hC hcost hLc t g hgx hgh hok hu]

end

end_when

when_defined Io_Condition_waitUncancelable.loop22

/-! ### Zig 0.17.0: the loops of `waitInner` inlined into `waitUncancelable` -/

section
variable {γ : Type} {L : FLock γ} {C : FCond γ} {P : Proto Tgt γ}
  {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}

/-- The inner loop's invariant (as `inv56`). -/
def inv45 (P : Proto Tgt γ) (L : FLock γ) (C : FCond γ) (t : ThreadId) (g : γ) (i jr : Nat)
    (e : BitVec 32) (D : Nat) (s : Io_Condition_waitUncancelableLocals) (G : ThreadId → γ)
    (m : Mem) (d : Nat) : Prop :=
  d < D ∧ m.current = t ∧
    ((s.prev_state = Packed.ofBits (1 : BitVec 32) ∧ s.epoch = e ∧
        P.inv (upd G t (gR L C g i jr false e)) m) ∨
      (s.prev_state = Packed.ofBits (0x10001 : BitVec 32) ∧ s.epoch = e ∧
        P.inv (upd G t (gR L C g i jr false e)) m) ∨
      (s.prev_state = Packed.ofBits (0x10001 : BitVec 32) ∧
        P.inv (upd G t (gR L C g i jr true e)) m))

/-- The alternatives are exactly the original existential invariant. -/
theorem inv45_iff_exists (P : Proto Tgt γ) (L : FLock γ) (C : FCond γ) (t : ThreadId)
    (g : γ) (i jr : Nat) (e : BitVec 32) (D : Nat) (s : Io_Condition_waitUncancelableLocals)
    (G : ThreadId → γ) (m : Mem) (d : Nat) :
    inv45 P L C t g i jr e D s G m d ↔
      d < D ∧ m.current = t ∧ ∃ (sn : Bool) (b : BitVec 32), s.prev_state = Packed.ofBits b ∧
        ((b = 1 ∧ sn = false) ∨ b = 0x10001) ∧ (sn = false → s.epoch = e) ∧
        P.inv (upd G t (gR L C g i jr sn e)) m := by
  constructor
  · rintro ⟨hd, hc, hs⟩
    refine ⟨hd, hc, ?_⟩
    rcases hs with ⟨hp, he, hi⟩ | ⟨hp, he, hi⟩ | ⟨hp, hi⟩
    · exact ⟨false, 1, hp, .inl ⟨rfl, rfl⟩, fun _ => he, hi⟩
    · exact ⟨false, 0x10001, hp, .inr rfl, fun _ => he, hi⟩
    · exact ⟨true, 0x10001, hp, .inr rfl, (by intro h; cases h), hi⟩
  · rintro ⟨hd, hc, sn, b, hp, hb, he, hi⟩
    refine ⟨hd, hc, ?_⟩
    rcases hb with ⟨rfl, rfl⟩ | rfl
    · exact .inl ⟨hp, he rfl, hi⟩
    · cases sn with
      | false => exact .inr (.inl ⟨hp, he rfl, hi⟩)
      | true => exact .inr (.inr ⟨hp, hi⟩)

/-- The inner loop ends with no signal to take (`br44`), or with `t` holding the mutex again. -/
def post45 (P : Proto Tgt γ) (L : FLock γ) (C : FCond γ) (t : ThreadId) (g : γ) (i jr : Nat)
    (e : BitVec 32) (D : Nat)
    (r : Io_Condition_waitUncancelableExit × Io_Condition_waitUncancelableLocals)
    (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ m.current = t ∧
  ((r.1 = .br44 ∧ r.2.epoch = e ∧ P.inv (upd G t (gR L C g i jr false e)) m) ∨
    (r.1 = .ret ∧ ∃ rL, P.inv (upd G t (L.set g .holds rL)) m))

theorem loop45_body (hC : L.Fits (C.prim L) P U ok) (hcost : P.cost = none)
    (hLc : L.c = ioMutex.c) (t : ThreadId) (g : γ) (hgx : C.ph g = .out) (hok : ok g)
    (hu : 0 < (L.part g).gh.ac.frag .unmetered)
    (i jr : Nat) (e : BitVec 32) (D : Nat) (io : Io) (s : Io_Condition_waitUncancelableLocals)
    (G : ThreadId → γ) (m : Mem) (d : Nat) (h : inv45 P L C t g i jr e D s G m d) :
    P.WP t ((Io_Condition_waitUncancelable.loop45 C.S.ptr io L.ptr).run s) (fun r G' m' d' =>
      if Io_Condition_waitUncancelable.again45 r.1 then inv45 P L C t g i jr e D r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧
          (fun _ => 0) r.2 < (fun (_ : Io_Condition_waitUncancelableLocals) => 0) s)
      else post45 P L C t g i jr e D r G' m' d') G m d := by
  fsym [hC.wp_tick_unmetered (t := t) (g := gR L C g i jr _ e),
    ioMutexCode.lock_wp_unmetered hC hcost (g := L.set g .out rnil)
      (hg := L.ph_set g .out rnil)
      (hok := (hC.ok_set g .out rnil).mpr hok),
    (fun {G : ThreadId → γ} {m : Mem} {d : Nat}
        {Q : BitVec 16 → (ThreadId → γ) → Mem → Nat → Prop}
        (v : Io_Condition_State) (hv : v = Packed.ofBits (0x10001 : BitVec 32)) =>
      WP.liftMem_pure (P := P) (t := t) (G := G) (m := m) (m' := m) (n := d) (Q := Q)
        (x := StateT.lift (sub false v.waiters (1 : BitVec 16)))
        (v := v.waiters - 1) (by
          have hs : sub false v.waiters (1 : BitVec 16) = pure (v.waiters - 1) := by
            rw [hv]; exact condS_subW rfl
          simp only [StateT.run_lift, hs, pure_bind]) rfl),
    (fun {G : ThreadId → γ} {m : Mem} {d : Nat}
        {Q : BitVec 16 → (ThreadId → γ) → Mem → Nat → Prop}
        (v : Io_Condition_State) (hv : v = Packed.ofBits (0x10001 : BitVec 32)) =>
      WP.liftMem_pure (P := P) (t := t) (G := G) (m := m) (m' := m) (n := d) (Q := Q)
        (x := StateT.lift (sub false v.signals (1 : BitVec 16)))
        (v := v.signals - 1) (by
          have hs : sub false v.signals (1 : BitVec 16) = pure (v.signals - 1) := by
            rw [hv]; exact condS_subS rfl
          simp only [StateT.run_lift, hs, pure_bind]) rfl),
    FCond.wp_consumeAs (α := Io_Condition_State) hC condS_dec
      (t := t) (i := i) (jr := jr) (e := e)
      (g := gR L C g i jr _ e) (hg := gR_ph) (hgo := gR_lph hC) (exp := s.prev_state)
      (new := { waiters := s.prev_state.waiters - 1, signals := s.prev_state.signals - 1 }),
    condS_eq, condS_bits, condS_take,
    condS_subW, condS_subS, condS_gtS, gR_ph, gR_lph hC, gR_set, gR_out hC hgx,
    gR_ok hC hgx hok, gR, hC.lpart, hC.lph, L.part_set, L.ph_set, L.set_set,
    C.ph_set, C.set_set, FCond.set_of hgx, inv45, post45, Io_Condition_waitUncancelable.again45]

/-- The outer loop's invariant (as `inv23`). -/
def inv22 (P : Proto Tgt γ) (L : FLock γ) (C : FCond γ) (t : ThreadId) (g : γ) (i jr : Nat)
    (e : BitVec 32) (D : Nat) (s : Io_Condition_waitUncancelableLocals) (G : ThreadId → γ)
    (m : Mem) (d : Nat) : Prop :=
  d < D ∧ m.current = t ∧ s.epoch = e ∧ P.inv (upd G t (gR L C g i jr false e)) m

/-- The outer loop ends with `t` holding the mutex again. -/
def post22 (P : Proto Tgt γ) (L : FLock γ) (g : γ) (t : ThreadId) (D : Nat)
    (r : Io_Condition_waitUncancelableExit × Io_Condition_waitUncancelableLocals)
    (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ r.1 = .ret ∧ m.current = t ∧ ∃ rL, P.inv (upd G t (L.set g .holds rL)) m

theorem loop22_body (hC : L.Fits (C.prim L) P U ok) (hcost : P.cost = none)
    (hLc : L.c = ioMutex.c) (t : ThreadId) (g : γ) (hgx : C.ph g = .out) (hok : ok g)
    (hu : 0 < (L.part g).gh.ac.frag .unmetered)
    (i jr : Nat) (e : BitVec 32) (D : Nat) (io : Io)
    (hlive : ∀ G₁ m₁, (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) → L.ph (G₁ t) = .away →
      P.inv G₁ m₁ → ¬ C.Signalled m₁ → P.Live t G₁ m₁)
    (s : Io_Condition_waitUncancelableLocals) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (h : inv22 P L C t g i jr e D s G m d) :
    P.WP t ((Io_Condition_waitUncancelable.loop22 C.S.ptr io L.ptr).run s) (fun r G' m' d' =>
      if Io_Condition_waitUncancelable.again22 r.1 then inv22 P L C t g i jr e D r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧
          (fun _ => 0) r.2 < (fun (_ : Io_Condition_waitUncancelableLocals) => 0) s)
      else post22 P L g t D r G' m' d') G m d := by
  have hwaitLive : ∀ G₁ m₁, C.ph (G₁ t) = C.ph (gR L C g i jr false e) →
      L.ph (G₁ t) = .away → P.inv G₁ m₁ → ¬ C.Signalled m₁ → P.Live t G₁ m₁ := by
    intro G₁ m₁ hph haway hi hnot
    exact hlive G₁ m₁ ⟨i, jr, e, by simpa only [gR_ph] using hph⟩ haway hi hnot
  fsym [hC.wp_tick_unmetered (t := t) (g := gR L C g i jr false e),
    hC.wp_projE (t := t) (G₀ := upd _ t (gR L C g i jr false e)),
    FCond.wp_waitEp (ε := BitVec 32) (w := 32) hC (t := t) (io := io)
      (e' := e) (i := i) (jr := jr) (e := e) (g := gR L C g i jr false e)
      (bits32 e) (hlive := hwaitLive),
    FCond.wp_loadEp hC (t := t) (i := i) (jr := jr) (e := e)
      (g := gR L C g i jr false e),
    FCond.wp_loadSAs (α := Io_Condition_State) hC condS_dec
      (t := t) (i := i) (jr := jr) (e := e) (g := gR L C g i jr _ e)
      (hg := gR_ph) (hgo := gR_lph hC),
    WP.loop _ _ (inv45 P L C t g i jr e d) (fun _ => 0) (post45 P L C t g i jr e d)
      (loop45_body hC hcost hLc t g hgx hok hu i jr e d io),
    condS_eq, gR_ph, gR_lph hC, gR_set, gR, hC.lpart, hC.lph, L.part_set, L.ph_set,
    C.ph_set, C.set_set, FCond.ptr_ep, inv22, post22, Io_Condition_waitUncancelable.again22]

/-- **`Io.Condition.waitUncancelable`** of Zig 0.17.0 (the loops inlined). -/
theorem ioCond_wait_wp_v017 (hC : L.Fits (C.prim L) P U ok)
    (hcost : P.cost = none) {p q : Ptr} (hp : p = C.S.ptr) (hq : q = L.ptr) (hLc : L.c = ioMutex.c)
    (t : ThreadId) (g : γ) (hgx : C.ph g = .out) (hgh : L.ph g = .holds) (hok : ok g)
    (hu : 0 < (L.part g).gh.ac.frag .unmetered) (io : Io)
    (G : ThreadId → γ) (m : Mem) (d : Nat) (hone : ∀ u, u ≠ t → C.ph (G u) = .out)
    (hhb : ∀ j < (C.Ep.hist m).size, VClock.le (C.Ep.hist m)[j]!.clock (m.clocks[t]!) = true)
    (hent : ∀ rX, U (upd G t g) rX m → C.Inv L (upd G t (C.set g .en)) m →
      U (upd G t (C.set g .en)) rX m)
    (hlive : ∀ G₁ m₁, (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) → L.ph (G₁ t) = .away →
      P.inv G₁ m₁ → ¬ C.Signalled m₁ → P.Live t G₁ m₁)
    (hi : P.inv (upd G t g) m) :
    P.WP t (Io_Condition_waitUncancelable p io q) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ rL, P.inv (upd G' t (L.set g .holds rL)) m') G m d := by
  subst hp hq
  have hi0 := hC.enterEn hgx hgh hone hhb hent hi
  fsym [FCond.wp_ldEp hC (t := t) (g := C.set g .en),
    FCond.wp_regAs (α := Io_Condition_State) hC (t := t)
      (v := Packed.ofBits (1 : BitVec 32)) (g := C.set g (.ld _ _))
      (hg := C.ph_set g _) (hgh := by rw [hC.lph]; exact hgh)
      condS_bits1 ⟨_, condS_of 0⟩,
    hC.wp_projE (t := t) (G₀ := upd _ t (C.set g .en)),
    ioMutex.unlock_wp hC hcost rfl hLc t (C.set g (.reg _ _ false _))
      (by rw [hC.lph]; exact hgh)
      ((hC.ok_calm g (.reg _ _ false _) .out rfl rfl).mpr
        (by simpa only [FCond.set_of hgx] using hok)),
    WP.loop _ _ (inv22 P L C t g _ _ _ d) (fun _ => 0) (post22 P L g t d)
      (loop22_body hC hcost hLc t g hgx hok hu _ _ _ d io hlive),
    (fun {G : ThreadId → γ} {m : Mem} {d : Nat}
        {Q : Unit → (ThreadId → γ) → Mem → Nat → Prop} =>
      WP.liftMem_pure (P := P) (t := t) (G := G) (m := m) (m' := m) (n := d) (Q := Q)
        (x := StateT.lift (debug_assert
          (lt false (Packed.ofBits (0 : BitVec 32) : Io_Condition_State).waiters
            (65535 : BitVec 16)))) (v := ()) (by
          have hs : debug_assert
              (lt false (Packed.ofBits (0 : BitVec 32) : Io_Condition_State).waiters
                (65535 : BitVec 16)) = pure () := by
            rw [condS_lt0 (b := (0 : BitVec 32)) rfl]
            exact debugAssert_true
          simp only [StateT.run_lift, hs, pure_bind]) rfl),
    condS_eq, gR_ph, gR_lph hC, gR,
    hC.lpart, hC.lph, hC.ph_l, hC.set_l, hC.ok_calm, hC.ok_set,
    L.part_set, L.ph_set, L.set_set, C.ph_set, C.set_set, FCond.set_of hgx,
    FCond.ptr_ep, inv22, post22]

end

end_when

section
variable {γ : Type} {L : FLock γ} {C : FCond γ} {P : Proto Tgt γ}
  {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}

/-- **`Io.Condition.waitUncancelable`** of this translation. -/
theorem ioCond_wait_wp_unmetered (hC : L.Fits (C.prim L) P U ok)
    (hcost : P.cost = none) {p q : Ptr} (hp : p = C.S.ptr) (hq : q = L.ptr) (hLc : L.c = ioMutex.c)
    (t : ThreadId) (g : γ) (hgx : C.ph g = .out) (hgh : L.ph g = .holds) (hok : ok g) (io : Io)
    (G : ThreadId → γ) (m : Mem) (d : Nat) (hone : ∀ u, u ≠ t → C.ph (G u) = .out)
    (hhb : ∀ j < (C.Ep.hist m).size, VClock.le (C.Ep.hist m)[j]!.clock (m.clocks[t]!) = true)
    (hent : ∀ rX, U (upd G t g) rX m → C.Inv L (upd G t (C.set g .en)) m →
      U (upd G t (C.set g .en)) rX m)
    (hlive : ∀ G₁ m₁, (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) → L.ph (G₁ t) = .away →
      P.inv G₁ m₁ → ¬ C.Signalled m₁ → P.Live t G₁ m₁)
    (hu : 0 < (L.part g).gh.ac.frag .unmetered) (hi : P.inv (upd G t g) m) (_hc : m.current = t) :
    P.WP t (Io_Condition_waitUncancelable p io q) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ rL, P.inv (upd G' t (L.set g .holds rL)) m') G m d := by
  first
    | exact ioCond_wait_wp_v016 hC hcost hp hq hLc t g hgx hgh hok hu io G m d hone hhb hent
        hlive hi
    | exact ioCond_wait_wp_v017 hC hcost hp hq hLc t g hgx hgh hok hu io G m d hone hhb hent
        hlive hi

/-- The existing Plain wait follows from its unmetered fragment; it supplies no extra
assumption about stack budgets to the actual condition or mutex code. -/
theorem ioCond_wait_wp (hC : L.Fits (C.prim L) P U ok)
    (hcost : P.cost = none) {p q : Ptr} (hp : p = C.S.ptr) (hq : q = L.ptr) (hLc : L.c = ioMutex.c)
    (t : ThreadId) (g : γ) (hgx : C.ph g = .out) (hgh : L.ph g = .holds) (hok : ok g) (io : Io)
    (G : ThreadId → γ) (m : Mem) (d : Nat) (hone : ∀ u, u ≠ t → C.ph (G u) = .out)
    (hhb : ∀ j < (C.Ep.hist m).size, VClock.le (C.Ep.hist m)[j]!.clock (m.clocks[t]!) = true)
    (hent : ∀ rX, U (upd G t g) rX m → C.Inv L (upd G t (C.set g .en)) m →
      U (upd G t (C.set g .en)) rX m)
    (hlive : ∀ G₁ m₁, (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) → L.ph (G₁ t) = .away →
      P.inv G₁ m₁ → ¬ C.Signalled m₁ → P.Live t G₁ m₁)
    (hplain : (L.part g).Plain) (hi : P.inv (upd G t g) m) (hc : m.current = t) :
    P.WP t (Io_Condition_waitUncancelable p io q) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ rL, P.inv (upd G' t (L.set g .holds rL)) m') G m d :=
  ioCond_wait_wp_unmetered hC hcost hp hq hLc t g hgx hgh hok io G m d hone hhb hent
    hlive hplain.2 hi hc

/-- The actual unmetered wait preserves its exact caller part, with the protected resource
returned separately after the re-lock. -/
theorem ioCond_wait_wp_resource (hC : L.Fits (C.prim L) P U ok)
    (hcost : P.cost = none) {p q : Ptr} (hp : p = C.S.ptr) (hq : q = L.ptr) (hLc : L.c = ioMutex.c)
    (t : ThreadId) (g : γ) (hgx : C.ph g = .out) (hgh : L.ph g = .holds) (hok : ok g) (io : Io)
    (G : ThreadId → γ) (m : Mem) (d : Nat) (hone : ∀ u, u ≠ t → C.ph (G u) = .out)
    (hhb : ∀ j < (C.Ep.hist m).size, VClock.le (C.Ep.hist m)[j]!.clock (m.clocks[t]!) = true)
    (hent : ∀ rX, U (upd G t g) rX m → C.Inv L (upd G t (C.set g .en)) m →
      U (upd G t (C.set g .en)) rX m)
    (hlive : ∀ G₁ m₁, (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) → L.ph (G₁ t) = .away →
      P.inv G₁ m₁ → ¬ C.Signalled m₁ → P.Live t G₁ m₁)
    (hu : payUnmetered t (L.part g)) (hi : P.inv (upd G t g) m) (hc : m.current = t) :
    P.WP t (Io_Condition_waitUncancelable p io q) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ r' rL, keepPart t (L.part g) r' ∧
        P.inv (upd G' t (L.set (L.setPart g r') .holds rL)) m') G m d := by
  refine WP.mono ?_ (ioCond_wait_wp_unmetered hC hcost hp hq hLc t g hgx hgh hok
    io G m d hone hhb hent hlive hu hi hc)
  rintro _ G' m' d' ⟨hd, hcur, rL, hi'⟩
  exact ⟨hd, hcur, L.part g, rL, rfl, by simpa only [L.setPart_self] using hi'⟩

end

/-- `Io.Condition` of this program as a condition, with the program's `Io.Mutex`. -/
def ioCond : CondImpl Tgt where
  wait := Io_Condition_waitUncancelable
  signal := Io_Condition_signal
  c := ioMutex.c
  wait_pre := payUnmetered
  wait_post := keepPart
  wait_plain_pre _ _ := payUnmetered_plain
  wait_plain_post _ _ _ _ hr := hr
  signal_pre := payUnmetered
  signal_during := keepPart
  signal_post := keepPart
  signal_plain_pre _ _ := payUnmetered_plain
  signal_plain_post _ _ _ _ hr := hr
  wait_wp_resource := ioCond_wait_wp_resource
  signal_wp_resource := ioCond_signal_wp_resource

end Sync
