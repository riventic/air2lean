import Proofs.Sync.IoMutex
import ZigLean.Sep.Full.Cond
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
  d < D ∧ m.current = t ∧ P.inv (upd G t g) m ∧ ∃ b : BitVec 32, s.prev_state = Packed.ofBits b ∧
    (b = 0 ∨ b = 1 ∨ b = 0x10001) ∧
    (b ≠ 1 → ∀ u i jr sn e, C.ph (G u) = .reg i jr sn e → C.Signalled m)

/-- `signal`'s loop ends with `t` out and a registered waiter signalled. -/
def sigPost (P : Proto Tgt γ) (C : FCond γ) (t : ThreadId) (g : γ) (D : Nat)
    (r : Io_Condition_signalExit × Io_Condition_signalLocals) (G : ThreadId → γ) (m : Mem)
    (d : Nat) : Prop :=
  (r.1 = .ret ∨ r.1 = .br10) ∧ d < D ∧ m.current = t ∧ P.inv (upd G t g) m ∧
    ∀ u i jr sn e, C.ph (G u) = .reg i jr sn e → C.Signalled m

theorem sig_body (hC : C.Fits L P U ok) (hP : L.FitsOn P U ok) (hcost : P.cost = none)
    (t : ThreadId) (g : γ) (hgx : C.ph g = .out) (hgo : L.ph g = .out) (hsx : C.sx g) (D : Nat)
    (io : Io)
    (hseen : ∀ G₁ rX m₁, G₁ t = g → U G₁ rX m₁ → ∀ u i jr sn e, C.ph (G₁ u) = .reg i jr sn e →
      VClock.le (C.S.hist m₁)[jr]!.clock (m₁.clocks[t]!) = true)
    (s : Io_Condition_signalLocals) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (h : sigInv P C t g D s G m d) :
    P.WP t ((Io_Condition_signal.loop11 C.S.ptr io).run s) (fun r G' m' d' =>
      if Io_Condition_signal.again11 r.1 then sigInv P C t g D r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : Io_Condition_signalLocals) => 0) s)
      else sigPost P C t g D r G' m' d') G m d := by
  obtain ⟨ps⟩ := s
  obtain ⟨hD, hc, hi, b, hps, hb, hsg⟩ := h
  simp only at hps
  unfold Io_Condition_signal.loop11
  simp only [StateT.run_bind, StateT.run_get, pure_bind, bind_assoc]
  refine WP.bind ?_
  by_cases hb1 : b = 1
  · have hg : gt false ps.waiters ps.signals = true := by rw [hps, condS_gtWS hb]; simp [hb1]
    simp only [hg, ↓reduceIte]
    simp only [StateT.run_bind, StateT.run_get]
    simp only [pure_bind]
    refine WP.bind (WP.callRC_ok (by rw [hps]; exact condS_add1 hb1) ?_)
    refine WP.bind (FCond.wp_signalAs hC hP condS_dec (by rw [hps, condS_bits hb, hb1])
      (by rw [hps]; exact condS_sig hb1) hgx hgo hsx hseen hi
      fun k hk G₁ m₁ hc₁ => ⟨fun hi₁ => ?_, fun b' r hd hb' hs' hi₁ => ?_⟩)
    · -- success: `epoch += 1`, the wake
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
      refine WP.bind (WP.bind (WP.callMC_ptrProject (hC.projE hP hi₁) ?_))
      dsimp only
      rw [FCond.ptr_ep]
      refine WP.bind (FCond.wp_bump hC hP (C.ph_set _ _) (by rw [hC.lph]; exact hgo) hi₁
        fun k₂ hk₂ G₂ m₂ o hc₂ hi₂ => ?_)
      refine WP.bind (WP.callMC_ptrProject (hC.projE hP hi₂) ?_)
      dsimp only
      rw [FCond.ptr_ep]
      refine WP.bind (FCond.wp_wakeEp hC hP (by decide) (C.ph_set _ _) hi₂
        fun k₃ hk₃ G₃ m₃ hc₃ hsg₃ hi₃ => ?_)
      rw [C.set_set, C.set_set, FCond.set_of hgx] at hi₃
      repeat (first
        | exact ⟨.inl rfl, by omega, hc₃, hi₃, hsg₃⟩
        | refine WP.pure' ?_
        | simp only [StateT.run_pure, pure_bind, Io_Condition_signal.again11, Bool.false_eq_true,
            ↓reduceIte])
      done
    · -- failure: the read value
      obtain rfl := condS_eq hd
      simp only [Option.isSome_some, ↓reduceIte, StateT.run_bind]
      refine WP.bind (WP.bind (WP.callRC_ok (x := optPayload (some (Packed.ofBits b'))) rfl ?_))
      repeat (first
        | exact ⟨⟨by omega, hc₁, hi₁, b', rfl, hb', hs'⟩, .inl (by omega)⟩
        | refine WP.pure' ?_
        | simp only [StateT.run_pure, StateT.run_modify, StateT.run_bind, pure_bind,
            Io_Condition_signal.again11, ↓reduceIte])
      done
  · have hg : gt false ps.waiters ps.signals = false := by
      rw [hps, condS_gtWS hb]; simpa using hb1
    simp only [hg, Bool.false_eq_true, ↓reduceIte]
    repeat (first
      | exact ⟨.inr rfl, hD, hc, hi, hsg hb1⟩
      | refine WP.pure' ?_
      | simp only [StateT.run_pure, pure_bind, Io_Condition_signal.again11, Bool.false_eq_true,
          ↓reduceIte])
    done

/-- **`Io.Condition.signal`** by a thread out of the condition's and the lock's code that may
signal, after every registration (`hseen`). -/
theorem ioCond_signal_wp (hC : C.Fits L P U ok) (hP : L.FitsOn P U ok) (hcost : P.cost = none)
    {p : Ptr} (hp : p = C.S.ptr) (t : ThreadId) (g : γ) (hgx : C.ph g = .out)
    (hgo : L.ph g = .out) (hsx : C.sx g) (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hseen : ∀ G₁ rX m₁, G₁ t = g → U G₁ rX m₁ → ∀ u i jr sn e, C.ph (G₁ u) = .reg i jr sn e →
      VClock.le (C.S.hist m₁)[jr]!.clock (m₁.clocks[t]!) = true)
    (hi : P.inv (upd G t g) m) :
    P.WP t (Io_Condition_signal p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      P.inv (upd G' t g) m' ∧ ∀ u i jr sn e, C.ph (G' u) = .reg i jr sn e → C.Signalled m')
      G m d := by
  subst hp
  unfold Io_Condition_signal
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  refine WP.bind (FCond.wp_sloadAs hC hP condS_dec hgo hseen hi
    fun k hk G₁ m₁ b r hc₁ hd hb hsg hi₁ => ?_)
  obtain rfl := condS_eq hd
  simp only [StateT.run_modify, pure_bind]
  refine WP.bind (WP.mono ?_ (WP.loop _ _ (sigInv P C t g d) (fun _ => 0) (sigPost P C t g d)
    (sig_body hC hP hcost t g hgx hgo hsx d io hseen) _ G₁ m₁ k
    ⟨by omega, hc₁, hi₁, b, rfl, hb, hsg⟩))
  rintro ⟨e, s'⟩ G₂ m₂ d₂ ⟨he, hd₂, hc₂, hi₂, hsg₂⟩
  rcases he with rfl | rfl <;>
  · simp only [StateT.run_pure]
    exact WP.pure' (WP.pure' ⟨hd₂, hc₂, hi₂, hsg₂⟩)

/-! ## `wait`

The waiter's ghost value after its `unlock`: `gR g i jr sn e` (registered, out of the lock's
code). -/

/-- The waiter registered, out of the lock's code. -/
abbrev gR (L : FLock γ) (C : FCond γ) (g : γ) (i jr : Nat) (sn : Bool) (e : BitVec 32) : γ :=
  C.set (L.set g .out rnil) (.reg i jr sn e)

theorem gR_ph {g : γ} {i jr : Nat} {sn : Bool} {e : BitVec 32} :
    C.ph (gR L C g i jr sn e) = .reg i jr sn e := C.ph_set _ _

theorem gR_lph (hC : C.Fits L P U ok) {g : γ} {i jr : Nat} {sn : Bool} {e : BitVec 32} :
    L.ph (gR L C g i jr sn e) = .out := by rw [hC.lph, L.ph_set]

theorem gR_set {g : γ} {i jr : Nat} {sn sn' : Bool} {e : BitVec 32} :
    C.set (gR L C g i jr sn e) (.reg i jr sn' e) = gR L C g i jr sn' e := C.set_set _ _ _

/-- After the waiter took the signal: `g` out of the lock's code. -/
theorem gR_out (hC : C.Fits L P U ok) {g : γ} (hgx : C.ph g = .out) {i jr : Nat} {sn : Bool}
    {e : BitVec 32} : C.set (gR L C g i jr sn e) .out = L.set g .out rnil := by
  show C.set (C.set (L.set g .out rnil) (.reg i jr sn e)) .out = _
  rw [C.set_set, FCond.set_of (by rw [hC.ph_l]; exact hgx)]

theorem gR_ok (hC : C.Fits L P U ok) {g : γ} (hgx : C.ph g = .out) (hP : L.FitsOn P U ok)
    (hok : ok g) {i jr : Nat} {sn : Bool} {e : BitVec 32} : ok (gR L C g i jr sn e) := by
  have h0 : C.set (L.set g .out rnil) .out = L.set g .out rnil :=
    FCond.set_of (by rw [hC.ph_l]; exact hgx)
  rw [hC.ok_c _ _ .out rfl rfl, h0]; exact (hP.ok_set _ _ _).mpr hok

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
  d < D ∧ m.current = t ∧ ∃ (sn : Bool) (b : BitVec 32), s.prev_state = Packed.ofBits b ∧
    ((b = 1 ∧ sn = false) ∨ b = 0x10001) ∧ (sn = false → s.epoch = e) ∧
    P.inv (upd G t (gR L C g i jr sn e)) m

/-- The inner loop ends with no signal to take (`br55`), or with `t` holding the mutex again. -/
def post56 (P : Proto Tgt γ) (L : FLock γ) (C : FCond γ) (t : ThreadId) (g : γ) (i jr : Nat)
    (e : BitVec 32) (D : Nat) (r : Io_Condition_waitInnerExit × Io_Condition_waitInnerLocals)
    (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ m.current = t ∧
  ((r.1 = .br55 ∧ r.2.epoch = e ∧ P.inv (upd G t (gR L C g i jr false e)) m) ∨
    (r.1 = .ret (.ok ()) ∧ ∃ rL, P.inv (upd G t (L.set g .holds rL)) m))

theorem loop56_body (hC : C.Fits L P U ok) (hP : L.FitsOn P U ok) (hcost : P.cost = none)
    (hLc : L.c = ioMutex.c) (t : ThreadId) (g : γ) (hgx : C.ph g = .out) (hok : ok g)
    (i jr : Nat) (e : BitVec 32) (D : Nat) (io : Io) (s : Io_Condition_waitInnerLocals)
    (G : ThreadId → γ) (m : Mem) (d : Nat) (h : inv56 P L C t g i jr e D s G m d) :
    P.WP t ((Io_Condition_waitInner.loop56 C.S.ptr io L.ptr).run s) (fun r G' m' d' =>
      if Io_Condition_waitInner.again56 r.1 then inv56 P L C t g i jr e D r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : Io_Condition_waitInnerLocals) => 0) s)
      else post56 P L C t g i jr e D r G' m' d') G m d := by
  obtain ⟨hD, hc, sn, b, hps, hb, hep, hi⟩ := h
  unfold Io_Condition_waitInner.loop56
  simp only [StateT.run_bind, StateT.run_get, pure_bind, bind_assoc]
  refine WP.bind ?_
  by_cases hb2 : b = 0x10001
  · have hg : gt false s.prev_state.signals 0 = true := by
      rw [hps, condS_gtS (by rcases hb with ⟨h, -⟩ | h <;> simp [h])]; simp [hb2]
    simp only [hg, ↓reduceIte]
    simp only [StateT.run_bind, StateT.run_get]
    simp only [pure_bind]
    refine WP.bind (WP.callRC_ok (by rw [hps]; exact condS_subW hb2) ?_)
    refine WP.bind (WP.callRC_ok (by rw [hps]; exact condS_subS hb2) ?_)
    dsimp only
    refine WP.bind (FCond.wp_consumeAs hC hP condS_dec (condS_take hb2) gR_ph
      (gR_lph hC) hi fun k hk G₁ m₁ hc₁ => ⟨fun hi₁ => ?_, fun b' r hd hb' hi₁ => ?_⟩)
    · -- the signal taken: `lock`
      rw [gR_out hC hgx] at hi₁
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
      refine WP.bind (WP.bind (WP.callC (WP.mono ?_ (ioMutex.lock_wp hP hcost rfl hLc t _
        (L.ph_set _ _ _) ((hP.ok_set _ _ _).mpr hok) io G₁ m₁ k hi₁))))
      rintro _ G₂ m₂ d₂ ⟨hd₂, hc₂, rL, hi₂⟩
      rw [L.set_set] at hi₂
      repeat (first
        | exact ⟨by omega, hc₂, .inr ⟨rfl, rL, hi₂⟩⟩
        | refine WP.pure' ?_
        | simp only [StateT.run_pure, pure_bind, Io_Condition_waitInner.again56,
            Bool.false_eq_true, ↓reduceIte])
      done
    · -- the `cmpxchg` failed: the read value
      obtain rfl := condS_eq hd
      simp only [Option.isSome_some, ↓reduceIte, StateT.run_bind]
      refine WP.bind (WP.bind (WP.callRC_ok (x := optPayload (some (Packed.ofBits b'))) rfl ?_))
      repeat (first
        | exact ⟨⟨by omega, hc₁, sn, b', rfl, hb', hep, hi₁⟩, .inl (by omega)⟩
        | refine WP.pure' ?_
        | simp only [StateT.run_pure, StateT.run_modify, StateT.run_bind, pure_bind,
            Io_Condition_waitInner.again56, ↓reduceIte])
      done
  · -- no signal: `(1, 0)`, before `t` saw the next epoch write
    obtain ⟨rfl, rfl⟩ : b = 1 ∧ sn = false := by
      rcases hb with h | h
      · exact h
      · exact absurd h hb2
    have hg : gt false s.prev_state.signals 0 = false := by
      rw [hps, condS_gtS (.inl rfl)]; decide
    simp only [hg, Bool.false_eq_true, ↓reduceIte]
    repeat (first
      | exact ⟨hD, hc, .inl ⟨rfl, hep rfl, hi⟩⟩
      | refine WP.pure' ?_
      | simp only [StateT.run_pure, pure_bind, Io_Condition_waitInner.again56, Bool.false_eq_true,
          ↓reduceIte])
    done

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

theorem loop23_body (hC : C.Fits L P U ok) (hP : L.FitsOn P U ok) (hcost : P.cost = none)
    (hLc : L.c = ioMutex.c) (t : ThreadId) (g : γ) (hgx : C.ph g = .out) (hok : ok g)
    (i jr : Nat) (e : BitVec 32) (D : Nat) (io : Io)
    (hlive : ∀ G₁ m₁, (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) → L.ph (G₁ t) = .away →
      P.inv G₁ m₁ → ¬ C.Signalled m₁ → P.Live t G₁ m₁)
    (s : Io_Condition_waitInnerLocals) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (h : inv23 P L C t g i jr e D s G m d) :
    P.WP t ((Io_Condition_waitInner.loop23 C.S.ptr io L.ptr true).run s) (fun r G' m' d' =>
      if Io_Condition_waitInner.again23 r.1 then inv23 P L C t g i jr e D r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : Io_Condition_waitInnerLocals) => 0) s)
      else post23 P L g t D r G' m' d') G m d := by
  obtain ⟨hD, hc, hep, hi⟩ := h
  unfold Io_Condition_waitInner.loop23
  simp only [StateT.run_bind, StateT.run_get, pure_bind, bind_assoc, ↓reduceIte]
  refine WP.bind (WP.callMC_ptrProject (hC.projE hP hi) ?_)
  dsimp only
  rw [FCond.ptr_ep, hep]
  refine WP.bind (FCond.wp_waitEp hC hP (bits32 e) gR_ph (gR_lph hC) hi
    (fun G₁ m₁ h1 h2 h3 h4 => hlive G₁ m₁ ⟨i, jr, e, by rw [h1, gR_ph]⟩ h2 h3 h4)
    fun k hk G₁ m₁ hc₁ hi₁ => ?_)
  dsimp only
  refine WP.bind (WP.callMC_ptrProject (hC.projE hP hi₁) ?_)
  dsimp only
  rw [FCond.ptr_ep]
  refine WP.bind (FCond.wp_loadEp hC hP gR_ph (gR_lph hC) hi₁
    fun k₂ hk₂ G₂ m₂ v hc₂ hcase => ?_)
  -- the epoch read: `t`'s own value, or the next write
  obtain ⟨sn, hsn, hi₂⟩ : ∃ sn : Bool, (sn = false → v = e) ∧
      P.inv (upd G₂ t (gR L C g i jr sn e)) m₂ := by
    rcases hcase with ⟨rfl, h⟩ | ⟨rfl, h⟩
    · exact ⟨false, fun _ => rfl, h⟩
    · exact ⟨true, nofun, by rw [gR_set] at h; exact h⟩
  simp only [StateT.run_modify, pure_bind]
  refine WP.bind (FCond.wp_loadSAs hC hP condS_dec gR_ph (gR_lph hC) hi₂
    fun k₃ hk₃ G₃ m₃ b r hc₃ hd hb hi₃ => ?_)
  obtain rfl := condS_eq hd
  refine WP.bind (WP.mono ?_ (WP.loop _ _ (inv56 P L C t g i jr e d) (fun _ => 0)
    (post56 P L C t g i jr e d) (loop56_body hC hP hcost hLc t g hgx hok i jr e d io) _ G₃ m₃ k₃
    ⟨by omega, hc₃, sn, b, rfl, hb, fun h' => hsn h', hi₃⟩))
  rintro ⟨x, s'⟩ G₄ m₄ d₄ ⟨hd₄, hc₄, ⟨rfl, hep₄, hi₄⟩ | ⟨rfl, rL, hi₄⟩⟩
  · repeat (first
      | exact ⟨⟨by omega, hc₄, hep₄, hi₄⟩, .inl (by omega)⟩
      | refine WP.pure' ?_
      | simp only [StateT.run_pure, pure_bind, StateT.run_bind, isNonErr, ↓reduceIte,
          Io_Condition_waitInner.again23])
    done
  · repeat (first
      | exact ⟨by omega, rfl, hc₄, rL, hi₄⟩
      | refine WP.pure' ?_
      | simp only [StateT.run_pure, pure_bind, StateT.run_bind, Io_Condition_waitInner.again23,
          Bool.false_eq_true, ↓reduceIte])
    done

/-- `waitInner(…, true)` (uncancelable) by the mutex's holder, out of the condition's code: it
returns `ok`, holding the mutex again. -/
theorem waitInner_wp (hC : C.Fits L P U ok) (hP : L.FitsOn P U ok) (hcost : P.cost = none)
    (hLc : L.c = ioMutex.c) (t : ThreadId) (g : γ) (hgx : C.ph g = .out)
    (hgh : L.ph g = .holds) (hok : ok g) (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hone : ∀ u, u ≠ t → C.ph (G u) = .out)
    (hhb : ∀ j < (C.Ep.hist m).size, VClock.le (C.Ep.hist m)[j]!.clock (m.clocks[t]!) = true)
    (hent : ∀ rX, U (upd G t g) rX m → C.Inv L (upd G t (C.set g .en)) m →
      U (upd G t (C.set g .en)) rX m)
    (hlive : ∀ G₁ m₁, (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) → L.ph (G₁ t) = .away →
      P.inv G₁ m₁ → ¬ C.Signalled m₁ → P.Live t G₁ m₁)
    (hi : P.inv (upd G t g) m) :
    P.WP t (Io_Condition_waitInner C.S.ptr io L.ptr true) (fun r G' m' d' => d' < d ∧
      r = .ok () ∧ m'.current = t ∧ ∃ rL, P.inv (upd G' t (L.set g .holds rL)) m') G m d := by
  have hi0 := hC.enter hP hgx hgh hone hhb hent hi
  have hgh0 : L.ph (C.set g .en) = .holds := by rw [hC.lph]; exact hgh
  unfold Io_Condition_waitInner
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, StateT.run_pure, pure_bind]
  refine WP.bind (WP.callMC_ptrProject (hC.projE hP hi0) ?_)
  dsimp only
  rw [FCond.ptr_ep]
  refine WP.bind (WP.bind (FCond.wp_ldEp hC hP (C.ph_set _ _) hgh0 hi0
    fun k₁ hk₁ G₁ m₁ v i hc₁ hi₁ => ?_))
  refine WP.pure' ?_
  dsimp only
  simp only [StateT.run_bind, StateT.run_modify, pure_bind]
  refine WP.bind (WP.bind (WP.bind (FCond.wp_regAs hC hP condS_bits1 ⟨_, condS_of 0⟩
    (C.ph_set _ _) (by rw [hC.lph]; exact hgh0) hi₁ fun k₂ hk₂ G₂ m₂ jr r hc₂ hd hi₂ => ?_)))
  obtain rfl := condS_eq hd
  rw [C.set_set, C.set_set] at hi₂
  refine WP.pure' ?_
  dsimp only
  simp only [StateT.run_bind]
  rw [condS_lt0 rfl]
  refine WP.bind (WP.callRC_ok debugAssert_true ?_)
  simp only [StateT.run_pure]
  refine WP.pure' ?_
  dsimp only
  simp only [StateT.run_bind]
  -- `unlock`
  refine WP.bind (WP.callC (WP.mono ?_ (ioMutex.unlock_wp hP hcost rfl hLc t _
    (by rw [hC.lph]; exact hgh) (by rw [hC.ok_c _ _ .out rfl rfl, FCond.set_of hgx]; exact hok)
    io G₂ m₂ k₂ hi₂ hc₂)))
  rintro _ G₃ m₃ d₃ ⟨hd₃, hc₃, hi₃⟩
  rw [← hC.set_l] at hi₃
  refine WP.mono ?_ (WP.loop _ _ (inv23 P L C t g i jr v d) (fun _ => 0) (post23 P L g t d)
    (loop23_body hC hP hcost hLc t g hgx hok i jr v d io hlive) _ G₃ m₃ d₃ ⟨by omega, hc₃, rfl, hi₃⟩)
  rintro ⟨x, s'⟩ G₄ m₄ d₄ ⟨hd₄, rfl, hc₄, rL, hi₄⟩
  exact WP.pure' ⟨by omega, rfl, hc₄, rL, hi₄⟩

/-- **`Io.Condition.waitUncancelable`** of Zig 0.16.0 (`waitInner(…, true)`). -/
theorem ioCond_wait_wp_v016 (hC : C.Fits L P U ok) (hP : L.FitsOn P U ok)
    (hcost : P.cost = none) {p q : Ptr} (hp : p = C.S.ptr) (hq : q = L.ptr) (hLc : L.c = ioMutex.c)
    (t : ThreadId) (g : γ) (hgx : C.ph g = .out) (hgh : L.ph g = .holds) (hok : ok g) (io : Io)
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
  unfold Io_Condition_waitUncancelable
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind]
  refine WP.bind (WP.callC (WP.mono ?_ (waitInner_wp hC hP hcost hLc t g hgx hgh hok io G m d
    hone hhb hent hlive hi)))
  rintro r G₁ m₁ d₁ ⟨hd₁, rfl, hc₁, rL, hi₁⟩
  simp only [StateT.run_pure, pure_bind, isNonErr]
  exact WP.pure' (WP.pure' ⟨hd₁, hc₁, rL, hi₁⟩)

end

end_when

end Sync
