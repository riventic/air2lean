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

end

end Sync
