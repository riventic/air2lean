import Proofs.Sync.IoMutex
import ZigLean.Sep.Full.Cond
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

`Io.Condition.State` is the packed `(waiters, signals)`: the low and the high 16 bits of the
condition's state word (`FCond`), every bit pattern a value. Stated for an abstract value `b`, so
that the walks keep `b` abstract (a literal state would let the kernel evaluate the packed
fields). -/

theorem condS_of (b : BitVec 32) :
    (Packed.ofBits? (α := Io_Condition_State) b).run = some (.ok (Packed.ofBits b)) := rfl

theorem condS_dec : ∀ b : BitVec 32, FCond.SOk b →
    ∃ r, (Packed.ofBits? (α := Io_Condition_State) b).run = some (.ok r) :=
  fun b _ => ⟨_, condS_of b⟩

theorem condS_eq {b : BitVec 32} {r : Io_Condition_State}
    (h : (Packed.ofBits? (α := Io_Condition_State) b).run = some (.ok r)) : r = Packed.ofBits b := by
  rw [condS_of] at h; cases h; rfl

/-- `waiters` is the low half of the state word. -/
theorem condS_w (b : BitVec 32) :
    (Packed.ofBits b : Io_Condition_State).waiters.toNat = b.toNat % 65536 := by
  show (b.extractLsb' 0 16).toNat = _
  simp

/-- `signals` is the high half of the state word. -/
theorem condS_s (b : BitVec 32) :
    (Packed.ofBits b : Io_Condition_State).signals.toNat = b.toNat / 65536 := by
  show (b.extractLsb' 16 16).toNat = _
  have := b.isLt
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  omega

/-- The state word of `(waiters, signals)`. -/
theorem condS_mk (w s : BitVec 16) :
    (Packed.toBits (Io_Condition_State.mk w s)).toNat = w.toNat + 65536 * s.toNat := by
  show ((w.setWidth 32 <<< 0) ||| (s.setWidth 32 <<< 16)).toNat = _
  have hw := w.isLt
  have hs := s.isLt
  rw [BitVec.toNat_or, BitVec.shiftLeft_zero, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
    BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : w.toNat < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : s.toNat < 2 ^ 32),
    Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega), Nat.or_comm,
    ← Nat.shiftLeft_add_eq_or_of_lt (by omega), Nat.shiftLeft_eq]
  omega

/-- Every state word is the word of its value. -/
theorem condS_bits (b : BitVec 32) :
    Packed.toBits (Packed.ofBits b : Io_Condition_State) = b := by
  apply BitVec.eq_of_toNat_eq
  show (Packed.toBits (Io_Condition_State.mk (Packed.ofBits b : Io_Condition_State).waiters
    (Packed.ofBits b : Io_Condition_State).signals)).toNat = _
  rw [condS_mk, condS_w, condS_s]
  omega

/-- `signal`'s post: one more signal to a state with a waiter lacking one. -/
theorem condS_post {b : BitVec 32} {r : BitVec 16}
    (hlt : ¬b.toNat % 65536 ≤ b.toNat / 65536)
    (hr : r.toNat = b.toNat / 65536 + 1) :
    FCond.PostOk (Packed.toBits (Packed.ofBits b : Io_Condition_State))
      (Packed.toBits (Io_Condition_State.mk (Packed.ofBits b : Io_Condition_State).waiters r)) := by
  unfold FCond.PostOk
  rw [condS_bits, condS_mk, condS_w, hr]
  omega

theorem condS_bits1 : Packed.toBits (Packed.ofBits (1 : BitVec 32) : Io_Condition_State) = 1 :=
  condS_bits 1

/-- The waiter's take of a signal: `(w, s) - (1, 1)`, with `0 < s ≤ w`. -/
theorem condS_take {b : BitVec 32} (hok : FCond.SOk b) (hs : b.toNat / 65536 ≠ 0) :
    Packed.toBits (Io_Condition_State.mk ((Packed.ofBits b : Io_Condition_State).waiters - 1)
      ((Packed.ofBits b : Io_Condition_State).signals - 1)) =
      Packed.toBits (Packed.ofBits b : Io_Condition_State) - 0x10001 := by
  unfold FCond.SOk at hok
  rw [condS_bits]
  apply BitVec.eq_of_toNat_eq
  have hw := condS_w b
  have hs' := condS_s b
  have h1 : ((Packed.ofBits b : Io_Condition_State).waiters - 1).toNat =
      (Packed.ofBits b : Io_Condition_State).waiters.toNat - 1 :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hw]; simp; omega)
  have h2 : ((Packed.ofBits b : Io_Condition_State).signals - 1).toNat =
      (Packed.ofBits b : Io_Condition_State).signals.toNat - 1 :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hs']; simp; omega)
  have h3 : (b - 0x10001).toNat = b.toNat - 65537 := by bv_omega
  rw [condS_mk, h1, h2, h3, hw, hs']
  omega

/-- A state value with a signal: `0 < s`. -/
theorem condS_sig (b : BitVec 32) :
    gt false (Packed.ofBits b : Io_Condition_State).signals 0 = decide (b.toNat / 65536 ≠ 0) := by
  simp only [gt, lt, Bool.false_eq_true, ↓reduceIte, BitVec.ult, condS_s]
  by_cases h : b.toNat / 65536 = 0 <;> simp [h] <;> omega

theorem condS_subW {b : BitVec 32} (hok : FCond.SOk b) (hs : b.toNat / 65536 ≠ 0) :
    (sub false (Packed.ofBits b : Io_Condition_State).waiters (1 : BitVec 16)).run =
    some (.ok ((Packed.ofBits b : Io_Condition_State).waiters - 1)) := by
  unfold FCond.SOk at hok
  rw [Auto.sub_ok (by rw [condS_w]; simp; omega)]; rfl

theorem condS_subS {b : BitVec 32} (hs : b.toNat / 65536 ≠ 0) :
    (sub false (Packed.ofBits b : Io_Condition_State).signals (1 : BitVec 16)).run =
    some (.ok ((Packed.ofBits b : Io_Condition_State).signals - 1)) := by
  rw [Auto.sub_ok (by rw [condS_s]; simp; omega)]; rfl

/-- `assert(prev_state.waiters < maxInt(u16))` of a registration (`FCond.RegOld`). -/
theorem condS_room {b : BitVec 32} (h : FCond.RegOld b) :
    lt false (Packed.ofBits b : Io_Condition_State).waiters (65535 : BitVec 16) = true := by
  unfold FCond.RegOld at h
  simp only [lt, Bool.false_eq_true, ↓reduceIte, BitVec.ult, condS_w]
  simp; omega

theorem debugAssert_true : (debug_assert true).run = some (.ok ()) := rfl

section
variable {γ : Type} {L : FLock γ} {C : FCond γ} {P : Proto Tgt γ}
  {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}

/-! ## `signal` -/

/-- `signal`'s loop invariant, for the call snapshot `h c` (`FCond.Fits.enterSl`): `t` last read
the state value `b` (`waiters ≥ signals`); a served value (`waiters ≤ signals`) gave the history
post and `t` is out, else `t` is still at `sl h c`. -/
def sigInv (P : Proto Tgt γ) (C : FCond γ) (t : ThreadId) (g : γ) (h : Array Word.Entry)
    (c : VClock) (D : Nat) (s : Io_Condition_signalLocals) (G : ThreadId → γ) (m : Mem)
    (d : Nat) : Prop :=
  d < D ∧ m.current = t ∧ ∃ b : BitVec 32, s.prev_state = Packed.ofBits b ∧ FCond.SOk b ∧
    (b.toNat % 65536 ≤ b.toNat / 65536 → ∀ all, C.SigPost h c all m) ∧
    P.inv (upd G t (C.set g (FCond.afterSRead h c b))) m

/-- `signal`'s loop ends with `t` out and the history post. -/
def sigPost (P : Proto Tgt γ) (C : FCond γ) (t : ThreadId) (g : γ) (h : Array Word.Entry)
    (c : VClock) (D : Nat) (r : Io_Condition_signalExit × Io_Condition_signalLocals)
    (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  (r.1 = .ret ∨ r.1 = .br10) ∧ d < D ∧ m.current = t ∧ P.inv (upd G t g) m ∧
    C.SigPost h c false m

theorem sig_body (hC : L.Fits (C.prim L) P U ok) (hcost : P.cost = none)
    (t : ThreadId) (g : γ) (hgx : C.ph g = .out)
    (hgo : L.ph g = .out ∨ L.ph g = .holds) (h : Array Word.Entry) (c : VClock) (D : Nat)
    (io : Io) (s : Io_Condition_signalLocals) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hs : sigInv P C t g h c D s G m d) :
    P.WP t ((Io_Condition_signal.loop11 C.S.ptr io).run s) (fun r G' m' d' =>
      if Io_Condition_signal.again11 r.1 then sigInv P C t g h c D r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : Io_Condition_signalLocals) => 0) s)
      else sigPost P C t g h c D r G' m' d') G m d := by
  obtain ⟨hd, hcur, b, hb, hok, hsp, hi⟩ := hs
  obtain ⟨ps⟩ := s
  simp only at hb
  subst hb
  by_cases hsv : b.toNat % 65536 ≤ b.toNat / 65536
  · have hp := hsp hsv false
    rw [show FCond.afterSRead h c b = .out by simp [FCond.afterSRead, hsv],
      FCond.set_of hgx] at hi
    clear hsp
    fsym [condS_w, condS_s, FCond.SOk, sigPost, Io_Condition_signal.again11]
  · rw [show FCond.afterSRead h c b = .sl h c by simp [FCond.afterSRead, hsv]] at hi
    clear hsp
    fsym [FCond.wp_postAs hC condS_dec (sh := h) (c := c), FCond.wp_bump hC, FCond.wp_wakeEp hC,
      hC.wp_projE (t := t), FCond.SigPost.ofPost, condS_post hsv, condS_eq, condS_w, condS_s, condS_mk,
      C.ph_set, hC.lph, C.set_set, FCond.set_of, (FCond.set_of hgx), FCond.ptr_ep,
      FCond.SOk, sigInv, sigPost, Io_Condition_signal.again11]

/-- **`Io.Condition.signal`** outside or holding the mutex, preserving its complete resource,
with the history post of its call (`FCond.SigPost`). -/
theorem ioCond_signal_wp (hC : L.Fits (C.prim L) P U ok) (hcost : P.cost = none)
    {p : Ptr} (hp : p = C.S.ptr) (t : ThreadId) (g : γ) (hgx : C.ph g = .out)
    (hgo : L.ph g = .out ∨ L.ph g = .holds) (hsx : C.sx g)
    (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat) (hi : P.inv (upd G t g) m) :
    P.WP t (Io_Condition_signal p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      P.inv (upd G' t g) m' ∧ C.SigPost (C.S.hist m) (m.clocks[t]!) false m') G m d := by
  have hi' := hC.enterSl hgx hgo hsx hi
  generalize C.S.hist m = h at hi' ⊢
  generalize m.clocks[t]! = c at hi' ⊢
  clear hi
  fsym [FCond.wp_sloadAs hC condS_dec, condS_eq, C.ph_set, hC.lph, C.set_set,
    WP.loop _ _ (sigInv P C t g h c d) (fun _ => 0) (sigPost P C t g h c d)
      (sig_body hC hcost t g hgx hgo h c d io),
    sigInv, sigPost]

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

theorem gR_set {g : γ} {i i' jr : Nat} {sn sn' : Bool} {e e' : BitVec 32} :
    C.set (gR L C g i jr sn e) (.reg i' jr sn' e') = gR L C g i' jr sn' e' := C.set_set _ _ _

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

/-- The inner loop's invariant: `t` registered (write `jr`), with its epoch write `i` and value
`e` (the local `epoch`), and the state value `b` it read last (`waiters ≥ signals`), at
`afterRead i jr e b`: it has a signal to take iff `signals ≠ 0`. -/
def inv56 (P : Proto Tgt γ) (L : FLock γ) (C : FCond γ) (t : ThreadId) (g : γ) (i jr : Nat)
    (e : BitVec 32) (D : Nat) (s : Io_Condition_waitInnerLocals) (G : ThreadId → γ) (m : Mem)
    (d : Nat) : Prop :=
  d < D ∧ m.current = t ∧ s.epoch = e ∧ ∃ b : BitVec 32, s.prev_state = Packed.ofBits b ∧
    FCond.SOk b ∧ P.inv (upd G t (gR L C g i jr (decide (b.toNat / 65536 ≠ 0)) e)) m

/-- The inner loop ends with no signal to take (`br55`), or with `t` holding the mutex again. -/
def post56 (P : Proto Tgt γ) (L : FLock γ) (C : FCond γ) (t : ThreadId) (g : γ) (i jr : Nat)
    (e : BitVec 32) (D : Nat) (r : Io_Condition_waitInnerExit × Io_Condition_waitInnerLocals)
    (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ m.current = t ∧
  ((r.1 = .br55 ∧ r.2.epoch = e ∧ P.inv (upd G t (gR L C g i jr false e)) m) ∨
    (r.1 = .ret (.ok ()) ∧ ∃ rL, P.inv (upd G t (L.set g .holds rL)) m))

theorem loop56_body (hC : L.Fits (C.prim L) P U ok) (hcost : P.cost = none)
    (hLc : L.c = ioMutex.c) (t : ThreadId) (g : γ) (hgx : C.ph g = .out) (hok : ok g)
    (i jr : Nat) (e : BitVec 32) (D : Nat) (io : Io) (s : Io_Condition_waitInnerLocals)
    (G : ThreadId → γ) (m : Mem) (d : Nat) (h : inv56 P L C t g i jr e D s G m d) :
    P.WP t ((Io_Condition_waitInner.loop56 C.S.ptr io L.ptr).run s) (fun r G' m' d' =>
      if Io_Condition_waitInner.again56 r.1 then inv56 P L C t g i jr e D r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : Io_Condition_waitInnerLocals) => 0) s)
      else post56 P L C t g i jr e D r G' m' d') G m d := by
  obtain ⟨hD, hc, hep, b, hps, hb, hi⟩ := h
  unfold Io_Condition_waitInner.loop56
  simp only [StateT.run_bind, StateT.run_get, pure_bind, bind_assoc]
  refine WP.bind ?_
  have hg : gt false s.prev_state.signals 0 = decide (b.toNat / 65536 ≠ 0) := by
    rw [hps, condS_sig]
  by_cases hs : b.toNat / 65536 = 0
  · -- no signal: back to the futex wait
    simp only [hg, hs, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
      ↓reduceIte] at hi ⊢
    repeat (first
      | exact ⟨hD, hc, .inl ⟨rfl, hep, hi⟩⟩
      | refine WP.pure' ?_
      | simp only [StateT.run_pure, pure_bind, Io_Condition_waitInner.again56, Bool.false_eq_true,
          ↓reduceIte])
    done
  · -- a signal: take it
    simp only [hg, hs, ne_eq, not_false_eq_true, decide_true, ↓reduceIte] at hi ⊢
    simp only [StateT.run_bind, StateT.run_get]
    simp only [pure_bind]
    refine WP.bind (WP.callRC_ok (by rw [hps]; exact condS_subW hb hs) ?_)
    refine WP.bind (WP.callRC_ok (by rw [hps]; exact condS_subS hs) ?_)
    dsimp only
    rw [hps]
    refine WP.bind (FCond.wp_consumeAs hC condS_dec (by rw [condS_bits]; omega)
      (condS_take hb hs) gR_ph (gR_lph hC) hi
      fun k hk G₁ m₁ hc₁ => ⟨fun hi₁ => ?_, fun b' r hd hb' hi₁ => ?_⟩)
    · -- the signal taken: `lock`
      rw [gR_out hC hgx] at hi₁
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
      refine WP.bind (WP.bind (WP.callC (WP.mono ?_ (ioMutex.lock_wp hC hcost rfl hLc t _
        (L.ph_set _ _ _) ((hC.ok_set _ _ _).mpr hok) io G₁ m₁ k hi₁))))
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
      rw [FCond.afterRead, gR_set] at hi₁
      simp only [Option.isSome_some, ↓reduceIte, StateT.run_bind]
      refine WP.bind (WP.bind (WP.callRC_ok (x := optPayload (some (Packed.ofBits b'))) rfl ?_))
      repeat (first
        | exact ⟨⟨by omega, hc₁, hep, b', rfl, hb', hi₁⟩, .inl (by omega)⟩
        | refine WP.pure' ?_
        | simp only [StateT.run_pure, StateT.run_modify, StateT.run_bind, pure_bind,
            Io_Condition_waitInner.again56, ↓reduceIte])
      done

/-- The outer loop's invariant: `t` registered (write `jr`), before its futex wait, with an
epoch write `i` and its value, the local `epoch`. -/
def inv23 (P : Proto Tgt γ) (L : FLock γ) (C : FCond γ) (t : ThreadId) (g : γ) (jr : Nat)
    (D : Nat) (s : Io_Condition_waitInnerLocals) (G : ThreadId → γ) (m : Mem)
    (d : Nat) : Prop :=
  d < D ∧ m.current = t ∧ ∃ i, P.inv (upd G t (gR L C g i jr false s.epoch)) m

/-- The outer loop ends with `t` holding the mutex again. -/
def post23 (P : Proto Tgt γ) (L : FLock γ) (g : γ) (t : ThreadId) (D : Nat)
    (r : Io_Condition_waitInnerExit × Io_Condition_waitInnerLocals) (G : ThreadId → γ) (m : Mem)
    (d : Nat) : Prop :=
  d < D ∧ r.1 = .ret (.ok ()) ∧ m.current = t ∧ ∃ rL, P.inv (upd G t (L.set g .holds rL)) m

theorem loop23_body (hC : C.Fits L P U ok) (hcost : P.cost = none)
    (hLc : L.c = ioMutex.c) (t : ThreadId) (g : γ) (hgx : C.ph g = .out) (hok : ok g)
    (jr : Nat) (D : Nat) (io : Io)
    (hlive : ∀ G₁ m₁, (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) → L.ph (G₁ t) = .away →
      P.inv G₁ m₁ → FCond.sOf (C.lastS m₁) = 0 → (∀ v, (C.ph (G₁ v)).sig = false) →
      P.Live t G₁ m₁)
    (s : Io_Condition_waitInnerLocals) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (h : inv23 P L C t g jr D s G m d) :
    P.WP t ((Io_Condition_waitInner.loop23 C.S.ptr io L.ptr true).run s) (fun r G' m' d' =>
      if Io_Condition_waitInner.again23 r.1 then inv23 P L C t g jr D r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : Io_Condition_waitInnerLocals) => 0) s)
      else post23 P L g t D r G' m' d') G m d := by
  obtain ⟨hD, hc, i, hi⟩ := h
  have hF := hC.toFits
  unfold Io_Condition_waitInner.loop23
  simp only [StateT.run_bind, StateT.run_get, pure_bind, bind_assoc, ↓reduceIte]
  refine WP.bind (WP.callMC_ptrProject (hF.projE hi) ?_)
  dsimp only
  rw [FCond.ptr_ep]
  refine WP.bind (FCond.wp_waitEp hC (bits32 s.epoch) gR_ph (gR_lph hF) hi hlive
    fun k hk G₁ m₁ hc₁ hi₁ => ?_)
  rw [FCond.afterWait, gR_set] at hi₁
  dsimp only
  refine WP.bind (WP.callMC_ptrProject (hF.projE hi₁) ?_)
  dsimp only
  rw [FCond.ptr_ep]
  refine WP.bind (FCond.wp_loadEp hF gR_ph (gR_lph hF) hi₁
    fun k₂ hk₂ G₂ m₂ v i' hc₂ hi₂ => ?_)
  rw [gR_set] at hi₂
  simp only [StateT.run_modify, pure_bind]
  refine WP.bind (FCond.wp_loadSAs hF condS_dec gR_ph (gR_lph hF) hi₂
    fun k₃ hk₃ G₃ m₃ b r hc₃ hd hb hi₃ => ?_)
  obtain rfl := condS_eq hd
  rw [FCond.afterRead, gR_set] at hi₃
  refine WP.bind (WP.mono ?_ (WP.loop _ _ (inv56 P L C t g i' jr v d) (fun _ => 0)
    (post56 P L C t g i' jr v d) (loop56_body hF hcost hLc t g hgx hok i' jr v d io) _ G₃ m₃ k₃
    ⟨by omega, hc₃, rfl, b, rfl, hb, hi₃⟩))
  rintro ⟨x, s'⟩ G₄ m₄ d₄ ⟨hd₄, hc₄, ⟨rfl, hep₄, hi₄⟩ | ⟨rfl, rL, hi₄⟩⟩
  · rw [← hep₄] at hi₄
    repeat (first
      | exact ⟨⟨by omega, hc₄, i', hi₄⟩, .inl (by omega)⟩
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
theorem waitInner_wp (hC' : C.Fits L P U ok) (hcost : P.cost = none)
    (hLc : L.c = ioMutex.c) (t : ThreadId) (g : γ) (hgx : C.ph g = .out)
    (hgh : L.ph g = .holds) (hok : ok g) (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hroom : ∀ T, (∀ u, T ≤ u → C.ph (upd G t g u) = .out) → C.nreg (upd G t g) T < 65535)
    (hent : ∀ rX, U (upd G t g) rX m → C.Inv L (upd G t (C.set g .en)) m →
      U (upd G t (C.set g .en)) rX m)
    (hlive : ∀ G₁ m₁, (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) → L.ph (G₁ t) = .away →
      P.inv G₁ m₁ → FCond.sOf (C.lastS m₁) = 0 → (∀ v, (C.ph (G₁ v)).sig = false) →
      P.Live t G₁ m₁)
    (hi : P.inv (upd G t g) m) :
    P.WP t (Io_Condition_waitInner C.S.ptr io L.ptr true) (fun r G' m' d' => d' < d ∧
      r = .ok () ∧ m'.current = t ∧ ∃ rL, P.inv (upd G' t (L.set g .holds rL)) m') G m d := by
  have hC := hC'.toFits
  have hi0 := hC.enterEn hgx hgh hroom hent hi
  have hgh0 : L.ph (C.set g .en) = .holds := by rw [hC.lph]; exact hgh
  unfold Io_Condition_waitInner
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, StateT.run_pure, pure_bind]
  refine WP.bind (WP.callMC_ptrProject (hC.projE hi0) ?_)
  dsimp only
  rw [FCond.ptr_ep]
  refine WP.bind (WP.bind (FCond.wp_ldEp hC (C.ph_set _ _) hgh0 hi0
    fun k₁ hk₁ G₁ m₁ v i hc₁ hi₁ => ?_))
  refine WP.pure' ?_
  dsimp only
  simp only [StateT.run_bind, StateT.run_modify, pure_bind]
  refine WP.bind (WP.bind (WP.bind (FCond.wp_regAs hC condS_bits1 (fun b _ => ⟨_, condS_of b⟩)
    (C.ph_set _ _) (by rw [hC.lph]; exact hgh0) hi₁
    fun k₂ hk₂ G₂ m₂ jr old r hc₂ hro hd hi₂ => ?_)))
  obtain rfl := condS_eq hd
  rw [C.set_set, C.set_set] at hi₂
  refine WP.pure' ?_
  dsimp only
  simp only [StateT.run_bind]
  rw [condS_room hro]
  refine WP.bind (WP.callRC_ok debugAssert_true ?_)
  simp only [StateT.run_pure]
  refine WP.pure' ?_
  dsimp only
  simp only [StateT.run_bind]
  -- `unlock`
  refine WP.bind (WP.callC (WP.mono ?_ (ioMutex.unlock_wp hC hcost rfl hLc t _
    (by rw [hC.lph]; exact hgh) (by rw [hC.ok_calm _ _ .out rfl rfl, FCond.set_of hgx]; exact hok)
    io G₂ m₂ k₂ hi₂ hc₂)))
  rintro _ G₃ m₃ d₃ ⟨hd₃, hc₃, hi₃⟩
  rw [← hC.set_l] at hi₃
  refine WP.mono ?_ (WP.loop _ _ (inv23 P L C t g jr d) (fun _ => 0) (post23 P L g t d)
    (loop23_body hC' hcost hLc t g hgx hok jr d io hlive) _ G₃ m₃ d₃ ⟨by omega, hc₃, i, hi₃⟩)
  rintro ⟨x, s'⟩ G₄ m₄ d₄ ⟨hd₄, rfl, hc₄, rL, hi₄⟩
  exact WP.pure' ⟨by omega, rfl, hc₄, rL, hi₄⟩

/-- **`Io.Condition.waitUncancelable`** of Zig 0.16.0 (`waitInner(…, true)`). -/
theorem ioCond_wait_wp_v016 (hC : C.Fits L P U ok)
    (hcost : P.cost = none) {p q : Ptr} (hp : p = C.S.ptr) (hq : q = L.ptr) (hLc : L.c = ioMutex.c)
    (t : ThreadId) (g : γ) (hgx : C.ph g = .out) (hgh : L.ph g = .holds) (hok : ok g) (io : Io)
    (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hroom : ∀ T, (∀ u, T ≤ u → C.ph (upd G t g u) = .out) → C.nreg (upd G t g) T < 65535)
    (hent : ∀ rX, U (upd G t g) rX m → C.Inv L (upd G t (C.set g .en)) m →
      U (upd G t (C.set g .en)) rX m)
    (hlive : ∀ G₁ m₁, (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) → L.ph (G₁ t) = .away →
      P.inv G₁ m₁ → FCond.sOf (C.lastS m₁) = 0 → (∀ v, (C.ph (G₁ v)).sig = false) →
      P.Live t G₁ m₁)
    (hi : P.inv (upd G t g) m) :
    P.WP t (Io_Condition_waitUncancelable p io q) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ rL, P.inv (upd G' t (L.set g .holds rL)) m') G m d := by
  subst hp hq
  unfold Io_Condition_waitUncancelable
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind]
  refine WP.bind (WP.callC (WP.mono ?_ (waitInner_wp hC hcost hLc t g hgx hgh hok io G m d
    hroom hent hlive hi)))
  rintro r G₁ m₁ d₁ ⟨hd₁, rfl, hc₁, rL, hi₁⟩
  simp only [StateT.run_pure, pure_bind, isNonErr]
  exact WP.pure' (WP.pure' ⟨hd₁, hc₁, rL, hi₁⟩)

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
  d < D ∧ m.current = t ∧ s.epoch = e ∧ ∃ b : BitVec 32, s.prev_state = Packed.ofBits b ∧
    FCond.SOk b ∧ P.inv (upd G t (gR L C g i jr (decide (b.toNat / 65536 ≠ 0)) e)) m

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
    (i jr : Nat) (e : BitVec 32) (D : Nat) (io : Io) (s : Io_Condition_waitUncancelableLocals)
    (G : ThreadId → γ) (m : Mem) (d : Nat) (h : inv45 P L C t g i jr e D s G m d) :
    P.WP t ((Io_Condition_waitUncancelable.loop45 C.S.ptr io L.ptr).run s) (fun r G' m' d' =>
      if Io_Condition_waitUncancelable.again45 r.1 then inv45 P L C t g i jr e D r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧
          (fun _ => 0) r.2 < (fun (_ : Io_Condition_waitUncancelableLocals) => 0) s)
      else post45 P L C t g i jr e D r G' m' d') G m d := by
  obtain ⟨hD, hc, hep, b, hps, hb, hi⟩ := h
  unfold Io_Condition_waitUncancelable.loop45
  simp only [StateT.run_bind, StateT.run_get, pure_bind, bind_assoc]
  refine WP.bind ?_
  have hg : gt false s.prev_state.signals 0 = decide (b.toNat / 65536 ≠ 0) := by
    rw [hps, condS_sig]
  by_cases hs : b.toNat / 65536 = 0
  · -- no signal: back to the futex wait
    simp only [hg, hs, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
      ↓reduceIte] at hi ⊢
    repeat (first
      | exact ⟨hD, hc, .inl ⟨rfl, hep, hi⟩⟩
      | refine WP.pure' ?_
      | simp only [StateT.run_pure, pure_bind, Io_Condition_waitUncancelable.again45,
          Bool.false_eq_true, ↓reduceIte])
    done
  · -- a signal: take it
    simp only [hg, hs, ne_eq, not_false_eq_true, decide_true, ↓reduceIte] at hi ⊢
    simp only [StateT.run_bind, StateT.run_get]
    simp only [pure_bind]
    refine WP.bind (WP.callRC_ok (by rw [hps]; exact condS_subW hb hs) ?_)
    refine WP.bind (WP.callRC_ok (by rw [hps]; exact condS_subS hs) ?_)
    dsimp only
    rw [hps]
    refine WP.bind (FCond.wp_consumeAs hC condS_dec (by rw [condS_bits]; omega)
      (condS_take hb hs) gR_ph (gR_lph hC) hi
      fun k hk G₁ m₁ hc₁ => ⟨fun hi₁ => ?_, fun b' r hd hb' hi₁ => ?_⟩)
    · -- the signal taken: `lock`
      rw [gR_out hC hgx] at hi₁
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
      refine WP.bind (WP.bind (WP.callC (WP.mono ?_ (ioMutex.lock_wp hC hcost rfl hLc t _
        (L.ph_set _ _ _) ((hC.ok_set _ _ _).mpr hok) io G₁ m₁ k hi₁))))
      rintro _ G₂ m₂ d₂ ⟨hd₂, hc₂, rL, hi₂⟩
      rw [L.set_set] at hi₂
      repeat (first
        | exact ⟨by omega, hc₂, .inr ⟨rfl, rL, hi₂⟩⟩
        | refine WP.pure' ?_
        | simp only [StateT.run_pure, pure_bind, Io_Condition_waitUncancelable.again45,
            Bool.false_eq_true, ↓reduceIte])
      done
    · -- the `cmpxchg` failed: the read value
      obtain rfl := condS_eq hd
      rw [FCond.afterRead, gR_set] at hi₁
      simp only [Option.isSome_some, ↓reduceIte, StateT.run_bind]
      refine WP.bind (WP.bind (WP.callRC_ok (x := optPayload (some (Packed.ofBits b'))) rfl ?_))
      repeat (first
        | exact ⟨⟨by omega, hc₁, hep, b', rfl, hb', hi₁⟩, .inl (by omega)⟩
        | refine WP.pure' ?_
        | simp only [StateT.run_pure, StateT.run_modify, StateT.run_bind, pure_bind,
            Io_Condition_waitUncancelable.again45, ↓reduceIte])
      done

/-- The outer loop's invariant (as `inv23`). -/
def inv22 (P : Proto Tgt γ) (L : FLock γ) (C : FCond γ) (t : ThreadId) (g : γ) (jr : Nat)
    (D : Nat) (s : Io_Condition_waitUncancelableLocals) (G : ThreadId → γ)
    (m : Mem) (d : Nat) : Prop :=
  d < D ∧ m.current = t ∧ ∃ i, P.inv (upd G t (gR L C g i jr false s.epoch)) m

/-- The outer loop ends with `t` holding the mutex again. -/
def post22 (P : Proto Tgt γ) (L : FLock γ) (g : γ) (t : ThreadId) (D : Nat)
    (r : Io_Condition_waitUncancelableExit × Io_Condition_waitUncancelableLocals)
    (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ r.1 = .ret ∧ m.current = t ∧ ∃ rL, P.inv (upd G t (L.set g .holds rL)) m

theorem loop22_body (hC' : C.Fits L P U ok) (hcost : P.cost = none)
    (hLc : L.c = ioMutex.c) (t : ThreadId) (g : γ) (hgx : C.ph g = .out) (hok : ok g)
    (jr : Nat) (D : Nat) (io : Io)
    (hlive : ∀ G₁ m₁, (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) → L.ph (G₁ t) = .away →
      P.inv G₁ m₁ → FCond.sOf (C.lastS m₁) = 0 → (∀ v, (C.ph (G₁ v)).sig = false) →
      P.Live t G₁ m₁)
    (s : Io_Condition_waitUncancelableLocals) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (h : inv22 P L C t g jr D s G m d) :
    P.WP t ((Io_Condition_waitUncancelable.loop22 C.S.ptr io L.ptr).run s) (fun r G' m' d' =>
      if Io_Condition_waitUncancelable.again22 r.1 then inv22 P L C t g jr D r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧
          (fun _ => 0) r.2 < (fun (_ : Io_Condition_waitUncancelableLocals) => 0) s)
      else post22 P L g t D r G' m' d') G m d := by
  obtain ⟨hD, hc, i, hi⟩ := h
  have hC := hC'.toFits
  unfold Io_Condition_waitUncancelable.loop22
  simp only [StateT.run_bind, StateT.run_get, pure_bind, bind_assoc]
  refine WP.bind (WP.callMC_ptrProject (hC.projE hi) ?_)
  dsimp only
  rw [FCond.ptr_ep]
  refine WP.bind (FCond.wp_waitEp hC' (bits32 s.epoch) gR_ph (gR_lph hC) hi hlive
    fun k hk G₁ m₁ hc₁ hi₁ => ?_)
  rw [FCond.afterWait, gR_set] at hi₁
  dsimp only
  refine WP.bind (WP.callMC_ptrProject (hC.projE hi₁) ?_)
  dsimp only
  rw [FCond.ptr_ep]
  refine WP.bind (FCond.wp_loadEp hC gR_ph (gR_lph hC) hi₁
    fun k₂ hk₂ G₂ m₂ v i' hc₂ hi₂ => ?_)
  rw [gR_set] at hi₂
  simp only [StateT.run_modify, pure_bind]
  refine WP.bind (FCond.wp_loadSAs hC condS_dec gR_ph (gR_lph hC) hi₂
    fun k₃ hk₃ G₃ m₃ b r hc₃ hd hb hi₃ => ?_)
  obtain rfl := condS_eq hd
  rw [FCond.afterRead, gR_set] at hi₃
  refine WP.bind (WP.mono ?_ (WP.loop _ _ (inv45 P L C t g i' jr v d) (fun _ => 0)
    (post45 P L C t g i' jr v d) (loop45_body hC hcost hLc t g hgx hok i' jr v d io) _ G₃ m₃ k₃
    ⟨by omega, hc₃, rfl, b, rfl, hb, hi₃⟩))
  rintro ⟨x, s'⟩ G₄ m₄ d₄ ⟨hd₄, hc₄, ⟨rfl, hep₄, hi₄⟩ | ⟨rfl, rL, hi₄⟩⟩
  · rw [← hep₄] at hi₄
    repeat (first
      | exact ⟨⟨by omega, hc₄, i', hi₄⟩, .inl (by omega)⟩
      | refine WP.pure' ?_
      | simp only [StateT.run_pure, pure_bind, StateT.run_bind, ↓reduceIte,
          Io_Condition_waitUncancelable.again22])
    done
  · repeat (first
      | exact ⟨by omega, rfl, hc₄, rL, hi₄⟩
      | refine WP.pure' ?_
      | simp only [StateT.run_pure, pure_bind, StateT.run_bind,
          Io_Condition_waitUncancelable.again22, Bool.false_eq_true, ↓reduceIte])
    done

/-- **`Io.Condition.waitUncancelable`** of Zig 0.17.0 (the loops inlined). -/
theorem ioCond_wait_wp_v017 (hC' : C.Fits L P U ok)
    (hcost : P.cost = none) {p q : Ptr} (hp : p = C.S.ptr) (hq : q = L.ptr) (hLc : L.c = ioMutex.c)
    (t : ThreadId) (g : γ) (hgx : C.ph g = .out) (hgh : L.ph g = .holds) (hok : ok g) (io : Io)
    (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hroom : ∀ T, (∀ u, T ≤ u → C.ph (upd G t g u) = .out) → C.nreg (upd G t g) T < 65535)
    (hent : ∀ rX, U (upd G t g) rX m → C.Inv L (upd G t (C.set g .en)) m →
      U (upd G t (C.set g .en)) rX m)
    (hlive : ∀ G₁ m₁, (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) → L.ph (G₁ t) = .away →
      P.inv G₁ m₁ → FCond.sOf (C.lastS m₁) = 0 → (∀ v, (C.ph (G₁ v)).sig = false) →
      P.Live t G₁ m₁)
    (hi : P.inv (upd G t g) m) :
    P.WP t (Io_Condition_waitUncancelable p io q) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ rL, P.inv (upd G' t (L.set g .holds rL)) m') G m d := by
  subst hp hq
  have hC := hC'.toFits
  have hi0 := hC.enterEn hgx hgh hroom hent hi
  have hgh0 : L.ph (C.set g .en) = .holds := by rw [hC.lph]; exact hgh
  unfold Io_Condition_waitUncancelable
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, StateT.run_pure, pure_bind]
  refine WP.bind (WP.callMC_ptrProject (hC.projE hi0) ?_)
  dsimp only
  rw [FCond.ptr_ep]
  refine WP.bind (WP.bind (FCond.wp_ldEp hC (C.ph_set _ _) hgh0 hi0
    fun k₁ hk₁ G₁ m₁ v i hc₁ hi₁ => ?_))
  refine WP.pure' ?_
  dsimp only
  simp only [StateT.run_bind, StateT.run_modify, pure_bind]
  refine WP.bind (WP.bind (WP.bind (FCond.wp_regAs hC condS_bits1 (fun b _ => ⟨_, condS_of b⟩)
    (C.ph_set _ _) (by rw [hC.lph]; exact hgh0) hi₁
    fun k₂ hk₂ G₂ m₂ jr old r hc₂ hro hd hi₂ => ?_)))
  obtain rfl := condS_eq hd
  rw [C.set_set, C.set_set] at hi₂
  refine WP.pure' ?_
  dsimp only
  simp only [StateT.run_bind]
  rw [condS_room hro]
  refine WP.bind (WP.callRC_ok debugAssert_true ?_)
  simp only [StateT.run_pure]
  refine WP.pure' ?_
  dsimp only
  simp only [StateT.run_bind]
  -- `unlock`
  refine WP.bind (WP.callC (WP.mono ?_ (ioMutex.unlock_wp hC hcost rfl hLc t _
    (by rw [hC.lph]; exact hgh) (by rw [hC.ok_calm _ _ .out rfl rfl, FCond.set_of hgx]; exact hok)
    io G₂ m₂ k₂ hi₂ hc₂)))
  rintro _ G₃ m₃ d₃ ⟨hd₃, hc₃, hi₃⟩
  rw [← hC.set_l] at hi₃
  refine WP.mono ?_ (WP.loop _ _ (inv22 P L C t g jr d) (fun _ => 0) (post22 P L g t d)
    (loop22_body hC' hcost hLc t g hgx hok jr d io hlive) _ G₃ m₃ d₃ ⟨by omega, hc₃, i, hi₃⟩)
  rintro ⟨x, s'⟩ G₄ m₄ d₄ ⟨hd₄, rfl, hc₄, rL, hi₄⟩
  exact WP.pure' ⟨by omega, hc₄, rL, hi₄⟩

end

end_when

section
variable {γ : Type} {L : FLock γ} {C : FCond γ} {P : Proto Tgt γ}
  {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}

/-- **`Io.Condition.waitUncancelable`** of this translation. -/
theorem ioCond_wait_wp (hC : C.Fits L P U ok)
    (hcost : P.cost = none) {p q : Ptr} (hp : p = C.S.ptr) (hq : q = L.ptr) (hLc : L.c = ioMutex.c)
    (t : ThreadId) (g : γ) (hgx : C.ph g = .out) (hgh : L.ph g = .holds) (hok : ok g) (io : Io)
    (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hroom : ∀ T, (∀ u, T ≤ u → C.ph (upd G t g u) = .out) → C.nreg (upd G t g) T < 65535)
    (hent : ∀ rX, U (upd G t g) rX m → C.Inv L (upd G t (C.set g .en)) m →
      U (upd G t (C.set g .en)) rX m)
    (hlive : ∀ G₁ m₁, (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) → L.ph (G₁ t) = .away →
      P.inv G₁ m₁ → FCond.sOf (C.lastS m₁) = 0 → (∀ v, (C.ph (G₁ v)).sig = false) →
      P.Live t G₁ m₁)
    (_hpl : (L.part g).Plain) (hi : P.inv (upd G t g) m) (_hc : m.current = t) :
    P.WP t (Io_Condition_waitUncancelable p io q) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ rL, P.inv (upd G' t (L.set g .holds rL)) m') G m d := by
  first
    | exact ioCond_wait_wp_v016 hC hcost hp hq hLc t g hgx hgh hok io G m d hroom hent
        hlive hi
    | exact ioCond_wait_wp_v017 hC hcost hp hq hLc t g hgx hgh hok io G m d hroom hent
        hlive hi

end

/-- `Io.Condition` of this program as a condition, with the program's `Io.Mutex`. -/
def ioCond : CondImpl Tgt where
  wait := Io_Condition_waitUncancelable
  signal := Io_Condition_signal
  c := ioMutex.c
  wait_wp := ioCond_wait_wp
  signal_wp hC := ioCond_signal_wp hC.toFits

end Sync
