import ZigLean.Conc.Stops
import ZigLean.Conc.Total

/-!
# Concurrent termination within the summed turn budget

`Proto.returnsWithin`: if `main` and every spawn target the budget allows keep turn budgets
(`Stops`, `ZigLean/Conc/Stops.lean`), and a strict protocol proof (`Proto.run_spec` with
`Proto.strict`) covers the program, then **every** schedule returns within `B` turns, where `B`
is `main`'s budget. A spawn charges the new thread's budget to its spawner, so `B` is the sum
of the budgets of all threads (`ReturnsWithin B`, uniform in the oracle).

The argument is a potential: the sum of the budgets of the waiting threads, at most the fuel
that is left. Each turn costs its thread at least one turn of its budget, and a spawn moves
`k + 1` of the spawner's `k + 2` to the new thread, so the sum goes down by at least one per
turn. The strict protocol gives a thread that can go on (no deadlock, `Proto.ready_ne`) and the
rely: every memory a thread is resumed in has the blocks of a memory that satisfies the
invariant (`hR`, `hRb`; the scheduler's part of a sync op does not change blocks). No fairness
premise is used: the bound holds for every oracle. A program whose turns depend on another
thread's progress (a futex wait, a deferred task) has no budget (`opCost`), so it fails closed.

Turns count scheduler turns of the model (THR-01), not time (SEM-05).
-/

namespace Zig
namespace Conc

open Proto

variable {Tgt γ : Type} {P : Proto Tgt γ}

/-! ## Budgets of the scheduler's threads -/

/-- The paths of a thread end within `B` turns; the values at the end are not constrained. -/
abbrev TT (R : Mem → Prop) (kb : Tgt → Option Nat) {β : Type} (B : Nat) {n : Nat}
    (x : CoN Tgt (β × Mem) n) : Prop :=
  Turns R kb (fun _ _ _ _ => True) B x

/-- A waiting thread with budget `b`: the op it waits at fits, and the rest is within the rest. -/
def PB (R : Mem → Prop) (kb : Tgt → Option Nat) {β : Type} (b : Nat) (p : Sched.Paused Tgt β) :
    Prop :=
  ∃ c, opCost kb p.op = some c ∧ c ≤ b ∧ ∀ r m', R m' → TT R kb (b - c) (p.k r m')

/-- A thread with budget `b` (an ended thread needs none). -/
def TB (R : Mem → Prop) (kb : Tgt → Option Nat) {β : Type} (b : Nat) : Sched.TS Tgt β → Prop
  | .paused p => PB R kb b p
  | .done => True

/-- The sum `f 0 + … + f (n - 1)`. -/
def bsum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => bsum f n + f n

theorem bsum_congr {f g : Nat → Nat} : ∀ {n}, (∀ j < n, f j = g j) → bsum f n = bsum g n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [bsum]
    rw [bsum_congr fun j hj => h j (by omega), h n (by omega)]

theorem bsum_set {f : Nat → Nat} {i v : Nat} :
    ∀ {n}, i < n → bsum (fun j => if j = i then v else f j) n + f i = bsum f n + v
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    simp only [bsum]
    by_cases hi : i = n
    · subst hi
      have : bsum (fun j => if j = i then v else f j) i = bsum f i :=
        bsum_congr fun j hj => by simp [Nat.ne_of_lt hj]
      simp only [this, ↓reduceIte]; omega
    · have ih : bsum (fun j => if j = i then v else f j) n + f i = bsum f n + v :=
        bsum_set (by omega)
      simp only [Ne.symm hi, ↓reduceIte]; omega

/-- The budgets of the threads of `s` sum to at most `fuel`. -/
def BInv (R : Mem → Prop) (kb : Tgt → Option Nat) {α : Type} (s : Sched.State Tgt α)
    (fuel : Nat) : Prop :=
  ∃ bm bk, TB R kb bm s.main ∧ (∀ i (h : i < s.kids.size), TB R kb (bk i) s.kids[i]) ∧
    bm + bsum bk s.kids.size ≤ fuel

/-! ## One turn -/

/-- A turn's result within budget `b`: it has a result, and on success the thread is left with
`b - c` for some `c ≥ 1`, `main` is unchanged, and the kids are the same or have one new kid
with `k + 1` of the `c = k + 2`. -/
def TurnB (R : Mem → Prop) (kb : Tgt → Option Nat) {α β : Type} (b : Nat) (s : Sched.State Tgt α) :
    Except (Option Error) (Sched.TS Tgt β × Option β × Sched.State Tgt α) → Prop
  | .error none => False
  | .error (some _) => True
  | .ok (ts, _, s') => ∃ c, 1 ≤ c ∧ c ≤ b ∧ TB R kb (b - c) ts ∧ s'.main = s.main ∧
      (s'.kids = s.kids ∨ ∃ k, c = k + 2 ∧ ∃ nk, s'.kids = s.kids.push nk ∧ TB R kb (k + 1) nk)

variable {R : Mem → Prop} {kb : Tgt → Option Nat}

/-- `settle` of a tree within `b - c`, from a state whose `main` and kids are those of `s` (or
have the new kid of a spawn). -/
theorem settle_budget {α β : Type} {t : ThreadId} {s s₁ : Sched.State Tgt α} {b c n : Nat}
    {tree : CoN Tgt (β × Mem) n} (hc : 1 ≤ c) (hcb : c ≤ b) (ht : TT R kb (b - c) tree)
    (hm : s₁.main = s.main)
    (hk : s₁.kids = s.kids ∨ ∃ k, c = k + 2 ∧ ∃ nk, s₁.kids = s.kids.push nk ∧ TB R kb (k + 1) nk) :
    TurnB R kb b s (Sched.settle t s₁ tree) := by
  cases tree with
  | leaf r =>
    rcases r with _ | _ | ⟨v, m⟩
    · simp [TT, Turns] at ht
    · trivial
    · simp only [Sched.settle]
      have hh := checkJoinedByChild_halts t m
      unfold Result.Halts at hh
      match hr : ((Thread.checkJoinedByChild t).run m).run, hh with
      | some (.error _), _ => trivial
      | some (.ok _), _ => exact ⟨c, hc, hcb, trivial, hm, hk⟩
  | sync op m k => exact ⟨c, hc, hcb, ht, hm, hk⟩

/-- The scheduler's part of a fork, a join or a futex wake keeps the blocks. -/
theorem fork_blocks {m m' : Mem} {c : ThreadId} (h : (Thread.fork.run m).run = some (.ok (c, m'))) :
    m'.blocks = m.blocks := by
  simp [Thread.fork, Thread.forkWith, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get,
    StateT.get, set, StateT.set, pure, StateT.pure, ExceptT.pure, ExceptT.mk, ExceptT.run,
    ExceptT.bind, ExceptT.bindCont, Option.bind] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

theorem join_blocks {m m' : Mem} {tid : ThreadId}
    (h : ((Thread.join tid).run m).run = some (.ok ((), m'))) : m'.blocks = m.blocks := by
  unfold Thread.join at h
  cases hr : m.threads[tid]? with
  | none =>
    simp_all [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      ExceptT.run, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, pure, ExceptT.pure, throw,
      throwThe, MonadExceptOf.throw, StateT.lift]
  | some rec =>
    by_cases hc : (rec.spawner != m.current || rec.joined || m.isGated tid) = true <;>
      simp_all [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
        ExceptT.run, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, pure, ExceptT.pure,
        throw, throwThe, MonadExceptOf.throw, StateT.lift, set, StateT.set]
    rw [← h]

/-- One turn of a thread with budget `b` (`PB`), from a state whose memory satisfies the rely. -/
theorem turn_budget {α β : Type} (env : Env) (dispatch : Tgt → ConcM Tgt Unit) (fuel : Nat)
    (o : Nat → Nat) (hRb : ∀ m m', m.blocks = m'.blocks → R m → R m')
    (hkid : ∀ tgt k, kb tgt = some k → ∀ m, R m →
      Stops R kb (dispatch tgt) (fun _ _ _ => True) m k)
    {t : ThreadId} {s : Sched.State Tgt α} {p : Sched.Paused Tgt β} {b : Nat}
    (hRs : R s.mem) (hpb : PB R kb b p) (hfuel : b ≤ fuel + 1) :
    TurnB R kb b s (Sched.turn env dispatch fuel o t s p) := by
  obtain ⟨d, op, k⟩ := p
  obtain ⟨c, hc, hcb, hk⟩ := hpb
  have c1 := opCost_pos hc
  have hRt : R { s.mem with current := t } := hRb s.mem _ rfl hRs
  cases op with
  | yield =>
    simp only [Sched.turn, Sched.turnTrace]
    exact settle_budget c1 hcb (hk _ _ hRt) rfl (.inl rfl)
  | choose n =>
    simp only [Sched.turn, Sched.turnTrace, Sched.State.choose]
    exact settle_budget c1 hcb (hk _ _ hRt) rfl (.inl rfl)
  | pick count =>
    simp only [Sched.turn, Sched.turnTrace, Sched.State.choose]
    exact settle_budget c1 hcb (hk _ _ hRt) rfl (.inl rfl)
  | asyncChoice =>
    simp only [Sched.turn, Sched.turnTrace]
    generalize hso : Sched.State.asyncChoice env { s with mem := { s.mem with current := t } } o = so
    obtain ⟨c', s₀⟩ := so
    obtain ⟨⟨st, tr, rfl⟩, -⟩ := asyncChoice_eq hso
    exact settle_budget c1 hcb (hk _ _ hRt) rfl (.inl rfl)
  | wake ptr n =>
    simp only [Sched.turn, Sched.turnTrace]
    generalize hso : Sched.State.chooseWake { s with mem := { s.mem with current := t } } o ptr n = so
    obtain ⟨cs, s₀⟩ := so
    obtain ⟨st, tr, rfl⟩ := chooseWake_eq hso
    obtain ⟨m₁, hw, -⟩ := futexWake_ok ptr n cs { s.mem with current := t }
    have hb : m₁.blocks = s.mem.blocks := by
      simp only [Thread.futexWake, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
        StateT.run, pure, ExceptT.pure, ExceptT.mk, ExceptT.run, Option.some.injEq,
        Except.ok.injEq, Prod.mk.injEq] at hw
      rw [← hw.2]
    simp only [Sched.State.onMem, bind, Except.bind, hw]
    exact settle_budget c1 hcb (hk _ _ (hRb _ _ hb.symm hRs)) rfl (.inl rfl)
  | join tid =>
    simp only [Sched.turn, Sched.turnTrace, Sched.State.onMem, bind, Except.bind]
    have hh := join_halts tid { s.mem with current := t }
    unfold Result.Halts at hh
    match hj : ((Thread.join tid).run { s.mem with current := t }).run, hh with
    | some (.error _), _ => trivial
    | some (.ok ((), m₁)), _ =>
      exact settle_budget c1 hcb (hk _ _ (hRb _ _ (join_blocks hj).symm hRt)) rfl (.inl rfl)
  | spawn tgt =>
    simp only [opCost] at hc
    obtain ⟨kk, hkk, rfl⟩ : ∃ kk, kb tgt = some kk ∧ kk + 2 = c := by
      cases h : kb tgt <;> simp_all
    simp only [Sched.turn, Sched.turnTrace]
    generalize hso : Sched.State.spawnOutcome env { s with mem := { s.mem with current := t } } o = so
    obtain ⟨c', s₀⟩ := so
    obtain ⟨⟨st, tr, rfl⟩, -⟩ := spawnOutcome_eq hso
    simp only
    split
    rotate_left
    · exact settle_budget c1 hcb (hk _ _ hRt) rfl (.inl rfl)
    simp only [Sched.State.onMem, bind, Except.bind]
    have hh := fork_halts { s.mem with current := t }
    unfold Result.Halts at hh
    match hf : (Thread.fork.run { s.mem with current := t }).run, hh with
    | some (.error _), _ => trivial
    | some (.ok (child, m₁)), _ =>
      refine settle_budget c1 hcb (hk _ _ (hRb _ _ (fork_blocks hf).symm hRt)) rfl
        (.inr ⟨kk, rfl, _, rfl, ⟨1, rfl, by omega, fun _ m' hr => ?_⟩⟩)
      exact Turns.mono (fun _ h => h) (fun _ _ _ _ _ => trivial) _
        (hkid tgt kk hkk m' hr fuel (by omega))
  | wait | gate | spawnGated => simp [opCost] at hc

/-- The kids after a turn of cost `c`: the same, or one new kid with `k + 1` of `c = k + 2`. The
new budgets agree below `kids.size` and their sum grows by at most `c - 1`. -/
theorem kids_budget {kids kids₂ : Array (Sched.TS Tgt Unit)} {bk : Nat → Nat} {c : Nat}
    (hc : 1 ≤ c) (hbk : ∀ i (h : i < kids.size), TB R kb (bk i) kids[i])
    (hk : kids₂ = kids ∨ ∃ k, c = k + 2 ∧ ∃ nk, kids₂ = kids.push nk ∧ TB R kb (k + 1) nk) :
    ∃ bk', (∀ i < kids.size, bk' i = bk i) ∧ (∀ i (h : i < kids₂.size), TB R kb (bk' i) kids₂[i]) ∧
      bsum bk' kids₂.size + 1 ≤ bsum bk kids.size + c := by
  rcases hk with rfl | ⟨k, rfl, nk, rfl, hnk⟩
  · exact ⟨bk, fun _ _ => rfl, hbk, by omega⟩
  · refine ⟨fun j => if j = kids.size then k + 1 else bk j, fun i hi => by simp [Nat.ne_of_lt hi],
      fun i hi => ?_, ?_⟩
    · rw [Array.getElem_push]
      split
      · rename_i hlt; simp only [Nat.ne_of_lt hlt, ↓reduceIte]; exact hbk i hlt
      · rename_i hlt
        simp only [Array.size_push] at hi
        have : i = kids.size := by omega
        subst this; simpa using hnk
    · simp only [Array.size_push, bsum, ↓reduceIte]
      rw [bsum_congr (g := bk) fun j hj => by simp [Nat.ne_of_lt hj]]
      omega

/-! ## The scheduler returns -/

/-- With at least the summed budget of fuel, `go` from a state that keeps the strict protocol
and the budgets has a result. -/
theorem go_some {α : Type} (env : Env) (henv : env.spawn = .fallible → P.spawnFails = true)
    (dispatch : Tgt → ConcM Tgt Unit) (o : Nat → Nat) {QM : α → (ThreadId → γ) → Mem → Nat → Prop}
    (hdisp : ∀ tgt g, P.init tgt g → ∀ u G m n, 0 < u → G u = g → P.inv G m →
      P.WP u (dispatch tgt) (P.QKid u) G { m with current := u } n)
    (hR : ∀ G m, P.inv G m → R m) (hRb : ∀ m m', m.blocks = m'.blocks → R m → R m')
    (hkid : ∀ tgt k, kb tgt = some k → ∀ m, R m →
      Stops R kb (dispatch tgt) (fun _ _ _ => True) m k) :
    ∀ (fuel : Nat) (s : Sched.State Tgt α) (G : ThreadId → γ), P.SInv QM s G →
      BInv R kb s fuel → (Sched.go env dispatch o fuel s).1 ≠ none := by
  intro fuel
  induction fuel with
  | zero =>
    rintro s G hs ⟨bm, bk, hbm, -, hle⟩
    obtain ⟨p, hp, -⟩ := hs.main
    rw [hp] at hbm
    obtain ⟨c, hc, hcb, -⟩ := hbm
    have := opCost_pos hc
    omega
  | succ fuel ih =>
    rintro s G hs ⟨bm, bk, hbm, hbk, hle⟩
    simp only [Sched.go, Sched.State.choose]
    split
    · have hrun : s.anyRunning = true := by
        obtain ⟨p, hp, -⟩ := hs.main; simp [Sched.State.anyRunning, hp]
      simp [hrun]
    rename_i hne
    have hpos : 0 < s.ready.size := by
      rw [Array.isEmpty_iff_size_eq_zero] at hne; omega
    simp only [Nat.pos_iff_ne_zero.mp hpos, ite_false]
    have hmem : s.ready[o s.step % s.ready.size]! ∈ s.ready := by
      rw [getElem!_pos s.ready _ (Nat.mod_lt _ hpos)]; exact Array.getElem_mem _
    generalize s.ready[o s.step % s.ready.size]! = t at hmem ⊢
    generalize hs₁ : ({ s with step := s.step + 1, trace := s.trace.push s.ready.size } :
      Sched.State Tgt α) = s₁
    have hS₁ : P.SInv QM s₁ G := by rw [← hs₁]; exact ⟨hs.inv, hs.size, hs.main, hs.kids⟩
    have hm₁ : s₁.main = s.main := by rw [← hs₁]
    have hk₁ : s₁.kids = s.kids := by rw [← hs₁]
    have hgo₁ : ∀ t (op : SyncOp Tgt), Sched.canGo s t op = true → Sched.canGo s₁ t op = true := by
      intro t op h; rw [← hs₁]; exact h
    have hRs : R s₁.mem := hR _ _ hS₁.inv
    rw [← hk₁] at hbk hle
    split
    · -- `main`'s turn
      rename_i ht0
      subst ht0
      obtain ⟨p₀, hp₀, hok⟩ := hs.main
      have hgo : Sched.canGo s₁ 0 p₀.op = true := by
        rcases mem_ready hmem with ⟨-, p, hp, hgo⟩ | ⟨i, _, hi, -⟩
        · rw [hp₀] at hp; cases hp; exact hgo₁ _ _ hgo
        · exact absurd hi.symm (Nat.succ_ne_zero i)
      simp only [hp₀]
      rw [← hm₁] at hp₀
      rw [← hm₁, hp₀] at hbm
      have htb := turn_budget env dispatch fuel o hRb hkid (t := 0) hRs hbm (by omega)
      unfold Sched.turn at htb
      split
      · rename_i e he
        rw [he] at htb
        cases e with
        | none => simp [TurnB] at htb
        | some e => simp [Sched.outOf]
      · simp
      · rename_i ts s₂ ht
        rw [ht] at htb
        obtain ⟨c, hc1, hcb, htb', hmain₂, hkids₂⟩ := htb
        obtain ⟨G₂, hagree, hmain, hsize, hkids, hr⟩ := turn_ok env henv dispatch fuel o hdisp
          hS₁.inv hS₁.size hok hgo hS₁.done ht
        rcases hr with ⟨-, p', g, rfl, hi, hpk⟩ | ⟨b, d, -, hov, -⟩
        · obtain ⟨bk', -, hbk', hsum⟩ := kids_budget hc1 hbk hkids₂
          refine ih { s₂ with main := .paused p' } (upd G₂ 0 g)
            ⟨hi, hsize, ⟨p', rfl, by rw [upd_self]; exact hpk⟩, fun i hi' =>
              kids_after hS₁.kids hagree hkids (fun u hu => upd_ne G₂ g hu) i hi' (by omega)⟩
            ⟨bm - c, bk', htb', hbk', by simp only at hsum ⊢; omega⟩
        · cases hov
    · -- a kid's turn
      rename_i ht0
      split
      · rename_i p hk
        rcases mem_ready hmem with ⟨h0, -⟩ | ⟨i, p', rfl, hi, hgo⟩
        · exact absurd h0 ht0
        simp only [Nat.add_sub_cancel] at hk
        rw [hk] at hi; cases hi
        rw [← hk₁, Array.getElem?_eq_some_iff] at hk
        obtain ⟨hlt, he⟩ := hk
        have hok := hS₁.kids i hlt
        rw [he] at hok
        have hpb := hbk i hlt
        rw [he] at hpb
        have hbi : bk i ≤ bsum bk s₁.kids.size := by
          have := bsum_set (f := bk) (v := 0) hlt; omega
        have htb := turn_budget env dispatch fuel o hRb hkid (t := i + 1) hRs hpb (by omega)
        unfold Sched.turn at htb
        split
        · rename_i e he'
          rw [he'] at htb
          cases e with
          | none => simp [TurnB] at htb
          | some e => simp [Sched.outOf]
        · rename_i ts ov s₂ ht
          rw [ht] at htb
          obtain ⟨c, hc1, hcb, htb', hmain₂, hkids₂⟩ := htb
          obtain ⟨G₂, hagree, hmain, hsize, hkids, hr⟩ := turn_ok (s := s₁) env henv dispatch fuel o
            hdisp hS₁.inv hS₁.size hok (hgo₁ _ _ hgo) hS₁.done ht
          obtain ⟨p₀, hp₀, hok₀⟩ := hS₁.main
          have hmain' : ∀ g, ∃ p, s₂.main = .paused p ∧
              P.PausedOk 0 QM (upd G₂ (i + 1) g 0) p :=
            fun g => ⟨p₀, hmain ▸ hp₀, by
              rw [upd_ne G₂ g (show (0 : Nat) ≠ i + 1 by omega), hagree 0 (Nat.succ_pos _)]
              exact hok₀⟩
          have hkids' : ∀ g (ts' : Sched.TS Tgt Unit), P.KidOk (i + 1) g ts' →
              ∀ j (h : j < (s₂.kids.set! i ts').size),
                P.KidOk (j + 1) (upd G₂ (i + 1) g (j + 1)) (s₂.kids.set! i ts')[j] := by
            intro g ts' hts j hj
            simp only [Array.set!, Array.size_setIfInBounds] at hj ⊢
            rw [Array.getElem_setIfInBounds hj]
            split
            · rename_i hij; subst hij; rw [upd_self]; exact hts
            · rename_i hij
              exact kids_after hS₁.kids hagree hkids (fun u hu => upd_ne G₂ g hu) j hj
                (by omega)
          -- the budgets: kid `i` keeps `bk i - c`
          obtain ⟨bk', hbk'i, hbk', hsum⟩ := kids_budget hc1 hbk hkids₂
          have hlt₂ : i < s₂.kids.size := by
            rcases hkids₂ with h | ⟨_, _, _, h, _⟩
            · rw [h]; exact hlt
            · rw [h, Array.size_push]; exact Nat.lt_succ_of_lt hlt
          have hB : BInv R kb { s₂ with kids := s₂.kids.set! i ts } fuel := by
            refine ⟨bm, fun j => if j = i then bk i - c else bk' j, ?_, fun j hj => ?_, ?_⟩
            · show TB R kb bm s₂.main; rw [hmain₂, hm₁]; exact hbm
            · simp only [Array.set!, Array.size_setIfInBounds] at hj ⊢
              rw [Array.getElem_setIfInBounds hj]
              split
              · rename_i hij; subst hij; simpa using htb'
              · rename_i hij; simp only [Ne.symm hij, ↓reduceIte]; exact hbk' j hj
            · simp only [Array.set!, Array.size_setIfInBounds]
              have := bsum_set (f := bk') (v := bk i - c) hlt₂
              rw [hbk'i i hlt] at this
              omega
          rcases hr with ⟨-, p', g, rfl, hi, hpk⟩ | ⟨b, d, rfl, -, g, hi, hfin⟩
          · exact ih { s₂ with kids := s₂.kids.set! i (.paused p') } (upd G₂ (i + 1) g)
              ⟨hi, by simp [hsize], hmain' g, hkids' g (.paused p') hpk⟩ hB
          · exact ih { s₂ with kids := s₂.kids.set! i .done } (upd G₂ (i + 1) g)
              ⟨hi, by simp [hsize], hmain' g, hkids' g .done hfin.1⟩ hB
      · rename_i hnp
        rcases mem_ready hmem with ⟨h0, -⟩ | ⟨i, p', rfl, hi, -⟩
        · exact absurd h0 ht0
        simp only [Nat.add_sub_cancel] at hnp
        exact (hnp p' hi).elim

namespace Proto

/-- **Termination within the summed turn budget.** A strict protocol proof of `main` (as for
`Proto.run_safe`), a turn budget `B` of `main` and a budget `kb tgt` of each spawn target that
the budgets allow, with a rely `R` that the invariant implies and that depends on the blocks
only: every schedule returns within `B` turns, with a result that satisfies `QM`. -/
theorem returnsWithin {α : Type} (env : Env) (henv : env.spawn = .fallible → P.spawnFails = true)
    (dispatch : Tgt → ConcM Tgt Unit) {main : ConcM Tgt α} {m0 : Mem}
    {QM : α → (ThreadId → γ) → Mem → Nat → Prop} (G0 : ThreadId → γ) (hstr : P.strict = true)
    (hdisp : ∀ tgt g, P.init tgt g → ∀ u G m n, 0 < u → G u = g → P.inv G m →
      P.WP u (dispatch tgt) (P.QKid u) G { m with current := u } n)
    (hQM : ∀ v G m d, QM v G m d → joinedAll 0 m)
    (hsize : m0.threads.size = 1)
    (hmain : ∀ n, P.WP 0 main QM G0 { m0 with current := 0 } n)
    {R : Mem → Prop} {kb : Tgt → Option Nat}
    (hR : ∀ G m, P.inv G m → R m) (hRb : ∀ m m', m.blocks = m'.blocks → R m → R m')
    (hkid : ∀ tgt k, kb tgt = some k → ∀ m, R m →
      Stops R kb (dispatch tgt) (fun _ _ _ => True) m k)
    {B : Nat} (hB : Stops R kb main (fun _ _ _ => True) { m0 with current := 0 } B) :
    Total.ReturnsWithin B env dispatch main m0 (fun v m => ∃ G d, QM v G m d) := by
  intro o fuel hf
  have hsome : (Sched.run env dispatch fuel o main m0).run ≠ none := by
    simp only [Sched.run, Sched.runTrace, ExceptT.run, ExceptT.mk]
    have hsafe : P.Safe 0 QM 1 G0 (main fuel { m0 with current := 0 }) := by
      have := hmain fuel; unfold WP at this; rwa [show ({ m0 with current := 0 } : Mem).threads.size = 1
        from hsize] at this
    have htb := settle_budget (R := R) (kb := kb) (t := 0)
      (s := ({ main := .done, kids := #[], mem := { m0 with current := 0 }, step := 0, trace := #[] } :
        Sched.State Tgt α)) (b := B + 1) (c := 1) (Nat.le_refl _) (by omega)
      (Turns.mono (fun _ h => h) (fun _ _ _ _ _ => trivial) _ (hB fuel hf)) rfl (.inl rfl)
    split
    · rename_i e he
      rw [he] at htb
      cases e with
      | none => simp [TurnB] at htb
      | some e => simp [Sched.outOf]
    · simp
    · rename_i ts s₁ hs
      rw [hs] at htb
      obtain ⟨c, hc1, -, htb', -⟩ := htb
      obtain ⟨e, hN, hr⟩ := settle_ok hsafe hs
      rcases hr with ⟨-, p, g, rfl, hi, hpk⟩ | ⟨b, d, -, hov, -⟩
      · have hk0 : s₁.kids.size = 0 := by rw [e]; rfl
        refine go_some env henv dispatch o hdisp hR hRb hkid fuel { s₁ with main := .paused p }
          (upd G0 0 g) ⟨hi, ?_, ⟨p, rfl, by rw [upd_self]; exact hpk⟩, ?_⟩
          ⟨B + 1 - c, fun _ => 0, htb', fun i hi => absurd hi (by simp [hk0]), ?_⟩
        · show s₁.mem.threads.size = s₁.kids.size + 1
          rw [hN, hk0]
        · intro i hi; simp only [hk0] at hi; omega
        · simp only [hk0, bsum]; omega
      · cases hov
  obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp hsome
  obtain ⟨hok, herr⟩ := run_spec env henv dispatch G0 hdisp (fun _ => hQM) hsize hmain hr
  rcases r with e | ⟨v, m⟩
  · exact absurd rfl (herr hstr e)
  · exact ⟨v, m, hr, hok v m rfl⟩

end Proto

end Conc
end Zig
