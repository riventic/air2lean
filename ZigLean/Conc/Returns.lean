import ZigLean.Conc.Lemmas

/-!
# Concurrent termination within the summed credits (`Proto.cost`)

`Proto.returnsWithin`: a strict protocol proof (the premises of `Proto.run_safe`) whose protocol
counts turns (`Proto.cost = some cr`, `docs/sep-threads.md` §Termination) gives, for **every**
oracle, a result within `B` scheduler turns, where `B = cr (G0 0)` is `main`'s credits at the
start. There is no second judgment: the turn budget is part of the one weakest precondition
(`Proto.Safe`'s charge at each stop, `Proto.Charged`).

The argument is a potential: the sum of the budgets of the waiting threads (`BInv`), at most the
fuel that is left. A waiting thread's budget (`PB`) is its credits, plus, at a spawn, the
credits it reserved for the new thread. A turn ends at a stop that paid one credit
(`Proto.ChargeOk`) or ends the thread, which held at least one credit; a spawn moves the
reserved credits to the new thread. So each turn makes the sum smaller by at least one. A stop
is also one level deeper in the thread's run (`CoN`), and a waiting thread has at least as much
depth as credits, so a run never stops for want of depth, and in strict mode with a cost a
`MemM` step has a result (`Safe`'s `leaf none` case). The strict protocol gives a thread that can
go on (no deadlock, `Proto.ready_ne`). No fairness premise is used. A futex wait, a deferred task
and its gate have no charge (`ChargeOk` is `False`), so a program that reaches one has no cost
proof: it fails closed. Turns count scheduler turns of the model (THR-01), not time.
-/

namespace Zig
namespace Conc
namespace Proto

variable {Tgt γ : Type} {P : Proto Tgt γ}

/-! ## Budgets -/

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

variable (P) in
/-- The budget `b` of a thread that waits at `p` with the ghost value `g`: at least one credit,
no more credits than depth, and the credits plus, at a spawn, the reservation for the new thread
(every start value of the target has between `1` and `k` credits). A futex wait, a gate and a
deferred spawn have no budget. -/
def PB {β : Type} (cr : γ → Nat) (g : γ) (b : Nat) (p : Sched.Paused Tgt β) : Prop :=
  1 ≤ cr g ∧ cr g ≤ p.depth ∧
    match p.op with
    | .spawn tgt => ∃ k, (∀ g₀, P.init tgt g₀ → 1 ≤ cr g₀ ∧ cr g₀ ≤ k) ∧ cr g + k ≤ b
    | .wait _ _ | .gate | .spawnGated _ => False
    | _ => cr g ≤ b

theorem PB.le {β : Type} {cr : γ → Nat} {g : γ} {b : Nat} {p : Sched.Paused Tgt β}
    (h : P.PB cr g b p) : 1 ≤ cr g ∧ cr g ≤ b := by
  obtain ⟨d, op, k⟩ := p
  obtain ⟨h1, -, h3⟩ := h
  refine ⟨h1, ?_⟩
  cases op <;> simp only at h3
  all_goals first | exact h3 | exact h3.elim | (obtain ⟨k, -, hk⟩ := h3; omega)

/-- A stop that paid for its turn (`ChargeOk`) leaves the thread a budget one smaller. -/
theorem PB.of_charge {β : Type} {cr : γ → Nat} {g : γ} {old : Nat} {p : Sched.Paused Tgt β}
    (hc : P.ChargeOk cr p.op old (cr g)) (hd : cr g ≤ p.depth) : P.PB cr g (old - 1) p := by
  obtain ⟨d, op, k⟩ := p
  cases op <;> simp only [ChargeOk] at hc
  all_goals first
    | exact hc.elim
    | (obtain ⟨h1, k', hk, hle⟩ := hc; exact ⟨h1, hd, k', hk, by omega⟩)
    | (obtain ⟨h1, hle⟩ := hc; exact ⟨h1, hd, by omega⟩)

variable (P) in
/-- The budget `b` of a thread state (an ended thread needs none). -/
def TB {β : Type} (cr : γ → Nat) (g : γ) (b : Nat) : Sched.TS Tgt β → Prop
  | .paused p => P.PB cr g b p
  | .done => True

variable (P) in
/-- The budgets of the threads of `s` (ghost values `G`) sum to at most `fuel`. -/
def BInv {α : Type} (cr : γ → Nat) (G : ThreadId → γ) (s : Sched.State Tgt α) (fuel : Nat) :
    Prop :=
  ∃ bm bk, P.TB cr (G 0) bm s.main ∧
    (∀ i (h : i < s.kids.size), P.TB cr (G (i + 1)) (bk i) s.kids[i]) ∧
    bm + bsum bk s.kids.size ≤ fuel

/-! ## A turn has a result -/

theorem checkJoined_some (t : ThreadId) (m : Mem) :
    ((Thread.checkJoinedByChild t).run m).run ≠ none := by
  unfold Thread.checkJoinedByChild
  simp only [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    ExceptT.run, ExceptT.bind, ExceptT.mk, ExceptT.pure, pure, Option.bind, ExceptT.bindCont]
  split <;> simp [throw, throwThe, MonadExceptOf.throw, StateT.lift, ExceptT.mk, ExceptT.bind,
    ExceptT.bindCont, bind, pure, ExceptT.pure, Option.bind, StateT.pure]

theorem join_some (tid : ThreadId) (m : Mem) : ((Thread.join tid).run m).run ≠ none := by
  unfold Thread.join
  cases hr : m.threads[tid]? with
  | none =>
    simp_all [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      ExceptT.run, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, pure, ExceptT.pure,
      throw, throwThe, MonadExceptOf.throw, StateT.lift]
  | some rec =>
    by_cases hc : (rec.spawner != m.current || rec.joined || m.isGated tid) = true <;>
      simp_all [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
        ExceptT.run, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, pure, ExceptT.pure,
        throw, throwThe, MonadExceptOf.throw, StateT.lift, set, StateT.set]

/-- A tree that keeps a protocol that counts turns in strict mode (`¬ P.Partial`), at a depth of
at least one, settles to a stop, an end or an error: never to "no result". -/
theorem settle_ne_none {α β : Type} {t : ThreadId} {Q : β → (ThreadId → γ) → Mem → Nat → Prop}
    {s : Sched.State Tgt α} {n N : Nat} {G : ThreadId → γ} {tree : CoN Tgt (β × Mem) n}
    (hnp : ¬ P.Partial) (hs : P.Safe t Q N G tree) (hn : 1 ≤ n) :
    Sched.settle t s tree ≠ .error none := by
  cases tree with
  | leaf r =>
    rcases r with _ | _ | ⟨b, m⟩
    · simp only [Safe] at hs
      rcases hs with h | h
      · exact absurd h hnp
      · omega
    · simp [Sched.settle]
    · simp only [Sched.settle]
      have := checkJoined_some t m
      split
      · simp
      · simp
      · rename_i h; exact absurd h this
  | sync op m k => simp [Sched.settle]

/-- In a protocol that counts turns in strict mode, a turn of a thread with a budget has a
result (`Sched.turn` is not "no result"). -/
theorem turn_ne_none {α β : Type} (env : Env) (henv : env.spawn = .fallible → P.spawnFails = true)
    (dispatch : Tgt → ConcM Tgt Unit) (fuel : Nat) (o : Nat → Nat) {cr : γ → Nat}
    (hnp : ¬ P.Partial) {t : ThreadId} {Q : β → (ThreadId → γ) → Mem → Nat → Prop}
    {s : Sched.State Tgt α} {G : ThreadId → γ} {p : Sched.Paused Tgt β} {b : Nat}
    (hinv : P.inv G s.mem) (hp : P.PausedOk t Q (G t) p) (hpb : P.PB cr (G t) b p)
    (hgo : Sched.canGo s t p.op = true) (hdone : ∀ u, s.isDone u = true → P.fin (G u)) :
    Sched.turn env dispatch fuel o t s p ≠ .error none := by
  obtain ⟨d, op, k⟩ := p
  obtain ⟨h1, hd, hop⟩ := hpb
  have hd1 : 1 ≤ d := Nat.le_trans h1 hd
  have hstep := hp G s.mem rfl hinv
  cases op with
  | yield =>
    simp only [Sched.turn, Sched.turnTrace]; exact settle_ne_none hnp hstep hd1
  | choose n =>
    simp only [Sched.turn, Sched.turnTrace, Sched.State.choose]
    exact settle_ne_none hnp (hstep _ (choice_lt _ _)) hd1
  | pick count =>
    simp only [Sched.turn, Sched.turnTrace, Sched.State.choose]
    exact settle_ne_none hnp (hstep _ (choice_lt _ _)) hd1
  | asyncChoice =>
    simp only [Sched.turn, Sched.turnTrace]
    generalize hso : Sched.State.asyncChoice env { s with mem := { s.mem with current := t } } o = so
    obtain ⟨c, s₀⟩ := so
    obtain ⟨⟨st, tr, rfl⟩, hc3⟩ := asyncChoice_eq hso
    exact settle_ne_none hnp (hstep c hc3) hd1
  | wake ptr n =>
    simp only [Sched.turn, Sched.turnTrace]
    generalize hso : Sched.State.chooseWake { s with mem := { s.mem with current := t } } o ptr n = so
    obtain ⟨cs, s₀⟩ := so
    obtain ⟨st, tr, rfl⟩ := chooseWake_eq hso
    obtain ⟨m₁, hw, -⟩ := futexWake_ok ptr n cs { s.mem with current := t }
    simp only [Sched.State.onMem, bind, Except.bind, hw]
    exact settle_ne_none hnp (hstep cs m₁ hw) hd1
  | spawn tgt =>
    obtain ⟨hfail, g₀, hg₀, hk⟩ := hstep
    simp only [Sched.turn, Sched.turnTrace]
    generalize hso : Sched.State.spawnOutcome env { s with mem := { s.mem with current := t } } o = so
    obtain ⟨c, s₀⟩ := so
    obtain ⟨⟨st, tr, rfl⟩, hcf⟩ := spawnOutcome_eq hso
    simp only
    split
    · simp only [Sched.State.onMem, bind, Except.bind]
      have hf : (Thread.fork.run { s.mem with current := t }).run = some (.ok (_, _)) :=
        fork_run _
      rw [hf]
      exact settle_ne_none hnp (hk _ _ hf) hd1
    · rename_i hc
      exact settle_ne_none hnp (hfail (henv (hcf hc)) _) hd1
  | join tid =>
    simp only [Sched.turn, Sched.turnTrace, Sched.State.onMem, bind, Except.bind]
    match hj : ((Thread.join tid).run { s.mem with current := t }).run with
    | none => exact absurd hj (join_some tid _)
    | some (.error _) => simp
    | some (.ok ((), m₁)) =>
      simp only
      have hv : Thread.joinValid s.mem t tid = true := join_valid hj
      have hf : P.fin (G tid) := hdone tid (by simpa [Sched.canGo, hv] using hgo)
      exact settle_ne_none hnp ((hstep.2 hf).2 m₁ hj) hd1
  | wait | gate | spawnGated => exact hop.elim

/-! ## The scheduler returns -/

/-- A turn's budgets: after a turn of the thread with budget `b`, its new budget and the new
thread's sum to less than `b`. -/
theorem turn_budget {β : Type} {cr : γ → Nat} (hcost : P.cost = some cr) {t : ThreadId}
    {G G₂ : ThreadId → γ} {p p' : Sched.Paused Tgt β}
    {g : γ} {b : Nat} (hpb : P.PB cr (G t) b p) (hG : G₂ t = G t)
    (hc : (P.Charged t p'.op G₂ g ∧ p'.depth + 1 = p.depth) ∨
      (p'.op = p.op ∧ ∃ ptr e, p.op = .wait ptr e)) :
    P.PB cr g (cr (G t) - 1) p' := by
  rcases hc with ⟨hch, hd⟩ | ⟨-, ptr, e, he⟩
  · have hco := hch cr hcost
    rw [hG] at hco
    have hgle : cr g + 1 ≤ cr (G t) := by
      obtain ⟨dd, op, k⟩ := p'
      cases op <;> simp only [ChargeOk] at hco
      all_goals first
        | exact hco.elim
        | (obtain ⟨-, k', -, hle⟩ := hco; omega)
        | (obtain ⟨-, hle⟩ := hco; omega)
    exact PB.of_charge hco (by have := hpb.2.1; omega)
  · obtain ⟨d, op, k⟩ := p
    simp only at he
    subst he
    exact hpb.2.2.elim

/-- A budget's reservation for a new thread: `kk` (`0` unless the thread waits at a spawn). -/
theorem PB.resv {β : Type} {cr : γ → Nat} {g : γ} {b : Nat} {p : Sched.Paused Tgt β}
    (h : P.PB cr g b p) : ∃ kk, (∀ tgt, p.op = .spawn tgt → ∀ g₀, P.init tgt g₀ →
      1 ≤ cr g₀ ∧ cr g₀ ≤ kk) ∧ cr g + kk ≤ b ∧ ∀ tgt, p.op ≠ .spawnGated tgt := by
  obtain ⟨d, op, k⟩ := p
  obtain ⟨-, -, h3⟩ := h
  cases op <;> simp only at h3
  case spawn tgt =>
    obtain ⟨kk, hkk, hle⟩ := h3
    exact ⟨kk, ⟨fun tgt' he => by simp only [SyncOp.spawn.injEq] at he; subst he; exact hkk,
      hle, fun _ he => by simp at he⟩⟩
  all_goals first
    | exact h3.elim
    | exact ⟨0, ⟨fun _ he => by simp at he, by omega, fun _ he => by simp at he⟩⟩

/-- The kids after a turn of a thread at `pop` that reserved `kk` credits: the same kids, or one
new kid whose start credits (at most `kk`) are its budget. -/
theorem kids_budget {cr : γ → Nat} {kids kids₂ : Array (Sched.TS Tgt Unit)} {bk : Nat → Nat}
    {G G₂ : ThreadId → γ} {pop : SyncOp Tgt} {fuel kk : Nat}
    (hagree : ∀ u, u < kids.size + 1 → G₂ u = G u)
    (hbk : ∀ j (h : j < kids.size), P.TB cr (G (j + 1)) (bk j) kids[j])
    (hkids : kids₂ = kids ∨ ∃ nk, kids₂ = kids.push nk ∧
      P.KidOk (kids.size + 1) (G₂ (kids.size + 1)) nk ∧
      ∃ tgt, ((pop = .spawn tgt ∧ ∃ k₀, nk = .paused ⟨fuel, .yield, k₀⟩) ∨
        pop = .spawnGated tgt) ∧ P.init tgt (G₂ (kids.size + 1)))
    (hres : ∀ tgt, pop = .spawn tgt → ∀ g₀, P.init tgt g₀ → 1 ≤ cr g₀ ∧ cr g₀ ≤ kk)
    (hgated : ∀ tgt, pop ≠ .spawnGated tgt) (hkf : kk ≤ fuel) :
    ∃ bk', kids.size ≤ kids₂.size ∧ (∀ j < kids.size, bk' j = bk j) ∧
      (∀ j (h : j < kids₂.size), P.TB cr (G₂ (j + 1)) (bk' j) kids₂[j]) ∧
      bsum bk' kids₂.size ≤ bsum bk kids.size + kk := by
  rcases hkids with rfl | ⟨nk, rfl, -, tgt, (⟨hsp, k₀, rfl⟩ | hsp), hin⟩
  · exact ⟨bk, Nat.le_refl _, fun _ _ => rfl, fun j hj => by
      rw [hagree _ (by omega)]; exact hbk j hj, by omega⟩
  · obtain ⟨hc1, hck⟩ := hres tgt hsp _ hin
    refine ⟨fun j => if j = kids.size then cr (G₂ (kids.size + 1)) else bk j, by simp,
      fun j hj => by simp [Nat.ne_of_lt hj], fun j hj => ?_, ?_⟩
    · rw [Array.getElem_push]
      dsimp only
      by_cases hlt : j < kids.size
      · rw [dif_pos hlt, if_neg (Nat.ne_of_lt hlt), hagree _ (by omega)]
        exact hbk j hlt
      · have hieq : j = kids.size := by simp only [Array.size_push] at hj; omega
        subst hieq
        rw [dif_neg hlt, if_pos rfl]
        exact ⟨hc1, by show cr (G₂ (kids.size + 1)) ≤ fuel; omega, by simp⟩
    · simp only [Array.size_push, bsum, ↓reduceIte]
      rw [bsum_congr (g := bk) fun j hj => by simp [Nat.ne_of_lt hj]]
      omega
  · exact (hgated tgt hsp).elim

/-- With at least the summed budget of fuel, `go` from a state that keeps the strict protocol
with a turn cost and the budgets has a result. -/
theorem go_some {α : Type} (env : Env) (henv : env.spawn = .fallible → P.spawnFails = true)
    (dispatch : Tgt → ConcM Tgt Unit) (o : Nat → Nat) {cr : γ → Nat} (hcost : P.cost = some cr)
    (hstr : P.strict = true) {QM : α → (ThreadId → γ) → Mem → Nat → Prop}
    (hdisp : ∀ tgt g, P.init tgt g → ∀ u G m n, 0 < u → G u = g → P.inv G m →
      P.WP u (dispatch tgt) (P.QKid u) G { m with current := u } n) :
    ∀ (fuel : Nat) (s : Sched.State Tgt α) (G : ThreadId → γ), P.SInv QM s G →
      P.BInv cr G s fuel → (Sched.go env dispatch o fuel s).1 ≠ none := by
  have hnp : ¬ P.Partial := by
    rintro (h | h)
    · rw [hstr] at h; cases h
    · rw [hcost] at h; cases h
  intro fuel
  induction fuel with
  | zero =>
    rintro s G hs ⟨bm, bk, hbm, -, hle⟩
    obtain ⟨p, hp, -⟩ := hs.main
    rw [hp] at hbm
    have := (PB.le hbm).2
    have := (PB.le hbm).1
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
      rw [hp₀] at hbm
      simp only [hp₀]
      have hnn := turn_ne_none env henv dispatch fuel o hnp hS₁.inv hok hbm hgo hS₁.done
      unfold Sched.turn at hnn
      split
      · rename_i e he
        rw [he] at hnn
        cases e with
        | none => exact absurd rfl hnn
        | some e => simp [Sched.outOf]
      · simp
      · rename_i ts s₂ ht
        obtain ⟨G₂, hagree, hmain, hsize, hkids, hr⟩ := turn_ok env henv dispatch fuel o hdisp
          hS₁.inv hS₁.size hok hgo hS₁.done ht
        have hG0 : G₂ 0 = G 0 := hagree 0 (Nat.succ_pos _)
        rcases hr with ⟨-, p', g, rfl, hi, hpk, hc⟩ | ⟨b, d, -, hov, -⟩
        · have hpb' := turn_budget hcost hbm hG0 hc
          -- the kids' budgets: the same, or a new kid with its reserved credits
          refine ih { s₂ with main := .paused p' } (upd G₂ 0 g)
            ⟨hi, hsize, ⟨p', rfl, by rw [upd_self]; exact hpk⟩, fun i hi' =>
              kids_after hS₁.kids hagree hkids (fun u hu => upd_ne G₂ g hu) i hi' (by omega)⟩ ?_
          rcases hkids with hk | ⟨nk, hk, -, tgt, hsp, hin⟩
          have hmle := PB.le hbm
          · refine ⟨cr (G 0) - 1, bk, by simpa [TB] using hpb', fun i hi' => ?_, ?_⟩
            · simp only at hi' ⊢
              revert hi'
              rw [hk]
              intro hi'
              rw [upd_ne G₂ g (show i + 1 ≠ 0 by omega), hagree _ (by omega)]
              exact hbk i hi'
            · show cr (G 0) - 1 + bsum bk s₂.kids.size ≤ fuel
              rw [hk]
              omega
          · rcases hsp with ⟨hsp, k₀, rfl⟩ | hsp
            · obtain ⟨h1m, -, hres⟩ := hbm
              obtain ⟨d₀, op₀, k'⟩ := p₀
              simp only at hsp
              subst hsp
              obtain ⟨kk, hkk, hle'⟩ := hres
              obtain ⟨hc1, hck⟩ := hkk _ hin
              refine ⟨cr (G 0) - 1, fun j => if j = s₁.kids.size then cr (G₂ (s₁.kids.size + 1))
                else bk j, by simpa [TB] using hpb', fun i hi' => ?_, ?_⟩
              · simp only at hi' ⊢
                revert hi'
                rw [hk]
                intro hi'
                rw [Array.getElem_push]
                by_cases hlt : i < s₁.kids.size
                · rw [dif_pos hlt, if_neg (Nat.ne_of_lt hlt), upd_ne G₂ g (show i + 1 ≠ 0 by omega),
                    hagree _ (by omega)]
                  exact hbk i hlt
                · have hieq : i = s₁.kids.size := by simp only [Array.size_push] at hi'; omega
                  subst hieq
                  rw [dif_neg hlt, if_pos rfl, upd_ne G₂ g (show s₁.kids.size + 1 ≠ 0 by omega)]
                  exact ⟨hc1, by show cr (G₂ (s₁.kids.size + 1)) ≤ fuel; omega, by simp⟩
              · show cr (G 0) - 1 + bsum _ s₂.kids.size ≤ fuel
                rw [hk, Array.size_push]
                simp only [bsum, ↓reduceIte]
                rw [bsum_congr (g := bk) fun j hj => by simp [Nat.ne_of_lt hj]]
                omega
            · obtain ⟨d₀, op₀, k'⟩ := p₀
              simp only at hsp
              subst hsp
              exact hbm.2.2.elim
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
        have hnn := turn_ne_none (s := s₁) env henv dispatch fuel o hnp hS₁.inv hok hpb
          (hgo₁ _ _ hgo) hS₁.done
        unfold Sched.turn at hnn
        split
        · rename_i e he'
          rw [he'] at hnn
          cases e with
          | none => exact absurd rfl hnn
          | some e => simp [Sched.outOf]
        · rename_i ts ov s₂ ht
          obtain ⟨G₂, hagree, hmain, hsize, hkids, hr⟩ := turn_ok (s := s₁) env henv dispatch fuel o
            hdisp hS₁.inv hS₁.size hok (hgo₁ _ _ hgo) hS₁.done ht
          have hGi : G₂ (i + 1) = G (i + 1) := hagree _ (by omega)
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
          -- the budgets: kid `i` keeps less than its credits or ends; a new kid gets its
          -- reserved credits
          obtain ⟨kk, hres, hkk, hgated⟩ := PB.resv hpb
          obtain ⟨hb1, hb2⟩ := PB.le hpb
          obtain ⟨bk', hsz', hagb, hbk', hsum⟩ := kids_budget (fuel := fuel) hagree hbk hkids hres
            hgated (by omega)
          have hmainB : ∀ g, P.TB cr (upd G₂ (i + 1) g 0) bm s₂.main := fun g => by
            rw [upd_ne G₂ g (show (0 : Nat) ≠ i + 1 by omega), hagree 0 (Nat.succ_pos _), hmain,
              hm₁]
            exact hbm
          have hlt₂ : i < s₂.kids.size := Nat.lt_of_lt_of_le hlt hsz'
          have hB : ∀ g (ts' : Sched.TS Tgt Unit) (v : Nat), P.TB cr g v ts' →
              v + 1 ≤ cr (G (i + 1)) →
              P.BInv cr (upd G₂ (i + 1) g) { s₂ with kids := s₂.kids.set! i ts' } fuel := by
            intro g ts' v htb hv
            refine ⟨bm, fun j => if j = i then v else bk' j, hmainB g, fun j hj => ?_, ?_⟩
            · simp only [Array.set!, Array.size_setIfInBounds] at hj ⊢
              rw [Array.getElem_setIfInBounds hj]
              split
              · rename_i hij; subst hij; simp only [↓reduceIte, upd_self]; exact htb
              · rename_i hij
                rw [if_neg (Ne.symm hij), upd_ne G₂ g (show j + 1 ≠ i + 1 by omega)]
                exact hbk' j hj
            · simp only [Array.set!, Array.size_setIfInBounds]
              have := bsum_set (f := bk') (v := v) hlt₂
              rw [hagb i hlt] at this
              omega
          simp only [Nat.add_sub_cancel]
          rcases hr with ⟨-, p'', g, rfl, hi, hpk, hc⟩ | ⟨b, d, rfl, -, g, hi, hfin⟩
          · exact ih { s₂ with kids := s₂.kids.set! i (.paused p'') } (upd G₂ (i + 1) g)
              ⟨hi, by simp [hsize], hmain' g, hkids' g (.paused p'') hpk⟩
              (hB g _ _ (turn_budget hcost hpb hGi hc) (by omega))
          · exact ih { s₂ with kids := s₂.kids.set! i .done } (upd G₂ (i + 1) g)
              ⟨hi, by simp [hsize], hmain' g, hkids' g .done hfin.1⟩ (hB g _ 0 trivial (by omega))
      · rename_i hnp'
        rcases mem_ready hmem with ⟨h0, -⟩ | ⟨i, p', rfl, hi, -⟩
        · exact absurd h0 ht0
        simp only [Nat.add_sub_cancel] at hnp'
        exact (hnp' p' hi).elim

/-! ## No stop is free (fail closed) -/

/-- **A stop cannot skip its charge**: in a protocol that counts turns, a thread with at most
one credit has no proof of any sync op (the stop pays one and keeps one). -/
theorem stop_needs_credits {cr : γ → Nat} (hcost : P.cost = some cr) {t : ThreadId}
    {op : SyncOp Tgt} {Q : op.Resp → (ThreadId → γ) → Mem → Nat → Prop} {G : ThreadId → γ}
    {m : Mem} {n : Nat} (hc : cr (G t) ≤ 1) : ¬ P.WP t (ConcM.sync op) Q G m (n + 1) := by
  intro h
  unfold WP at h
  simp only [ConcM.sync, Safe] at h
  obtain ⟨-, g, -, hch, -⟩ := h
  have hco := hch cr hcost
  cases op <;> simp only [ChargeOk] at hco
  all_goals first
    | exact hco.elim
    | (obtain ⟨h1, k', -, hle⟩ := hco; omega)
    | (obtain ⟨h1, hle⟩ := hco; omega)

/-- A futex wait has no charge: in a protocol that counts turns it has no proof (fail closed;
its turns depend on another thread's progress). -/
theorem wait_fails_closed {cr : γ → Nat} (hcost : P.cost = some cr) {t : ThreadId} {p : Ptr}
    {e : BitVec 32} {Q : Unit → (ThreadId → γ) → Mem → Nat → Prop} {G : ThreadId → γ} {m : Mem}
    {n : Nat} : ¬ P.WP t (ConcM.sync (.wait p e)) Q G m (n + 1) := by
  intro h
  unfold WP at h
  simp only [ConcM.sync, Safe] at h
  obtain ⟨-, g, -, hch, -⟩ := h
  exact hch cr hcost

/-- **Termination within the summed credits.** A strict protocol proof of `main` (as for
`Proto.run_safe`) whose protocol counts turns (`P.cost = some cr`), where `main` starts with
`B = cr (G0 0) ≥ 1` credits: under every oracle, every run with at least `B` turns gives a
result, and that result is `main`'s value with `QM`, or a stack overflow (premise STK-01; a run
whose memory has no stack budget has none). The new threads' credits come out of their
spawners' (`ChargeOk`), so `B` bounds the turns of all threads together. -/
theorem returnsWithin {α : Type} (env : Env) (henv : env.spawn = .fallible → P.spawnFails = true)
    (dispatch : Tgt → ConcM Tgt Unit) {main : ConcM Tgt α} {m0 : Mem}
    {QM : α → (ThreadId → γ) → Mem → Nat → Prop} (G0 : ThreadId → γ) {cr : γ → Nat}
    (hcost : P.cost = some cr) (hstr : P.strict = true)
    (hdisp : ∀ tgt g, P.init tgt g → ∀ u G m n, 0 < u → G u = g → P.inv G m →
      P.WP u (dispatch tgt) (P.QKid u) G { m with current := u } n)
    (hQM : ∀ v G m d, QM v G m d → joinedAll 0 m) (hsize : m0.threads.size = 1)
    (hmain : ∀ n, P.WP 0 main QM G0 { m0 with current := 0 } n) (hB : 1 ≤ cr (G0 0)) :
    ∀ o fuel, cr (G0 0) ≤ fuel → ∃ r, (Sched.run env dispatch fuel o main m0).run = some r ∧
      ((∃ v m', r = .ok (v, m') ∧ ∃ G d, QM v G m' d) ∨ r = .error .stackOverflow) := by
  intro o fuel hf
  have hnp : ¬ P.Partial := by
    rintro (h | h)
    · rw [hstr] at h; cases h
    · rw [hcost] at h; cases h
  have hsome : (Sched.run env dispatch fuel o main m0).run ≠ none := by
    simp only [Sched.run, Sched.runTrace, ExceptT.run, ExceptT.mk]
    have hsafe : P.Safe 0 QM 1 G0 (main fuel { m0 with current := 0 }) := by
      have := hmain fuel; unfold WP at this
      rwa [show ({ m0 with current := 0 } : Mem).threads.size = 1 from hsize] at this
    have hnn := settle_ne_none
      (s := (Sched.State.mk .done #[] { m0 with current := 0 } 0 #[] : Sched.State Tgt α))
      hnp hsafe (by omega)
    split
    · rename_i e he
      cases e with
      | none => exact absurd he hnn
      | some e => simp [Sched.outOf]
    · simp
    · rename_i ts s₁ hs
      obtain ⟨e, hN, hr⟩ := settle_ok hsafe hs
      rcases hr with ⟨-, p, g, rfl, hi, hpk, hch, hd⟩ | ⟨b, d, -, hov, -⟩
      · have hk0 : s₁.kids.size = 0 := by rw [e]; rfl
        have hco := hch cr hcost
        have hle : cr g + 1 ≤ cr (G0 0) := by
          obtain ⟨dd, op, k⟩ := p
          cases op <;> simp only [ChargeOk] at hco
          all_goals first
            | exact hco.elim
            | (obtain ⟨-, k', -, hle⟩ := hco; omega)
            | (obtain ⟨-, hle⟩ := hco; omega)
        have hpb : P.PB cr g (cr (G0 0) - 1) p := PB.of_charge hco (by omega)
        refine go_some env henv dispatch o hcost hstr hdisp fuel { s₁ with main := .paused p }
          (upd G0 0 g) ⟨hi, ?_, ⟨p, rfl, by rw [upd_self]; exact hpk⟩, ?_⟩
          ⟨cr (G0 0) - 1, fun _ => 0, by simpa [TB, upd_self] using hpb,
            fun i hi => absurd hi (by simp [hk0]), by simp only [hk0, bsum]; omega⟩
        · show s₁.mem.threads.size = s₁.kids.size + 1
          rw [hN, hk0]
        · intro i hi; simp only [hk0] at hi; omega
      · cases hov
  obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp hsome
  obtain ⟨hok, herr⟩ := run_spec env henv dispatch G0 hdisp (fun _ => hQM) hsize hmain hr
  refine ⟨r, hr, ?_⟩
  rcases r with e | ⟨v, m⟩
  · by_cases he : e = .stackOverflow
    · exact .inr (by rw [he])
    · exact absurd rfl (herr hstr e he)
  · exact .inl ⟨v, m, rfl, hok v m rfl⟩

end Proto
end Conc
end Zig
