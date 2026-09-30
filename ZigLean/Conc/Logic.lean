import ZigLean.Conc.Sched
import ZigLean.Conc.Call

/-!
# Proofs over all schedules

A spec of a concurrent function holds for every schedule: for every oracle `o` and every `fuel`,
if `Sched.run dispatch fuel o main m0` gives a result, the result satisfies the spec
(`Conc.run_sound`). This file is the program logic for such a spec: rely–guarantee with a global
invariant and ghost values.

- **Protocol** (`Proto`). Each thread has a ghost value (`γ`), a value that only the proof sees:
  what the thread did so far (for example, how many increments). The invariant `inv G m` is on
  the ghost values `G` of all threads and the memory; it holds at every stop of every thread. A
  new thread with the target `tgt` starts with the ghost value `init tgt`; `fin g` holds of the
  ghost value of a thread that has ended.
- **One thread** (`Safe`). A thread's run is a tree (`CoN`). At each stop the thread picks its
  new ghost value and shows the invariant. When it goes on, it knows only the invariant and its
  own ghost value: the other threads can have done anything that keeps the invariant (the rely),
  and each thread keeps it (the guarantee). A thread does not change the ghost value of another
  thread, and a run between two stops keeps the number of threads.
- **Join.** A `join` of thread `u` goes on only after `u` ended, so the thread learns `fin (G u)`.
- **Partial correctness.** An error and "no result" satisfy every spec: the spec is about the
  results that a run gives. A proof that no run gives `.illegal` is a later step (`PLAN.md`
  §Next, T4 (2)).

The rules for generated code are on `WP` (the weakest precondition of a `ConcM` run): `pure`,
`bind`, a step in `MemM` (`WP.liftMem`), a sync op (`WP.sync`), and a loop (`WP.loop`). The post
gets the depth that is left: a loop repeat that passes a sync op has a smaller depth, so a loop
with no measure (a spin-wait) is proved by induction on the depth.
-/

namespace Zig
namespace Conc

/-- The protocol of a proof over all schedules (see the module doc). -/
structure Proto (Tgt γ : Type) where
  /-- Holds at every stop of every thread, of the ghost values and the memory. -/
  inv : (ThreadId → γ) → Mem → Prop
  /-- The ghost value of a new thread with the target `tgt`; `none`: the proof does not allow
  a spawn of `tgt`. -/
  init : Tgt → Option γ
  /-- Holds of the ghost value of a thread that has ended. -/
  fin : γ → Prop
  /-- `true`: no run gives an error (`run_safe`): no error leaf, every join is of a later thread
  that has not been joined (so no deadlock), and no futex wait. `false`: partial correctness
  (`run_sound`). -/
  strict : Bool := false

variable {Tgt γ : Type}

/-- The ghost values `G` with `g` for thread `t`. -/
def upd (G : ThreadId → γ) (t : ThreadId) (g : γ) : ThreadId → γ :=
  fun u => if u = t then g else G u

@[simp] theorem upd_self (G : ThreadId → γ) (t : ThreadId) (g : γ) : upd G t g t = g := by
  simp [upd]

theorem upd_ne (G : ThreadId → γ) {t u : ThreadId} (g : γ) (h : u ≠ t) : upd G t g u = G u := by
  simp [upd, h]

namespace Proto

variable (P : Proto Tgt γ)

/-- Thread `t` goes on at `op`, with the ghost values `G` and the memory `m` at that time: `K`
holds of each response and the memory after the scheduler's part of the op
(`Sched.turn`). -/
def Step (t : ThreadId) (op : SyncOp Tgt) (G : ThreadId → γ) (m : Mem)
    (K : op.Resp → (ThreadId → γ) → Mem → Prop) : Prop :=
  match op, K with
  | .yield, K => K () G { m with current := t }
  | .choose n, K => ∀ c, (c < n ∨ n = 0 ∧ c = 0) → K c G { m with current := t }
  | .pick count, K => ∀ c, (c < count { m with current := t } ∨
      count { m with current := t } = 0 ∧ c = 0) → K c G { m with current := t }
  | .spawn tgt, K => ∃ g, P.init tgt = some g ∧ ∀ child m',
      (Thread.fork.run { m with current := t }).run = some (.ok (child, m')) →
      K child (upd G child g) m'
  | .join tid, K => (P.strict = true → t < tid ∧ tid < m.threads.size) ∧ (P.fin (G tid) →
      (P.strict = true → ∃ m', ((Thread.join tid).run { m with current := t }).run =
        some (.ok ((), m'))) ∧ ∀ m',
      ((Thread.join tid).run { m with current := t }).run = some (.ok ((), m')) → K () G m')
  | .wait .., K => (P.strict = true → False) ∧ K () G { m with current := t }
  | .wake .., K => K () G { m with current := t }

theorem Step.mono {t : ThreadId} {op : SyncOp Tgt} {G : ThreadId → γ} {m : Mem}
    {K K' : op.Resp → (ThreadId → γ) → Mem → Prop} (h : ∀ r G m, K r G m → K' r G m)
    (hs : P.Step t op G m K) : P.Step t op G m K' := by
  cases op with
  | yield | wake => exact h _ _ _ hs
  | wait => exact ⟨hs.1, h _ _ _ hs.2⟩
  | choose | pick => exact fun c hc => h _ _ _ (hs c hc)
  | spawn tgt =>
    obtain ⟨g, hg, hk⟩ := hs
    exact ⟨g, hg, fun c m' hr => h _ _ _ (hk c m' hr)⟩
  | join tid => exact ⟨hs.1, fun hf => ⟨(hs.2 hf).1, fun m' hr => h _ _ _ ((hs.2 hf).2 m' hr)⟩⟩

/-- Thread `t`'s run `x`, which began with `N` threads and the ghost values `G`, keeps the
protocol, and each result `b` at the memory `m` and the depth `d` that is left satisfies
`Q b G m d`. -/
def Safe {β : Type} (t : ThreadId) (Q : β → (ThreadId → γ) → Mem → Nat → Prop) :
    {n : Nat} → Nat → (ThreadId → γ) → CoN Tgt (β × Mem) n → Prop
  | _, _, _, .leaf none => True
  | _, _, _, .leaf (some (.error _)) => P.strict = false
  | n, N, G, .leaf (some (.ok (b, m))) => m.threads.size = N ∧ Q b G m n
  | _, N, G, .sync op m k => m.threads.size = N ∧ ∃ g, P.inv (upd G t g) m ∧
      ∀ G₁ m₁, G₁ t = g → P.inv G₁ m₁ →
        P.Step t op G₁ m₁ fun r G₂ m₂ => Safe t Q m₂.threads.size G₂ (k r m₂)

variable {P}

theorem Safe.mono {β : Type} {t : ThreadId} {Q Q' : β → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ b G m d, Q b G m d → Q' b G m d) {n N G} (x : CoN Tgt (β × Mem) n) :
    P.Safe t Q N G x → P.Safe t Q' N G x := by
  induction x generalizing N G with
  | leaf r =>
    rcases r with _ | _ | ⟨b, m⟩ <;> simp only [Safe] <;> try exact id
    exact fun ⟨hN, hq⟩ => ⟨hN, h _ _ _ _ hq⟩
  | sync op m k ih =>
    simp only [Safe]
    exact fun ⟨hN, g, hi, hk⟩ => ⟨hN, g, hi, fun G₁ m₁ hg hi₁ =>
      Step.mono P (fun r G₂ m₂ hs => ih r m₂ hs) (hk G₁ m₁ hg hi₁)⟩

/-- Sequencing: the rest `f` of a result runs with the depth that is left. -/
theorem Safe.bind {α β : Type} {t : ThreadId} {Q : β → (ThreadId → γ) → Mem → Nat → Prop}
    {f : α → (k : Nat) → Mem → CoN Tgt (β × Mem) k} {n N G} (x : CoN Tgt (α × Mem) n) :
    P.Safe t (fun a G m d => P.Safe t Q m.threads.size G (f a d m)) N G x →
    P.Safe t Q N G (x.bind fun (a, m) k => f a k m) := by
  induction x generalizing N G with
  | leaf r =>
    rcases r with _ | _ | ⟨a, m⟩ <;> simp only [Safe, CoN.bind] <;> try exact id
    exact fun ⟨hN, hq⟩ => hN ▸ hq
  | sync op m k ih =>
    simp only [Safe, CoN.bind]
    exact fun ⟨hN, g, hi, hk⟩ => ⟨hN, g, hi, fun G₁ m₁ hg hi₁ =>
      Step.mono P (fun r G₂ m₂ hs => ih r m₂ hs) (hk G₁ m₁ hg hi₁)⟩

/-! ## The weakest precondition of a run -/

variable (P) in
/-- `x` run by thread `t` from the memory `m` with depth `n` and the ghost values `G` keeps the
protocol, and each result satisfies `Q`. -/
def WP {α : Type} (t : ThreadId) (x : ConcM Tgt α) (Q : α → (ThreadId → γ) → Mem → Nat → Prop)
    (G : ThreadId → γ) (m : Mem) (n : Nat) : Prop :=
  P.Safe t Q m.threads.size G (x n m)

namespace WP

variable {α β : Type} {t : ThreadId} {G : ThreadId → γ} {m : Mem} {n : Nat}

theorem mono {x : ConcM Tgt α} {Q Q' : α → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ a G m d, Q a G m d → Q' a G m d) (hx : P.WP t x Q G m n) : P.WP t x Q' G m n :=
  Safe.mono h _ hx

theorem pure' {a : α} {Q : α → (ThreadId → γ) → Mem → Nat → Prop} (h : Q a G m n) :
    P.WP t (pure a : ConcM Tgt α) Q G m n := by
  show P.Safe t Q m.threads.size G (.leaf (some (.ok (a, m))))
  simp only [Safe, true_and]; exact h

theorem bind {x : ConcM Tgt α} {f : α → ConcM Tgt β} {Q : β → (ThreadId → γ) → Mem → Nat → Prop}
    (h : P.WP t x (fun a G m d => P.WP t (f a) Q G m d) G m n) : P.WP t (x >>= f) Q G m n :=
  Safe.bind (f := fun a k m => f a k m) (x n m) h

/-- A step in `MemM`: no stop. It keeps the number of threads. In strict mode it does not throw
(`herr`). -/
theorem liftMem {x : MemM α} {Q : α → (ThreadId → γ) → Mem → Nat → Prop}
    (herr : ∀ e, (x.run m).run = some (.error e) → P.strict = false)
    (h : ∀ a m', (x.run m).run = some (.ok (a, m')) →
      m'.threads.size = m.threads.size ∧ Q a G m' n) :
    P.WP t (ConcM.liftMem x : ConcM Tgt α) Q G m n := by
  show P.Safe t Q m.threads.size G (.leaf (x.run m))
  match hx : (x.run m).run with
  | none => rw [show x.run m = ExceptT.mk none from hx]; simp [ExceptT.mk, Safe]
  | some (.error e) =>
    rw [show x.run m = ExceptT.mk (some (.error e)) from hx]; simp only [ExceptT.mk, Safe]
    exact herr e hx
  | some (.ok (a, m')) =>
    rw [show x.run m = ExceptT.mk (some (.ok (a, m'))) from hx]
    simp only [ExceptT.mk, Safe]; exact h a m' hx

/-- A sync op: the thread stops with the ghost value `g` and the invariant; `Q` holds of each
response when it goes on. At depth `0` there is no result. -/
theorem sync {op : SyncOp Tgt} {Q : op.Resp → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∃ g, P.inv (upd G t g) m ∧ ∀ G₁ m₁, G₁ t = g → P.inv G₁ m₁ →
      P.Step t op G₁ m₁ fun r G₂ m₂ => Q r G₂ m₂ k) :
    P.WP t (ConcM.sync op) Q G m n := by
  unfold WP
  match n, h with
  | 0, _ => simp [ConcM.sync, Safe]
  | k + 1, h =>
    obtain ⟨g, hi, hk⟩ := h k rfl
    simp only [ConcM.sync, Safe, true_and]
    refine ⟨g, hi, fun G₁ m₁ hg hi₁ => Step.mono P ?_ (hk G₁ m₁ hg hi₁)⟩
    intro r G₂ m₂ hq
    exact hq

/-- A loop (`Zig.loop`) with the invariant `inv` on the locals, the ghost values, the memory
and the depth. Each repeat passes a sync op (the depth gets smaller) or makes the measure `meas`
smaller. -/
theorem loop {σ ε : Type} (body : CM Tgt σ ε) (again : ε → Bool)
    (inv : σ → (ThreadId → γ) → Mem → Nat → Prop) (meas : σ → Nat)
    (post : ε × σ → (ThreadId → γ) → Mem → Nat → Prop)
    (step : ∀ s G m n, inv s G m n → P.WP t (body.run s) (fun r G' m' d =>
      if again r.1 then inv r.2 G' m' d ∧ (d < n ∨ d = n ∧ meas r.2 < meas s)
      else post r G' m' d) G m n) :
    ∀ s G m n, inv s G m n → P.WP t ((Zig.loop body again).run s) post G m n := by
  intro s G m n
  induction n using Nat.strongRecOn generalizing s G m with
  | _ n ihn =>
  induction hk : meas s using Nat.strongRecOn generalizing s G m with
  | _ k ihk =>
  intro hi
  rw [Zig.loop.eq_1, StateT.run_bind]
  apply WP.bind
  refine WP.mono ?_ (step s G m n hi)
  rintro ⟨e, s'⟩ G' m' d hq
  cases ha : again e
  · simp only [ha, Bool.false_eq_true, ↓reduceIte] at hq ⊢
    exact WP.pure' hq
  · simp only [ha, ↓reduceIte] at hq ⊢
    obtain ⟨hi', hd | ⟨rfl, hm⟩⟩ := hq
    · exact ihn d hd s' G' m' hi'
    · exact ihk (meas s') (hk ▸ hm) s' G' m' rfl hi'

end WP

/-! ## Soundness: the scheduler keeps the protocol -/

/-- Thread `t` joined every thread that it spawned (`Thread.checkJoinedByChild` does not
throw). -/
def joinedAll (t : ThreadId) (m : Mem) : Prop :=
  ∀ r ∈ m.threads, r.spawner = t → r.joined = true

variable (P) in
/-- The end of a spawned thread `t`: the invariant with its last ghost value, which satisfies
`fin`; in strict mode it joined its own threads. -/
def QKid (t : ThreadId) : Unit → (ThreadId → γ) → Mem → Nat → Prop :=
  fun _ G m _ => ∃ g, P.inv (upd G t g) m ∧ P.fin g ∧ (P.strict = true → joinedAll t m)

variable (P) in
/-- Thread `t`, which waits at `p` with the ghost value `g`, keeps the protocol when it goes on. -/
def PausedOk {β : Type} (t : ThreadId) (Q : β → (ThreadId → γ) → Mem → Nat → Prop) (g : γ)
    (p : Sched.Paused Tgt β) : Prop :=
  ∀ G₁ m₁, G₁ t = g → P.inv G₁ m₁ →
    P.Step t p.op G₁ m₁ fun r G₂ m₂ => P.Safe t Q m₂.threads.size G₂ (p.k r m₂)

variable (P) in
/-- A spawned thread: it waits and keeps the protocol, or it has ended. -/
def KidOk (t : ThreadId) (g : γ) : Sched.TS Tgt Unit → Prop
  | .paused p => P.PausedOk t (P.QKid t) g p
  | .done => P.fin g

theorem upd_same (G : ThreadId → γ) (t : ThreadId) : upd G t (G t) = G := by
  funext u; by_cases h : u = t <;> simp [upd, h]

theorem checkJoined_ok {t : ThreadId} {m m' : Mem} {x : Unit}
    (h : ((Thread.checkJoinedByChild t).run m).run = some (.ok (x, m'))) : m' = m := by
  unfold Thread.checkJoinedByChild at h
  simp only [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    ExceptT.run, ExceptT.bind, ExceptT.mk, ExceptT.pure, pure, Option.bind, ExceptT.bindCont] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw, StateT.lift, ExceptT.mk,
      ExceptT.bind, ExceptT.bindCont, bind, pure, ExceptT.pure, Option.bind] at h
  · simp [StateT.pure, pure, ExceptT.pure, ExceptT.mk] at h
    exact h.symm

theorem checkJoined_of {t : ThreadId} {m : Mem} (h : joinedAll t m) :
    ((Thread.checkJoinedByChild t).run m).run = some (.ok ((), m)) := by
  have hne : ¬ ∃ i, ∃ hi : i < m.threads.size, m.threads[i].spawner = t ∧
      m.threads[i].joined = false := by
    rintro ⟨i, hi, hs, hj⟩
    rw [h _ (Array.getElem_mem hi) hs] at hj; cases hj
  unfold Thread.checkJoinedByChild
  simp only [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    ExceptT.run, ExceptT.bind, ExceptT.mk, ExceptT.pure, pure, Option.bind, ExceptT.bindCont]
  simp only [Array.any_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true']
  rw [ite_eq_right hne]; rfl

theorem fork_ok {m m' : Mem} {c : ThreadId}
    (h : (Thread.fork.run m).run = some (.ok (c, m'))) :
    c = m.threads.size ∧ m'.threads.size = m.threads.size + 1 := by
  simp [Thread.fork, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get,
    StateT.get, set, StateT.set, pure, StateT.pure, ExceptT.pure, ExceptT.mk, ExceptT.run,
    ExceptT.bind, ExceptT.bindCont, Option.bind] at h
  obtain ⟨rfl, rfl⟩ := h
  simp

theorem join_ok {m m' : Mem} {tid : ThreadId}
    (h : ((Thread.join tid).run m).run = some (.ok ((), m'))) :
    m'.threads.size = m.threads.size := by
  unfold Thread.join at h
  cases hr : m.threads[tid]? with
  | none =>
    simp_all [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      ExceptT.run, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, pure, ExceptT.pure,
      throw, throwThe, MonadExceptOf.throw, StateT.lift]
  | some rec =>
    by_cases hc : (rec.spawner != m.current || rec.joined) = true <;>
      simp_all [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
        ExceptT.run, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, pure, ExceptT.pure,
        throw, throwThe, MonadExceptOf.throw, StateT.lift, set, StateT.set]
    rw [← h]; simp

/-- A thread's run reached `tree` (`Sched.settle`): it stops at a sync op, with a new ghost
value and the invariant, or it ends. -/
theorem settle_ok {α β : Type} {t : ThreadId} {Q : β → (ThreadId → γ) → Mem → Nat → Prop}
    {s : Sched.State Tgt α} {n N : Nat} {G : ThreadId → γ} {tree : CoN Tgt (β × Mem) n}
    {ts : Sched.TS Tgt β} {ov : Option β} {s' : Sched.State Tgt α}
    (hs : P.Safe t Q N G tree) (h : Sched.settle t s tree = .ok (ts, ov, s')) :
    s' = { s with mem := s'.mem } ∧ s'.mem.threads.size = N ∧
    ((ov = none ∧ ∃ p g, ts = .paused p ∧ P.inv (upd G t g) s'.mem ∧ P.PausedOk t Q g p) ∨
     (∃ b d, ts = .done ∧ ov = some b ∧ Q b G s'.mem d)) := by
  cases tree with
  | leaf r =>
    rcases r with _ | _ | ⟨b, m⟩
    · simp [Sched.settle] at h
    · simp [Sched.settle] at h
    · simp only [Safe] at hs
      obtain ⟨hN, hq⟩ := hs
      simp only [Sched.settle] at h
      split at h
      · rename_i x m' hc
        have := checkJoined_ok hc; subst this
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨rfl, hN, .inr ⟨b, _, rfl, rfl, hq⟩⟩
      · simp at h
      · simp at h
  | sync op m k =>
    simp only [Safe] at hs
    obtain ⟨hN, g, hi, hk⟩ := hs
    simp only [Sched.settle, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, hN, .inl ⟨rfl, _, g, rfl, hi, hk⟩⟩

/-- In strict mode `settle` gives no error, if an end of the thread satisfies `joinedAll`. -/
theorem settle_safe {α β : Type} {t : ThreadId} {Q : β → (ThreadId → γ) → Mem → Nat → Prop}
    {s : Sched.State Tgt α} {n N : Nat} {G : ThreadId → γ} {tree : CoN Tgt (β × Mem) n}
    (hstr : P.strict = true) (hs : P.Safe t Q N G tree)
    (hQ : ∀ b G m d, Q b G m d → joinedAll t m) (e : Error) :
    Sched.settle t s tree ≠ .error (some e) := by
  cases tree with
  | leaf r =>
    rcases r with _ | _ | ⟨b, m⟩
    · simp [Sched.settle]
    · simp only [Safe] at hs; rw [hstr] at hs; cases hs
    · simp only [Safe] at hs
      simp only [Sched.settle, checkJoined_of (hQ _ _ _ _ hs.2)]
      simp
  | sync op m k => simp [Sched.settle]

variable (P) in
/-- What a turn of thread `t` gives (`turn_ok`): new ghost values `G₂` that agree with `G` on the
threads so far, the same `main`, the same kids or one new kid that keeps the protocol, and the
thread waits at its next op with a new ghost value and the invariant, or it has ended with `Q`. -/
def TurnPost {α β : Type} (t : ThreadId) (Q : β → (ThreadId → γ) → Mem → Nat → Prop)
    (s : Sched.State Tgt α) (G : ThreadId → γ) (ts : Sched.TS Tgt β) (ov : Option β)
    (s' : Sched.State Tgt α) : Prop :=
  ∃ G₂, (∀ u, u < s.kids.size + 1 → G₂ u = G u) ∧ s'.main = s.main ∧
    s'.mem.threads.size = s'.kids.size + 1 ∧
    (s'.kids = s.kids ∨ ∃ nk, s'.kids = s.kids.push nk ∧
      P.KidOk (s.kids.size + 1) (G₂ (s.kids.size + 1)) nk) ∧
    ((ov = none ∧ ∃ p' g, ts = .paused p' ∧ P.inv (upd G₂ t g) s'.mem ∧ P.PausedOk t Q g p') ∨
     (∃ b d, ts = .done ∧ ov = some b ∧ Q b G₂ s'.mem d))

/-- `settle` with no new kid. -/
theorem settle_turnPost {α β : Type} {t : ThreadId} {Q : β → (ThreadId → γ) → Mem → Nat → Prop}
    {s s₁ : Sched.State Tgt α} {G : ThreadId → γ} {n : Nat} {tree : CoN Tgt (β × Mem) n}
    {ts : Sched.TS Tgt β} {ov : Option β} {s' : Sched.State Tgt α}
    (h : Sched.settle t s₁ tree = .ok (ts, ov, s')) (hsafe : P.Safe t Q s₁.mem.threads.size G tree)
    (hsz : s.mem.threads.size = s.kids.size + 1) (hm : s₁.main = s.main) (hk : s₁.kids = s.kids)
    (hs : s₁.mem.threads.size = s.mem.threads.size) :
    P.TurnPost t Q s G ts ov s' := by
  obtain ⟨e, hN, hr⟩ := settle_ok hsafe h
  refine ⟨G, fun _ _ => rfl, ?_, ?_, .inl ?_, hr⟩
  · rw [e]; exact hm
  · rw [e]; show s'.mem.threads.size = s₁.kids.size + 1; rw [hN, hs, hsz, hk]
  · rw [e]; exact hk

/-- The choice of the oracle among `n` options (`Sched.State.choose`) is one of them. -/
theorem choice_lt (n k : Nat) : (if n = 0 then 0 else k % n) < n ∨
    n = 0 ∧ (if n = 0 then 0 else k % n) = 0 := by
  by_cases h : n = 0
  · exact .inr ⟨h, by simp [h]⟩
  · exact .inl (by simp only [h, ↓reduceIte]; exact Nat.mod_lt _ (Nat.pos_of_ne_zero h))

/-- One turn of thread `t` keeps the protocol. -/
theorem turn_ok {α β : Type} (dispatch : Tgt → ConcM Tgt Unit) (fuel : Nat) (o : Nat → Nat)
    {t : ThreadId} {Q : β → (ThreadId → γ) → Mem → Nat → Prop} {s : Sched.State Tgt α}
    {G : ThreadId → γ} {p : Sched.Paused Tgt β} {ts : Sched.TS Tgt β} {ov : Option β}
    {s' : Sched.State Tgt α}
    (hcur : ∀ G m u, P.inv G m → P.inv G { m with current := u })
    (hdisp : ∀ tgt g, P.init tgt = some g → ∀ u G m n, G u = g → P.inv G m →
      P.WP u (dispatch tgt) (P.QKid u) G { m with current := u } n)
    (hinv : P.inv G s.mem) (hsz : s.mem.threads.size = s.kids.size + 1)
    (hp : P.PausedOk t Q (G t) p)
    (hgo : Sched.canGo s t p.op = true) (hdone : ∀ u, s.isDone u = true → P.fin (G u))
    (h : Sched.turn dispatch fuel o t s p = .ok (ts, ov, s')) :
    P.TurnPost t Q s G ts ov s' := by
  obtain ⟨d, op, k⟩ := p
  have hstep := hp G s.mem rfl hinv
  cases op with
  | yield =>
    simp only [Sched.turn] at h
    exact settle_turnPost h hstep hsz rfl rfl rfl
  | choose n =>
    simp only [Sched.turn, Sched.State.choose] at h
    exact settle_turnPost h (hstep _ (choice_lt _ _)) hsz rfl rfl rfl
  | pick count =>
    simp only [Sched.turn, Sched.State.choose] at h
    exact settle_turnPost h (hstep _ (choice_lt _ _)) hsz rfl rfl rfl
  | wake ptr n =>
    simp only [Sched.turn] at h
    exact settle_turnPost h hstep hsz rfl rfl rfl
  | wait ptr e =>
    simp only [Sched.turn] at h
    split at h
    · exact settle_turnPost h hstep.2 hsz rfl rfl rfl
    · split at h
      · rename_i v _
        split at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          refine ⟨G, fun _ _ => rfl, rfl, hsz, .inl rfl, .inl ⟨rfl, _, G t, rfl, ?_, hp⟩⟩
          rw [upd_same]; exact hcur _ _ _ hinv
        · exact settle_turnPost h hstep.2 hsz rfl rfl rfl
      · simp at h
      · simp at h
  | spawn tgt =>
    obtain ⟨g₀, hg₀, hk⟩ := hstep
    simp only [Sched.turn, Sched.State.onMem, bind, Except.bind] at h
    match hf : (Thread.fork.run { s.mem with current := t }).run with
    | none => simp [hf] at h
    | some (.error _) => simp [hf] at h
    | some (.ok (child, m₁)) =>
      simp only [hf] at h
      obtain ⟨hc, hs₁⟩ := fork_ok hf
      have hsafe := hk child m₁ hf
      obtain ⟨e, hN, hr⟩ := settle_ok hsafe h
      have hne : ∀ u, u < s.kids.size + 1 → u ≠ child := by
        intro u hu; rw [hc]; simp only at hsz ⊢; omega
      refine ⟨upd G child g₀, fun u hu => upd_ne G g₀ (hne u hu), ?_, ?_,
        .inr ⟨.paused ⟨fuel, .yield, fun _ m => dispatch tgt fuel m⟩, ?_, ?_⟩, ?_⟩
      · rw [e]
      · rw [e]; simp only [Array.size_push]; rw [hN, hs₁]; simp only at hsz ⊢; omega
      · rw [e]
      · have : s.kids.size + 1 = child := by rw [hc]; simp only at hsz ⊢; omega
        rw [this, upd_self]
        intro G₁ m₁' hg hi
        exact hdisp tgt g₀ hg₀ child G₁ m₁' _ hg hi
      · exact hr
  | join tid =>
    have hf : P.fin (G tid) := hdone tid hgo
    simp only [Sched.turn, Sched.State.onMem, bind, Except.bind] at h
    match hj : ((Thread.join tid).run { s.mem with current := t }).run with
    | none => simp [hj] at h
    | some (.error _) => simp [hj] at h
    | some (.ok ((), m₁)) =>
      simp only [hj] at h
      exact settle_turnPost h ((hstep.2 hf).2 m₁ hj) hsz rfl rfl (join_ok hj : _)


/-- In strict mode a turn gives no error. -/
theorem turn_safe {α β : Type} (dispatch : Tgt → ConcM Tgt Unit) (fuel : Nat) (o : Nat → Nat)
    {t : ThreadId} {Q : β → (ThreadId → γ) → Mem → Nat → Prop} {s : Sched.State Tgt α}
    {G : ThreadId → γ} {p : Sched.Paused Tgt β} (hstr : P.strict = true)
    (hinv : P.inv G s.mem) (hp : P.PausedOk t Q (G t) p)
    (hQ : ∀ b G m d, Q b G m d → joinedAll t m)
    (hgo : Sched.canGo s t p.op = true) (hdone : ∀ u, s.isDone u = true → P.fin (G u))
    (e : Error) : Sched.turn dispatch fuel o t s p ≠ .error (some e) := by
  obtain ⟨d, op, k⟩ := p
  have hstep := hp G s.mem rfl hinv
  intro h
  cases op with
  | yield =>
    simp only [Sched.turn] at h
    exact settle_safe hstr hstep hQ e h
  | choose n =>
    simp only [Sched.turn, Sched.State.choose] at h
    exact settle_safe hstr (hstep _ (choice_lt _ _)) hQ e h
  | pick count =>
    simp only [Sched.turn, Sched.State.choose] at h
    exact settle_safe hstr (hstep _ (choice_lt _ _)) hQ e h
  | wake ptr n =>
    simp only [Sched.turn] at h
    exact settle_safe hstr hstep hQ e h
  | wait ptr e' => exact hstep.1 hstr
  | spawn tgt =>
    obtain ⟨g₀, hg₀, hk⟩ := hstep
    simp only [Sched.turn, Sched.State.onMem, bind, Except.bind] at h
    match hf : (Thread.fork.run { s.mem with current := t }).run with
    | none =>
      simp [Thread.fork, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, set, StateT.set, pure, StateT.pure, ExceptT.pure, ExceptT.mk, ExceptT.run,
        ExceptT.bind, ExceptT.bindCont, Option.bind] at hf
    | some (.error _) =>
      simp [Thread.fork, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, set, StateT.set, pure, StateT.pure, ExceptT.pure, ExceptT.mk, ExceptT.run,
        ExceptT.bind, ExceptT.bindCont, Option.bind] at hf
    | some (.ok (child, m₁)) =>
      simp only [hf] at h
      exact settle_safe hstr (hk child m₁ hf) hQ e h
  | join tid =>
    have hf : P.fin (G tid) := hdone tid hgo
    obtain ⟨m₁, hj⟩ := (hstep.2 hf).1 hstr
    simp only [Sched.turn, Sched.State.onMem, bind, Except.bind, hj] at h
    exact settle_safe hstr ((hstep.2 hf).2 m₁ hj) hQ e h

variable (P) in
/-- The state between two turns keeps the protocol with the ghost values `G`: the invariant
holds, the kids are threads `1 … kids.size`, `main` waits and keeps the protocol with the
post `QM`, and each kid keeps it or has ended. -/
structure SInv {α : Type} (QM : α → (ThreadId → γ) → Mem → Nat → Prop) (s : Sched.State Tgt α)
    (G : ThreadId → γ) : Prop where
  inv : P.inv G s.mem
  size : s.mem.threads.size = s.kids.size + 1
  main : ∃ p, s.main = .paused p ∧ P.PausedOk 0 QM (G 0) p
  kids : ∀ i (h : i < s.kids.size), P.KidOk (i + 1) (G (i + 1)) s.kids[i]

/-- A thread in `ready` waits and can go on. -/
theorem mem_ready {α : Type} {s : Sched.State Tgt α} {t : ThreadId} (h : t ∈ s.ready) :
    (t = 0 ∧ ∃ p, s.main = .paused p ∧ Sched.canGo s 0 p.op = true) ∨
    (∃ i p, t = i + 1 ∧ s.kids[i]? = some (.paused p) ∧ Sched.canGo s t p.op = true) := by
  unfold Sched.State.ready at h
  rw [Array.mem_append] at h
  rcases h with h | h
  · left
    split at h
    · rename_i p hp
      split at h
      · rename_i hc
        simp only [Array.mem_singleton] at h
        exact ⟨h, p, hp, hc⟩
      · simp at h
    · simp at h
  · right
    rw [Array.mem_filterMap] at h
    obtain ⟨⟨ts, i⟩, hmem, hf⟩ := h
    rw [Array.mem_zipIdx_iff_getElem?] at hmem
    cases ts with
    | paused p =>
      simp only at hf
      split at hf
      · rename_i hc
        simp only [Option.some.injEq] at hf
        subst hf
        exact ⟨i, p, rfl, hmem, hc⟩
      · simp at hf
    | done => simp at hf

theorem SInv.done {α : Type} {QM : α → (ThreadId → γ) → Mem → Nat → Prop}
    {s : Sched.State Tgt α} {G : ThreadId → γ} (hs : P.SInv QM s G) :
    ∀ u, s.isDone u = true → P.fin (G u) := by
  intro u hu
  unfold Sched.State.isDone at hu
  split at hu
  · obtain ⟨p, hp, _⟩ := hs.main
    rw [hp] at hu; simp at hu
  · rename_i hu0
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hu0
    split at hu
    · rename_i hk
      simp only [Nat.succ_sub_one] at hk
      rw [Array.getElem?_eq_some_iff] at hk
      obtain ⟨hlt, he⟩ := hk
      have := hs.kids j hlt
      rw [he] at this
      exact this
    · simp at hu

/-- The kids after a turn of thread `t` keep the protocol, except thread `t` itself. -/
theorem kids_after {kids kids₂ : Array (Sched.TS Tgt Unit)} {G G₂ G' : ThreadId → γ}
    {t : ThreadId} (hk : ∀ i (h : i < kids.size), P.KidOk (i + 1) (G (i + 1)) kids[i])
    (hagree : ∀ u, u < kids.size + 1 → G₂ u = G u)
    (hkids : kids₂ = kids ∨ ∃ nk, kids₂ = kids.push nk ∧
      P.KidOk (kids.size + 1) (G₂ (kids.size + 1)) nk)
    (hG' : ∀ u, u ≠ t → G' u = G₂ u) :
    ∀ i (h : i < kids₂.size), i + 1 ≠ t → P.KidOk (i + 1) (G' (i + 1)) kids₂[i] := by
  intro i hi hne
  rw [hG' _ hne]
  rcases hkids with rfl | ⟨nk, rfl, hnk⟩
  · rw [hagree _ (by omega)]; exact hk i hi
  · rw [Array.getElem_push]
    split
    · rename_i hlt; rw [hagree _ (by omega)]; exact hk i hlt
    · rename_i hlt
      simp only [Array.size_push] at hi
      have : i = kids.size := by omega
      subst this; exact hnk

variable (P) in
/-- A result of a run: an `ok` result satisfies `QM`; in strict mode it is not an error. -/
def Good {α : Type} (QM : α → (ThreadId → γ) → Mem → Nat → Prop) (r : Except Error (α × Mem)) :
    Prop :=
  (∀ v m, r = .ok (v, m) → ∃ G d, QM v G m d) ∧ (P.strict = true → ∀ e, r ≠ .error e)

/-- In strict mode a waiting thread is at a join of a later thread, or can go on. -/
theorem paused_info {β : Type} {t : ThreadId} {Q : β → (ThreadId → γ) → Mem → Nat → Prop} {g : γ}
    {p : Sched.Paused Tgt β} {G : ThreadId → γ} {m : Mem} (hstr : P.strict = true)
    (hp : P.PausedOk t Q g p) (hg : G t = g) (hi : P.inv G m) :
    (∀ tid, p.op = .join tid → t < tid ∧ tid < m.threads.size) ∧
      ∀ ptr e, p.op ≠ .wait ptr e := by
  obtain ⟨d, op, k⟩ := p
  have hs := hp G m hg hi
  cases op with
  | join tid' => exact ⟨fun tid h => (by cases h; exact hs.1 hstr), fun _ _ h => (by cases h)⟩
  | wait ptr e => exact (hs.1 hstr).elim
  | yield | choose | pick | spawn | wake =>
    exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h)⟩

/-- A waiting thread that can go on is in `ready`. -/
theorem ready_of_main {α : Type} {s : Sched.State Tgt α} {p : Sched.Paused Tgt α}
    (hp : s.main = .paused p) (hc : Sched.canGo s 0 p.op = true) : 0 ∈ s.ready := by
  unfold Sched.State.ready
  rw [Array.mem_append]; left
  simp [hp, hc]

theorem ready_of_kid {α : Type} {s : Sched.State Tgt α} {i : Nat} {p : Sched.Paused Tgt Unit}
    (hp : s.kids[i]? = some (.paused p)) (hc : Sched.canGo s (i + 1) p.op = true) :
    i + 1 ∈ s.ready := by
  unfold Sched.State.ready
  rw [Array.mem_append]; right
  rw [Array.mem_filterMap]
  refine ⟨(.paused p, i), Array.mem_zipIdx_iff_getElem?.mpr hp, ?_⟩
  simp [hc]

/-- **No deadlock.** In strict mode a state that keeps the protocol has a thread that can go on:
a waiting thread that cannot go on is at a join of a later thread that has not ended, so it
waits too; the thread ids go up, so this ends. -/
theorem ready_ne {α : Type} {QM : α → (ThreadId → γ) → Mem → Nat → Prop}
    {s : Sched.State Tgt α} {G : ThreadId → γ} (hstr : P.strict = true) (hs : P.SInv QM s G)
    (hre : s.ready = #[]) : False := by
  -- `B t`: thread `t` waits at an op that it cannot go on at, and that is not a futex wait.
  let B : ThreadId → Prop := fun t => ∃ op : SyncOp Tgt, Sched.canGo s t op = false ∧
    (∀ tid, op = .join tid → t < tid ∧ tid < s.mem.threads.size) ∧ ∀ ptr e, op ≠ .wait ptr e
  have hkid : ∀ i p, s.kids[i]? = some (.paused p) → B (i + 1) := by
    intro i p hp
    obtain ⟨hlt, he⟩ := Array.getElem?_eq_some_iff.mp hp
    have hok := hs.kids i hlt
    rw [he] at hok
    obtain ⟨hj, hw⟩ := paused_info hstr hok rfl hs.inv
    refine ⟨p.op, ?_, hj, hw⟩
    cases hc : Sched.canGo s (i + 1) p.op
    · rfl
    · have := ready_of_kid hp hc; rw [hre] at this; simp at this
  have hstep : ∀ t, B t → ∃ t', t < t' ∧ t' < s.mem.threads.size ∧ B t' := by
    rintro t ⟨op, hc, hj, hw⟩
    cases op with
    | join tid =>
      obtain ⟨h1, h2⟩ := hj tid rfl
      refine ⟨tid, h1, h2, ?_⟩
      have htid : tid ≠ 0 := by unfold ThreadId at *; omega
      simp only [Sched.canGo] at hc
      unfold Sched.State.isDone at hc
      simp only [htid, ↓reduceIte] at hc
      have hlt : tid - 1 < s.kids.size := by have := hs.size; unfold ThreadId at *; omega
      have hs' : tid - 1 + 1 = tid := by unfold ThreadId at *; omega
      cases hk : s.kids[tid - 1]? with
      | none => rw [Array.getElem?_eq_getElem hlt] at hk; cases hk
      | some ts =>
        cases ts with
        | done => rw [hk] at hc; cases hc
        | paused p => exact hs' ▸ hkid _ _ hk
    | wait ptr e => exact (hw ptr e rfl).elim
    | yield | choose | pick | spawn | wake => simp [Sched.canGo] at hc
  have hall : ∀ d t, s.mem.threads.size - t = d → t < s.mem.threads.size → B t → False := by
    intro d
    induction d using Nat.strongRecOn with
    | _ d ih =>
      intro t hd ht hb
      obtain ⟨t', h1, h2, hb'⟩ := hstep t hb
      exact ih _ (by unfold ThreadId at *; omega) t' rfl h2 hb'
  obtain ⟨p, hp, hok⟩ := hs.main
  obtain ⟨hj, hw⟩ := paused_info hstr hok rfl hs.inv
  refine hall _ 0 rfl (by have := hs.size; omega) ⟨p.op, ?_, hj, hw⟩
  cases hc : Sched.canGo s 0 p.op
  · rfl
  · have := ready_of_main hp hc; rw [hre] at this; simp at this

/-- Up to `fuel` turns from a state that keeps the protocol: a result of `main` is `Good`. -/
theorem go_spec {α : Type} (dispatch : Tgt → ConcM Tgt Unit) (o : Nat → Nat)
    {QM : α → (ThreadId → γ) → Mem → Nat → Prop}
    (hcur : ∀ G m u, P.inv G m → P.inv G { m with current := u })
    (hdisp : ∀ tgt g, P.init tgt = some g → ∀ u G m n, G u = g → P.inv G m →
      P.WP u (dispatch tgt) (P.QKid u) G { m with current := u } n)
    (hQM : P.strict = true → ∀ v G m d, QM v G m d → joinedAll 0 m) :
    ∀ (fuel : Nat) (s : Sched.State Tgt α) (G : ThreadId → γ), P.SInv QM s G →
      ∀ {r}, (Sched.go dispatch o fuel s).1 = some r → P.Good QM r := by
  intro fuel
  induction fuel with
  | zero => intro s G _ r h; simp [Sched.go] at h
  | succ fuel ih =>
    intro s G hs r h
    simp only [Sched.go, Sched.State.choose] at h
    split at h
    · rename_i hemp
      have hrun : s.anyRunning = true := by
        obtain ⟨p, hp, -⟩ := hs.main; simp [Sched.State.anyRunning, hp]
      simp only [hrun, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact ⟨fun _ _ h => (by cases h),
        fun hstr _ _ => ready_ne hstr hs (Array.isEmpty_iff.mp hemp)⟩
    · rename_i hne
      have hpos : 0 < s.ready.size := by
        rw [Array.isEmpty_iff_size_eq_zero] at hne; omega
      simp only [Nat.pos_iff_ne_zero.mp hpos, ite_false] at h
      have hmem : s.ready[o s.step % s.ready.size]! ∈ s.ready := by
        rw [getElem!_pos s.ready _ (Nat.mod_lt _ hpos)]; exact Array.getElem_mem _
      generalize s.ready[o s.step % s.ready.size]! = t at h hmem
      -- The state after the choice: only `step` and `trace` differ.
      generalize hs₁ : ({ s with step := s.step + 1, trace := s.trace.push s.ready.size } :
        Sched.State Tgt α) = s₁ at h
      have hS₁ : P.SInv QM s₁ G := by rw [← hs₁]; exact ⟨hs.inv, hs.size, hs.main, hs.kids⟩
      have hm₁ : s₁.main = s.main := by rw [← hs₁]
      have hk₁ : s₁.kids = s.kids := by rw [← hs₁]
      have hgo₁ : ∀ t (op : SyncOp Tgt), Sched.canGo s t op = true → Sched.canGo s₁ t op = true := by
        intro t op h; rw [← hs₁]; exact h
      split at h
      · -- `main`'s turn
        rename_i ht0
        subst ht0
        obtain ⟨p₀, hp₀, hok⟩ := hs.main
        rw [hp₀] at h
        have hgo : Sched.canGo s₁ 0 p₀.op = true := by
          rcases mem_ready hmem with ⟨-, p, hp, hgo⟩ | ⟨i, _, hi, -⟩
          · rw [hp₀] at hp; cases hp; exact hgo₁ _ _ hgo
          · exact absurd hi.symm (Nat.succ_ne_zero i)
        simp only at h
        split at h
        · rename_i e he
          cases e with
          | none => simp [Sched.outOf] at h
          | some e' =>
            simp only [Sched.outOf, Option.some.injEq] at h
            subst h
            exact ⟨fun _ _ h => (by cases h), fun hstr _ _ =>
              turn_safe dispatch fuel o hstr hS₁.inv hok (hQM hstr) hgo hS₁.done e' he⟩
        · rename_i ts v' s₂ ht
          obtain ⟨G₂, -, -, -, -, hr⟩ := turn_ok dispatch fuel o hcur hdisp hS₁.inv hS₁.size
            hok hgo hS₁.done ht
          simp only [Option.some.injEq] at h
          subst h
          refine ⟨fun v m h => ?_, fun _ _ h => (by cases h)⟩
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rcases hr with ⟨hov, -⟩ | ⟨b, d, -, hov, hq⟩
          · cases hov
          · cases hov; exact ⟨G₂, d, hq⟩
        · rename_i ts s₂ ht
          obtain ⟨G₂, hagree, hmain, hsize, hkids, hr⟩ := turn_ok dispatch fuel o hcur hdisp
            hS₁.inv hS₁.size hok hgo hS₁.done ht
          rcases hr with ⟨-, p', g, rfl, hi, hpk⟩ | ⟨b, d, -, hov, -⟩
          · refine ih { s₂ with main := .paused p' } (upd G₂ 0 g)
              ⟨hi, hsize, ⟨p', rfl, by rw [upd_self]; exact hpk⟩, ?_⟩ h
            intro i hi'
            exact kids_after hS₁.kids hagree hkids (fun u hu => upd_ne G₂ g hu) i hi' (by omega)
          · cases hov
      · -- a kid's turn
        rename_i ht0
        split at h
        · rename_i p hk
          rcases mem_ready hmem with ⟨h0, -⟩ | ⟨i, p', rfl, hi, hgo⟩
          · exact absurd h0 ht0
          simp only [Nat.add_sub_cancel] at hk
          rw [hk] at hi; cases hi
          rw [← hk₁, Array.getElem?_eq_some_iff] at hk
          obtain ⟨hlt, he⟩ := hk
          have hok := hS₁.kids i hlt
          rw [he] at hok
          split at h
          · rename_i e he
            cases e with
            | none => simp [Sched.outOf] at h
            | some e' =>
              simp only [Sched.outOf, Option.some.injEq] at h
              subst h
              exact ⟨fun _ _ h => (by cases h), fun hstr _ _ =>
                turn_safe (s := s₁) dispatch fuel o hstr hS₁.inv hok
                  (fun _ _ _ _ ⟨_, _, _, hj⟩ => hj hstr) (hgo₁ _ _ hgo) hS₁.done e' he⟩
          · rename_i ts ov s₂ ht
            obtain ⟨G₂, hagree, hmain, hsize, hkids, hr⟩ := turn_ok (s := s₁) dispatch fuel o hcur
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
            rcases hr with ⟨-, p', g, rfl, hi, hpk⟩ | ⟨b, d, rfl, -, g, hi, hfin⟩
            · exact ih { s₂ with kids := s₂.kids.set! i (.paused p') } (upd G₂ (i + 1) g)
                ⟨hi, by simp [hsize], hmain' g, hkids' g (.paused p') hpk⟩ h
            · exact ih { s₂ with kids := s₂.kids.set! i .done } (upd G₂ (i + 1) g)
                ⟨hi, by simp [hsize], hmain' g, hkids' g .done hfin.1⟩ h
        · simp at h

/-- **Soundness.** If `main` keeps the protocol from the start with the post `QM`, and each
spawn target that the protocol allows keeps it with the post `QKid`, then every result of a
run, under every schedule `o` and every `fuel`, is `Good`: an `ok` result satisfies `QM`, and in
strict mode no run gives an error (no data race, no deadlock, no panic). -/
theorem run_spec {α : Type} (dispatch : Tgt → ConcM Tgt Unit) {main : ConcM Tgt α} {m0 : Mem}
    {QM : α → (ThreadId → γ) → Mem → Nat → Prop} (G0 : ThreadId → γ)
    (hcur : ∀ G m u, P.inv G m → P.inv G { m with current := u })
    (hdisp : ∀ tgt g, P.init tgt = some g → ∀ u G m n, G u = g → P.inv G m →
      P.WP u (dispatch tgt) (P.QKid u) G { m with current := u } n)
    (hQM : P.strict = true → ∀ v G m d, QM v G m d → joinedAll 0 m)
    (hsize : m0.threads.size = 1)
    (hmain : ∀ n, P.WP 0 main QM G0 { m0 with current := 0 } n)
    {fuel : Nat} {o : Nat → Nat} {r : Except Error (α × Mem)}
    (h : (Sched.run dispatch fuel o main m0).run = some r) : P.Good QM r := by
  simp only [Sched.run, Sched.runTrace, ExceptT.run, ExceptT.mk] at h
  have hsafe : P.Safe 0 QM 1 G0 (main fuel { m0 with current := 0 }) := by
    have := hmain fuel; unfold WP at this; rwa [show ({ m0 with current := 0 } : Mem).threads.size = 1
      from hsize] at this
  split at h
  · rename_i e he
    cases e with
    | none => simp [Sched.outOf] at h
    | some e' =>
      simp only [Sched.outOf, Option.some.injEq] at h
      subst h
      exact ⟨fun _ _ h => (by cases h), fun hstr _ _ => settle_safe hstr hsafe (hQM hstr) e' he⟩
  · rename_i ts v' s₁ hs
    obtain ⟨-, -, hr⟩ := settle_ok hsafe hs
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨fun v m h => ?_, fun _ _ h => (by cases h)⟩
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rcases hr with ⟨hov, -⟩ | ⟨b, d, -, hov, hq⟩
    · cases hov
    · cases hov; exact ⟨G0, d, hq⟩
  · rename_i ts s₁ hs
    obtain ⟨e, hN, hr⟩ := settle_ok hsafe hs
    rcases hr with ⟨-, p, g, rfl, hi, hpk⟩ | ⟨b, d, -, hov, -⟩
    · refine go_spec dispatch o hcur hdisp hQM fuel { s₁ with main := .paused p } (upd G0 0 g)
        ⟨hi, ?_, ⟨p, rfl, by rw [upd_self]; exact hpk⟩, ?_⟩ h
      · show s₁.mem.threads.size = s₁.kids.size + 1
        rw [hN, e]; rfl
      · intro i hi
        have : s₁.kids.size = 0 := by rw [e]; rfl
        simp only [this] at hi; omega
    · cases hov

/-- Partial correctness: every `ok` result of a run satisfies `QM`. -/
theorem run_sound {α : Type} (dispatch : Tgt → ConcM Tgt Unit) {main : ConcM Tgt α} {m0 : Mem}
    {QM : α → (ThreadId → γ) → Mem → Nat → Prop} (G0 : ThreadId → γ)
    (hcur : ∀ G m u, P.inv G m → P.inv G { m with current := u })
    (hdisp : ∀ tgt g, P.init tgt = some g → ∀ u G m n, G u = g → P.inv G m →
      P.WP u (dispatch tgt) (P.QKid u) G { m with current := u } n)
    (hQM : P.strict = true → ∀ v G m d, QM v G m d → joinedAll 0 m)
    (hsize : m0.threads.size = 1)
    (hmain : ∀ n, P.WP 0 main QM G0 { m0 with current := 0 } n)
    {fuel : Nat} {o : Nat → Nat} {v : α} {m : Mem}
    (h : (Sched.run dispatch fuel o main m0).run = some (.ok (v, m))) :
    ∃ G d, QM v G m d :=
  (run_spec dispatch G0 hcur hdisp hQM hsize hmain h).1 v m rfl

/-- **No error.** In strict mode no run, under any schedule, gives an error. -/
theorem run_safe {α : Type} (dispatch : Tgt → ConcM Tgt Unit) {main : ConcM Tgt α} {m0 : Mem}
    {QM : α → (ThreadId → γ) → Mem → Nat → Prop} (G0 : ThreadId → γ) (hstr : P.strict = true)
    (hcur : ∀ G m u, P.inv G m → P.inv G { m with current := u })
    (hdisp : ∀ tgt g, P.init tgt = some g → ∀ u G m n, G u = g → P.inv G m →
      P.WP u (dispatch tgt) (P.QKid u) G { m with current := u } n)
    (hQM : ∀ v G m d, QM v G m d → joinedAll 0 m)
    (hsize : m0.threads.size = 1)
    (hmain : ∀ n, P.WP 0 main QM G0 { m0 with current := 0 } n)
    {fuel : Nat} {o : Nat → Nat} {e : Error} :
    (Sched.run dispatch fuel o main m0).run ≠ some (.error e) := fun h =>
  (run_spec dispatch G0 hcur hdisp (fun _ => hQM) hsize hmain h).2 hstr e rfl

end Proto
end Conc
end Zig
