import ZigLean.Conc.Spec.Sys

/-!
# The futex contract (`FutexSpec`)

What std 0.16.0 code may assume of `Threaded.Thread.futexWaitInner`/`futexWake` (and of the
`futexWait*`/`futexWake` slots of an `Io`), stated over an abstract futex so that the OS rows of
T2 (`os.linux.futex_4arg`/`futex_3arg`, `__ulock_wait2`/`__ulock_wake`, premises OSF-01/02)
instantiate it. `docs/thread-specs.md` has the design.

**Signature** (`Futex M A`). `M` is the memory the futex words live in, `A` the addresses of
the words. `W : M → A → Option (BitVec 32)` is the atomic view of the `u32` at an address
(`none`: no valid word there); it belongs to the memory model, not to the futex. The futex has
its own state `F` and an abstract **queue** view `queue : F → List (Tid × A)`: the threads asleep
at each address. Its operations are atomic steps, as relations (an implementation may be
nondeterministic):

* `wait t a e tm m f r f'`: the first step of `wait(a, e)` by thread `t` (`tm`: with a
  timeout) in memory `m`: `r = none`, `t` went to sleep; `r = some ret`, it returned at once.
* `resume t tm f r f'`: a thread that went to sleep returns with `r`.
* `wake t a n f k f'`: `wake(a, n)` woke `k` threads.

None of them gets or changes `M`: a futex op **only reads the word**, and it adds no
happens-before edge (no view moves through it; `ZigLean/Conc/Spec/Mutex.lean`).

**Contract** (`FutexSpec W X`).

| clause | statement |
|---|---|
| `init` | the queue starts empty |
| `wait_word` | `wait` reads the word atomically: it is a valid word `v`, and `t` sleeps only if `v = e` (the kernel's recheck) |
| `wait_local` | `wait` depends on the memory only through that word |
| `wait_sleep` | a sleeping `wait` adds exactly `(t, a)` to the queue |
| `wait_ret` | a returning `wait` leaves the queue; `timeout` only with a timeout. `woken`, `again` and `intr` are always allowed: a **spurious** return |
| `resume` | a resumed thread leaves the queue (it may still have been in it: spurious, `EINTR`, timeout) |
| `wake` | wakes an **arbitrary** set of exactly `min n c` distinct threads asleep at `a` (`c` of them), and returns their number |
| `wait_total`, `resume_total`, `wake_total` | progress: `wait` on a valid word by a thread that is not asleep can always step; a thread no longer in the queue can always resume; `wake` can always step |

A thread asleep in the queue need not be able to resume: only a wake is sure to make it go on.
Clients therefore re-check the word after every return (std's loops) and need a wake for
progress. `ZigLean/Conc/Spec/FutexToy.lean` has a FIFO futex and an always-spurious futex that
satisfy the contract, and a futex whose wake never wakes and one whose wait does not recheck,
which do not.
-/

namespace Zig
namespace Spec

/-- What a futex wait returned. Std treats every value as a return and re-checks. -/
inductive WaitRet where
  /-- A wake made the thread go on (Linux `0`). -/
  | woken
  /-- The word was not the expected value (`EAGAIN`). -/
  | again
  /-- Interrupted or spurious (`EINTR`; a pending cancel signal, OSG-01). -/
  | intr
  /-- The timeout expired (`ETIMEDOUT`); only for a wait with a timeout. -/
  | timeout
  deriving DecidableEq, Repr

/-- The futex queue: the threads asleep, each with the address it sleeps at. -/
abbrev Queue (A : Type) := List (Tid × A)

namespace Queue

variable {A : Type}

/-- The threads asleep at `a`, in queue order. -/
def waitersAt [DecidableEq A] (q : Queue A) (a : A) : List Tid := (q.filter fun x => x.2 == a).map (·.1)

/-- Thread `t` is asleep. -/
def has (q : Queue A) (t : Tid) : Bool := q.any (·.1 == t)

/-- Each thread is asleep at most once. -/
def WF (q : Queue A) : Prop := (q.map (·.1)).Nodup

/-- `q` without the threads `ws`. -/
def drop (q : Queue A) (ws : List Tid) : Queue A := q.filter fun x => !ws.contains x.1

theorem has_eq_false {q : Queue A} {t : Tid} : q.has t = false ↔ ∀ a, (t, a) ∉ q := by
  unfold has
  constructor
  · intro h a hm
    have := List.any_eq_false.mp h _ hm
    simp at this
  · intro h
    refine List.any_eq_false.mpr fun x hx he => ?_
    have : x.1 = t := by simpa using he
    exact h x.2 (by rw [← this]; exact hx)

theorem has_eq_true {q : Queue A} {t : Tid} : q.has t = true ↔ ∃ a, (t, a) ∈ q := by
  unfold has
  rw [List.any_eq_true]
  constructor
  · rintro ⟨x, hx, he⟩
    have : x.1 = t := by simpa using he
    exact ⟨x.2, by rw [← this]; exact hx⟩
  · rintro ⟨a, ha⟩
    exact ⟨(t, a), ha, by simp⟩

theorem mem_waitersAt [DecidableEq A] {q : Queue A} {a : A} {u : Tid} : u ∈ q.waitersAt a ↔ (u, a) ∈ q := by
  unfold waitersAt
  simp only [List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨x, ⟨hx, he⟩, rfl⟩
    rw [← he]; exact hx
  · intro h; exact ⟨(u, a), ⟨h, rfl⟩, rfl⟩

theorem mem_drop {q : Queue A} {ws : List Tid} {x : Tid × A} :
    x ∈ q.drop ws ↔ x ∈ q ∧ x.1 ∉ ws := by
  unfold drop
  simp [List.mem_filter]

theorem drop_nil (q : Queue A) : q.drop [] = q := by
  unfold drop; simp

/-- Dropping a thread that is not asleep changes nothing. -/
theorem drop_of_not_has {q : Queue A} {t : Tid} (h : q.has t = false) : q.drop [t] = q := by
  unfold drop
  refine List.filter_eq_self.mpr fun x hx => ?_
  have hne : x.1 ≠ t := fun e => has_eq_false.mp h x.2 (by rw [← e]; exact hx)
  simp [hne]

theorem WF.perm {q q' : Queue A} (h : q.WF) (hp : q'.Perm q) : q'.WF :=
  ((hp.map _).nodup_iff).mpr h

theorem WF.sublist {q q' : Queue A} (h : q.WF) (hs : q'.Sublist q) : q'.WF :=
  List.Nodup.sublist (hs.map _) h

theorem WF.drop {q : Queue A} (h : q.WF) (ws : List Tid) : (q.drop ws).WF :=
  h.sublist List.filter_sublist

theorem WF.push {q : Queue A} (h : q.WF) {t : Tid} (ht : q.has t = false) (a : A) :
    (q ++ [(t, a)]).WF := by
  unfold WF
  rw [List.map_append]
  refine (List.perm_append_comm.nodup_iff).mpr ?_
  simp only [List.map_cons, List.map_nil, List.singleton_append, List.nodup_cons]
  refine ⟨fun hm => ?_, h⟩
  obtain ⟨x, hx, he⟩ := List.mem_map.mp hm
  exact has_eq_false.mp ht x.2 (by rw [← he]; exact hx)

theorem WF.nil : Queue.WF ([] : Queue A) := List.nodup_nil

theorem waitersAt_nodup [DecidableEq A] {q : Queue A} (h : q.WF) (a : A) : (q.waitersAt a).Nodup :=
  List.Nodup.sublist (List.filter_sublist.map _) h

/-- In a well-formed queue a thread sleeps at one address. -/
theorem WF.unique {q : Queue A} (h : q.WF) {t : Tid} {a b : A} (ha : (t, a) ∈ q) (hb : (t, b) ∈ q) :
    a = b := by
  unfold WF at h
  induction q with
  | nil => cases ha
  | cons x q ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at h
    rcases List.mem_cons.mp ha with ea | ha' <;> rcases List.mem_cons.mp hb with eb | hb'
    · rw [← ea] at eb; cases eb; rfl
    · exact absurd ⟨(t, b), hb', by rw [← ea]⟩ h.1
    · exact absurd ⟨(t, a), ha', by rw [← eb]⟩ h.1
    · exact ih h.2 ha' hb'

end Queue

/-- The abstract futex signature (module doc): what an implementation provides. -/
structure Futex (M A : Type) where
  /-- The futex's own state (T2: the scheduler's queue, the pending interrupts). -/
  F : Type
  init : F → Prop
  /-- The threads asleep, with their addresses. -/
  queue : F → Queue A
  /-- The first, atomic step of `wait(a, e)` (`tm`: with a timeout) by `t` in memory `m`:
  `none`: `t` sleeps; `some r`: it returns `r`. -/
  wait : Tid → A → BitVec 32 → Bool → M → F → Option WaitRet → F → Prop
  /-- A thread that went to sleep returns. -/
  resume : Tid → Bool → F → WaitRet → F → Prop
  /-- `wake(a, n)` by `t`: the number of threads woken. -/
  wake : Tid → A → Nat → F → Nat → F → Prop

variable {M A : Type} [DecidableEq A]

/-- The futex contract (module doc). `W m a` is the atomic `u32` at `a` in `m`. -/
structure FutexSpec (W : M → A → Option (BitVec 32)) (X : Futex M A) : Prop where
  init : ∀ f, X.init f → X.queue f = []
  wait_word : ∀ t a e tm m f r f', X.wait t a e tm m f r f' →
    ∃ v, W m a = some v ∧ (r = none → v = e)
  wait_local : ∀ t a e tm m m' f r f', W m a = W m' a →
    X.wait t a e tm m f r f' → X.wait t a e tm m' f r f'
  wait_sleep : ∀ t a e tm m f f', X.wait t a e tm m f none f' →
    (X.queue f').Perm (X.queue f ++ [(t, a)])
  wait_ret : ∀ t a e tm m f r f', X.wait t a e tm m f (some r) f' →
    (X.queue f').Perm (X.queue f) ∧ (r = .timeout → tm = true)
  resume : ∀ t tm f r f', X.resume t tm f r f' →
    (X.queue f').Perm ((X.queue f).drop [t]) ∧ (r = .timeout → tm = true)
  wake : ∀ t a n f k f', (X.queue f).WF → X.wake t a n f k f' →
    ∃ ws : List Tid, ws.Nodup ∧ (∀ u ∈ ws, (u, a) ∈ X.queue f) ∧
      ws.length = min n ((X.queue f).waitersAt a).length ∧ k = ws.length ∧
      (X.queue f').Perm ((X.queue f).drop ws)
  wait_total : ∀ t a e tm m f v, W m a = some v → (X.queue f).has t = false →
    ∃ r f', X.wait t a e tm m f r f'
  resume_total : ∀ t tm f, (X.queue f).has t = false → ∃ r f', X.resume t tm f r f'
  wake_total : ∀ t a n f, (X.queue f).WF → ∃ k f', X.wake t a n f k f'

namespace FutexSpec

variable {W : M → A → Option (BitVec 32)} {X : Futex M A} (h : FutexSpec W X)
include h

/-! ## The lemma library for clients -/

/-- A sleeping wait read the expected value. -/
theorem sleep_word {t a e tm m f f'} (hw : X.wait t a e tm m f none f') : W m a = some e := by
  obtain ⟨v, hv, he⟩ := h.wait_word _ _ _ _ _ _ _ _ hw
  rw [hv, he rfl]

/-- The queue stays well formed: a wait by a thread that is not asleep. -/
theorem wf_wait {t a e tm m f r f'} (hq : (X.queue f).WF) (ht : (X.queue f).has t = false)
    (hw : X.wait t a e tm m f r f') : (X.queue f').WF := by
  cases r with
  | none => exact (hq.push ht a).perm (h.wait_sleep _ _ _ _ _ _ _ hw)
  | some r => exact hq.perm (h.wait_ret _ _ _ _ _ _ _ _ hw).1

theorem wf_resume {t tm f r f'} (hq : (X.queue f).WF) (hr : X.resume t tm f r f') :
    (X.queue f').WF :=
  (hq.drop _).perm (h.resume _ _ _ _ _ hr).1

theorem wf_wake {t a n f k f'} (hq : (X.queue f).WF) (hw : X.wake t a n f k f') :
    (X.queue f').WF := by
  obtain ⟨ws, -, -, -, -, hp⟩ := h.wake _ _ _ _ _ _ hq hw
  exact (hq.drop _).perm hp

/-- Who is asleep after a wait. -/
theorem mem_wait {t a e tm m f r f'} (hw : X.wait t a e tm m f r f') (x : Tid × A) :
    x ∈ X.queue f' ↔ x ∈ X.queue f ∨ (r = none ∧ x = (t, a)) := by
  cases r with
  | none =>
    rw [(h.wait_sleep _ _ _ _ _ _ _ hw).mem_iff, List.mem_append]
    simp
  | some r =>
    rw [(h.wait_ret _ _ _ _ _ _ _ _ hw).1.mem_iff]
    simp

/-- Who is asleep after a resume of `t`. -/
theorem mem_resume {t tm f r f'} (hr : X.resume t tm f r f') (x : Tid × A) :
    x ∈ X.queue f' ↔ x ∈ X.queue f ∧ x.1 ≠ t := by
  rw [(h.resume _ _ _ _ _ hr).1.mem_iff, Queue.mem_drop]
  simp

/-- A wake only removes threads. -/
theorem mem_wake {t a n f k f'} (hq : (X.queue f).WF) (hw : X.wake t a n f k f') {x : Tid × A}
    (hx : x ∈ X.queue f') : x ∈ X.queue f := by
  obtain ⟨ws, -, -, -, -, hp⟩ := h.wake _ _ _ _ _ _ hq hw
  exact (Queue.mem_drop.mp (hp.mem_iff.mp hx)).1

/-- A wake removes threads only at its address. -/
theorem wake_keeps {t a n f k f'} (hq : (X.queue f).WF) (hw : X.wake t a n f k f') {x : Tid × A}
    (hx : x ∈ X.queue f) (hb : x.2 ≠ a) : x ∈ X.queue f' := by
  obtain ⟨ws, -, hws, -, -, hp⟩ := h.wake _ _ _ _ _ _ hq hw
  refine hp.mem_iff.mpr (Queue.mem_drop.mpr ⟨hx, fun hm => hb ?_⟩)
  exact hq.unique (show (x.1, x.2) ∈ X.queue f from hx) (hws _ hm)

/-- **A wake of at least one thread at an address where some thread sleeps wakes one**: some
thread asleep at `a` is no longer asleep. This is what a wake that never wakes violates. -/
theorem wake_one {t a n f k f'} (hq : (X.queue f).WF) (hw : X.wake t a n f k f') (hn : 1 ≤ n)
    {u : Tid} (hu : (u, a) ∈ X.queue f) :
    1 ≤ k ∧ ∃ v, (v, a) ∈ X.queue f ∧ (X.queue f').has v = false := by
  obtain ⟨ws, -, hws, hlen, hk, hp⟩ := h.wake _ _ _ _ _ _ hq hw
  have hpos : 0 < ((X.queue f).waitersAt a).length :=
    List.length_pos_of_mem (Queue.mem_waitersAt.mpr hu)
  have hl : 1 ≤ ws.length := by rw [hlen]; omega
  obtain ⟨v, hv⟩ : ∃ v, v ∈ ws := by
    cases ws with
    | nil => simp at hl
    | cons v _ => exact ⟨v, List.mem_cons_self⟩
  refine ⟨hk ▸ hl, v, hws v hv, Queue.has_eq_false.mpr fun b hb => ?_⟩
  exact (Queue.mem_drop.mp (hp.mem_iff.mp hb)).2 hv

/-- A wake of at least as many threads as sleep at `a` (`Event.set`'s `maxInt(u32)`) wakes all
of them. -/
theorem wake_all {t a n f k f'} (hq : (X.queue f).WF) (hw : X.wake t a n f k f')
    (hn : ((X.queue f).waitersAt a).length ≤ n) : ∀ u, (u, a) ∉ X.queue f' := by
  obtain ⟨ws, hnd, hws, hlen, -, hp⟩ := h.wake _ _ _ _ _ _ hq hw
  intro u hu
  have hu0 := (Queue.mem_drop.mp (hp.mem_iff.mp hu))
  -- `ws` is a duplicate-free sublist-sized subset of the waiters at `a`, of the same length:
  -- it contains every waiter.
  have hsub : ∀ x ∈ ws, x ∈ (X.queue f).waitersAt a := fun x hx => Queue.mem_waitersAt.mpr (hws x hx)
  have heq : ws.length = ((X.queue f).waitersAt a).length := by rw [hlen]; omega
  have hall : ∀ x ∈ (X.queue f).waitersAt a, x ∈ ws := by
    intro x hx
    refine Classical.byContradiction fun hn => ?_
    have hsub' : ∀ y ∈ x :: ws, y ∈ (X.queue f).waitersAt a := by
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · exact hsub y hy
    have hnd' : (x :: ws).Nodup := List.nodup_cons.mpr ⟨hn, hnd⟩
    have := List.Nodup.length_le_of_subset hnd' hsub'
    simp only [List.length_cons] at this
    omega
  exact hu0.2 (hall u (Queue.mem_waitersAt.mpr hu0.1))

end FutexSpec

/-! ## Instantiation by an abstraction (what T2 proves) -/

/-- A futex `Y` (T2's concrete rows) whose steps are steps of a futex `X` that satisfies the
contract, under an abstraction of its state that keeps the queue, satisfies the contract too if
it has the progress of the contract itself. This is the analogue of `AllocSpec.congr`. -/
theorem FutexSpec.of_abs {W : M → A → Option (BitVec 32)} {X Y : Futex M A} (hX : FutexSpec W X)
    (abs : Y.F → X.F) (hq : ∀ f, Y.queue f = X.queue (abs f))
    (hi : ∀ f, Y.init f → X.init (abs f))
    (hw : ∀ t a e tm m f r f', Y.wait t a e tm m f r f' → X.wait t a e tm m (abs f) r (abs f'))
    (hloc : ∀ t a e tm m m' f r f', W m a = W m' a →
      Y.wait t a e tm m f r f' → Y.wait t a e tm m' f r f')
    (hr : ∀ t tm f r f', Y.resume t tm f r f' → X.resume t tm (abs f) r (abs f'))
    (hk : ∀ t a n f k f', Y.wake t a n f k f' → X.wake t a n (abs f) k (abs f'))
    (hwt : ∀ t a e tm m f v, W m a = some v → (Y.queue f).has t = false →
      ∃ r f', Y.wait t a e tm m f r f')
    (hrt : ∀ t tm f, (Y.queue f).has t = false → ∃ r f', Y.resume t tm f r f')
    (hkt : ∀ t a n f, (Y.queue f).WF → ∃ k f', Y.wake t a n f k f') : FutexSpec W Y where
  init f h := by rw [hq]; exact hX.init _ (hi f h)
  wait_word t a e tm m f r f' h := hX.wait_word _ _ _ _ _ _ _ _ (hw _ _ _ _ _ _ _ _ h)
  wait_local := hloc
  wait_sleep t a e tm m f f' h := by
    rw [hq, hq]; exact hX.wait_sleep _ _ _ _ _ _ _ (hw _ _ _ _ _ _ _ _ h)
  wait_ret t a e tm m f r f' h := by
    rw [hq, hq]; exact hX.wait_ret _ _ _ _ _ _ _ _ (hw _ _ _ _ _ _ _ _ h)
  resume t tm f r f' h := by rw [hq, hq]; exact hX.resume _ _ _ _ _ (hr _ _ _ _ _ h)
  wake t a n f k f' hwf h := by
    rw [hq, hq]; rw [hq] at hwf; exact hX.wake _ _ _ _ _ _ hwf (hk _ _ _ _ _ _ h)
  wait_total := hwt
  resume_total := hrt
  wake_total := hkt

end Spec
end Zig
