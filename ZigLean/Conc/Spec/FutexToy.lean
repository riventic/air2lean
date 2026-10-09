import ZigLean.Conc.Spec.Futex

/-!
# Futexes that satisfy the contract, and two that do not

* `Futex.ref W`: the most permissive futex of the contract, on the queue itself. `ref_spec`.
  A concrete futex (T2's OS rows) proves the contract by mapping each of its steps to a step of
  `ref` (`FutexSpec.of_abs`); `fifo_spec_of_ref` does this for `fifo`.
* `Futex.fifo W`: the queue itself is the state; a wait sleeps iff the word is the expected
  value, a sleeping thread goes on only after a wake, a wake wakes the oldest `min n c` waiters.
  `fifo_spec`: it satisfies `FutexSpec`. It is the hand model of `Thread.futexWait`/`futexWake`
  (THR-05) as an abstract futex.
* `Futex.spin W`: a wait never sleeps: it reads the word and returns `intr` (an always-spurious
  futex). `spinFutex_spec`: it satisfies `FutexSpec` too, so a client cannot assume that a wait
  blocks.
* `Futex.lazyWake W`: `fifo` whose wake never wakes anyone. `lazyWake_not_spec`.
* `Futex.noRecheck W`: `fifo` whose wait sleeps without comparing the word with the expected
  value. `noRecheck_not_spec`.

`ZigLean/Conc/Spec/IoMutex.lean` shows that both broken futexes make the std `Io.Mutex`
deadlock, so the two clauses that they violate are needed.
-/

namespace Zig
namespace Spec

variable {M A : Type} [DecidableEq A]

namespace Futex

/-- The FIFO futex (module doc). -/
abbrev fifo (W : M → A → Option (BitVec 32)) : Futex M A where
  F := Queue A
  init q := q = []
  queue q := q
  wait t a e _ m q r q' := ∃ v, W m a = some v ∧
    ((v = e ∧ r = none ∧ q' = q ++ [(t, a)]) ∨ (v ≠ e ∧ r = some .again ∧ q' = q))
  resume t _ q r q' := q.has t = false ∧ r = .woken ∧ q' = q
  wake _ a n q q' := q' = q.drop (List.take n (q.waitersAt a))

/-- The most permissive futex of the contract (module doc): a wait sleeps only on the expected
value and may always return instead; a resume may happen at any time; a wake wakes any set of
the right size. Every futex that satisfies the contract has, step by step, steps of this one
(on its queue view), so T2 proves its rows against it with `FutexSpec.of_abs`. -/
abbrev ref (W : M → A → Option (BitVec 32)) : Futex M A where
  F := Queue A
  init q := q = []
  queue q := q
  wait t a e tm m q r q' := ∃ v, W m a = some v ∧
    ((r = none ∧ v = e ∧ q' = q ++ [(t, a)]) ∨ (∃ r', r = some r' ∧ (r' = .timeout → tm = true) ∧ q' = q))
  resume t tm q r q' := q' = q.drop [t] ∧ (r = .timeout → tm = true)
  wake _ a n q q' := ∃ ws : List Tid, ws.Nodup ∧ (∀ u ∈ ws, (u, a) ∈ q) ∧
    min n (q.waitersAt a).length ≤ ws.length ∧ q' = q.drop ws

/-- The always-spurious futex (module doc). -/
abbrev spin (W : M → A → Option (BitVec 32)) : Futex M A where
  F := Unit
  init _ := True
  queue _ := []
  wait _ a _ _ m _ r _ := (∃ v, W m a = some v) ∧ r = some .intr
  resume _ _ _ r _ := r = .intr
  wake _ _ _ _ _ := True

/-- `fifo` with a wake that never wakes (module doc). -/
abbrev lazyWake (W : M → A → Option (BitVec 32)) : Futex M A where
  F := Queue A
  init q := q = []
  queue q := q
  wait := (fifo W).wait
  resume := (fifo W).resume
  wake _ _ _ q q' := q' = q

/-- `fifo` with a wait that sleeps whatever the word (module doc). -/
abbrev noRecheck (W : M → A → Option (BitVec 32)) : Futex M A where
  F := Queue A
  init q := q = []
  queue q := q
  wait t a _ _ m q r q' := (∃ v, W m a = some v) ∧ r = none ∧ q' = q ++ [(t, a)]
  resume := (fifo W).resume
  wake := (fifo W).wake

end Futex

variable (W : M → A → Option (BitVec 32))

theorem fifo_spec : FutexSpec W (Futex.fifo W) where
  init _ h := h
  wait_word := by
    rintro t a e tm m q r q' ⟨v, hv, ⟨rfl, rfl, -⟩ | ⟨-, rfl, -⟩⟩
    · exact ⟨_, hv, fun _ => rfl⟩
    · exact ⟨_, hv, fun h => by cases h⟩
  wait_local := by
    rintro t a e tm m m' q r q' he ⟨v, hv, h⟩
    exact ⟨v, he ▸ hv, h⟩
  wait_sleep := by
    rintro t a e tm m q q' ⟨v, -, ⟨-, -, rfl⟩ | ⟨-, h, -⟩⟩
    · exact List.Perm.refl _
    · cases h
  wait_ret := by
    rintro t a e tm m q r q' ⟨v, -, ⟨-, h, -⟩ | ⟨-, h, rfl⟩⟩
    · cases h
    · cases h; exact ⟨List.Perm.refl _, fun h => by cases h⟩
  resume := by
    rintro t tm q r q' ⟨hq, rfl, rfl⟩
    refine ⟨?_, fun h => by cases h⟩
    simp only [Queue.drop_of_not_has hq]
    exact List.Perm.refl _
  wake := by
    rintro t a n q q' hwf rfl
    exact ⟨_, (Queue.waitersAt_nodup hwf a).sublist (List.take_sublist _ _),
      fun u hu => Queue.mem_waitersAt.mp (List.mem_of_mem_take hu), (Nat.le_of_eq List.length_take.symm),
      List.Perm.refl _⟩
  wait_total := by
    intro t a e tm m q v hv _
    by_cases he : v = e
    · exact ⟨none, q ++ [(t, a)], v, hv, .inl ⟨he, rfl, rfl⟩⟩
    · exact ⟨some .again, q, v, hv, .inr ⟨he, rfl, rfl⟩⟩
  resume_total t _ q h := ⟨.woken, q, h, rfl, rfl⟩
  wake_total _ a n q _ := ⟨_, rfl⟩

theorem ref_spec : FutexSpec W (Futex.ref W) where
  init _ h := h
  wait_word := by
    rintro t a e tm m q r q' ⟨v, hv, ⟨rfl, rfl, -⟩ | ⟨r', rfl, -, -⟩⟩
    · exact ⟨_, hv, fun _ => rfl⟩
    · exact ⟨_, hv, fun h => by cases h⟩
  wait_local := by
    rintro t a e tm m m' q r q' he ⟨v, hv, h⟩
    exact ⟨v, he ▸ hv, h⟩
  wait_sleep := by
    rintro t a e tm m q q' ⟨v, -, ⟨-, -, rfl⟩ | ⟨r', h, -⟩⟩
    · exact List.Perm.refl _
    · cases h
  wait_ret := by
    rintro t a e tm m q r q' ⟨v, -, ⟨h, -⟩ | ⟨r', h, ht, rfl⟩⟩
    · cases h
    · cases h; exact ⟨List.Perm.refl _, ht⟩
  resume := by
    rintro t tm q r q' ⟨rfl, ht⟩
    exact ⟨List.Perm.refl _, ht⟩
  wake := by
    rintro t a n q q' - ⟨ws, hn, hm, hl, rfl⟩
    exact ⟨ws, hn, hm, hl, List.Perm.refl _⟩
  wait_total := by
    intro t a e tm m q v hv _
    by_cases he : v = e
    · exact ⟨none, q ++ [(t, a)], v, hv, .inl ⟨rfl, he, rfl⟩⟩
    · exact ⟨some .again, q, v, hv, .inr ⟨.again, rfl, (fun (h : WaitRet.again = .timeout) => nomatch h), rfl⟩⟩
  resume_total t _ q _ := ⟨.woken, q.drop [t], rfl, fun h => by cases h⟩
  wake_total _ a n q hwf := ⟨_, _, (Queue.waitersAt_nodup hwf a).sublist (List.take_sublist _ _),
    fun _ hu => Queue.mem_waitersAt.mp (List.mem_of_mem_take hu), (Nat.le_of_eq List.length_take.symm), rfl⟩

/-- The FIFO futex is an instance of the reference futex, so it inherits the contract from it
(`FutexSpec.of_abs`, the route of T2's rows). -/
theorem fifo_spec_of_ref : FutexSpec W (Futex.fifo W) := by
  refine FutexSpec.of_abs (ref_spec W) id (fun _ => rfl) (fun _ h => h) ?_
    (fifo_spec W).wait_local ?_ ?_ (fifo_spec W).wait_total (fifo_spec W).resume_total
    (fifo_spec W).wake_total
  · rintro t a e tm m q r q' ⟨v, hv, ⟨rfl, rfl, rfl⟩ | ⟨-, rfl, rfl⟩⟩
    · exact ⟨_, hv, .inl ⟨rfl, rfl, rfl⟩⟩
    · exact ⟨_, hv, .inr ⟨_, rfl, (fun (h : WaitRet.again = .timeout) => nomatch h), rfl⟩⟩
  · rintro t tm q r q' ⟨hq, rfl, rfl⟩
    exact ⟨(Queue.drop_of_not_has hq).symm, fun h => by cases h⟩
  · rintro t a n q q' hwf rfl
    exact ⟨_, (Queue.waitersAt_nodup hwf a).sublist (List.take_sublist _ _),
      fun _ hu => Queue.mem_waitersAt.mp (List.mem_of_mem_take hu), (Nat.le_of_eq List.length_take.symm), rfl⟩

theorem spinFutex_spec : FutexSpec W (Futex.spin W) where
  init _ _ := rfl
  wait_word := by
    rintro t a e tm m q r q' ⟨⟨v, hv⟩, rfl⟩
    exact ⟨v, hv, fun h => by cases h⟩
  wait_local := by
    rintro t a e tm m m' q r q' he ⟨⟨v, hv⟩, rfl⟩
    exact ⟨⟨v, he ▸ hv⟩, rfl⟩
  wait_sleep := by
    rintro t a e tm m q q' ⟨-, h⟩
    cases h
  wait_ret := by
    rintro t a e tm m q r q' ⟨-, h⟩
    cases h
    exact ⟨List.Perm.refl _, fun h => by cases h⟩
  resume := by
    rintro t tm q r q' rfl
    exact ⟨List.Perm.refl _, fun h => by cases h⟩
  wake := by
    rintro t a n q q' - -
    refine ⟨[], List.nodup_nil, fun _ h => absurd h List.not_mem_nil, ?_, List.Perm.refl _⟩
    simp [Queue.waitersAt]
  wait_total t a e tm m q v hv _ := ⟨some .intr, (), ⟨v, hv⟩, rfl⟩
  resume_total _ _ _ _ := ⟨.intr, (), rfl⟩
  wake_total _ _ _ _ _ := ⟨(), trivial⟩

/-- A wake that never wakes violates the contract: with one thread asleep at `a`, `wake(a, 1)`
must wake it. -/
theorem lazyWake_not_spec (a : A) : ¬ FutexSpec W (Futex.lazyWake W) := by
  intro h
  have hwf : Queue.WF ([(0, a)] : Queue A) := by simp [Queue.WF]
  obtain ⟨ws, -, hws, hlen, hp⟩ :=
    h.wake 0 a 1 ([(0, a)] : Queue A) ([(0, a)] : Queue A) hwf rfl
  simp only [Queue.waitersAt, List.filter_cons, beq_self_eq_true, ↓reduceIte, List.filter_nil,
    List.map_cons, List.map_nil, List.length_cons, List.length_nil] at hlen
  obtain ⟨u, hu⟩ : ∃ u, u ∈ ws := by
    cases ws with
    | nil => simp at hlen
    | cons u _ => exact ⟨u, List.mem_cons_self⟩
  have hu0 : u = 0 := by
    have := hws u hu
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at this
    exact this.1
  -- the thread stays asleep, but the contract removes every thread of `ws`
  have := (Queue.mem_drop.mp (hp.mem_iff.mp (List.mem_cons_self (a := (0, a)) (l := []))))
  exact this.2 (hu0 ▸ hu)

/-- A wait that does not compare the word with the expected value violates the contract, as
soon as some word differs from some expected value. -/
theorem noRecheck_not_spec {m : M} {a : A} {v e : BitVec 32} (hv : W m a = some v) (he : v ≠ e) :
    ¬ FutexSpec W (Futex.noRecheck W) := by
  intro h
  have := h.sleep_word (t := 0) (tm := false) (f := ([] : Queue A)) (f' := [(0, a)])
    (show (Futex.noRecheck W).wait 0 a e false m [] none [(0, a)] from ⟨⟨v, hv⟩, rfl, rfl⟩)
  rw [hv] at this
  exact he (Option.some.inj this)

end Spec
end Zig
