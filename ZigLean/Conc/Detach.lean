import ZigLean.Conc.Share

/-!
# Detached threads and join-handle ownership (C07)

The model rules of `Thread.detach` and of an explicit handle transfer
(`ZigLean/Mem/Thread.lean`), and what they guarantee.

- **One authorized join owner.** A thread record names the owner of its join handle
  (`ThreadRec.spawner`: the spawner, until `Thread.transferHandle` moves it) and whether the handle
  was consumed (`joined`). From any memory, at most one thread can join or detach a handle
  (`join_owner_unique`, `detach_owner_unique`), and after a successful join or detach every later
  join or detach of it, by any thread, throws `.illegal` (`join_after_join`, `join_after_detach`,
  `detach_after_join`, `detach_after_detach`). A transfer moves the right: afterwards the new owner's
  handle is valid (`transfer_joinValid`) and every other thread, including the old owner, throws
  `.illegal` at a join or detach (`join_after_transfer`, `detach_after_transfer`). The scheduler
  does not wait at a join of a consumed or foreign handle (`Thread.joinValid` is `false`), so the
  error is reported at once.
- **Detach.** A detached thread runs independently of its parent: the scheduler keeps running
  it, and `checkJoinedByChild` no longer requires its join (`joinedAll` counts it consumed,
  `joinedAll_detach`), so the parent may end first. There is no happens-before edge from the
  detached thread to anyone (`detach_clocks`). `main`'s end ends the run, as the process exit does.
- **Stack data.** A detached thread can outlive the frame of the function that spawned it. The
  frame's stack blocks die at the frame's exit (`free`), and every access to a dead block, by any
  thread, throws `.illegal` (`access_dead_any`, `load_dead`, `store_dead`, `frame_exit_kills`): a
  detached thread cannot read or write stack data that is gone. The dynamic check covers every
  access after the exit; the logic (`ZigLean/Conc/Csl.lean`, `ZigLean/Conc/Transfer.lean`) adds
  the static side: a stack region granted `owned` to a detached thread never returns to the
  parent (there is no join that regains it), so the parent cannot prove its frame's `free`. A
  detached worker may only capture values, or heap/global regions that it owns (a C01 `owned`
  transfer) and frees itself (`Proofs/Threads/Detach.lean`).
-/

namespace Zig
namespace Conc
namespace Detach

open Proto

variable {m m' : Mem} {tid : ThreadId}

private theorem run_get_bind {β : Type} (f : Mem → MemM β) :
    ((get >>= f : MemM β).run m).run = ((f m).run m).run := rfl

/-! ## The ops, from a result back to the memory -/

theorem join_run_ok (h : ((Thread.join tid).run m).run = some (.ok ((), m'))) :
    ∃ rec, m.threads[tid]? = some rec ∧ rec.spawner = m.current ∧ rec.joined = false ∧
      m' = { m with
        clocks := m.clocks.set! m.current
          (VClock.merge (VClock.bump (m.clocks[m.current]!) m.current) (m.clocks[tid]!))
        threads := m.threads.set! tid { rec with joined := true } } := by
  unfold Thread.join at h
  rw [run_get_bind] at h
  cases hr : m.threads[tid]? with
  | none => simp only [hr] at h; cases h
  | some rec =>
    simp only [hr] at h
    by_cases hc : (rec.spawner != m.current || rec.joined) = true
    · simp only [hc, ↓reduceIte] at h; cases h
    · simp only [Bool.not_eq_true] at hc
      simp only [hc, Bool.false_eq_true, ↓reduceIte] at h
      simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hc
      refine ⟨rec, rfl, hc.1, hc.2, ?_⟩
      simp only [StateT.run, set, StateT.set, pure, ExceptT.pure, ExceptT.mk, ExceptT.run,
        Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at h
      exact h.2.symm

theorem detach_run_ok (h : ((Thread.detach tid).run m).run = some (.ok ((), m'))) :
    ∃ rec, m.threads[tid]? = some rec ∧ rec.spawner = m.current ∧ rec.joined = false ∧
      m' = { m with threads := m.threads.set! tid { rec with joined := true } } := by
  unfold Thread.detach at h
  rw [run_get_bind] at h
  cases hr : m.threads[tid]? with
  | none => simp only [hr] at h; cases h
  | some rec =>
    simp only [hr] at h
    by_cases hc : (rec.spawner != m.current || rec.joined) = true
    · simp only [hc, ↓reduceIte] at h; cases h
    · simp only [Bool.not_eq_true] at hc
      simp only [hc, Bool.false_eq_true, ↓reduceIte] at h
      simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hc
      refine ⟨rec, rfl, hc.1, hc.2, ?_⟩
      simp only [StateT.run, set, StateT.set, pure, ExceptT.pure, ExceptT.mk, ExceptT.run,
        Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at h
      exact h.2.symm

theorem transfer_run_ok {owner : ThreadId}
    (h : ((Thread.transferHandle tid owner).run m).run = some (.ok ((), m'))) :
    ∃ rec, m.threads[tid]? = some rec ∧ rec.spawner = m.current ∧ rec.joined = false ∧
      owner ≠ tid ∧ owner < m.threads.size ∧
      m' = { m with threads := m.threads.set! tid { rec with spawner := owner } } := by
  unfold Thread.transferHandle at h
  rw [run_get_bind] at h
  cases hr : m.threads[tid]? with
  | none => simp only [hr] at h; cases h
  | some rec =>
    simp only [hr] at h
    by_cases hc : (rec.spawner != m.current || rec.joined || owner == tid ||
        decide (m.threads.size ≤ owner)) = true
    · simp only [hc, ↓reduceIte] at h; cases h
    · simp only [Bool.not_eq_true] at hc
      simp only [hc, Bool.false_eq_true, ↓reduceIte] at h
      simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq, beq_eq_false_iff_ne,
        decide_eq_false_iff_not, Nat.not_le] at hc
      refine ⟨rec, rfl, hc.1.1.1, hc.1.1.2, hc.1.2, hc.2, ?_⟩
      simp only [StateT.run, set, StateT.set, pure, ExceptT.pure, ExceptT.mk, ExceptT.run,
        Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at h
      exact h.2.symm

/-- The run of a valid detach. -/
theorem detach_run {rec : ThreadRec} (hr : m.threads[tid]? = some rec)
    (hs : rec.spawner = m.current) (hj : rec.joined = false) :
    ((Thread.detach tid).run m).run =
      some (.ok ((), { m with threads := m.threads.set! tid { rec with joined := true } })) := by
  unfold Thread.detach
  simp [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, ExceptT.run,
    ExceptT.bind, ExceptT.mk, ExceptT.bindCont, pure, ExceptT.pure, set, StateT.set, hr, hs, hj]

/-- The run of a valid transfer. -/
theorem transfer_run {owner : ThreadId} {rec : ThreadRec} (hr : m.threads[tid]? = some rec)
    (hs : rec.spawner = m.current) (hj : rec.joined = false) (hne : owner ≠ tid)
    (hlt : owner < m.threads.size) :
    ((Thread.transferHandle tid owner).run m).run =
      some (.ok ((), { m with threads := m.threads.set! tid { rec with spawner := owner } })) := by
  unfold Thread.transferHandle
  have hle : ¬ m.threads.size ≤ owner := Nat.not_le.mpr hlt
  simp [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, ExceptT.run,
    ExceptT.bind, ExceptT.mk, ExceptT.bindCont, pure, ExceptT.pure, set, StateT.set, hr, hs, hj,
    hne, hle]

/-! ## Invalid handles throw `.illegal` -/

/-- The handle is valid exactly when the caller owns it and it is not consumed. -/
theorem joinValid_iff {t : ThreadId} :
    Thread.joinValid m t tid = true ↔
      ∃ rec, m.threads[tid]? = some rec ∧ rec.spawner = t ∧ rec.joined = false := by
  unfold Thread.joinValid
  cases m.threads[tid]? with
  | none => simp
  | some rec => simp

theorem join_invalid (hv : Thread.joinValid m m.current tid = false) :
    ((Thread.join tid).run m).run = some (.error .illegal) := by
  unfold Thread.join
  rw [run_get_bind]
  unfold Thread.joinValid at hv
  cases hr : m.threads[tid]? with
  | none => rfl
  | some rec =>
    simp only [hr, Bool.and_eq_false_iff, beq_eq_false_iff_ne, Bool.not_eq_false'] at hv ⊢
    have hc : (rec.spawner != m.current || rec.joined) = true := by
      rcases hv with hv | hv <;> simp [hv]
    simp only [hc, ↓reduceIte]; rfl

theorem detach_invalid (hv : Thread.joinValid m m.current tid = false) :
    ((Thread.detach tid).run m).run = some (.error .illegal) := by
  unfold Thread.detach
  rw [run_get_bind]
  unfold Thread.joinValid at hv
  cases hr : m.threads[tid]? with
  | none => rfl
  | some rec =>
    simp only [hr, Bool.and_eq_false_iff, beq_eq_false_iff_ne, Bool.not_eq_false'] at hv ⊢
    have hc : (rec.spawner != m.current || rec.joined) = true := by
      rcases hv with hv | hv <;> simp [hv]
    simp only [hc, ↓reduceIte]; rfl

theorem joinValid_of_join (h : ((Thread.join tid).run m).run = some (.ok ((), m'))) :
    Thread.joinValid m m.current tid = true := by
  obtain ⟨rec, hr, hs, hj, -⟩ := join_run_ok h
  exact joinValid_iff.mpr ⟨rec, hr, hs, hj⟩

theorem joinValid_of_detach (h : ((Thread.detach tid).run m).run = some (.ok ((), m'))) :
    Thread.joinValid m m.current tid = true := by
  obtain ⟨rec, hr, hs, hj, -⟩ := detach_run_ok h
  exact joinValid_iff.mpr ⟨rec, hr, hs, hj⟩

/-! ## One authorized join owner -/

/-- **One owner.** From one memory, at most one thread can join the handle `tid`. -/
theorem join_owner_unique {t u : ThreadId} {m₁ m₂ : Mem}
    (h₁ : ((Thread.join tid).run { m with current := t }).run = some (.ok ((), m₁)))
    (h₂ : ((Thread.join tid).run { m with current := u }).run = some (.ok ((), m₂))) : t = u := by
  obtain ⟨r₁, hr₁, hs₁, -⟩ := join_run_ok h₁
  obtain ⟨r₂, hr₂, hs₂, -⟩ := join_run_ok h₂
  have : r₁ = r₂ := Option.some.inj (hr₁.symm.trans hr₂)
  subst this
  exact hs₁.symm.trans hs₂

/-- At most one thread can detach the handle `tid`, and it is the one that could join it. -/
theorem detach_owner_unique {t u : ThreadId} {m₁ m₂ : Mem}
    (h₁ : ((Thread.detach tid).run { m with current := t }).run = some (.ok ((), m₁)))
    (h₂ : ((Thread.join tid).run { m with current := u }).run = some (.ok ((), m₂)) ∨
      ((Thread.detach tid).run { m with current := u }).run = some (.ok ((), m₂))) : t = u := by
  obtain ⟨r₁, hr₁, hs₁, -⟩ := detach_run_ok h₁
  have ⟨r₂, hr₂, hs₂⟩ : ∃ r₂, m.threads[tid]? = some r₂ ∧ r₂.spawner = u := by
    rcases h₂ with h₂ | h₂
    · obtain ⟨r₂, hr₂, hs₂, -⟩ := join_run_ok h₂; exact ⟨r₂, hr₂, hs₂⟩
    · obtain ⟨r₂, hr₂, hs₂, -⟩ := detach_run_ok h₂; exact ⟨r₂, hr₂, hs₂⟩
  have : r₁ = r₂ := Option.some.inj (hr₁.symm.trans hr₂)
  subst this
  exact hs₁.symm.trans hs₂

/-- A consumed handle is not valid for any thread. -/
theorem joinValid_consumed {rec : ThreadRec} (hr : m.threads[tid]? = some rec)
    (hj : rec.joined = true) (t : ThreadId) : Thread.joinValid m t tid = false := by
  simp [Thread.joinValid, hr, hj]

private theorem get_set_self {rec : ThreadRec} (hr : m.threads[tid]? = some rec) (r : ThreadRec) :
    (m.threads.set! tid r)[tid]? = some r := by
  have hlt : tid < m.threads.size := (Array.getElem?_eq_some_iff.mp hr).1
  simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt hlt]

/-- **Join once.** After a join, every later join of the handle, by any thread, throws
`.illegal`. -/
theorem join_after_join (h : ((Thread.join tid).run m).run = some (.ok ((), m'))) (t : ThreadId) :
    ((Thread.join tid).run { m' with current := t }).run = some (.error .illegal) := by
  obtain ⟨rec, hr, -, -, rfl⟩ := join_run_ok h
  exact join_invalid (joinValid_consumed (get_set_self hr _) rfl t)

/-- After a join, a detach of the handle, by any thread, throws `.illegal`. -/
theorem detach_after_join (h : ((Thread.join tid).run m).run = some (.ok ((), m'))) (t : ThreadId) :
    ((Thread.detach tid).run { m' with current := t }).run = some (.error .illegal) := by
  obtain ⟨rec, hr, -, -, rfl⟩ := join_run_ok h
  exact detach_invalid (joinValid_consumed (get_set_self hr _) rfl t)

/-- **Detach consumes the handle.** After a detach, a join of the handle, by any thread, throws
`.illegal`; the scheduler does not wait for the detached thread (`joinValid` is `false`). -/
theorem join_after_detach (h : ((Thread.detach tid).run m).run = some (.ok ((), m')))
    (t : ThreadId) :
    Thread.joinValid m' t tid = false ∧
      ((Thread.join tid).run { m' with current := t }).run = some (.error .illegal) := by
  obtain ⟨rec, hr, -, -, rfl⟩ := detach_run_ok h
  exact ⟨joinValid_consumed (get_set_self hr _) rfl t,
    join_invalid (joinValid_consumed (get_set_self hr _) rfl t)⟩

/-- A second detach throws `.illegal`. -/
theorem detach_after_detach (h : ((Thread.detach tid).run m).run = some (.ok ((), m')))
    (t : ThreadId) :
    ((Thread.detach tid).run { m' with current := t }).run = some (.error .illegal) := by
  obtain ⟨rec, hr, -, -, rfl⟩ := detach_run_ok h
  exact detach_invalid (joinValid_consumed (get_set_self hr _) rfl t)

/-- **Transfer.** After a transfer of `tid` to `owner`, `owner` holds a valid handle, and it
is the only thread that can join or detach `tid`: every other thread, including the old owner,
throws `.illegal`. -/
theorem transfer_joinValid {owner : ThreadId}
    (h : ((Thread.transferHandle tid owner).run m).run = some (.ok ((), m'))) :
    Thread.joinValid m' owner tid = true := by
  obtain ⟨rec, hr, -, hj, -, -, rfl⟩ := transfer_run_ok h
  exact joinValid_iff.mpr ⟨_, get_set_self hr _, rfl, hj⟩

private theorem joinValid_foreign {owner t : ThreadId} {r : ThreadRec}
    (hr : m'.threads[tid]? = some r) (hs : r.spawner = owner) (ht : t ≠ owner) :
    Thread.joinValid m' t tid = false := by
  have hb : (owner == t) = false := by simp [Ne.symm ht]
  unfold Thread.joinValid
  rw [hr]
  simp [hs, hb]

theorem join_after_transfer {owner t : ThreadId}
    (h : ((Thread.transferHandle tid owner).run m).run = some (.ok ((), m'))) (ht : t ≠ owner) :
    ((Thread.join tid).run { m' with current := t }).run = some (.error .illegal) := by
  obtain ⟨rec, hr, -, -, -, -, rfl⟩ := transfer_run_ok h
  exact join_invalid (joinValid_foreign (get_set_self (m := { m with current := t }) hr _) rfl ht)

theorem detach_after_transfer {owner t : ThreadId}
    (h : ((Thread.transferHandle tid owner).run m).run = some (.ok ((), m'))) (ht : t ≠ owner) :
    ((Thread.detach tid).run { m' with current := t }).run = some (.error .illegal) := by
  obtain ⟨rec, hr, -, -, -, -, rfl⟩ := transfer_run_ok h
  exact detach_invalid (joinValid_foreign (get_set_self (m := { m with current := t }) hr _) rfl ht)

/-- The new owner's join succeeds (the old owner's would not: `join_after_transfer`). -/
theorem join_after_transfer_owner {owner : ThreadId}
    (h : ((Thread.transferHandle tid owner).run m).run = some (.ok ((), m'))) :
    ∃ m'', ((Thread.join tid).run { m' with current := owner }).run = some (.ok ((), m'')) := by
  obtain ⟨rec, hr, -, hj, -, -, rfl⟩ := transfer_run_ok h
  exact join_run (get_set_self hr _) rfl hj

/-! ## Detach: independent lifetime, no happens-before edge -/

/-- A detach changes only the thread table: no clock, block or footprint entry. -/
theorem detach_clocks (h : ((Thread.detach tid).run m).run = some (.ok ((), m'))) :
    m'.clocks = m.clocks ∧ m'.blocks = m.blocks ∧ m'.footprint = m.footprint ∧
      m'.current = m.current ∧ m'.threads.size = m.threads.size := by
  obtain ⟨rec, -, -, -, rfl⟩ := detach_run_ok h
  simp [Array.set!_eq_setIfInBounds]

/-- After a detach, the parent no longer owes a join of the detached thread: if every other
handle it owns is consumed, it may end (`checkJoinedByChild` passes) while the detached thread
still runs. -/
theorem joinedAll_detach {t : ThreadId} (h : ((Thread.detach tid).run m).run = some (.ok ((), m')))
    (hall : ∀ u (r : ThreadRec), u ≠ tid → m.threads[u]? = some r → r.spawner = t →
      r.joined = true) :
    joinedAll t m' := by
  obtain ⟨rec, hr, -, -, rfl⟩ := detach_run_ok h
  intro r hm hs
  dsimp only at hm
  obtain ⟨u, hu, rfl⟩ := Array.getElem_of_mem hm
  simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds] at hu hs ⊢
  by_cases hut : u = tid
  · subst hut
    simp [Array.getElem_setIfInBounds_self]
  · rw [Array.getElem_setIfInBounds_ne hu (Ne.symm hut)] at hs ⊢
    exact hall u _ hut (Array.getElem?_eq_getElem hu) hs

/-! ## Stack data dies with the frame -/

/-- An access to a dead block throws `.illegal`, whichever thread runs it. -/
theorem access_dead_any {b : BlockId} {blk : Block} (hb : m.blocks[b]? = some blk)
    (hl : blk.live = false) (u : ThreadId) (off : Int) (n a : Nat) :
    ({ m with current := u } : Mem).access ⟨some b, off⟩ n a = throw .illegal :=
  access_dead (m := { m with current := u }) hb hl off n a

/-- A load from a dead block throws `.illegal`, whichever thread runs it. -/
theorem load_dead {T : Type} [Enc T] {b : BlockId} {blk : Block} (hb : m.blocks[b]? = some blk)
    (hl : blk.live = false) (u : ThreadId) (off : Int) (a : Nat) :
    ((load T a ⟨some b, off⟩).run { m with current := u }).run = some (.error .illegal) := by
  have hacc := access_dead_any hb hl u off (Enc.size T) a
  simp [load, loadBytes, zig_unfold, hacc, ExceptT.bindCont, StateT.lift, ExceptT.run]

/-- A store to a dead block throws `.illegal`, whichever thread runs it. -/
theorem store_dead {T : Type} [Enc T] {b : BlockId} {blk : Block} (hb : m.blocks[b]? = some blk)
    (hl : blk.live = false) (u : ThreadId) (off : Int) (a : Nat) (v : T) :
    ((store a ⟨some b, off⟩ v).run { m with current := u }).run = some (.error .illegal) := by
  have hacc := access_dead_any hb hl u off (Enc.encode v).size a
  simp [store, storeBytes, Mem.accessW, zig_unfold, hacc, ExceptT.bindCont, StateT.lift,
    ExceptT.run]

/-- **A detached thread cannot retain freed stack data.** The exit of a frame frees its stack
block `b` (`free`). From then on, every load or store at `b`, by any thread — in particular a
detached thread that captured a pointer into the frame — throws `.illegal`. -/
theorem frame_exit_kills {b : BlockId} (h : ((free ⟨some b, 0⟩).run m).run = some (.ok ((), m')))
    (u : ThreadId) (off : Int) (a : Nat) :
    (∀ (T : Type) [Enc T], ((load T a ⟨some b, off⟩).run { m' with current := u }).run =
      some (.error .illegal)) ∧
    (∀ (T : Type) [Enc T] (v : T), ((store a ⟨some b, off⟩ v).run { m' with current := u }).run =
      some (.error .illegal)) := by
  obtain ⟨b', blk, hb', hblk, rfl⟩ := free_ok h
  cases hb'
  have hdead : ({ m with blocks := m.blocks.set! b { blk with live := false } } : Mem).blocks[b]? =
      some { blk with live := false } := by
    simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt
      (Array.getElem?_eq_some_iff.mp hblk).1]
  exact ⟨fun T _ => load_dead hdead rfl u off a, fun T _ v => store_dead hdead rfl u off a v⟩

end Detach
end Conc
end Zig
