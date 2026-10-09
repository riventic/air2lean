import ZigLean.Mem.Basic

/-!
# Threads that take turns

`Zig.ConcM Tgt α`: the body monad of a function that reaches a sync op (a concurrent function).
A run of such a function is a tree (`CoN`): it ends with a result (`leaf`), or it stops at a sync
op (`sync`) with the rest of its run as a function of the op's response and of the memory at
that time. The scheduler (`ZigLean/Conc/Sched.lean`) runs the threads: at each sync op it picks
the next thread, so threads take turns only at sync ops. Plain code between two sync ops runs
without a stop: a data race there is `.illegal` (the race check of `ZigLean/Mem/Basic.lean`), so
its order cannot change a result.

`Tgt` is the program's spawn-target type (`Emit.lean` generates it): a spawned function and its
argument. The scheduler gets the dispatcher `Tgt → ConcM Tgt Unit` from the program, so the tree
never holds a closure of another result type.

**Depth.** `CoN Tgt α n` is a tree with at most `n` sync ops on each path; `ConcM` is a tree for
each `n`. At `n = 0` a sync op is `leaf none` (no result, as a loop that does not end). The order
(`CoN.le`) has `leaf none` at the bottom and compares the rest of two sync ops pointwise. With the
depth, every chain has a least upper bound (`CoN.has_csup`, by induction on `n`), so `ConcM` has
`Lean.Order.CCPO` and `MonoBind`, and `partial_fixpoint` and the generic `Zig.loop` apply.
-/

namespace Zig

open Lean.Order

/-! ## The environment of a run (`Sched.run`)

A concurrent theorem states the environment it holds in: nothing about thread creation is a
default of the scheduler. -/

/-- Whether thread assignment can fail (`Thread.spawn`, `Io.Group.concurrent`, and the thread of
`Io.Group.async`). -/
inductive SpawnPolicy where
  /-- Assignment succeeds (a thread, and `Io.Threaded`'s allocation of an async task): an explicit
  environment permission. -/
  | available
  /-- Every declared failure is possible (`spawnErrors`), and the per-caller budget
  `Mem.spawnLimit` excludes success at an exhausted budget. -/
  | fallible
  deriving DecidableEq, Repr, Inhabited

/-- The `std.Io` implementation that runs `Io.Group.async`. -/
inductive AsyncEnv where
  /-- `Io.Threaded` on `cpus` CPUs: `async_limit = cpus - 1`. A task runs in the caller once that
  many tasks may be busy (and on an assignment failure, `SpawnPolicy.fallible`); it is never
  deferred. `single_threaded` builds are `threaded 1`. -/
  | threaded (cpus : Nat)
  /-- Any `Io` implementation: a task may get a thread, run in the caller, or be deferred until
  the group's `await`. -/
  | any
  deriving DecidableEq, Repr, Inhabited

/-- The environment of a run: how `Io.Group.async` executes and whether assignment can fail. The
`Io.Group.async` outcomes come from the environment alone (the translation's `--spawn-policy`
does not add any). The program's `std.mem.Allocator` is assumed thread-safe in a concurrent run
(premise ALC-08, `ZigLean/Mem/Alloc.lean`): its state has no race footprint. -/
structure Env where
  io : AsyncEnv
  spawn : SpawnPolicy
  deriving DecidableEq, Repr

/-- The exact declared SpawnError set in std.Thread 0.14.1, 0.15.2, and 0.16.0.
The model does not predict which platform resource fails or its frequency. -/
def spawnErrors : Array ErrName :=
  #["ThreadQuotaExceeded", "SystemResources", "OutOfMemory",
    "LockedMemoryLimitExceeded", "Unexpected"]

/-- A total lookup; the fallback only covers malformed direct callers. -/
def spawnErrorAt (choice : Nat) : ErrName := spawnErrors[choice]?.getD "Unexpected"

/-- The assigned children of thread `t` that no join has reclaimed. A deferred `Io.Group` task
(`ThreadRec.gated`) has no thread of its own: it does not count. -/
def Mem.liveChildren (m : Mem) (t : ThreadId) : Nat :=
  (m.threads.filter fun r => r.spawner == t && !r.joined && !r.gated).size

/-- The current thread may receive another child under `Mem.spawnLimit`. -/
def Mem.spawnAdmits (m : Mem) : Bool :=
  match m.spawnLimit with
  | none => true
  | some limit => decide (m.liveChildren m.current < limit)

/-- The oracle range of a resource choice with `total` outcomes, where outcome 0 assigns a
child: without budget for the caller, outcome 0 is not in the range. -/
def assignmentCount (total : Nat) (m : Mem) : Nat :=
  if m.spawnAdmits then total else total - 1

/-- The outcome of oracle choice `c`: without budget, choice `c` means outcome `c + 1`. -/
def assignmentOutcome (admits : Bool) (c : Nat) : Nat :=
  if admits then c else c + 1

/-- The threads that may count as busy `Io.Threaded` tasks: every thread but `main`, joined or
not (an upper bound of std's `busy_count`: a worker decrements it only after it signalled the
group, so `await` can return while a finished task still counts). -/
def Mem.busyBound (m : Mem) : Nat := m.threads.size - 1

/-- The executions of an `Io.Group.async` task that the environment allows, among 0 (a thread),
1 (the caller, at once) and 2 (deferred until `await`). A thread is always possible (the model's
busy count is an upper bound); `Io.Threaded` runs the task in the caller only once
`async_limit = cpus - 1` tasks may be busy (assignment failure is the thread's own outcome,
`SyncOp.spawn`), and never defers it. -/
def asyncOptions (io : AsyncEnv) (m : Mem) : Array Nat :=
  match io with
  | .any => #[0, 1, 2]
  | .threaded cpus => if cpus - 1 ≤ m.busyBound then #[0, 1] else #[0]

/-- An op where the scheduler takes over. An atomic op is `yield` and then the op in `MemM`
(`ZigLean/Mem/Thread.lean`): the scheduler picks the thread that runs it. -/
inductive SyncOp (Tgt : Type) where
  /-- Another thread can run first. -/
  | yield
  /-- A choice of the oracle: a number `< k` (`k = 0`: no choice, `0`). -/
  | choose (k : Nat)
  /-- A choice of the oracle among `count m` options, from the memory `m` when the thread goes
  on: the message that an atomic read reads, or the place of an atomic write
  (`ZigLean/Mem/Thread.lean`). -/
  | pick (count : Mem → Nat)
  /-- `Thread.spawn` of `t`: a new thread, or (`SpawnPolicy.fallible`) a declared error. -/
  | spawn (t : Tgt)
  /-- The execution of an `Io.Group.async` task that the environment picks (`asyncOptions`). -/
  | asyncChoice
  /-- A spawn of `t` whose thread does not start yet: an `Io.Group.async` task deferred until its
  group's `await` or `cancel` (`ThreadRec.gated`, `Thread.forkGated`). The new thread waits at `gate`
  until `Thread.groupTake` releases it. -/
  | spawnGated (t : Tgt)
  /-- The first stop of a deferred task (`spawnGated`): it goes on once it is no longer gated
  (`Mem.isGated`). Only the scheduler makes this stop. -/
  | gate
  /-- `Thread.join`: waits until thread `tid` ends. -/
  | join (tid : ThreadId)
  /-- A futex wait (`Io.futexWait`): if the `u32` at `p` is `expected`, the thread waits until a
  `wake` at `p`; else it goes on. -/
  | wait (p : Ptr) (expected : BitVec 32)
  /-- A futex wake (`Io.futexWake`): up to `n` threads that wait at `p` go on. -/
  | wake (p : Ptr) (n : Nat)

/-- The response of the scheduler to a sync op. -/
def SyncOp.Resp {Tgt : Type} : SyncOp Tgt → Type
  | .choose _ | .pick _ | .asyncChoice => Nat
  | .spawn _ => Except ErrName ThreadId
  | .spawnGated _ => ThreadId
  | .yield | .gate | .join _ | .wait .. | .wake .. => Unit

/-- A run of a thread with at most `n` sync ops on each path. `leaf none`: no result. `sync op m
k`: the thread stops at `op` with the memory `m`; `k` is the rest, from the response and the
memory when the thread goes on. -/
inductive CoN (Tgt α : Type) : Nat → Type where
  | leaf {n : Nat} (r : Option (Except Error α)) : CoN Tgt α n
  | sync {n : Nat} (op : SyncOp Tgt) (m : Mem) (k : op.Resp → Mem → CoN Tgt α n) :
      CoN Tgt α (n + 1)

namespace CoN

variable {Tgt α β : Type}

/-- `x ⊑ y`: `x` is `leaf none`, or both are the same leaf, or both stop at the same op with the
same memory and the rest of `x` is below the rest of `y` for every response and memory. -/
inductive le : {n : Nat} → CoN Tgt α n → CoN Tgt α n → Prop where
  | bot {n : Nat} (y : CoN Tgt α n) : le (.leaf none) y
  | leaf {n : Nat} (r : Except Error α) : le (n := n) (.leaf (some r)) (.leaf (some r))
  | sync {n : Nat} (op : SyncOp Tgt) (m₀ : Mem) (k₁ k₂ : op.Resp → Mem → CoN Tgt α n)
      (h : ∀ r m, le (k₁ r m) (k₂ r m)) : le (.sync op m₀ k₁) (.sync op m₀ k₂)

theorem le_refl {n : Nat} : (x : CoN Tgt α n) → le x x
  | .leaf none => .bot _
  | .leaf (some r) => .leaf r
  | .sync op m₀ k => .sync op m₀ k k fun r m => le_refl (k r m)

theorem le_trans {n : Nat} {x y z : CoN Tgt α n} (hxy : le x y) (hyz : le y z) : le x z := by
  induction hxy with
  | bot => exact .bot _
  | leaf => exact hyz
  | sync op m₀ k₁ k₂ _ ih =>
    cases hyz with
    | sync _ _ _ k₃ h₂ => exact .sync op m₀ k₁ k₃ fun r m => ih r m (h₂ r m)

theorem le_antisymm {n : Nat} {x y : CoN Tgt α n} (hxy : le x y) (hyx : le y x) : x = y := by
  induction hxy with
  | bot y => cases hyx; rfl
  | leaf => rfl
  | sync op m₀ k₁ k₂ _ ih =>
    cases hyx with
    | sync _ _ _ _ h₂ => congr; funext r m; exact ih r m (h₂ r m)

instance instPartialOrder {n : Nat} : PartialOrder (CoN Tgt α n) where
  rel := le
  rel_refl := le_refl _
  rel_trans := le_trans
  rel_antisymm := le_antisymm

/-- Above a `leaf (some r)` is only the same leaf. -/
theorem le_leaf_some {n : Nat} {r : Except Error α} {y : CoN Tgt α n}
    (h : le (.leaf (some r)) y) : y = .leaf (some r) := by
  cases h; rfl

/-- Above a sync op is the same op with the same memory, with each rest above. -/
theorem le_sync {n : Nat} {op : SyncOp Tgt} {m₀ : Mem} {k : op.Resp → Mem → CoN Tgt α n}
    {y : CoN Tgt α (n + 1)} (h : le (.sync op m₀ k) y) :
    ∃ k', y = .sync op m₀ k' ∧ ∀ r m, le (k r m) (k' r m) := by
  cases h with
  | sync _ _ _ k' h => exact ⟨k', rfl, h⟩

/-- Below a sync op is `leaf none` or the same op with the same memory, with each rest below. -/
theorem le_of_le_sync {n : Nat} {op : SyncOp Tgt} {m₀ : Mem} {k : op.Resp → Mem → CoN Tgt α n}
    {y : CoN Tgt α (n + 1)} (h : le y (.sync op m₀ k)) :
    y = .leaf none ∨ ∃ k', y = .sync op m₀ k' ∧ ∀ r m, le (k' r m) (k r m) := by
  cases h with
  | bot => exact .inl rfl
  | sync _ _ k' _ h => exact .inr ⟨k', rfl, h⟩

/-- Every chain has a least upper bound. -/
theorem has_csup : ∀ {n : Nat} {c : CoN Tgt α n → Prop}, chain c → ∃ s, is_sup c s := by
  intro n
  induction n with
  | zero =>
    intro c hc
    by_cases hx : ∃ r, c (.leaf (some r))
    · obtain ⟨r, hr⟩ := hx
      refine ⟨.leaf (some r), fun z => ⟨fun hz y hy => ?_, fun h => h _ hr⟩⟩
      rcases hc _ _ hy hr with h | h
      · exact le_trans h hz
      · rw [le_leaf_some h]; exact hz
    · refine ⟨.leaf none, fun z => ⟨fun _ y hy => ?_, fun _ => .bot z⟩⟩
      cases y with
      | leaf r => cases r with
        | none => exact .bot z
        | some r => exact absurd ⟨r, hy⟩ hx
  | succ n ih =>
    intro c hc
    by_cases hx : ∃ r, c (.leaf (some r))
    · obtain ⟨r, hr⟩ := hx
      refine ⟨.leaf (some r), fun z => ⟨fun hz y hy => ?_, fun h => h _ hr⟩⟩
      rcases hc _ _ hy hr with h | h
      · exact le_trans h hz
      · rw [le_leaf_some h]; exact hz
    by_cases hs : ∃ op m₀ k, c (.sync op m₀ k)
    · obtain ⟨op, m₀, k, hk⟩ := hs
      -- Every element is `leaf none` or `sync op m₀ _`, with the same `op` and `m₀`.
      have shape : ∀ y, c y → y = .leaf none ∨ ∃ k', y = .sync op m₀ k' := by
        intro y hy
        rcases hc _ _ hy hk with h | h
        · rcases le_of_le_sync h with h | ⟨k', h, -⟩
          · exact .inl h
          · exact .inr ⟨k', h⟩
        · obtain ⟨k', h, -⟩ := le_sync h; exact .inr ⟨k', h⟩
      -- The rests at `(r, m)` form a chain at depth `n`.
      let c' (r : op.Resp) (m : Mem) : CoN Tgt α n → Prop :=
        fun z => ∃ k', c (.sync op m₀ k') ∧ z = k' r m
      have hc' : ∀ r m, chain (c' r m) := by
        intro r m x y ⟨k₁, h₁, e₁⟩ ⟨k₂, h₂, e₂⟩
        subst e₁ e₂
        rcases hc _ _ h₁ h₂ with h | h
        · obtain ⟨k', e, h⟩ := le_sync h
          cases e; exact .inl (h r m)
        · obtain ⟨k', e, h⟩ := le_sync h
          cases e; exact .inr (h r m)
      have hsup : ∀ r m, ∃ s, is_sup (c' r m) s := fun r m => ih (hc' r m)
      let s : op.Resp → Mem → CoN Tgt α n := fun r m => Classical.choose (hsup r m)
      have hs : ∀ r m, is_sup (c' r m) (s r m) := fun r m => Classical.choose_spec (hsup r m)
      refine ⟨.sync op m₀ s, fun z => ⟨fun hz y hy => ?_, fun h => ?_⟩⟩
      · rcases shape y hy with e | ⟨k', e⟩
        · subst e; exact .bot z
        · subst e
          obtain ⟨kz, ez, hkz⟩ := le_sync hz
          subst ez
          exact .sync op m₀ k' kz fun r m =>
            le_trans (((hs r m) (s r m)).mp (le_refl _) _ ⟨k', hy, rfl⟩) (hkz r m)
      · obtain ⟨kz, ez, -⟩ := le_sync (h _ hk)
        subst ez
        refine .sync op m₀ s kz fun r m => ((hs r m) (kz r m)).mpr ?_
        rintro _ ⟨k', hk', rfl⟩
        obtain ⟨kz', ez', h'⟩ := le_sync (h _ hk')
        cases ez'; exact h' r m
    · refine ⟨.leaf none, fun z => ⟨fun _ y hy => ?_, fun _ => .bot z⟩⟩
      cases y with
      | leaf r => cases r with
        | none => exact .bot z
        | some r => exact absurd ⟨r, hy⟩ hx
      | sync op m₀ k => exact absurd ⟨op, m₀, k, hy⟩ hs

instance instCCPO {n : Nat} : CCPO (CoN Tgt α n) where
  has_csup := has_csup

/-- Sequencing: the rest `f` of a leaf gets the depth that is left at the leaf. -/
def bind {n : Nat} (x : CoN Tgt α n) (f : α → (k : Nat) → CoN Tgt β k) : CoN Tgt β n :=
  match x with
  | .leaf none => .leaf none
  | .leaf (some (.error e)) => .leaf (some (.error e))
  | .leaf (some (.ok a)) => f a n
  | .sync op m₀ k => .sync op m₀ fun r m => (k r m).bind f

theorem bind_mono_left {n : Nat} {x₁ x₂ : CoN Tgt α n} {f : α → (k : Nat) → CoN Tgt β k}
    (h : le x₁ x₂) : le (x₁.bind f) (x₂.bind f) := by
  induction h with
  | bot => exact .bot _
  | leaf => exact le_refl _
  | sync op m₀ k₁ k₂ _ ih => exact .sync op m₀ _ _ fun r m => ih r m

theorem bind_mono_right {n : Nat} (x : CoN Tgt α n) {f₁ f₂ : α → (k : Nat) → CoN Tgt β k}
    (h : ∀ a k, le (f₁ a k) (f₂ a k)) : le (x.bind f₁) (x.bind f₂) := by
  induction x with
  | leaf r =>
    rcases r with _ | _ | a
    · exact .bot _
    · exact le_refl _
    · exact h a _
  | sync op m₀ k ih => exact .sync op m₀ _ _ fun r m => ih r m

theorem bind_leaf_ok {n : Nat} (x : CoN Tgt α n) : x.bind (fun a _ => .leaf (some (.ok a))) = x := by
  induction x with
  | leaf r => rcases r with _ | _ | a <;> rfl
  | sync op m₀ k ih => simp only [bind]; congr; funext r m; exact ih r m

theorem bind_assoc {γ : Type} {n : Nat} (x : CoN Tgt α n) (f : α → (k : Nat) → CoN Tgt β k)
    (g : β → (k : Nat) → CoN Tgt γ k) :
    (x.bind f).bind g = x.bind (fun a k => (f a k).bind g) := by
  induction x with
  | leaf r => rcases r with _ | _ | a <;> rfl
  | sync op m₀ k ih => simp only [bind]; congr; funext r m; exact ih r m

/-- Handle an error at any remaining depth. Within a segment the handler starts from the
segment's entry memory, as for `StateT`; after a sync it starts from the resumed shared memory,
so handling an error never rolls back another thread's intervening changes. This handles
errors in the thread's tree. Errors while the scheduler executes a sync op (for example an
invalid join or futex pointer) terminate the run before its continuation and are not caught. -/
def tryCatch {n : Nat} (x : CoN Tgt α n) (m : Mem)
    (h : Error → (k : Nat) → Mem → CoN Tgt α k) : CoN Tgt α n :=
  match x with
  | .leaf (some (.error e)) => h e n m
  | .leaf r => .leaf r
  | .sync op m₀ k => .sync op m₀ fun r m => (k r m).tryCatch m h

end CoN

/-- The monad of a concurrent function: a run for each depth `n`, from the memory at the start. -/
def ConcM (Tgt α : Type) : Type := (n : Nat) → Mem → CoN Tgt (α × Mem) n

namespace ConcM

variable {Tgt α β : Type}

instance : Monad (ConcM Tgt) where
  pure a := fun _ m => .leaf (some (.ok (a, m)))
  bind x f := fun n m => (x n m).bind fun (a, m') k => f a k m'

instance : MonadExceptOf Error (ConcM Tgt) where
  throw e := fun _ _ => .leaf (some (.error e))
  tryCatch x h := fun n m => (x n m).tryCatch m h

/-- A function that uses memory, run with no stop (`MemM`: no sync op). -/
def liftMem (x : MemM α) : ConcM Tgt α := fun _ m => .leaf (x.run m)

instance : MonadLift MemM (ConcM Tgt) where
  monadLift := liftMem

/-- A sync op: the thread stops with its memory `m`, the scheduler takes over, then the thread
goes on with the response and the memory at that time. At depth 0 there is no result. -/
def sync (op : SyncOp Tgt) : ConcM Tgt op.Resp := fun n m =>
  match n with
  | 0 => .leaf none
  | _ + 1 => .sync op m fun r m' => .leaf (some (.ok (r, m')))

instance instOrder : PartialOrder (ConcM Tgt α) :=
  inferInstanceAs (PartialOrder ((n : Nat) → Mem → CoN Tgt (α × Mem) n))

instance instCCPO : CCPO (ConcM Tgt α) :=
  inferInstanceAs (CCPO ((n : Nat) → Mem → CoN Tgt (α × Mem) n))

instance instMonoBind : MonoBind (ConcM Tgt) where
  bind_mono_left h := fun n m => CoN.bind_mono_left (h n m)
  bind_mono_right h := fun _ _ => CoN.bind_mono_right _ fun (a, m') k => h a k m'

instance instLawfulMonad : LawfulMonad (ConcM Tgt) := LawfulMonad.mk'
  (id_map := fun x => by
    funext n m
    show (x n m).bind _ = x n m
    exact CoN.bind_leaf_ok (x n m))
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun x f g => by
    funext n m
    show ((x n m).bind _).bind _ = (x n m).bind _
    exact CoN.bind_assoc (x n m) _ _)

end ConcM

end Zig
