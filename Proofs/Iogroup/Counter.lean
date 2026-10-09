import ZigLean.Conc.Unroll
import Proofs.Iogroup.Gen
import ZigLean.Conc.LockRules
import ZigLean.Conc.Share
import ZigLean.Witness

/-!
# `groupCounter` over all schedules

`groupCounter` runs three tasks in an `Io.Group` (`Group.async`; each task is a thread in the
model); each task adds 1 to a counter under an `Io.Mutex` (translated from Zig 0.16.0's std
code). After `Group.await` the result is 3 under every schedule (`groupCounter_spec`), and no
schedule gives an error (`groupCounter_safe`).

The proof uses the rules of a lock that owns a resource (`ZigLean/Conc/Lock.lean`,
`ZigLean/Conc/LockRules.lean`), as `Proofs/Sync/Mutex.lean` does for `mutexCounter`: the mutex
(bytes 16..20 of the `Counter`, block 0) owns the counter (bytes 20..24), whose value is the
number of tasks that did their increment (`R`). This file proves the rest:

- **Ghost values** (`Gh = LG × Ph`): the lock's part, and where the thread is: `main` at its
  spawns (`spawn j`) and at its joins (`joins i`), a task before and after its increment.
- **The rest of the invariant** (`U`): the threads and the group's tasks (`Shape`), the bytes of
  `io` (each access is a read, or happened before every thread), no thread has a part of the
  heap, the two blocks, and each joined task has ended and happened before `main` (`Jle`).
- **`main`**: before its first spawn it gives the mutex and the counter to the lock
  (`Inv.make`); the `Io.Group` (block 1) and `io` belong to no thread. `Group.async` is a spawn
  (`WP.groupAsyncC`); `Group.await` joins the three tasks; then `main` takes the counter back
  (`Inv.take`) and reads 3.
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Conc.Lock Iogroup Assn

namespace Iogroup.GroupCounter

/-- Where a thread is, outside the lock's code. -/
inductive Ph where
  | none
  /-- `main` after `j` spawns. -/
  | spawn (j : Nat)
  /-- `main` after `i` joins. -/
  | joins (i : Nat)
  /-- A task; `done`: it did its increment. -/
  | task (done : Bool)
  /-- A task that has ended. -/
  | fin

/-- The increment of a thread. -/
def Ph.count : Ph → Nat
  | .task true | .fin => 1
  | _ => 0

abbrev Gh := LG × Ph

/-- The `Counter` (block 0). -/
def cPtr : Ptr := ⟨some 0, 0⟩

/-- The `Io.Group` (block 1). -/
def gPtr : Ptr := ⟨some 1, 0⟩

/-- The increments of the three tasks. -/
def sum (X : ThreadId → Ph) : Nat := (X 1).count + (X 2).count + (X 3).count

/-- The counter holds the increments of the tasks. -/
def R (X : ThreadId → Ph) : Assn := pts (cPtr.add 20) 4 (BitVec.ofNat 32 (sum X))

/-- The `Io.Mutex`: bytes 16..20 of the `Counter`. It owns the counter. -/
abbrev L : Lock Gh := Lock.prod 0 16 R

/-- The states of `Io.Mutex`. -/
def S : States Io_Mutex_State where
  unl := .unlocked
  one := .locked_once
  two := .contended
  c := 2
  bits0 := rfl
  bits1 := rfl
  bits2 := rfl
  dec0 := rfl
  dec1 := rfl
  dec2 := rfl
  ne01 := by decide
  ne02 := by decide
  ne12 := by decide

/-- The accesses to the bytes of `io` (0..16 of the `Counter`). -/
def IoR (e : FootprintEntry) : Prop := e.block = 0 ∧ e.off < 16

/-- The tasks read-share `io` (`ZigLean/Conc/Share.lean`): each access to it is a read that
happened before some thread, or happened before every thread. -/
def IoOk (m : Mem) : Prop :=
  ∀ e ∈ m.footprint, e.block = 0 → e.off < 16 → (e.kind = .read ∧ SomeLe m e.clock) ∨
    AllLe m e.clock

theorem ioOk_iff {m : Mem} : IoOk m ↔ ReadShared IoR m :=
  ⟨fun h e he hr => h e he hr.1 hr.2, fun h e he hb ho => h e he ⟨hb, ho⟩⟩

theorem covers_io : Covers IoR 0 0 16 := fun _ hb _ h2 => ⟨hb, by omega⟩

/-- The tasks of the group after `j` spawns. -/
def grp (j : Nat) : Array (Ptr × ThreadId) := (Array.range j).map fun i => (gPtr, i + 1)

/-- The threads: `main` and its tasks, which it spawned; a joined task has ended. Before the
`await` the group records the tasks; after it, `main` joins them in order. -/
def Shape (X : ThreadId → Ph) (m : Mem) : Prop :=
  m.threads[0]? = some { spawner := 0, joined := true } ∧
  (∀ u, 1 ≤ u → u < m.threads.size → ∃ jn, m.threads[u]? = some { spawner := 0, joined := jn } ∧
    (jn = true → X u = .fin) ∧ ((∃ d, X u = .task d) ∨ X u = .fin)) ∧
  (∀ u, m.threads.size ≤ u → X u = .none) ∧
  ((∃ j ≤ 3, X 0 = .spawn j ∧ m.threads.size = j + 1 ∧ m.groups = grp j ∧
      ∀ u, joinedB m u = false) ∨
   (∃ i ≤ 3, X 0 = .joins i ∧ m.threads.size = 4 ∧ m.groups = #[] ∧
      ∀ u, joinedB m u = true ↔ 1 ≤ u ∧ u ≤ i))

/-- Block 0 is the live `Counter`: 24 bytes on the stack, at an address that is a multiple of 8. -/
def BlkOk (m : Mem) : Prop :=
  ∃ blk, m.blocks[0]? = some blk ∧ blk.live = true ∧ blk.bytes.size = 24 ∧ blk.addr % 8 = 0 ∧
    blk.kind = .stack

/-- A joined task has ended, and its clock happened before `main`'s. -/
def Jle (G : ThreadId → Gh) (m : Mem) : Prop :=
  ∀ v, joinedB m v = true → (G v).1.ph = .gone ∧ VClock.le (m.clocks[v]!) (m.clocks[0]!) = true

/-- The rest of the invariant (module doc). -/
structure U (G : ThreadId → Gh) (m : Mem) : Prop where
  shape : Shape (fun u => (G u).2) m
  io : IoOk m
  parts : ∀ u, (G u).1.part = Heap.empty
  blk : BlkOk m
  blk1 : ∃ blk, m.blocks[1]? = some blk ∧ blk.live = true ∧ blk.bytes.size = 16
  jle : Jle G m

/-- The protocol, in strict mode. -/
def proto : Proto Tgt Gh where
  inv G m := L.Inv G m ∧ U G m
  init tgt g := match tgt with
    | .add p => p = cPtr ∧ g = (⟨.out, Heap.empty, Heap.empty⟩, .task false)
  fin g := g.1.ph = .gone ∧ g.2 = .fin
  strict := true
  joins g := g.1.ph = .out ∧ ∃ i, g.2 = .joins i

/-- Join before free: block 0 (the `Counter`, with the read-shared `io`) is freed, and every
access to `io` happened before `main` (`ZigLean/Conc/Share.lean`'s `RegionOwned`). -/
def Reclaimed (m : Mem) : Prop :=
  (∃ blk, m.blocks[0]? = some blk ∧ blk.live = false) ∧ RegionOwned IoR m (m.clocks[0]!)

/-- `main`'s post: the result, all tasks joined, and `io` reclaimed. -/
def QM : Except ErrName (BitVec 32) → (ThreadId → Gh) → Mem → Nat → Prop :=
  fun v _ m _ => v = .ok 3 ∧ joinedAll 0 m ∧ Reclaimed m

/-! ## The protocol has the lock -/

/-- Block 1 after a lock step: the same. -/
theorem blk1_step {t : ThreadId} {m m' : Mem} (hs : L.Step t m m')
    (h : ∃ blk, m.blocks[1]? = some blk ∧ blk.live = true ∧ blk.bytes.size = 16) :
    ∃ blk, m'.blocks[1]? = some blk ∧ blk.live = true ∧ blk.bytes.size = 16 := by
  obtain ⟨blk, hb, hl, hsz⟩ := h
  rcases hs.blocks with e | ⟨blk', bs, h1, h2, h3, h4, h5⟩
  · exact ⟨blk, by rw [e]; exact hb, hl, hsz⟩
  · refine ⟨blk, ?_, hl, hsz⟩
    rw [h5]; show (m.blocks.set! 0 _)[1]? = _
    rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]; simpa using hb

theorem stable (G : ThreadId → Gh) (m m' : Mem) (t : ThreadId) (p : LPh) (h : Heap)
    (hg : L.ph (G t) ≠ .gone) (hu : U G m) (hs : L.Step t m m')
    (_ : L.ph (G t) = .holds → p ≠ .holds → L.Before m' (m.clocks[t]!)) :
    U (upd G t (L.set (G t) p h)) m' := by
  obtain ⟨hsh, hio, hpart, hblk, hblk1, hjle⟩ := hu
  have hjb : joinedB m' = joinedB m := joinedB_congr hs.threads
  refine ⟨?_, fun e he hb ho => ?_, fun u => ?_, ?_, blk1_step hs hblk1, fun v hv => ?_⟩
  · rw [snd_set]; unfold Shape at hsh ⊢; rw [hs.threads, hs.groups, hjb]; exact hsh
  · rcases hs.fp e he with h' | ⟨hb', ho', -⟩
    · rcases hio e h' hb ho with ⟨hk, h''⟩ | h''
      · exact .inl ⟨hk, someLe_mono hs.threads (fun u _ => hs.clocks u) h''⟩
      · exact .inr (hs.allLe h'')
    · exact absurd ho (by rw [ho']; decide)
  · unfold upd; split
    · rename_i e; subst e; exact hpart u
    · exact hpart u
  · obtain ⟨blk, hb, hl, hsz, ha, hk⟩ := hblk
    rcases hs.blocks with e | ⟨blk', bs, h1, -, h3, h4, h5⟩
    · exact ⟨blk, by rw [e]; exact hb, hl, hsz, ha, hk⟩
    · have h1' : m.blocks[0]? = some blk' := h1
      rw [hb] at h1'; cases h1'
      refine ⟨{ blk with bytes := writeBytes blk.bytes 16 bs }, ?_, hl, ?_, ha, hk⟩
      · rw [h5]; show (m.blocks.set! 0 _)[0]? = _
        rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt
          (Array.getElem?_eq_some_iff.mp hb).1]; rfl
      · show (writeBytes blk.bytes 16 bs).size = 24
        rw [writeBytes_size _ _ _ (by rw [h3, hsz]; decide), hsz]
  · rw [hjb] at hv
    obtain ⟨hgv, hle⟩ := hjle v hv
    have hvt : v ≠ t := fun e => by rw [e] at hgv; exact hg hgv
    refine ⟨by rw [upd_ne _ _ hvt]; exact hgv, ?_⟩
    rw [hs.others v hvt]
    exact VClock.le_trans hle (hs.clocks 0)

theorem fits : L.Fits proto U :=
  ⟨fun _ _ => Iff.rfl, fun _ h => h.1, fun _ h => h.1, stable⟩

/-- The word: `L.ptr`. -/
theorem mptr : ((cPtr.add 16).add 0).add 0 = L.ptr := rfl

/-! ## `lock` -/

/-- `lock`'s loop invariant: thread `t` is at `spin`. -/
def lockInv (t : ThreadId) (g : Gh) (D : Nat) (_ : Io_Mutex_lockUncancelableLocals)
    (G : ThreadId → Gh) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ m.current = t ∧ proto.inv (upd G t (L.set g .spin Heap.empty)) m

/-- `lock`'s loop ends when thread `t` holds the mutex. -/
def lockPost (t : ThreadId) (g : Gh) (D : Nat)
    (r : Io_Mutex_lockUncancelableExit × Io_Mutex_lockUncancelableLocals) (G : ThreadId → Gh)
    (m : Mem) (d : Nat) : Prop :=
  r.1 = .br22 ∧ d < D ∧ m.current = t ∧ ∃ hL, proto.inv (upd G t (L.set g .holds hL)) m

/-- One repeat of `lock`'s loop: `xchg(contended)`; the thread holds the mutex, or it waits at
the futex (a stop, so the depth gets smaller). -/
theorem loop23_body (t : ThreadId) (g : Gh) (D : Nat) (io : Io)
    (s : Io_Mutex_lockUncancelableLocals) (G : ThreadId → Gh) (m : Mem) (d : Nat)
    (h : lockInv t g D s G m d) :
    proto.WP t ((Io_Mutex_lockUncancelable.loop23 (cPtr.add 16) io).run s) (fun r G' m' d' =>
      if Io_Mutex_lockUncancelable.again23 r.1 then lockInv t g D r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : Io_Mutex_lockUncancelableLocals) => 0) s)
      else lockPost t g D r G' m' d') G m d := by
  obtain ⟨hD, -, hi⟩ := h
  unfold Io_Mutex_lockUncancelable.loop23
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  rw [mptr]
  refine WP.bind (wp_xchgLock fits S rfl (g := L.set g .spin Heap.empty) rfl hi
    fun k hk G₁ m₁ r hc₁ hcase => ?_)
  rcases hcase with ⟨rfl, hL, hi₁⟩ | ⟨hr, hi₁⟩
  · simp only [StateT.run_pure, pure_bind]
    refine WP.pure' ?_
    simp only [Io_Mutex_lockUncancelable.again23, Bool.false_eq_true, ↓reduceIte]
    exact ⟨rfl, by omega, hc₁, hL, hi₁⟩
  · have hne : (r != S.unl) = true := by simpa using hr
    simp only [StateT.run_pure, pure_bind]
    simp only [show (r != Io_Mutex_State.unlocked) = true from hne, ↓reduceIte, StateT.run_bind,
      bind_assoc, pure_bind]
    refine WP.bind (wp_wait fits S rfl (g := L.set g .wait Heap.empty) rfl hi₁
      fun k₂ hk₂ G₂ m₂ hc₂ hi₂ => ?_)
    simp only [StateT.run_pure, pure_bind]
    refine WP.pure' ?_
    simp only [Io_Mutex_lockUncancelable.again23, ↓reduceIte]
    exact ⟨⟨by omega, hc₂, hi₂⟩, .inl (by omega)⟩

/-- `lock` by thread `t` at `out` (`g`): it holds the mutex, with the counter. -/
theorem lock_spec (t : ThreadId) (g : Gh) (hg : g.1.ph = .out) (io : Io) (G : ThreadId → Gh)
    (m : Mem) (d : Nat) (hi : proto.inv (upd G t g) m) :
    proto.WP t (Io_Mutex_lockUncancelable (cPtr.add 16) io) (fun _ G' m' d' => d' < d ∧
      m'.current = t ∧ ∃ hL, proto.inv (upd G' t (L.set g .holds hL)) m') G m d := by
  unfold Io_Mutex_lockUncancelable
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  rw [mptr]
  refine WP.bind (wp_cas fits S rfl (g := g) hg hi fun k₁ hk₁ G₁ m₁ r hc₁ hcase => ?_)
  -- the loop, from `spin`
  have hloop : ∀ G₃ m₃ d₃, lockInv t g d default G₃ m₃ d₃ →
      proto.WP t ((do
          let __do_lift ← loop (Io_Mutex_lockUncancelable.loop23 (cPtr.add 16) io)
            Io_Mutex_lockUncancelable.again23
          match __do_lift with
          | Io_Mutex_lockUncancelableExit.br22 => pure Io_Mutex_lockUncancelableExit.ret
          | e => pure e : CM Tgt Io_Mutex_lockUncancelableLocals Io_Mutex_lockUncancelableExit).run
          default)
        (fun a G₄ m₄ d₄ => proto.WP t (match a.1 with
          | Io_Mutex_lockUncancelableExit.ret => pure ()
          | _ => throw Error.panic)
          (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
            ∃ hL, proto.inv (upd G' t (L.set g .holds hL)) m') G₄ m₄ d₄)
        G₃ m₃ d₃ := by
    intro G₃ m₃ d₃ h₃
    simp only [StateT.run_bind]
    refine WP.bind (WP.mono ?_ (WP.loop _ _ (lockInv t g d) (fun _ => 0) (lockPost t g d)
      (loop23_body t g d io) default G₃ m₃ d₃ h₃))
    rintro ⟨e, s'⟩ G' m' d' ⟨rfl, hd', hc', hL, hi'⟩
    simp only [StateT.run_pure]
    refine WP.pure' ?_
    exact WP.pure' ⟨hd', hc', hL, hi'⟩
  rcases hcase with ⟨rfl, hL, hi₁⟩ | ⟨rfl, hi₁⟩ | ⟨rfl, hi₁⟩
  · simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind]
    refine WP.pure' ?_
    exact WP.pure' ⟨by omega, hc₁, hL, hi₁⟩
  · simp only [Option.isSome_some, ↓reduceIte, StateT.run_bind, bind_assoc]
    refine WP.bind (WP.callRC (fun e he => by cases he) fun a ha => ?_)
    cases ha
    simp only [StateT.run_pure, pure_bind]
    simp only [S, beq_iff_eq, reduceCtorEq, ↓reduceIte, pure_bind]
    exact hloop G₁ m₁ k₁ ⟨by omega, hc₁, hi₁⟩
  · simp only [Option.isSome_some, ↓reduceIte, StateT.run_bind, bind_assoc]
    refine WP.bind (WP.callRC (fun e he => by cases he) fun a ha => ?_)
    cases ha
    simp only [StateT.run_pure, pure_bind]
    simp only [S, beq_self_eq_true, ↓reduceIte, StateT.run_bind, bind_assoc]
    refine WP.bind (wp_wait fits S rfl (g := L.set g .wait Heap.empty) rfl hi₁
      fun k₂ hk₂ G₂ m₂ hc₂ hi₂ => ?_)
    simp only [StateT.run_pure, pure_bind]
    exact hloop G₂ m₂ k₂ ⟨by omega, hc₂, hi₂⟩

/-! ## `unlock` -/

/-- `unlock` by the holder `t` (`g`): it goes to `out`. -/
theorem unlock_spec (t : ThreadId) (g : Gh) (hg : g.1.ph = .holds) (io : Io) (G : ThreadId → Gh)
    (m : Mem) (d : Nat) (hi : proto.inv (upd G t g) m) :
    proto.WP t (Io_Mutex_unlock (cPtr.add 16) io) (fun _ G' m' d' => d' ≤ d ∧
      m'.current = t ∧ proto.inv (upd G' t (L.set g .out Heap.empty)) m') G m d := by
  unfold Io_Mutex_unlock
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  rw [mptr]
  refine WP.bind (wp_xchgUnlock fits S rfl (g := g) hg hi fun k₁ hk₁ G₁ m₁ r hc₁ hcase => ?_)
  rcases hcase with ⟨rfl, hi₁⟩ | ⟨rfl, hi₁⟩
  · simp only [S, StateT.run_pure, pure_bind]
    refine WP.pure' ?_
    exact WP.pure' ⟨by omega, hc₁, hi₁⟩
  · simp only [S, StateT.run_bind, bind_assoc, pure_bind]
    refine WP.bind (wp_wake fits (g := L.set g .wake Heap.empty) rfl hi₁
      fun k₂ hk₂ G₂ m₂ hc₂ hi₂ => ?_)
    simp only [StateT.run_pure, pure_bind]
    refine WP.pure' ?_
    exact WP.pure' ⟨by omega, hc₂, hi₂⟩


/-! ## The threads and the heap -/

theorem shape_size {X : ThreadId → Ph} {m : Mem} (h : Shape X m) : m.threads.size ≤ 4 := by
  obtain ⟨-, -, -, ⟨j, hj, -, hs, -⟩ | ⟨-, -, -, hs, -⟩⟩ := h <;> omega

/-- A task is thread 1, 2 or 3. -/
theorem task_at {X : ThreadId → Ph} {m : Mem} {t : ThreadId} {d : Bool} (h : Shape X m)
    (hx : X t = .task d) : 1 ≤ t ∧ t < m.threads.size ∧ t ≤ 3 := by
  have hs4 := shape_size h
  obtain ⟨-, -, hn, hph⟩ := h
  have ht : t < m.threads.size := by
    by_cases hc : t < m.threads.size
    · exact hc
    · rw [hn t (Nat.le_of_not_lt hc)] at hx; cases hx
  have h1 : 1 ≤ t := by
    by_cases hc : t = 0
    · subst hc
      rcases hph with ⟨j, -, h0, -⟩ | ⟨i, -, h0, -⟩ <;> rw [h0] at hx <;> cases hx
    · exact Nat.pos_of_ne_zero hc
  exact ⟨h1, ht, Nat.le_of_lt_succ (Nat.lt_of_lt_of_le ht hs4)⟩

/-- A task changes its place: a task again, or it has ended. -/
theorem shape_task {X : ThreadId → Ph} {m : Mem} {t : ThreadId} {d : Bool} (h : Shape X m)
    (hx : X t = .task d) (p : Ph) (hp : (∃ d', p = .task d') ∨ p = .fin) :
    Shape (upd X t p) m := by
  obtain ⟨h1, hlt, -⟩ := task_at h hx
  obtain ⟨h00, hrec, hn, hph⟩ := h
  have h0t : (0 : Nat) ≠ t := by unfold ThreadId at *; omega
  refine ⟨h00, fun u hu1 hu => ?_, fun u hu => ?_, ?_⟩
  · obtain ⟨jn, hr, hj, hk⟩ := hrec u hu1 hu
    refine ⟨jn, hr, fun hjn => ?_, ?_⟩
    · by_cases hut : u = t
      · subst hut; rw [hj hjn] at hx; cases hx
      · rw [upd_ne _ _ hut]; exact hj hjn
    · by_cases hut : u = t
      · subst hut; rw [upd_self]
        rcases hp with ⟨d', rfl⟩ | rfl
        · exact .inl ⟨d', rfl⟩
        · exact .inr rfl
      · rw [upd_ne _ _ hut]; exact hk
  · rw [upd_ne _ _ (by unfold ThreadId at *; omega)]; exact hn u hu
  · rw [upd_ne _ _ h0t]; exact hph

theorem count_le (p : Ph) : p.count ≤ 1 := by
  unfold Ph.count; split <;> decide

/-- The sum, when task `t` did not do its increment: at most 2. -/
theorem sum_le {X : ThreadId → Ph} {m : Mem} {t : ThreadId} (h : Shape X m)
    (hx : X t = .task false) : sum X ≤ 2 := by
  obtain ⟨h1, -, h3⟩ := task_at h hx
  have c1 := count_le (X 1)
  have c2 := count_le (X 2)
  have c3 := count_le (X 3)
  have c0 : (X t).count = 0 := by rw [hx]; rfl
  have ht : t = 1 ∨ t = 2 ∨ t = 3 := by unfold ThreadId at *; omega
  clear h hx
  unfold sum
  rcases ht with rfl | rfl | rfl <;> omega

/-- Task `t`'s increment: the sum is one more. -/
theorem sum_succ {X : ThreadId → Ph} {t : ThreadId} (h1 : 1 ≤ t) (h3 : t ≤ 3)
    (hx : X t = .task false) : sum (upd X t (.task true)) = sum X + 1 := by
  have c0 : (X t).count = 0 := by rw [hx]; rfl
  unfold sum
  rcases (by unfold ThreadId at *; omega : t = 1 ∨ t = 2 ∨ t = 3) with rfl | rfl | rfl
  · rw [upd_self, upd_ne _ _ (by decide : (2 : Nat) ≠ 1), upd_ne _ _ (by decide : (3 : Nat) ≠ 1)]
    show 1 + _ + _ = _; omega
  · rw [upd_self, upd_ne _ _ (by decide : (1 : Nat) ≠ 2), upd_ne _ _ (by decide : (3 : Nat) ≠ 2)]
    show _ + 1 + _ = _; omega
  · rw [upd_self, upd_ne _ _ (by decide : (1 : Nat) ≠ 3), upd_ne _ _ (by decide : (2 : Nat) ≠ 3)]
    show _ + _ + 1 = _; omega

/-- The counter's bytes: in block 0, from byte 20 on. -/
theorem pts_none {v : BitVec 32} {h : Heap} (hp : pts (cPtr.add 20) 4 v h) {b x : Nat}
    (hx : (b = 0 ∧ x < 20) ∨ b = 1) : h (b, x) = none := by
  obtain ⟨A, S, K, bs, -, -, -, ⟨b', hb, -, hl⟩, -⟩ := hp
  cases hb
  rw [hl, if_neg]
  simp only [cPtr, Ptr.add, not_and, Nat.not_lt]
  intro hb0 h2; simp at hb0 h2; unfold BlockId at *; omega

/-- No thread owns a byte of block 0 before the counter, or a byte of block 1. -/
theorem own_none {G : ThreadId → Gh} {m : Mem} (hi : proto.inv G m) (u : ThreadId) {b x : Nat}
    (hx : (b = 0 ∧ x < 20) ∨ b = 1) : L.own G m u (b, x) = none := by
  unfold Lock.own; split
  · rfl
  · show ((G u).1.part ∪ (G u).1.held) (b, x) = none
    rw [hi.2.parts u, Heap.empty_union]
    by_cases hh : L.ph (G u) = .holds
    · exact pts_none (hi.1.res u hh) hx
    · rw [show (G u).1.held = L.held (G u) from rfl, hi.1.idle u hh]; rfl

/-- The cell of byte `x < 24` of the `Counter`. -/
theorem blk_heap {m : Mem} (hb : BlkOk m) {x : Nat} (hx : x < 24) : m.heap (0, x) ≠ none := by
  obtain ⟨blk, hblk, hl, hs, -⟩ := hb
  simp only [Mem.heap, hblk]
  rw [dite_eq_left_of_eq_true (eq_true ⟨hl, by omega⟩)]
  simp

/-- The same first cell: the same block 0. -/
theorem blk_keep {m m' : Mem} (hb : BlkOk m) (h : m'.heap (0, 0) = m.heap (0, 0)) : BlkOk m' := by
  obtain ⟨blk, hblk, hl, hs, ha, hk⟩ := hb
  have hc : m.heap (0, 0) = some ⟨blk.bytes[0]'(by omega), blk.addr, blk.bytes.size, blk.kind⟩ := by
    simp only [Mem.heap, hblk]; rw [dite_eq_left_of_eq_true (eq_true ⟨hl, by omega⟩)]
  rw [hc] at h
  obtain ⟨blk', hblk', hl', ho', he⟩ := Mem.heap_some h
  simp only [Cell.mk.injEq] at he
  obtain ⟨-, hA, hS, hK⟩ := he
  exact ⟨blk', hblk', by simpa using hl', by rw [← hS, hs], by rw [← hA, ha], by rw [← hK, hk]⟩

/-- Block 1, live with 16 bytes. -/
def Blk1 (m : Mem) : Prop := ∃ blk, m.blocks[1]? = some blk ∧ blk.live = true ∧ blk.bytes.size = 16

theorem blk1_keep {m m' : Mem} (hb : Blk1 m) (h : m'.heap (1, 0) = m.heap (1, 0)) : Blk1 m' := by
  obtain ⟨blk, hblk, hl, hs⟩ := hb
  have hc : m.heap (1, 0) = some ⟨blk.bytes[0]'(by omega), blk.addr, blk.bytes.size, blk.kind⟩ := by
    simp only [Mem.heap, hblk]; rw [dite_eq_left_of_eq_true (eq_true ⟨hl, by omega⟩)]
  rw [hc] at h
  obtain ⟨blk', hblk', hl', ho', he⟩ := Mem.heap_some h
  simp only [Cell.mk.injEq] at he
  exact ⟨blk', hblk', by simpa using hl', by rw [← he.2.2.1, hs]⟩

theorem blk1_heap {m : Mem} (hb : Blk1 m) : m.heap (1, 0) ≠ none := by
  obtain ⟨blk, hblk, hl, hs⟩ := hb
  simp only [Mem.heap, hblk]
  rw [dite_eq_left_of_eq_true (eq_true ⟨hl, by omega⟩)]
  simp

/-- A step of thread `t` (not joined) on its own part keeps `U`, with `t`'s new ghost value `g`
(no part) and the shape `hsh`. -/
theorem U_stepIn {G : ThreadId → Gh} {m m' : Mem} {t : ThreadId} {g : Gh} {hQ : Heap}
    (hi : proto.inv G m) (hc : m.current = t) (hjt : joinedB m t = false)
    (hs : StepIn (m.heap.diff (L.own G m t)) m m')
    (hm' : m'.heap = hQ ∪ m.heap.diff (L.own G m t))
    (hd : Heap.Disjoint hQ (m.heap.diff (L.own G m t)))
    (hsh : Shape (upd (fun u => (G u).2) t g.2) m) (hpart : g.1.part = Heap.empty) :
    U (upd G t g) m' := by
  have hrest : ∀ b x, (b = 0 ∧ x < 20) ∨ b = 1 →
      m.heap.diff (L.own G m t) (b, x) = m.heap (b, x) := fun b x hx => by
    simp [Heap.diff, own_none hi t hx]
  have hcell : ∀ b x, (b = 0 ∧ x < 20) ∨ b = 1 → m.heap (b, x) ≠ none →
      m'.heap (b, x) = m.heap (b, x) := fun b x hx hn => by
    rw [hm', Heap.union_of_right ((hd (b, x)).resolve_right (by rw [hrest b x hx]; exact hn)),
      hrest b x hx]
  have hjb : joinedB m' = joinedB m := joinedB_congr hs.threads
  refine ⟨?_, fun e he hb ho => ?_, fun u => ?_,
    blk_keep hi.2.blk (hcell 0 0 (.inl ⟨rfl, by decide⟩) (blk_heap hi.2.blk (by decide))),
    blk1_keep hi.2.blk1 (hcell 1 0 (.inr rfl) (blk1_heap hi.2.blk1)), fun v hv => ?_⟩
  · rw [snd_upd]; unfold Shape at hsh ⊢; rw [hs.threads, hs.groups, hjb]; exact hsh
  · rcases hs.fp e he with h' | ⟨-, hnt, -⟩
    · rcases hi.2.io e h' hb ho with ⟨hk, h''⟩ | h''
      · exact .inl ⟨hk, someLe_mono hs.threads (fun u _ => hs.clock u) h''⟩
      · exact .inr (allLe_stepIn hs h'')
    · exact absurd ⟨e.off, Nat.le_refl _, .inr rfl, by
        rw [hb, hrest _ _ (.inl ⟨rfl, by omega⟩)]; exact blk_heap hi.2.blk (by omega)⟩ hnt
  · unfold upd; split
    · exact hpart
    · exact hi.2.parts u
  · rw [hjb] at hv
    have hvt : v ≠ t := fun e => by rw [e, hjt] at hv; cases hv
    obtain ⟨h1, h2⟩ := hi.2.jle v hv
    refine ⟨by rw [upd_ne _ _ hvt]; exact h1, ?_⟩
    rw [hs.others v (hc ▸ hvt)]
    exact VClock.le_trans h2 (hs.clock 0)

/-! ## `io` -/

theorem noRace_io {m : Mem} (hio : IoOk m) (ht : m.current < m.threads.size) :
    NoRace m 0 0 16 .read :=
  (ioOk_iff.mp hio).noRace_read ht covers_io

/-- A read of `io` (bytes 0..16 of the `Counter`) by a thread that is not joined: no race, and
the invariant holds after it. -/
theorem step_io {G : ThreadId → Gh} {m : Mem} (hi : proto.inv G m)
    (ht : m.current < m.threads.size) (hjc : joinedB m m.current = false) :
    (load Io 8 cPtr).run m = pure (⟨⟩, m.recordAt 0 0 16 .read) ∧
      proto.inv G (m.recordAt 0 0 16 .read) := by
  obtain ⟨blk, hblk, hl, hs, ha, hk⟩ := hi.2.blk
  have hacc : m.access cPtr (Enc.size Io) 8 = pure (0, blk, 0) :=
    access_of (p := cPtr) rfl hblk hl (by decide)
      (by rw [show Enc.size Io = 16 from rfl]; simp [cPtr, hs]) (by simpa [cPtr] using ha)
  refine ⟨load_run hacc rfl (noRace_io hi.2.io ht), ?_, ?_⟩
  · refine hi.1.read (b := 0) (o := 0) (n := 16) (Array.getElem?_eq_some_iff.mp hblk).1 (by decide)
      (fun u x _ hx => own_none hi u (.inl ⟨rfl, by omega⟩))
      (fun hL hR x _ hx => pts_none hR (.inl ⟨rfl, by omega⟩)) (.inr (.inl (by decide)))
  · refine ⟨hi.2.shape, ioOk_iff.mpr ((ioOk_iff.mp hi.2.io).read ht
      (by rw [hi.1.own.csize]) 0 0 16), hi.2.parts, hi.2.blk, hi.2.blk1, fun v hv => ?_⟩
    · have hv' : joinedB m v = true := hv
      obtain ⟨h1, h2⟩ := hi.2.jle v hv'
      refine ⟨h1, ?_⟩
      have hvc : v ≠ m.current := fun e => by rw [e, hjc] at hv'; cases hv'
      show VClock.le ((m.clocks.set! m.current _)[v]!) ((m.clocks.set! m.current _)[0]!) = true
      rw [Proto.getElem!_set!_ite, if_neg (fun h => hvc h.1)]
      exact VClock.le_trans h2 (recordAt_le m 0 0 16 .read 0)

/-- A read of `io` by thread `t` (not joined) in generated code. -/
theorem wp_io {σ : Type} {s : σ} {t : ThreadId} {G : ThreadId → Gh} {m : Mem} {d : Nat} {g : Gh}
    (hi : proto.inv (upd G t g) m) (hc : m.current = t) (ht : t < m.threads.size)
    (hjt : joinedB m t = false) {Q : Io × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ m', m'.current = t → m'.threads = m.threads → proto.inv (upd G t g) m' →
      Q (⟨⟩, s) G m' d) :
    proto.WP t ((liftM (load Io 8 cPtr) : CM Tgt σ Io).run s) Q G m d := by
  obtain ⟨hrun, hi'⟩ := step_io hi (hc ▸ ht) (hc ▸ hjt)
  refine WP.liftM (fun e he => (MemM.noErr_of_run hrun e he).elim) fun v m' hr => ?_
  rw [hrun] at hr
  simp only [pure, ExceptT.pure, ExceptT.mk, ExceptT.run, Option.some.injEq, Except.ok.injEq,
    Prod.mk.injEq] at hr
  obtain ⟨-, rfl⟩ := hr
  cases v
  exact ⟨rfl, h _ hc rfl hi'⟩

/-! ## A task -/

/-- A task at `out`; `done`: after its increment. -/
def gTask (done : Bool) : Gh := (⟨.out, Heap.empty, Heap.empty⟩, .task done)

/-- A task that holds the mutex and the counter `h`. -/
def gHold (done : Bool) (h : Heap) : Gh := (⟨.holds, Heap.empty, h⟩, .task done)

/-- The holder's load of the counter: the increments of the tasks. -/
theorem wp_cntLoad {σ : Type} {s : σ} {t : ThreadId} {dn : Bool} {hL : Heap} {G : ThreadId → Gh}
    {m : Mem} {d : Nat} (hi : proto.inv (upd G t (gHold dn hL)) m) (hc : m.current = t)
    {Q : BitVec 32 × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ m' hQ, m'.current = t → m'.threads = m.threads →
      proto.inv (upd G t (gHold dn hQ)) m' →
      Q (BitVec.ofNat 32 (sum fun u => (upd G t (gHold dn hL) u).2), s) G m' d) :
    proto.WP t ((liftM (load (BitVec 32) 4 (cPtr.add 20)) : CM Tgt σ (BitVec 32)).run s) Q G m d := by
  have hh : L.ph (upd G t (gHold dn hL) t) = .holds := by rw [upd_self]; rfl
  obtain ⟨ht, hjt⟩ := hi.1.live t (by rw [hh]; decide)
  have hres : R (fun u => (upd G t (gHold dn hL) u).2) hL := by
    have := hi.1.res t hh
    rwa [show L.held (upd G t (gHold dn hL) t) = hL by rw [upd_self]; rfl] at this
  have hown : L.own (upd G t (gHold dn hL)) m t = hL := by
    rw [L.own_live hjt, upd_self]; exact Heap.empty_union hL
  refine WP.liftM_owned (TTriple.load (by decide)) hi.1.own hc ht (by rw [hown]; exact hres)
    fun a m' hQ hr ho' hq hs hm' hd => ?_
  obtain ⟨rfl, hq'⟩ := sep_lift.mp hq
  have hQe : L.part (gHold dn hQ) ∪ L.held (gHold dn hQ) = hQ := Heap.empty_union hQ
  have hl := hi.1.stepIn (g := gHold dn hQ) hc hjt (by rw [hQe]; exact ho') hs (by rw [hQe]; exact hm')
    (by rw [hQe]; exact hd) (by rw [upd_self]; rfl) (fun _ => .inl rfl) (fun h => absurd rfl h)
    (fun h => absurd hh h) (fun _ => by
      show R (fun u => (upd (upd G t (gHold dn hL)) t (gHold dn hQ) u).2) hQ
      rw [snd_upd_upd G t (gHold dn hL) (gHold dn hQ) rfl]; exact hq')
  rw [upd_upd] at hl
  refine h m' hQ (hs.current.trans hc) hs.threads ⟨hl, ?_⟩
  have hx : (fun u => (upd G t (gHold dn hL) u).2) t = .task dn := by
    show (upd G t (gHold dn hL) t).2 = _; rw [upd_self]; rfl
  have := U_stepIn (g := gHold dn hQ) hi hc hjt hs hm' hd (by
    show Shape (upd _ t (Ph.task dn)) m
    rw [← hx, upd_same]; exact hi.2.shape) rfl
  rwa [upd_upd] at this

/-- The holder's store of `w`, the increments of the tasks after its own. -/
theorem wp_cntStore {σ : Type} {s : σ} {t : ThreadId} {hL : Heap} {G : ThreadId → Gh}
    {m : Mem} {d : Nat} (w : BitVec 32) (hi : proto.inv (upd G t (gHold false hL)) m)
    (hc : m.current = t)
    (hw : w = BitVec.ofNat 32 (sum fun u => (upd G t (gHold true hL) u).2))
    {Q : Unit × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ m' hQ, m'.current = t → m'.threads = m.threads →
      proto.inv (upd G t (gHold true hQ)) m' → Q ((), s) G m' d) :
    proto.WP t ((liftM (store (α := BitVec 32) 4 (cPtr.add 20) w) : CM Tgt σ Unit).run s) Q G m d := by
  have hh : L.ph (upd G t (gHold false hL) t) = .holds := by rw [upd_self]; rfl
  obtain ⟨ht, hjt⟩ := hi.1.live t (by rw [hh]; decide)
  have hres : R (fun u => (upd G t (gHold false hL) u).2) hL := by
    have := hi.1.res t hh
    rwa [show L.held (upd G t (gHold false hL) t) = hL by rw [upd_self]; rfl] at this
  have hown : L.own (upd G t (gHold false hL)) m t = hL := by
    rw [L.own_live hjt, upd_self]; exact Heap.empty_union hL
  refine WP.liftM_owned (TTriple.store (by decide) w) hi.1.own hc ht (by rw [hown]; exact hres)
    fun a m' hQ hr ho' hq hs hm' hd => ?_
  have hQe : L.part (gHold true hQ) ∪ L.held (gHold true hQ) = hQ := Heap.empty_union hQ
  have hX : (fun u => (upd (upd G t (gHold false hL)) t (gHold true hQ) u).2) =
      fun u => (upd G t (gHold true hL) u).2 := by
    rw [upd_upd]; funext u; unfold upd; split <;> rfl
  have hl := hi.1.stepIn (g := gHold true hQ) hc hjt (by rw [hQe]; exact ho') hs
    (by rw [hQe]; exact hm') (by rw [hQe]; exact hd) (by rw [upd_self]; rfl) (fun _ => .inl rfl)
    (fun h => absurd rfl h) (fun h => absurd hh h) (fun _ => by
      show R (fun u => (upd (upd G t (gHold false hL)) t (gHold true hQ) u).2) hQ
      rw [hX]; unfold R; rw [← hw]; exact hq)
  rw [upd_upd] at hl
  refine h m' hQ (hs.current.trans hc) hs.threads ⟨hl, ?_⟩
  have hx : (fun u => (upd G t (gHold false hL) u).2) t = .task false := by
    show (upd G t (gHold false hL) t).2 = _; rw [upd_self]; rfl
  have := U_stepIn (g := gHold true hQ) hi hc hjt hs hm' hd
    (shape_task hi.2.shape hx _ (.inl ⟨true, rfl⟩)) rfl
  rwa [upd_upd] at this

/-- A task's `add`: `io`, `lock`, the increment of the counter, `io`, `unlock`. -/
theorem add_spec (t : ThreadId) (G : ThreadId → Gh) (m : Mem) (d : Nat)
    (hi : proto.inv (upd G t (gTask false)) m) (hc : m.current = t) :
    proto.WP t (add cPtr) (fun _ G' m' _ => m'.current = t ∧ proto.inv (upd G' t (gTask true)) m')
      G m d := by
  have hx : (fun u => (upd G t (gTask false) u).2) t = .task false := by
    show (upd G t (gTask false) t).2 = _; rw [upd_self]; rfl
  obtain ⟨h1, ht, h3⟩ := task_at hi.2.shape hx
  have hjt : joinedB m t = false :=
    (hi.1.live t (by rw [upd_self]; exact (by decide : LPh.out ≠ LPh.gone))).2
  unfold add
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, pure_bind]
  rw [show cPtr.add 0 = cPtr from rfl]
  -- the read of `io`
  refine WP.bind (wp_io hi hc ht hjt fun m₁ hc₁ ht₁ hi₁ => ?_)
  -- `lock`
  refine WP.bind (WP.callC (WP.mono ?_ (lock_spec t (gTask false) rfl _ G m₁ d hi₁)))
  rintro _ G₂ m₂ d₂ ⟨hd₂, hc₂, hL, hi₂⟩
  have hi₂' : proto.inv (upd G₂ t (gHold false hL)) m₂ := hi₂
  -- the load of the counter
  refine WP.bind (wp_cntLoad hi₂' hc₂ fun m₃ hQ hc₃ ht₃ hi₃ => ?_)
  have hx₂ : (fun u => (upd G₂ t (gHold false hL) u).2) t = .task false := by
    show (upd G₂ t (gHold false hL) t).2 = _; rw [upd_self]; rfl
  have hsum := sum_le hi₂'.2.shape hx₂
  generalize hS : (sum fun u => (upd G₂ t (gHold false hL) u).2) = S at hsum ⊢
  have hS3 : S + 1 < 2 ^ 32 := Nat.lt_of_le_of_lt (by omega : S + 1 ≤ 3) (by decide)
  have hS32 : (BitVec.ofNat 32 S).toNat = S := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  -- the add
  refine WP.bind (WP.callRC (fun e he => (add_one_noErr (by rw [hS32]; exact hS3) e he).elim)
    fun v₃ hadd => ?_)
  have hv₃ := add_one_ok hadd (by rw [hS32]; exact hS3)
  rw [hS32] at hv₃
  -- the store
  have hsucc : (sum fun u => (upd G₂ t (gHold true hQ) u).2) = S + 1 := by
    rw [← hS, snd_upd, snd_upd]
    have := sum_succ (X := upd (fun u => (G₂ u).2) t (.task false)) h1 h3 (upd_self _ _ _)
    rw [upd_upd] at this; exact this
  refine WP.bind (wp_cntStore v₃ hi₃ hc₃ (by
    apply BitVec.eq_of_toNat_eq
    rw [hv₃, hsucc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hS3]) fun m₄ hQ' hc₄ ht₄ hi₄ => ?_)
  -- the read of `io`
  have hl₄ := hi₄.1.live t (by rw [upd_self]; exact (by decide : LPh.holds ≠ LPh.gone))
  refine WP.bind (wp_io hi₄ hc₄ hl₄.1 hl₄.2 fun m₅ hc₅ ht₅ hi₅ => ?_)
  -- `unlock`
  refine WP.bind (WP.callC (WP.mono ?_ (unlock_spec t (gHold true hQ') rfl _ G₂ m₅ d₂ hi₅)))
  rintro _ G₃ m₆ d₃ ⟨hd₃, hc₆, hi₆⟩
  simp only [StateT.run_pure, pure_bind]
  refine WP.pure' ?_
  exact WP.pure' ⟨hc₆, hi₆⟩

/-- A task at its end: `out` to `gone`, `task true` to `fin`. -/
theorem inv_end {G : ThreadId → Gh} {m : Mem} {t : ThreadId}
    (hi : proto.inv (upd G t (gTask true)) m) :
    proto.inv (upd G t (⟨.gone, Heap.empty, Heap.empty⟩, .fin)) m := by
  have hx : (fun u => (upd G t (gTask true) u).2) t = .task true := by
    show (upd G t (gTask true) t).2 = _; rw [upd_self]; rfl
  have hX : (fun u => (upd (upd G t (gTask true)) t (⟨.gone, Heap.empty, Heap.empty⟩, .fin) u).2) =
      upd (fun u => (upd G t (gTask true) u).2) t .fin := snd_upd _ _ _
  have hsum : sum (fun u => (upd (upd G t (gTask true)) t (⟨.gone, Heap.empty, Heap.empty⟩, .fin) u).2) =
      sum (fun u => (upd G t (gTask true) u).2) := by
    rw [hX]; unfold sum; unfold upd
    split <;> split <;> split <;> simp_all [Ph.count]
  have hl := hi.1.ghost (t := t) (g := (⟨.gone, Heap.empty, Heap.empty⟩, .fin))
    (by rw [upd_self]; rfl) (.inr (.inl rfl)) (by rw [upd_self]; rfl) rfl
    (fun h => absurd rfl h)
    (fun hL hR => by
      have hR' : R (fun u => (upd G t (gTask true) u).2) hL := hR
      show R _ hL; unfold R at hR' ⊢; rw [hsum]; exact hR')
  rw [upd_upd] at hl
  refine ⟨hl, ?_⟩
  have hu := hi.2
  have hsh := shape_task hu.shape hx .fin (.inr rfl)
  rw [snd_upd, upd_upd] at hsh
  refine ⟨by rw [snd_upd]; exact hsh, hu.io, fun u => ?_, hu.blk, hu.blk1, fun v hv => ?_⟩
  · unfold upd; split
    · rfl
    · rename_i h; have := hu.parts u; rwa [upd_ne _ _ h] at this
  · obtain ⟨h1, h2⟩ := hu.jle v hv
    refine ⟨?_, h2⟩
    unfold upd; split
    · rfl
    · rename_i h; rwa [upd_ne _ _ h] at h1

/-- A task spawned nothing. -/
theorem joinedAll_task {G : ThreadId → Gh} {m : Mem} {u : ThreadId} (hi : proto.inv G m)
    (hu : 0 < u) : joinedAll u m := by
  intro r hr hs
  obtain ⟨h0, hrec, -⟩ := hi.2.shape
  obtain ⟨i, hi', rfl⟩ := Array.mem_iff_getElem.mp hr
  by_cases hi0 : i = 0
  · subst hi0
    rw [Array.getElem?_eq_getElem hi'] at h0
    rw [Option.some.inj h0] at hs; exact absurd hs (Nat.ne_of_lt hu)
  · obtain ⟨jn, hr', -⟩ := hrec i (Nat.pos_of_ne_zero hi0) hi'
    rw [Array.getElem?_eq_getElem hi'] at hr'
    rw [Option.some.inj hr'] at hs; exact absurd hs (Nat.ne_of_lt hu)

/-- A task: `add` on the `Counter`, then its end. -/
theorem dispatch_spec (tgt : Tgt) (g : Gh) (hg : proto.init tgt g) (u : ThreadId)
    (G : ThreadId → Gh) (m : Mem) (d : Nat) (hu : 0 < u) (hgu : G u = g) (hi : proto.inv G m) :
    proto.WP u (dispatch tgt) (proto.QKid u) G { m with current := u } d := by
  cases tgt with
  | add p =>
    obtain ⟨rfl, rfl⟩ := hg
    show proto.WP u ((fun _ => ()) <$> add cPtr) _ G _ d
    refine WP.map (WP.mono ?_ (add_spec u G _ d
      (by rw [show gTask false = G u from hgu.symm, upd_same]
          exact fits.cur u hi (by rw [hgu]; exact (by decide : LPh.out ≠ LPh.gone))) rfl))
    rintro _ G' m' _ ⟨-, hi'⟩
    exact ⟨_, inv_end hi', ⟨rfl, rfl⟩, fun _ => joinedAll_task hi' hu⟩

/-! ## `main` -/

theorem enc_io (io : Io) : (Enc.encode io).size = 16 := by
  show (Array.replicate 16 _).size = 16; simp

/-- The initial mutex. -/
def mutex0 : Io_Mutex := { state := { raw := Io_Mutex_State.unlocked } }

theorem enc_mutex : Enc.encode mutex0 = Enc.encode (0 : BitVec 32) := by decide +kernel

theorem enc_u32 (v : BitVec 32) : (Enc.encode v).size = 4 := LawfulEnc.size_encode v

/-- The initial `Io.Group`. -/
def group0 : Io_Group := { token := { raw := none }, state := 0 }

theorem enc_group : (Enc.encode group0).size = 16 := by decide +kernel

/-- `main` after `j` spawns. -/
def gSpawn (j : Nat) : Gh := (⟨.out, Heap.empty, Heap.empty⟩, .spawn j)

/-- `main` after `i` joins. -/
def gJoins (i : Nat) : Gh := (⟨.out, Heap.empty, Heap.empty⟩, .joins i)

/-- The start: no thread. -/
def G0 : ThreadId → Gh := fun _ => (⟨.gone, Heap.empty, Heap.empty⟩, .none)

/-- The `Counter` in three parts, after `main`'s stores: `io`, the mutex, the counter. -/
def Parts (io : Io) (A : Nat) : Assn :=
  bytesAt cPtr A 24 .stack (Enc.encode io) ∗ (bytesAt (cPtr.add 16) A 24 .stack (Enc.encode mutex0) ∗
    bytesAt (cPtr.add 20) A 24 .stack (Enc.encode (0 : BitVec 32)))

/-- Before its first spawn: `main` alone owns the `Counter` and the `Io.Group`. The lock starts:
it owns the mutex and the counter; `io` and the `Io.Group` belong to no thread. -/
theorem inv_start {m : Mem} {io : Io} {A A' : Nat} {h hG : Heap}
    (ho : Owned (upd (fun _ => Heap.empty) 0 (h ∪ hG)) m) (hdG : Heap.Disjoint h hG)
    (hp : Parts io A h) (hg : bytesAt gPtr A' 16 .stack (Enc.encode group0) hG) (hA : A % 8 = 0)
    (hth : m.threads = #[{ spawner := 0, joined := true }]) (hat : m.atomics = #[])
    (hq : m.waiters = #[]) (hgr : m.groups = #[]) :
    proto.inv (upd G0 0 (gSpawn 0)) m := by
  obtain ⟨hI, hWC, dI, rfl, hio, hW, hC, dWC, rfl, hw, hc⟩ := hp
  have hs : ((hI ∪ (hW ∪ hC)) ∪ hG).Sub m.heap := by have := ho.sub 0; rwa [upd_self] at this
  have hs0 : (hI ∪ (hW ∪ hC)).Sub m.heap := Heap.sub_union_left.trans hs
  have hsW : hW.Sub m.heap := (Heap.sub_union_left.trans (Heap.sub_union_right dI)).trans hs0
  have hsI : hI.Sub m.heap := Heap.sub_union_left.trans hs0
  have hsG : hG.Sub m.heap := (Heap.sub_union_right hdG).trans hs
  have h1 : m.threads.size = 1 := by rw [hth]; rfl
  have hcell : ∀ x, x < 16 → hI (0, x) ≠ none := fun x hx =>
    bytesAt_in hio rfl (by simp [cPtr]) (by simp [cPtr, enc_io]; omega)
  have hcellW : ∀ x, 16 ≤ x → x < 16 + 4 → hW (0, x) ≠ none := fun x h1 h2 =>
    bytesAt_in hw rfl (by simp [cPtr, Ptr.add]; omega)
      (by simp [cPtr, Ptr.add, enc_mutex, enc_u32]; omega)
  -- the blocks, and the mutex's bytes
  obtain ⟨blk, hblk, hl, hA', hS', hK', -⟩ := bytesAt_blk (m := m) hio hsI rfl
    (by rw [enc_io]; decide)
  obtain ⟨blk', hblk', -, -, -, -, hx⟩ := bytesAt_blk (m := m) hw hsW rfl
    (by rw [enc_mutex, enc_u32]; decide)
  rw [hblk] at hblk'; cases hblk'
  obtain ⟨blkG, hblkG, hlG, -, hSG, -, -⟩ := bytesAt_blk (m := m) hg hsG rfl
    (by rw [enc_group]; decide)
  have hbk : BlkOk m := ⟨blk, hblk, hl, hS', by rw [hA']; exact hA, hK'⟩
  have h0 : L.U32 m 0 := by
    show (intOfBytes 32 (curBytes m 0 16 4)).run = _
    unfold curBytes; rw [hblk]
    simp only [Option.map_some, Option.getD_some]
    rw [show (16 : Nat) = (cPtr.add 16).off.toNat from rfl, show 4 = (Enc.encode mutex0).size by
      rw [enc_mutex, enc_u32], hx, enc_mutex]
    exact intOfBytes_rmw 0
  -- main keeps the mutex and the counter; `io` and the `Io.Group` belong to no thread
  have hsub : (Heap.empty ∪ (hC ∪ hW)).Sub ((hI ∪ (hW ∪ hC)) ∪ hG) := by
    rw [Heap.empty_union, Heap.union_comm dWC.symm]
    exact (Heap.sub_union_right dI).trans Heap.sub_union_left
  have ho' := ho.shrink (t := 0) (by rw [upd_self]; exact hsub)
  rw [upd_upd] at ho'
  have hGu : ∀ u, u ≠ 0 → upd G0 0 (gSpawn 0) u = G0 u := fun u h => upd_ne _ _ h
  have hjt : joinedB m 0 = false := rfl
  have hjb : ∀ u, joinedB m u = false := by
    intro u; unfold joinedB
    by_cases hu : u = 0
    · subst hu; rfl
    · have : m.threads.size ≤ u := by rw [h1]; unfold ThreadId at *; omega
      simp [hu, Array.getElem?_eq_none this]
  refine ⟨Inv.make (t := 0) (hL := hC) (hW := hW) ho' hjt (fun u hu => ?_) (by rw [upd_self]; rfl)
    (by rw [upd_self]; exact fun _ => .inl rfl) dWC.symm (fun u => ?_) (fun u => ?_) ?_
    (fun x h1 h2 => hcellW x h1 h2) ⟨blk, hblk, hl, by rw [hS']; decide,
      by show (blk.addr + 16) % 4 = 0; rw [hA']; omega,
      by rw [hK']; decide⟩ h0 (by rw [hat]; simp) hq (fun u hu => ?_) (by rw [h1]; decide), ?_⟩
  · rw [upd_ne _ _ hu]
    unfold Lock.own; rw [hGu u hu]; split <;> rfl
  · by_cases hu : u = 0
    · subst hu; rw [upd_self]; exact .inl ⟨rfl, by rw [h1]; decide, rfl⟩
    · rw [hGu u hu]; exact .inr rfl
  · by_cases hu : u = 0
    · subst hu; rw [upd_self]; rfl
    · rw [hGu u hu]; rfl
  · -- the counter holds `0`
    show pts (cPtr.add 20) 4 (BitVec.ofNat 32 (sum _)) hC
    have hsum : sum (fun u => (upd G0 0 (gSpawn 0) u).2) = 0 := by
      show (upd G0 0 (gSpawn 0) 1).2.count + (upd G0 0 (gSpawn 0) 2).2.count +
        (upd G0 0 (gSpawn 0) 3).2.count = 0
      rw [hGu 1 (by decide), hGu 2 (by decide), hGu 3 (by decide)]; rfl
    rw [hsum]
    exact ⟨A, 24, .stack, Enc.encode (0 : BitVec 32), by simp [cPtr, Ptr.add]; omega, enc_u32 0,
      LawfulEnc.decode_encode _, hc, by decide⟩
  · have : u = 0 := by rw [h1] at hu; unfold ThreadId at *; omega
    subst this; exact VClock.le_refl _
  · refine ⟨⟨by rw [hth]; rfl, fun u hu1 hu => by rw [h1] at hu; unfold ThreadId at *; omega,
      fun u hu => ?_, .inl ⟨0, by decide, ?_, h1, by rw [hgr]; simp [grp], hjb⟩⟩,
      fun e he hb ho16 => .inr fun u hu => ?_, fun u => ?_, hbk, ⟨blkG, hblkG, hlG, hSG⟩,
      fun v hv => by rw [hjb v] at hv; cases hv⟩
    · show (upd G0 0 (gSpawn 0) u).2 = _
      rw [hGu u (by rw [h1] at hu; unfold ThreadId at *; omega)]; rfl
    · show (upd G0 0 (gSpawn 0) 0).2 = _; rw [upd_self]; rfl
    · have : u = 0 := by rw [h1] at hu; unfold ThreadId at *; omega
      subst this
      exact ho.owns 0 (by rw [h1]; decide) e he (.inl ⟨e.off, Nat.le_refl _, .inr rfl, by
        rw [upd_self, hb]; simp only [Heap.union_apply]
        have := hcell e.off ho16
        cases e' : hI (0, e.off) with
        | none => exact absurd e' this
        | some c => simp⟩)
    · by_cases hu : u = 0
      · subst hu; rw [upd_self]; rfl
      · rw [hGu u hu]; rfl

theorem grp_succ (j : Nat) : grp (j + 1) = (grp j).push (gPtr, j + 1) := by
  simp [grp, Array.range_succ]

/-- The sum reads only the tasks 1, 2, 3. -/
theorem sum_congr {X X' : ThreadId → Ph} (h : ∀ u, 1 ≤ u → u ≤ 3 → (X' u).count = (X u).count) :
    sum X' = sum X := by
  unfold sum
  rw [h 1 (by decide) (by decide), h 2 (by decide) (by decide), h 3 (by decide) (by decide)]

theorem R_main {G : ThreadId → Gh} {hL : Heap} {g : Gh} (hR : L.R G hL) :
    L.R (upd G 0 g) hL := by
  have hR' : R (fun u => (G u).2) hL := hR
  show R _ hL; unfold R at hR' ⊢
  rw [sum_congr (X := fun u => (G u).2) fun u h1 _ => by
    show (upd G 0 g u).2.count = _; rw [upd_ne _ _ (by unfold ThreadId at *; omega)]]
  exact hR'

/-- The spawn of task `j + 1` by `main` (`Group.async`): the group records it. -/
theorem inv_spawn {G₁ : ThreadId → Gh} {m₁ m' : Mem} {child : ThreadId} {j : Nat} (hj : j < 3)
    (hi : proto.inv G₁ m₁) (hg : G₁ 0 = gSpawn j)
    (hf : (Thread.fork.run { m₁ with current := 0 }).run = some (.ok (child, m'))) :
    child = j + 1 ∧ m'.current = 0 ∧
      proto.inv (upd (upd G₁ child (gTask false)) 0 (gSpawn (j + 1)))
        { m' with groups := m'.groups.push (gPtr, child) } := by
  obtain ⟨h00, hrec, hnone, hph⟩ := hi.2.shape
  have hX0 : (G₁ 0).2 = .spawn j := by rw [hg]; rfl
  obtain ⟨j', -, h0, hsz, hgr, hjb⟩ | ⟨i, -, h0, -⟩ := hph
  rotate_left
  · exfalso; change (G₁ 0).2 = _ at h0; rw [hX0] at h0; cases h0
  have : j' = j := by change (G₁ 0).2 = _ at h0; rw [hX0] at h0; cases h0; rfl
  subst this
  have hcs : m₁.clocks.size = j' + 1 := by rw [hi.1.own.csize, hsz]
  have hfk := hf
  obtain ⟨hch, hm'⟩ := Lock.fork_eq hf
  rw [hsz] at hch
  subst hch hm'
  have hne : (j' + 1 : Nat) ≠ 0 := by omega
  have hX : ∀ u, (upd (upd G₁ (j' + 1) (gTask false)) 0 (gSpawn (j' + 1)) u).2 =
      if u = 0 then .spawn (j' + 1) else if u = j' + 1 then .task false else (G₁ u).2 := by
    intro u; unfold upd; split
    · rfl
    · split <;> rfl
  refine ⟨rfl, rfl, (hi.1.fork (t := 0) (by rw [hg]; rfl) hfk (by rw [hg]; rfl) (fun _ => .inl rfl)
    rfl rfl rfl rfl fun hL hR => ?_).groups _, ⟨⟨?_, fun u hu1 hu => ?_, fun u hu => ?_,
      .inl ⟨j' + 1, by omega,
        by show (upd (upd G₁ (j' + 1) (gTask false)) 0 (gSpawn (j' + 1)) 0).2 = _
           rw [upd_self]; rfl, by simp [hsz],
        by rw [hgr, grp_succ], fun u => ?_⟩⟩, ?_, fun u => ?_, hi.2.blk,
      hi.2.blk1, fun v hv => ?_⟩⟩
  · -- the counter does not change: the new task has not done its increment
    apply R_main
    have hR' : R (fun u => (G₁ u).2) hL := hR
    show R _ hL; unfold R at hR' ⊢
    rw [sum_congr (X := fun u => (G₁ u).2) fun u h1 _ => by
      show (upd G₁ (j' + 1) (gTask false) u).2.count = _
      by_cases hu : u = j' + 1
      · subst hu
        have h1 : (G₁ (j' + 1)).2 = .none := hnone _ (by rw [hsz]; exact Nat.le_refl _)
        rw [upd_self, h1]; rfl
      · rw [upd_ne _ _ hu]]
    exact hR'
  · simp only [Array.getElem?_push]; rw [if_neg (by omega)]; exact h00
  · simp only [Array.size_push] at hu
    show ∃ jn, (m₁.threads.push _)[u]? = _ ∧ _
    simp only [Array.getElem?_push]
    rw [hX u]
    by_cases hu' : u = j' + 1
    · subst hu'
      refine ⟨false, by simp [hsz], fun h => absurd h (by decide), ?_⟩
      simp [hne]
    · have hu0 : u ≠ 0 := by unfold ThreadId at *; omega
      rw [if_neg (by rw [hsz]; exact hu'), if_neg hu0, if_neg hu']
      exact hrec u hu1 (by rw [hsz]; unfold ThreadId at *; omega)
  · simp only [Array.size_push] at hu
    show (upd (upd G₁ (j' + 1) (gTask false)) 0 (gSpawn (j' + 1)) u).2 = _
    rw [hX u, if_neg (by unfold ThreadId at *; omega), if_neg (by rw [hsz] at hu; unfold ThreadId at *; omega)]
    exact hnone u (by rw [hsz] at hu ⊢; unfold ThreadId at *; omega)
  · unfold joinedB
    simp only [Array.getElem?_push]
    by_cases hu : u = m₁.threads.size
    · simp [hu]
    · rw [if_neg hu]; have := hjb u; unfold joinedB at this; exact this
  · obtain ⟨hcl, hcn, -⟩ := Lock.fork_clocks (cs := m₁.clocks) (t := 0) (by
      rw [hcs]; exact Nat.succ_pos _)
    exact ioOk_iff.mpr ((ioOk_iff.mp hi.2.io).fork (t := 0)
      (by rw [← hi.1.own.csize, hcs]; exact Nat.succ_pos _)
      (by show (m₁.threads.push _).size = _; simp)
      (fun u hu => hcl u (by rw [hi.1.own.csize]; exact hu)) (by rw [← hi.1.own.csize]; exact hcn)
      fun _ he _ => he)
  · unfold upd; split
    · rfl
    · split
      · rfl
      · exact hi.2.parts u
  · exfalso
    have : joinedB m₁ v = true := by
      unfold joinedB at hv ⊢
      simp only [Array.getElem?_push] at hv
      by_cases h : v = m₁.threads.size
      · simp [h] at hv
      · rwa [if_neg h] at hv
    rw [hjb v] at this; cases this

/-- `Group.await` takes the three tasks: `main` goes to its joins. -/
theorem inv_await {G : ThreadId → Gh} {m : Mem} (hi : proto.inv (upd G 0 (gSpawn 3)) m) :
    proto.inv (upd G 0 (gJoins 0)) { m with groups := #[] } := by
  obtain ⟨h00, hrec, hnone, hph⟩ := hi.2.shape
  have hX0 : (upd G 0 (gSpawn 3) 0).2 = .spawn 3 := by rw [upd_self]; rfl
  obtain ⟨j, -, h0, hsz, -, hjb⟩ | ⟨i, -, h0, -⟩ := hph
  rotate_left
  · exfalso; change (upd G 0 (gSpawn 3) 0).2 = _ at h0; rw [hX0] at h0; cases h0
  have : j = 3 := by change (upd G 0 (gSpawn 3) 0).2 = _ at h0; rw [hX0] at h0; cases h0; rfl
  subst this
  have hl := hi.1.ghost (t := 0) (g := gJoins 0) (by rw [upd_self]; rfl) (.inl rfl)
    (by rw [upd_self]; rfl) rfl (fun _ => ⟨by rw [hsz]; decide, rfl⟩) fun hL hR => R_main hR
  rw [upd_upd] at hl
  have hX : ∀ u, u ≠ 0 → (upd G 0 (gJoins 0) u).2 = (upd G 0 (gSpawn 3) u).2 := fun u hu => by
    rw [upd_ne _ _ hu, upd_ne _ _ hu]
  refine ⟨hl.groups _, ⟨⟨h00, fun u hu1 hu => ?_, fun u hu => ?_, .inr ⟨0, by decide,
    by show (upd G 0 (gJoins 0) 0).2 = _; rw [upd_self]; rfl, hsz, rfl, fun u => ?_⟩⟩,
    hi.2.io, fun u => ?_, hi.2.blk, hi.2.blk1, fun v hv => ?_⟩⟩
  · obtain ⟨jn, hr, hj, hk⟩ := hrec u hu1 hu
    have hu0 : u ≠ 0 := by unfold ThreadId at *; omega
    exact ⟨jn, hr, by show _ → (upd G 0 _ u).2 = _; rw [hX u hu0]; exact hj,
      by show (∃ d, (upd G 0 _ u).2 = _) ∨ (upd G 0 _ u).2 = _; rw [hX u hu0]; exact hk⟩
  · show (upd G 0 _ u).2 = _
    rw [hX u (by rw [hsz] at hu; unfold ThreadId at *; omega)]; exact hnone u hu
  · have := hjb u
    constructor
    · intro h; change joinedB m u = true at h; rw [this] at h; cases h
    · intro h; exfalso; unfold ThreadId at *; omega
  · unfold upd; split
    · rfl
    · rename_i h; have := hi.2.parts u; rwa [upd_ne _ _ h] at this
  · change joinedB m v = true at hv; rw [hjb v] at hv; cases hv

/-- The join of task `i + 1` is possible: `main` spawned it and did not join it. -/
theorem join_ok {G : ThreadId → Gh} {m : Mem} {i : Nat} (hi3 : i < 3) (hi : proto.inv G m)
    (hg : (G 0).2 = .joins i) :
    i + 1 < m.threads.size ∧ ∃ m', ((Thread.join (i + 1)).run { m with current := 0 }).run =
      some (.ok ((), m')) := by
  obtain ⟨-, hrec, -, hph⟩ := hi.2.shape
  obtain ⟨j, -, h0, -⟩ | ⟨i', -, h0, hsz, -, hjb⟩ := hph
  · exfalso; change (G 0).2 = _ at h0; rw [hg] at h0; cases h0
  have : i' = i := by change (G 0).2 = _ at h0; rw [hg] at h0; cases h0; rfl
  subst this
  have hlt : i' + 1 < m.threads.size := by rw [hsz]; omega
  obtain ⟨jn, hr, -, -⟩ := hrec (i' + 1) (by omega) hlt
  have hjn : jn = false := by
    have := hjb (i' + 1)
    unfold joinedB at this; rw [hr] at this
    cases jn
    · rfl
    · simp at this; exfalso; unfold ThreadId at *; omega
  subst hjn
  exact ⟨hlt, join_run (m := { m with current := 0 }) hr rfl rfl⟩

/-- `main`'s join of task `i + 1`: it takes the task's part (none). -/
theorem inv_join {G₁ : ThreadId → Gh} {m m' : Mem} {i : Nat} (hi3 : i < 3) (hi : proto.inv G₁ m)
    (hg : G₁ 0 = gJoins i) (hfin : proto.fin (G₁ (i + 1)))
    (hj : ((Thread.join (i + 1)).run { m with current := 0 }).run = some (.ok ((), m'))) :
    m'.current = 0 ∧ proto.inv (upd G₁ 0 (gJoins (i + 1))) m' := by
  obtain ⟨h00, hrec, hnone, hph⟩ := hi.2.shape
  have hX0 : (G₁ 0).2 = .joins i := by rw [hg]; rfl
  obtain ⟨j, -, h0, -⟩ | ⟨i', -, h0, hsz, hgr, hjb⟩ := hph
  · exfalso; change (G₁ 0).2 = _ at h0; rw [hX0] at h0; cases h0
  have : i' = i := by change (G₁ 0).2 = _ at h0; rw [hX0] at h0; cases h0; rfl
  subst this
  have hu0 : (i' + 1 : Nat) ≠ 0 := by omega
  have hown : L.own G₁ m (i' + 1) = Heap.empty := by
    have : joinedB m (i' + 1) = false := by
      have := hjb (i' + 1); cases e : joinedB m (i' + 1)
      · rfl
      · rw [e] at this; have := this.mp rfl; exfalso; unfold ThreadId at *; omega
    unfold Lock.own; rw [this]
    show (G₁ (i' + 1)).1.part ∪ L.held (G₁ (i' + 1)) = _
    rw [hi.2.parts, hi.1.idle _ (by rw [show L.ph (G₁ (i' + 1)) = .gone from hfin.1]; decide),
      Heap.empty_union]
  have hl := hi.1.join (t := 0) (u := i' + 1) (g := gJoins (i' + 1)) hu0 hu0
    (by rw [hg]; rfl) hfin.1 hj (by
      show Heap.empty = (G₁ 0).1.part ∪ _
      rw [hi.2.parts, hown, Heap.empty_union]) rfl rfl fun hL hR => R_main hR
  obtain ⟨rec, hrec', hjf, hm'⟩ := join_eq hj
  have hcs : m.clocks.size = 4 := by rw [hi.1.own.csize, hsz]
  have hth : m'.threads = m.threads.set! (i' + 1) { rec with joined := true } := by rw [hm']
  have hsz' : m'.threads.size = 4 := by rw [hth, Array.size_set!, hsz]
  have hc0 : m'.clocks[0]! = VClock.merge (VClock.bump (m.clocks[0]!) 0) (m.clocks[i' + 1]!) := by
    rw [hm']; show (m.clocks.set! 0 _)[0]! = _
    rw [Proto.getElem!_set!_ite]; simp [hcs]
  have hcv : ∀ v, v ≠ 0 → m'.clocks[v]! = m.clocks[v]! := fun v hv => by
    rw [hm']; show (m.clocks.set! 0 _)[v]! = _
    rw [Proto.getElem!_set!_ite, if_neg (fun h => hv h.1)]
  have hgrow : VClock.le (m.clocks[0]!) (m'.clocks[0]!) = true := by
    rw [hc0]; exact VClock.le_trans (VClock.le_bump _ _) (VClock.le_merge_left _ _)
  have hjb' : ∀ u, joinedB m' u = (if u = i' + 1 then true else joinedB m u) := by
    intro u; unfold joinedB; rw [hth]
    simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    by_cases hu : u = i' + 1
    · subst hu; simp [hsz, show i' + 1 < 4 by omega]
    · simp [hu, Ne.symm hu]
  have hrec_r : rec = { spawner := 0, joined := false } := by
    obtain ⟨jn, hr, -, -⟩ := hrec (i' + 1) (by omega) (by rw [hsz]; omega)
    simp only at hrec'
    rw [hr] at hrec'; cases hrec'; simp only at hjf; subst hjf; rfl
  have hX : ∀ u, u ≠ 0 → (upd G₁ 0 (gJoins (i' + 1)) u).2 = (G₁ u).2 := fun u hu => by
    rw [upd_ne _ _ hu]
  refine ⟨by rw [hm'], hl, ⟨⟨?_, fun u hu1 hu => ?_, fun u hu => ?_, .inr ⟨i' + 1, by omega,
    by show (upd G₁ 0 _ 0).2 = _; rw [upd_self]; rfl, hsz', by rw [hm']; exact hgr, fun u => ?_⟩⟩,
    ?_, fun u => ?_, ?_, ?_, fun v hv => ?_⟩⟩
  · rw [hth, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, if_neg (by omega)]
    exact h00
  · rw [hsz'] at hu
    have hu0' : u ≠ 0 := by unfold ThreadId at *; omega
    obtain ⟨jn, hr, hj, hk⟩ := hrec u hu1 (by rw [hsz]; exact hu)
    dsimp only
    rw [hX u hu0']
    by_cases hui : u = i' + 1
    · subst hui
      refine ⟨true, ?_, fun _ => hfin.2, hk⟩
      rw [hth, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, if_pos rfl,
        if_pos (by rw [hsz]; omega), hrec_r]
    · refine ⟨jn, ?_, hj, hk⟩
      rw [hth, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, if_neg (Ne.symm hui)]
      exact hr
  · rw [hsz'] at hu
    show (upd G₁ 0 _ u).2 = _
    rw [hX u (by unfold ThreadId at *; omega)]; exact hnone u (by rw [hsz]; exact hu)
  · rw [hjb' u]
    by_cases hu : u = i' + 1
    · subst hu; simp
    · rw [if_neg hu, hjb u]
      constructor <;> intro h <;> unfold ThreadId at * <;> omega
  · refine ioOk_iff.mpr ((ioOk_iff.mp hi.2.io).keep (by rw [hsz', hsz]) (fun u _ => ?_)
      fun e he _ => by rw [hm'] at he; exact he)
    by_cases hu0 : u = 0
    · subst hu0; exact hgrow
    · rw [hcv u hu0]; exact VClock.le_refl _
  · unfold upd; split
    · rfl
    · exact hi.2.parts u
  · obtain ⟨blk, hb, hl', hs', ha, hk⟩ := hi.2.blk
    exact ⟨blk, by rw [hm']; exact hb, hl', hs', ha, hk⟩
  · obtain ⟨blk, hb, hl', hs'⟩ := hi.2.blk1
    exact ⟨blk, by rw [hm']; exact hb, hl', hs'⟩
  · rw [hjb' v] at hv
    have hv0 : v ≠ 0 := by
      intro e; subst e; rw [if_neg (Ne.symm hu0)] at hv; simp [joinedB] at hv
    by_cases hvi : v = i' + 1
    · subst hvi
      refine ⟨by rw [upd_ne _ _ hv0]; exact hfin.1, ?_⟩
      rw [hcv _ hv0, hc0]; exact VClock.le_merge_right _ _
    · rw [if_neg hvi] at hv
      obtain ⟨h1, h2⟩ := hi.2.jle v hv
      refine ⟨by rw [upd_ne _ _ hv0]; exact h1, ?_⟩
      rw [hcv _ hv0]; exact VClock.le_trans h2 hgrow

/-! ## `main`'s spawns and joins -/

/-- The spawn loop's invariant: `main` did `local10` spawns. -/
def spawnInv (s : groupCounterLocals) (G : ThreadId → Gh) (m : Mem) (_ : Nat) : Prop :=
  m.current = 0 ∧ s.local10.toNat ≤ 3 ∧ proto.inv (upd G 0 (gSpawn s.local10.toNat)) m

/-- The spawn loop ends after 3 spawns. -/
def spawnPost (r : groupCounterExit × groupCounterLocals) (G : ThreadId → Gh) (m : Mem) (_ : Nat) :
    Prop :=
  r.1 = .br12 ∧ m.current = 0 ∧ proto.inv (upd G 0 (gSpawn 3)) m

theorem loop13_body (io : Io) (s : groupCounterLocals) (G : ThreadId → Gh) (m : Mem) (d : Nat)
    (h : spawnInv s G m d) :
    proto.WP 0 ((groupCounter.loop13 io cPtr gPtr).run s) (fun r G' m' d' =>
      if groupCounter.again13 r.1 then spawnInv r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : groupCounterLocals) => 0) s)
      else spawnPost r G' m' d') G m d := by
  obtain ⟨hc, hle, hi⟩ := h
  unfold groupCounter.loop13
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · rename_i hlt
    have hlt' : s.local10.toNat < 3 := by simpa [lt, BitVec.ult] using hlt
    simp only [StateT.run_bind, bind_assoc, pure_bind]
    refine WP.bind (WP.groupAsyncC fun k hk => ⟨gSpawn s.local10.toNat, hi, fun G₁ m₁ hg₁ hi₁ =>
      ⟨gTask false, ⟨rfl, rfl⟩, fun child m' hf => ?_⟩⟩)
    obtain ⟨rfl, hc', hi'⟩ := inv_spawn hlt' hi₁ hg₁ hf
    simp only [StateT.run_pure, pure_bind, StateT.run_bind]
    refine WP.bind (WP.callRC (fun e he =>
      (add_one_noErr (a := s.local10) (by have := s.local10.isLt; omega) e he).elim) fun i23 hadd => ?_)
    have h23 := add_one_ok (a := s.local10) hadd (by have := s.local10.isLt; omega)
    simp only [StateT.run_modify, StateT.run_pure, pure_bind]
    refine WP.pure' ?_
    simp only [groupCounter.again13, ↓reduceIte]
    refine ⟨⟨hc', by simp only; omega, by simp only; rw [h23]; exact hi'⟩, .inl (by omega)⟩
  · rename_i hge
    have hge' : ¬ s.local10.toNat < 3 := by simpa [lt, BitVec.ult] using hge
    have heq : s.local10.toNat = 3 := by omega
    simp only [StateT.run_pure, pure_bind]
    refine WP.pure' ?_
    simp only [groupCounter.again13, Bool.false_eq_true, ↓reduceIte]
    exact ⟨rfl, hc, heq ▸ hi⟩

/-- `main`'s join of task `i + 1`, at `joins i`. -/
theorem wp_join {σ : Type} {s : σ} {i : Nat} (u : ThreadId) (hu : u = i + 1) (hi3 : i < 3)
    {G : ThreadId → Gh} {m : Mem} {n : Nat} (hi : proto.inv (upd G 0 (gJoins i)) m)
    {Q : Unit × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m', m'.current = 0 → proto.inv (upd G₁ 0 (gJoins (i + 1))) m' →
      Q ((), s) G₁ m' k) :
    proto.WP 0 ((joinC u : CM Tgt σ Unit).run s) Q G m n := by
  subst hu
  refine WP.joinC fun k hk => ⟨gJoins i, hi, fun G₁ m₁ hg₁ hi₁ => ?_⟩
  have hX : (G₁ 0).2 = .joins i := by rw [hg₁]; rfl
  obtain ⟨hlt, hex⟩ := join_ok hi3 hi₁ hX
  refine ⟨fun _ => ⟨Nat.succ_pos _, hlt, ⟨rfl, i, rfl⟩, by
    obtain ⟨m', hj⟩ := hex
    exact Proto.join_valid hj⟩, fun hfin => ⟨fun _ => hex, fun m' hj => ?_⟩⟩
  obtain ⟨hc', hi'⟩ := inv_join hi3 hi₁ hg₁ hfin hj
  exact h k hk G₁ m' hc' hi'

/-- After 3 spawns the group records the three tasks. -/
theorem groups_spawn3 {G : ThreadId → Gh} {m : Mem} (hi : proto.inv (upd G 0 (gSpawn 3)) m) :
    m.groups = grp 3 := by
  obtain ⟨-, -, -, ⟨j, -, h0, -, hgr, -⟩ | ⟨i, -, h0, -⟩⟩ := hi.2.shape
  · change (upd G 0 (gSpawn 3) 0).2 = _ at h0; rw [upd_self] at h0; cases h0; exact hgr
  · change (upd G 0 (gSpawn 3) 0).2 = _ at h0; rw [upd_self] at h0; cases h0

/-- After the three joins: `main` owns the counter, which holds 3; every thread is joined, and
the tasks' read shares of `io` are back: `main` owns `io` alone (`ReadShared.reclaim`). -/
theorem inv_final {G : ThreadId → Gh} {m : Mem} (hi : proto.inv (upd G 0 (gJoins 3)) m) :
    ∃ own : ThreadId → Heap, ∃ rest, Owned own m ∧
      (pts (cPtr.add 20) 4 (BitVec.ofNat 32 3) ∗ fun h => h = rest) (own 0) ∧
      m.threads.size = 4 ∧ joinedAll 0 m ∧ BlkOk m ∧ Blk1 m ∧
      RegionOwned IoR m (m.clocks[0]!) := by
  obtain ⟨h00, hrec, hnone, hph⟩ := hi.2.shape
  have hX0 : (upd G 0 (gJoins 3) 0).2 = .joins 3 := by rw [upd_self]; rfl
  obtain ⟨j, -, h0, -⟩ | ⟨i, -, h0, hsz, -, hjb⟩ := hph
  · exfalso; change (upd G 0 (gJoins 3) 0).2 = _ at h0; rw [hX0] at h0; cases h0
  have : i = 3 := by change (upd G 0 (gJoins 3) 0).2 = _ at h0; rw [hX0] at h0; cases h0; rfl
  subst this
  have hfinu : ∀ u, 1 ≤ u → u ≤ 3 → (upd G 0 (gJoins 3) u).2 = .fin := by
    intro u h1 h3
    obtain ⟨jn, hr, hj, -⟩ := hrec u h1 (by rw [hsz]; unfold ThreadId at *; omega)
    have hjt := (hjb u).mpr ⟨h1, h3⟩
    unfold joinedB at hjt; rw [hr] at hjt
    have : jn = true := by
      cases jn
      · simp at hjt
      · rfl
    exact hj this
  have hF : L.Free (upd G 0 (gJoins 3)) := by
    intro u hu
    by_cases h0 : u = 0
    · subst h0; rw [upd_self] at hu; cases hu
    · by_cases h3 : u ≤ 3
      · have := (hi.2.jle u ((hjb u).mpr ⟨Nat.pos_of_ne_zero h0, h3⟩)).1
        rw [show L.ph (upd G 0 (gJoins 3) u) = (upd G 0 (gJoins 3) u).1.ph from rfl, this] at hu
        cases hu
      · have := (hi.1.live u (by rw [hu]; decide)).1
        rw [hsz] at this; unfold ThreadId at *; omega
  have hall : ∀ u < m.threads.size, VClock.le (m.clocks[u]!) (m.clocks[0]!) = true := fun u hu => by
    by_cases h0 : u = 0
    · subst h0; exact VClock.le_refl _
    · rw [hsz] at hu
      exact (hi.2.jle u ((hjb u).mpr ⟨Nat.pos_of_ne_zero h0, by unfold ThreadId at *; omega⟩)).2
  obtain ⟨hL, hR, hdLW, hd, ho⟩ :=
    hi.1.take (t := 0) (by rw [hsz]; decide) hF (by rw [upd_self]; decide) hall
  have hR3 : pts (cPtr.add 20) 4 (BitVec.ofNat 32 3) hL := by
    have : R (fun u => (upd G 0 (gJoins 3) u).2) hL := hR
    have h3 : sum (fun u => (upd G 0 (gJoins 3) u).2) = 3 := by
      show (upd G 0 (gJoins 3) 1).2.count + (upd G 0 (gJoins 3) 2).2.count +
        (upd G 0 (gJoins 3) 3).2.count = 3
      rw [hfinu 1 (by decide) (by decide), hfinu 2 (by decide) (by decide),
        hfinu 3 (by decide) (by decide)]; rfl
    unfold R at this; rw [h3] at this; exact this
  let own := L.own (upd G 0 (gJoins 3)) m
  have hd' : Heap.Disjoint hL (own 0 ∪ L.wordH m) :=
    Heap.disjoint_union_right.mpr ⟨(Heap.disjoint_union_right.mp hd).1.symm, hdLW⟩
  have heq : own 0 ∪ (hL ∪ L.wordH m) = hL ∪ (own 0 ∪ L.wordH m) :=
    Heap.union_left_comm (Heap.disjoint_union_right.mp hd).1
  refine ⟨_, own 0 ∪ L.wordH m, ho, by rw [upd_self, heq]; exact ⟨hL, _, hd', rfl, hR3, rfl⟩, hsz,
    fun r hr hsp => ?_, hi.2.blk, hi.2.blk1,
    (ioOk_iff.mp hi.2.io).reclaim (by rw [hsz]; decide) hall⟩
  obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.mp hr
  by_cases hk0 : k = 0
  · subst hk0
    rw [Array.getElem?_eq_getElem hk] at h00
    rw [Option.some.inj h00]
  · obtain ⟨jn, hr', -, -⟩ := hrec k (Nat.pos_of_ne_zero hk0) hk
    have hjt := (hjb k).mpr ⟨Nat.pos_of_ne_zero hk0, by rw [hsz] at hk; unfold ThreadId at *; omega⟩
    unfold joinedB at hjt
    rw [Array.getElem?_eq_getElem hk] at hr' hjt
    simp only [Option.map_some, Option.getD_some, Bool.and_eq_true, bne_iff_ne, ne_eq] at hjt
    exact hjt.2

/-- `Group.await`'s take of the group's tasks: 1, 2, 3; the group is empty after it. -/
theorem take_run {m : Mem} (hg : m.groups = grp 3) :
    ((Thread.groupTake gPtr).run m).run = some (.ok (#[1, 2, 3], { m with groups := #[] })) := by
  unfold Thread.groupTake
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hg]
  rw [show (grp 3).filter (·.1 != gPtr) = #[] by decide +kernel,
    show ((grp 3).filter (·.1 == gPtr)).map (·.2) = #[1, 2, 3] by decide +kernel]
  rfl

theorem main_spec (σ : Placement) (io : Io) (d : Nat) :
    proto.WP 0 (groupCounter io) QM G0 { mem0 σ with current := 0 } d := by
  unfold groupCounter
  -- the `Counter`: block 0
  refine WP.bind (WP.liftMem_owned (own := fun _ => Heap.empty) (TTriple.alloc .stack 24 8 (by decide))
    (Owned.start rfl rfl) rfl (by simp [mem0, Mem.ofGlobals]) rfl fun s1 m₁ h₁ hr₁ ho₁ hq₁ hs₁ hm₁ hd₁ => ?_)
  obtain ⟨rfl, hm₁e⟩ := alloc_ok hr₁
  obtain ⟨A, hA⟩ := hq₁
  obtain ⟨⟨-, hA8⟩, hb₁⟩ := sep_lift.mp hA
  have hc₁ : m₁.current = 0 := hs₁.current
  rw [show (⟨some ({ mem0 σ with current := 0 } : Mem).blocks.size, 0⟩ : Ptr) = cPtr from rfl] at hb₁ ⊢
  -- the `Io.Group`: block 1
  have ho₁' : Owned (upd (fun _ => Heap.empty) 0 h₁) m₁ := ho₁
  refine WP.bind (WP.liftMem_owned (alloc_next (R := bytesAt cPtr A 24 .stack
    (Array.replicate 24 .undef)) 16 8 (by decide)) ho₁' hc₁ (by rw [hs₁.threads]; simp [mem0, Mem.ofGlobals])
    (by rw [upd_self]; exact hb₁) fun s8 m₂ h₂ hr₂ ho₂ hq₂ hs₂ hm₂ hd₂ => ?_)
  rw [upd_upd] at ho₂
  obtain ⟨rfl, -⟩ := alloc_ok hr₂
  rw [show (⟨some m₁.blocks.size, 0⟩ : Ptr) = gPtr by rw [hm₁e]; rfl]
  obtain ⟨A', ⟨-, hA8'⟩, hq₂'⟩ := sep_ex_lift hq₂
  obtain ⟨h0, hG, d0G, rfl, hb0, hbG⟩ := hq₂'
  rw [show (⟨some m₁.blocks.size, 0⟩ : Ptr) = gPtr by rw [hm₁e]; rfl] at hbG
  have hc₂ : m₂.current = 0 := hs₂.current.trans hc₁
  -- the `Counter`'s three parts
  obtain ⟨hI, hR₁, dI, rfl, hI₁, hR₁'⟩ := bytesAt_split hb0 (k := 16) (by simp)
  obtain ⟨hW, hC, dWC, rfl, hW₁, hC₁⟩ := bytesAt_split hR₁' (k := 4) (by simp)
  have hsI : ((Array.replicate 24 Byte.undef).extract 0 16).size = 16 := by simp
  have hsW : (((Array.replicate 24 Byte.undef).extract 16).extract 0 4).size = 4 := by simp
  have hsC : (((Array.replicate 24 Byte.undef).extract 16).extract 4).size = 4 := by simp
  have hsG : (Array.replicate 16 Byte.undef).size = 16 := by simp
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  -- `io`, the mutex, the counter, the `Io.Group`
  have F₂ : ((bytesAt cPtr A 24 .stack ((Array.replicate 24 Byte.undef).extract 0 16) ∗
      (bytesAt (cPtr.add 16) A 24 .stack (((Array.replicate 24 Byte.undef).extract 16).extract 0 4) ∗
        bytesAt ((cPtr.add 16).add 4) A 24 .stack
          (((Array.replicate 24 Byte.undef).extract 16).extract 4))) ∗
      bytesAt gPtr A' 16 .stack (Array.replicate 16 .undef))
      ((hI ∪ (hW ∪ hC)) ∪ hG) := ⟨_, hG, d0G, rfl, ⟨hI, hW ∪ hC, dI, rfl, hI₁, hW, hC, dWC, rfl, hW₁, hC₁⟩, hbG⟩
  refine WP.bind (WP.liftM_owned ((TTriple.storeAt (p := cPtr) (A := A) (S := 24) (K := .stack)
    (k := 0) (a := 8) io rfl (by decide) (by rw [hsI]; decide) (by simp [cPtr]; omega)
    (by decide)).frame.frame) ho₂ hc₂ (by rw [hs₂.threads, hs₁.threads]; simp [mem0, Mem.ofGlobals])
    (by rw [upd_self]; exact F₂) fun _ m₃ h₃ _ ho₃ F₃ hs₃ _ _ => ?_)
  rw [upd_upd] at ho₃
  refine WP.bind (WP.liftM_owned ((TTriple.storeAt' (p := cPtr.add 16) (A := A) (S := 24)
    (K := .stack) (k := 0) (a := 4) mutex0 (by rw [enc_mutex, enc_u32]; rfl) rfl (by decide)
    (by rw [hsW]; decide) (by simp [cPtr, Ptr.add]; omega) (by decide)).frame.frameL.frame) ho₃
    (hs₃.current.trans hc₂) (by rw [hs₃.threads, hs₂.threads, hs₁.threads]; simp [mem0, Mem.ofGlobals])
    (by rw [upd_self]; exact F₃) fun _ m₄ h₄ _ ho₄ F₄ hs₄ _ _ => ?_)
  rw [upd_upd] at ho₄
  refine WP.bind (WP.liftM_owned ((TTriple.storeAt (p := (cPtr.add 16).add 4) (A := A) (S := 24)
    (K := .stack) (k := 0) (a := 4) (0 : BitVec 32) rfl (by decide) (by rw [hsC]; decide)
    (by simp [cPtr, Ptr.add]; omega) (by decide)).frameL.frameL.frame) ho₄
    (hs₄.current.trans (hs₃.current.trans hc₂))
    (by rw [hs₄.threads, hs₃.threads, hs₂.threads, hs₁.threads]; simp [mem0, Mem.ofGlobals]) (by rw [upd_self]; exact F₄)
    fun _ m₅ h₅ _ ho₅ F₅ hs₅ _ _ => ?_)
  rw [upd_upd] at ho₅
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  refine WP.bind (WP.liftM_owned ((TTriple.storeAt' (p := gPtr) (A := A') (S := 16) (K := .stack)
    (k := 0) (a := 8) group0 enc_group rfl (by decide) (by rw [hsG]; decide)
    (by simp [gPtr]; omega) (by decide)).frameL) ho₅
    (hs₅.current.trans (hs₄.current.trans (hs₃.current.trans hc₂)))
    (by rw [hs₅.threads, hs₄.threads, hs₃.threads, hs₂.threads, hs₁.threads]; simp [mem0, Mem.ofGlobals])
    (by rw [upd_self]; exact F₅) fun _ m₆ h₆ _ ho₆ F₆ hs₆ _ _ => ?_)
  rw [upd_upd] at ho₆
  have hc₆ : m₆.current = 0 :=
    hs₆.current.trans (hs₅.current.trans (hs₄.current.trans (hs₃.current.trans hc₂)))
  have hth₆ : m₆.threads = #[{ spawner := 0, joined := true }] := by
    rw [hs₆.threads, hs₅.threads, hs₄.threads, hs₃.threads, hs₂.threads, hs₁.threads]; rfl
  have hat₆ : m₆.atomics = #[] := by
    rw [hs₆.atomics, hs₅.atomics, hs₄.atomics, hs₃.atomics, hs₂.atomics, hs₁.atomics]; rfl
  have hq₆ : m₆.waiters = #[] := by
    rw [hs₆.waiters, hs₅.waiters, hs₄.waiters, hs₃.waiters, hs₂.waiters, hs₁.waiters]; rfl
  have hgr₆ : m₆.groups = #[] := by
    rw [hs₆.groups, hs₅.groups, hs₄.groups, hs₃.groups, hs₂.groups, hs₁.groups]; rfl
  rw [writeBytes_all (by rw [hsI, enc_io]), writeBytes_all (by rw [hsW, enc_mutex, enc_u32]),
    writeBytes_all (by rw [hsC, enc_u32]), writeBytes_all (by rw [hsG, enc_group])] at F₆
  obtain ⟨hc, hg, dcg, rfl, hp, hgp⟩ := F₆
  have hi₀ := inv_start ho₆ dcg hp hgp hA8 hth₆ hat₆ hq₆ hgr₆
  -- the spawns
  simp only [StateT.run_modify, pure_bind]
  refine WP.bind (WP.mono ?_ (WP.loop _ _ spawnInv (fun _ => 0) spawnPost (loop13_body io)
    { c := cPtr, g := gPtr, local10 := 0 } G0 m₆ d ⟨hc₆, by decide, by simpa using hi₀⟩))
  rintro ⟨e, s'⟩ G₁ m₇ d₁ ⟨rfl, hc₇, hi₇⟩
  -- `Group.await`: the take of the tasks, then the joins
  simp only [StateT.run_bind]
  unfold groupAwaitC
  simp only [StateT.run_bind]
  have hrun := take_run (groups_spawn3 hi₇)
  refine WP.bind (WP.bind (WP.callMC (fun e he => by rw [hrun] at he; cases he) fun tids m₈ hr => ?_))
  rw [hrun] at hr
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  refine ⟨rfl, ?_⟩
  -- `main` is not an `Io` task: no cancelation
  refine WP.bind (WP.callMC (fun e he => by rw [isTask_run] at he; cases he) fun b m₈ hr => ?_)
  rw [isTask_run] at hr
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hr
  obtain ⟨hb, rfl⟩ := hr
  obtain rfl : b = false := by rw [← hb]; simp [hc₇]
  refine ⟨rfl, ?_⟩
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hiA := inv_await hi₇
  rw [← Array.forIn_toList]
  simp only [Array.toList, List.forIn_cons, List.forIn_nil, StateT.run_bind, bind_assoc]
  refine WP.bind (wp_join (i := 0) 1 rfl (by decide) hiA fun k₁ _ G₂ m₉ hc₉ hi₉ => ?_)
  simp only [StateT.run_pure, pure_bind, StateT.run_bind, bind_assoc]
  refine WP.bind (wp_join (i := 1) 2 rfl (by decide) hi₉ fun k₂ _ G₃ m₁₀ hc₁₀ hi₁₀ => ?_)
  simp only [StateT.run_pure, pure_bind, StateT.run_bind, bind_assoc]
  refine WP.bind (wp_join (i := 2) 3 rfl (by decide) hi₁₀ fun k₃ _ G₄ m₁₁ hc₁₁ hi₁₁ => ?_)
  simp only [StateT.run_pure, pure_bind]
  refine WP.pure' ?_
  simp only [StateT.run_bind]
  -- the counter holds 3
  obtain ⟨own, rest, ho, hp, hsz, hja, hbk, hb1, hio⟩ := inv_final hi₁₁
  refine WP.bind (WP.liftM_owned (TTriple.load (p := cPtr.add 20) (a := 4)
    (v := BitVec.ofNat 32 3) (by decide)).frame ho hc₁₁ (by rw [hsz]; decide) hp
    fun a m₁₂ hQ hr ho' hq hs₁₂ _ _ => ?_)
  obtain ⟨h₁, h₂, -, -, hq₁, -⟩ := hq
  obtain ⟨rfl, -⟩ := sep_lift.mp hq₁
  obtain ⟨b, blk, o, -, -, -, hm₁₂⟩ := load_ok hr
  simp only [StateT.run_pure]
  refine WP.pure' ?_
  -- the frees
  obtain ⟨blk₀, hblk₀, hl₀, -⟩ := hbk
  obtain ⟨blk₁, hblk₁, hl₁, -⟩ := hb1
  have hb₁₂ : m₁₂.blocks = m₁₁.blocks := by rw [hm₁₂]; rfl
  refine WP.bind (WP.liftMem (fun e he => (free_noErr (by rw [hb₁₂]; exact hblk₀) hl₀ e he).elim)
    fun _ m₁₃ hfr => ?_)
  obtain ⟨b', blk', hb', hblk', rfl⟩ := free_ok hfr
  cases hb'
  refine ⟨rfl, ?_⟩
  refine WP.bind (WP.liftMem (fun e he => (free_noErr (b := 1) (by
    simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]; rw [hb₁₂]; simpa using hblk₁)
    hl₁ e he).elim) fun _ m₁₄ hfr' => ?_)
  obtain ⟨b'', -, hb'', -, rfl⟩ := free_ok hfr'
  cases hb''
  refine ⟨rfl, WP.pure' ⟨rfl, fun r hr hsp => ?_, ⟨{ blk' with live := false }, ?_, rfl⟩, ?_⟩⟩
  · have hth : m₁₂.threads = m₁₁.threads := by rw [hm₁₂]; rfl
    exact hja r (by simpa [hth] using hr) hsp
  · simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (by decide : (1 : Nat) ≠ 0)]
    exact Array.getElem?_setIfInBounds_self_of_lt (Array.getElem?_eq_some_iff.mp hblk').1
  · show RegionOwned IoR m₁₂ (m₁₂.clocks[0]!)
    rw [hm₁₂]
    exact hio.recordAt hc₁₁ (by rw [ho.csize, hsz]; decide) b o 4 .read

/-! ## The results -/

/-- **`groupCounter` gives 3 under every schedule** (every oracle `o`, every `fuel`). -/
theorem groupCounter_spec {σ : Placement} {fuel : Nat} {o : Nat → Nat} {v : Except ErrName (BitVec 32)} {m : Mem}
    (io : Io) (h : (Sched.run dispatch fuel o (groupCounter io) (mem0 σ)).run = some (.ok (v, m))) :
    v = .ok 3 := by
  obtain ⟨_, _, hv, -⟩ := proto.run_sound dispatch G0 dispatch_spec
    (fun _ _ _ _ _ hq => hq.2.1) rfl (main_spec σ io) h
  exact hv

/-- **No run of `groupCounter` gives an error**: no data race on the counter, no deadlock at the
futex or at `Group.await`, no panic, under every schedule. -/
theorem groupCounter_safe {σ : Placement} {fuel : Nat} {o : Nat → Nat} {e : Error} (io : Io) :
    (Sched.run dispatch fuel o (groupCounter io) (mem0 σ)).run ≠ some (.error e) :=
  proto.run_safe dispatch G0 rfl dispatch_spec (fun _ _ _ _ hq => hq.2.1) rfl (main_spec σ io)

/-- One schedule completes: under the oracle that always picks option 0, the `Io.Group` counter returns 3 within
fuel 1000, from `mem0` with the translation's spawn policy. The kernel computes the run, with
each loop cut after 10 iterations (`unroll_sched`, `ZigLean/Conc/Unroll.lean`). -/
theorem groupCounter_completes :
    ∃ σ, Witness.okVal (Sched.run dispatch 1000 (fun _ => 0) (groupCounter ⟨⟩) (mem0 σ)) = some 3 :=
  ⟨.fresh, by unroll_sched 10⟩

/-- **Join before free, under every schedule.** Three tasks read-share `io` (bytes 0..16 of block
0, `ZigLean/Conc/Share.lean`'s `ReadShared`); `main` frees the block only with every task joined
and every access to `io` happened before it. The run ends right after the frees, which change no
thread, clock or footprint entry, so the final memory gives these facts at the free. -/
theorem groupCounter_reclaim {σ : Placement} {fuel : Nat} {o : Nat → Nat} {v : Except ErrName (BitVec 32)}
    {m : Mem} (io : Io)
    (h : (Sched.run dispatch fuel o (groupCounter io) (mem0 σ)).run = some (.ok (v, m))) :
    joinedAll 0 m ∧ Reclaimed m := by
  obtain ⟨_, _, -, hq⟩ := proto.run_sound dispatch G0 dispatch_spec
    (fun _ _ _ _ _ hq => hq.2.1) rfl (main_spec σ io) h
  exact hq

nonvacuity_witness take_run := ⟨{ groups := grp 3 }, rfl, trivial⟩

end Iogroup.GroupCounter
