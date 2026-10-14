import Proofs.Iogroup.Lock
import ZigLean.Sep.Full.ThreadFacts
import ZigLean.Sep.Full.Local
import ZigLean.Sep.Full.Word
import ZigLean.Conc.Share
import ZigLean.Conc.SpawnLemmas
import ZigLean.Conc.Unroll
import ZigLean.Witness

/-!
# `groupCounter` over all schedules

`groupCounter` runs three tasks in an `Io.Group` (`Group.async`); each task adds 1 to a counter
under an `Io.Mutex` (translated from Zig 0.16.0's std code). `Group.async` is an oracle choice
(`ZigLean/Conc/Spawn.lean`): the task gets its own thread, runs in `main` at once (eager), or is
deferred until `Group.await` (a gated thread). After `Group.await` the result is 3 under every
schedule and every choice (`groupCounter_spec`), and no schedule gives an error
(`groupCounter_safe`).

The proof is in the full-state concurrent separation logic (`docs/sep-threads.md`): the threads'
parts are full-state resources (`FOwned`), a thread's `MemM` step is a thread triple
(`FTTriple`), and the mutex is a lock that owns a resource (`ZigLean/Sep/Full/Lock.lean`). The
client uses only the mutex contract (`MutexImpl`, `ZigLean/Sep/Full/Mutex.lean`): `lock` and
`unlock` of this program's `Io.Mutex` are `ioMutex` (`Proofs/Iogroup/Lock.lean`). The mutex
(bytes 16..20 of the `Counter`, block 0) owns the counter (bytes 20..24, `R`), whose value is the
number of increments done. This file proves the rest:

- **Ghost values** (`Gh = FLG × Ph`): the lock's part, and where the thread is: `main` after `j`
  asyncs of which `k` made a task (`spawn j k`; the other `j - k` it ran itself) and at its joins
  (`joins i k`), a task before and after its increment. `main`'s eager increments count with the
  tasks' (`sum`).
- **Resources**: `main`'s part (`MainPart`) holds both blocks' extents (`bext`, which pin the
  blocks in every memory: `FOwned.blkOf`) and the `Io.Group`'s bytes; a task's part is empty. The
  bytes of `io` (0..16 of the `Counter`) are the protocol's own rest (`IoRest`): the tasks only
  read them (`FLock.Inv.recordX`), and they are read-shared (`ReadShared`).
- **The rest of the invariant** (`U`): the threads and the group's tasks (`Shape`), the read
  shares of `io`, the parts, `io` in the rest, and each joined task has ended and happened before
  `main` (`Jle`).
- **`main`**: before its first spawn it gives `io` to the rest (`FOwned.give`) and the mutex and
  the counter to the lock (`FLock.Inv.make`). `Group.async` is a spawn (`FLock.Inv.fork`), a
  deferred spawn, or `main`'s own `add`; `Group.await` joins the `k` tasks (`FLock.Inv.join`);
  then `main` takes the counter back (`FLock.Inv.take`) and reads 3.
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Full Zig.Full.FAssn Iogroup

namespace Iogroup.GroupCounter

-- Unification must not unfold `WP` into the program (as in `Proofs/Sync/RwLock.lean`).
attribute [local irreducible] Proto.WP

/-- Where a thread is, outside the lock's code. -/
inductive Ph where
  | none
  /-- `main` after `j` asyncs, `k` of which made a task (threads `1 … k`). -/
  | spawn (j k : Nat)
  /-- `main` after `Group.await` took its `k` tasks and `i` joins. -/
  | joins (i k : Nat)
  /-- A task; `done`: it did its increment. -/
  | task (done : Bool)
  /-- A task that has ended. -/
  | fin

/-- The increments of a thread: one for a task that did its increment; for `main`, the asyncs
it ran itself. -/
def Ph.count : Ph → Nat
  | .spawn j k => j - k
  | .joins _ k => 3 - k
  | .task true | .fin => 1
  | _ => 0

abbrev Gh := FLG × Ph

/-- The `Counter` (block 0). -/
def cPtr : Ptr := ⟨some 0, 0⟩

/-- The `Io.Group` (block 1). -/
def gPtr : Ptr := ⟨some 1, 0⟩

/-- The increments of `main` and of the tasks. -/
def sum (X : ThreadId → Ph) : Nat := (X 0).count + (X 1).count + (X 2).count + (X 3).count

/-- The sum reads only the threads 0 … 3. -/
theorem sum_congr {X X' : ThreadId → Ph} (h : ∀ u, u ≤ 3 → (X' u).count = (X u).count) :
    sum X' = sum X := by
  unfold sum
  rw [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide)]

/-- The counter holds the increments of the tasks. -/
def R (X : ThreadId → Ph) : FAssn := up (pts (cPtr.add 20) 4 (BitVec.ofNat 32 (sum X)))

/-- The `Io.Mutex`: bytes 16..20 of the `Counter`. It owns the counter. -/
abbrev L : FLock Gh := FLock.prod 0 16 R

/-- The accesses to the bytes of `io` (0..16 of the `Counter`; a zero-length access touches
none). -/
def IoR (e : FootprintEntry) : Prop := e.block = 0 ∧ 0 < e.len ∧ e.off < 16

theorem covers_io : Covers IoR 0 0 16 := fun _ hb hl _ h2 => ⟨hb, hl, by omega⟩

/-- The tasks of the group after `j` tasks. -/
def grp (j : Nat) : Array (Ptr × ThreadId) := (Array.range j).map fun i => (gPtr, i + 1)

/-- The threads: `main` and its tasks (spawned or deferred, `gated`), which it spawned; a joined
task has ended. Before the `await` the group records the tasks; after it, `main` joins them in
order. -/
def Shape (X : ThreadId → Ph) (m : Mem) : Prop :=
  m.threads[0]? = some { spawner := 0, joined := true } ∧
  (∀ u, 1 ≤ u → u < m.threads.size → ∃ jn gt,
    m.threads[u]? = some { spawner := 0, joined := jn, gated := gt } ∧
    (jn = true → X u = .fin) ∧ ((∃ d, X u = .task d) ∨ X u = .fin)) ∧
  (∀ u, m.threads.size ≤ u → X u = .none) ∧
  ((∃ j k, k ≤ j ∧ j ≤ 3 ∧ X 0 = .spawn j k ∧ m.threads.size = k + 1 ∧ m.groups = grp k ∧
      ∀ u, joinedB m u = false) ∨
   (∃ i k, i ≤ k ∧ k ≤ 3 ∧ X 0 = .joins i k ∧ m.threads.size = k + 1 ∧ m.groups = #[] ∧
      ∀ u, joinedB m u = true ↔ 1 ≤ u ∧ u ≤ i))

/-- The initial `Io.Group`. -/
def group0 : Io_Group := { token := { raw := none }, state := 0 }

theorem enc_group : (Enc.encode group0).size = 16 := by decide +kernel

/-- `main`'s part: the extents of the `Counter` and of the `Io.Group`, and the group's bytes. -/
def MainPart : FAssn :=
  bext 0 24 .stack ⋆ (bext 1 16 .stack ⋆ FAssn.ex fun A' : Nat =>
    up (bytesAt gPtr A' 16 .stack (Enc.encode group0)))

/-- The protocol's own rest: the bytes of `io`, bytes 0..16 of the `Counter`. -/
def IoRest (rX : Res) : Prop :=
  ∃ A bs, A % 8 = 0 ∧ bs.size = 16 ∧ Enc.decode bs = pure (⟨⟩ : Io) ∧
    up (bytesAt cPtr A 24 .stack bs) rX

/-- A joined task has ended, and its clock happened before `main`'s. -/
def Jle (G : ThreadId → Gh) (m : Mem) : Prop :=
  ∀ v, joinedB m v = true → (G v).1.ph = .gone ∧ VClock.le (m.clocks[v]!) (m.clocks[0]!) = true

/-- The rest of the invariant (module doc). -/
structure U (G : ThreadId → Gh) (rX : Res) (m : Mem) : Prop where
  shape : Shape (fun u => (G u).2) m
  io : ReadShared IoR m
  parts : ∀ u, u ≠ 0 → (G u).1.part = rnil
  main : MainPart (G 0).1.part
  rest : IoRest rX
  jle : Jle G m

/-- The protocol, in strict mode. -/
def proto : Proto Tgt Gh where
  inv G m := ∃ rX, L.Inv G rX m ∧ U G rX m
  init tgt g := match tgt with
    | .add p => p = cPtr ∧ g = (⟨.out, rnil, rnil⟩, .task false)
  fin g := g.1.ph = .gone ∧ g.2 = .fin
  strict := true
  spawnFails := true
  joins g := g.1.ph = .out ∧ ((∃ i k, g.2 = .joins i k) ∨ g.2 = .task false)

/-- Join before free: block 0 (the `Counter`, with the read-shared `io`) is freed, and every
access to `io` happened before `main` (`ZigLean/Conc/Share.lean`'s `RegionOwned`). -/
def Reclaimed (m : Mem) : Prop :=
  (∃ blk, m.blocks[0]? = some blk ∧ blk.live = false) ∧ RegionOwned IoR m (m.clocks[0]!)

/-- `main`'s post: the result, all tasks joined, and `io` reclaimed. -/
def QM : Except ErrName (BitVec 32) → (ThreadId → Gh) → Mem → Nat → Prop :=
  fun v _ m _ => v = .ok 3 ∧ joinedAll 0 m ∧ Reclaimed m

/-! ## The protocol has the lock -/

theorem stable (G : ThreadId → Gh) (rX : Res) (m m' : Mem) (t : ThreadId) (p : LPh) (h : Res)
    (hg : L.ph (G t) ≠ .gone) (hu : U G rX m) (hs : L.Step t m m')
    (_ : L.ph (G t) = .holds → p ≠ .holds → L.Before m' (m.clocks[t]!)) :
    U (upd G t (L.set (G t) p h)) rX m' := by
  obtain ⟨hsh, hio, hpart, hmain, hrest, hjle⟩ := hu
  have hjb : joinedB m' = joinedB m := LockWord.joinedB_congr hs.threads
  have hX : ∀ u, (upd G t (L.set (G t) p h) u).1.part = (G u).1.part := fun u => by
    unfold upd; split
    · rename_i e; subst e; rfl
    · rfl
  refine ⟨?_, fun e he hr => ?_, fun u hu => by rw [hX]; exact hpart u hu,
    by rw [hX]; exact hmain, hrest, fun v hv => ?_⟩
  · rw [FLock.snd_set]; unfold Shape at hsh ⊢; rw [hs.threads, hs.groups, hjb]; exact hsh
  · rcases hs.fp e he with h' | ⟨-, ho', -⟩
    · rcases hio e h' hr with ⟨hk, h''⟩ | h''
      · exact .inl ⟨hk, hs.someLe h''⟩
      · exact .inr (hs.allLe h'')
    · exact absurd hr.2.2 (by rw [ho']; decide)
  · rw [hjb] at hv
    obtain ⟨hgv, hle⟩ := hjle v hv
    have hvt : v ≠ t := fun e => by rw [e] at hgv; exact hg hgv
    refine ⟨by rw [upd_ne _ _ hvt]; exact hgv, ?_⟩
    rw [hs.others v hvt]
    exact VClock.le_trans hle (hs.clocks 0)

theorem fits : L.Fits proto U :=
  ⟨fun _ _ => Iff.rfl, fun _ h => h.1, fun _ h => h.1, stable⟩

/-- The protocol's invariant at a stop of `t`. -/
theorem inv_cur {G : ThreadId → Gh} {m : Mem} (t : ThreadId) (hi : proto.inv G m)
    (hph : (G t).1.ph ≠ .gone) : proto.inv G { m with current := t } := by
  obtain ⟨-, -, -, h⟩ := fits.on.cur t hi hph
  exact h

/-! ## The blocks -/

/-- `main`'s part with the lock's resource while it holds the lock. -/
theorem own_main {G : ThreadId → Gh} {rX : Res} {m : Mem} (hi : L.Inv G rX m) (hu : U G rX m) :
    (MainPart ⋆ fun r => r = L.held (G 0)) (L.own G m 0) := by
  rw [FLock.own_live (L := L) (rfl : joinedB m 0 = false)]
  exact ⟨_, _, hi.pdisj 0, rfl, hu.main, rfl⟩

theorem main_lt {X : ThreadId → Ph} {m : Mem} (h : Shape X m) : 0 < m.threads.size := by
  obtain ⟨-, -, -, ⟨_, _, _, _, _, hs, _⟩ | ⟨_, _, _, _, _, hs, _⟩⟩ := h <;> omega

/-- A byte of `io` is a byte of the protocol's rest at the `Counter`'s address. -/
theorem io_cell {G : ThreadId → Gh} {rX : Res} {m : Mem} (hi : L.Inv G rX m) {A : Nat}
    {bs : Array Byte} (hX : up (bytesAt cPtr A 24 .stack bs) rX) {x : Nat} (hx : x < bs.size) :
    ∃ blk, m.blocks[0]? = some blk ∧ blk.addr = A := by
  obtain ⟨fc, hfc, hc⟩ := up_bytesAt_cell hX rfl hx
  have hA : fc.cell.addr = A := by rw [hc]
  simp only [cPtr, Int.toNat_zero, Nat.zero_add] at hfc
  obtain ⟨rL, ho, -, hLX, -⟩ := hi.rest
  have hL : rL.heap (0, x) = none := (hLX (0, x)).resolve_right (by rw [hfc]; simp)
  obtain ⟨blk, hblk, -, -, hA'⟩ := ho.rest_addr (b := 0) (x := x) (fc := fc) (by
    have hW : (L.wordR m).heap (0, x) = none := cellsAt_none fun ⟨_, h2, h3⟩ => by
      have := (LockWord.off_erase.mp hi.xoff (0, x) ⟨rfl, h2, h3⟩)
      simp [hfc] at this
    simp [FHeap.union_apply, hW, hL, hfc])
  exact ⟨blk, hblk, by rw [hA', hA]⟩

/-- **The `Counter` is block 0**: live, 24 bytes on the stack, at an address that is a multiple of
8 (`main`'s extent and `io`'s address). -/
theorem blk0 {G : ThreadId → Gh} {rX : Res} {m : Mem} (hi : L.Inv G rX m) (hu : U G rX m) :
    m.BlkOk 0 24 8 .stack := by
  obtain ⟨rL, ho, -⟩ := hi.rest
  obtain ⟨blk, hblk, hl, hs, hk⟩ := ho.blkOf (t := 0) (main_lt hu.shape) (sep_assoc (own_main hi hu))
  obtain ⟨A, bs, hA, hbs, -, hX⟩ := hu.rest
  obtain ⟨blk', hblk', hA'⟩ := io_cell hi hX (x := 0) (by omega)
  rw [hblk] at hblk'; cases hblk'
  exact ⟨blk, hblk, hl, hs, by rw [hA']; exact hA, hk⟩

/-- **The `Io.Group` is block 1**: live, 16 bytes on the stack (`main`'s extent). -/
theorem blk1 {G : ThreadId → Gh} {rX : Res} {m : Mem} (hi : L.Inv G rX m) (hu : U G rX m) :
    m.BlkOk 1 16 1 .stack := by
  obtain ⟨rL, ho, -⟩ := hi.rest
  have h := own_main hi hu
  unfold MainPart at h
  rw [sep_left_comm_eq] at h
  obtain ⟨blk, hblk, hl, hs, hk⟩ := ho.blkOf (t := 0) (main_lt hu.shape) (sep_assoc h)
  exact ⟨blk, hblk, hl, hs, Nat.mod_one _, hk⟩

/-- A field pointer of the 24-byte `Counter` (block 0) is formed (`ptrProject`, MM-3). -/
theorem projC {m : Mem} (hb : m.BlkOk 0 24 8 .stack) {k : Nat} (hk : k ≤ 24) :
    (ptrProject cPtr (·.add k)).run m = pure (cPtr.add k, m) := by
  obtain ⟨blk, hb, -, hsz, -⟩ := hb
  exact ptrProject_block_run hb rfl (by decide) (by simp [cPtr, hsz]; omega)

/-! ## The threads -/

theorem shape_size {X : ThreadId → Ph} {m : Mem} (h : Shape X m) : m.threads.size ≤ 4 := by
  obtain ⟨-, -, -, ⟨j, k, hk, hj, -, hs, -⟩ | ⟨i, k, -, hk, -, hs, -⟩⟩ := h <;> omega

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
      rcases hph with ⟨j, k, -, -, h0, -⟩ | ⟨i, k, -, -, h0, -⟩ <;> rw [h0] at hx <;> cases hx
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
  · obtain ⟨jn, gt, hr, hj, hk⟩ := hrec u hu1 hu
    refine ⟨jn, gt, hr, fun hjn => ?_, ?_⟩
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

/-- `main`'s own increment, at its `j`-th async (`j < 3`): `spawn j k` to `spawn (j + 1) k`. -/
theorem shape_main {X : ThreadId → Ph} {m : Mem} {j k : Nat} (h : Shape X m)
    (hx : X 0 = .spawn j k) (hj : j < 3) : Shape (upd X 0 (.spawn (j + 1) k)) m := by
  obtain ⟨h00, hrec, hn, hph⟩ := h
  refine ⟨h00, fun u hu1 hu => ?_, fun u hu => ?_, ?_⟩
  · have hu0 : u ≠ 0 := by unfold ThreadId at *; omega
    obtain ⟨jn, gt, hr, hj', hk⟩ := hrec u hu1 hu
    exact ⟨jn, gt, hr, fun h => by rw [upd_ne _ _ hu0]; exact hj' h, by rw [upd_ne _ _ hu0]; exact hk⟩
  · by_cases hu0 : u = 0
    · exfalso; subst hu0
      have h4 : 0 < m.threads.size := by
        rcases hph with ⟨_, _, _, _, _, hs, _⟩ | ⟨_, _, _, _, _, hs, _⟩
        · rw [hs]; exact Nat.succ_pos _
        · rw [hs]; exact Nat.succ_pos _
      exact absurd hu (Nat.not_le.mpr h4)
    · rw [upd_ne _ _ hu0]; exact hn u hu
  · rcases hph with ⟨j', k', hk, -, h0, hs, hg, hjb⟩ | ⟨i, k', -, -, h0, -⟩
    · rw [hx] at h0; cases h0
      exact .inl ⟨j + 1, k, by omega, by omega, upd_self _ _ _, hs, hg, hjb⟩
    · rw [hx] at h0; cases h0

/-- The increments of thread `u ≥ 1`: at most one, and none for a thread that does not exist. -/
theorem count_kid {X : ThreadId → Ph} {m : Mem} {u : ThreadId} (h : Shape X m) (h1 : 1 ≤ u) :
    (X u).count ≤ 1 ∧ (m.threads.size ≤ u → (X u).count = 0) := by
  obtain ⟨-, hrec, hn, -⟩ := h
  by_cases hu : u < m.threads.size
  · obtain ⟨jn, gt, -, -, hk⟩ := hrec u h1 hu
    refine ⟨?_, fun h => absurd h (Nat.not_le.mpr hu)⟩
    rcases hk with ⟨d, hd⟩ | hd <;> rw [hd]
    · cases d <;> decide
    · decide
  · rw [hn u (Nat.le_of_not_lt hu)]; exact ⟨by decide, fun _ => rfl⟩

/-- `main`'s increments and the number of threads: `j - k` or `3 - k` with `k + 1` threads. -/
theorem count_main {X : ThreadId → Ph} {m : Mem} (h : Shape X m) :
    ∃ k, k ≤ 3 ∧ m.threads.size = k + 1 ∧
      ((∃ j, k ≤ j ∧ j ≤ 3 ∧ X 0 = .spawn j k ∧ (X 0).count = j - k) ∨
       (∃ i, X 0 = .joins i k ∧ (X 0).count = 3 - k)) := by
  obtain ⟨-, -, -, ⟨j, k, hk, hj, h0, hs, -⟩ | ⟨i, k, -, hk, h0, hs, -⟩⟩ := h
  · exact ⟨k, by omega, hs, .inl ⟨j, hk, hj, h0, by rw [h0]; rfl⟩⟩
  · exact ⟨k, hk, hs, .inr ⟨i, h0, by rw [h0]; rfl⟩⟩

/-- The sum, when task `t` did not do its increment: at most 2. -/
theorem sum_le {X : ThreadId → Ph} {m : Mem} {t : ThreadId} (h : Shape X m)
    (hx : X t = .task false) : sum X ≤ 2 := by
  obtain ⟨h1, htl, h3⟩ := task_at h hx
  obtain ⟨k, hk3, hs, hm⟩ := count_main h
  obtain ⟨c1, z1⟩ := count_kid h (u := 1) (by decide)
  obtain ⟨c2, z2⟩ := count_kid h (u := 2) (by decide)
  obtain ⟨c3, z3⟩ := count_kid h (u := 3) (by decide)
  have c0 : (X t).count = 0 := by rw [hx]; rfl
  unfold sum
  rw [hs] at z1 z2 z3 htl
  have ht : t = 1 ∨ t = 2 ∨ t = 3 := by unfold ThreadId at *; omega
  rcases hm with ⟨j, -, hj, -, e0⟩ | ⟨i, -, e0⟩ <;> rw [e0] <;>
    rcases ht with rfl | rfl | rfl <;>
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
    simp_all <;> omega

/-- The sum at `main`'s `j`-th async (`j < 3`): at most 2. -/
theorem sum_le_main {X : ThreadId → Ph} {m : Mem} {j k : Nat} (h : Shape X m)
    (hx : X 0 = .spawn j k) (hj : j < 3) : sum X ≤ 2 := by
  obtain ⟨k', -, hs, hm⟩ := count_main h
  obtain ⟨c1, z1⟩ := count_kid h (u := 1) (by decide)
  obtain ⟨c2, z2⟩ := count_kid h (u := 2) (by decide)
  obtain ⟨c3, z3⟩ := count_kid h (u := 3) (by decide)
  rcases hm with ⟨j', hk, -, e, e0⟩ | ⟨i, e, -⟩
  · rw [hx] at e; cases e
    unfold sum
    rw [hs] at z1 z2 z3
    rw [e0]
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;> simp_all <;> omega
  · rw [hx] at e; cases e

/-- Task `t`'s increment: the sum is one more. -/
theorem sum_succ {X : ThreadId → Ph} {t : ThreadId} (h1 : 1 ≤ t) (h3 : t ≤ 3)
    (hx : X t = .task false) : sum (upd X t (.task true)) = sum X + 1 := by
  have c0 : (X t).count = 0 := by rw [hx]; rfl
  unfold sum
  rcases (by unfold ThreadId at *; omega : t = 1 ∨ t = 2 ∨ t = 3) with rfl | rfl | rfl
  · rw [upd_self, upd_ne _ _ (by decide : (0 : Nat) ≠ 1), upd_ne _ _ (by decide : (2 : Nat) ≠ 1),
      upd_ne _ _ (by decide : (3 : Nat) ≠ 1)]
    show _ + 1 + _ + _ = _; omega
  · rw [upd_self, upd_ne _ _ (by decide : (0 : Nat) ≠ 2), upd_ne _ _ (by decide : (1 : Nat) ≠ 2),
      upd_ne _ _ (by decide : (3 : Nat) ≠ 2)]
    show _ + _ + 1 + _ = _; omega
  · rw [upd_self, upd_ne _ _ (by decide : (0 : Nat) ≠ 3), upd_ne _ _ (by decide : (1 : Nat) ≠ 3),
      upd_ne _ _ (by decide : (2 : Nat) ≠ 3)]
    show _ + _ + _ + 1 = _; omega

/-- `main`'s own increment: the sum is one more. -/
theorem sum_succ_main {X : ThreadId → Ph} {j k : Nat} (hk : k ≤ j) (hx : X 0 = .spawn j k) :
    sum (upd X 0 (.spawn (j + 1) k)) = sum X + 1 := by
  unfold sum
  rw [upd_self, upd_ne _ _ (by decide : (1 : Nat) ≠ 0), upd_ne _ _ (by decide : (2 : Nat) ≠ 0),
    upd_ne _ _ (by decide : (3 : Nat) ≠ 0), hx]
  show (j + 1 - k) + _ + _ + _ = (j - k) + _ + _ + _ + 1
  omega

/-- `main` spawned every thread. -/
theorem spawners {X : ThreadId → Ph} {m : Mem} (h : Shape X m) : ∀ r ∈ m.threads, r.spawner = 0 :=
  spawners_of_getElem fun i hi => by
    obtain ⟨h0, hrec, -⟩ := h
    by_cases hi0 : i = 0
    · subst hi0; rw [Array.getElem?_eq_getElem hi] at h0; rw [Option.some.inj h0]
    · obtain ⟨jn, gt, hr, -⟩ := hrec i (Nat.pos_of_ne_zero hi0) hi
      rw [Array.getElem?_eq_getElem hi] at hr; rw [Option.some.inj hr]

/-! ## Steps on a thread's own part -/

/-- A step of thread `t` (not joined) that keeps the protocol's rest `rX` (`FStepIn`) keeps `U`,
with `t`'s new ghost value `g` (the same part) and the shape `hsh`. -/
theorem U_step {G : ThreadId → Gh} {rX : Res} {m m' : Mem} {t : ThreadId} {g : Gh}
    (hu : U G rX m) (hc : m.current = t) (hjt : joinedB m t = false)
    (hs : FStepIn rX.heap.erase m m') (hpart : g.1.part = (G t).1.part)
    (hsh : Shape (upd (fun u => (G u).2) t g.2) m) : U (upd G t g) rX m' := by
  have hjb : joinedB m' = joinedB m := LockWord.joinedB_congr hs.threads
  obtain ⟨A, bs, -, hbs, -, hX⟩ := hu.rest
  have hP : ∀ u, (upd G t g u).1.part = (G u).1.part := fun u => by
    unfold upd; split
    · rename_i e; subst e; exact hpart
    · rfl
  refine ⟨?_, fun e he hr => ?_, fun u hu0 => by rw [hP]; exact hu.parts u hu0,
    by rw [hP]; exact hu.main, hu.rest, fun v hv => ?_⟩
  · rw [FLock.snd_upd]; unfold Shape at hsh ⊢; rw [hs.threads, hs.groups, hjb]; exact hsh
  · rcases hs.fp e he with ⟨e₀, he₀, hn⟩ | ⟨-, hnt, -⟩
    · obtain ⟨-, hb, hk, ho, hl, hcl⟩ := hn
      rcases hu.io e₀ he₀ ⟨hb.symm.trans hr.1, by have := hr.2.1; omega,
        by have := hr.2.2; omega⟩ with ⟨hk', h''⟩ | h''
      · exact .inl ⟨hk.trans hk', LockWord.someLe_mono hs.threads (fun u _ => hs.clock u)
          (LockWord.someLe_le hcl h'')⟩
      · exact .inr (LockWord.allLe_mono hs.threads (fun u _ => hs.clock u)
          fun u hu => VClock.le_trans hcl (h'' u hu))
    · refine absurd ⟨e.off, Nat.le_refl _, by have := hr.2.1; omega, ?_⟩ hnt
      have hr2 := hr.2.2
      have := (up_bytesAt_some hX rfl (e.block, e.off)).mpr ⟨hr.1, by simp [cPtr],
        by simp [cPtr, hbs]; omega⟩
      simpa [FHeap.erase] using this
  · rw [hjb] at hv
    have hvt : v ≠ t := fun e => by rw [e, hjt] at hv; cases hv
    obtain ⟨h1, h2⟩ := hu.jle v hv
    refine ⟨by rw [upd_ne _ _ hvt]; exact h1, ?_⟩
    rw [hs.others v (hc ▸ hvt)]
    exact VClock.le_trans h2 (hs.clock 0)

/-! ## `io` -/

/-- A read of `io` by thread `t` (not joined) in generated code: no race (the tasks read-share
it), and the invariant holds after it (`FLock.Inv.recordX`: `io` is the protocol's rest). -/
theorem wp_io {σ : Type} {s : σ} {t : ThreadId} {G : ThreadId → Gh} {m : Mem} {d : Nat} {g : Gh}
    (hi : proto.inv (upd G t g) m) (hc : m.current = t) (ht : t < m.threads.size)
    (hjt : joinedB m t = false) {Q : Io × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ m', m'.current = t → m'.threads = m.threads → proto.inv (upd G t g) m' →
      Q (⟨⟩, s) G m' d) :
    proto.WP t ((liftM (load Io 8 cPtr) : CM Tgt σ Io).run s) Q G m d := by
  obtain ⟨rX, hiL, hU⟩ := hi
  obtain ⟨A, bs, -, hbs, hdec, hX⟩ := hU.rest
  obtain ⟨blk, hblk, hl, hs, ha, hk⟩ := blk0 hiL hU
  have hacc : m.access cPtr (Enc.size Io) 8 = pure (0, blk, 0) :=
    access_of (p := cPtr) rfl hblk hl (by decide)
      (by rw [show Enc.size Io = 16 from rfl]; simp [cPtr, hs]) (by simpa [cPtr] using ha)
  obtain ⟨blk', hblk', hx⟩ := hiL.restBytes hX rfl (fun _ _ h => h) (by rw [hbs]; decide)
  rw [hblk] at hblk'; cases hblk'
  have hx' : blk.bytes.extract 0 (0 + Enc.size Io) = bs := by
    rw [show Enc.size Io = bs.size by rw [hbs]; rfl]; simpa [cPtr] using hx
  have hd : Enc.decode (blk.bytes.extract 0 (0 + Enc.size Io)) = pure (⟨⟩ : Io) := by
    rw [hx']; exact hdec
  have hrun : (load Io 8 cPtr).run m = pure (⟨⟩, m.recordAt 0 0 16 .read) :=
    load_run hacc hd (by rw [hk]; decide) (hU.io.noRace_read (hc ▸ ht) covers_io)
  refine WP.liftM (fun e he => (MemM.noErr_of_run hrun e he).elim) fun v m' hr => ?_
  rw [hrun] at hr
  simp only [pure, ExceptT.pure, ExceptT.mk, ExceptT.run, Option.some.injEq, Except.ok.injEq,
    Prod.mk.injEq] at hr
  obtain ⟨-, rfl⟩ := hr
  cases v
  refine ⟨rfl, h _ hc rfl ⟨rX, hiL.recordX (k := .read) (by decide) hc ht
    (Array.getElem?_eq_some_iff.mp hblk).1 (by decide) fun x _ hx =>
      (up_bytesAt_some hX rfl (0, x)).mpr ⟨rfl, by simp [cPtr], by simp [cPtr]; omega⟩, ?_⟩⟩
  refine ⟨hU.shape, hU.io.read (hc ▸ ht) hiL.w.csize 0 0 16, hU.parts, hU.main, hU.rest,
    fun v hv => ?_⟩
  have hv' : joinedB m v = true := hv
  obtain ⟨h1, h2⟩ := hU.jle v hv'
  refine ⟨h1, ?_⟩
  have hvc : v ≠ m.current := fun e => by rw [e, hc, hjt] at hv'; cases hv'
  show VClock.le ((m.clocks.set! m.current _)[v]!) ((m.clocks.set! m.current _)[0]!) = true
  rw [Proto.getElem!_set!_ite, if_neg (fun h => hvc h.1)]
  exact VClock.le_trans h2 (LockWord.recordAt_le m 0 0 16 .read 0)

/-! ## The holder's increment -/

/-- A thread out of the lock's code with the part `rp`, at the place `p`. -/
def gOut (rp : Res) (p : Ph) : Gh := (⟨.out, rp, rnil⟩, p)

/-- A thread with the part `rp` at the place `p` that holds the mutex and the counter `rL`. -/
def gHold (rp : Res) (p : Ph) (rL : Res) : Gh := (⟨.holds, rp, rL⟩, p)

/-- The ghost values `X` after a new ghost value for `t` with the place `p`. -/
theorem snd_upd_upd (G : ThreadId → Gh) (t : ThreadId) (g g' : Gh) (h : g'.2 = g.2) :
    (fun u => (upd (upd G t g) t g' u).2) = fun u => (upd G t g u).2 := by
  funext u; unfold upd; split
  · exact h
  · rfl

/-- The holder's step on the counter, a thread triple on its part `rp ⋆ counter`
(`FLock.Inv.wp_liftM`): the holder goes from the place `p₀` to `p₁`, the counter's new resource
has `R` at `p₁` (`hR`), and the shape holds at `p₁`. -/
theorem wp_cnt {σ α : Type} {x : MemM α} {s : σ} {t : ThreadId} {rp rL : Res} {p₀ p₁ : Ph}
    {G : ThreadId → Gh} {m : Mem} {d : Nat} {Pa : FAssn} {Qa : α → FAssn}
    (htt : FTTriple Pa x Qa) (hpa : R (fun u => (upd G t (gHold rp p₀ rL) u).2) rL → Pa rL)
    (hi : proto.inv (upd G t (gHold rp p₀ rL)) m) (hc : m.current = t)
    (hsh : Shape (upd (fun u => (upd G t (gHold rp p₀ rL) u).2) t p₁) m)
    {Q : α × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (hR : ∀ a r, Qa a r → R (fun u => (upd G t (gHold rp p₁ r) u).2) r)
    (h : ∀ a m' rQ, m'.current = t → m'.threads = m.threads → Qa a rQ →
      proto.inv (upd G t (gHold rp p₁ rQ)) m' → Q (a, s) G m' d) :
    proto.WP t ((liftM x : CM Tgt σ α).run s) Q G m d := by
  obtain ⟨rX, hiL, hU⟩ := hi
  have hh : L.ph (upd G t (gHold rp p₀ rL) t) = .holds := by rw [upd_self]; rfl
  obtain ⟨ht, hjt⟩ := hiL.ht (by rw [hh]; decide)
  have hres : R (fun u => (upd G t (gHold rp p₀ rL) u).2) rL := by
    have := hiL.res t hh; rwa [upd_self] at this
  have hd : FHeap.Disjoint rp.heap rL.heap := by have := hiL.pdisj t; rwa [upd_self] at this
  refine hiL.wp_liftM hc ht hjt (htt.frameL (R := fun r => r = rp))
    (by rw [upd_self]; exact ⟨rp, rL, hd, rfl, rfl, hpa hres⟩) fun a m' r' hr hq hs hc' hk => ?_
  obtain ⟨r₁, rQ, hdQ, e, hr₁, hq'⟩ := hq
  rw [hr₁] at e hdQ
  have hl := hk (gHold rp p₁ rQ) (by rw [upd_self]; rfl) e.symm hdQ (fun h => absurd rfl h)
    (fun h => absurd hh h) (fun _ => by
      show R (fun u => (upd (upd G t (gHold rp p₀ rL)) t (gHold rp p₁ rQ) u).2) rQ
      rw [upd_upd]; exact hR a rQ hq')
  rw [upd_upd] at hl
  have hU' := U_step (g := gHold rp p₁ rQ) hU hc hjt
    (hs.weaken fun l hl => by
      simp only [rsum, FHeap.erase, FHeap.union_apply, ne_eq, Option.map_eq_none_iff,
        Option.or_eq_none_iff, not_and] at hl ⊢
      exact fun _ => hl)
    (by rw [upd_self]; rfl) hsh
  rw [upd_upd] at hU'
  exact h a m' rQ hc' hs.threads hq' ⟨rX, hl, hU'⟩

/-- The place `p₀` of thread `t` before its increment and `p₁` after it: in every shape the sum is
at most 2 before it, one more after it, and the shape stays. -/
def IncStep (t : ThreadId) (p₀ p₁ : Ph) : Prop :=
  ∀ X m, Shape X m → X t = p₀ → sum X ≤ 2 ∧ sum (upd X t p₁) = sum X + 1 ∧ Shape (upd X t p₁) m

/-- A task's increment. -/
theorem incStep_task (t : ThreadId) : IncStep t (.task false) (.task true) := fun _ _ hsh hx => by
  obtain ⟨h1, -, h3⟩ := task_at hsh hx
  exact ⟨sum_le hsh hx, sum_succ h1 h3 hx, shape_task hsh hx _ (.inl ⟨true, rfl⟩)⟩

/-- `main`'s own increment at its `j`-th async. -/
theorem incStep_main {j k : Nat} (hj : j < 3) : IncStep 0 (.spawn j k) (.spawn (j + 1) k) :=
  fun _ _ hsh hx => by
    obtain ⟨k', -, -, ⟨j', hk, -, e, -⟩ | ⟨i, e, -⟩⟩ := count_main hsh
    · rw [hx] at e; cases e
      exact ⟨sum_le_main hsh hx hj, sum_succ_main hk hx, shape_main hsh hx hj⟩
    · rw [hx] at e; cases e

/-- The shape at the place `p` of `t`: the same. -/
theorem shape_self {G : ThreadId → Gh} {m : Mem} {t : ThreadId} {g : Gh}
    (h : Shape (fun u => (upd G t g u).2) m) : Shape (upd (fun u => (upd G t g u).2) t g.2) m := by
  have e : upd (fun u => (upd G t g u).2) t g.2 = fun u => (upd G t g u).2 := by
    funext u; by_cases hu : u = t
    · subst hu; simp [upd]
    · simp [upd, hu]
  rw [e]; exact h

/-- `add` by thread `t` with the part `rp` at the place `p₀` (a task, or `main` that runs the
task itself): `io`, `lock`, the increment of the counter, `io`, `unlock`; then `t` is at `p₁`. -/
theorem add_spec (t : ThreadId) (rp : Res) (p₀ p₁ : Ph) (hinc : IncStep t p₀ p₁)
    (G : ThreadId → Gh) (m : Mem) (d : Nat) (hi : proto.inv (upd G t (gOut rp p₀)) m)
    (hc : m.current = t) :
    proto.WP t (add cPtr) (fun _ G' m' d' => d' ≤ d ∧ m'.current = t ∧
      proto.inv (upd G' t (gOut rp p₁)) m') G m d := by
  obtain ⟨ht, hjt⟩ := (show L.Inv _ _ m from hi.choose_spec.1).ht (t := t)
    (by rw [upd_self]; exact (by decide : LPh.out ≠ LPh.gone))
  have hb0 : ∀ {G' : ThreadId → Gh} {m' : Mem}, proto.inv G' m' → m'.BlkOk 0 24 8 .stack :=
    fun hi' => by obtain ⟨rX, hiL, hU⟩ := hi'; exact blk0 hiL hU
  unfold add
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, pure_bind]
  refine WP.bind (WP.callMC_ptrProject (projC (hb0 hi) (k := 16) (by decide)) ?_)
  dsimp only
  -- the read of `io`
  refine WP.bind (wp_io hi hc ht hjt fun m₁ hc₁ ht₁ hi₁ => ?_)
  -- `lock`
  refine WP.bind (WP.callC (WP.mono ?_ (ioMutex.lock_wp fits.on rfl rfl rfl t (gOut rp p₀) rfl
    trivial _ G m₁ d hi₁)))
  rintro _ G₂ m₂ d₂ ⟨hd₂, hc₂, rL, hi₂⟩
  have hi₂' : proto.inv (upd G₂ t (gHold rp p₀ rL)) m₂ := hi₂
  refine WP.bind (WP.callMC_ptrProject (projC (hb0 hi₂') (k := 20) (by decide)) ?_)
  dsimp only
  have hsh₂ : Shape (upd (fun u => (G₂ u).2) t p₀) m₂ := by
    obtain ⟨rX, -, hU⟩ := hi₂'; have := hU.shape; rw [FLock.snd_upd] at this; exact this
  obtain ⟨hsum, hsucc0, hsh₁⟩ := hinc _ _ hsh₂ (upd_self _ _ _)
  have hS0 : (sum fun u => (upd G₂ t (gHold rp p₀ rL) u).2) = sum (upd (fun u => (G₂ u).2) t p₀) := by
    rw [FLock.snd_upd]; rfl
  -- the load of the counter
  refine WP.bind (wp_cnt (p₁ := p₀) (FTTriple.load (q := cPtr.add 20) (a := 4)
    (v := BitVec.ofNat 32 (sum fun u => (upd G₂ t (gHold rp p₀ rL) u).2)) (by decide))
    (fun h => h) hi₂' hc₂ (shape_self (by obtain ⟨rX, -, hU⟩ := hi₂'; exact hU.shape))
    (fun a r h => by
      have := (sep_lift.mp h).2
      unfold R; rw [FLock.snd_upd]; rw [FLock.snd_upd] at this; exact this)
    fun a m₃ rQ hc₃ ht₃ hq hi₃ => ?_)
  obtain ⟨rfl, -⟩ := sep_lift.mp hq
  rw [← hS0] at hsum
  generalize hS : (sum fun u => (upd G₂ t (gHold rp p₀ rL) u).2) = S at hsum hS0 ⊢
  have hS3 : S + 1 < 2 ^ 32 := Nat.lt_of_le_of_lt (by omega : S + 1 ≤ 3) (by decide)
  have hS32 : (BitVec.ofNat 32 S).toNat = S := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  -- the add
  refine WP.bind (WP.callRC (fun e he => (add_one_noErr (by rw [hS32]; exact hS3) e he).elim)
    fun v₃ hadd => ?_)
  have hv₃ := add_one_ok hadd (by rw [hS32]; exact hS3)
  rw [hS32] at hv₃
  -- the store
  have hsucc : ∀ r, (sum fun u => (upd G₂ t (gHold rp p₁ r) u).2) = S + 1 := fun r => by
    rw [← hS, FLock.snd_upd, FLock.snd_upd]; rw [upd_upd] at hsucc0; exact hsucc0
  have hshape₃ : Shape (upd (fun u => (upd G₂ t (gHold rp p₀ rQ) u).2) t p₁) m₃ := by
    obtain ⟨rX, -, hU⟩ := hi₃
    have := hU.shape; rw [FLock.snd_upd] at this ⊢
    have h3 := (hinc _ _ this (upd_self _ _ _)).2.2
    rwa [upd_upd] at h3 ⊢
  refine WP.bind (wp_cnt (p₁ := p₁) (FTTriple.store (q := cPtr.add 20) (a := 4)
    (v := BitVec.ofNat 32 S) (by decide) v₃) (fun h => ?_) hi₃ hc₃ hshape₃
    (fun _ r h => ?_) fun _ m₄ rQ' hc₄ ht₄ _ hi₄ => ?_)
  · have : (sum fun u => (upd G₂ t (gHold rp p₀ rQ) u).2) = S := by
      rw [← hS, FLock.snd_upd, FLock.snd_upd]; rfl
    unfold R at h; rwa [this] at h
  · show up (pts (cPtr.add 20) 4 (BitVec.ofNat 32 _)) r
    rw [hsucc r]
    have : v₃ = BitVec.ofNat 32 (S + 1) := by
      apply BitVec.eq_of_toNat_eq; rw [hv₃, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hS3]
    rw [← this]; exact h
  -- the read of `io`
  have hl₄ : t < m₄.threads.size ∧ joinedB m₄ t = false := by
    obtain ⟨rX, hiL, -⟩ := hi₄
    exact hiL.ht (by rw [upd_self]; exact (by decide : LPh.holds ≠ LPh.gone))
  refine WP.bind (WP.callMC_ptrProject (projC (hb0 hi₄) (k := 16) (by decide)) ?_)
  dsimp only
  refine WP.bind (wp_io hi₄ hc₄ hl₄.1 hl₄.2 fun m₅ hc₅ ht₅ hi₅ => ?_)
  -- `unlock`
  refine WP.bind (WP.callC (WP.mono ?_ (ioMutex.unlock_wp fits.on rfl rfl rfl t (gHold rp p₁ rQ') rfl
    trivial _ G₂ m₅ d₂ hi₅ hc₅)))
  rintro _ G₃ m₆ d₃ ⟨hd₃, hc₆, hi₆⟩
  simp only [StateT.run_pure, pure_bind]
  refine WP.pure' ?_
  exact WP.pure' ⟨by omega, hc₆, hi₆⟩

/-! ## A task -/

/-- A task at its end: `out` to `gone`, `task true` to `fin`. -/
theorem inv_end {G : ThreadId → Gh} {m : Mem} {t : ThreadId}
    (hi : proto.inv (upd G t (gOut rnil (.task true))) m) :
    proto.inv (upd G t (⟨.gone, rnil, rnil⟩, .fin)) m := by
  obtain ⟨rX, hiL, hU⟩ := hi
  have hx : (fun u => (upd G t (gOut rnil (.task true)) u).2) t = .task true := by
    show (upd G t _ t).2 = _; rw [upd_self]; rfl
  have ht0 : t ≠ 0 := by
    have := (task_at hU.shape hx).1; unfold ThreadId at *; omega
  have hsum : sum (fun u => (upd (upd G t (gOut rnil (.task true))) t
      (⟨.gone, rnil, rnil⟩, .fin) u).2) = sum (fun u => (upd G t (gOut rnil (.task true)) u).2) := by
    rw [FLock.snd_upd]; apply sum_congr; intro u _
    by_cases h : u = t
    · subst h; simp [upd, gOut, Ph.count]
    · simp [upd, h]
  have hl := hiL.ghost (t := t) (g := (⟨.gone, rnil, rnil⟩, .fin)) (by rw [upd_self]; rfl)
    (.inr (.inl rfl)) (by rw [upd_self]; rfl) rfl (fun h => absurd rfl h)
    (fun r hR => by
      have hR' : R (fun u => (upd G t (gOut rnil (.task true)) u).2) r := hR
      show R _ r; unfold R at hR' ⊢; rw [hsum]; exact hR')
  rw [upd_upd] at hl
  refine ⟨rX, hl, ?_⟩
  have hsh := shape_task hU.shape hx .fin (.inr rfl)
  rw [FLock.snd_upd, upd_upd] at hsh
  refine ⟨by rw [FLock.snd_upd]; exact hsh, hU.io, fun u hu => ?_, ?_, hU.rest, fun v hv => ?_⟩
  · unfold upd; split
    · rfl
    · rename_i h; have := hU.parts u hu; rwa [upd_ne _ _ h] at this
  · rw [upd_ne _ _ (Ne.symm ht0)]; have := hU.main; rwa [upd_ne _ _ (Ne.symm ht0)] at this
  · obtain ⟨h1, h2⟩ := hU.jle v hv
    refine ⟨?_, h2⟩
    unfold upd; split
    · rfl
    · rename_i h; rwa [upd_ne _ _ h] at h1

/-- A task: `add` on the `Counter`, then its end. -/
theorem dispatch_spec (tgt : Tgt) (g : Gh) (hg : proto.init tgt g) (u : ThreadId)
    (G : ThreadId → Gh) (m : Mem) (d : Nat) (hu : 0 < u) (hgu : G u = g) (hi : proto.inv G m) :
    proto.WP u (dispatch tgt) (proto.QKid u) G { m with current := u } d := by
  cases tgt with
  | add p =>
    obtain ⟨rfl, rfl⟩ := hg
    show proto.WP u ((fun _ => ()) <$> add cPtr) _ G _ d
    refine WP.map (WP.mono ?_ (add_spec u rnil _ _ (incStep_task u) G _ d
      (by rw [show gOut rnil (.task false) = G u from hgu.symm, upd_same]
          exact inv_cur u hi (by rw [hgu]; exact (by decide : LPh.out ≠ LPh.gone))) rfl))
    rintro _ G' m' _ ⟨-, -, hi'⟩
    have hi'' := inv_end hi'
    refine ⟨_, hi'', ⟨rfl, rfl⟩, fun _ => ?_⟩
    obtain ⟨rX, -, hU⟩ := hi''
    exact joinedAll_of_main (spawners hU.shape) hu

/-! ## `main`'s spawns and joins -/

/-- `main` after `j` asyncs, `k` of which made a task. -/
abbrev gSpawn (rM : Res) (j k : Nat) : Gh := gOut rM (.spawn j k)

/-- `main` after the `await` of `k` tasks and `i` joins. -/
abbrev gJoins (rM : Res) (i k : Nat) : Gh := gOut rM (.joins i k)

theorem grp_succ (j : Nat) : grp (j + 1) = (grp j).push (gPtr, j + 1) := by
  simp [grp, Array.range_succ]

/-- A new ghost value for `main` with the same count keeps the counter's resource. -/
theorem R_main {G : ThreadId → Gh} {r : Res} {g : Gh} (hR : L.R G r)
    (hc : g.2.count = (G 0).2.count) : L.R (upd G 0 g) r := by
  have hR' : R (fun u => (G u).2) r := hR
  show R _ r; unfold R at hR' ⊢
  rw [sum_congr (X := fun u => (G u).2) fun u _ => by
    show (upd G 0 g u).2.count = _
    by_cases hu : u = 0
    · subst hu; rw [upd_self]; exact hc
    · rw [upd_ne _ _ hu]]
  exact hR'

/-- The spawn of task `k + 1` by `main` at its `j`-th async (`Group.async`; a deferred task if
`gt`): the task's part is empty, and the group records it. -/
theorem inv_spawn {G₁ : ThreadId → Gh} {m₁ m' : Mem} {child : ThreadId} {rM : Res} {j k : Nat}
    {gt : Bool} (hj : j < 3) (hi : proto.inv G₁ m₁) (hg : G₁ 0 = gSpawn rM j k)
    (hf : ((Thread.forkWith gt).run { m₁ with current := 0 }).run = some (.ok (child, m'))) :
    child = k + 1 ∧ m'.current = 0 ∧
      proto.inv (upd (upd G₁ child (gOut rnil (.task false))) 0 (gSpawn rM (j + 1) (k + 1)))
        { m' with groups := m'.groups.push (gPtr, child) } := by
  obtain ⟨rX, hiL, hU⟩ := hi
  obtain ⟨h00, hrec, hnone, hph⟩ := hU.shape
  have hX0 : (G₁ 0).2 = .spawn j k := by rw [hg]; rfl
  obtain ⟨j', k', hk', -, h0, hsz, hgr, hjb⟩ | ⟨i, k', -, -, h0, -⟩ := hph
  rotate_left
  · exfalso; change (G₁ 0).2 = _ at h0; rw [hX0] at h0; cases h0
  obtain ⟨e1, e2⟩ : j' = j ∧ k' = k := by
    change (G₁ 0).2 = _ at h0; rw [hX0] at h0; cases h0; exact ⟨rfl, rfl⟩
  subst j' k'
  have hcs : m₁.clocks.size = k + 1 := by rw [hiL.w.csize, hsz]
  have hX : ∀ u, (upd (upd G₁ (k + 1) (gOut rnil (.task false))) 0
      (gSpawn rM (j + 1) (k + 1)) u).2 =
      if u = 0 then .spawn (j + 1) (k + 1) else if u = k + 1 then .task false else (G₁ u).2 := by
    intro u; unfold upd; split
    · rfl
    · split <;> rfl
  have hfk := hf
  rw [Proto.forkWith_run] at hf
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hf
  obtain ⟨rfl, rfl⟩ := hf
  have hne : (k + 1 : Nat) ≠ 0 := by omega
  have hl := hiL.fork (t := 0) (g₁ := gSpawn rM (j + 1) (k + 1)) (g₀ := gOut rnil (.task false))
    (by rw [hg]; rfl) hfk (by rw [hg]; exact (rsum_rnil rM).symm) (FHeap.disjoint_empty _) rfl rfl
    rfl rfl fun r hR => by
      -- the counter does not change: the new task has not done its increment, and `main` made
      -- one more task
      have hR' : R (fun u => (G₁ u).2) r := hR
      show R _ r; unfold R at hR' ⊢
      rw [sum_congr (X := fun u => (G₁ u).2) fun u _ => by
        show (upd (upd G₁ m₁.threads.size (gOut rnil (.task false))) 0
          (gSpawn rM (j + 1) (k + 1)) u).2.count = _
        rw [hsz, hX u]
        by_cases hu0 : u = 0
        · subst hu0; rw [if_pos rfl, hX0]; show (j + 1) - (k + 1) = j - k; omega
        · rw [if_neg hu0]
          by_cases hu : u = k + 1
          · subst hu
            rw [if_pos rfl, show (G₁ (k + 1)).2 = .none from
              hnone _ (by rw [hsz]; exact Nat.le_refl _)]
            rfl
          · rw [if_neg hu]]
      exact hR'
  rw [hsz] at hl ⊢
  refine ⟨rfl, rfl, rX, hl.groups _, ⟨⟨?_, fun u hu1 hu => ?_, fun u hu => ?_,
      .inl ⟨j + 1, k + 1, by omega, by omega,
        by show (upd (upd G₁ (k + 1) (gOut rnil (.task false))) 0 (gSpawn rM (j + 1) (k + 1)) 0).2 = _
           rw [upd_self]; rfl, by simp [hsz],
        by rw [hgr, grp_succ], fun u => ?_⟩⟩, ?_, fun u hu0 => ?_, ?_, hU.rest, fun v hv => ?_⟩⟩
  · simp only [Array.getElem?_push]; rw [if_neg (by omega)]; exact h00
  · simp only [Array.size_push] at hu
    show ∃ jn gt', (m₁.threads.push _)[u]? = _ ∧ _
    simp only [Array.getElem?_push]
    rw [hX u]
    by_cases hu' : u = k + 1
    · subst hu'
      refine ⟨false, gt, by simp [hsz], fun h => absurd h (by decide), ?_⟩
      simp [hne]
    · have hu0 : u ≠ 0 := by unfold ThreadId at *; omega
      rw [if_neg (by rw [hsz]; exact hu'), if_neg hu0, if_neg hu']
      exact hrec u hu1 (by rw [hsz]; unfold ThreadId at *; omega)
  · simp only [Array.size_push] at hu
    show (upd (upd G₁ (k + 1) (gOut rnil (.task false))) 0 (gSpawn rM (j + 1) (k + 1)) u).2 = _
    rw [hX u, if_neg (by unfold ThreadId at *; omega),
      if_neg (by rw [hsz] at hu; unfold ThreadId at *; omega)]
    exact hnone u (by rw [hsz] at hu ⊢; unfold ThreadId at *; omega)
  · unfold joinedB
    simp only [Array.getElem?_push]
    by_cases hu : u = m₁.threads.size
    · simp [hu]
    · rw [if_neg hu]; have := hjb u; unfold joinedB at this; exact this
  · obtain ⟨hcl, hcn, -⟩ := LockWord.fork_clocks (cs := m₁.clocks) (t := 0) (by
      rw [hcs]; exact Nat.succ_pos _)
    exact hU.io.fork (t := 0) (by rw [← hiL.w.csize, hcs]; exact Nat.succ_pos _)
      (by show (m₁.threads.push _).size = _; simp)
      (fun u hu => hcl u (by rw [hiL.w.csize]; exact hu)) (by rw [← hiL.w.csize]; exact hcn)
      fun _ he _ => he
  · unfold upd; rw [if_neg hu0]; split
    · rfl
    · exact hU.parts u hu0
  · rw [upd_self]; have := hU.main; rw [hg] at this; exact this
  · exfalso
    have : joinedB m₁ v = true := by
      unfold joinedB at hv ⊢
      simp only [Array.getElem?_push] at hv
      by_cases h : v = m₁.threads.size
      · simp [h] at hv
      · rwa [if_neg h] at hv
    rw [hjb v] at this; cases this

/-- `Group.await` takes the three tasks: `main` goes to its joins. -/
theorem inv_await {G : ThreadId → Gh} {m : Mem} {rM : Res} {k : Nat}
    (hi : proto.inv (upd G 0 (gSpawn rM 3 k)) m) :
    proto.inv (upd G 0 (gJoins rM 0 k)) { m with groups := #[] } := by
  obtain ⟨rX, hiL, hU⟩ := hi
  obtain ⟨h00, hrec, hnone, hph⟩ := hU.shape
  have hX0 : (upd G 0 (gSpawn rM 3 k) 0).2 = .spawn 3 k := by rw [upd_self]; rfl
  obtain ⟨j, k', hk, -, h0, hsz, -, hjb⟩ | ⟨i, k', -, -, h0, -⟩ := hph
  rotate_left
  · exfalso; change (upd G 0 (gSpawn rM 3 k) 0).2 = _ at h0; rw [hX0] at h0; cases h0
  obtain ⟨e1, e2⟩ : j = 3 ∧ k' = k := by
    change (upd G 0 (gSpawn rM 3 k) 0).2 = _ at h0; rw [hX0] at h0; cases h0; exact ⟨rfl, rfl⟩
  subst j k'
  have hl := hiL.ghost (t := 0) (g := gJoins rM 0 k) (by rw [upd_self]; rfl) (.inl rfl)
    (by rw [upd_self]; rfl) rfl (fun _ => ⟨by rw [hsz]; exact Nat.succ_pos _, rfl⟩)
    fun r hR => R_main hR (by rw [upd_self]; rfl)
  rw [upd_upd] at hl
  have hX : ∀ u, u ≠ 0 → upd G 0 (gJoins rM 0 k) u = upd G 0 (gSpawn rM 3 k) u := fun u hu => by
    rw [upd_ne _ _ hu, upd_ne _ _ hu]
  refine ⟨rX, hl.groups _, ⟨⟨h00, fun u hu1 hu => ?_, fun u hu => ?_, .inr ⟨0, k, Nat.zero_le _,
    by omega, by show (upd G 0 (gJoins rM 0 k) 0).2 = _; rw [upd_self]; rfl, hsz, rfl,
    fun u => ?_⟩⟩, hU.io, fun u hu => ?_, ?_, hU.rest, fun v hv => ?_⟩⟩
  · obtain ⟨jn, gt, hr, hj, hk'⟩ := hrec u hu1 hu
    have hu0 : u ≠ 0 := by unfold ThreadId at *; omega
    exact ⟨jn, gt, hr, by show _ → (upd G 0 _ u).2 = _; rw [hX u hu0]; exact hj,
      by show (∃ d, (upd G 0 _ u).2 = _) ∨ (upd G 0 _ u).2 = _; rw [hX u hu0]; exact hk'⟩
  · show (upd G 0 _ u).2 = _
    rw [hX u (by rw [hsz] at hu; unfold ThreadId at *; omega)]; exact hnone u hu
  · have := hjb u
    constructor
    · intro h; change joinedB m u = true at h; rw [this] at h; cases h
    · intro h; exfalso; unfold ThreadId at *; omega
  · rw [hX u hu]; exact hU.parts u hu
  · rw [upd_self]; have := hU.main; rw [upd_self] at this; exact this
  · change joinedB m v = true at hv; rw [hjb v] at hv; cases hv

/-- The join of task `i + 1 ≤ k` is possible: `main` spawned it, did not join it, and the group no
longer records it (a deferred task is released). -/
theorem join_ok {G : ThreadId → Gh} {m : Mem} {i k : Nat} (hik : i < k) (hi : proto.inv G m)
    (hg : (G 0).2 = .joins i k) :
    i + 1 < m.threads.size ∧ ∃ m', ((Thread.join (i + 1)).run { m with current := 0 }).run =
      some (.ok ((), m')) := by
  obtain ⟨rX, -, hU⟩ := hi
  obtain ⟨-, hrec, -, hph⟩ := hU.shape
  obtain ⟨j, k', -, -, h0, -⟩ | ⟨i', k', -, -, h0, hsz, hgr, hjb⟩ := hph
  · exfalso; change (G 0).2 = _ at h0; rw [hg] at h0; cases h0
  obtain ⟨e1, e2⟩ : i' = i ∧ k' = k := by
    change (G 0).2 = _ at h0; rw [hg] at h0; cases h0; exact ⟨rfl, rfl⟩
  subst i' k'
  have hlt : i + 1 < m.threads.size := by rw [hsz]; omega
  obtain ⟨jn, gt, hr, -, -⟩ := hrec (i + 1) (by omega) hlt
  have hjn : jn = false := by
    have := hjb (i + 1)
    unfold joinedB at this; rw [hr] at this
    cases jn
    · rfl
    · simp at this; exfalso; unfold ThreadId at *; omega
  subst hjn
  exact ⟨hlt, join_run (m := { m with current := 0 }) hr rfl rfl (.inr (by simp [hgr]))⟩

/-- `main`'s join of task `i + 1`: it takes the task's (empty) part. -/
theorem inv_join {G₁ : ThreadId → Gh} {m m' : Mem} {rM : Res} {i k : Nat} (hik : i < k)
    (hi : proto.inv G₁ m) (hg : G₁ 0 = gJoins rM i k) (hfin : proto.fin (G₁ (i + 1)))
    (hj : ((Thread.join (i + 1)).run { m with current := 0 }).run = some (.ok ((), m'))) :
    m'.current = 0 ∧ proto.inv (upd G₁ 0 (gJoins rM (i + 1) k)) m' := by
  obtain ⟨rX, hiL, hU⟩ := hi
  obtain ⟨h00, hrec, hnone, hph⟩ := hU.shape
  have hX0 : (G₁ 0).2 = .joins i k := by rw [hg]; rfl
  obtain ⟨j, k', -, -, h0, -⟩ | ⟨i', k', -, hk3, h0, hsz, hgr, hjb⟩ := hph
  · exfalso; change (G₁ 0).2 = _ at h0; rw [hX0] at h0; cases h0
  obtain ⟨e1, e2⟩ : i' = i ∧ k' = k := by
    change (G₁ 0).2 = _ at h0; rw [hX0] at h0; cases h0; exact ⟨rfl, rfl⟩
  subst i k
  have hu0 : (i' + 1 : Nat) ≠ 0 := by omega
  have hown : L.own G₁ m (i' + 1) = rnil := by
    have : joinedB m (i' + 1) = false := by
      have := hjb (i' + 1); cases e : joinedB m (i' + 1)
      · rfl
      · rw [e] at this; have := this.mp rfl; exfalso; unfold ThreadId at *; omega
    rw [FLock.own_live (L := L) this]
    show rsum (G₁ (i' + 1)).1.part (L.held (G₁ (i' + 1))) = _
    rw [hU.parts _ hu0, hiL.idle _ (by rw [show L.ph (G₁ (i' + 1)) = .gone from hfin.1]; decide),
      rnil_rsum]
  have hl := hiL.join (t := 0) (u := i' + 1) (g := gJoins rM (i' + 1) k') hu0 hu0
    (by rw [hg]; rfl) hfin.1 hj (by
      show rM = rsum (G₁ 0).1.part _
      rw [hown, rsum_rnil, hg]; rfl) rfl rfl fun r hR => R_main hR (by rw [hg]; rfl)
  obtain ⟨rec, hrec', hjf, hm'⟩ := Proto.join_eq hj
  have hcs : m.clocks.size = k' + 1 := by rw [hiL.w.csize, hsz]
  have hth : m'.threads = m.threads.set! (i' + 1) { rec with joined := true } := by rw [hm']
  have hsz' : m'.threads.size = k' + 1 := by rw [hth, Array.size_set!, hsz]
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
    · subst hu; simp [hsz, show i' + 1 < k' + 1 by omega]
    · simp [hu, Ne.symm hu]
  obtain ⟨gt₀, hrec_r⟩ : ∃ gt, rec = { spawner := 0, joined := false, gated := gt } := by
    obtain ⟨jn, gt, hr, -, -⟩ := hrec (i' + 1) (by omega) (by rw [hsz]; omega)
    simp only at hrec'
    rw [hr] at hrec'; cases hrec'; simp only at hjf; subst hjf; exact ⟨gt, rfl⟩
  have hX : ∀ u, u ≠ 0 → upd G₁ 0 (gJoins rM (i' + 1) k') u = G₁ u := fun u hu => by
    rw [upd_ne _ _ hu]
  refine ⟨by rw [hm'], rX, hl, ⟨⟨?_, fun u hu1 hu => ?_, fun u hu => ?_, .inr ⟨i' + 1, k', by omega,
    hk3, by show (upd G₁ 0 _ 0).2 = _; rw [upd_self]; rfl, hsz', by rw [hm']; exact hgr,
    fun u => ?_⟩⟩, ?_, fun u hu => ?_, ?_, hU.rest, fun v hv => ?_⟩⟩
  · rw [hth, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, if_neg (by omega)]
    exact h00
  · rw [hsz'] at hu
    have hu0' : u ≠ 0 := by unfold ThreadId at *; omega
    obtain ⟨jn, gt, hr, hj, hk⟩ := hrec u hu1 (by rw [hsz]; exact hu)
    dsimp only
    rw [hX u hu0']
    by_cases hui : u = i' + 1
    · subst hui
      refine ⟨true, gt₀, ?_, fun _ => hfin.2, hk⟩
      rw [hth, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, if_pos rfl,
        if_pos (by rw [hsz]; omega), hrec_r]
    · refine ⟨jn, gt, ?_, hj, hk⟩
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
  · refine hU.io.keep (by rw [hsz', hsz]) (fun u _ => ?_) fun e he _ => by rw [hm'] at he; exact he
    by_cases hu0 : u = 0
    · subst hu0; exact hgrow
    · rw [hcv u hu0]; exact VClock.le_refl _
  · rw [hX u hu]; exact hU.parts u hu
  · rw [upd_self]; have := hU.main; rw [hg] at this; exact this
  · rw [hjb' v] at hv
    have hv0 : v ≠ 0 := by
      intro e; subst e; rw [if_neg (Ne.symm hu0)] at hv; simp [joinedB] at hv
    by_cases hvi : v = i' + 1
    · subst hvi
      refine ⟨by rw [upd_ne _ _ hv0]; exact hfin.1, ?_⟩
      rw [hcv _ hv0, hc0]; exact VClock.le_merge_right _ _
    · rw [if_neg hvi] at hv
      obtain ⟨h1, h2⟩ := hU.jle v hv
      refine ⟨by rw [upd_ne _ _ hv0]; exact h1, ?_⟩
      rw [hcv _ hv0]; exact VClock.le_trans h2 hgrow

/-! ## `main`'s asyncs and joins -/

/-- `main` runs the task itself at its `j`-th async: its own increment. -/
theorem eager_spec {σ : Type} {s : σ} {rM : Res} {j k : Nat} (hj : j < 3) (hk : k ≤ j)
    {G₁ : ThreadId → Gh} {m₁ : Mem} {d : Nat}
    (hi₁' : proto.inv (upd G₁ 0 (gSpawn rM j k)) { m₁ with current := 0 }) :
    proto.WP 0 ((callC ((fun a => (do discard (add a) : ConcM Tgt Unit)) cPtr) :
        CM Tgt σ Unit).run s)
      (fun r G' m' d' => r = ((), s) ∧ d' ≤ d ∧ m'.current = 0 ∧
        ∃ k' ≤ j + 1, proto.inv (upd G' 0 (gSpawn rM (j + 1) k')) m') G₁
      { m₁ with current := 0 } d := by
  refine WP.callC ?_
  show proto.WP 0 ((fun _ => ()) <$> add cPtr) _ G₁ _ d
  refine WP.map (WP.mono ?_ (add_spec 0 rM _ _ (incStep_main (k := k) hj) G₁ _ d hi₁' rfl))
  rintro _ G' m' d' ⟨hd', hc', hi'⟩
  exact ⟨rfl, hd', hc', k, by omega, hi'⟩

/-- One `Group.async` by `main` at its `j`-th async (`j < 3`, `k` tasks so far), under every
execution that an environment can pick: a thread (task `k + 1`; on an assignment failure, `main`
runs the task), `main`'s own `add`, or a deferred task (task `k + 1`, gated until the `await`). -/
theorem async_spec {σ : Type} {s : σ} {rM : Res} {j k : Nat} (hj : j < 3) (hk : k ≤ j) (io : Io)
    {G : ThreadId → Gh} {m : Mem} {d : Nat} (hi : proto.inv (upd G 0 (gSpawn rM j k)) m) :
    proto.WP 0 ((groupAsyncWithPolicyC .available gPtr io (Tgt.add cPtr)
        ((fun a => (do discard (add a) : ConcM Tgt Unit)) cPtr) : CM Tgt σ Unit).run s)
      (fun r G' m' d' => r = ((), s) ∧ d' < d ∧ m'.current = 0 ∧
        ∃ k' ≤ j + 1, proto.inv (upd G' 0 (gSpawn rM (j + 1) k')) m') G m d := by
  refine WP.groupAsyncWithPolicyC fun k₁ hk₁ => ⟨gSpawn rM j k, hi, fun G₁ m₁ hg₁ hi₁ c hc3 => ?_⟩
  have hi₁' : proto.inv (upd G₁ 0 (gSpawn rM j k)) { m₁ with current := 0 } := by
    rw [← hg₁, upd_same]; exact inv_cur 0 hi₁ (by rw [hg₁]; exact (by decide : LPh.out ≠ LPh.gone))
  have heager := eager_spec (s := s) (d := k₁) hj hk hi₁'
  unfold groupAsyncOutcomes at hc3
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl
  · -- a thread, or `main` when the assignment fails
    rw [groupAsyncOutcomeC, if_pos rfl]
    refine WP.groupAsyncCFail fun k₂ hk₂ => ⟨gSpawn rM j k, hi₁', fun G₂ m₂ hg₂ hi₂ =>
      ⟨fun _ => ?_, gOut rnil (.task false), ⟨rfl, rfl⟩, fun child m' hf => ?_⟩⟩
    · have hi₂' : proto.inv (upd G₂ 0 (gSpawn rM j k)) { m₂ with current := 0 } := by
        rw [← hg₂, upd_same]
        exact inv_cur 0 hi₂ (by rw [hg₂]; exact (by decide : LPh.out ≠ LPh.gone))
      exact WP.mono (fun r G' m' d' ⟨h1, h2, h3, h4⟩ => ⟨h1, by omega, h3, h4⟩)
        (eager_spec (s := s) (d := k₂) hj hk hi₂')
    · obtain ⟨rfl, hc', hi'⟩ := inv_spawn hj hi₂ hg₂ hf
      exact ⟨rfl, by omega, hc', k + 1, by omega, hi'⟩
  · -- `main` runs the task itself
    rw [groupAsyncOutcomeC, if_neg (by decide), if_pos rfl]
    exact WP.mono (fun r G' m' d' ⟨h1, h2, h3, h4⟩ => ⟨h1, by omega, h3, h4⟩) heager
  · -- a deferred task
    rw [groupAsyncOutcomeC, if_neg (by decide), if_neg (by decide)]
    refine WP.groupDeferC fun k₂ hk₂ => ⟨gSpawn rM j k, hi₁', fun G₂ m₂ hg₂ hi₂ =>
      ⟨gOut rnil (.task false), ⟨rfl, rfl⟩, fun _ => ⟨rfl, .inr rfl⟩, fun child m' hf => ?_⟩⟩
    obtain ⟨rfl, hc', hi'⟩ := inv_spawn hj hi₂ hg₂ hf
    exact ⟨rfl, by omega, hc', k + 1, by omega, hi'⟩

/-- The async loop's invariant: `main` did `local10` asyncs. -/
def spawnInv (rM : Res) (s : groupCounterLocals) (G : ThreadId → Gh) (m : Mem) (_ : Nat) : Prop :=
  m.current = 0 ∧ s.local10.toNat ≤ 3 ∧
    ∃ k ≤ s.local10.toNat, proto.inv (upd G 0 (gSpawn rM s.local10.toNat k)) m

/-- The async loop ends after 3 asyncs. -/
def spawnPost (rM : Res) (r : groupCounterExit × groupCounterLocals) (G : ThreadId → Gh) (m : Mem)
    (_ : Nat) : Prop :=
  r.1 = .br12 ∧ m.current = 0 ∧ ∃ k ≤ 3, proto.inv (upd G 0 (gSpawn rM 3 k)) m

theorem loop13_body (rM : Res) (io : Io) (s : groupCounterLocals) (G : ThreadId → Gh) (m : Mem)
    (d : Nat) (h : spawnInv rM s G m d) :
    proto.WP 0 ((groupCounter.loop13 io cPtr gPtr).run s) (fun r G' m' d' =>
      if groupCounter.again13 r.1 then spawnInv rM r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : groupCounterLocals) => 0) s)
      else spawnPost rM r G' m' d') G m d := by
  obtain ⟨hc, hle, k, hk, hi⟩ := h
  unfold groupCounter.loop13
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · rename_i hlt
    have hlt' : s.local10.toNat < 3 := by simpa [lt, BitVec.ult] using hlt
    simp only [StateT.run_bind, bind_assoc, pure_bind]
    refine WP.bind (WP.mono ?_ (async_spec hlt' hk io hi))
    rintro r G' m' d' ⟨rfl, hd', hc', k', hk', hi'⟩
    simp only [StateT.run_pure, pure_bind, StateT.run_bind]
    refine WP.bind (WP.callRC (fun e he =>
      (add_one_noErr (a := s.local10) (by have := s.local10.isLt; omega) e he).elim) fun i23 hadd => ?_)
    have h23 := add_one_ok (a := s.local10) hadd (by have := s.local10.isLt; omega)
    simp only [StateT.run_modify, StateT.run_pure, pure_bind]
    refine WP.pure' ?_
    simp only [groupCounter.again13, ↓reduceIte]
    refine ⟨⟨hc', by simp only; omega, k', by simp only; omega, by simp only; rw [h23]; exact hi'⟩,
      .inl hd'⟩
  · rename_i hge
    have hge' : ¬ s.local10.toNat < 3 := by simpa [lt, BitVec.ult] using hge
    have heq : s.local10.toNat = 3 := by omega
    simp only [StateT.run_pure, pure_bind]
    refine WP.pure' ?_
    simp only [groupCounter.again13, Bool.false_eq_true, ↓reduceIte]
    exact ⟨rfl, hc, k, by omega, heq ▸ hi⟩

/-- `main`'s join of task `i + 1`, at `joins i k`. -/
theorem wp_join {σ : Type} {s : σ} {rM : Res} {i k : Nat} (u : ThreadId) (hu : u = i + 1)
    (hik : i < k) {G : ThreadId → Gh} {m : Mem} {n : Nat} (hi : proto.inv (upd G 0 (gJoins rM i k)) m)
    {Q : Unit × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ k₁, n = k₁ + 1 → ∀ G₁ m', m'.current = 0 →
      proto.inv (upd G₁ 0 (gJoins rM (i + 1) k)) m' → Q ((), s) G₁ m' k₁) :
    proto.WP 0 ((joinC u : CM Tgt σ Unit).run s) Q G m n := by
  subst hu
  refine WP.joinC fun k₁ hk₁ => ⟨gJoins rM i k, hi, fun G₁ m₁ hg₁ hi₁ => ?_⟩
  have hX : (G₁ 0).2 = .joins i k := by rw [hg₁]; rfl
  obtain ⟨hlt, hex⟩ := join_ok hik hi₁ hX
  refine ⟨fun _ => ⟨Nat.succ_pos _, hlt, ⟨rfl, .inl ⟨i, k, rfl⟩⟩, by
    obtain ⟨m', hj⟩ := hex
    exact Proto.join_valid hj⟩, fun hfin => ⟨fun _ => hex, fun m' hj => ?_⟩⟩
  obtain ⟨hc', hi'⟩ := inv_join hik hi₁ hg₁ hfin hj
  exact h k₁ hk₁ G₁ m' hc' hi'

/-- `Group.await`'s joins of the tasks `i + 1 … k`, in order. -/
theorem joins_spec {σ : Type} {s : σ} {rM : Res} {k : Nat} :
    ∀ (n i : Nat), i + n = k → ∀ {G : ThreadId → Gh} {m : Mem} {d : Nat}, m.current = 0 →
      proto.inv (upd G 0 (gJoins rM i k)) m →
      ∀ {Q : PUnit × σ → (ThreadId → Gh) → Mem → Nat → Prop},
      (∀ G' m' d', m'.current = 0 → proto.inv (upd G' 0 (gJoins rM k k)) m' →
        Q (PUnit.unit, s) G' m' d') →
      proto.WP 0 ((forIn (List.range' (i + 1) n) PUnit.unit fun tid (_ : PUnit) =>
        (do joinC tid; pure (ForInStep.yield PUnit.unit) : CM Tgt σ (ForInStep PUnit))).run s)
        Q G m d
  | 0, i, hik, G, m, d, hc, hi, Q, h => by
    simp only [List.range'_zero, List.forIn_nil, StateT.run_pure]
    obtain rfl : i = k := by omega
    exact WP.pure' (h G m d hc hi)
  | n + 1, i, hik, G, m, d, hc, hi, Q, h => by
    rw [List.range'_succ]
    simp only [List.forIn_cons, StateT.run_bind, bind_assoc]
    refine WP.bind (wp_join (i + 1) rfl (by omega) hi fun k₁ _ G₁ m' hc' hi' => ?_)
    simp only [StateT.run_pure, pure_bind]
    exact joins_spec n (i + 1) (by omega) hc' hi' h

/-- After the asyncs the group records the `k` tasks. -/
theorem groups_spawn3 {G : ThreadId → Gh} {m : Mem} {rM : Res} {k : Nat}
    (hi : proto.inv (upd G 0 (gSpawn rM 3 k)) m) : m.groups = grp k := by
  obtain ⟨rX, -, hU⟩ := hi
  obtain ⟨-, -, -, ⟨j, k', -, -, h0, -, hgr, -⟩ | ⟨i, k', -, -, h0, -⟩⟩ := hU.shape
  · change (upd G 0 (gSpawn rM 3 k) 0).2 = _ at h0; rw [upd_self] at h0; cases h0; exact hgr
  · change (upd G 0 (gSpawn rM 3 k) 0).2 = _ at h0; rw [upd_self] at h0; cases h0

/-- `Group.await`'s take of the group's `k` tasks: 1 … k; the group is empty after it. -/
theorem take_run {m : Mem} {k : Nat} (hk : k ≤ 3) (hg : m.groups = grp k) :
    ((Thread.groupTake gPtr).run m).run =
      some (.ok (⟨List.range' 1 k⟩, { m with groups := #[] })) := by
  unfold Thread.groupTake
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hg]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
  · rw [show (grp 0).filter (·.1 != gPtr) = #[] by decide +kernel,
      show ((grp 0).filter (·.1 == gPtr)).map (·.2) = ⟨List.range' 1 0⟩ by decide +kernel]; rfl
  · rw [show (grp 1).filter (·.1 != gPtr) = #[] by decide +kernel,
      show ((grp 1).filter (·.1 == gPtr)).map (·.2) = ⟨List.range' 1 1⟩ by decide +kernel]; rfl
  · rw [show (grp 2).filter (·.1 != gPtr) = #[] by decide +kernel,
      show ((grp 2).filter (·.1 == gPtr)).map (·.2) = ⟨List.range' 1 2⟩ by decide +kernel]; rfl
  · rw [show (grp 3).filter (·.1 != gPtr) = #[] by decide +kernel,
      show ((grp 3).filter (·.1 == gPtr)).map (·.2) = ⟨List.range' 1 3⟩ by decide +kernel]; rfl

/-- After the `k` joins: `main` takes the counter back (`FLock.Inv.take`), which holds 3 (`k`
tasks and `3 - k` of its own increments); every thread is joined, and the tasks' read shares of
`io` are back: `main` owns `io` alone (`ReadShared.reclaim`). -/
theorem inv_final {G : ThreadId → Gh} {m : Mem} {rM : Res} {k : Nat}
    (hi : proto.inv (upd G 0 (gJoins rM k k)) m) :
    ∃ own rX r, FOwned (upd own 0 r) rX m ∧
      ((fun r => r = own 0) ⋆ (up (pts (cPtr.add 20) 4 (BitVec.ofNat 32 3)) ⋆
        fun r => r = L.wordR m)) r ∧
      m.threads.size = k + 1 ∧ joinedAll 0 m ∧ m.BlkOk 0 24 8 .stack ∧ m.BlkOk 1 16 1 .stack ∧
      RegionOwned IoR m (m.clocks[0]!) ∧
      ∀ u < m.threads.size, VClock.le (m.clocks[u]!) (m.clocks[0]!) = true := by
  obtain ⟨rX, hiL, hU⟩ := hi
  obtain ⟨h00, hrec, hnone, hph⟩ := hU.shape
  have hX0 : (upd G 0 (gJoins rM k k) 0).2 = .joins k k := by rw [upd_self]; rfl
  obtain ⟨j, k', -, -, h0, -⟩ | ⟨i, k', -, hk3, h0, hsz, -, hjb⟩ := hph
  · exfalso; change (upd G 0 (gJoins rM k k) 0).2 = _ at h0; rw [hX0] at h0; cases h0
  obtain ⟨e1, e2⟩ : i = k ∧ k' = k := by
    change (upd G 0 (gJoins rM k k) 0).2 = _ at h0; rw [hX0] at h0; cases h0; exact ⟨rfl, rfl⟩
  subst i k'
  have hfinu : ∀ u, 1 ≤ u → u ≤ k → (upd G 0 (gJoins rM k k) u).2 = .fin := by
    intro u h1 h3
    obtain ⟨jn, gt, hr, hj, -⟩ := hrec u h1 (by rw [hsz]; unfold ThreadId at *; omega)
    have hjt := (hjb u).mpr ⟨h1, h3⟩
    unfold joinedB at hjt; rw [hr] at hjt
    have : jn = true := by
      cases jn
      · simp at hjt
      · rfl
    exact hj this
  have hF : L.Free (upd G 0 (gJoins rM k k)) := by
    intro u hu
    by_cases h0 : u = 0
    · subst h0; simp only [FLock.pl] at hu; rw [upd_self] at hu; cases hu
    · by_cases h3 : u ≤ k
      · have := (hU.jle u ((hjb u).mpr ⟨Nat.pos_of_ne_zero h0, h3⟩)).1
        simp only [FLock.pl] at hu
        rw [show L.ph (upd G 0 (gJoins rM k k) u) = (upd G 0 (gJoins rM k k) u).1.ph from rfl,
          this] at hu
        cases hu
      · have := (hiL.w.live u (by rw [hu]; decide)).1
        rw [hsz] at this; unfold ThreadId at *; omega
  have hall : ∀ u < m.threads.size, VClock.le (m.clocks[u]!) (m.clocks[0]!) = true := fun u hu => by
    by_cases h0 : u = 0
    · subst h0; exact VClock.le_refl _
    · rw [hsz] at hu
      exact (hU.jle u ((hjb u).mpr ⟨Nat.pos_of_ne_zero h0, by unfold ThreadId at *; omega⟩)).2
  obtain ⟨rL, hR, hsep, ho⟩ := hiL.take (t := 0) hF
    (by rw [upd_self]; exact (by decide : LPh.out ≠ LPh.gone)) hall
  have hR3 : up (pts (cPtr.add 20) 4 (BitVec.ofNat 32 3)) rL := by
    have : R (fun u => (upd G 0 (gJoins rM k k) u).2) rL := hR
    have hc : ∀ u, 1 ≤ u → u ≤ 3 →
        (upd G 0 (gJoins rM k k) u).2.count = if u ≤ k then 1 else 0 := by
      intro u h1 h3
      split
      · rename_i h; rw [hfinu u h1 h]; rfl
      · rename_i h
        rw [show (upd G 0 (gJoins rM k k) u).2 = .none from
          hnone u (by rw [hsz]; unfold ThreadId at *; omega)]; rfl
    have h3 : sum (fun u => (upd G 0 (gJoins rM k k) u).2) = 3 := by
      show (upd G 0 (gJoins rM k k) 0).2.count + (upd G 0 (gJoins rM k k) 1).2.count +
        (upd G 0 (gJoins rM k k) 2).2.count + (upd G 0 (gJoins rM k k) 3).2.count = 3
      rw [hc 1 (by decide) (by decide), hc 2 (by decide) (by decide),
        hc 3 (by decide) (by decide), upd_self]
      show 3 - k + _ + _ + _ = 3
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> rfl
    unfold R at this; rw [h3] at this; exact this
  refine ⟨_, rX, _, ho, sep_mono_right (fun _ h => sep_mono_left (fun r (h : r = rL) => by
      subst h; exact hR3) h) hsep, hsz,
    fun r hr hsp => ?_, blk0 hiL hU, blk1 hiL hU,
    hU.io.reclaim (by rw [hsz]; exact Nat.succ_pos _) hall, hall⟩
  obtain ⟨u, hu, rfl⟩ := Array.mem_iff_getElem.mp hr
  by_cases hu0 : u = 0
  · subst hu0
    rw [Array.getElem?_eq_getElem hu] at h00
    rw [Option.some.inj h00]
  · obtain ⟨jn, gt, hr', -, -⟩ := hrec u (Nat.pos_of_ne_zero hu0) hu
    have hjt := (hjb u).mpr ⟨Nat.pos_of_ne_zero hu0, by rw [hsz] at hu; unfold ThreadId at *; omega⟩
    unfold joinedB at hjt
    rw [Array.getElem?_eq_getElem hu] at hr' hjt
    simp only [Option.map_some, Option.getD_some, Bool.and_eq_true, bne_iff_ne, ne_eq] at hjt
    exact hjt.2

/-! ## `main` -/

/-- The start: no thread. -/
def G0 : ThreadId → Gh := fun _ => (⟨.gone, rnil, rnil⟩, .none)

theorem enc_io (io : Io) : (Enc.encode io).size = 16 := LawfulEnc.size_encode io

/-- The initial mutex. -/
def mutex0 : Io_Mutex := { state := { raw := Io_Mutex_State.unlocked } }

theorem enc_mutex : Enc.encode mutex0 = Enc.encode (0 : BitVec 32) := by decide +kernel

theorem enc_mutex_size : (Enc.encode mutex0).size = 4 := by
  rw [enc_mutex]; exact LawfulEnc.size_encode _

/-- Before its first spawn: `main` owns the `Counter` (`io`, the mutex `rW`, the counter `rC`)
and its part `rM` (both extents and the `Io.Group`). It gives `io` to the protocol's rest
(`FOwned.give`), and the mutex and the counter to the lock (`FLock.Inv.make`). -/
theorem inv_start {m : Mem} {own : ThreadId → Res} {io : Io} {A A' : Nat} {rIO rM rC rW : Res}
    (ho : FOwned (upd own 0 (rsum (rsum rM (rsum rC rW)) rIO)) rnil m)
    (hown : ∀ u, u ≠ 0 → own u = rnil)
    (hd : FHeap.Disjoint (rsum rM (rsum rC rW)).heap rIO.heap)
    (hdM : FHeap.Disjoint rM.heap (rsum rC rW).heap) (hdCW : FHeap.Disjoint rC.heap rW.heap)
    (hIO : up (bytesAt cPtr A 24 .stack (Enc.encode io)) rIO)
    (hW : up (bytesAt (cPtr.add 16) A 24 .stack (Enc.encode mutex0)) rW)
    (hC : up (bytesAt ((cPtr.add 16).add 4) A 24 .stack (Enc.encode (0 : BitVec 32))) rC)
    (hM : (bext 0 24 .stack ⋆ (bext 1 16 .stack ⋆
      up (bytesAt gPtr A' 16 .stack (Enc.encode group0)))) rM)
    (hA : A % 8 = 0) (hth : m.threads = #[{ spawner := 0, joined := true }])
    (hat : m.atomics = #[]) (hq : m.waiters = #[]) (hgr : m.groups = #[]) :
    proto.inv (upd G0 0 (gSpawn rM 0 0)) m := by
  have h1 : m.threads.size = 1 := by rw [hth]; rfl
  have ht : 0 < m.threads.size := by rw [h1]; decide
  -- the word's block and bytes
  have hown0 : (((up (bytesAt (cPtr.add 16) A 24 .stack (Enc.encode mutex0)) ⋆
      bext 0 24 .stack) ⋆ (bext 1 16 .stack ⋆ (up (bytesAt gPtr A' 16 .stack (Enc.encode group0)) ⋆
        (up (bytesAt ((cPtr.add 16).add 4) A 24 .stack (Enc.encode (0 : BitVec 32))) ⋆
          up (bytesAt cPtr A 24 .stack (Enc.encode io)))))))
      (upd own 0 (rsum (rsum rM (rsum rC rW)) rIO) 0) := by
    rw [upd_self]
    have h : (((bext 0 24 .stack ⋆ (bext 1 16 .stack ⋆
        up (bytesAt gPtr A' 16 .stack (Enc.encode group0)))) ⋆
        (up (bytesAt ((cPtr.add 16).add 4) A 24 .stack (Enc.encode (0 : BitVec 32))) ⋆
          up (bytesAt (cPtr.add 16) A 24 .stack (Enc.encode mutex0)))) ⋆
        up (bytesAt cPtr A 24 .stack (Enc.encode io))) (rsum (rsum rM (rsum rC rW)) rIO) :=
      ⟨_, _, hd, rfl, ⟨_, _, hdM, rfl, hM, _, _, hdCW, rfl, hC, hW⟩, hIO⟩
    have e : (((bext 0 24 .stack ⋆ (bext 1 16 .stack ⋆
        up (bytesAt gPtr A' 16 .stack (Enc.encode group0)))) ⋆
        (up (bytesAt ((cPtr.add 16).add 4) A 24 .stack (Enc.encode (0 : BitVec 32))) ⋆
          up (bytesAt (cPtr.add 16) A 24 .stack (Enc.encode mutex0)))) ⋆
        up (bytesAt cPtr A 24 .stack (Enc.encode io))) =
        ((up (bytesAt (cPtr.add 16) A 24 .stack (Enc.encode mutex0)) ⋆ bext 0 24 .stack) ⋆
        (bext 1 16 .stack ⋆ (up (bytesAt gPtr A' 16 .stack (Enc.encode group0)) ⋆
          (up (bytesAt ((cPtr.add 16).add 4) A 24 .stack (Enc.encode (0 : BitVec 32))) ⋆
            up (bytesAt cPtr A 24 .stack (Enc.encode io)))))) := by ac_rfl
    rw [e] at h; exact h
  obtain ⟨blk, hblk, hl, hA', hS', hK', hx⟩ :=
    ho.bytesOf ht (rfl : (cPtr.add 16).block = some 0) (by rw [enc_mutex_size]; decide) hown0
  have h0 : L.U32 m 0 := by
    show (intOfBytes 32 (curBytes m 0 16 4)).run = _
    unfold curBytes; rw [hblk]
    simp only [Option.map_some, Option.getD_some]
    rw [show (16 : Nat) = (cPtr.add 16).off.toNat from rfl,
      show 4 = (Enc.encode mutex0).size from enc_mutex_size.symm, hx, enc_mutex]
    exact intOfBytes_rmw 0
  -- `io` to the rest
  have ho' := ho.give (t := 0) ht (by rw [upd_self]) hd
  rw [upd_upd] at ho'
  have hGu : ∀ u, u ≠ 0 → upd G0 0 (gSpawn rM 0 0) u = G0 u := fun u h => upd_ne _ _ h
  have hjb : ∀ u, joinedB m u = false := by
    intro u; unfold joinedB
    by_cases hu : u = 0
    · subst hu; rfl
    · have : m.threads.size ≤ u := by rw [h1]; unfold ThreadId at *; omega
      simp [hu, Array.getElem?_eq_none this]
  refine ⟨rsum rIO rnil, FLock.Inv.make (t := 0) (rL := rC) (rW := rW) ho' rfl ht (fun u hu => ?_)
    (by rw [upd_self, upd_self]; rfl) (by rw [upd_self]; exact hdM) hdCW (fun l => ?_) hW.2.1 hW.2.2
    (fun u => ?_) (fun u => ?_) ?_ ⟨blk, hblk, hl, by rw [hS']; decide,
      by show (blk.addr + 16) % 4 = 0; rw [hA']; omega, by rw [hK']; decide,
      by rw [hK']; decide⟩ h0 (by rw [hat]; simp) hq (allLe_of_one h1 (VClock.le_refl _)), ?_⟩
  · rw [upd_ne _ _ hu, hown u hu]
    unfold FLock.own; rw [hGu u hu]; split <;> simp [G0, FLock.prod, rnil_rsum]
  · rw [up_bytesAt_some hW rfl l, enc_mutex_size]
    show _ ↔ l.1 = 0 ∧ 16 ≤ l.2 ∧ l.2 < 16 + 4
    simp [cPtr, Ptr.add]
  · by_cases hu : u = 0
    · subst hu; rw [upd_self]; exact .inl ⟨rfl, ht, rfl⟩
    · rw [hGu u hu]; exact .inr rfl
  · by_cases hu : u = 0
    · subst hu; rw [upd_self]; rfl
    · rw [hGu u hu]; rfl
  · -- the counter holds `0`
    show R _ rC
    have hsum : sum (fun u => (upd G0 0 (gSpawn rM 0 0) u).2) = 0 := by
      show (upd G0 0 (gSpawn rM 0 0) 0).2.count + (upd G0 0 (gSpawn rM 0 0) 1).2.count +
        (upd G0 0 (gSpawn rM 0 0) 2).2.count + (upd G0 0 (gSpawn rM 0 0) 3).2.count = 0
      rw [upd_self, hGu 1 (by decide), hGu 2 (by decide), hGu 3 (by decide)]; rfl
    unfold R; rw [hsum]
    exact ⟨⟨A, 24, .stack, Enc.encode (0 : BitVec 32), by simp [cPtr, Ptr.add]; omega,
      LawfulEnc.size_encode _, LawfulEnc.decode_encode _, hC.1, by decide⟩, hC.2.1, hC.2.2⟩
  · refine ⟨⟨by rw [hth]; rfl, fun u hu1 hu => by rw [h1] at hu; unfold ThreadId at *; omega,
      fun u hu => ?_, .inl ⟨0, 0, Nat.le_refl _, by decide, ?_, h1, by rw [hgr]; simp [grp], hjb⟩⟩,
      fun e he hr => .inr fun u hu => ?_, fun u hu => by rw [hGu u hu]; rfl, ?_, ?_,
      fun v hv => by rw [hjb v] at hv; cases hv⟩
    · show (upd G0 0 (gSpawn rM 0 0) u).2 = _
      rw [hGu u (by rw [h1] at hu; unfold ThreadId at *; omega)]; rfl
    · show (upd G0 0 (gSpawn rM 0 0) 0).2 = _; rw [upd_self]; rfl
    · -- every access to `io` happened before `main`, which owned it
      have : u = 0 := by rw [h1] at hu; unfold ThreadId at *; omega
      subst this
      have hio : rIO.heap (e.block, e.off) ≠ none :=
        (up_bytesAt_some hIO rfl _).mpr ⟨hr.1, by simp [cPtr], by rw [enc_io]; simp [cPtr]; exact hr.2.2⟩
      refine ho.owns 0 ht e he (.inl ⟨e.off, Nat.le_refl _, by have := hr.2.1; omega, ?_⟩)
      rw [upd_self]
      cases e' : (rsum rM (rsum rC rW)).heap (e.block, e.off) <;>
        simp [FHeap.erase, FHeap.union_apply, e', hio]
    · rw [upd_self]; unfold MainPart
      exact sep_mono_right (fun _ h => sep_mono_right (fun _ h' => ⟨A', h'⟩) h) hM
    · rw [rsum_rnil]
      exact ⟨A, _, hA, enc_io io, by cases io; exact LawfulEnc.decode_encode _, hIO⟩

/-- The start memory holds the parts: `main` holds the plain mode (for its stack blocks), no
thread owns anything else, the rest is empty. -/
theorem start (σ : Placement) : FOwned plainOwn rnil { mem0 σ with current := 0 } :=
  FOwned.start0_plain σ

/-- The fresh `Counter`'s bytes in three parts: `io`, the mutex, the counter. -/
theorem split_counter {A : Nat} {r : Res}
    (h : up (bytesAt cPtr A 24 .stack (Array.replicate 24 .undef)) r) :
    (up (bytesAt cPtr A 24 .stack ((Array.replicate 24 Byte.undef).extract 0 16)) ⋆
      (up (bytesAt (cPtr.add 16) A 24 .stack
        (((Array.replicate 24 Byte.undef).extract 16).extract 0 4)) ⋆
       up (bytesAt ((cPtr.add 16).add 4) A 24 .stack
        (((Array.replicate 24 Byte.undef).extract 16).extract 4)))) r :=
  sep_mono_right (fun _ h => up_sep ⟨bytesAt_split h.1 (k := 4) (by simp), h.2⟩)
    (up_sep ⟨bytesAt_split h.1 (k := 16) (by simp), h.2⟩)

/-! The order of `main`'s resources at its stores: the store's bytes next to their block's extent. -/

theorem sep_lcomm {P Q R : FAssn} {r : Res} (h : (P ⋆ (Q ⋆ R)) r) : (Q ⋆ (P ⋆ R)) r :=
  sep_assoc (sep_mono_left (fun _ h => sep_comm h) (sep_assoc' h))

theorem order₁ {I W C b G : FAssn} {r : Res} (h : (((I ⋆ (W ⋆ C)) ⋆ b) ⋆ G) r) :
    ((I ⋆ b) ⋆ ((W ⋆ C) ⋆ G)) r := by
  have e : (((I ⋆ (W ⋆ C)) ⋆ b) ⋆ G) = ((I ⋆ b) ⋆ ((W ⋆ C) ⋆ G)) := by ac_rfl
  rw [e] at h; exact h

theorem order₂ {I W C b G : FAssn} {r : Res} (h : ((I ⋆ b) ⋆ ((W ⋆ C) ⋆ G)) r) :
    ((W ⋆ b) ⋆ (I ⋆ (C ⋆ G))) r := by
  have e : ((I ⋆ b) ⋆ ((W ⋆ C) ⋆ G)) = ((W ⋆ b) ⋆ (I ⋆ (C ⋆ G))) := by ac_rfl
  rw [e] at h; exact h

theorem order₃ {I W C b G : FAssn} {r : Res} (h : ((W ⋆ b) ⋆ (I ⋆ (C ⋆ G))) r) :
    ((C ⋆ b) ⋆ (I ⋆ (W ⋆ G))) r := by
  have e : ((W ⋆ b) ⋆ (I ⋆ (C ⋆ G))) = ((C ⋆ b) ⋆ (I ⋆ (W ⋆ G))) := by ac_rfl
  rw [e] at h; exact h

theorem order₄ {I W C b G : FAssn} {r : Res} (h : ((C ⋆ b) ⋆ (I ⋆ (W ⋆ G))) r) :
    (((C ⋆ b) ⋆ (I ⋆ W)) ⋆ G) r := by
  have e : ((C ⋆ b) ⋆ (I ⋆ (W ⋆ G))) = (((C ⋆ b) ⋆ (I ⋆ W)) ⋆ G) := by ac_rfl
  rw [e] at h; exact h

theorem order₅ {I W C b₀ b₁ G : FAssn} {r : Res} (h : (((C ⋆ b₀) ⋆ (I ⋆ W)) ⋆ (G ⋆ b₁)) r) :
    (((b₀ ⋆ (b₁ ⋆ G)) ⋆ (C ⋆ W)) ⋆ I) r := by
  have e : (((C ⋆ b₀) ⋆ (I ⋆ W)) ⋆ (G ⋆ b₁)) = (((b₀ ⋆ (b₁ ⋆ G)) ⋆ (C ⋆ W)) ⋆ I) := by ac_rfl
  rw [e] at h; exact h

/-- A field pointer of the `Counter` from `main`'s extent of block 0. -/
theorem projOf {m : Mem} {own : ThreadId → Res} {rO : Res} {R : FAssn} (ho : FOwned own rO m)
    (ht : 0 < m.threads.size) (h : (bext 0 24 .stack ⋆ R) (own 0)) {k : Nat} (hk : k ≤ 24) :
    (ptrProject cPtr (·.add k)).run m = pure (cPtr.add k, m) := by
  obtain ⟨blk, hb, -, hsz, -⟩ := ho.blkOf ht h
  exact ptrProject_block_run hb rfl (by decide) (by simp [cPtr, hsz]; omega)

set_option maxHeartbeats 4000000 in
theorem main_spec (σ : Placement) (io : Io) (d : Nat) :
    proto.WP 0 (groupCounter io) QM G0 { mem0 σ with current := 0 } d := by
  unfold groupCounter
  have ht0 : ({ mem0 σ with current := 0 } : Mem).threads = #[{ spawner := 0, joined := true }] :=
    rfl
  -- the `Counter`: block 0
  refine WP.bind (WP.liftMem_fownedS (FTTriple.allocStack 24 8 (by decide) (by decide))
    (start σ) rfl (by rw [ht0]; decide) (by rw [plainOwn_zero]; exact plain_intro)
    fun s1 m₁ r₁ _ hr₁ ho₁ hq₁ hs₁ => ?_)
  obtain ⟨rfl, hm₁e⟩ := alloc_ok hr₁
  obtain ⟨A, b, hq₁⟩ := hq₁
  obtain ⟨⟨hpb, -, hA8⟩, hb₁⟩ := sep_lift.mp hq₁
  obtain rfl : b = 0 := by cases hpb; rfl
  rw [show (⟨some ({ mem0 σ with current := 0 } : Mem).blocks.size, 0⟩ : Ptr) = cPtr from rfl]
    at hb₁ ⊢
  -- the `Io.Group`: block 1, the last stack block (`main` gives up the plain mode)
  refine WP.bind (WP.liftMem_fownedS ((FTTriple.allocStackDrop 16 8 (by decide) (by decide)).frameL
    (R := up (bytesAt cPtr A 24 .stack (Array.replicate 24 .undef)) ⋆ bext 0 24 .stack))
    ho₁ hs₁.current (by rw [hs₁.threads, ht0]; decide)
    (by rw [upd_self]; exact hb₁) fun s8 m₂ r₂ _ hr₂ ho₂ hq₂ hs₂ => ?_)
  simp only [plainOwn, upd_upd] at ho₂
  obtain ⟨rfl, hm₂e⟩ := alloc_ok hr₂
  obtain ⟨A', b', ⟨hpb', -, hA8'⟩, hq₂⟩ := sep_ex_ex_lift hq₂
  have hgp : (⟨some m₁.blocks.size, 0⟩ : Ptr) = gPtr := by rw [hm₁e]; rfl
  rw [hgp] at hpb' hq₂ ⊢
  obtain rfl : b' = 1 := by cases hpb'; rfl
  have hc₂ : m₂.current = 0 := hs₂.current.trans hs₁.current
  have ht₂ : m₂.threads = #[{ spawner := 0, joined := true }] := by
    rw [hs₂.threads, hs₁.threads]; rfl
  -- the `Counter`'s three parts
  have F₂ := order₁ (sep_mono_left (fun _ h => sep_mono_left (fun _ h => split_counter h) h) hq₂)
  have hsI : ((Array.replicate 24 Byte.undef).extract 0 16).size = 16 := by simp
  have hsW : (((Array.replicate 24 Byte.undef).extract 16).extract 0 4).size = 4 := by simp
  have hsC : (((Array.replicate 24 Byte.undef).extract 16).extract 4).size = 4 := by simp
  have hsG : (Array.replicate 16 Byte.undef).size = 16 := by simp
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  -- `io`
  refine WP.bind (WP.callMC_fownedS ((FTTriple.storeAt (p := cPtr) (A := A) (S := 24)
    (K := .stack) (k := 0) (a := 8) io rfl rfl (by decide) (by rw [hsI]; decide)
    (by simp [cPtr]; omega) (by decide)).frame) ho₂ hc₂ (by rw [ht₂]; decide)
    (by rw [upd_self]; exact F₂) fun _ m₃ r₃ _ hr₃ ho₃ F₃ hs₃ => ?_)
  rw [upd_upd] at ho₃
  have hc₃ : m₃.current = 0 := hs₃.current.trans hc₂
  have ht₃ : m₃.threads = #[{ spawner := 0, joined := true }] := hs₃.threads.trans ht₂
  -- `&counter.mutex` (`ptrProject`, MM-3)
  refine WP.bind (WP.callMC_ptrProject (projOf ho₃ (by rw [ht₃]; decide)
    (by rw [upd_self]; exact sep_lcomm (sep_assoc F₃)) (k := 16) (by decide)) ?_)
  dsimp only
  refine WP.bind (WP.callMC_fownedS ((FTTriple.storeAt' (p := cPtr.add 16) (A := A) (S := 24)
    (K := .stack) (k := 0) (a := 4) mutex0 enc_mutex_size rfl rfl (by decide) (by rw [hsW]; decide)
    (by simp [cPtr, Ptr.add]; omega) (by decide)).frame) ho₃ hc₃ (by rw [ht₃]; decide)
    (by rw [upd_self]; exact order₂ F₃) fun _ m₄ r₄ _ hr₄ ho₄ F₄ hs₄ => ?_)
  rw [upd_upd] at ho₄
  have hc₄ : m₄.current = 0 := hs₄.current.trans hc₃
  have ht₄ : m₄.threads = #[{ spawner := 0, joined := true }] := hs₄.threads.trans ht₃
  -- `&counter.count` (`ptrProject`, MM-3)
  refine WP.bind (WP.callMC_ptrProject (projOf ho₄ (by rw [ht₄]; decide)
    (by rw [upd_self]; exact sep_lcomm (sep_assoc F₄)) (k := 20) (by decide)) ?_)
  dsimp only
  refine WP.bind (WP.callMC_fownedS ((FTTriple.storeAt (p := (cPtr.add 16).add 4) (A := A)
    (S := 24) (K := .stack) (k := 0) (a := 4) (0 : BitVec 32) rfl rfl (by decide)
    (by rw [hsC]; decide) (by simp [cPtr, Ptr.add]; omega) (by decide)).frame) ho₄ hc₄
    (by rw [ht₄]; decide) (by rw [upd_self]; exact order₃ F₄) fun _ m₅ r₅ _ hr₅ ho₅ F₅ hs₅ => ?_)
  rw [upd_upd] at ho₅
  have hc₅ : m₅.current = 0 := hs₅.current.trans hc₄
  have ht₅ : m₅.threads = #[{ spawner := 0, joined := true }] := hs₅.threads.trans ht₄
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  -- the `Io.Group`
  refine WP.bind (WP.callMC_fownedS ((FTTriple.storeAt' (p := gPtr) (A := A') (S := 16)
    (K := .stack) (k := 0) (a := 8) group0 enc_group rfl rfl (by decide) (by rw [hsG]; decide)
    (by simp [gPtr]; omega) (by decide)).frameL) ho₅ hc₅ (by rw [ht₅]; decide)
    (by rw [upd_self]; exact order₄ F₅) fun _ m₆ r₆ _ hr₆ ho₆ F₆ hs₆ => ?_)
  rw [upd_upd] at ho₆
  have hc₆ : m₆.current = 0 := hs₆.current.trans hc₅
  have hth₆ : m₆.threads = #[{ spawner := 0, joined := true }] := hs₆.threads.trans ht₅
  have hat₆ : m₆.atomics = #[] := by
    rw [store_atomics hr₆, store_atomics hr₅, store_atomics hr₄, store_atomics hr₃, hm₂e, hm₁e]
    rfl
  have hq₆ : m₆.waiters = #[] := by
    rw [hs₆.waiters, hs₅.waiters, hs₄.waiters, hs₃.waiters, hs₂.waiters, hs₁.waiters]; rfl
  have hgr₆ : m₆.groups = #[] := by
    rw [hs₆.groups, hs₅.groups, hs₄.groups, hs₃.groups, hs₂.groups, hs₁.groups]; rfl
  rw [writeBytes_all (a := (Array.replicate 24 Byte.undef).extract 0 16) (by rw [hsI, enc_io]),
    writeBytes_all (a := ((Array.replicate 24 Byte.undef).extract 16).extract 0 4)
      (by rw [hsW, enc_mutex_size]),
    writeBytes_all (a := ((Array.replicate 24 Byte.undef).extract 16).extract 4)
      (by rw [hsC]; exact LawfulEnc.size_encode _),
    writeBytes_all (a := Array.replicate 16 Byte.undef) (by rw [hsG, enc_group])] at F₆
  obtain ⟨_, rIO, hd, rfl, ⟨rM, _, hdM, rfl, hM, rC, rW, hdCW, rfl, hC, hW⟩, hIO⟩ := order₅ F₆
  have hi₀ := inv_start (own := fun _ => rnil) ho₆ (fun _ _ => rfl) hd hdM hdCW hIO hW hC hM hA8
    hth₆ hat₆ hq₆ hgr₆
  -- the asyncs
  simp only [StateT.run_modify, pure_bind]
  refine WP.bind (WP.mono ?_ (WP.loop _ _ (spawnInv rM) (fun _ => 0) (spawnPost rM)
    (loop13_body rM io) { c := cPtr, g := gPtr, local10 := 0 } G0 m₆ d
    ⟨hc₆, by decide, 0, Nat.le_refl _, by simpa using hi₀⟩))
  rintro ⟨e, s'⟩ G₁ m₇ d₁ ⟨rfl, hc₇, k, hk3, hi₇⟩
  -- `Group.await`: the take of the tasks, then the joins
  simp only [StateT.run_bind]
  unfold groupAwaitC
  simp only [StateT.run_bind]
  have hrun := take_run hk3 (groups_spawn3 hi₇)
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
  simp only [StateT.run_bind]
  refine WP.bind (joins_spec (k := k) (m := { m₇ with groups := #[] }) k 0 (by omega) hc₇ hiA
    fun G₄ m₁₁ d₄ hc₁₁ hi₁₁ => ?_)
  simp only [StateT.run_pure]
  refine WP.pure' ?_
  simp only [StateT.run_bind]
  -- the counter holds 3
  obtain ⟨own, rX, r, ho, hp, hsz, hja, hbk, hb1, hio, hall⟩ := inv_final hi₁₁
  refine WP.bind (WP.callMC_ptrProject (projC hbk (k := 20) (by decide)) ?_)
  dsimp only
  refine WP.bind (WP.liftM_fowned ((FTTriple.load (q := cPtr.add 20) (a := 4)
    (v := BitVec.ofNat 32 3) (by decide)).frame.frameL) ho hc₁₁ (by rw [hsz]; exact Nat.succ_pos _)
    (by rw [upd_self]; exact hp) fun a m₁₂ r' hr ho' hq _ _ => ?_)
  obtain ⟨-, -, -, -, -, ⟨r₃, -, -, -, hq₃, -⟩⟩ := hq
  obtain ⟨rfl, -⟩ := sep_lift.mp hq₃
  obtain ⟨b, blk, o, -, -, -, hm₁₂⟩ := load_ok hr
  simp only [StateT.run_pure]
  refine WP.pure' ?_
  -- the frees
  obtain ⟨blk₀, hblk₀, hl₀, -, -, hkc₀⟩ := hbk
  obtain ⟨blk₁, hblk₁, hl₁, -, -, hkc₁⟩ := hb1
  have hb₁₂ : m₁₂.blocks = m₁₁.blocks := by rw [hm₁₂, Mem.readAt_blocks]
  -- every task is joined: the ends of the blocks race with no access
  have hcl : m₁₂.ClocksLe := by
    rw [hm₁₂]
    exact (Mem.ClocksLe.of_threads ho.csize (by rw [hc₁₁]; exact hall)).readAt _ _ _ _ _
  refine WP.bind (WP.liftMem (fun e he => (free_noErr (by rw [hb₁₂]; exact hblk₁) hl₁
    (hcl.freeRaces _ _) (by rw [hkc₁]; nofun) e he).elim)
    fun _ m₁₃ hfr => ?_)
  obtain ⟨b', blk', hb', -, rfl⟩ := free_ok hfr
  cases hb'
  refine ⟨rfl, ?_⟩
  refine WP.bind (WP.liftMem (fun e he => (free_noErr (b := 0)
    (m := { m₁₂ with blocks := m₁₂.blocks.set! 1 { blk' with live := false } }) (by
    simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]; rw [hb₁₂]; simpa using hblk₀)
    hl₀ (hcl.freeRaces _ _) (by rw [hkc₀]; nofun) e he).elim) fun _ m₁₄ hfr' => ?_)
  obtain ⟨b'', blk'', hb'', hblk'', rfl⟩ := free_ok hfr'
  cases hb''
  refine ⟨rfl, WP.pure' ⟨rfl, fun r hr hsp => ?_, ⟨{ blk'' with live := false }, ?_, rfl⟩, ?_⟩⟩
  · have hth : m₁₂.threads = m₁₁.threads := by rw [hm₁₂, Mem.readAt_threads]
    exact hja r (by simpa [hth] using hr) hsp
  · simp only [Array.set!_eq_setIfInBounds]
    exact Array.getElem?_setIfInBounds_self_of_lt (Array.getElem?_eq_some_iff.mp hblk'').1
  · show RegionOwned IoR m₁₂ (m₁₂.clocks[0]!)
    rw [hm₁₂]
    exact hio.readAt hc₁₁ (by rw [ho.csize, hsz]; exact Nat.succ_pos _) blk b o 4 .read

/-! ## The results -/

/-- **`groupCounter` gives 3 under every schedule** (every oracle `o`, every `fuel`). -/
theorem groupCounter_spec (env : Env) {σ : Placement} {fuel : Nat} {o : Nat → Nat} {v : Except ErrName (BitVec 32)} {m : Mem}
    (io : Io) (h : (Sched.run env dispatch fuel o (groupCounter io) (mem0 σ)).run = some (.ok (v, m))) :
    v = .ok 3 := by
  obtain ⟨_, _, hv, -⟩ := proto.run_sound env (fun _ => rfl) dispatch G0 dispatch_spec
    (fun _ _ _ _ _ hq => hq.2.1) rfl (main_spec σ io) h
  exact hv

/-- **No run of `groupCounter` gives an error**: no data race on the counter, no deadlock at the
futex or at `Group.await`, no panic, under every schedule. -/
theorem groupCounter_safe (env : Env) {σ : Placement} {fuel : Nat} {o : Nat → Nat} {e : Error} (io : Io) :
    e ≠ .stackOverflow → (Sched.run env dispatch fuel o (groupCounter io) (mem0 σ)).run ≠ some (.error e) :=
  proto.run_safe env (fun _ => rfl) dispatch G0 rfl dispatch_spec (fun _ _ _ _ hq => hq.2.1) rfl (main_spec σ io)

/-- One schedule completes: under the oracle that always picks option 0, the `Io.Group` counter returns 3 within
fuel 1000, from `mem0` with the translation's spawn policy. The kernel computes the run, with
each loop cut after 10 iterations (`unroll_sched`, `ZigLean/Conc/Unroll.lean`). -/
theorem groupCounter_completes :
    ∃ σ, Witness.okVal (Sched.run ⟨.any, .available⟩ dispatch 1000 (fun _ => 0) (groupCounter ⟨⟩) (mem0 σ)) = some 3 :=
  ⟨.fresh, by unroll_sched 10⟩

/-- **Join before free, under every schedule.** Three tasks read-share `io` (bytes 0..16 of block
0, `ZigLean/Conc/Share.lean`'s `ReadShared`); `main` frees the block only with every task joined
and every access to `io` happened before it. The run ends right after the frees, which change no
thread, clock or footprint entry, so the final memory gives these facts at the free. -/
theorem groupCounter_reclaim (env : Env) {σ : Placement} {fuel : Nat} {o : Nat → Nat} {v : Except ErrName (BitVec 32)}
    {m : Mem} (io : Io)
    (h : (Sched.run env dispatch fuel o (groupCounter io) (mem0 σ)).run = some (.ok (v, m))) :
    joinedAll 0 m ∧ Reclaimed m := by
  obtain ⟨_, _, -, hq⟩ := proto.run_sound env (fun _ => rfl) dispatch G0 dispatch_spec
    (fun _ _ _ _ _ hq => hq.2.1) rfl (main_spec σ io) h
  exact hq

nonvacuity_witness take_run := ⟨{ groups := grp 3 }, 3, Nat.le_refl 3, rfl, trivial⟩

end Iogroup.GroupCounter
