import Proofs.Sync.Lock
import ZigLean.Witness
import ZigLean.Conc.Word
import ZigLean.Conc.WeakWord
import ZigLean.VersionGate

/-!
# `waitUncancelable` and `post` of the translated `Io.Semaphore`

An `Io.Semaphore` (Zig 0.16.0's std code, translated; the futex under it is the model) is a
permit count (8 bytes at offset `o` of block `b`), an `Io.Mutex` (offset `o + 8`) and an
`Io.Condition` (state at `o + 12`, epoch at `o + 16`). This file gives the specs of its two ops
for every protocol that has the semaphore (`Sem.Fits`): `Sem.wait_spec` (the thread gets one
permit and its resource) and `Sem.post_spec` (the thread gives one back).

- **The mutex** is a lock (`ZigLean/Conc/Lock.lean`) that owns the permit count, whose value is
  `pv` of the protocol's ghost values, and the resource of the free permits (`Res`). `wait` takes a
  part of `Res` to the thread's part (`T`), `post` gives a part back.
- **The condition** (`Sem.Inv`). Its state and epoch are shared words (`ZigLean/Conc/Word.lean`).
  At most one thread waits at the condition (`one`; the protocol shows it at each `wait` with no
  permit): its `waiters += 1` is state write `jr`, and it loaded epoch write `i` with the value `e` (`SPh.reg`). Only a thread with a ghost value
  that the protocol allows (`Sem.wx`) waits there. After
  that the state has at most one more write (`signals += 1`, by a `signal`), and the epoch at most
  one more (`+ 1`, after that signal: `Era`). A thread in the critical code of the condition
  (`SPh.crit`) holds the mutex, so these writes cannot interleave.
- **No deadlock.** The waiter sleeps at the epoch only while it is write `i`. Then a thread in the
  critical code goes on, or no signal came and the permit count is 0 (`PZ`): the protocol shows
  that then a thread goes on (`Fits.live`).
- **The rest of the invariant** (`U`) stays under each step of the semaphore's code (`Sem.Step`,
  `Fits.stable`), and under the two steps that move a resource (hypotheses of the specs).
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Conc.Lock Assn

namespace Sync

/-- Where a thread is in the condition code of an `Io.Semaphore`. -/
inductive SPh where
  | none
  /-- In `Condition.wait`, holding the mutex: it loaded epoch write `i`. -/
  | ld (i : Nat) (e : BitVec 32)
  /-- It did `waiters += 1` (state write `jr`) after it loaded epoch write `i`; `seen`: it
  loaded epoch write `i + 1`. -/
  | reg (i jr : Nat) (seen : Bool) (e : BitVec 32)
  /-- In `signal`, holding the mutex. -/
  | pst
  /-- `signal` did `signals += 1`: before `epoch += 1`. -/
  | inc
  /-- `signal` did `epoch += 1`: before its futex wake. -/
  | wk
  deriving DecidableEq

instance : Inhabited SPh := ⟨.none⟩

/-- The critical code of the condition: the thread holds the mutex. -/
def SPh.crit : SPh → Bool
  | .ld _ _ | .pst | .inc | .wk => true
  | _ => false

/-- The thread waits at the condition, or goes to it. -/
def SPh.waits : SPh → Bool
  | .ld _ _ | .reg _ _ _ _ => true
  | _ => false

/-- The ghost value of a thread: the mutex's part, the place in the condition, and the rest of
the protocol's ghost value. -/
abbrev SGh (X : Type) := LG × (SPh × X)

/-- An `Io.Semaphore` at offset `o` of block `b`: the permit count is `pv` of the ghost values,
and the free permits own `Res`. -/
structure Sem (X : Type) where
  b : BlockId
  o : Nat
  pv : (ThreadId → X) → BitVec 64
  Res : (ThreadId → X) → Assn
  /-- `Res` has no byte of the mutex or of the condition. -/
  res_off : ∀ Y h, Res Y h → ∀ x, o + 8 ≤ x → x < o + 20 → h (b, x) = none
  /-- The ghost values with which a thread can wait at the condition (in `wait`, out of a permit). -/
  wx : X → Prop := fun _ => True
  /-- The ghost values of the threads that run the semaphore's code. -/
  inS : X → Prop := fun _ => True

namespace Sem

variable {X : Type} (S : Sem X)

/-- The semaphore (its permit count). -/
def ptr : Ptr := ⟨some S.b, (S.o : Int)⟩

/-- The protocol's ghost values without the semaphore's part. -/
def xs (Y : ThreadId → SPh × X) : ThreadId → X := fun u => (Y u).2

/-- The mutex's resource: the permit count and the free permits' resource. -/
def R (Y : ThreadId → SPh × X) : Assn := pts S.ptr 8 (S.pv (xs Y)) ∗ S.Res (xs Y)

/-- The mutex: bytes `o + 8 .. o + 12`. -/
abbrev L : Lock (SGh X) := Lock.prod S.b (S.o + 8) S.R

/-- The condition's state and epoch. -/
def WS : Word 32 4 := { b := S.b, o := S.o + 12 }
def WE : Word 32 4 := { b := S.b, o := S.o + 16 }

/-- The newest write of a word. -/
abbrev last (h : Array Word.Entry) : Word.Entry := h[h.size - 1]!

/-- The clock `c` happened before the mutex's holder, before its newest message, or before every
thread. -/
def HBH (G : ThreadId → SGh X) (m : Mem) (c : VClock) : Prop :=
  (∃ u, (G u).1.ph = .holds ∧ VClock.le c (m.clocks[u]!) = true) ∨ S.L.Before m c ∨ AllLe m c

/-- The values of the condition's state: `(0, 0)`, `(1, 0)`, `(1, 1)` (`waiters` low). -/
def SV (v : BitVec 32) : Prop := v = 0 ∨ v = 1 ∨ v = 0x10001

/-- The permit count is 0. -/
def PZ (m : Mem) : Prop := ∃ h, pts S.ptr 8 (0 : BitVec 64) h ∧ h.Sub m.heap

/-- The writes of the condition while thread `u` waits (`SPh.reg i jr sn`). -/
structure Era (G : ThreadId → SGh X) (m : Mem) (u i jr : Nat) (sn : Bool) (e : BitVec 32) : Prop where
  ssz : (S.WS.hist m).size = jr + 1 ∨ (S.WS.hist m).size = jr + 2
  s0 : (S.WS.hist m)[jr]!.Val (1 : BitVec 32)
  s1 : (S.WS.hist m).size = jr + 2 → (S.WS.hist m)[jr + 1]!.Val (0x10001 : BitVec 32)
  esz : (S.WE.hist m).size = i + 1 ∨ ((S.WE.hist m).size = i + 2 ∧ (S.WS.hist m).size = jr + 2 ∧
    VClock.le (S.WS.hist m)[jr + 1]!.clock (S.WE.hist m)[i + 1]!.relClock = true)
  eval : (S.WE.hist m)[i]!.Val e ∧
    ((S.WE.hist m).size = i + 2 → (S.WE.hist m)[i + 1]!.Val (e + 1))
  seen : sn = true → (S.WE.hist m).size = i + 2 ∧
    VClock.le (S.WE.hist m)[i + 1]!.relClock (m.clocks[u]!) = true
  cs : VClock.le (S.WS.hist m)[jr]!.clock (m.clocks[u]!) = true
  ce : VClock.le (S.WE.hist m)[i]!.clock (m.clocks[u]!) = true
  hb : S.HBH G m (S.WS.hist m)[jr]!.clock
  pz : (S.WS.hist m).size = jr + 1 → S.PZ m ∨ ∃ v, (G v).2.1 = .pst
  pend : (S.WS.hist m).size = jr + 2 → (S.WE.hist m).size = i + 1 → ∃ v, (G v).2.1 = .inc

/-- The invariant of the condition (module doc). -/
structure Inv (G : ThreadId → SGh X) (m : Mem) : Prop where
  ws : S.WS.Ok m
  we : S.WE.Ok m
  sv : ∀ k < (S.WS.hist m).size, ∃ v, SV v ∧ (S.WS.hist m)[k]!.Val v
  one : ∀ u v i jr sn e i' jr' sn' e', (G u).2.1 = .reg i jr sn e → (G v).2.1 = .reg i' jr' sn' e' → u = v
  idle : (∀ u i jr sn e, (G u).2.1 ≠ .reg i jr sn e) → (last (S.WS.hist m)).Val (0 : BitVec 32)
  era : ∀ u i jr sn e, (G u).2.1 = .reg i jr sn e → S.Era G m u i jr sn e
  hbE : S.HBH G m (last (S.WE.hist m)).clock
  crit : ∀ u, (G u).2.1.crit = true → (G u).1.ph = .holds
  ld : ∀ u i e, (G u).2.1 = .ld i e → (S.WE.hist m).size = i + 1 ∧ (S.WE.hist m)[i]!.Val e
  inc : ∀ u, (G u).2.1 = .inc → ∀ v i jr sn e, (G v).2.1 = .reg i jr sn e →
    (S.WS.hist m).size = jr + 2 ∧ (S.WE.hist m).size = i + 1 ∧
    VClock.le (S.WS.hist m)[jr + 1]!.clock (m.clocks[u]!) = true
  wk : ∀ u, (G u).2.1 = .wk → ∀ v i jr sn e, (G v).2.1 = .reg i jr sn e → (S.WE.hist m).size = i + 2
  /-- A thread at the epoch's futex waits at the condition, while the epoch is write `i` or a
  thread is at `signal`'s wake. -/
  q : ∀ w ∈ m.waiters, w.2 = S.WE.ptr → ∃ i jr e, (G w.1).2.1 = .reg i jr false e ∧
    ((S.WE.hist m).size = i + 1 ∨ ∃ v, (G v).2.1 = .wk)
  /-- No part has a byte of the condition. -/
  off : ∀ u, ∀ x, S.o + 12 ≤ x → x < S.o + 20 → (G u).1.part (S.b, x) = none

/-- A step of the semaphore's code by thread `t`: it changes only the semaphore's bytes, its
atomic locations and the futex queue at the mutex and the epoch. -/
structure Step (t : ThreadId) (m m' : Mem) : Prop where
  threads : m'.threads = m.threads
  csize : m'.clocks.size = m.clocks.size
  clocks : ∀ u : Nat, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true
  bsize : m'.blocks.size = m.blocks.size
  cells : ∀ l : Zig.Loc, ¬ (l.1 = S.b ∧ S.o ≤ l.2 ∧ l.2 < S.o + 20) → m'.heap l = m.heap l
  fp : ∀ e ∈ m'.footprint, e ∈ m.footprint ∨
    (e.tid = t ∧ e.block = S.b ∧ S.o ≤ e.off ∧ e.off + e.len ≤ S.o + 20)
  waiters : ∀ w ∈ m'.waiters, w.2 ≠ S.L.ptr → w.2 ≠ S.WE.ptr → w ∈ m.waiters
  groups : m'.groups = m.groups
  akeep : ∀ b' o', ¬ (b' = S.b ∧ S.o + 8 ≤ o' ∧ o' < S.o + 20) → ∀ i l,
    (m'.atomics.findIdx? (fun l => l.block == b' && l.off == o') = some i ∧ m'.atomics[i]? = some l) ↔
    (m.atomics.findIdx? (fun l => l.block == b' && l.off == o') = some i ∧ m.atomics[i]? = some l)
  anew : ∀ l ∈ m'.atomics, l ∈ m.atomics ∨ (l.block = S.b ∧ S.o + 8 ≤ l.off ∧ l.off + l.len ≤ S.o + 20)

/-- A protocol with the semaphore `S` (module doc). -/
structure Fits {Tgt : Type} (P : Proto Tgt (SGh X)) (U : (ThreadId → SGh X) → Mem → Prop) :
    Prop where
  inv : ∀ G m, P.inv G m ↔ S.L.Inv G m ∧ S.Inv G m ∧ U G m
  fin : ∀ g, P.fin g → g.1.ph = .gone
  joins : ∀ g, P.joins g → g.1.ph = .out
  /-- A step of the semaphore's code keeps `U`: the thread's place in the mutex and the
  condition changes, its part and the rest of its ghost value stay. -/
  stable : ∀ G m m' t g, U G m → S.Step t m m' → g.2.2 = (G t).2.2 → g.1.part = (G t).1.part →
    (g.2.1.waits = true → (G t).2.1.waits = true ∨ S.wx g.2.2) →
    ((g.1.ph ≠ (G t).1.ph ∨ g.2.1 ≠ (G t).2.1) → S.inS g.2.2) → U (upd G t g) m'
  /-- A step of the holder on its own bytes keeps `U`; its part and the rest of its ghost value
  stay. -/
  own : ∀ G m m' t g hQ, S.L.Inv G m → U G m → StepIn (m.heap.diff (S.L.own G m t)) m m' →
    m'.heap = hQ ∪ m.heap.diff (S.L.own G m t) → Heap.Disjoint hQ (m.heap.diff (S.L.own G m t)) →
    (G t).1.ph = .holds → g.1.ph = .holds → g.2 = (G t).2 → g.1.part = (G t).1.part →
    g.1.part ∪ g.1.held = hQ → U (upd G t g) m'
  /-- A thread that waits at the condition sleeps only at the mutex or the epoch. -/
  waits : ∀ G m w i jr sn e, P.inv G m → w ∈ m.waiters → (G w.1).2.1 = .reg i jr sn e →
    w.2 = S.L.ptr ∨ w.2 = S.WE.ptr
  /-- A thread waits at the condition and the permit count is 0: a thread goes on. -/
  live : ∀ G m r i jr sn e, P.inv G m → (G r).2.1 = .reg i jr sn e → S.PZ m →
    (∀ u < m.threads.size, P.fin (G u) ∨ m.waiters.any (·.1 == u) = true ∨ P.joins (G u)) → False

/-! ## Basic facts -/

variable {S}

theorem ptr_mutex : S.ptr.add 8 = S.L.ptr := by
  simp only [Sem.ptr, Ptr.add, Lock.ptr, Lock.prod]; congr 1
theorem ptr_state : S.ptr.add 12 = S.WS.ptr := by
  simp only [Sem.ptr, Ptr.add, Word.ptr, Sem.WS]; congr 1
theorem ptr_epoch : (S.ptr.add 12).add 4 = S.WE.ptr := by
  simp only [Sem.ptr, Ptr.add, Word.ptr, Sem.WE]; congr 1

/-- The semaphore's 20 bytes are in bounds of its block: a field pointer into them is formed
(`ptrProject`, MM-3). -/
theorem Inv.proj {G : ThreadId → SGh X} {m : Mem} (hs : S.Inv G m) {p : Ptr} {k : Nat}
    (hb : p.block = some S.b) (h0 : (S.o : Int) ≤ p.off) (hk : p.off + k ≤ S.o + 20) :
    (ptrProject p (·.add k)).run m = pure (p.add k, m) := by
  obtain ⟨blk, hblk, -, hsz, -⟩ := hs.we.blk
  simp only [Sem.WE] at hsz
  exact ptrProject_add_run (inBounds_of hb hblk (by omega) (by omega))
    (inBounds_of hb hblk (by simp [Ptr.add]; omega) (by simp [Ptr.add]; omega))

/-- `Inv.proj` from the protocol invariant. -/
theorem Fits.proj (hP : S.Fits P U) {G : ThreadId → SGh X} {m : Mem} (hi : P.inv G m) {p : Ptr}
    {k : Nat} (hb : p.block = some S.b) (h0 : (S.o : Int) ≤ p.off) (hk : p.off + k ≤ S.o + 20) :
    (ptrProject p (·.add k)).run m = pure (p.add k, m) :=
  ((hP.inv G m).mp hi).2.1.proj hb h0 hk

theorem ws_epoch : S.WS.ptr.add 4 = S.WE.ptr := by
  simp only [Ptr.add, Word.ptr, Sem.WS, Sem.WE]; congr 1

/-- The epoch's pointer is formed from the condition's (`&cond.epoch`). -/
theorem Fits.projE (hP : S.Fits P U) {G : ThreadId → SGh X} {m : Mem} (hi : P.inv G m) :
    (ptrProject S.WS.ptr (·.add 4)).run m = pure (S.WE.ptr, m) := by
  rw [← ws_epoch]; exact hP.proj hi rfl (by simp [Word.ptr, Sem.WS]; omega) (by simp [Word.ptr, Sem.WS]; omega)

/-- `projE` before `ptr_state` is rewritten: from the condition's pointer `S.ptr + 12`. -/
theorem Fits.projCE (hP : S.Fits P U) {G : ThreadId → SGh X} {m : Mem} (hi : P.inv G m) :
    (ptrProject (S.ptr.add 12) (·.add 4)).run m = pure ((S.ptr.add 12).add 4, m) :=
  hP.proj hi rfl (by simp [Sem.ptr, Ptr.add]; omega) (by simp [Sem.ptr, Ptr.add]; omega)

/-- A field pointer of the semaphore (`&sem.mutex`, `&sem.cond`) is formed. -/
theorem Fits.projS (hP : S.Fits P U) {G : ThreadId → SGh X} {m : Mem} (hi : P.inv G m) {k : Nat}
    (hk : k ≤ 20) : (ptrProject S.ptr (·.add k)).run m = pure (S.ptr.add k, m) :=
  hP.proj hi rfl (by simp [Sem.ptr]) (by simp [Sem.ptr]; omega)

theorem ptr_ne : S.WE.ptr ≠ S.L.ptr := by
  simp only [Word.ptr, Sem.WE, Lock.ptr, Lock.prod, ne_eq, Ptr.mk.injEq, true_and]; omega

theorem apS : Word.Apart S.L S.WS := .inr (.inl (by simp [Sem.WS, Lock.prod]))
theorem apE : Word.Apart S.L S.WE := .inr (.inl (by simp [Sem.WE, Lock.prod]))
theorem apSE : S.WS.b ≠ S.WE.b ∨ S.WS.o + 4 ≤ S.WE.o ∨ S.WE.o + 4 ≤ S.WS.o :=
  .inr (.inl (by simp [Sem.WS, Sem.WE]))
theorem apES : S.WE.b ≠ S.WS.b ∨ S.WE.o + 4 ≤ S.WS.o ∨ S.WS.o + 4 ≤ S.WE.o :=
  .inr (.inr (by simp [Sem.WS, Sem.WE]))

/-- The bytes of a `pts` at the semaphore: its permit count. -/
theorem pts_cells {v : BitVec 64} {h : Heap} (hp : pts S.ptr 8 v h) {l : Zig.Loc} (hl : h l ≠ none) :
    l.1 = S.b ∧ S.o ≤ l.2 ∧ l.2 < S.o + 8 := by
  obtain ⟨A, Sz, K, bs, -, hs, -, ⟨b, hb, -, hown⟩, -⟩ := hp
  cases hb
  rw [hown] at hl
  split at hl
  · rename_i hc
    refine ⟨hc.1, ?_, ?_⟩
    · have := hc.2.1; simp only [Sem.ptr, Int.toNat_natCast] at this; exact this
    · have := hc.2.2; simp only [Sem.ptr, Int.toNat_natCast] at this
      rw [hs] at this; exact this
  · exact absurd rfl hl

/-- `PZ` stays if the permit count's cells do. -/
theorem PZ.mono {m m' : Mem} (h : S.PZ m)
    (hc : ∀ x, S.o ≤ x → x < S.o + 8 → m'.heap (S.b, x) = m.heap (S.b, x)) : S.PZ m' := by
  obtain ⟨hz, hp, hs⟩ := h
  refine ⟨hz, hp, fun l c hl => ?_⟩
  obtain ⟨hb, h1, h2⟩ := pts_cells hp (l := l) (by rw [hl]; simp)
  obtain ⟨b, x⟩ := l
  simp only at hb h1 h2; subst hb
  rw [hc x h1 h2]; exact hs _ c hl

theorem allLe_keep {m m' : Mem} (hcl : ∀ u : Nat, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (hth : m'.threads.size = m.threads.size) : ∀ c, AllLe m c → AllLe m' c := fun _ h u hu =>
  VClock.le_trans (h u (by omega)) (hcl u)

theorem HBH.mono {G G' : ThreadId → SGh X} {m m' : Mem} {c : VClock} (h : S.HBH G m c)
    (hcl : ∀ u : Nat, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (hh : ∀ u, (G u).1.ph = .holds → (G' u).1.ph = .holds ∨ S.L.Before m' (m.clocks[u]!))
    (hb : ∀ c, S.L.Before m c → S.L.Before m' c) (hA : ∀ c, AllLe m c → AllLe m' c) :
    S.HBH G' m' c := by
  rcases h with ⟨u, hu, hle⟩ | hbf | hal
  · rcases hh u hu with h' | h'
    · exact .inl ⟨u, h', VClock.le_trans hle (hcl u)⟩
    · exact .inr (.inl (before_le h' hle))
  · exact .inr (.inl (hb _ hbf))
  · exact .inr (.inr (hA _ hal))

theorem Era.mono {G G' : ThreadId → SGh X} {m m' : Mem} {u i jr : Nat} {sn : Bool}
    (h : S.Era G m u i jr sn e) (hS : S.WS.hist m' = S.WS.hist m) (hE : S.WE.hist m' = S.WE.hist m)
    (hcl : ∀ u : Nat, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (hhb : ∀ c, S.HBH G m c → S.HBH G' m' c) (hpz : S.PZ m → S.PZ m' ∨ ∃ v, (G' v).2.1 = .pst)
    (hst : ∀ v p, (p = SPh.pst ∨ p = .inc) → (G v).2.1 = p → ∃ v', (G' v').2.1 = p) :
    S.Era G' m' u i jr sn e := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  refine ⟨by rw [hS]; exact h1, by rw [hS]; exact h2, by rw [hS]; exact h3,
    by rw [hS, hE]; exact h4, by rw [hE]; exact h5, fun hs => ?_,
    by rw [hS]; exact VClock.le_trans h7 (hcl u), by rw [hE]; exact VClock.le_trans h8 (hcl u),
    by rw [hS]; exact hhb _ h9, fun hs => ?_, fun hs he => ?_⟩
  · obtain ⟨a, b⟩ := h6 hs; rw [hE]; exact ⟨a, VClock.le_trans b (hcl u)⟩
  · rw [hS] at hs
    rcases h10 hs with h | ⟨v, hv⟩
    · exact hpz h
    · exact .inr (hst v _ (.inl rfl) hv)
  · rw [hS] at hs; rw [hE] at he
    obtain ⟨v, hv⟩ := h11 hs he
    exact hst v _ (.inr rfl) hv

/-! ## Steps of the semaphore's code -/

theorem Step.of_lock {t : ThreadId} {m m' : Mem} (hs : S.L.Step t m m') : S.Step t m m' where
  threads := hs.threads
  csize := hs.csize
  clocks := hs.clocks
  bsize := hs.bsize
  cells l hl := hs.heap fun ⟨h1, h2, h3⟩ => hl ⟨h1, by simp [Lock.prod] at h2; omega,
    by simp [Lock.prod] at h3; omega⟩
  fp e he := by
    rcases hs.fpt e he with h | ⟨ht, -⟩
    · exact .inl h
    · rcases hs.fp e he with h | ⟨hb, ho, hl, -⟩
      · exact .inl h
      · exact .inr ⟨ht, hb, by simp [Lock.prod] at ho; omega, by simp [Lock.prod] at ho; omega⟩
  waiters w hw h _ := (hs.waiters w h).mp hw
  groups := hs.groups
  akeep b' o' hn i l := hs.locs.same b' o' (by
    by_cases hb : b' = S.b
    · exact .inr (by simp only [Lock.prod]; intro e; exact hn ⟨hb, by omega, by omega⟩)
    · exact .inl (by simp only [Lock.prod]; exact hb)) i l
  anew l hl := (hs.locs.new l hl).imp id fun ⟨hb, ho, hk⟩ =>
    ⟨hb, by simp [Lock.prod] at ho; omega, by simp [Lock.prod] at ho hk; omega⟩

/-- An op at the state or the epoch. -/
theorem Step.of_op {W : Word 32 4} (hW : W = S.WS ∨ W = S.WE) {t : ThreadId} {m m' : Mem}
    (hop : W.Op t m m') : S.Step t m m' := by
  have hb : W.b = S.b := by rcases hW with rfl | rfl <;> rfl
  have ho : S.o + 12 ≤ W.o ∧ W.o + 4 ≤ S.o + 20 := by
    rcases hW with rfl | rfl <;> simp [Sem.WS, Sem.WE] <;> omega
  refine ⟨hop.threads, hop.csize, hop.clocks, hop.bsize, fun l hl => hop.cells l ?_,
    fun e he => ?_, fun w hw _ _ => by rw [hop.waiters] at hw; exact hw, hop.groups,
    fun b' o' hn i l => hop.locs.same b' o' ?_ i l, fun l hl => ?_⟩
  · rintro ⟨h1, h2, h3⟩; exact hl ⟨hb ▸ h1, by omega, by omega⟩
  · rcases hop.fpt e he with h | ⟨ht, -⟩
    · exact .inl h
    · rcases hop.fp e he with h | ⟨h1, h2, h3, -⟩
      · exact .inl h
      · exact .inr ⟨ht, hb ▸ h1, by omega, by omega⟩
  · by_cases h : b' = W.b
    · exact .inr (fun e => hn ⟨hb ▸ h, by omega, by omega⟩)
    · exact .inl h
  · rcases hop.locs.new l hl with h | ⟨h1, h2, h3⟩
    · exact .inl h
    · exact .inr ⟨hb ▸ h1, by omega, by omega⟩

/-! ## The mutex's steps keep the condition's invariant -/

/-- A lock step of a thread outside the critical code keeps `Inv`. -/
theorem Inv.lockStep (G : ThreadId → SGh X) (m m' : Mem) (t : ThreadId) (p : LPh) (h : Heap)
    (hok : (G t).2.1.crit = false) (hi : S.Inv G m) (hs : S.L.Step t m m')
    (hrel : S.L.ph (G t) = .holds → p ≠ .holds → S.L.Before m' (m.clocks[t]!)) :
    S.Inv (upd G t (S.L.set (G t) p h)) m' := by
  have hkS := Word.keep_lockStep hs apS
  have hkE := Word.keep_lockStep hs apE
  have hhS := Word.hist_keep hi.ws hkS
  have hhE := Word.hist_keep hi.we hkE
  have hsg : ∀ u, (upd G t (S.L.set (G t) p h) u).2 = (G u).2 := fun u => by
    unfold upd; split
    · rename_i e; subst e; rfl
    · rfl
  have hph : ∀ u, u ≠ t → (upd G t (S.L.set (G t) p h) u).1.ph = (G u).1.ph := fun u hu => by
    rw [upd_ne _ _ hu]
  have hhb : ∀ c, S.HBH G m c → S.HBH (upd G t (S.L.set (G t) p h)) m' c := fun c h' =>
    HBH.mono h' hs.clocks (fun u hu => by
      by_cases hut : u = t
      · subst hut
        by_cases hp : p = .holds
        · subst hp; exact .inl (by rw [upd_self]; rfl)
        · exact .inr (hrel hu hp)
      · exact .inl (by rw [hph u hut]; exact hu)) (fun c => hs.before c) (allLe_keep hs.clocks (by rw [hs.threads]))
  have hpz : S.PZ m → S.PZ m' := fun h' => PZ.mono h' fun x h1 h2 => hs.heap (by
    simp only [Lock.prod, not_and, Nat.not_lt]; intro _ h3; omega)
  refine ⟨hi.ws.keep hkS, hi.we.keep hkE, by rw [hhS]; exact hi.sv,
    fun u v i jr sn e i' jr' sn' e' hu hv => hi.one u v i jr sn e i' jr' sn' e' (by rw [← hsg u]; exact hu)
      (by rw [← hsg v]; exact hv),
    fun hn => by rw [hhS]; exact hi.idle fun u i jr sn => by rw [← hsg u]; exact hn u i jr sn,
    fun u i jr sn e hu => ?_, by rw [hhE]; exact hhb _ hi.hbE, fun u hu => ?_,
    fun u i e hu => by rw [hhE]; exact hi.ld u i e (by rw [← hsg u]; exact hu),
    fun u hu v i jr sn e hv => ?_, fun u hu v i jr sn e hv => ?_, fun w hw he => ?_, fun u => by
      unfold upd; split
      · rename_i e; subst e; exact hi.off _
      · exact hi.off u⟩
  · rw [hsg] at hu
    exact (hi.era u i jr sn e hu).mono hhS hhE hs.clocks hhb (fun h => .inl (hpz h)) fun v p _ hv =>
      ⟨v, by rw [hsg]; exact hv⟩
  · rw [hsg] at hu
    by_cases hut : u = t
    · subst hut; rw [hok] at hu; cases hu
    · rw [hph u hut]; exact hi.crit u hu
  · rw [hsg] at hu hv
    obtain ⟨a, b, c⟩ := hi.inc u hu v i jr sn e hv
    exact ⟨by rw [hhS]; exact a, by rw [hhE]; exact b, by rw [hhS]; exact VClock.le_trans c (hs.clocks u)⟩
  · rw [hsg] at hu hv; rw [hhE]; exact hi.wk u hu v i jr sn e hv
  · have hw' := (hs.waiters w (by rw [he]; exact ptr_ne)).mp hw
    obtain ⟨i, jr, ee, h1, h2⟩ := hi.q w hw' he
    refine ⟨i, jr, ee, by rw [hsg]; exact h1, ?_⟩
    rw [hhE]
    rcases h2 with h2 | ⟨v, hv⟩
    · exact .inl h2
    · exact .inr ⟨v, by rw [hsg]; exact hv⟩

variable {P : Proto Tgt (SGh X)} {U : (ThreadId → SGh X) → Mem → Prop}

/-- The protocol has the mutex: only a thread outside the critical code runs the mutex's code. -/
theorem Fits.lf {Tgt : Type} {P : Proto Tgt (SGh X)} (hP : S.Fits P U) :
    S.L.FitsOn P (fun G m => S.Inv G m ∧ U G m) (fun g => g.2.1.crit = false ∧ S.inS g.2.2) where
  inv G m := hP.inv G m
  fin g h := hP.fin g h
  joins g h := hP.joins g h
  ok_set _ _ _ := Iff.rfl
  stable G m m' t p h hok _ hu hs hrel :=
    ⟨Inv.lockStep G m m' t p h hok.1 hu.1 hs hrel,
      hP.stable G m m' t _ hu.2 (Step.of_lock hs) rfl rfl (fun h => .inl h) (fun _ => hok.2)⟩

/-! ## The protocol's invariant -/

theorem Fits.split (hP : S.Fits P U) {G : ThreadId → SGh X} {m : Mem} (hi : P.inv G m) :
    S.L.Inv G m ∧ S.Inv G m ∧ U G m := (hP.inv G m).mp hi

theorem Fits.pack (hP : S.Fits P U) {G : ThreadId → SGh X} {m : Mem} (h1 : S.L.Inv G m)
    (h2 : S.Inv G m) (h3 : U G m) : P.inv G m := (hP.inv G m).mpr ⟨h1, h2, h3⟩

/-- The same atomic locations, blocks, footprint, threads, clocks and futex queue. -/
theorem Inv.congr {G : ThreadId → SGh X} {m m' : Mem} (hi : S.Inv G m) (ha : m'.atomics = m.atomics)
    (hb : m'.blocks = m.blocks) (hf : m'.footprint = m.footprint) (ht : m'.threads = m.threads)
    (hc : m'.clocks = m.clocks) (hwt : m'.waiters = m.waiters) : S.Inv G m' := by
  have hS : S.WS.hist m' = S.WS.hist m := Word.hist_congr ha hb
  have hE : S.WE.hist m' = S.WE.hist m := Word.hist_congr ha hb
  have hk : ∀ (W : Word 32 4), W.Keep m m' := fun _ =>
    Word.keep_of hb ha hf ht fun u => by rw [hc]; exact VClock.le_refl _
  have hcl : ∀ u : Nat, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true := fun u => by
    rw [hc]; exact VClock.le_refl _
  have hbf : ∀ c, S.L.Before m c → S.L.Before m' c := fun c ⟨i, l, hl, hle⟩ =>
    ⟨i, l, by unfold Lock.Loc; rw [ha]; exact hl, hle⟩
  have hhb : ∀ c, S.HBH G m c → S.HBH G m' c := fun c h =>
    HBH.mono h hcl (fun u hu => .inl hu) hbf (allLe_keep hcl (by rw [ht]))
  have hpz : S.PZ m → S.PZ m' := fun h => PZ.mono h fun x _ _ => by simp only [Mem.heap, hb]
  refine ⟨hi.ws.keep (hk _), hi.we.keep (hk _), by rw [hS]; exact hi.sv, hi.one,
    fun hn => by rw [hS]; exact hi.idle hn, fun u i jr sn e hu => ?_, by rw [hE]; exact hhb _ hi.hbE,
    hi.crit, fun u i e hu => by rw [hE]; exact hi.ld u i e hu, fun u hu v i jr sn e hv => ?_,
    fun u hu v i jr sn e hv => by rw [hE]; exact hi.wk u hu v i jr sn e hv, fun w hw he => ?_, hi.off⟩
  · exact (hi.era u i jr sn e hu).mono hS hE hcl hhb (fun h => .inl (hpz h)) fun v _ _ hv => ⟨v, hv⟩
  · obtain ⟨a, b, c⟩ := hi.inc u hu v i jr sn e hv
    exact ⟨by rw [hS]; exact a, by rw [hE]; exact b, by rw [hS, hc]; exact c⟩
  · rw [hwt] at hw; obtain ⟨i, jr, ee, h1, h2⟩ := hi.q w hw he
    exact ⟨i, jr, ee, h1, by rw [hE]; exact h2⟩

/-- A step that changes only `current` and the woken threads. -/
theorem Step.cur (t : ThreadId) (m : Mem) (c : ThreadId) (wk : Array ThreadId) :
    S.Step t m { m with current := c, woken := wk } :=
  ⟨rfl, rfl, fun _ => VClock.le_refl _, rfl, fun _ _ => rfl, fun _ he => .inl he,
    fun _ hw _ _ => hw, rfl, fun _ _ _ _ _ => Iff.rfl, fun _ hl => .inl hl⟩

theorem Step.refl (t : ThreadId) (m : Mem) : S.Step t m m := by
  have := Step.cur (S := S) t m m.current m.woken
  rwa [show ({ m with current := m.current, woken := m.woken } : Mem) = m from rfl] at this

/-- The protocol's invariant with another `current` and other woken threads. -/
theorem Fits.cur (hP : S.Fits P U) {G : ThreadId → SGh X} {m : Mem} (t c : ThreadId)
    (wk : Array ThreadId) (hi : P.inv G m) : P.inv G { m with current := c, woken := wk } := by
  obtain ⟨hl, hs, hu⟩ := hP.split hi
  refine hP.pack (hl.same c m.seen m.nextMsg wk) (hs.congr rfl rfl rfl rfl rfl rfl) ?_
  have := hP.stable G m _ t (G t) hu (Step.cur t m c wk) rfl rfl (fun h => .inl h)
    (fun h => by rcases h with h | h <;> exact absurd rfl h)
  rwa [upd_same] at this

/-- No thread owns a byte of the condition, and the mutex's resource has none. -/
theorem R_off {Y : ThreadId → SPh × X} {h : Heap} (hR : S.R Y h) {x : Nat} (h1 : S.o + 8 ≤ x)
    (h2 : x < S.o + 20) : h (S.b, x) = none := by
  obtain ⟨hp, hr, -, rfl, hpp, hrr⟩ := hR
  have : hp (S.b, x) = none := by
    cases hc : hp (S.b, x) with
    | none => rfl
    | some c =>
      have := (pts_cells hpp (l := (S.b, x)) (by rw [hc]; simp)).2.2; simp only at this; omega
  simp only [Heap.union_apply, this, Option.none_or]; exact S.res_off _ _ hrr x h1 h2

theorem own_off {G : ThreadId → SGh X} {m : Mem} (hl : S.L.Inv G m) (hs : S.Inv G m) (u : ThreadId)
    {x : Nat} (h1 : S.o + 12 ≤ x) (h2 : x < S.o + 20) : S.L.own G m u (S.b, x) = none := by
  unfold Lock.own; split
  · rfl
  · show ((G u).1.part ∪ (G u).1.held) (S.b, x) = none
    rw [Heap.union_apply, hs.off u x h1 h2]
    by_cases hh : S.L.ph (G u) = .holds
    · exact R_off (hl.res u hh) (by omega) h2
    · rw [show (G u).1.held = S.L.held (G u) from rfl, hl.idle u hh]; rfl

theorem wd_off {W : Word 32 4} (hW : W = S.WS ∨ W = S.WE) {G : ThreadId → SGh X} {m : Mem}
    (hl : S.L.Inv G m) (hs : S.Inv G m) :
    (∀ u, W.Off (S.L.own G m u)) ∧ ∀ hL, S.L.R G hL → W.Off hL := by
  have hb : W.b = S.b := by rcases hW with rfl | rfl <;> rfl
  have ho : S.o + 12 ≤ W.o ∧ W.o + 4 ≤ S.o + 20 := by
    rcases hW with rfl | rfl <;> simp [Sem.WS, Sem.WE] <;> omega
  refine ⟨fun u x h1 h2 => ?_, fun hL hR x h1 h2 => ?_⟩
  · rw [hb]; exact own_off hl hs u (by omega) (by omega)
  · rw [hb]; exact R_off hR (by omega) (by omega)

theorem wd_ok {W : Word 32 4} (hW : W = S.WS ∨ W = S.WE) {G : ThreadId → SGh X} {m : Mem}
    (hs : S.Inv G m) : W.Ok m := by
  rcases hW with rfl | rfl
  · exact hs.ws
  · exact hs.we

theorem wd_ap {W : Word 32 4} (hW : W = S.WS ∨ W = S.WE) : Word.Apart S.L W := by
  rcases hW with rfl | rfl
  · exact apS
  · exact apE

/-- An op at the state or the epoch keeps the mutex's invariant and `U`. -/
theorem Fits.op (hP : S.Fits P U) {W : Word 32 4} (hW : W = S.WS ∨ W = S.WE)
    {G : ThreadId → SGh X} {t : ThreadId} {m m' : Mem} (hi : P.inv G m) (hop : W.Op t m m') :
    S.L.Inv G m' ∧ U G m' := by
  obtain ⟨hl, hs, hu⟩ := hP.split hi
  obtain ⟨ho, hR⟩ := wd_off hW hl hs
  refine ⟨hl.wordOp (wd_ok hW hs) hop (wd_ap hW) ho hR, ?_⟩
  have := hP.stable G m m' t (G t) hu (Step.of_op hW hop) rfl rfl (fun h => .inl h)
    (fun h => by rcases h with h | h <;> exact absurd rfl h)
  rwa [upd_same] at this

theorem op_of_cur {W : Word 32 4} {t : ThreadId} {m₁ m' : Mem}
    (hop : W.Op t { m₁ with current := t } m') : W.Op t m₁ m' :=
  ⟨hop.current, hop.threads, hop.waiters, hop.woken, hop.groups, hop.csize, hop.others,
    hop.mine, hop.bsize, hop.cells, hop.fp, ⟨hop.locs.new, hop.locs.same⟩, hop.fpt⟩

/-! ## The ops at the condition's words -/

variable {σ : Type}

theorem alive (hP : S.Fits P U) {G : ThreadId → SGh X} {m : Mem} {t : ThreadId} {g : SGh X}
    (hi : P.inv G m) (hg : G t = g) (hgone : g.1.ph ≠ .gone) : t < m.threads.size :=
  ((hP.split hi).1.live t (by rw [hg]; exact hgone)).1

theorem hcs (hP : S.Fits P U) {G : ThreadId → SGh X} {m : Mem} (hi : P.inv G m) :
    m.clocks.size = m.threads.size := (hP.split hi).1.own.csize

/-- An atomic load of a `u32` at the state or the epoch, by thread `t` (`g`). -/
theorem wp_load (hP : S.Fits P U) {W : Word 32 4} (hW : W = S.WS ∨ W = S.WE) {s : σ}
    {t : ThreadId} {G : ThreadId → SGh X} {m : Mem} {n : Nat} {g : SGh X} {ord : AtomicOrder}
    (hgone : g.1.ph ≠ .gone) (hi : P.inv (upd G t g) m)
    {Q : BitVec 32 × σ → (ThreadId → SGh X) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m₁ m' v j, G₁ t = g → P.inv G₁ m₁ →
      j < (W.hist m₁).size → (W.hist m₁)[j]!.Val v → Word.Floor (W.hist m₁) (m₁.clocks[t]!) j →
      (ord.isAcq = true → VClock.le (W.hist m₁)[j]!.relClock (m'.clocks[t]!) = true) →
      W.hist m' = W.hist m₁ → W.Ok m' → W.Op t m₁ m' → S.L.Inv G₁ m' → U G₁ m' →
      Q (v, s) G₁ m' k) :
    P.WP t ((atomicLoadC (n := 32) ord 4 W.ptr : CM Tgt σ (BitVec 32)).run s) Q G m n := by
  unfold atomicLoadC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ c hcr => ?_⟩)
  have hic := hP.cur t t m₁.woken hi₁
  have htl : t < m₁.threads.size := alive hP hi₁ hg₁ hgone
  have hwc := wd_ok hW (hP.split hic).2.1
  refine WP.callMC (fun e he => (hwc.load_noErr htl (hcs hP hic) hcr e he).elim) fun v m' hr => ?_
  obtain ⟨j, hj, hv, hfl, hacq, hh, hw', hop⟩ := hwc.load rfl htl (hcs hP hic) hr
  have hh₁ : W.hist { m₁ with current := t } = W.hist m₁ := Word.hist_congr rfl rfl
  rw [hh₁] at hj hv hfl hacq hh
  obtain ⟨hl', hu'⟩ := hP.op hW hic hop
  exact ⟨by rw [hop.threads], h k hk G₁ m₁ m' v j hg₁ hi₁ hj hv hfl hacq hh hw'
    (op_of_cur hop) hl' hu'⟩

/-- An atomic load with a decode (`atomicLoadAsC`) at the state, by thread `t` (`g`). -/
theorem wp_loadAs {α : Type} [Packed α 32] (hP : S.Fits P U) {W : Word 32 4}
    (hW : W = S.WS ∨ W = S.WE) {s : σ} {t : ThreadId} {G : ThreadId → SGh X} {m : Mem} {n : Nat}
    {g : SGh X} {ord : AtomicOrder} (hgone : g.1.ph ≠ .gone) (hi : P.inv (upd G t g) m)
    (hdec : ∀ b, ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r))
    {Q : α × σ → (ThreadId → SGh X) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m₁ m' b r j, G₁ t = g → P.inv G₁ m₁ →
      (Packed.ofBits? (α := α) b).run = some (.ok r) →
      j < (W.hist m₁).size → (W.hist m₁)[j]!.Val b → Word.Floor (W.hist m₁) (m₁.clocks[t]!) j →
      W.hist m' = W.hist m₁ → W.Ok m' → W.Op t m₁ m' → S.L.Inv G₁ m' → U G₁ m' →
      Q (r, s) G₁ m' k) :
    P.WP t ((atomicLoadAsC α ord 4 W.ptr : CM Tgt σ α).run s) Q G m n := by
  unfold atomicLoadAsC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ c hcr => ?_⟩)
  have hic := hP.cur t t m₁.woken hi₁
  have htl : t < m₁.threads.size := alive hP hi₁ hg₁ hgone
  have hwc := wd_ok hW (hP.split hic).2.1
  refine WP.callMC (fun e he => (atomicLoadAs_noErr (hwc.load_noErr htl (hcs hP hic) hcr)
    (fun b _ _ => hdec b) e he).elim) fun r m' hr => ?_
  obtain ⟨b, hb, hd⟩ := atomicLoadAs_ok hr
  obtain ⟨j, hj, hv, hfl, -, hh, hw', hop⟩ := hwc.load rfl htl (hcs hP hic) hb
  have hh₁ : W.hist { m₁ with current := t } = W.hist m₁ := Word.hist_congr rfl rfl
  rw [hh₁] at hj hv hfl hh
  obtain ⟨hl', hu'⟩ := hP.op hW hic hop
  exact ⟨by rw [hop.threads], h k hk G₁ m₁ m' b r j hg₁ hi₁ hd hj hv hfl hh hw'
    (op_of_cur hop) hl' hu'⟩

/-- An RMW of a `u32` (`atomicRmwC`) at the epoch, by thread `t` (`g`). -/
theorem wp_rmw (hP : S.Fits P U) {W : Word 32 4} (hW : W = S.WS ∨ W = S.WE) {s : σ}
    {t : ThreadId} {G : ThreadId → SGh X} {m : Mem} {n : Nat} {g : SGh X} {op : RmwOp}
    {signed : Bool} {ord : AtomicOrder} {v : BitVec 32} (hgone : g.1.ph ≠ .gone)
    (hi : P.inv (upd G t g) m) {Q : BitVec 32 × σ → (ThreadId → SGh X) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m₁ m' old, G₁ t = g → P.inv G₁ m₁ →
      (last (W.hist m₁)).Val old → W.Holds m' (op.apply signed old v) →
      W.hist m' = (W.hist m₁).push
        (Word.rmwEnt m' t ord (last (W.hist m₁)) (op.apply signed old v)) →
      W.Ok m' → W.Op t m₁ m' → S.L.Inv G₁ m' → U G₁ m' → Q (old, s) G₁ m' k) :
    P.WP t ((atomicRmwC op signed ord 4 W.ptr v : CM Tgt σ (BitVec 32)).run s) Q G m n := by
  unfold atomicRmwC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ c hcr => ?_⟩)
  have hic := hP.cur t t m₁.woken hi₁
  have htl : t < m₁.threads.size := alive hP hi₁ hg₁ hgone
  have hwc := wd_ok hW (hP.split hic).2.1
  refine WP.callMC (fun e he => (hwc.rmw_noErr htl (hcs hP hic) hcr e he).elim)
    fun old m' hr => ?_
  obtain ⟨hv, hw', hop, hU, hh, -⟩ := hwc.rmw rfl htl (hcs hP hic) hr
  have hh₁ : W.hist { m₁ with current := t } = W.hist m₁ := Word.hist_congr rfl rfl
  rw [hh₁] at hv hh
  obtain ⟨hl', hu'⟩ := hP.op hW hic hop
  exact ⟨by rw [hop.threads], h k hk G₁ m₁ m' old hg₁ hi₁ hv hU hh hw'
    (op_of_cur hop) hl' hu'⟩

/-- An RMW with a decode (`atomicRmwAsC`) at the state, by thread `t` (`g`). -/
theorem wp_rmwAs {α : Type} [Packed α 32] (hP : S.Fits P U) {W : Word 32 4}
    (hW : W = S.WS ∨ W = S.WE) {s : σ} {t : ThreadId} {G : ThreadId → SGh X} {m : Mem} {n : Nat}
    {g : SGh X} {op : RmwOp} {ord : AtomicOrder} {v : α} (hgone : g.1.ph ≠ .gone)
    (hi : P.inv (upd G t g) m) (hdec : ∀ b, ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r))
    {Q : α × σ → (ThreadId → SGh X) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m₁ m' old r, G₁ t = g → P.inv G₁ m₁ →
      (Packed.ofBits? (α := α) old).run = some (.ok r) →
      (last (W.hist m₁)).Val old → W.Holds m' (op.apply false old (Packed.toBits v)) →
      W.hist m' = (W.hist m₁).push
        (Word.rmwEnt m' t ord (last (W.hist m₁)) (op.apply false old (Packed.toBits v))) →
      W.Ok m' → W.Op t m₁ m' → S.L.Inv G₁ m' → U G₁ m' → Q (r, s) G₁ m' k) :
    P.WP t ((atomicRmwAsC op ord 4 W.ptr v : CM Tgt σ α).run s) Q G m n := by
  unfold atomicRmwAsC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ c hcr => ?_⟩)
  have hic := hP.cur t t m₁.woken hi₁
  have htl : t < m₁.threads.size := alive hP hi₁ hg₁ hgone
  have hwc := wd_ok hW (hP.split hic).2.1
  have hh₁ : W.hist { m₁ with current := t } = W.hist m₁ := Word.hist_congr rfl rfl
  refine WP.callMC (fun e he => (atomicRmwAs_noErr (hwc.rmw_noErr htl (hcs hP hic) hcr)
    (fun b _ _ => hdec b) e he).elim) fun r m' hr => ?_
  obtain ⟨old, hb, hd⟩ := atomicRmwAs_ok hr
  obtain ⟨hv, hw', hop, hU, hh, -⟩ := hwc.rmw rfl htl (hcs hP hic) hb
  rw [hh₁] at hv hh
  obtain ⟨hl', hu'⟩ := hP.op hW hic hop
  exact ⟨by rw [hop.threads], h k hk G₁ m₁ m' old r hg₁ hi₁ hd hv hU hh hw'
    (op_of_cur hop) hl' hu'⟩

/-- A `cmpxchg` with a decode (`cmpxchgAsC`) at the state, by thread `t` (`g`): on success an RMW
of the newest write, which holds `exp`; on failure a read of write `j`. -/
theorem wp_casAs {α : Type} [Packed α 32] (hP : S.Fits P U) {W : Word 32 4}
    (hW : W = S.WS ∨ W = S.WE) {s : σ} {t : ThreadId} {G : ThreadId → SGh X} {m : Mem} {n : Nat}
    {g : SGh X} {succ fail : AtomicOrder} {exp new : α} (hgone : g.1.ph ≠ .gone)
    (hi : P.inv (upd G t g) m) (hdec : ∀ b, ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r))
    {Q : Option α × σ → (ThreadId → SGh X) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m₁ m', G₁ t = g → P.inv G₁ m₁ → W.Ok m' → W.Op t m₁ m' →
      S.L.Inv G₁ m' → U G₁ m' →
      ((last (W.hist m₁)).Val (Packed.toBits exp) → W.Holds m' (Packed.toBits new) →
        W.hist m' = (W.hist m₁).push (Word.rmwEnt m' t succ (last (W.hist m₁)) (Packed.toBits new)) →
        (succ.isAcq = true → VClock.le (last (W.hist m₁)).relClock (m'.clocks[t]!) = true) →
        Q (none, s) G₁ m' k) ∧
      (∀ j b r, b ≠ Packed.toBits exp → (Packed.ofBits? (α := α) b).run = some (.ok r) →
        j < (W.hist m₁).size → (W.hist m₁)[j]!.Val b → Word.Floor (W.hist m₁) (m₁.clocks[t]!) j →
        W.hist m' = W.hist m₁ → Q (some r, s) G₁ m' k)) :
    P.WP t ((cmpxchgAsC succ fail 4 W.ptr exp new : CM Tgt σ (Option α)).run s) Q G m n := by
  unfold cmpxchgAsC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ c hcr => ?_⟩)
  have hic := hP.cur t t m₁.woken hi₁
  have htl : t < m₁.threads.size := alive hP hi₁ hg₁ hgone
  have hwc := wd_ok hW (hP.split hic).2.1
  have hh₁ : W.hist { m₁ with current := t } = W.hist m₁ := Word.hist_congr rfl rfl
  refine WP.callMC (fun e he => (cmpxchgAs_noErr (hwc.cas_noErr (fail := fail)
    (new := Packed.toBits new) htl (hcs hP hic) hcr) (fun b _ _ => hdec b) e he).elim)
    fun r m' hr => ?_
  rcases cmpxchgAs_ok hr with ⟨rfl, ho⟩ | ⟨b, v, rfl, ho, hd⟩
  · obtain ⟨hw', hop, ⟨-, hv, hU, hh, hacq⟩ | ⟨j, old, he, -⟩⟩ := hwc.cas rfl htl (hcs hP hic) ho
    · rw [hh₁] at hv hh hacq
      obtain ⟨hl', hu'⟩ := hP.op hW hic hop
      exact ⟨by rw [hop.threads], (h k hk G₁ m₁ m' hg₁ hi₁ hw' (op_of_cur hop)
        hl' hu').1 hv hU hh hacq⟩
    · cases he
  · obtain ⟨hw', hop, ⟨he, -⟩ | ⟨j, old, he, hne, hj, hv, hfl, -, hh⟩⟩ :=
      hwc.cas rfl htl (hcs hP hic) ho
    · cases he
    · cases he
      rw [hh₁] at hj hv hfl hh
      obtain ⟨hl', hu'⟩ := hP.op hW hic hop
      exact ⟨by rw [hop.threads], (h k hk G₁ m₁ m' hg₁ hi₁ hw' (op_of_cur hop)
        hl' hu').2 j b v hne hd hj hv hfl hh⟩

/-- A weak `cmpxchg` at the condition state: failure may read the expected value.
The history and floor guarantees still let either condition loop retry. -/
theorem wp_weakCasAs {α : Type} [Packed α 32] (hP : S.Fits P U) {W : Word 32 4}
    (hW : W = S.WS ∨ W = S.WE) {s : σ} {t : ThreadId} {G : ThreadId → SGh X} {m : Mem} {n : Nat}
    {g : SGh X} {succ fail : AtomicOrder} {exp new : α} (hgone : g.1.ph ≠ .gone)
    (hi : P.inv (upd G t g) m) (hdec : ∀ b, ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r))
    {Q : Option α × σ → (ThreadId → SGh X) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m₁ m', G₁ t = g → P.inv G₁ m₁ → W.Ok m' → W.Op t m₁ m' →
      S.L.Inv G₁ m' → U G₁ m' →
      ((last (W.hist m₁)).Val (Packed.toBits exp) → W.Holds m' (Packed.toBits new) →
        W.hist m' = (W.hist m₁).push (Word.rmwEnt m' t succ (last (W.hist m₁)) (Packed.toBits new)) →
        (succ.isAcq = true → VClock.le (last (W.hist m₁)).relClock (m'.clocks[t]!) = true) →
        Q (none, s) G₁ m' k) ∧
      (∀ j b r, (Packed.ofBits? (α := α) b).run = some (.ok r) →
        j < (W.hist m₁).size → (W.hist m₁)[j]!.Val b → Word.Floor (W.hist m₁) (m₁.clocks[t]!) j →
        W.hist m' = W.hist m₁ → Q (some r, s) G₁ m' k)) :
    P.WP t ((cmpxchgWeakAsC succ fail 4 W.ptr exp new : CM Tgt σ (Option α)).run s) Q G m n := by
  unfold cmpxchgWeakAsC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ c hcr => ?_⟩)
  have hic := hP.cur t t m₁.woken hi₁
  have htl : t < m₁.threads.size := alive hP hi₁ hg₁ hgone
  have hwc := wd_ok hW (hP.split hic).2.1
  have hh₁ : W.hist { m₁ with current := t } = W.hist m₁ := Word.hist_congr rfl rfl
  refine WP.callMC (fun e he => (cmpxchgWeakAs_noErr (hwc.weakCas_noErr (fail := fail)
    (new := Packed.toBits new) htl (hcs hP hic) hcr) (fun b _ _ => hdec b) e he).elim)
    fun r m' hr => ?_
  rcases cmpxchgWeakAs_ok hr with ⟨rfl, ho⟩ | ⟨b, v, rfl, ho, hd⟩
  · obtain ⟨hw', hop, ⟨-, hv, hU, hh, hacq⟩ | ⟨j, old, he, -⟩⟩ := hwc.weakCas rfl htl (hcs hP hic) ho
    · rw [hh₁] at hv hh hacq
      obtain ⟨hl', hu'⟩ := hP.op hW hic hop
      exact ⟨by rw [hop.threads], (h k hk G₁ m₁ m' hg₁ hi₁ hw' (op_of_cur hop)
        hl' hu').1 hv hU hh hacq⟩
    · cases he
  · obtain ⟨hw', hop, ⟨he, -⟩ | ⟨j, old, he, hj, hv, hfl, -, hh⟩⟩ :=
      hwc.weakCas rfl htl (hcs hP hic) ho
    · cases he
    · cases he
      rw [hh₁] at hj hv hfl hh
      obtain ⟨hl', hu'⟩ := hP.op hW hic hop
      exact ⟨by rw [hop.threads], (h k hk G₁ m₁ m' hg₁ hi₁ hw' (op_of_cur hop)
        hl' hu').2 j b v hd hj hv hfl hh⟩

/-! ## Steps that keep the condition's invariant -/

theorem sph_upd (G : ThreadId → SGh X) (t : ThreadId) (g : SGh X) (u : ThreadId) :
    (upd G t g u).2.1 = if u = t then g.2.1 else (G u).2.1 := by
  unfold upd; split <;> rfl

/-- A step with the same ghost values: the writes of both words stay, the clocks grow, the
mutex's newest message stays, the permit count stays, and no thread joins the epoch's queue. -/
theorem Inv.mono {G : ThreadId → SGh X} {m m' : Mem} (hi : S.Inv G m) (hws : S.WS.Ok m')
    (hwe : S.WE.Ok m') (hS : S.WS.hist m' = S.WS.hist m) (hE : S.WE.hist m' = S.WE.hist m)
    (hcl : ∀ u : Nat, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (hbf : ∀ c, S.L.Before m c → S.L.Before m' c) (hpz : S.PZ m → S.PZ m' ∨ ∃ v, (G v).2.1 = .pst)
    (hwt : ∀ w ∈ m'.waiters, w.2 = S.WE.ptr → w ∈ m.waiters ∨
      ∃ i jr e, (G w.1).2.1 = .reg i jr false e ∧ (S.WE.hist m).size = i + 1)
    (hal : ∀ c, AllLe m c → AllLe m' c) : S.Inv G m' := by
  have hhb : ∀ c, S.HBH G m c → S.HBH G m' c := fun c h =>
    HBH.mono h hcl (fun u hu => .inl hu) hbf hal
  refine ⟨hws, hwe, by rw [hS]; exact hi.sv, hi.one, fun hn => by rw [hS]; exact hi.idle hn,
    fun u i jr sn e hu => (hi.era u i jr sn e hu).mono hS hE hcl hhb hpz fun v _ _ hv => ⟨v, hv⟩,
    by rw [hE]; exact hhb _ hi.hbE, hi.crit, fun u i e hu => by rw [hE]; exact hi.ld u i e hu,
    fun u hu v i jr sn e hv => ?_, fun u hu v i jr sn e hv => by rw [hE]; exact hi.wk u hu v i jr sn e hv,
    fun w hw he => ?_, hi.off⟩
  · obtain ⟨a, b, c⟩ := hi.inc u hu v i jr sn e hv
    exact ⟨by rw [hS]; exact a, by rw [hE]; exact b, by rw [hS]; exact VClock.le_trans c (hcl u)⟩
  · rcases hwt w hw he with hw' | ⟨i, jr, ee, h1, h2⟩
    · obtain ⟨i, jr, ee, h1, h2⟩ := hi.q w hw' he
      exact ⟨i, jr, ee, h1, by rw [hE]; exact h2⟩
    · exact ⟨i, jr, ee, h1, .inl (by rw [hE]; exact h2)⟩

/-- An op at a word that keeps its writes (a load, a failed `cmpxchg`). -/
theorem Inv.opKeep {W : Word 32 4} (hW : W = S.WS ∨ W = S.WE) {G : ThreadId → SGh X}
    {t : ThreadId} {m m' : Mem} (hi : S.Inv G m) (hop : W.Op t m m') (hw' : W.Ok m')
    (hh : W.hist m' = W.hist m) : S.Inv G m' := by
  have hb : W.b = S.b := by rcases hW with rfl | rfl <;> rfl
  have ho : S.o + 12 ≤ W.o ∧ W.o + 4 ≤ S.o + 20 := by
    rcases hW with rfl | rfl <;> simp [Sem.WS, Sem.WE] <;> omega
  have hk : ∀ W' : Word 32 4, W' ≠ W → (W' = S.WS ∨ W' = S.WE) → W'.Keep m m' := by
    intro W' hne hW'
    refine Word.keep_op hop ?_
    rcases hW with rfl | rfl <;> rcases hW' with rfl | rfl
    · exact absurd rfl hne
    · exact apSE
    · exact apES
    · exact absurd rfl hne
  have hok : ∀ W' : Word 32 4, (W' = S.WS ∨ W' = S.WE) → W'.Ok m' ∧ W'.hist m' = W'.hist m := by
    intro W' hW'
    by_cases e : W' = W
    · subst e; exact ⟨hw', hh⟩
    · exact ⟨(wd_ok hW' hi).keep (hk W' e hW'), Word.hist_keep (wd_ok hW' hi) (hk W' e hW')⟩
  refine hi.mono (hok _ (.inl rfl)).1 (hok _ (.inr rfl)).1 (hok _ (.inl rfl)).2 (hok _ (.inr rfl)).2
    hop.clocks (fun c ⟨i, l, hl, hle⟩ => ⟨i, l, (hop.locs.same _ _ ?_ i l).mpr hl, hle⟩)
    (fun h => .inl (PZ.mono h fun x _ h2 => hop.cells _ ?_))
    (fun w hw _ => .inl (by rw [hop.waiters] at hw; exact hw)) (allLe_keep hop.clocks (by rw [hop.threads]))
  · by_cases e : S.L.b = W.b
    · exact .inr (by simp only [Lock.prod]; omega)
    · exact .inl e
  · rintro ⟨-, h3, -⟩; simp only at h3; omega

/-- A change of thread `t`'s ghost value, with the same memory. -/
theorem Inv.retag {G : ThreadId → SGh X} {m : Mem} {t : ThreadId} {g : SGh X} (hi : S.Inv G m)
    (hhold : (G t).1.ph = .holds → g.1.ph = .holds)
    (hcrit : g.2.1.crit = true → g.1.ph = .holds)
    (hreg : ∀ i jr e, (∃ sn, g.2.1 = .reg i jr sn e) ↔ (∃ sn, (G t).2.1 = .reg i jr sn e))
    (hera : ∀ i jr sn e, g.2.1 = .reg i jr sn e → S.Era (upd G t g) m t i jr sn e)
    (hinc : g.2.1 = .inc ↔ (G t).2.1 = .inc) (hwk : g.2.1 = .wk → (G t).2.1 = .wk)
    (hwk' : (G t).2.1 = .wk → g.2.1 = .wk ∨ ∀ w ∈ m.waiters, w.2 = S.WE.ptr → False)
    (hld : ∀ i e, g.2.1 = .ld i e → (S.WE.hist m).size = i + 1 ∧ (S.WE.hist m)[i]!.Val e)
    (hpst : (G t).2.1 = .pst → g.2.1 = .pst ∨
      ∀ u i jr sn e, (G u).2.1 = .reg i jr sn e → (S.WS.hist m).size = jr + 1 → S.PZ m)
    (hoff : ∀ x, S.o + 12 ≤ x → x < S.o + 20 → g.1.part (S.b, x) = none)
    (htq : ∀ w ∈ m.waiters, w.2 = S.WE.ptr → w.1 ≠ t) : S.Inv (upd G t g) m := by
  have hsp := sph_upd G t g
  have hne : ∀ u, u ≠ t → upd G t g u = G u := fun u hu => upd_ne _ _ hu
  have hhb : ∀ c, S.HBH G m c → S.HBH (upd G t g) m c := fun c h =>
    HBH.mono h (fun _ => VClock.le_refl _) (fun u hu => .inl (by
      by_cases e : u = t
      · subst e; rw [upd_self]; exact hhold hu
      · rw [hne u e]; exact hu)) (fun _ h => h) (fun _ h => h)
  have hinc' : ∀ u, (upd G t g u).2.1 = .inc ↔ (G u).2.1 = .inc := fun u => by
    rw [hsp]; split
    · rename_i e; subst e; exact hinc
    · exact Iff.rfl
  have hwk1 : ∀ u, (upd G t g u).2.1 = .wk → (G u).2.1 = .wk := fun u => by
    rw [hsp]; split
    · rename_i e; subst e; exact hwk
    · exact id
  -- a thread that waits at the condition after waited before, with the same writes
  have hreg' : ∀ u i jr sn ep, (upd G t g u).2.1 = .reg i jr sn ep → ∃ sn', (G u).2.1 = .reg i jr sn' ep := by
    intro u i jr sn ep hu
    by_cases e : u = t
    · subst e; rw [upd_self] at hu; exact (hreg i jr ep).mp ⟨sn, hu⟩
    · exact ⟨sn, by rw [hne u e] at hu; exact hu⟩
  refine ⟨hi.ws, hi.we, hi.sv, fun u v i jr sn ep i' jr' sn' ep' hu hv => ?_, fun hn => hi.idle ?_,
    fun u i jr sn ep hu => ?_, hhb _ hi.hbE, fun u hu => ?_, fun u i _ hu => ?_,
    fun u hu v i jr sn ep hv => ?_, fun u hu v i jr sn ep hv => ?_, fun w hw he => ?_, fun u => ?_⟩
  · obtain ⟨c, hu'⟩ := hreg' u i jr sn ep hu
    obtain ⟨c', hv'⟩ := hreg' v i' jr' sn' ep' hv
    exact hi.one u v i jr c ep i' jr' c' ep' hu' hv'
  · intro u i jr sn ep hu
    by_cases e : u = t
    · subst e
      obtain ⟨c, h⟩ := (hreg i jr ep).mpr ⟨sn, hu⟩
      exact hn u i jr c ep (by rw [upd_self]; exact h)
    · exact hn u i jr sn ep (by rw [hne u e]; exact hu)
  · by_cases e : u = t
    · subst e; rw [upd_self] at hu; exact hera i jr sn ep hu
    · rw [hne u e] at hu
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hi.era u i jr sn ep hu
      refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, hhb _ h9, fun hs => ?_, fun hs he => ?_⟩
      · rcases h10 hs with h | ⟨v, hv⟩
        · exact .inl h
        · by_cases ev : v = t
          · subst ev
            rcases hpst hv with h' | h'
            · exact .inr ⟨v, by rw [upd_self]; exact h'⟩
            · exact .inl (h' u i jr sn ep hu hs)
          · exact .inr ⟨v, by rw [hne v ev]; exact hv⟩
      · obtain ⟨v, hv⟩ := h11 hs he
        exact ⟨v, (hinc' v).mpr hv⟩
  · by_cases e : u = t
    · subst e; rw [upd_self] at hu ⊢; exact hcrit hu
    · rw [hne u e] at hu ⊢; exact hi.crit u hu
  · by_cases e : u = t
    · subst e; rw [upd_self] at hu; exact hld i _ hu
    · rw [hne u e] at hu; exact hi.ld u i _ hu
  · obtain ⟨c, hv'⟩ := hreg' v i jr sn ep hv
    exact hi.inc u ((hinc' u).mp hu) v i jr c ep hv'
  · obtain ⟨c, hv'⟩ := hreg' v i jr sn ep hv
    exact hi.wk u (hwk1 u hu) v i jr c ep hv'
  · have hwt := htq w hw he
    obtain ⟨i, jr, ee, h1, h2⟩ := hi.q w hw he
    refine ⟨i, jr, ee, by rw [hne _ hwt]; exact h1, ?_⟩
    rcases h2 with h2 | ⟨v, hv⟩
    · exact .inl h2
    · by_cases ev : v = t
      · subst ev
        rcases hwk' hv with h' | h'
        · exact .inr ⟨v, by rw [upd_self]; exact h'⟩
        · exact absurd he (h' w hw)
      · exact .inr ⟨v, by rw [hne v ev]; exact hv⟩
  · intro x h1 h2
    by_cases e : u = t
    · subst e; rw [upd_self]; exact hoff x h1 h2
    · rw [hne u e]; exact hi.off u x h1 h2

/-! ## Ops that write a word of the condition -/

theorem push_lt {h : Array Word.Entry} {x : Word.Entry} {k : Nat} (hk : k < h.size) :
    (h.push x)[k]! = h[k]! := by
  have h1 : k < (h.push x).size := by simp; omega
  rw [getElem!_pos (h.push x) k h1, getElem!_pos h k hk, Array.getElem_push_lt hk]

theorem push_eq {h : Array Word.Entry} {x : Word.Entry} : (h.push x)[h.size]! = x := by
  rw [getElem!_pos _ _ (by simp)]; simp

theorem last_push {h : Array Word.Entry} {x : Word.Entry} : last (h.push x) = x := by
  simp only [last, Array.size_push, Nat.add_sub_cancel]; exact push_eq

theorem rmwEnt_val {M : Mem} {t : ThreadId} {ord : AtomicOrder} {e : Word.Entry}
    {new : BitVec 32} : (Word.rmwEnt M t ord e new).Val new := intOfBytes_rmw new

theorem val_eq {x : Word.Entry} {a b : BitVec 32} (ha : x.Val a) (hb : x.Val b) : a = b := by
  unfold Word.Entry.Val at ha hb; rw [ha] at hb; cases hb; rfl

theorem hist_pos {W : Word 32 4} {m : Mem} (hw : W.Ok m) : 0 < (W.hist m).size := by
  unfold Word.hist
  cases hf : m.atomics.findIdx? (fun l => l.block == W.b && l.off == W.o) with
  | none => simp
  | some i =>
    obtain ⟨-, h0, -⟩ := hw.loc i _ (Word.loc_of_find hf)
    simpa using h0

/-- An op at the state: the epoch stays. -/
theorem opS_E {G : ThreadId → SGh X} {t : ThreadId} {m m' : Mem} (hi : S.Inv G m)
    (hop : S.WS.Op t m m') : S.WE.Ok m' ∧ S.WE.hist m' = S.WE.hist m :=
  ⟨hi.we.keep (Word.keep_op hop apSE), Word.hist_keep hi.we (Word.keep_op hop apSE)⟩

/-- An op at the epoch: the state stays. -/
theorem opE_S {G : ThreadId → SGh X} {t : ThreadId} {m m' : Mem} (hi : S.Inv G m)
    (hop : S.WE.Op t m m') : S.WS.Ok m' ∧ S.WS.hist m' = S.WS.hist m :=
  ⟨hi.ws.keep (Word.keep_op hop apES), Word.hist_keep hi.ws (Word.keep_op hop apES)⟩

/-- An op at a word of the condition keeps the mutex's newest message and the permit count. -/
theorem op_keep {W : Word 32 4} (hW : W = S.WS ∨ W = S.WE) {t : ThreadId} {m m' : Mem}
    (hop : W.Op t m m') : (∀ c, S.L.Before m c → S.L.Before m' c) ∧ (S.PZ m → S.PZ m') := by
  have hb : W.b = S.b := by rcases hW with rfl | rfl <;> rfl
  have ho : S.o + 12 ≤ W.o := by rcases hW with rfl | rfl <;> simp [Sem.WS, Sem.WE]
  refine ⟨fun c ⟨i, l, hl, hle⟩ => ⟨i, l, (hop.locs.same _ _ ?_ i l).mpr hl, hle⟩,
    fun h => PZ.mono h fun x _ h2 => hop.cells _ ?_⟩
  · by_cases e : S.L.b = W.b
    · exact .inr (by simp only [Lock.prod]; omega)
    · exact .inl e
  · rintro ⟨-, h3, -⟩; simp only at h3; omega

theorem HBH.op {W : Word 32 4} (hW : W = S.WS ∨ W = S.WE) {G : ThreadId → SGh X} {t : ThreadId}
    {m m' : Mem} (hop : W.Op t m m') {c : VClock} (h : S.HBH G m c) : S.HBH G m' c :=
  HBH.mono h hop.clocks (fun _ hu => .inl hu) (op_keep hW hop).1 (allLe_keep hop.clocks (by rw [hop.threads]))

/-- Thread `t` waits at the condition: `waiters += 1` (state write `jr`). -/
theorem Inv.reg {G : ThreadId → SGh X} {t : ThreadId} {m m' : Mem} {i : Nat} {ord : AtomicOrder}
    {ev : BitVec 32} (hi : S.Inv G m) (hg : (G t).2.1 = .ld i ev) (hh : (G t).1.ph = .holds)
    (hcr : ∀ u, u ≠ t → (G u).2.1.crit = false) (hnr : ∀ u i' jr sn e, (G u).2.1 ≠ .reg i' jr sn e)
    (hop : S.WS.Op t m m') (hw' : S.WS.Ok m')
    (hS : S.WS.hist m' = (S.WS.hist m).push (Word.rmwEnt m' t ord (last (S.WS.hist m)) (1 : BitVec 32)))
    (hpz : S.PZ m') (he : (S.WE.hist m)[i]!.Val ev)
    (hce : VClock.le (S.WE.hist m)[i]!.clock (m'.clocks[t]!) = true) :
    S.Inv (upd G t ((G t).1, .reg i (S.WS.hist m).size false ev, (G t).2.2)) m' := by
  obtain ⟨hwe, hE⟩ := opS_E hi hop
  have hsp := sph_upd G t ((G t).1, .reg i (S.WS.hist m).size false ev, (G t).2.2)
  have hne : ∀ u, u ≠ t → upd G t ((G t).1, .reg i (S.WS.hist m).size false ev, (G t).2.2) u = G u :=
    fun u hu => upd_ne _ _ hu
  have hld := (hi.ld t i ev hg).1
  have hhb : ∀ c, S.HBH G m c → S.HBH (upd G t ((G t).1, .reg i (S.WS.hist m).size false ev, (G t).2.2)) m' c :=
    fun c h => HBH.mono h hop.clocks (fun u hu => .inl (by
      by_cases e : u = t
      · subst e; rw [upd_self]; exact hu
      · rw [hne u e]; exact hu)) (op_keep (.inl rfl) hop).1 (allLe_keep hop.clocks (by rw [hop.threads]))
  have hsz : (S.WS.hist m').size = (S.WS.hist m).size + 1 := by rw [hS]; simp
  have hnew : (S.WS.hist m')[(S.WS.hist m).size]! =
      Word.rmwEnt m' t ord (last (S.WS.hist m)) (1 : BitVec 32) := by
    rw [hS]; exact push_eq
  have hreg : ∀ u i' jr sn ep, (upd G t ((G t).1, .reg i (S.WS.hist m).size false ev, (G t).2.2) u).2.1 =
      .reg i' jr sn ep → u = t := fun u i' jr sn ep hu => by
    by_cases e : u = t
    · exact e
    · rw [hne u e] at hu; exact absurd hu (hnr u i' jr sn ep)
  refine ⟨hw', hwe, fun k hk => ?_, fun u v _ _ _ _ _ _ _ _ hu hv => (hreg u _ _ _ _ hu).trans
      (hreg v _ _ _ _ hv).symm, fun hn => absurd (by rw [upd_self]) (hn t i _ false ev),
    fun u i' jr sn ep hu => ?_, by rw [hE]; exact hhb _ hi.hbE, fun u hu => ?_,
    fun u i' _ hu => ?_, fun u hu => ?_, fun u hu => ?_, fun w hw he' => ?_, fun u x h1 h2 => ?_⟩
  · rw [hsz] at hk
    by_cases hk' : k < (S.WS.hist m).size
    · rw [hS, push_lt hk']; exact hi.sv k hk'
    · have : k = (S.WS.hist m).size := by omega
      subst this; rw [hnew]; exact ⟨1, .inr (.inl rfl), rmwEnt_val⟩
  · have := hreg u i' jr sn ep hu; subst this
    rw [upd_self] at hu
    simp only [SPh.reg.injEq] at hu
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hu
    refine ⟨.inl hsz, by rw [hnew]; exact rmwEnt_val, fun h => by omega, .inl (by rw [hE]; exact hld),
      ⟨by rw [hE]; exact he, fun h => by rw [hE] at h; omega⟩, fun h => (by cases h),
      by rw [hnew]; exact VClock.le_refl _, by rw [hE]; exact hce,
      .inl ⟨u, by rw [upd_self]; exact hh, by rw [hnew]; exact VClock.le_refl _⟩,
      fun _ => .inl hpz, fun h => by omega⟩
  · by_cases e : u = t
    · subst e; rw [upd_self] at hu; cases hu
    · rw [hne u e] at hu ⊢; exact hi.crit u hu
  · by_cases e : u = t
    · subst e; rw [upd_self] at hu; cases hu
    · rw [hne u e] at hu; have := hcr u e; rw [hu] at this; cases this
  · by_cases e : u = t
    · subst e; rw [upd_self] at hu; cases hu
    · rw [hne u e] at hu; have := hcr u e; rw [hu] at this; cases this
  · by_cases e : u = t
    · subst e; rw [upd_self] at hu; cases hu
    · rw [hne u e] at hu; have := hcr u e; rw [hu] at this; cases this
  · rw [hop.waiters] at hw
    obtain ⟨i', jr', ee', h1, -⟩ := hi.q w hw he'
    exact absurd h1 (hnr _ _ _ _ _)
  · by_cases e : u = t
    · subst e; rw [upd_self]; exact hi.off u x h1 h2
    · rw [hne u e]; exact hi.off u x h1 h2

/-- A registered thread `R` before the newest state write `(1, 0)` of a `signal`: that write is
its `waiters += 1`, so no signal is there yet and the epoch is write `i`. -/
theorem Inv.find {G : ThreadId → SGh X} {m : Mem} (hi : S.Inv G m)
    (hv : (last (S.WS.hist m)).Val (1 : BitVec 32)) :
    ∃ R i jr sn e, (G R).2.1 = .reg i jr sn e ∧ (S.WS.hist m).size = jr + 1 ∧
      (S.WE.hist m).size = i + 1 := by
  by_cases h : ∃ R i jr sn e, (G R).2.1 = .reg i jr sn e
  · obtain ⟨R, i, jr, sn, ep, hR⟩ := h
    have he := hi.era R i jr sn ep hR
    have hs : (S.WS.hist m).size = jr + 1 := by
      rcases he.ssz with h | h
      · exact h
      · have h1 := he.s1 h
        simp only [last, h] at hv
        have := val_eq hv h1; cases this
    refine ⟨R, i, jr, sn, ep, hR, hs, ?_⟩
    rcases he.esz with h | ⟨-, h, -⟩
    · exact h
    · omega
  · have := val_eq hv (hi.idle fun u i jr sn e hu => h ⟨u, i, jr, sn, e, hu⟩); cases this

/-- The waiter `t` takes the signal: `(1, 1) → (0, 0)`. -/
theorem Inv.consume {G : ThreadId → SGh X} {t : ThreadId} {m m' : Mem} {i jr : Nat} {sn : Bool}
    {ord : AtomicOrder} (hi : S.Inv G m) (hg : (G t).2.1 = .reg i jr sn e)
    (htq : ∀ w ∈ m.waiters, w.2 = S.WE.ptr → w.1 ≠ t)
    (hop : S.WS.Op t m m') (hw' : S.WS.Ok m')
    (hS : S.WS.hist m' = (S.WS.hist m).push (Word.rmwEnt m' t ord (last (S.WS.hist m)) (0 : BitVec 32))) :
    S.Inv (upd G t ((G t).1, .none, (G t).2.2)) m' := by
  obtain ⟨hwe, hE⟩ := opS_E hi hop
  have hne : ∀ u, u ≠ t → upd G t ((G t).1, .none, (G t).2.2) u = G u := fun u hu => upd_ne _ _ hu
  -- no thread waits at the condition after it
  have hnr : ∀ u i' jr' sn' e', (upd G t ((G t).1, .none, (G t).2.2) u).2.1 ≠ .reg i' jr' sn' e' := by
    intro u i' jr' sn' e' hu
    by_cases e : u = t
    · subst e; rw [upd_self] at hu; cases hu
    · rw [hne u e] at hu; exact e (hi.one u t _ _ _ _ _ _ _ _ hu hg)
  have hhb : ∀ c, S.HBH G m c → S.HBH (upd G t ((G t).1, .none, (G t).2.2)) m' c :=
    fun c h => HBH.mono h hop.clocks (fun u hu => .inl (by
      by_cases e : u = t
      · subst e; rw [upd_self]; exact hu
      · rw [hne u e]; exact hu)) (op_keep (.inl rfl) hop).1 (allLe_keep hop.clocks (by rw [hop.threads]))
  have hsz : (S.WS.hist m').size = (S.WS.hist m).size + 1 := by rw [hS]; simp
  refine ⟨hw', hwe, fun k hk => ?_, fun u _ _ _ _ _ _ _ _ _ hu => absurd hu (hnr u _ _ _ _),
    fun _ => by rw [hS, last_push]; exact rmwEnt_val, fun u _ _ _ _ hu => absurd hu (hnr u _ _ _ _),
    by rw [hE]; exact hhb _ hi.hbE, fun u hu => ?_, fun u i' _ hu => ?_,
    fun _ _ v _ _ _ _ hv => absurd hv (hnr v _ _ _ _), fun _ _ v _ _ _ _ hv => absurd hv (hnr v _ _ _ _),
    fun w hw he => ?_, fun u x h1 h2 => ?_⟩
  · rw [hsz] at hk
    by_cases hk' : k < (S.WS.hist m).size
    · rw [hS, push_lt hk']; exact hi.sv k hk'
    · have : k = (S.WS.hist m).size := by omega
      subst this; rw [hS, push_eq]; exact ⟨0, .inl rfl, rmwEnt_val⟩
  · by_cases e : u = t
    · subst e; rw [upd_self] at hu; cases hu
    · rw [hne u e] at hu ⊢; exact hi.crit u hu
  · by_cases e : u = t
    · subst e; rw [upd_self] at hu; cases hu
    · rw [hne u e] at hu; rw [hE]; exact hi.ld u i' _ hu
  · rw [hop.waiters] at hw
    obtain ⟨i', jr', ee', h1, -⟩ := hi.q w hw he
    exact absurd (by rw [hne _ (htq w hw he)]; exact h1) (hnr w.1 _ _ _ _)
  · by_cases e : u = t
    · subst e; rw [upd_self]; exact hi.off u x h1 h2
    · rw [hne u e]; exact hi.off u x h1 h2

/-- `signal`'s `signals += 1` by `t`: `(1, 0) → (1, 1)`. -/
theorem Inv.sig {G : ThreadId → SGh X} {t : ThreadId} {m m' : Mem} {ord : AtomicOrder}
    (hi : S.Inv G m) (hg : (G t).2.1 = .pst) (hh : (G t).1.ph = .holds)
    (hcr : ∀ u, u ≠ t → (G u).2.1.crit = false) (hop : S.WS.Op t m m') (hw' : S.WS.Ok m')
    (hv : (last (S.WS.hist m)).Val (1 : BitVec 32))
    (hS : S.WS.hist m' =
      (S.WS.hist m).push (Word.rmwEnt m' t ord (last (S.WS.hist m)) (0x10001 : BitVec 32))) :
    S.Inv (upd G t ((G t).1, .inc, (G t).2.2)) m' := by
  obtain ⟨hwe, hE⟩ := opS_E hi hop
  obtain ⟨R, i, jr, sn, ep, hR, hsR, heR⟩ := hi.find hv
  have hne : ∀ u, u ≠ t → upd G t ((G t).1, .inc, (G t).2.2) u = G u := fun u hu => upd_ne _ _ hu
  have hRt : R ≠ t := fun e => by rw [e, hg] at hR; cases hR
  have hregG : ∀ u i' jr' sn' e', (upd G t ((G t).1, .inc, (G t).2.2) u).2.1 = .reg i' jr' sn' e' →
      u ≠ t ∧ (G u).2.1 = .reg i' jr' sn' e' := by
    intro u i' jr' sn' e' hu
    by_cases e : u = t
    · subst e; rw [upd_self] at hu; cases hu
    · rw [hne u e] at hu; exact ⟨e, hu⟩
  have hhb : ∀ c, S.HBH G m c → S.HBH (upd G t ((G t).1, .inc, (G t).2.2)) m' c :=
    fun c h => HBH.mono h hop.clocks (fun u hu => .inl (by
      by_cases e : u = t
      · subst e; rw [upd_self]; exact hu
      · rw [hne u e]; exact hu)) (op_keep (.inl rfl) hop).1 (allLe_keep hop.clocks (by rw [hop.threads]))
  have hsz : (S.WS.hist m').size = jr + 2 := by rw [hS]; simp [hsR]
  have hnew : (S.WS.hist m')[jr + 1]! =
      Word.rmwEnt m' t ord (last (S.WS.hist m)) (0x10001 : BitVec 32) := by
    rw [hS, show jr + 1 = (S.WS.hist m).size by omega]; exact push_eq
  have hold : ∀ k, k < (S.WS.hist m).size → (S.WS.hist m')[k]! = (S.WS.hist m)[k]! := fun k hk => by
    rw [hS, push_lt hk]
  have hnc : ∀ u, u ≠ t → ∀ p, (G u).2.1 = p → p.crit = true → False := fun u hu p h hc => by
    have := hcr u hu; rw [h, hc] at this; cases this
  refine ⟨hw', hwe, fun k hk => ?_, fun u v _ _ _ _ _ _ _ _ hu hv => ?_, fun hn => ?_,
    fun u i' jr' sn' e' hu => ?_, by rw [hE]; exact hhb _ hi.hbE, fun u hu => ?_, fun u i' _ hu => ?_,
    fun u hu v i' jr' sn' e' hv => ?_, fun u hu v i' jr' sn' e' hv => ?_, fun w hw he => ?_,
    fun u x h1 h2 => ?_⟩
  · rw [hsz] at hk
    by_cases hk' : k < (S.WS.hist m).size
    · rw [hold k hk']; exact hi.sv k hk'
    · have : k = jr + 1 := by omega
      subst this; rw [hnew]; exact ⟨_, .inr (.inr rfl), rmwEnt_val⟩
  · obtain ⟨-, hu'⟩ := hregG u _ _ _ _ hu
    obtain ⟨-, hv'⟩ := hregG v _ _ _ _ hv
    exact hi.one u v _ _ _ _ _ _ _ _ hu' hv'
  · exact absurd (by rw [hne R hRt]; exact hR) (hn R i jr sn ep)
  · obtain ⟨hut, hu'⟩ := hregG u _ _ _ _ hu
    have e := hi.one u R _ _ _ _ _ _ _ _ hu' hR
    subst e
    have hq := hR.symm.trans hu'
    simp only [SPh.reg.injEq] at hq
    obtain ⟨e1, e2, -, -⟩ := hq
    rw [e1] at heR; rw [e2] at hsR hsz hnew
    obtain ⟨h1, h2, -, h4, h5, h6, h7, h8, h9, -, -⟩ := hi.era u i' jr' sn' e' hu'
    refine ⟨.inr hsz, by rw [hold jr' (by omega)]; exact h2, fun _ => by rw [hnew]; exact rmwEnt_val,
      .inl (by rw [hE]; exact heR), by rw [hE]; exact h5, fun hs => ?_,
      by rw [hold jr' (by omega)]; exact VClock.le_trans h7 (hop.clocks u),
      by rw [hE]; exact VClock.le_trans h8 (hop.clocks u),
      by rw [hold jr' (by omega)]; exact hhb _ h9, fun hs => by omega,
      fun _ _ => ⟨t, by rw [upd_self]⟩⟩
    have := (h6 hs).1; omega
  · by_cases e : u = t
    · subst e; rw [upd_self]; exact hh
    · rw [hne u e] at hu ⊢; exact hi.crit u hu
  · by_cases e : u = t
    · subst e; rw [upd_self] at hu; cases hu
    · rw [hne u e] at hu; exact (hnc u e _ hu rfl).elim
  · by_cases e : u = t
    · subst e
      obtain ⟨hvt, hv'⟩ := hregG v _ _ _ _ hv
      have e := hi.one v R _ _ _ _ _ _ _ _ hv' hR
      subst e
      have hq := hR.symm.trans hv'
      simp only [SPh.reg.injEq] at hq
      obtain ⟨e1, e2, -, -⟩ := hq
      rw [e1] at heR; rw [e2] at hsR hsz hnew
      exact ⟨hsz, by rw [hE]; exact heR, by rw [hnew]; exact VClock.le_refl _⟩
    · rw [hne u e] at hu; exact (hnc u e _ hu rfl).elim
  · by_cases e : u = t
    · subst e; rw [upd_self] at hu; cases hu
    · rw [hne u e] at hu; exact (hnc u e _ hu rfl).elim
  · rw [hop.waiters] at hw
    obtain ⟨i', jr', ee', h1, h2⟩ := hi.q w hw he
    have hwt : w.1 ≠ t := fun e => by rw [e, hg] at h1; cases h1
    refine ⟨i', jr', ee', by rw [hne _ hwt]; exact h1, ?_⟩
    rcases h2 with h2 | ⟨v, hv⟩
    · exact .inl (by rw [hE]; exact h2)
    · by_cases ev : v = t
      · subst ev; rw [hg] at hv; cases hv
      · exact (hnc v ev _ hv rfl).elim
  · by_cases e : u = t
    · subst e; rw [upd_self]; exact hi.off u x h1 h2
    · rw [hne u e]; exact hi.off u x h1 h2

/-- `signal`'s `epoch += 1` (a release) by `t`. -/
theorem Inv.epoch {G : ThreadId → SGh X} {t : ThreadId} {m m' : Mem} {old : BitVec 32}
    (hi : S.Inv G m) (hg : (G t).2.1 = .inc) (hh : (G t).1.ph = .holds)
    (hcr : ∀ u, u ≠ t → (G u).2.1.crit = false) (hop : S.WE.Op t m m') (hw' : S.WE.Ok m')
    (hv : (last (S.WE.hist m)).Val old)
    (hE : S.WE.hist m' = (S.WE.hist m).push (Word.rmwEnt m' t .release (last (S.WE.hist m)) (old + 1))) :
    S.Inv (upd G t ((G t).1, .wk, (G t).2.2)) m' := by
  obtain ⟨hws, hS⟩ := opE_S hi hop
  have hne : ∀ u, u ≠ t → upd G t ((G t).1, .wk, (G t).2.2) u = G u := fun u hu => upd_ne _ _ hu
  have hregG : ∀ u i' jr' sn' e', (upd G t ((G t).1, .wk, (G t).2.2) u).2.1 = .reg i' jr' sn' e' →
      u ≠ t ∧ (G u).2.1 = .reg i' jr' sn' e' := by
    intro u i' jr' sn' e' hu
    by_cases e : u = t
    · subst e; rw [upd_self] at hu; cases hu
    · rw [hne u e] at hu; exact ⟨e, hu⟩
  have hhb : ∀ c, S.HBH G m c → S.HBH (upd G t ((G t).1, .wk, (G t).2.2)) m' c :=
    fun c h => HBH.mono h hop.clocks (fun u hu => .inl (by
      by_cases e : u = t
      · subst e; rw [upd_self]; exact hu
      · rw [hne u e]; exact hu)) (op_keep (.inr rfl) hop).1 (allLe_keep hop.clocks (by rw [hop.threads]))
  have hsz : (S.WE.hist m').size = (S.WE.hist m).size + 1 := by rw [hE]; simp
  have hold : ∀ k, k < (S.WE.hist m).size → (S.WE.hist m')[k]! = (S.WE.hist m)[k]! := fun k hk => by
    rw [hE, push_lt hk]
  have hnew : (S.WE.hist m')[(S.WE.hist m).size]! =
      Word.rmwEnt m' t .release (last (S.WE.hist m)) (old + 1) := by rw [hE]; exact push_eq
  have hnc : ∀ u, u ≠ t → ∀ p, (G u).2.1 = p → p.crit = true → False := fun u hu p h hc => by
    have := hcr u hu; rw [h, hc] at this; cases this
  have hpos := hist_pos hi.we
  refine ⟨hws, hw', by rw [hS]; exact hi.sv, fun u v _ _ _ _ _ _ _ _ hu hv => ?_, fun hn => ?_,
    fun u i jr sn e hu => ?_, ?_, fun u hu => ?_, fun u i _ hu => ?_, fun u hu => ?_,
    fun u hu v i jr sn e hv => ?_, fun w hw he => ?_, fun u x h1 h2 => ?_⟩
  · exact hi.one u v _ _ _ _ _ _ _ _ (hregG u _ _ _ _ hu).2 (hregG v _ _ _ _ hv).2
  · rw [hS]; exact hi.idle fun u i jr sn e hu => hn u i jr sn e (by
      have hut : u ≠ t := fun e => by rw [e, hg] at hu; cases hu
      rw [hne u hut]; exact hu)
  · obtain ⟨hut, hu'⟩ := hregG u _ _ _ _ hu
    obtain ⟨h1, h2, h3, -, ⟨he, -⟩, h6, h7, h8, h9, h10, -⟩ := hi.era u i jr sn e hu'
    obtain ⟨hs2, he1, hcl⟩ := hi.inc t hg u i jr sn e hu'
    have hlast : last (S.WE.hist m) = (S.WE.hist m)[i]! := by simp only [last, he1, Nat.add_sub_cancel]
    rw [hlast] at hv
    have hoe := val_eq hv he
    subst hoe
    refine ⟨by rw [hS]; exact h1, by rw [hS]; exact h2, by rw [hS]; exact h3,
      .inr ⟨by rw [hsz, he1], by rw [hS]; exact hs2, ?_⟩,
      ⟨by rw [hold i (by omega)]; exact he, fun _ => by
        rw [show i + 1 = (S.WE.hist m).size by omega, hnew]; exact rmwEnt_val⟩,
      fun hsn => ?_, by rw [hS]; exact VClock.le_trans h7 (hop.clocks u),
      by rw [hold i (by omega)]; exact VClock.le_trans h8 (hop.clocks u),
      by rw [hS]; exact hhb _ h9, fun hs => by rw [hS] at hs; omega, fun _ he' => by omega⟩
    · rw [hS, show i + 1 = (S.WE.hist m).size by omega, hnew]
      simp only [Word.rmwEnt, AtomicOrder.isRel, ↓reduceIte]
      exact VClock.le_trans hcl (VClock.le_trans (hop.clocks t) (VClock.le_merge_right _ _))
    · have := (h6 hsn).1; omega
  · rw [show last (S.WE.hist m') = (S.WE.hist m')[(S.WE.hist m).size]! by
      simp only [last, hsz, Nat.add_sub_cancel], hnew]
    exact .inl ⟨t, by rw [upd_self]; exact hh, VClock.le_refl _⟩
  · by_cases e : u = t
    · subst e; rw [upd_self]; exact hh
    · rw [hne u e] at hu ⊢; exact hi.crit u hu
  · by_cases e : u = t
    · subst e; rw [upd_self] at hu; cases hu
    · rw [hne u e] at hu; exact (hnc u e _ hu rfl).elim
  · by_cases e : u = t
    · subst e; rw [upd_self] at hu; cases hu
    · rw [hne u e] at hu; exact (hnc u e _ hu rfl).elim
  · by_cases e : u = t
    · subst e
      obtain ⟨-, hv'⟩ := hregG v _ _ _ _ hv
      obtain ⟨-, he1, -⟩ := hi.inc u hg v i jr sn e hv'
      rw [hsz, he1]
    · rw [hne u e] at hu; exact (hnc u e _ hu rfl).elim
  · rw [hop.waiters] at hw
    obtain ⟨i', jr', ee', h1, -⟩ := hi.q w hw he
    have hwt : w.1 ≠ t := fun e => by rw [e, hg] at h1; cases h1
    exact ⟨i', jr', ee', by rw [hne _ hwt]; exact h1, .inr ⟨t, by rw [upd_self]⟩⟩
  · by_cases e : u = t
    · subst e; rw [upd_self]; exact hi.off u x h1 h2
    · rw [hne u e]; exact hi.off u x h1 h2

/-- `signal`'s futex wake at the epoch: the waiter (if it sleeps) wakes, and no thread is left at
the epoch's futex. -/
theorem wakeE_none {G : ThreadId → SGh X} {m : Mem} (hi : S.Inv G m) :
    ∀ w ∈ m.waiters.filter (fun w => !(((m.waiters.filter (·.2 == S.WE.ptr)).extract 0 1).map
      (·.1)).contains w.1), w.2 = S.WE.ptr → False := by
  intro w hw he
  obtain ⟨hw, hnc⟩ := Array.mem_filter.mp hw
  have hwf : w ∈ m.waiters.filter (·.2 == S.WE.ptr) := Array.mem_filter.mpr ⟨hw, by simp [he]⟩
  have hpos : 0 < (m.waiters.filter (·.2 == S.WE.ptr)).size := by
    obtain ⟨k, hk, -⟩ := Array.mem_iff_getElem.mp hwf; omega
  have h0 := Array.getElem_mem hpos
  obtain ⟨h0w, h0e⟩ := Array.mem_filter.mp h0
  obtain ⟨i, jr, ee, h1, -⟩ := hi.q w hw he
  obtain ⟨i', jr', ee', h1', -⟩ := hi.q _ h0w (by simpa using h0e)
  have e := hi.one _ _ _ _ _ _ _ _ _ _ h1' h1
  have : (((m.waiters.filter (·.2 == S.WE.ptr)).extract 0 1).map (·.1)).contains w.1 = true := by
    rw [Array.contains_iff_mem, Array.mem_map]
    exact ⟨_, Array.mem_extract_iff_getElem.mpr ⟨0, by simp; omega, rfl⟩, e⟩
  rw [this] at hnc; cases hnc

/-- A step of the holder `t` on its own part (`WP.liftMem_owned`): the words, the clocks of the
others and the futex queue stay. -/
theorem Inv.stepIn {G : ThreadId → SGh X} {m m' : Mem} {t : ThreadId} {hQ : Heap}
    (hl : S.L.Inv G m) (hi : S.Inv G m) (hs : StepIn (m.heap.diff (S.L.own G m t)) m m')
    (hm' : m'.heap = hQ ∪ m.heap.diff (S.L.own G m t))
    (hd : Heap.Disjoint hQ (m.heap.diff (S.L.own G m t)))
    (hpz : S.PZ m → S.PZ m' ∨ ∃ v, (G v).2.1 = .pst) : S.Inv G m' := by
  have hoff : ∀ (W : Word 32 4), (W = S.WS ∨ W = S.WE) → W.Off (S.L.own G m t) := fun W hW =>
    (wd_off hW hl hi).1 t
  have hkS := Word.keep_stepIn hi.ws (hoff _ (.inl rfl)) hs hm' hd
  have hkE := Word.keep_stepIn hi.we (hoff _ (.inr rfl)) hs hm' hd
  have hcl : ∀ u : Nat, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true := fun u => by
    by_cases hu : u = m.current
    · subst hu; exact hs.mine
    · rw [hs.others u hu]; exact VClock.le_refl _
  exact hi.mono (hi.ws.keep hkS) (hi.we.keep hkE) (Word.hist_keep hi.ws hkS)
    (Word.hist_keep hi.we hkE) hcl (fun c ⟨i, l, hl, hle⟩ => ⟨i, l, by unfold Lock.Loc; rw [hs.atomics]; exact hl, hle⟩)
    hpz (fun w hw _ => .inl (by rw [hs.waiters] at hw; exact hw)) (allLe_keep hcl (by rw [hs.threads]))

/-! ## The holder -/

/-- A clock that happened before the holder or the mutex's newest message happened before the
holder `t`. -/
theorem HBH.le {G : ThreadId → SGh X} {m : Mem} {t : ThreadId} {c : VClock} (hl : S.L.Inv G m)
    (hh : (G t).1.ph = .holds) (h : S.HBH G m c) : VClock.le c (m.clocks[t]!) = true := by
  rcases h with ⟨u, hu, hle⟩ | ⟨i, l, hloc, hle⟩ | hal
  · have := hl.one u t hu hh; subst this; exact hle
  · exact VClock.le_trans hle ((hl.rel i l hloc).2 t hh)
  · exact hal t (hl.live t (by change (G t).1.ph ≠ _; rw [hh]; decide)).1

/-- Only the holder `t` is in the critical code. -/
theorem crit_one {G : ThreadId → SGh X} {m : Mem} {t : ThreadId} (hl : S.L.Inv G m)
    (hs : S.Inv G m) (hh : (G t).1.ph = .holds) (u : ThreadId) (hu : u ≠ t) :
    (G u).2.1.crit = false := by
  cases e : (G u).2.1.crit
  · rfl
  · exact absurd (hl.one u t (hs.crit u e) hh) hu

/-- The holder reads the state after each waiter's `waiters += 1`. -/
theorem reg_le {G : ThreadId → SGh X} {m : Mem} {t R i jr : Nat} {sn : Bool} (hl : S.L.Inv G m)
    (hs : S.Inv G m) (hh : (G t).1.ph = .holds) (hR : (G R).2.1 = .reg i jr sn e) {j : Nat}
    (hfl : Word.Floor (S.WS.hist m) (m.clocks[t]!) j) : jr ≤ j := by
  have he := hs.era R i jr sn e hR
  exact hfl jr (by rcases he.ssz with h | h <;> omega) (HBH.le hl hh he.hb)

/-- A change of `t`'s place in the condition: the protocol's invariant from the condition's. -/
theorem Fits.retag (hP : S.Fits P U) {G : ThreadId → SGh X} {m : Mem} {t : ThreadId} {g : SGh X}
    (hl : S.L.Inv G m) (hu : U G m) (hs : S.Inv (upd G t g) m) (h1 : g.1 = (G t).1)
    (h2 : g.2.2 = (G t).2.2) (hw : g.2.1.waits = true → (G t).2.1.waits = true ∨ S.wx g.2.2)
    (hS : S.inS g.2.2) : P.inv (upd G t g) m := by
  refine hP.pack (hl.congr (fun u => ?_) (fun u => ?_) (fun u => ?_) fun h => ?_) hs
    (hP.stable G m m t g hu (Step.refl t m) h2 (by rw [h1]) hw (fun _ => hS))
  · unfold upd; split
    · rename_i e; subst e; show g.1.ph = _; rw [h1]; rfl
    · rfl
  · unfold upd; split
    · rename_i e; subst e; show g.1.part = _; rw [h1]; rfl
    · rfl
  · unfold upd; split
    · rename_i e; subst e; show g.1.held = _; rw [h1]; rfl
    · rfl
  · show S.R _ h ↔ S.R _ h
    have : xs (fun u => (upd G t g u).2) = xs (fun u => (G u).2) := by
      funext u; simp only [xs, upd]; split
      · rename_i e; subst e; exact h2
      · rfl
    unfold Sem.R; rw [this]

/-! ## The condition's state as bits -/

theorem ofBits_cst (b : BitVec 32) :
    (Packed.ofBits? (α := Io_Condition_State) b).run = some (.ok (Packed.ofBits b)) := rfl

theorem bits1 : Packed.toBits (Packed.ofBits (1 : BitVec 32) : Io_Condition_State) = 1 := by
  decide +kernel
theorem bits11 : Packed.toBits (Packed.ofBits (0x10001 : BitVec 32) : Io_Condition_State) =
    0x10001 := by decide +kernel
/-- The condition's state `(w, s)`. -/
abbrev cst (w s : BitVec 16) : Io_Condition_State := ⟨w, s⟩

theorem bits_sig : Packed.toBits (cst (Packed.ofBits (1 : BitVec 32) : Io_Condition_State).waiters 1) =
    0x10001 := by decide +kernel
theorem bits_take : Packed.toBits (cst 0 0) = 0 := by decide +kernel

/-- `signal` sends a signal only at `(1, 0)`. -/
theorem gt_sv {b : BitVec 32} (hb : SV b) :
    gt false (Packed.ofBits b : Io_Condition_State).waiters
      (Packed.ofBits b : Io_Condition_State).signals = true ↔
      b = 1 := by
  rcases hb with rfl | rfl | rfl <;> decide +kernel

/-- The waiter takes a signal only at `(1, 1)`. -/
theorem sig_sv {b : BitVec 32} (hb : SV b) :
    gt false (Packed.ofBits b : Io_Condition_State).signals 0 = true ↔ b = 0x10001 := by
  rcases hb with rfl | rfl | rfl <;> decide +kernel

theorem add_sig : (add false (Packed.ofBits (1 : BitVec 32) : Io_Condition_State).signals
    (1 : BitVec 16)).run = some (.ok 1) := by
  cases h : (add false (Packed.ofBits (1 : BitVec 32) : Io_Condition_State).signals (1 : BitVec 16)).run with
  | none =>
    exact absurd h (by
      simp [add]; split <;> simp [throw, throwThe, MonadExceptOf.throw, ExceptT.mk, pure,
        ExceptT.pure, ExceptT.run])
  | some r =>
    cases r with
    | error e => exact absurd h (add_one_noErr (by decide +kernel) e)
    | ok v =>
      have := add_one_ok h (by decide +kernel)
      rw [show v = 1 from BitVec.eq_of_toNat_eq (by rw [this]; decide +kernel)]

theorem sub_w : (sub false (Packed.ofBits (0x10001 : BitVec 32) : Io_Condition_State).waiters
    (1 : BitVec 16)).run =
      some (.ok ((Packed.ofBits (0x10001 : BitVec 32) : Io_Condition_State).waiters - 1)) := rfl
theorem sub_s : (sub false (Packed.ofBits (0x10001 : BitVec 32) : Io_Condition_State).signals
    (1 : BitVec 16)).run =
      some (.ok ((Packed.ofBits (0x10001 : BitVec 32) : Io_Condition_State).signals - 1)) := rfl
theorem bits_take' : Packed.toBits (cst ((Packed.ofBits (0x10001 : BitVec 32) : Io_Condition_State).waiters - 1)
    ((Packed.ofBits (0x10001 : BitVec 32) : Io_Condition_State).signals - 1)) = 0 := by decide +kernel

/-! ## `signal` -/

/-- A futex wake at the epoch. -/
theorem Step.wake {t : ThreadId} {m : Mem} (ws : Array (ThreadId × Ptr)) (wk : Array ThreadId)
    (hw : ∀ w ∈ ws, w ∈ m.waiters) :
    S.Step t m { m with current := t, waiters := ws, woken := wk } :=
  ⟨rfl, rfl, fun _ => VClock.le_refl _, rfl, fun _ _ => rfl, fun _ he => .inl he,
    fun w h _ _ => hw w h, rfl, fun _ _ _ _ _ => Iff.rfl, fun _ hl => .inl hl⟩

/-- A new futex queue `ws` (a part of the old one, with no thread at the epoch's futex) and
woken threads `wk`, and `t` leaves `wk`. -/
theorem Fits.requeue (hP : S.Fits P U) {G : ThreadId → SGh X} {m : Mem} {t : ThreadId} {a : LG}
    {x : X} (hinS : S.inS x) {ws : Array (ThreadId × Ptr)} {wk : Array ThreadId} (hi : P.inv (upd G t (a, .wk, x)) m)
    (hsub : ∀ w ∈ ws, w ∈ m.waiters) (hnone : ∀ w ∈ ws, w.2 = S.WE.ptr → False)
    (hl' : S.L.Inv (upd G t (a, .wk, x)) { m with current := t, waiters := ws, woken := wk }) :
    P.inv (upd G t (a, .none, x)) { m with current := t, waiters := ws, woken := wk } := by
  obtain ⟨-, hs, hu⟩ := hP.split hi
  have hk : ∀ W : Word 32 4, W.Keep m { m with current := t, waiters := ws, woken := wk } :=
    fun _ => Word.keep_same m t m.seen m.nextMsg ws wk m.groups
  have hs' := hs.mono (hs.ws.keep (hk _)) (hs.we.keep (hk _)) (Word.hist_congr rfl rfl)
    (Word.hist_congr rfl rfl) (fun _ => VClock.le_refl _) (fun _ h => h) (fun h => .inl h)
    (fun w hw _ => .inl (hsub w hw)) (fun _ h => h)
  have hs'' := hs'.retag (t := t) (g := (a, .none, x)) (hhold := by rw [upd_self]; exact id)
    (hcrit := fun h => by cases h)
    (hreg := fun i jr _ => by rw [upd_self]; exact ⟨fun ⟨_, h⟩ => (by simp at h), fun ⟨_, h⟩ => (by simp at h)⟩)
    (hera := fun _ _ _ _ h => by cases h)
    (hinc := by rw [upd_self]; exact ⟨fun h => (by cases h), fun h => (by cases h)⟩)
    (hwk := fun h => by cases h) (hwk' := fun _ => .inr hnone) (hld := fun i _ h => by cases h)
    (hpst := fun h => by rw [upd_self] at h; cases h)
    (hoff := fun y h1 h2 => by have := hs.off t y h1 h2; rwa [upd_self] at this)
    (htq := fun w hw he => (hnone w hw he).elim)
  rw [upd_upd] at hs''
  refine hP.pack (hl'.congr (fun u => ?_) (fun u => ?_) (fun u => ?_) fun h => ?_) hs'' ?_
  · unfold upd; split <;> rfl
  · unfold upd; split <;> rfl
  · unfold upd; split <;> rfl
  · show S.R _ h ↔ S.R _ h
    have : xs (fun u => (upd G t (a, SPh.none, x) u).2) = xs (fun u => (upd G t (a, SPh.wk, x) u).2) := by
      funext u; simp only [xs, upd]; split <;> rfl
    unfold Sem.R; rw [this]
  · have := hP.stable _ m _ t (a, .none, x) hu (Step.wake ws wk hsub) (by rw [upd_self]) (by rw [upd_self]) (fun h => by simp [SPh.waits] at h)
      (fun _ => hinS)
    rwa [upd_upd] at this

/-- `signal`'s futex wake at the epoch by `t` at `wk`: it goes on outside the condition. -/
theorem Fits.wakeE (hP : S.Fits P U) {G : ThreadId → SGh X} {m m' : Mem} {t : ThreadId} {a : LG}
    {x : X} (hinS : S.inS x) (hi : P.inv (upd G t (a, .wk, x)) m)
    (hw : ((Thread.futexWake S.WE.ptr (1 : BitVec 32).toNat).run { m with current := t }).run =
      some (.ok ((), m'))) :
    m'.current = t ∧ P.inv (upd G t (a, .none, x)) m' := by
  have hl' := (hP.split hi).1.wakeOff ptr_ne hw
  have hm' := Proto.modify_ok hw
  subst hm'
  have hi' := hP.cur t t m.woken hi
  exact ⟨rfl, hP.requeue hinS hi' (fun w hw => (Array.mem_filter.mp hw).1)
    (wakeE_none (hP.split hi').2.1) hl'⟩

/-- The holder is not in the futex queue. -/
theorem holds_notQ {G : ThreadId → SGh X} {m : Mem} {t : ThreadId} (hl : S.L.Inv G m)
    (hh : (G t).1.ph = .holds) : ∀ w ∈ m.waiters, w.2 = S.WE.ptr → w.1 ≠ t := fun w hw _ e => by
  rcases hl.fq w hw with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [e] at h <;> change (G t).1.ph = _ at h <;>
    rw [hh] at h <;> cases h

/-- The holder `t` leaves `signal` (`pst`) without a signal: no waiter is before a signal. -/
theorem Fits.pstNone (hP : S.Fits P U) {G : ThreadId → SGh X} {m : Mem} {t : ThreadId} {a : LG}
    {x : X} (hinS : S.inS x) (hi : P.inv (upd G t (a, .pst, x)) m) (ha : a.ph = .holds)
    (hn : ∀ R i jr sn e, (upd G t (a, .pst, x) R).2.1 = .reg i jr sn e → (S.WS.hist m).size ≠ jr + 1) :
    P.inv (upd G t (a, .none, x)) m := by
  obtain ⟨hl, hs, hu⟩ := hP.split hi
  have hh : (upd G t (a, SPh.pst, x) t).1.ph = .holds := by rw [upd_self]; exact ha
  have := hP.retag (t := t) (g := (a, .none, x)) hl hu (hs.retag (by rw [upd_self]; exact id)
    (fun h => by cases h)
    (fun i jr _ => by rw [upd_self]; exact ⟨fun ⟨_, h⟩ => (by simp at h), fun ⟨_, h⟩ => (by simp at h)⟩)
    (fun _ _ _ _ h => by cases h)
    (by rw [upd_self]; exact ⟨fun h => (by cases h), fun h => (by cases h)⟩) (fun h => by cases h)
    (fun h => by rw [upd_self] at h; cases h) (fun i _ h => by cases h)
    (fun _ => .inr fun R i jr sn e hR hs' => absurd hs' (hn R i jr sn e hR))
    (fun y h1 h2 => by have := hs.off t y h1 h2; rwa [upd_self] at this)
    (holds_notQ hl hh)) (by rw [upd_self]) (by rw [upd_self]) (fun h => by simp [SPh.waits] at h) hinS
  rwa [upd_upd] at this

/-- The holder `t` goes into `signal` (`pst`). -/
theorem Fits.toPst (hP : S.Fits P U) {G : ThreadId → SGh X} {m : Mem} {t : ThreadId} {a : LG}
    {x : X} (hinS : S.inS x) (hi : P.inv (upd G t (a, .none, x)) m) (ha : a.ph = .holds) :
    P.inv (upd G t (a, .pst, x)) m := by
  obtain ⟨hl, hs, hu⟩ := hP.split hi
  have hh : (upd G t (a, SPh.none, x) t).1.ph = .holds := by rw [upd_self]; exact ha
  have := hP.retag (t := t) (g := (a, .pst, x)) hl hu (hs.retag (by rw [upd_self]; exact id)
    (fun _ => ha)
    (fun i jr _ => by rw [upd_self]; exact ⟨fun ⟨_, h⟩ => (by simp at h), fun ⟨_, h⟩ => (by simp at h)⟩)
    (fun _ _ _ _ h => by cases h)
    (by rw [upd_self]; exact ⟨fun h => (by cases h), fun h => (by cases h)⟩) (fun h => by cases h)
    (fun h => by rw [upd_self] at h; cases h) (fun i _ h => by cases h)
    (fun h => by rw [upd_self] at h; cases h)
    (fun y h1 h2 => by have := hs.off t y h1 h2; rwa [upd_self] at this)
    (holds_notQ hl hh)) (by rw [upd_self]) (by rw [upd_self]) (fun h => by simp [SPh.waits] at h) hinS
  rwa [upd_upd] at this

/-- `signal`'s loop: `t` at `pst` read the state `b`; if `b` is not `(1, 0)`, no waiter is before
a signal. -/
def sInv (P : Proto Tgt (SGh X)) (t : ThreadId) (a : LG) (x : X) (D : Nat) (s : Io_Condition_signalLocals)
    (G : ThreadId → SGh X) (m : Mem) (d : Nat) : Prop :=
  d ≤ D ∧ m.current = t ∧ ∃ b, s.prev_state = Packed.ofBits b ∧ SV b ∧ P.inv (upd G t (a, .pst, x)) m ∧
    (b ≠ 1 → ∀ R i jr sn e, (upd G t (a, .pst, x) R).2.1 = .reg i jr sn e → (S.WS.hist m).size ≠ jr + 1)

/-- `signal`'s loop ends with `t` outside the condition. -/
def sPost (P : Proto Tgt (SGh X)) (t : ThreadId) (a : LG) (x : X) (D : Nat)
    (r : Io_Condition_signalExit × Io_Condition_signalLocals) (G : ThreadId → SGh X) (m : Mem)
    (d : Nat) : Prop :=
  d ≤ D ∧ (r.1 = .ret ∨ r.1 = .br10) ∧ m.current = t ∧ P.inv (upd G t (a, .none, x)) m

theorem sv_of {G : ThreadId → SGh X} {m : Mem} (hs : S.Inv G m) {j : Nat} {b : BitVec 32}
    (hj : j < (S.WS.hist m).size) (hv : (S.WS.hist m)[j]!.Val b) : SV b := by
  obtain ⟨v, h1, h2⟩ := hs.sv j hj
  rw [val_eq hv h2]; exact h1

/-- A read of the state by the holder: if it is not `(1, 0)`, no waiter is before a signal. -/
theorem read_noR {G : ThreadId → SGh X} {m : Mem} {t : ThreadId} {j : Nat} {b : BitVec 32}
    (hl : S.L.Inv G m) (hs : S.Inv G m) (hh : (G t).1.ph = .holds) (hv : (S.WS.hist m)[j]!.Val b)
    (hj : j < (S.WS.hist m).size) (hfl : Word.Floor (S.WS.hist m) (m.clocks[t]!) j) (hb : b ≠ 1) :
    ∀ R i jr sn e, (G R).2.1 = .reg i jr sn e → (S.WS.hist m).size ≠ jr + 1 := by
  intro R i jr sn e hR hsz
  have := reg_le hl hs hh hR hfl
  have hj' : j = jr := by omega
  subst hj'
  exact hb (val_eq hv (hs.era R i j sn e hR).s0)

theorem sig_body (hP : S.Fits P U) (t : ThreadId) (a : LG) (x : X) (ha : a.ph = .holds) (hinS : S.inS x) (io : Io) (D : Nat)
    (s : Io_Condition_signalLocals) (G : ThreadId → SGh X) (m : Mem) (d : Nat)
    (h : S.sInv P t a x D s G m d) :
    P.WP t ((Io_Condition_signal.loop11 (S.ptr.add 12) io).run s) (fun r G' m' d' =>
      if Io_Condition_signal.again11 r.1 then S.sInv P t a x D r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : Io_Condition_signalLocals) => 0) s)
      else sPost P t a x D r G' m' d') G m d := by
  obtain ⟨ps⟩ := s
  obtain ⟨hD, hc, b, hps, hsv, hi, hn⟩ := h
  simp only at hps
  subst hps
  unfold Io_Condition_signal.loop11
  simp only [StateT.run_bind, StateT.run_get, pure_bind, bind_assoc]
  by_cases hb : b = 1
  · subst hb
    refine WP.bind ?_
    rw [if_pos ((gt_sv hsv).mpr rfl)]
    simp only [StateT.run_bind, StateT.run_get]
    simp only [pure_bind]
    refine WP.bind (WP.callRC (fun e he => by
      change (add false (Packed.ofBits (1 : BitVec 32) : Io_Condition_State).signals 1).run = _ at he
      rw [add_sig] at he; cases he) fun v hv => ?_)
    have hv1 : v = 1 := by
      change (add false (Packed.ofBits (1 : BitVec 32) : Io_Condition_State).signals 1).run = _ at hv
      rw [add_sig] at hv; cases hv; rfl
    subst hv1
    rw [ptr_state]
    refine WP.bind (wp_weakCasAs hP (.inl rfl) (g := (a, .pst, x)) (by rw [ha]; decide) hi
      (fun b => ⟨_, ofBits_cst b⟩) fun k hk G₁ m₁ m' hg₁ hi₁ hw' hop hL hU =>
        ⟨fun hv hU' hh hacq => ?_, fun j b r hd hj hv hfl hh => ?_⟩)
    · -- the signal
      rw [bits1] at hv
      have hh' := hh
      rw [bits_sig] at hh'
      have hg₁' : upd G₁ t (a, .pst, x) = G₁ := by rw [← hg₁, upd_same]
      obtain ⟨hl₁, hs₁, -⟩ := hP.split hi₁
      have hh₁ : (G₁ t).1.ph = .holds := by rw [hg₁]; exact ha
      have hs₂ := hs₁.sig (by rw [hg₁]) hh₁ (crit_one hl₁ hs₁ hh₁) hop hw' hv hh'
      have hi₂ := hP.retag hL hU hs₂ rfl rfl (fun h => by simp [SPh.waits] at h) (by rw [hg₁]; exact hinS)
      rw [hg₁] at hi₂
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      simp only [StateT.run_bind]
      refine WP.bind (WP.bind (WP.callMC_ptrProject (hP.projE hi₂) ?_))
      refine WP.bind (wp_rmw hP (.inr rfl) (g := (a, .inc, x)) (by rw [ha]; decide) hi₂
        fun k₂ hk₂ G₂ m₂ m₃ old hg₂ hi₃ hv₃ hU₃ hh₃ hw₃ hop₃ hL₃ hu₃ => ?_)
      obtain ⟨hl₂, hs₃, -⟩ := hP.split hi₃
      have hh₂ : (G₂ t).1.ph = .holds := by rw [hg₂]; exact ha
      have hs₄ := hs₃.epoch (by rw [hg₂]) hh₂ (crit_one hl₂ hs₃ hh₂) hop₃ hw₃ hv₃ hh₃
      have hi₄ := hP.retag hL₃ hu₃ hs₄ rfl rfl (fun h => by simp [SPh.waits] at h) (by rw [hg₂]; exact hinS)
      rw [hg₂] at hi₄
      refine WP.bind (WP.callMC_ptrProject (hP.projE hi₄) ?_)
      refine WP.bind (WP.futexWakeC fun k₃ hk₃ => ⟨(a, .wk, x), hi₄, fun G₃ m₄ hg₃ hi₅ m₅ hw => ?_⟩)
      rw [← upd_same G₃ t, hg₃] at hi₅
      obtain ⟨hc₅, hi₆⟩ := hP.wakeE hinS hi₅ hw
      simp only [StateT.run_pure]
      refine WP.pure' (WP.pure' (WP.pure' ?_))
      simp only [Io_Condition_signal.again11, Bool.false_eq_true, ↓reduceIte]
      exact ⟨by omega, .inl rfl, hc₅, hi₆⟩
    · -- no signal: `t` read write `j`
      obtain ⟨hl₁, hs₁, -⟩ := hP.split hi₁
      have hh₁ : (G₁ t).1.ph = .holds := by rw [hg₁]; exact ha
      have hs₂ := hs₁.opKeep (.inl rfl) hop hw' hh
      have hi₂ : P.inv G₁ m' := hP.pack hL hs₂ hU
      have hr : r = Packed.ofBits b := by rw [ofBits_cst] at hd; cases hd; rfl
      simp only [Option.isSome_some, ↓reduceIte]
      simp only [StateT.run_bind]
      refine WP.bind (WP.bind (show P.WP t ((callRC (optPayload (some r)) : CM Tgt _ _).run _) _ _ _ _ from
        WP.callRC_ok (v := r) rfl ?_))
      simp only [StateT.run_pure]
      refine WP.pure' (WP.pure' (WP.pure' ?_))
      simp only [Io_Condition_signal.again11, ↓reduceIte]
      refine ⟨⟨by omega, hop.current, b, hr, sv_of hs₁ hj hv, by rw [← hg₁, upd_same]; exact hi₂, fun hb => ?_⟩,
        .inl (by omega)⟩
      intro R i jr sn e hR
      rw [hh]; rw [← hg₁, upd_same] at hR
      exact read_noR hl₁ hs₁ hh₁ hv hj hfl hb R i jr sn e hR
  · -- `(0, 0)` or `(1, 1)`: no signal
    rw [if_neg (fun h => hb ((gt_sv hsv).mp h))]
    simp only [StateT.run_pure, pure_bind]
    refine WP.pure' ?_
    simp only [Io_Condition_signal.again11, Bool.false_eq_true, ↓reduceIte]
    exact ⟨hD, .inr rfl, hc, hP.pstNone hinS hi ha (hn hb)⟩

/-- `signal` by the holder `t`: it goes on outside the condition, with the same lock part. -/
theorem signal_spec (hP : S.Fits P U) (t : ThreadId) (a : LG) (x : X) (ha : a.ph = .holds) (hinS : S.inS x)
    (io : Io) (G : ThreadId → SGh X) (m : Mem) (d : Nat) (hi : P.inv (upd G t (a, .pst, x)) m) :
    P.WP t (Io_Condition_signal (S.ptr.add 12) io) (fun _ G' m' d' => d' ≤ d ∧ m'.current = t ∧
      P.inv (upd G' t (a, .none, x)) m') G m d := by
  unfold Io_Condition_signal
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind]
  simp only [StateT.run_pure, pure_bind, bind_assoc]
  rw [ptr_state]
  refine WP.bind (wp_loadAs hP (.inl rfl) (g := (a, .pst, x)) (by rw [ha]; decide) hi
    (fun b => ⟨_, ofBits_cst b⟩) fun k hk G₁ m₁ m' b r j hg₁ hi₁ hd hj hv hfl hh hw' hop hL hU => ?_)
  obtain ⟨hl₁, hs₁, -⟩ := hP.split hi₁
  have hh₁ : (G₁ t).1.ph = .holds := by rw [hg₁]; exact ha
  have hi₂ : P.inv G₁ m' := hP.pack hL (hs₁.opKeep (.inl rfl) hop hw' hh) hU
  have hr : r = Packed.ofBits b := by rw [ofBits_cst] at hd; cases hd; rfl
  subst hr
  simp only [StateT.run_bind]
  simp only [StateT.run_modify, pure_bind]
  refine WP.bind (WP.mono ?_ (WP.loop _ _ (sInv P t a x d) (fun _ => 0) (sPost P t a x d)
    (sig_body hP t a x ha hinS io d) _ G₁ m' k ⟨by omega, hop.current, b, rfl, sv_of hs₁ hj hv,
      by rw [← hg₁, upd_same]; exact hi₂, fun hb R i jr sn e hR => ?_⟩))
  · rintro ⟨e, s'⟩ G₂ m₂ d₂ ⟨hd₂, he, hc₂, hi₃⟩
    rcases he with rfl | rfl <;>
    · simp only [StateT.run_pure]
      exact WP.pure' (WP.pure' ⟨hd₂, hc₂, hi₃⟩)
  · rw [hh]; rw [← hg₁, upd_same] at hR; exact read_noR hl₁ hs₁ hh₁ hv hj hfl hb R i jr sn e hR

/-! ## The permit count -/

theorem enc_u64 : Enc.size (BitVec 64) = 8 := rfl

/-- Two `pts` at one pointer, in one heap, have the same value. -/
theorem pts_same {T : Type} [Enc T] {p : Ptr} {a : Nat} {v w : T} {h₁ h₂ M : Heap}
    (hv : pts p a v h₁) (s₁ : h₁.Sub M) (hw : pts p a w h₂) (s₂ : h₂.Sub M) : v = w := by
  obtain ⟨A, Sz, K, bs, -, hs, hd, ⟨b, hb, h0, ho⟩, -⟩ := hv
  obtain ⟨A', Sz', K', bs', -, hs', hd', ⟨b', hb', -, ho'⟩, -⟩ := hw
  rw [hb] at hb'; cases hb'
  have hbs : bs = bs' := by
    refine Array.ext (by rw [hs, hs']) fun i h1 h2 => ?_
    have e₁ := ho (b, p.off.toNat + i); have e₂ := ho' (b, p.off.toNat + i)
    simp only [true_and, Nat.le_add_right, Nat.add_lt_add_iff_left, h1, h2, ↓reduceIte,
      Nat.add_sub_cancel_left] at e₁ e₂
    have := (s₁ _ _ e₁).symm.trans (s₂ _ _ e₂)
    simp only [Option.some.injEq, Cell.mk.injEq] at this
    rw [getElem!_pos bs i h1, getElem!_pos bs' i h2] at this; exact this.1
  subst hbs
  have := congrArg ExceptT.run (hd.symm.trans hd')
  simp only [pure, ExceptT.pure, ExceptT.run_mk, Option.some.injEq, Except.ok.injEq] at this
  exact this

/-- Two `pts` of the permit count in one heap have the same value. -/
theorem pts_eq {v w : BitVec 64} {h₁ h₂ M : Heap} (hv : pts S.ptr 8 v h₁) (s₁ : h₁.Sub M)
    (hw : pts S.ptr 8 w h₂) (s₂ : h₂.Sub M) : v = w :=
  pts_same hv s₁ hw s₂

theorem sub_union_left {h₁ h₂ M : Heap} (h : (h₁ ∪ h₂).Sub M) : h₁.Sub M := fun l c hl =>
  h l c (by simp [hl])

/-- The condition's invariant reads of each thread only its place in the condition, its place in
the mutex and its part. -/
theorem Inv.congrG {G G' : ThreadId → SGh X} {m : Mem} (hi : S.Inv G m)
    (h1 : ∀ u, (G' u).2.1 = (G u).2.1) (h2 : ∀ u, (G' u).1.ph = .holds ↔ (G u).1.ph = .holds)
    (h3 : ∀ u x, S.o + 12 ≤ x → x < S.o + 20 → (G' u).1.part (S.b, x) = none) : S.Inv G' m := by
  have hhb : ∀ c, S.HBH G m c → S.HBH G' m c := fun c h =>
    HBH.mono h (fun _ => VClock.le_refl _) (fun u hu => .inl ((h2 u).mpr hu)) (fun _ h => h) (fun _ h => h)
  refine ⟨hi.ws, hi.we, hi.sv, fun u v i jr sn e i' jr' sn' e' hu hv => ?_, fun hn => hi.idle ?_,
    fun u i jr sn e hu => ?_, hhb _ hi.hbE, fun u hu => ?_, fun u i _ hu => ?_,
    fun u hu v i jr sn e hv => ?_, fun u hu v i jr sn e hv => ?_, fun w hw he => ?_, h3⟩
  · rw [h1] at hu hv; exact hi.one u v i jr sn e i' jr' sn' e' hu hv
  · intro u i jr sn e hu; exact hn u i jr sn e (by rw [h1]; exact hu)
  · rw [h1] at hu
    exact (hi.era u i jr sn e hu).mono rfl rfl (fun _ => VClock.le_refl _) hhb (fun h => .inl h)
      fun v p _ hv => ⟨v, by rw [h1]; exact hv⟩
  · rw [h1] at hu; exact (h2 u).mpr (hi.crit u hu)
  · rw [h1] at hu; exact hi.ld u i _ hu
  · rw [h1] at hu hv; exact hi.inc u hu v i jr sn e hv
  · rw [h1] at hu hv; exact hi.wk u hu v i jr sn e hv
  · obtain ⟨i, jr, ee, a, b⟩ := hi.q w hw he
    refine ⟨i, jr, ee, by rw [h1]; exact a, ?_⟩
    rcases b with b | ⟨v, hv⟩
    · exact .inl b
    · exact .inr ⟨v, by rw [h1]; exact hv⟩

/-- The holder `t`'s step `c` on the permit count, `v` to `v'`; the rest of its bytes is the
frame. Its part becomes `pa'` and its ghost value `x'`, as `hmv` says. -/
theorem wp_cnt (hP : S.Fits P U) {β : Type} {c : MemM β} {s : σ} {t : ThreadId}
    {G : ThreadId → SGh X} {m : Mem} {n : Nat} {pa hL : Heap} {Mv : Heap → Prop} {sp : SPh} {x x' : X}
    {v v' : BitVec 64} {r₀ : β} {Q : β × σ → (ThreadId → SGh X) → Mem → Nat → Prop}
    (hi : P.inv (upd G t (⟨.holds, pa, hL⟩, sp, x)) m) (hc : m.current = t)
    (ht : TTriple (pts S.ptr 8 v) c (fun r => ⌜r = r₀⌝ ∗ pts S.ptr 8 v'))
    (hv : S.pv (xs fun u => (upd G t (⟨.holds, pa, hL⟩, sp, x) u).2) = v)
    (hmv : ∀ hr, S.Res (xs fun u => (upd G t (⟨.holds, pa, hL⟩, sp, x) u).2) hr →
      Heap.Disjoint pa hr → ∃ pa' hr', pa' ∪ hr' = pa ∪ hr ∧ Heap.Disjoint pa' hr' ∧
        S.Res (xs fun u => (upd G t (⟨.holds, pa, hL⟩, sp, x') u).2) hr' ∧
        S.pv (xs fun u => (upd G t (⟨.holds, pa, hL⟩, sp, x') u).2) = v' ∧ Mv pa')
    (hpz : v' = v ∨ v ≠ 0 ∨ sp = .pst)
    (hU : ∀ m' h₁ h₂ pa', Mv pa' → U (upd G t (⟨.holds, pa, h₁⟩, sp, x)) m' →
      U (upd G t (⟨.holds, pa', h₂⟩, sp, x')) m')
    (h : ∀ m' pa' hL', Mv pa' → m'.current = t → m'.threads = m.threads →
      P.inv (upd G t (⟨.holds, pa', hL'⟩, sp, x')) m' → Q (r₀, s) G m' n) :
    P.WP t ((liftM c : CM Tgt σ β).run s) Q G m n := by
  subst hv
  obtain ⟨hl, hs, hu⟩ := hP.split hi
  have hh : S.L.ph (upd G t (⟨.holds, pa, hL⟩, sp, x) t) = .holds := by rw [upd_self]; rfl
  obtain ⟨htl, hjt⟩ := hl.live t (by rw [hh]; decide)
  have hres := hl.res t hh
  rw [show S.L.held (upd G t (⟨.holds, pa, hL⟩, sp, x) t) = hL by rw [upd_self]; rfl] at hres
  obtain ⟨hp, hr, hdpr, rfl, hpp, hrr⟩ := hres
  have hpd := hl.pdisj t
  rw [show S.L.part (upd G t (⟨.holds, pa, hp ∪ hr⟩, sp, x) t) = pa by rw [upd_self]; rfl,
    show S.L.held (upd G t (⟨.holds, pa, hp ∪ hr⟩, sp, x) t) = hp ∪ hr by rw [upd_self]; rfl] at hpd
  obtain ⟨hdp, hdr⟩ := Heap.disjoint_union_right.mp hpd
  have hown : S.L.own (upd G t (⟨.holds, pa, hp ∪ hr⟩, sp, x)) m t = pa ∪ (hp ∪ hr) := by
    rw [Lock.own_live hjt, upd_self]; rfl
  have hown2 : pa ∪ (hp ∪ hr) = hp ∪ (pa ∪ hr) := Heap.union_left_comm hdp
  have hdp' : Heap.Disjoint hp (pa ∪ hr) := Heap.disjoint_union_right.mpr ⟨hdp.symm, hdpr⟩
  refine WP.liftM_owned (TTriple.frame (R := fun h => h = pa ∪ hr) ht) hl.own hc htl
    (by rw [hown, hown2]; exact ⟨hp, _, hdp', rfl, hpp, rfl⟩) fun a m' hQ _ ho' hq hst hm' hd => ?_
  obtain ⟨hp', hrest, hd', rfl, hq1, rfl⟩ := hq
  obtain ⟨rfl, hpp'⟩ := sep_lift.mp hq1
  obtain ⟨pa', hr₂, he, hd₂, hres₂, hpv₂, hmv'⟩ := hmv hr hrr hdr
  have hd'' : Heap.Disjoint hp' (pa' ∪ hr₂) := by rw [he]; exact hd'
  obtain ⟨hdp₂, hdr₂⟩ := Heap.disjoint_union_right.mp hd''
  have hQe : pa' ∪ (hp' ∪ hr₂) = hp' ∪ (pa ∪ hr) := by
    rw [Heap.union_left_comm hdp₂.symm, he]
  rw [hown] at hst hm' hd
  have hl' := hl.stepIn (g := (({ ph := .holds, part := pa', held := hp' ∪ hr₂ } : LG), sp, x')) hc hjt
    (by show Owned (upd _ t (pa' ∪ (hp' ∪ hr₂))) m'; rw [hQe]; exact ho')
    (by rw [hown]; exact hst) (by rw [hown]; show _ = (pa' ∪ (hp' ∪ hr₂)) ∪ _; rw [hQe]; exact hm')
    (by rw [hown]; show Heap.Disjoint (pa' ∪ (hp' ∪ hr₂)) _; rw [hQe]; exact hd)
    (by rw [upd_self]; rfl) (Heap.disjoint_union_right.mpr ⟨hdp₂.symm, hd₂⟩) (fun h => absurd rfl h)
    (fun h => absurd hh h) (fun _ => ?_)
  · rw [upd_upd] at hl'
    have hpzm : S.PZ m → S.PZ m' ∨
        ∃ u, (upd G t (⟨.holds, pa, hp ∪ hr⟩, sp, x) u).2.1 = .pst := by
      intro ⟨hz, hzp, hzs⟩
      have hps : hp.Sub m.heap := fun l c hl₁ => by
        have := hl.own.sub t l c
        rw [hown] at this
        refine this ?_
        rcases hdp l with e | e
        · simp [e, hl₁]
        · rw [hl₁] at e; cases e
      have hv0 := pts_eq hpp hps hzp hzs
      rcases hpz with rfl | hne | hpst
      · refine .inl ⟨hp', by rw [hv0] at hpp'; exact hpp', fun l c hl => ?_⟩
        rw [hm']; simp [hl]
      · exact absurd hv0 hne
      · exact .inr ⟨t, by rw [upd_self]; exact hpst⟩
    have hs' := (hs.stepIn hl (by rw [hown]; exact hst) (by rw [hown]; exact hm')
      (by rw [hown]; exact hd) hpzm).congrG (G' := upd G t (⟨.holds, pa', hp' ∪ hr₂⟩, sp, x'))
      (fun u => by unfold upd; split <;> rfl) (fun u => by unfold upd; split <;> exact Iff.rfl)
      (fun u y h1 h2 => ?_)
    · have hu' := hP.own _ m m' t (⟨.holds, pa, hp' ∪ hr⟩, sp, x) _ hl hu
        (by rw [hown]; exact hst) (by rw [hown]; exact hm') (by rw [hown]; exact hd)
        (by rw [upd_self]) rfl (by rw [upd_self]) (by rw [upd_self])
        (Heap.union_left_comm (Heap.disjoint_union_right.mp hd').1.symm)
      rw [upd_upd] at hu'
      exact h m' pa' _ hmv' (hst.current.trans hc) hst.threads (hP.pack hl' hs' (hU m' _ _ pa' hmv' hu'))
    · unfold upd; split
      · rename_i e; subst e
        show pa' (S.b, y) = none
        have hpe := congrFun he (S.b, y)
        have hpa := hs.off u y h1 h2
        rw [upd_self] at hpa
        have hro := S.res_off _ _ hrr y (by omega) h2
        simp only [Heap.union_apply, show pa (S.b, y) = none from hpa, hro, Option.none_or]
          at hpe
        cases e : pa' (S.b, y) with
        | none => rfl
        | some _ => rw [e] at hpe; cases hpe
      · rename_i hne; have := hs.off u y h1 h2; rwa [upd_ne _ _ hne] at this
  · show S.R _ (hp' ∪ hr₂)
    have hx : xs (fun u => (upd (upd G t (⟨.holds, pa, hp ∪ hr⟩, sp, x)) t
        (⟨.holds, pa', hp' ∪ hr₂⟩, sp, x') u).2) =
        xs (fun u => (upd G t (⟨.holds, pa, hp ∪ hr⟩, sp, x') u).2) := by
      rw [upd_upd]; funext u; simp only [xs, upd]; split <;> rfl
    unfold Sem.R; rw [hx, hpv₂]
    exact ⟨hp', hr₂, hdr₂, rfl, hpp', hres₂⟩


/-! ## The waiter's futex wait at the epoch -/

/-- The mutex's resource reads only the second part of the ghost values. -/
theorem R_upd1 {G : ThreadId → SGh X} {t : ThreadId} {g : SGh X} (h2 : g.2 = (G t).2) (hL : Heap) :
    S.L.R (upd G t g) hL ↔ S.L.R G hL := by
  show S.R _ hL ↔ S.R _ hL
  have : (fun u => (upd G t g u).2) = fun u => (G u).2 := by
    funext u; unfold upd; split
    · rename_i e; subst e; exact h2
    · rfl
  rw [this]

/-- A holder is not asleep, has not ended and does not wait at a join. -/
theorem holds_runs (hP : S.Fits P U) {G : ThreadId → SGh X} {m : Mem} (hi : P.inv G m) {v : ThreadId}
    (hv : (G v).1.ph = .holds)
    (hall : ∀ u < m.threads.size, P.fin (G u) ∨ m.waiters.any (·.1 == u) = true ∨ P.joins (G u)) :
    False := by
  obtain ⟨hl, -, -⟩ := hP.split hi
  have hlv := (hl.live v (by change (G v).1.ph ≠ _; rw [hv]; decide)).1
  rcases hall v hlv with h | h | h
  · have := hP.fin _ h; rw [hv] at this; cases this
  · obtain ⟨k, hk, hek⟩ := Array.any_eq_true.mp h
    have hw := Array.getElem_mem hk
    have he : m.waiters[k].1 = v := by simpa using hek
    rcases hl.fq _ hw with ⟨-, h'⟩ | ⟨-, h'⟩ <;> rw [he] at h' <;> change (G v).1.ph = _ at h' <;>
      rw [hv] at h' <;> cases h'
  · have := hP.joins _ h; rw [hv] at this; cases this

/-- No deadlock while a thread waits at the condition, at `away`. -/
theorem live_reg (hP : S.Fits P U) {G : ThreadId → SGh X} {m : Mem} {r i jr : Nat} {sn : Bool}
    {e : BitVec 32} (hi : P.inv G m) (hr : (G r).2.1 = .reg i jr sn e) (hph : (G r).1.ph = .away) :
    P.Live r G m := by
  intro hw hall
  obtain ⟨hl, hs, -⟩ := hP.split hi
  have hcrit : ∀ v, (G v).2.1.crit = true → False := fun v h => holds_runs hP hi (hs.crit v h) hall
  have he := hs.era r i jr sn e hr
  rcases he.ssz with h1 | h2
  · rcases he.pz h1 with hz | ⟨v, hv⟩
    · exact hP.live G m r i jr sn e hi hr hz hall
    · exact hcrit v (by rw [hv]; rfl)
  · rcases he.esz with h3 | ⟨h3, -, -⟩
    · obtain ⟨v, hv⟩ := he.pend h2 h3; exact hcrit v (by rw [hv]; rfl)
    · obtain ⟨k, hk, hek⟩ := Array.any_eq_true.mp hw
      have hwm := Array.getElem_mem hk
      have hr' : m.waiters[k].1 = r := by simpa using hek
      rcases hP.waits G m _ i jr sn e hi hwm (by rw [hr', hr]) with hL | hE
      · rcases hl.fq _ hwm with ⟨-, h'⟩ | ⟨h'', -⟩
        · rw [hr'] at h'; change (G r).1.ph = _ at h'; rw [hph] at h'; cases h'
        · exact h'' hL
      · obtain ⟨i', jr', e', h1, h2⟩ := hs.q _ hwm hE
        rw [hr', hr] at h1
        simp only [SPh.reg.injEq] at h1
        obtain ⟨rfl, -, -, -⟩ := h1
        rcases h2 with h2 | ⟨v, hv⟩
        · omega
        · exact hcrit v (by rw [hv]; rfl)

/-- A change of the futex queue at the epoch only, and of the woken threads. -/
theorem Step.sleep {t : ThreadId} {m : Mem} (ws : Array (ThreadId × Ptr)) (wk : Array ThreadId)
    (hw : ∀ w ∈ ws, w ∈ m.waiters ∨ w.2 = S.WE.ptr) :
    S.Step t m { m with current := t, waiters := ws, woken := wk } :=
  ⟨rfl, rfl, fun _ => VClock.le_refl _, rfl, fun _ _ => rfl, fun _ he => .inl he,
    fun w h _ h2 => (hw w h).resolve_right h2, rfl, fun _ _ _ _ _ => Iff.rfl, fun _ hl => .inl hl⟩

/-- The waiter `t`'s futex wait at the epoch, with the value `e` of epoch write `i`. It sleeps
only while the epoch is write `i`; it goes on at the same place. -/
theorem wp_ewait (hP : S.Fits P U) {s : σ} {t : ThreadId} {G : ThreadId → SGh X} {m : Mem}
    {n : Nat} {pa : Heap} {i jr : Nat} {e : BitVec 32} {x : X} {io : Io} (hinS : S.inS x)
    (hi : P.inv (upd G t (⟨.out, pa, Heap.empty⟩, .reg i jr false e, x)) m)
    {Q : Unit × σ → (ThreadId → SGh X) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m', m'.current = t →
      P.inv (upd G₁ t (⟨.out, pa, Heap.empty⟩, .reg i jr false e, x)) m' → Q ((), s) G₁ m' k) :
    P.WP t ((futexWaitC io S.WE.ptr e : CM Tgt σ Unit).run s) Q G m n := by
  have hgo : ∀ (G₀ : ThreadId → SGh X) m₀ (p p' : LPh), (G₀ t).1 = ⟨p, pa, Heap.empty⟩ →
      (p = .holds ↔ p' = .holds) → S.inS (G₀ t).2.2 → S.Inv G₀ m₀ → U G₀ m₀ →
      S.L.Inv (upd G₀ t (⟨p', pa, Heap.empty⟩, (G₀ t).2)) m₀ →
      P.inv (upd G₀ t (⟨p', pa, Heap.empty⟩, (G₀ t).2)) m₀ := by
    intro G₀ m₀ p p' hg hh hx hs hu hl₀
    refine hP.pack hl₀ (hs.congrG (fun u => by unfold upd; split <;> simp_all)
      (fun u => by unfold upd; split <;> simp_all) fun u y h1 h2 => ?_)
      (hP.stable G₀ m₀ m₀ t _ hu (Step.refl t m₀) rfl (by rw [hg]) (fun h => .inl h) (fun _ => hx))
    unfold upd; split
    · rename_i e; subst e; have := hs.off u y h1 h2; rw [hg] at this; exact this
    · exact hs.off u y h1 h2
  refine WP.futexWaitC fun k hk => ⟨(⟨.away, pa, Heap.empty⟩, .reg i jr false e, x), ?_,
    fun G₁ m₁ hg₁ hi₁ => ?_⟩
  · obtain ⟨hl, hs, hu⟩ := hP.split hi
    have hl' := hl.ghost (t := t) (g := (⟨.away, pa, Heap.empty⟩, .reg i jr false e, x))
      (by rw [upd_self]; rfl) (.inr (.inr rfl)) (by rw [upd_self]; rfl) rfl
      (fun _ => hl.live t (by rw [upd_self]; exact fun h => by cases h)) fun hL hR => (R_upd1 (by rw [upd_self]) hL).mpr hR
    have := hgo _ m .out .away (by rw [upd_self]) (by simp) (by rw [upd_self]; exact hinS) hs hu (by rw [upd_self]; exact hl')
    rwa [upd_self, upd_upd] at this
  have hph : (G₁ t).1.ph = .away := by rw [hg₁]
  obtain ⟨hl₁, hs₁, hu₁⟩ := hP.split hi₁
  refine ⟨fun _ => live_reg hP hi₁ (by rw [hg₁]) hph, fun hq0 => ⟨fun _ => ?_, fun b m' hr => ?_⟩⟩
  · by_cases hwk : ({ m₁ with current := t } : Mem).woken.contains
      ({ m₁ with current := t } : Mem).current = true
    · exact ⟨_, _, futexWait_run_woken hwk⟩
    · obtain ⟨blk, hb, -, -, ha, -⟩ := hs₁.we.access
      obtain ⟨v, hv⟩ := hs₁.we.val
      rw [Word.holds_bytes hb] at hv
      exact ⟨_, _, futexWait_run_go (by simpa using hwk) ha hv⟩
  have hl := hl₁.waitOff (t := t) (by change (G₁ t).1.ph = _; exact hph) ptr_ne hq0 hr
  have hout : ∀ m₂ : Mem, m₂.current = t → S.L.Inv (upd G₁ t (S.L.set (G₁ t) .out Heap.empty)) m₂ →
      S.Inv G₁ m₂ → U G₁ m₂ → Q ((), s) G₁ m₂ k := fun m₂ hc hl₂ hs₂ hu₂ => by
    have := hgo G₁ m₂ .away .out (by rw [hg₁]) (by simp) (by rw [hg₁]; exact hinS) hs₂ hu₂ (by rw [hg₁] at hl₂ ⊢; exact hl₂)
    rw [hg₁] at this
    exact h k hk G₁ m₂ hc this
  rcases futexWait_ok hr with ⟨-, rfl, rfl⟩ | ⟨-, bid, blk, o, v, ha, hv, ⟨hve, rfl, rfl⟩ | ⟨-, rfl, rfl⟩⟩
  · simp only [Bool.false_eq_true, ↓reduceIte] at hl ⊢
    have := hP.stable G₁ m₁ _ t (G₁ t) hu₁ (Step.cur t m₁ t (m₁.woken.erase t)) rfl rfl (fun h => .inl h)
      (fun h => by rcases h with h | h <;> exact absurd rfl h)
    rw [upd_same] at this
    exact hout _ rfl hl.2 (hs₁.congr rfl rfl rfl rfl rfl rfl) this
  · simp only [↓reduceIte] at hl ⊢
    refine ⟨?_, ?_⟩
    rotate_left
    · have hl := hl₁.spuriousOff (t := t) (by change (G₁ t).1.ph = _; exact hph) hq0
      have := hP.stable G₁ m₁ _ t (G₁ t) hu₁ (Step.cur t m₁ t m₁.woken) rfl rfl (fun h => .inl h)
        (fun h => by rcases h with h | h <;> exact absurd rfl h)
      rw [upd_same] at this
      exact hout _ rfl hl.2 (hs₁.congr rfl rfl rfl rfl rfl rfl) this
    obtain ⟨blk₀, hb₀, -, -, ha₀, -⟩ := hs₁.we.access
    have : ({ m₁ with current := t } : Mem).access S.WE.ptr 4 4 = m₁.access S.WE.ptr 4 4 := rfl
    rw [this, ha₀] at ha
    cases ha
    have hE : S.WE.Holds m₁ e := by
      rw [Word.holds_bytes hb₀, ← show (Packed.toBits e).setWidth 32 = e from BitVec.setWidth_eq e,
        ← hve]; exact hv
    have hlast := (hs₁.we.holds_last).mp hE
    have he := hs₁.era t i jr false e (by rw [hg₁])
    have hsz : (S.WE.hist m₁).size = i + 1 := by
      rcases he.esz with h1 | ⟨h1, -, -⟩
      · exact h1
      · rw [h1, show i + 2 - 1 = i + 1 by omega] at hlast
        have h2 := val_eq (he.eval.2 h1) hlast
        have := congrArg BitVec.toNat h2
        simp [BitVec.toNat_add] at this; omega
    have hk : ∀ W : Word 32 4, W.Keep m₁ { m₁ with current := t, waiters := m₁.waiters.push (t, S.WE.ptr) } :=
      fun _ => Word.keep_same m₁ t m₁.seen m₁.nextMsg _ m₁.woken m₁.groups
    refine hP.pack hl (hs₁.mono (hs₁.ws.keep (hk _)) (hs₁.we.keep (hk _)) (Word.hist_congr rfl rfl)
      (Word.hist_congr rfl rfl) (fun _ => VClock.le_refl _) (fun _ h => h) (fun h => .inl h)
      (fun w hw _ => ?_) (fun _ h => h)) ?_
    · rcases Array.mem_push.mp hw with hw | rfl
      · exact .inl hw
      · exact .inr ⟨i, jr, e, by rw [hg₁], hsz⟩
    · have := hP.stable G₁ m₁ _ t (G₁ t) hu₁ (Step.sleep (t := t) (m := m₁) (m₁.waiters.push (t, S.WE.ptr)) m₁.woken fun w hw => by
        rcases Array.mem_push.mp hw with hw | rfl
        · exact .inl hw
        · exact .inr rfl) rfl rfl (fun h => .inl h)
        (fun h => by rcases h with h | h <;> exact absurd rfl h)
      rwa [upd_same] at this
  · simp only [Bool.false_eq_true, ↓reduceIte] at hl ⊢
    have := hP.stable G₁ m₁ _ t (G₁ t) hu₁ (Step.cur t m₁ t m₁.woken) rfl rfl (fun h => .inl h)
      (fun h => by rcases h with h | h <;> exact absurd rfl h)
    rw [upd_same] at this
    exact hout _ rfl hl.2 (hs₁.congr rfl rfl rfl rfl rfl rfl) this


/-! ## `Condition.wait` by a holder that saw no permit -/

theorem dbg_true : (debug_assert true).run = some (.ok ()) := rfl
theorem lt_w : lt false (Packed.ofBits (0 : BitVec 32) : Io_Condition_State).waiters (65535 : BitVec 16) =
    true := by decide +kernel
theorem bits_add1 : RmwOp.add.apply false (0 : BitVec 32)
    (Packed.toBits (Packed.ofBits (1 : BitVec 32) : Io_Condition_State)) = 1 := by decide +kernel

/-- The holder's bytes are in the heap. -/
theorem held_sub (hP : S.Fits P U) {G : ThreadId → SGh X} {m : Mem} {t : ThreadId} {pa hL : Heap}
    {sp : SPh} {x : X} (hi : P.inv (upd G t (⟨.holds, pa, hL⟩, sp, x)) m) : hL.Sub m.heap := by
  obtain ⟨hl, -, -⟩ := hP.split hi
  have hh : S.L.ph (upd G t (⟨.holds, pa, hL⟩, sp, x) t) = .holds := by rw [upd_self]; rfl
  obtain ⟨-, hjt⟩ := hl.live t (by rw [hh]; decide)
  have hs := hl.own.sub t
  rw [Lock.own_live hjt, upd_self] at hs
  have hpd := hl.pdisj t
  rw [upd_self] at hpd
  change Heap.Disjoint pa hL at hpd
  change (pa ∪ hL).Sub m.heap at hs
  intro l c hl₁
  refine hs l c ?_
  show (pa ∪ hL) l = some c
  rcases hpd l with e | e
  · simp [e, hl₁]
  · rw [hl₁] at e; cases e

/-- A thread at `out` is not in the futex queue. -/
theorem out_notQ (hP : S.Fits P U) {G : ThreadId → SGh X} {m : Mem} {t : ThreadId} (hi : P.inv G m)
    (ho : (G t).1.ph = .out) : ∀ w ∈ m.waiters, w.2 = S.WE.ptr → w.1 ≠ t := fun w hw _ e => by
  rcases (hP.split hi).1.fq w hw with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [e] at h <;>
    change (G t).1.ph = _ at h <;> rw [ho] at h <;> cases h

/-- The holder `t`'s acquire load of the epoch, outside the condition: it reads the newest write
`i`, with the value `e`, and goes to `ld i e`. -/
theorem wp_ldE (hP : S.Fits P U) {s : σ} {t : ThreadId} {G : ThreadId → SGh X} {m : Mem} {n : Nat}
    {a : LG} {x : X} (ha : a.ph = .holds) (hwx : S.wx x) (hinS : S.inS x) (hi : P.inv (upd G t (a, .none, x)) m)
    {Q : BitVec 32 × σ → (ThreadId → SGh X) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' i e, m'.current = t → P.inv (upd G₁ t (a, .ld i e, x)) m' →
      Q (e, s) G₁ m' k) :
    P.WP t ((atomicLoadC (n := 32) .acquire 4 S.WE.ptr : CM Tgt σ (BitVec 32)).run s) Q G m n := by
  refine wp_load hP (.inr rfl) (g := (a, .none, x)) (by rw [ha]; decide) hi
    fun k hk G₁ m₁ m' v j hg₁ hi₁ hj hv hfl _ hh hw' hop hL hU => ?_
  obtain ⟨hl₁, hs₁, -⟩ := hP.split hi₁
  have hh₁ : (G₁ t).1.ph = .holds := by rw [hg₁]; exact ha
  have hs' := hs₁.opKeep (.inr rfl) hop hw' hh
  have hpos := hist_pos hs₁.we
  have hjl : j = (S.WE.hist m₁).size - 1 := by
    have := hfl _ (by omega) (HBH.le hl₁ hh₁ hs₁.hbE); omega
  have hrt := hs'.retag (t := t) (g := (a, .ld j v, x)) (by rw [hg₁]; exact id) (fun _ => ha)
    (fun i jr e => by rw [hg₁]; exact ⟨fun ⟨_, h⟩ => (by cases h), fun ⟨_, h⟩ => (by cases h)⟩)
    (fun _ _ _ _ h => by cases h) (by rw [hg₁]; exact ⟨fun h => (by cases h), fun h => (by cases h)⟩)
    (fun h => by cases h) (fun h => by rw [hg₁] at h; cases h)
    (fun i e h => by
      simp only [SPh.ld.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      rw [hh]; exact ⟨by omega, hv⟩)
    (fun h => by rw [hg₁] at h; cases h)
    (fun y h1 h2 => by have := hs₁.off t y h1 h2; rwa [hg₁] at this)
    (holds_notQ hL hh₁)
  exact h k hk G₁ m' j v hop.current (hP.retag hL hU hrt (by rw [hg₁]) (by rw [hg₁]) (fun _ => .inr hwx) hinS)


/-- The holder `t`'s `waiters += 1` at `ld i e`, while no other thread waits at the condition and
the permit count in its bytes `hL` is 0: it waits at the condition (state write `jr`). -/
theorem wp_regS (hP : S.Fits P U) {s : σ} {t : ThreadId} {G : ThreadId → SGh X} {m : Mem} {n : Nat}
    {pa hL : Heap} {x : X} {i : Nat} {e : BitVec 32} (hinS : S.inS x)
    (hi : P.inv (upd G t (⟨.holds, pa, hL⟩, .ld i e, x)) m)
    (hz : ∃ hp, pts S.ptr 8 (0 : BitVec 64) hp ∧ hp.Sub hL)
    (hone : ∀ G' m', P.inv G' m' → (G' t).2.2 = x → (G' t).1.ph = .holds → S.PZ m' → ∀ u, u ≠ t →
      ∀ i jr sn e, (G' u).2.1 ≠ .reg i jr sn e)
    {Q : Io_Condition_State × σ → (ThreadId → SGh X) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' jr, m'.current = t →
      P.inv (upd G₁ t (⟨.holds, pa, hL⟩, .reg i jr false e, x)) m' → Q (Packed.ofBits 0, s) G₁ m' k) :
    P.WP t ((atomicRmwAsC .add .relaxed 4 S.WS.ptr (Packed.ofBits 1 : Io_Condition_State) :
      CM Tgt σ Io_Condition_State).run s) Q G m n := by
  refine wp_rmwAs hP (.inl rfl) (g := (⟨.holds, pa, hL⟩, .ld i e, x)) (fun h => by cases h) hi
    (fun b => ⟨_, ofBits_cst b⟩) fun k hk G₁ m₁ m' old r hg₁ hi₁ hd hv _ hh hw' hop hL' hU' => ?_
  obtain ⟨hl₁, hs₁, -⟩ := hP.split hi₁
  have hh₁ : (G₁ t).1.ph = .holds := by rw [hg₁]
  have hpz₁ : S.PZ m₁ := by
    obtain ⟨hp, hpp, hps⟩ := hz
    have hsub := held_sub hP (G := G₁) (t := t) (by rw [← hg₁, upd_same]; exact hi₁)
    exact ⟨hp, hpp, fun l c h => hsub l c (hps l c h)⟩
  have hnr : ∀ u i' jr sn e', (G₁ u).2.1 ≠ .reg i' jr sn e' := fun u i' jr sn e' hu => by
    by_cases hut : u = t
    · subst hut; rw [hg₁] at hu; cases hu
    · exact hone G₁ m₁ hi₁ (by rw [hg₁]) hh₁ hpz₁ u hut i' jr sn e' hu
  have hold : old = 0 := val_eq hv (hs₁.idle hnr)
  subst hold
  rw [bits_add1] at hh
  have hr : r = Packed.ofBits 0 := by rw [ofBits_cst] at hd; cases hd; rfl
  subst hr
  obtain ⟨hsz, he⟩ := hs₁.ld t i e (by rw [hg₁])
  have hce : VClock.le (S.WE.hist m₁)[i]!.clock (m'.clocks[t]!) = true := by
    have := HBH.le hl₁ hh₁ hs₁.hbE
    simp only [last, hsz, Nat.add_sub_cancel] at this
    exact VClock.le_trans this (hop.clocks t)
  have hpz : S.PZ m' := (op_keep (.inl rfl) hop).2 hpz₁
  have hs' := hs₁.reg (by rw [hg₁]) hh₁ (crit_one hl₁ hs₁ hh₁) hnr hop hw' hh hpz he hce
  have := hP.retag hL' hU' hs' rfl rfl (fun _ => .inl (by rw [hg₁]; rfl)) (by rw [hg₁]; exact hinS)
  rw [hg₁] at this
  exact h k hk G₁ m' _ hop.current this


/-- The waiter `t` at `reg i jr false e` reads epoch write `i + 1`: it saw the signal's epoch. -/
theorem Inv.see {G : ThreadId → SGh X} {m : Mem} {t i jr : Nat} {e : BitVec 32} (hi : S.Inv G m)
    (hg : (G t).2.1 = .reg i jr false e) (hsz : (S.WE.hist m).size = i + 2)
    (hc : VClock.le (S.WE.hist m)[i + 1]!.relClock (m.clocks[t]!) = true)
    (htq : ∀ w ∈ m.waiters, w.2 = S.WE.ptr → w.1 ≠ t) :
    S.Inv (upd G t ((G t).1, .reg i jr true e, (G t).2.2)) m := by
  have he := hi.era t i jr false e hg
  refine hi.retag id (fun h => by cases h)
    (fun i' jr' e' => by rw [hg]; exact ⟨fun ⟨_, h⟩ => ⟨false, by cases h; rfl⟩,
      fun ⟨_, h⟩ => ⟨true, by cases h; rfl⟩⟩)
    (fun i' jr' sn' e' h => by
      simp only [SPh.reg.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact { (he.mono rfl rfl (fun _ => VClock.le_refl _) (fun c h => HBH.mono h
          (fun _ => VClock.le_refl _) (fun u hu => .inl (by
            unfold upd; split
            · rename_i e; subst e; exact hu
            · exact hu)) (fun _ h => h) (fun _ h => h)) (fun h => .inl h) (fun v p hp hv => ⟨v, by
          unfold upd; split
          · rename_i e; subst e; rw [hg] at hv; rcases hp with rfl | rfl <;> cases hv
          · exact hv⟩)) with seen := fun _ => ⟨hsz, hc⟩ })
    (by rw [hg]; exact ⟨fun h => (by cases h), fun h => (by cases h)⟩) (fun h => by cases h)
    (fun h => by rw [hg] at h; cases h) (fun _ _ h => by cases h) (fun h => by rw [hg] at h; cases h)
    (fun y h1 h2 => hi.off t y h1 h2) htq

-- `Condition.waitUncancelable` per translation (`ZigLean.VersionGate`): Zig 0.16.0 calls
-- `waitInner(…, true)`, whose loops also hold the cancelable path; Zig 0.17.0 inlines the
-- uncancelable loops (`loop22`, `loop45`). Each proves `condWait_spec_v*`; `condWait_spec` is the
-- version-neutral statement.
when_defined Io_Condition_waitInner

section Wait

variable (t : ThreadId) (pa : Heap) (x : X) (io : Io) (i jr : Nat) (e : BitVec 32)

/-- The waiter's ghost value at `reg`, out of the mutex. -/
abbrev gw (sn : Bool) : SGh X := (⟨.out, pa, Heap.empty⟩, .reg i jr sn e, x)

/-- The inner loop's invariant: the waiter read the state `b`; if it saw the signal's epoch, `b`
has the signal. -/
def inv56 (D : Nat) (s : Io_Condition_waitInnerLocals) (G : ThreadId → SGh X) (m : Mem) (d : Nat) :
    Prop :=
  d < D ∧ m.current = t ∧ ∃ sn b, s.prev_state = Packed.ofBits b ∧ SV b ∧
    s.epoch = (if sn then e + 1 else e) ∧ (sn = true → b = 0x10001) ∧ P.inv (upd G t (gw pa x i jr e sn)) m

/-- The inner loop ends with no signal to take, or with the waiter holding the mutex. -/
def post56 (D : Nat) (r : Io_Condition_waitInnerExit × Io_Condition_waitInnerLocals)
    (G : ThreadId → SGh X) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ m.current = t ∧
    ((r.1 = .br55 ∧ r.2.epoch = e ∧ P.inv (upd G t (gw pa x i jr e false)) m) ∨
      (r.1 = .ret (.ok ()) ∧ ∃ hL, P.inv (upd G t (⟨.holds, pa, hL⟩, .none, x)) m))

theorem loop56_body (hP : S.Fits P U) (hinS : S.inS x) (D : Nat) (s : Io_Condition_waitInnerLocals) (G : ThreadId → SGh X) (m : Mem)
    (d : Nat) (h : inv56 (P := P) t pa x i jr e D s G m d) :
    P.WP t ((Io_Condition_waitInner.loop56 (S.ptr.add 12) io (S.ptr.add 8)).run s) (fun r G' m' d' =>
      if Io_Condition_waitInner.again56 r.1 then inv56 (P := P) t pa x i jr e D r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : Io_Condition_waitInnerLocals) => 0) s)
      else post56 (P := P) t pa x i jr e D r G' m' d') G m d := by
  obtain ⟨ep, ps⟩ := s
  obtain ⟨hD, hc, sn, b, hps, hsv, hep, hsn, hi⟩ := h
  simp only at hps hep
  subst hps
  unfold Io_Condition_waitInner.loop56
  simp only [StateT.run_bind, StateT.run_get]
  simp only [pure_bind]
  refine WP.bind ?_
  simp only [StateT.run_pure]
  simp only [pure_bind]
  by_cases hb : b = 0x10001
  · subst hb
    rw [if_pos ((sig_sv hsv).mpr rfl)]
    simp only [StateT.run_bind, StateT.run_get]
    simp only [pure_bind]
    refine WP.bind (WP.bind (WP.callRC (fun e he => by
      change (sub false _ 1).run = _ at he; rw [sub_w] at he; cases he) fun a ha => ?_))
    have ha' : a = (Packed.ofBits (0x10001 : BitVec 32) : Io_Condition_State).waiters - 1 := by
      change (sub false _ 1).run = _ at ha; rw [sub_w] at ha; cases ha; rfl
    subst ha'
    refine WP.bind (WP.callRC (fun e he => by
      change (sub false _ 1).run = _ at he; rw [sub_s] at he; cases he) fun c hc' => ?_)
    have hc'' : c = (Packed.ofBits (0x10001 : BitVec 32) : Io_Condition_State).signals - 1 := by
      change (sub false _ 1).run = _ at hc'; rw [sub_s] at hc'; cases hc'; rfl
    subst hc''
    dsimp only
    rw [ptr_state]
    refine WP.bind (WP.bind (wp_weakCasAs hP (.inl rfl) (g := gw pa x i jr e sn) (fun h => by cases h) hi
      (fun b => ⟨_, ofBits_cst b⟩) fun k hk G₁ m₁ m' hg₁ hi₁ hw' hop hL hU =>
        ⟨fun hv _ hh _ => ?_, fun j b r hd hj hv hfl hh => ?_⟩))
    · -- the waiter takes the signal, then locks the mutex
      rw [bits_take'] at hh
      obtain ⟨-, hs₁, -⟩ := hP.split hi₁
      have hs₂ := hs₁.consume (by rw [hg₁]) (out_notQ hP hi₁ (by rw [hg₁])) hop hw' hh
      have hi₂ := hP.retag hL hU hs₂ rfl rfl (fun h => by simp [SPh.waits] at h) (by rw [hg₁]; exact hinS)
      rw [hg₁] at hi₂
      refine WP.pure' ?_
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      simp only [StateT.run_bind]
      refine WP.bind (WP.callC (WP.mono ?_ (MutexOps.lock_specOn hP.lf ptr_mutex rfl t
        (⟨.out, pa, Heap.empty⟩, .none, x) rfl ⟨rfl, hinS⟩ io G₁ m' k hi₂)))
      rintro _ G₂ m₂ d₂ ⟨hd₂, hc₂, hL₂, hi₃⟩
      simp only [StateT.run_pure]
      refine WP.pure' (WP.pure' (WP.pure' ?_))
      simp only [Io_Condition_waitInner.again56, Bool.false_eq_true, ↓reduceIte]
      exact ⟨by omega, hc₂, .inr ⟨rfl, hL₂, hi₃⟩⟩
    · -- no signal taken: a weak failure can retry even after seeing the epoch
      obtain ⟨-, hs₁, -⟩ := hP.split hi₁
      have hsn₂ : sn = true → b = 0x10001 := by
        intro hsn'
        subst hsn'
        have he := hs₁.era t i jr true e (by rw [hg₁])
        obtain ⟨hsz, hcl⟩ := he.seen rfl
        rcases he.esz with h1 | ⟨-, h2, h3⟩
        · omega
        · have := hfl (jr + 1) (by omega) (VClock.le_trans h3 hcl)
          obtain rfl : j = jr + 1 := by omega
          exact val_eq hv (he.s1 h2)
      have hi₂ : P.inv G₁ m' := hP.pack hL (hs₁.opKeep (.inl rfl) hop hw' hh) hU
      have hr : r = Packed.ofBits b := by rw [ofBits_cst] at hd; cases hd; rfl
      simp only [StateT.run_pure]
      refine WP.pure' ?_
      simp only [Option.isSome_some, ↓reduceIte]
      simp only [StateT.run_bind]
      refine WP.bind (WP.callRC_ok (v := r) rfl ?_)
      simp only [StateT.run_pure]
      refine WP.pure' (WP.pure' (WP.pure' ?_))
      simp only [Io_Condition_waitInner.again56, ↓reduceIte]
      refine ⟨⟨by omega, hop.current, sn, b, hr, sv_of hs₁ hj hv, hep,
        hsn₂, by rw [← hg₁, upd_same]; exact hi₂⟩, .inl (by omega)⟩
  · have hsnf : sn = false := by cases sn; rfl; exact absurd (hsn rfl) hb
    subst hsnf
    rw [if_neg (fun h => hb ((sig_sv hsv).mp h))]
    simp only [StateT.run_pure]
    refine WP.pure' ?_
    simp only [StateT.run_pure]
    refine WP.pure' ?_
    simp only [Io_Condition_waitInner.again56, Bool.false_eq_true, ↓reduceIte]
    exact ⟨hD, hc, .inl ⟨rfl, by simpa using hep, hi⟩⟩

end Wait


section Wait2

variable (t : ThreadId) (pa : Heap) (x : X) (io : Io) (i jr : Nat) (e : BitVec 32)

/-- The outer loop's invariant: the waiter at `reg`, with the value `e` of epoch write `i`. -/
def inv23 (D : Nat) (s : Io_Condition_waitInnerLocals) (G : ThreadId → SGh X) (m : Mem) (d : Nat) :
    Prop :=
  d < D ∧ m.current = t ∧ s.epoch = e ∧ P.inv (upd G t (gw pa x i jr e false)) m

/-- The outer loop ends with the waiter holding the mutex. -/
def post23 (D : Nat) (r : Io_Condition_waitInnerExit × Io_Condition_waitInnerLocals)
    (G : ThreadId → SGh X) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ r.1 = .ret (.ok ()) ∧ m.current = t ∧ ∃ hL, P.inv (upd G t (⟨.holds, pa, hL⟩, .none, x)) m

theorem loop23_body (hP : S.Fits P U) (hinS : S.inS x) (D : Nat) (s : Io_Condition_waitInnerLocals)
    (G : ThreadId → SGh X) (m : Mem) (d : Nat) (h : inv23 (P := P) t pa x i jr e D s G m d) :
    P.WP t ((Io_Condition_waitInner.loop23 (S.ptr.add 12) io (S.ptr.add 8) true).run s)
      (fun r G' m' d' =>
        if Io_Condition_waitInner.again23 r.1 then inv23 (P := P) t pa x i jr e D r.2 G' m' d' ∧
          (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : Io_Condition_waitInnerLocals) => 0) s)
        else post23 (P := P) t pa x D r G' m' d') G m d := by
  obtain ⟨ep, ps⟩ := s
  obtain ⟨hD, hc, he, hi⟩ := h
  simp only at he
  subst ep
  unfold Io_Condition_waitInner.loop23
  simp only [StateT.run_bind]
  simp only [pure_bind]
  refine WP.bind ?_
  simp only [↓reduceIte]
  simp only [StateT.run_bind, StateT.run_get]
  simp only [pure_bind]
  refine WP.bind (WP.bind (WP.callMC_ptrProject (hP.projCE hi) ?_))
  dsimp only
  rw [ptr_epoch]
  refine WP.bind (wp_ewait hP hinS hi fun k hk G₁ m₁ hc₁ hi₁ => ?_)
  refine WP.pure' ?_
  dsimp only
  simp only [StateT.run_bind]
  refine WP.bind (WP.callMC_ptrProject (hP.projCE hi₁) ?_)
  dsimp only
  rw [ptr_epoch]
  refine WP.bind (WP.bind (wp_load hP (.inr rfl) (g := gw pa x i jr e false) (fun h => by cases h) hi₁
    fun k₂ hk₂ G₂ m₂ m₃ v j hg₂ hi₂ hj hv hfl hacq hh hw' hop hL hU => ?_))
  obtain ⟨-, hs₂, -⟩ := hP.split hi₂
  have he₂ := hs₂.era t i jr false e (by rw [hg₂])
  have hle : i + 1 ≤ (S.WE.hist m₂).size ∧ (S.WE.hist m₂).size ≤ i + 2 := by
    rcases he₂.esz with h1 | ⟨h1, -⟩ <;> omega
  have hij : i ≤ j := hfl i (by omega) he₂.ce
  have hs₃ := hs₂.opKeep (.inr rfl) hop hw' hh
  have hp₃ : P.inv G₂ m₃ := hP.pack hL hs₃ hU
  obtain ⟨sn, hvsn, hi₃⟩ : ∃ sn, v = (if sn then e + 1 else e) ∧ P.inv (upd G₂ t (gw pa x i jr e sn)) m₃ := by
    rcases (by omega : j = i ∨ j = i + 1) with rfl | rfl
    · exact ⟨false, val_eq hv he₂.eval.1, by rw [← hg₂, upd_same]; exact hp₃⟩
    · have hsz : (S.WE.hist m₂).size = i + 2 := by omega
      refine ⟨true, val_eq hv (he₂.eval.2 hsz), ?_⟩
      have := hP.retag hL hU (hs₃.see (by rw [hg₂]) (by rw [hh]; exact hsz)
        (by rw [hh]; exact hacq rfl) (out_notQ hP hp₃ (by rw [hg₂]))) rfl rfl (fun _ => .inl (by rw [hg₂]; rfl)) (by rw [hg₂]; exact hinS)
      rwa [hg₂] at this
  refine WP.pure' ?_
  dsimp only
  simp only [StateT.run_bind, StateT.run_modify]
  simp only [pure_bind]
  rw [ptr_state]
  refine WP.bind (WP.bind (WP.bind (wp_loadAs hP (.inl rfl) (g := gw pa x i jr e sn) (fun h => by cases h)
    hi₃ (fun b => ⟨_, ofBits_cst b⟩)
    fun k₃ hk₃ G₃ m₄ m₅ b r j' hg₃ hi₄ hd hj' hv' hfl' hh' hw₅ hop₅ hL₅ hU₅ => ?_)))
  obtain ⟨-, hs₄, -⟩ := hP.split hi₄
  have hr : r = Packed.ofBits b := by rw [ofBits_cst] at hd; cases hd; rfl
  have hsb : sn = true → b = 0x10001 := fun hsn => by
    subst hsn
    have he₄ := hs₄.era t i jr true e (by rw [hg₃])
    obtain ⟨hsz, hcl⟩ := he₄.seen rfl
    rcases he₄.esz with h1 | ⟨-, h2, h3⟩
    · omega
    · have := hfl' (jr + 1) (by omega) (VClock.le_trans h3 hcl)
      obtain rfl : j' = jr + 1 := by omega
      exact val_eq hv' (he₄.s1 h2)
  have hi₅ : P.inv G₃ m₅ := hP.pack hL₅ (hs₄.opKeep (.inl rfl) hop₅ hw₅ hh') hU₅
  refine WP.pure' ?_
  dsimp only
  simp only [StateT.run_bind, StateT.run_modify]
  simp only [pure_bind]
  refine WP.bind (WP.mono ?_ (WP.loop _ _ (inv56 (P := P) t pa x i jr e d) (fun _ => 0)
    (post56 (P := P) t pa x i jr e d) (loop56_body t pa x io i jr e hP hinS d) _ G₃ m₅ k₃
    ⟨by omega, hop₅.current, sn, b, hr, sv_of hs₄ hj' hv', hvsn, hsb,
      by rw [← hg₃, upd_same]; exact hi₅⟩))
  rintro ⟨e', s'⟩ G₄ m₆ d₄ ⟨hd₄, hc₆, ⟨rfl, hep, hi₆⟩ | ⟨rfl, hL₆, hi₆⟩⟩
  · simp only [StateT.run_pure]
    refine WP.pure' ?_
    dsimp only
    simp only [isNonErr]
    refine WP.pure' (WP.pure' ?_)
    simp only [Io_Condition_waitInner.again23, ↓reduceIte]
    exact ⟨⟨by omega, hc₆, hep, hi₆⟩, .inl (by omega)⟩
  · simp only [StateT.run_pure]
    refine WP.pure' (WP.pure' (WP.pure' ?_))
    simp only [Io_Condition_waitInner.again23, Bool.false_eq_true, ↓reduceIte]
    exact ⟨by omega, rfl, hc₆, hL₆, hi₆⟩

end Wait2

/-- `Condition.wait` by the holder `t`, which saw no permit (`hz`) while no other thread waits
at the condition (`hone`): it holds the mutex again, at the same place. -/
theorem condWait_spec_v016 (hP : S.Fits P U) (t : ThreadId) (pa hL : Heap) (x : X) (io : Io)
    (G : ThreadId → SGh X) (m : Mem) (d : Nat)
    (hi : P.inv (upd G t (⟨.holds, pa, hL⟩, .none, x)) m)
    (hz : ∃ hp, pts S.ptr 8 (0 : BitVec 64) hp ∧ hp.Sub hL)
    (hone : ∀ G' m', P.inv G' m' → (G' t).2.2 = x → (G' t).1.ph = .holds → S.PZ m' → ∀ u, u ≠ t →
      ∀ i jr sn e, (G' u).2.1 ≠ .reg i jr sn e) (hwx : S.wx x) (hinS : S.inS x) :
    P.WP t (Io_Condition_waitUncancelable (S.ptr.add 12) io (S.ptr.add 8)) (fun _ G' m' d' =>
      d' < d ∧ m'.current = t ∧ ∃ hL', P.inv (upd G' t (⟨.holds, pa, hL'⟩, .none, x)) m') G m d := by
  have hwi : P.WP t (Io_Condition_waitInner (S.ptr.add 12) io (S.ptr.add 8) true) (fun r G' m' d' =>
      d' < d ∧ r = .ok () ∧ m'.current = t ∧
        ∃ hL', P.inv (upd G' t (⟨.holds, pa, hL'⟩, .none, x)) m') G m d := by
    unfold Io_Condition_waitInner
    refine WP.bind ?_
    rw [StateT.run'_eq]
    refine WP.map ?_
    simp only [StateT.run_bind]
    simp only [StateT.run_pure, pure_bind]
    refine WP.bind (WP.callMC_ptrProject (hP.projCE hi) ?_)
    dsimp only
    rw [ptr_epoch]
    refine WP.bind (WP.bind (wp_ldE hP rfl hwx hinS hi fun k₁ hk₁ G₁ m₁ i ev hc₁ hi₁ => ?_))
    refine WP.pure' ?_
    dsimp only
    simp only [StateT.run_bind, StateT.run_modify]
    simp only [pure_bind]
    rw [ptr_state]
    refine WP.bind (WP.bind (WP.bind (wp_regS hP hinS hi₁ hz hone fun k₂ hk₂ G₂ m₂ jr hc₂ hi₂ => ?_)))
    refine WP.pure' ?_
    dsimp only
    simp only [StateT.run_bind]
    rw [lt_w]
    refine WP.bind (WP.callRC_ok dbg_true ?_)
    simp only [StateT.run_pure]
    refine WP.pure' ?_
    dsimp only
    simp only [StateT.run_bind]
    refine WP.bind (WP.callC (WP.mono ?_ (MutexOps.unlock_specOn hP.lf ptr_mutex rfl t
      (⟨.holds, pa, hL⟩, .reg i jr false ev, x) rfl ⟨rfl, hinS⟩ io G₂ m₂ k₂ hi₂)))
    rintro _ G₃ m₃ d₃ ⟨hd₃, hc₃, hi₃⟩
    refine WP.mono ?_ (WP.loop _ _ (inv23 (P := P) t pa x i jr ev d) (fun _ => 0)
      (post23 (P := P) t pa x d) (loop23_body t pa x io i jr ev hP hinS d) _ G₃ m₃ d₃
      ⟨by omega, hc₃, rfl, hi₃⟩)
    rintro ⟨e', s'⟩ G₄ m₄ d₄ ⟨hd₄, rfl, hc₄, hL₄, hi₄⟩
    exact WP.pure' ⟨hd₄, rfl, hc₄, hL₄, hi₄⟩
  unfold Io_Condition_waitUncancelable
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind]
  refine WP.bind (WP.callC (WP.mono ?_ hwi))
  rintro r G₁ m₁ d₁ ⟨hd₁, rfl, hc₁, hL₁, hi₁⟩
  simp only [StateT.run_pure]
  simp only [pure_bind]
  simp only [isNonErr]
  exact WP.pure' (WP.pure' ⟨hd₁, hc₁, hL₁, hi₁⟩)

end_when

when_defined Io_Condition_waitUncancelable.loop22

section Wait017

variable (t : ThreadId) (pa : Heap) (x : X) (io : Io) (i jr : Nat) (e : BitVec 32)

/-- The waiter's ghost value at `reg`, out of the mutex. -/
abbrev gw (sn : Bool) : SGh X := (⟨.out, pa, Heap.empty⟩, .reg i jr sn e, x)

/-- The inner loop's invariant: the waiter read the state `b`; if it saw the signal's epoch, `b`
has the signal. -/
def inv45 (D : Nat) (s : Io_Condition_waitUncancelableLocals) (G : ThreadId → SGh X) (m : Mem) (d : Nat) :
    Prop :=
  d < D ∧ m.current = t ∧ ∃ sn b, s.prev_state = Packed.ofBits b ∧ SV b ∧
    s.epoch = (if sn then e + 1 else e) ∧ (sn = true → b = 0x10001) ∧ P.inv (upd G t (gw pa x i jr e sn)) m

/-- The inner loop ends with no signal to take, or with the waiter holding the mutex. -/
def post45 (D : Nat) (r : Io_Condition_waitUncancelableExit × Io_Condition_waitUncancelableLocals)
    (G : ThreadId → SGh X) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ m.current = t ∧
    ((r.1 = .br44 ∧ r.2.epoch = e ∧ P.inv (upd G t (gw pa x i jr e false)) m) ∨
      (r.1 = .ret ∧ ∃ hL, P.inv (upd G t (⟨.holds, pa, hL⟩, .none, x)) m))

theorem loop45_body (hP : S.Fits P U) (hinS : S.inS x) (D : Nat) (s : Io_Condition_waitUncancelableLocals) (G : ThreadId → SGh X) (m : Mem)
    (d : Nat) (h : inv45 (P := P) t pa x i jr e D s G m d) :
    P.WP t ((Io_Condition_waitUncancelable.loop45 (S.ptr.add 12) io (S.ptr.add 8)).run s) (fun r G' m' d' =>
      if Io_Condition_waitUncancelable.again45 r.1 then inv45 (P := P) t pa x i jr e D r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : Io_Condition_waitUncancelableLocals) => 0) s)
      else post45 (P := P) t pa x i jr e D r G' m' d') G m d := by
  obtain ⟨ep, ps⟩ := s
  obtain ⟨hD, hc, sn, b, hps, hsv, hep, hsn, hi⟩ := h
  simp only at hps hep
  subst hps
  unfold Io_Condition_waitUncancelable.loop45
  simp only [StateT.run_bind, StateT.run_get]
  simp only [pure_bind]
  refine WP.bind ?_
  simp only [StateT.run_pure]
  simp only [pure_bind]
  by_cases hb : b = 0x10001
  · subst hb
    rw [if_pos ((sig_sv hsv).mpr rfl)]
    simp only [StateT.run_bind, StateT.run_get]
    simp only [pure_bind]
    refine WP.bind (WP.bind (WP.callRC (fun e he => by
      change (sub false _ 1).run = _ at he; rw [sub_w] at he; cases he) fun a ha => ?_))
    have ha' : a = (Packed.ofBits (0x10001 : BitVec 32) : Io_Condition_State).waiters - 1 := by
      change (sub false _ 1).run = _ at ha; rw [sub_w] at ha; cases ha; rfl
    subst ha'
    refine WP.bind (WP.callRC (fun e he => by
      change (sub false _ 1).run = _ at he; rw [sub_s] at he; cases he) fun c hc' => ?_)
    have hc'' : c = (Packed.ofBits (0x10001 : BitVec 32) : Io_Condition_State).signals - 1 := by
      change (sub false _ 1).run = _ at hc'; rw [sub_s] at hc'; cases hc'; rfl
    subst hc''
    dsimp only
    rw [ptr_state]
    refine WP.bind (WP.bind (wp_weakCasAs hP (.inl rfl) (g := gw pa x i jr e sn) (fun h => by cases h) hi
      (fun b => ⟨_, ofBits_cst b⟩) fun k hk G₁ m₁ m' hg₁ hi₁ hw' hop hL hU =>
        ⟨fun hv _ hh _ => ?_, fun j b r hd hj hv hfl hh => ?_⟩))
    · -- the waiter takes the signal, then locks the mutex
      rw [bits_take'] at hh
      obtain ⟨-, hs₁, -⟩ := hP.split hi₁
      have hs₂ := hs₁.consume (by rw [hg₁]) (out_notQ hP hi₁ (by rw [hg₁])) hop hw' hh
      have hi₂ := hP.retag hL hU hs₂ rfl rfl (fun h => by simp [SPh.waits] at h) (by rw [hg₁]; exact hinS)
      rw [hg₁] at hi₂
      refine WP.pure' ?_
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      simp only [StateT.run_bind]
      refine WP.bind (WP.callC (WP.mono ?_ (MutexOps.lock_specOn hP.lf ptr_mutex rfl t
        (⟨.out, pa, Heap.empty⟩, .none, x) rfl ⟨rfl, hinS⟩ io G₁ m' k hi₂)))
      rintro _ G₂ m₂ d₂ ⟨hd₂, hc₂, hL₂, hi₃⟩
      simp only [StateT.run_pure]
      refine WP.pure' (WP.pure' (WP.pure' ?_))
      simp only [Io_Condition_waitUncancelable.again45, Bool.false_eq_true, ↓reduceIte]
      exact ⟨by omega, hc₂, .inr ⟨rfl, hL₂, hi₃⟩⟩
    · -- no signal taken: a weak failure can retry even after seeing the epoch
      obtain ⟨-, hs₁, -⟩ := hP.split hi₁
      have hsn₂ : sn = true → b = 0x10001 := by
        intro hsn'
        subst hsn'
        have he := hs₁.era t i jr true e (by rw [hg₁])
        obtain ⟨hsz, hcl⟩ := he.seen rfl
        rcases he.esz with h1 | ⟨-, h2, h3⟩
        · omega
        · have := hfl (jr + 1) (by omega) (VClock.le_trans h3 hcl)
          obtain rfl : j = jr + 1 := by omega
          exact val_eq hv (he.s1 h2)
      have hi₂ : P.inv G₁ m' := hP.pack hL (hs₁.opKeep (.inl rfl) hop hw' hh) hU
      have hr : r = Packed.ofBits b := by rw [ofBits_cst] at hd; cases hd; rfl
      simp only [StateT.run_pure]
      refine WP.pure' ?_
      simp only [Option.isSome_some, ↓reduceIte]
      simp only [StateT.run_bind]
      refine WP.bind (WP.callRC_ok (v := r) rfl ?_)
      simp only [StateT.run_pure]
      refine WP.pure' (WP.pure' (WP.pure' ?_))
      simp only [Io_Condition_waitUncancelable.again45, ↓reduceIte]
      refine ⟨⟨by omega, hop.current, sn, b, hr, sv_of hs₁ hj hv, hep,
        hsn₂, by rw [← hg₁, upd_same]; exact hi₂⟩, .inl (by omega)⟩
  · have hsnf : sn = false := by cases sn; rfl; exact absurd (hsn rfl) hb
    subst hsnf
    rw [if_neg (fun h => hb ((sig_sv hsv).mp h))]
    simp only [StateT.run_pure]
    refine WP.pure' ?_
    simp only [StateT.run_pure]
    refine WP.pure' ?_
    simp only [Io_Condition_waitUncancelable.again45, Bool.false_eq_true, ↓reduceIte]
    exact ⟨hD, hc, .inl ⟨rfl, by simpa using hep, hi⟩⟩

end Wait017


section Wait2017

variable (t : ThreadId) (pa : Heap) (x : X) (io : Io) (i jr : Nat) (e : BitVec 32)

/-- The outer loop's invariant: the waiter at `reg`, with the value `e` of epoch write `i`. -/
def inv22 (D : Nat) (s : Io_Condition_waitUncancelableLocals) (G : ThreadId → SGh X) (m : Mem) (d : Nat) :
    Prop :=
  d < D ∧ m.current = t ∧ s.epoch = e ∧ P.inv (upd G t (gw pa x i jr e false)) m

/-- The outer loop ends with the waiter holding the mutex. -/
def post22 (D : Nat) (r : Io_Condition_waitUncancelableExit × Io_Condition_waitUncancelableLocals)
    (G : ThreadId → SGh X) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ r.1 = .ret ∧ m.current = t ∧ ∃ hL, P.inv (upd G t (⟨.holds, pa, hL⟩, .none, x)) m

theorem loop22_body (hP : S.Fits P U) (hinS : S.inS x) (D : Nat) (s : Io_Condition_waitUncancelableLocals)
    (G : ThreadId → SGh X) (m : Mem) (d : Nat) (h : inv22 (P := P) t pa x i jr e D s G m d) :
    P.WP t ((Io_Condition_waitUncancelable.loop22 (S.ptr.add 12) io (S.ptr.add 8)).run s)
      (fun r G' m' d' =>
        if Io_Condition_waitUncancelable.again22 r.1 then inv22 (P := P) t pa x i jr e D r.2 G' m' d' ∧
          (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : Io_Condition_waitUncancelableLocals) => 0) s)
        else post22 (P := P) t pa x D r G' m' d') G m d := by
  obtain ⟨ep, ps⟩ := s
  obtain ⟨hD, hc, he, hi⟩ := h
  simp only at he
  subst ep
  unfold Io_Condition_waitUncancelable.loop22
  simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind]
  first
  | rw [ptr_epoch]
  | refine WP.bind (WP.callMC_ptrProject (hP.projCE hi) ?_)
    simp only [StateT.run_bind, StateT.run_pure, pure_bind]
    rw [ptr_epoch]
  refine WP.bind (wp_ewait hP hinS hi fun k hk G₁ m₁ hc₁ hi₁ => ?_)
  dsimp only
  -- Zig 0.17.0 forms the epoch pointer again before the load.
  try (refine WP.bind (WP.callMC_ptrProject (hP.projCE hi₁) ?_)
       simp only [StateT.run_bind, StateT.run_pure, pure_bind]
       rw [ptr_epoch])
  refine WP.bind (WP.bind (wp_load hP (.inr rfl) (g := gw pa x i jr e false) (fun h => by cases h) hi₁
    fun k₂ hk₂ G₂ m₂ m₃ v j hg₂ hi₂ hj hv hfl hacq hh hw' hop hL hU => ?_))
  obtain ⟨-, hs₂, -⟩ := hP.split hi₂
  have he₂ := hs₂.era t i jr false e (by rw [hg₂])
  have hle : i + 1 ≤ (S.WE.hist m₂).size ∧ (S.WE.hist m₂).size ≤ i + 2 := by
    rcases he₂.esz with h1 | ⟨h1, -⟩ <;> omega
  have hij : i ≤ j := hfl i (by omega) he₂.ce
  have hs₃ := hs₂.opKeep (.inr rfl) hop hw' hh
  have hp₃ : P.inv G₂ m₃ := hP.pack hL hs₃ hU
  obtain ⟨sn, hvsn, hi₃⟩ : ∃ sn, v = (if sn then e + 1 else e) ∧ P.inv (upd G₂ t (gw pa x i jr e sn)) m₃ := by
    rcases (by omega : j = i ∨ j = i + 1) with rfl | rfl
    · exact ⟨false, val_eq hv he₂.eval.1, by rw [← hg₂, upd_same]; exact hp₃⟩
    · have hsz : (S.WE.hist m₂).size = i + 2 := by omega
      refine ⟨true, val_eq hv (he₂.eval.2 hsz), ?_⟩
      have := hP.retag hL hU (hs₃.see (by rw [hg₂]) (by rw [hh]; exact hsz)
        (by rw [hh]; exact hacq rfl) (out_notQ hP hp₃ (by rw [hg₂]))) rfl rfl (fun _ => .inl (by rw [hg₂]; rfl)) (by rw [hg₂]; exact hinS)
      rwa [hg₂] at this
  refine WP.pure' ?_
  dsimp only
  simp only [StateT.run_bind, StateT.run_modify]
  simp only [pure_bind]
  rw [ptr_state]
  refine WP.bind (WP.bind (WP.bind (wp_loadAs hP (.inl rfl) (g := gw pa x i jr e sn) (fun h => by cases h)
    hi₃ (fun b => ⟨_, ofBits_cst b⟩)
    fun k₃ hk₃ G₃ m₄ m₅ b r j' hg₃ hi₄ hd hj' hv' hfl' hh' hw₅ hop₅ hL₅ hU₅ => ?_)))
  obtain ⟨-, hs₄, -⟩ := hP.split hi₄
  have hr : r = Packed.ofBits b := by rw [ofBits_cst] at hd; cases hd; rfl
  have hsb : sn = true → b = 0x10001 := fun hsn => by
    subst hsn
    have he₄ := hs₄.era t i jr true e (by rw [hg₃])
    obtain ⟨hsz, hcl⟩ := he₄.seen rfl
    rcases he₄.esz with h1 | ⟨-, h2, h3⟩
    · omega
    · have := hfl' (jr + 1) (by omega) (VClock.le_trans h3 hcl)
      obtain rfl : j' = jr + 1 := by omega
      exact val_eq hv' (he₄.s1 h2)
  have hi₅ : P.inv G₃ m₅ := hP.pack hL₅ (hs₄.opKeep (.inl rfl) hop₅ hw₅ hh') hU₅
  refine WP.pure' ?_
  dsimp only
  simp only [StateT.run_bind, StateT.run_modify]
  simp only [pure_bind]
  refine WP.bind (WP.mono ?_ (WP.loop _ _ (inv45 (P := P) t pa x i jr e d) (fun _ => 0)
    (post45 (P := P) t pa x i jr e d) (loop45_body t pa x io i jr e hP hinS d) _ G₃ m₅ k₃
    ⟨by omega, hop₅.current, sn, b, hr, sv_of hs₄ hj' hv', hvsn, hsb,
      by rw [← hg₃, upd_same]; exact hi₅⟩))
  rintro ⟨e', s'⟩ G₄ m₆ d₄ ⟨hd₄, hc₆, ⟨rfl, hep, hi₆⟩ | ⟨rfl, hL₆, hi₆⟩⟩
  · simp only [StateT.run_pure]
    refine WP.pure' (WP.pure' ?_)
    simp only [Io_Condition_waitUncancelable.again22, ↓reduceIte]
    exact ⟨⟨by omega, hc₆, hep, hi₆⟩, .inl (by omega)⟩
  · simp only [StateT.run_pure]
    refine WP.pure' (WP.pure' ?_)
    simp only [Io_Condition_waitUncancelable.again22, Bool.false_eq_true, ↓reduceIte]
    exact ⟨by omega, rfl, hc₆, hL₆, hi₆⟩

end Wait2017

/-- `Condition.wait` by the holder `t`, which saw no permit (`hz`) while no other thread waits
at the condition (`hone`): it holds the mutex again, at the same place. -/
theorem condWait_spec_v017 (hP : S.Fits P U) (t : ThreadId) (pa hL : Heap) (x : X) (io : Io)
    (G : ThreadId → SGh X) (m : Mem) (d : Nat)
    (hi : P.inv (upd G t (⟨.holds, pa, hL⟩, .none, x)) m)
    (hz : ∃ hp, pts S.ptr 8 (0 : BitVec 64) hp ∧ hp.Sub hL)
    (hone : ∀ G' m', P.inv G' m' → (G' t).2.2 = x → (G' t).1.ph = .holds → S.PZ m' → ∀ u, u ≠ t →
      ∀ i jr sn e, (G' u).2.1 ≠ .reg i jr sn e) (hwx : S.wx x) (hinS : S.inS x) :
    P.WP t (Io_Condition_waitUncancelable (S.ptr.add 12) io (S.ptr.add 8)) (fun _ G' m' d' =>
      d' < d ∧ m'.current = t ∧ ∃ hL', P.inv (upd G' t (⟨.holds, pa, hL'⟩, .none, x)) m') G m d := by
  unfold Io_Condition_waitUncancelable
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind]
  simp only [StateT.run_pure, pure_bind]
  first
  | rw [ptr_epoch]
  | refine WP.bind (WP.callMC_ptrProject (hP.projCE hi) ?_)
    simp only [StateT.run_bind, StateT.run_pure, pure_bind]
    rw [ptr_epoch]
  refine WP.bind (WP.bind (wp_ldE hP rfl hwx hinS hi fun k₁ hk₁ G₁ m₁ i ev hc₁ hi₁ => ?_))
  refine WP.pure' ?_
  dsimp only
  simp only [StateT.run_bind, StateT.run_modify]
  simp only [pure_bind]
  rw [ptr_state]
  refine WP.bind (WP.bind (WP.bind (wp_regS hP hinS hi₁ hz hone fun k₂ hk₂ G₂ m₂ jr hc₂ hi₂ => ?_)))
  refine WP.pure' ?_
  dsimp only
  simp only [StateT.run_bind]
  rw [lt_w]
  refine WP.bind (WP.callRC_ok dbg_true ?_)
  simp only [StateT.run_pure]
  refine WP.pure' ?_
  dsimp only
  simp only [StateT.run_bind]
  refine WP.bind (WP.callC (WP.mono ?_ (MutexOps.unlock_specOn hP.lf ptr_mutex rfl t
    (⟨.holds, pa, hL⟩, .reg i jr false ev, x) rfl ⟨rfl, hinS⟩ io G₂ m₂ k₂ hi₂)))
  rintro _ G₃ m₃ d₃ ⟨hd₃, hc₃, hi₃⟩
  refine WP.mono ?_ (WP.loop _ _ (inv22 (P := P) t pa x i jr ev d) (fun _ => 0)
    (post22 (P := P) t pa x d) (loop22_body t pa x io i jr ev hP hinS d) _ G₃ m₃ d₃
    ⟨by omega, hc₃, rfl, hi₃⟩)
  rintro ⟨e', s'⟩ G₄ m₄ d₄ ⟨hd₄, rfl, hc₄, hL₄, hi₄⟩
  exact WP.pure' ⟨hd₄, hc₄, hL₄, hi₄⟩

end_when

theorem condWait_spec (hP : S.Fits P U) (t : ThreadId) (pa hL : Heap) (x : X) (io : Io)
    (G : ThreadId → SGh X) (m : Mem) (d : Nat)
    (hi : P.inv (upd G t (⟨.holds, pa, hL⟩, .none, x)) m)
    (hz : ∃ hp, pts S.ptr 8 (0 : BitVec 64) hp ∧ hp.Sub hL)
    (hone : ∀ G' m', P.inv G' m' → (G' t).2.2 = x → (G' t).1.ph = .holds → S.PZ m' → ∀ u, u ≠ t →
      ∀ i jr sn e, (G' u).2.1 ≠ .reg i jr sn e) (hwx : S.wx x) (hinS : S.inS x) :
    P.WP t (Io_Condition_waitUncancelable (S.ptr.add 12) io (S.ptr.add 8)) (fun _ G' m' d' =>
      d' < d ∧ m'.current = t ∧ ∃ hL', P.inv (upd G' t (⟨.holds, pa, hL'⟩, .none, x)) m') G m d := by
  first
  | exact condWait_spec_v016 hP t pa hL x io G m d hi hz hone hwx hinS
  | exact condWait_spec_v017 hP t pa hL x io G m d hi hz hone hwx hinS


/-! ## `wait` and `post` -/

theorem ptr0 : S.ptr.add 0 = S.ptr := by simp [Sem.ptr, Ptr.add]

theorem sub1_run {a : BitVec 64} (h : a ≠ 0) : (sub false a 1).run = some (.ok (a - 1)) := by
  have h0 : a.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
  simp only [sub, Bool.false_eq_true, ↓reduceIte]
  split
  · rename_i ho; simp [BitVec.usubOverflow] at ho; try omega
  · rfl

theorem add1_run {a : BitVec 64} (h : a.toNat + 1 < 2 ^ 64) : (add false a 1).run = some (.ok (a + 1)) := by
  simp only [add, Bool.false_eq_true, ↓reduceIte]
  split
  · rename_i ho; simp [BitVec.uaddOverflow] at ho; try omega
  · rfl

nonvacuity_witness sub1_run := ⟨1, by decide, trivial⟩
nonvacuity_witness add1_run := ⟨0, by decide, trivial⟩

/-- The ghost values without the semaphore's part, after a change of `t`'s value. -/
theorem xs_upd (G : ThreadId → SGh X) (t : ThreadId) (g g' : SGh X) :
    xs (fun u => (upd G t g' u).2) = upd (xs fun u => (upd G t g u).2) t g'.2.2 := by
  funext u; simp only [xs, upd]; split <;> rfl

theorem xs_self (G : ThreadId → SGh X) (t : ThreadId) (g : SGh X) :
    xs (fun u => (upd G t g u).2) t = g.2.2 := by simp only [xs, upd_self]

/-- The holder's load of the permit count. -/
theorem wp_cntLoad (hP : S.Fits P U) {s : σ} {t : ThreadId} {G : ThreadId → SGh X} {m : Mem}
    {n : Nat} {pa hL : Heap} {sp : SPh} {x : X}
    {Q : BitVec 64 × σ → (ThreadId → SGh X) → Mem → Nat → Prop}
    (hi : P.inv (upd G t (⟨.holds, pa, hL⟩, sp, x)) m) (hc : m.current = t)
    (h : ∀ m' hL', m'.current = t → P.inv (upd G t (⟨.holds, pa, hL'⟩, sp, x)) m' →
      Q (S.pv (xs fun u => (upd G t (⟨.holds, pa, hL⟩, sp, x) u).2), s) G m' n) :
    P.WP t ((liftM (load (BitVec 64) 8 S.ptr) : CM Tgt σ (BitVec 64)).run s) Q G m n :=
  wp_cnt hP (Mv := (· = pa)) hi hc (TTriple.load (by decide)) rfl
    (fun hr hrr hd => ⟨pa, hr, rfl, hd, hrr, rfl, rfl⟩) (.inl rfl)
    (fun m' h₁ h₂ pa' hpa hu => by
      subst hpa
      have := hP.stable _ m' m' t (⟨.holds, pa', h₂⟩, sp, x) hu (Step.refl t m') (by rw [upd_self])
        (by rw [upd_self]) (fun h => .inl (by rw [upd_self]; exact h))
        (fun h => by rw [upd_self] at h; rcases h with h | h <;> exact absurd rfl h)
      rwa [upd_upd] at this)
    fun m' pa' hL' hpa hc' _ hi' => by subst hpa; exact h m' hL' hc' hi'

section SemWait

variable (t : ThreadId) (pa : Heap) (x : X)

/-- `wait`'s loop: `t` holds the mutex at `x`. -/
def inv5 (D : Nat) (_ : Io_Semaphore_waitUncancelableLocals) (G : ThreadId → SGh X) (m : Mem)
    (d : Nat) : Prop :=
  d ≤ D ∧ m.current = t ∧ ∃ hL, P.inv (upd G t (⟨.holds, pa, hL⟩, .none, x)) m

/-- `wait`'s loop ends when `t` sees a permit. -/
def post5 (D : Nat) (r : Io_Semaphore_waitUncancelableExit × Io_Semaphore_waitUncancelableLocals)
    (G : ThreadId → SGh X) (m : Mem) (d : Nat) : Prop :=
  d ≤ D ∧ r.1 = .br4 ∧ m.current = t ∧ ∃ hL, P.inv (upd G t (⟨.holds, pa, hL⟩, .none, x)) m ∧
    S.pv (xs fun u => (upd G t (⟨.holds, pa, hL⟩, .none, x) u).2) ≠ 0

theorem loop5_body (hP : S.Fits P U) (io : Io)
    (hone : ∀ G' m', P.inv G' m' → (G' t).2.2 = x → (G' t).1.ph = .holds → S.PZ m' → ∀ u, u ≠ t →
      ∀ i jr sn e, (G' u).2.1 ≠ .reg i jr sn e) (hwx : S.wx x) (hinS : S.inS x)
    (D : Nat) (s : Io_Semaphore_waitUncancelableLocals) (G : ThreadId → SGh X) (m : Mem) (d : Nat)
    (h : inv5 (P := P) t pa x D s G m d) :
    P.WP t ((Io_Semaphore_waitUncancelable.loop5 S.ptr io).run s) (fun r G' m' d' =>
      if Io_Semaphore_waitUncancelable.again5 r.1 then inv5 (P := P) t pa x D r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : Io_Semaphore_waitUncancelableLocals) => 0) s)
      else post5 (S := S) (P := P) t pa x D r G' m' d') G m d := by
  obtain ⟨hD, hc, hL, hi⟩ := h
  unfold Io_Semaphore_waitUncancelable.loop5
  simp only [StateT.run_bind, pure_bind]
  refine WP.bind (WP.bind (wp_cntLoad hP hi hc fun m' hL' hc' hi' => ?_))
  by_cases hz : S.pv (xs fun u => (upd G t (⟨.holds, pa, hL⟩, .none, x) u).2) = 0
  · rw [hz]
    simp only [beq_self_eq_true, ↓reduceIte, StateT.run_bind]
    have hz' : ∃ hp, pts S.ptr 8 (0 : BitVec 64) hp ∧ hp.Sub hL' := by
      obtain ⟨hl', -, -⟩ := hP.split hi'
      have := hl'.res t (by rw [upd_self]; rfl)
      rw [show S.L.held (upd G t (⟨.holds, pa, hL'⟩, .none, x) t) = hL' by rw [upd_self]; rfl] at this
      obtain ⟨hp, hr, -, rfl, hpp, -⟩ := this
      refine ⟨hp, ?_, fun l c h => by simp [h]⟩
      have e : xs (fun u => (upd G t (⟨.holds, pa, hp ∪ hr⟩, .none, x) u).2) =
          xs (fun u => (upd G t (⟨.holds, pa, hL⟩, .none, x) u).2) := by
        funext u; simp only [xs, upd]; split <;> rfl
      rw [e, hz] at hpp; exact hpp
    refine WP.bind (WP.callMC_ptrProject (hP.projS hi' (k := 12) (by decide)) ?_)
    refine WP.bind (WP.callMC_ptrProject (hP.projS hi' (k := 8) (by decide)) ?_)
    refine WP.bind (WP.callC (WP.mono ?_ (condWait_spec hP t pa hL' x io G m' d hi' hz' hone hwx hinS)))
    rintro _ G₁ m₁ d₁ ⟨hd₁, hc₁, hL₁, hi₁⟩
    simp only [StateT.run_pure]
    refine WP.pure' (WP.pure' ?_)
    simp only [Io_Semaphore_waitUncancelable.again5, ↓reduceIte]
    exact ⟨⟨by omega, hc₁, hL₁, hi₁⟩, .inl hd₁⟩
  · have hne : (S.pv (xs fun u => (upd G t (⟨.holds, pa, hL⟩, .none, x) u).2) == 0) = false := by
      simpa using hz
    simp only [hne, Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
    refine WP.pure' (WP.pure' ?_)
    simp only [Io_Semaphore_waitUncancelable.again5, Bool.false_eq_true, ↓reduceIte]
    refine ⟨hD, rfl, hc', hL', hi', ?_⟩
    have e : xs (fun u => (upd G t (⟨.holds, pa, hL'⟩, .none, x) u).2) =
        xs (fun u => (upd G t (⟨.holds, pa, hL⟩, .none, x) u).2) := by
      funext u; simp only [xs, upd]; split <;> rfl
    rw [e]; exact hz

end SemWait


theorem xs_eq (G : ThreadId → SGh X) (t : ThreadId) (a a' : LG) (sp sp' : SPh) (x : X) :
    xs (fun u => (upd G t (a, sp, x) u).2) = xs (fun u => (upd G t (a', sp', x) u).2) := by
  funext u; simp only [xs, upd]; split <;> rfl

/-- `wait` by `t` at `x`, out of the semaphore: it takes a permit, and with it the resource `T`
(`hmv`); its part grows by `T`, its ghost value is `x'`. -/
theorem wait_spec (hP : S.Fits P U) (t : ThreadId) (pa : Heap) (x x' : X) (T : Assn) (io : Io)
    (hone : ∀ G' m', P.inv G' m' → (G' t).2.2 = x → (G' t).1.ph = .holds → S.PZ m' → ∀ u, u ≠ t →
      ∀ i jr sn e, (G' u).2.1 ≠ .reg i jr sn e) (hwx : S.wx x) (hinS : S.inS x)
    (hinS' : S.inS x')
    (hmv : ∀ Y : ThreadId → X, Y t = x → S.pv Y ≠ 0 → S.pv (upd Y t x') = S.pv Y - 1 ∧
      ∀ hr, S.Res Y hr → ∃ h₁ h₂, hr = h₁ ∪ h₂ ∧ Heap.Disjoint h₁ h₂ ∧ S.Res (upd Y t x') h₁ ∧ T h₂)
    (hU : ∀ G m h₁ h₂ h₃ h₄, T h₃ → Heap.Disjoint h₄ h₃ →
      S.Res (xs fun u => (upd G t (⟨.holds, pa, h₁⟩, .none, x) u).2) (h₄ ∪ h₃) →
      U (upd G t (⟨.holds, pa, h₁⟩, .none, x)) m → U (upd G t (⟨.holds, pa ∪ h₃, h₂⟩, .none, x')) m)
    (G : ThreadId → SGh X) (m : Mem) (d : Nat)
    (hi : P.inv (upd G t (⟨.out, pa, Heap.empty⟩, .none, x)) m) :
    P.WP t (Io_Semaphore_waitUncancelable S.ptr io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ h₃, T h₃ ∧ P.inv (upd G' t (⟨.out, pa ∪ h₃, Heap.empty⟩, .none, x')) m') G m d := by
  unfold Io_Semaphore_waitUncancelable
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  refine WP.bind (WP.callMC_ptrProject (hP.projS hi (k := 8) (by decide)) ?_)
  rw [ptr_mutex]
  refine WP.bind (WP.callC (WP.mono ?_ (MutexOps.lock_specOn hP.lf rfl rfl t
    (⟨.out, pa, Heap.empty⟩, .none, x) rfl ⟨rfl, hinS⟩ io G m d hi)))
  rintro _ G₁ m₁ d₁ ⟨hd₁, hc₁, hL₁, hi₁⟩
  refine WP.bind (WP.mono ?_ (WP.loop _ _ (inv5 (P := P) t pa x d₁) (fun _ => 0)
    (post5 (S := S) (P := P) t pa x d₁) (loop5_body t pa x hP io hone hwx hinS d₁) _ G₁ m₁ d₁
    ⟨by omega, hc₁, hL₁, hi₁⟩))
  rintro ⟨e, s'⟩ G₂ m₂ d₂ ⟨hd₂, rfl, hc₂, hL₂, hi₂, hz₂⟩
  simp only [StateT.run_bind]
  refine WP.bind (wp_cntLoad hP hi₂ hc₂ fun m₃ hL₃ hc₃ hi₃ => ?_)
  refine WP.bind (WP.callRC_ok (sub1_run hz₂) ?_)
  have hY := xs_self G₂ t (⟨.holds, pa, hL₃⟩, .none, x)
  have hxs := xs_eq G₂ t ⟨.holds, pa, hL₃⟩ ⟨.holds, pa, hL₂⟩ .none .none x
  refine WP.bind (wp_cnt hP (Mv := fun pa' => ∃ h₃ h₄, T h₃ ∧ pa' = pa ∪ h₃ ∧ Heap.Disjoint h₄ h₃ ∧
      S.Res (xs fun u => (upd G₂ t (⟨.holds, pa, hL₂⟩, .none, x) u).2) (h₄ ∪ h₃)) (x' := x') (r₀ := ()) hi₃ hc₃
    (TTriple.conseq (TTriple.store (by decide) _) (fun _ h => h) fun _ _ hq => sep_lift.mpr ⟨Subsingleton.elim _ _, hq⟩)
    (by rw [hxs]) (fun hr hrr hdr => ?_) (.inr (.inl hz₂))
    (fun m' h₁ h₂ pa' ⟨h₃, h₄, hT, hpa, hd4, hR4⟩ hu => by
      subst hpa; exact hU _ _ _ _ _ _ hT hd4 (by rw [xs_eq G₂ t _ ⟨.holds, pa, hL₂⟩]; exact hR4) hu)
    fun m₄ pa' hL₄ ⟨h₃, _, hT, hpa, _, _⟩ hc₄ _ hi₄ => ?_)
  · rw [hxs] at hrr hY
    obtain ⟨hpv, hres⟩ := hmv (xs fun u => (upd G₂ t (⟨.holds, pa, hL₂⟩, .none, x) u).2) hY hz₂
    obtain ⟨h₁, h₂, rfl, hd12, hr1, hT2⟩ := hres hr hrr
    obtain ⟨hdp1, hdp2⟩ := Heap.disjoint_union_right.mp hdr
    refine ⟨pa ∪ h₂, h₁, ?_, Heap.disjoint_union_left.mpr ⟨hdp1, hd12.symm⟩, ?_, ?_, h₂, h₁, hT2, rfl, hd12, hrr⟩
    · rw [Heap.union_assoc, Heap.union_comm hd12.symm]
    · rw [xs_upd G₂ t (⟨.holds, pa, hL₂⟩, .none, x)]; exact hr1
    · rw [xs_upd G₂ t (⟨.holds, pa, hL₂⟩, .none, x)]; exact hpv
  subst hpa
  refine WP.bind (wp_cntLoad hP hi₄ hc₄ fun m₅ hL₅ hc₅ hi₅ => ?_)
  have hfin : ∀ G₆ m₆ d₆ hL₆, d₆ ≤ d₁ → m₆.current = t →
      P.inv (upd G₆ t (⟨.holds, pa ∪ h₃, hL₆⟩, .none, x')) m₆ →
      P.WP t ((do
        let i32 ← callMC (ptrProject S.ptr (·.add 8))
        let _i33 ← callC (Io_Mutex_unlock i32 io)
        pure Io_Semaphore_waitUncancelableExit.ret : CM Tgt Io_Semaphore_waitUncancelableLocals _).run
          s') (fun a G' m' d' => P.WP t (match a.1 with
            | .ret => pure ()
            | _ => throw .panic) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
              ∃ h₃, T h₃ ∧ P.inv (upd G' t (⟨.out, pa ∪ h₃, Heap.empty⟩, .none, x')) m') G' m' d')
        G₆ m₆ d₆ := by
    intro G₆ m₆ d₆ hL₆ hd₆ _ hi₆
    simp only [StateT.run_bind]
    refine WP.bind (WP.callMC_ptrProject (hP.projS hi₆ (k := 8) (by decide)) ?_)
    rw [ptr_mutex]
    refine WP.bind (WP.callC (WP.mono ?_ (MutexOps.unlock_specOn hP.lf rfl rfl t
      (⟨.holds, pa ∪ h₃, hL₆⟩, .none, x') rfl ⟨rfl, hinS'⟩ io G₆ m₆ d₆ hi₆)))
    rintro _ G₇ m₇ d₇ ⟨hd₇, hc₇, hi₇⟩
    exact WP.pure' (WP.pure' ⟨by omega, hc₇, h₃, hT, hi₇⟩)
  dsimp only
  by_cases hgt : gt false (S.pv (xs fun u => (upd G₂ t (⟨.holds, pa ∪ h₃, hL₄⟩, .none, x') u).2))
    (0 : BitVec 64) = true
  · rw [hgt]
    simp only [↓reduceIte, StateT.run_bind]
    have hp₅ := hP.toPst hinS' hi₅ rfl
    refine WP.bind (WP.bind (WP.callMC_ptrProject (hP.projS hi₅ (k := 12) (by decide)) ?_))
    dsimp only
    refine WP.bind (WP.callC (WP.mono ?_ (signal_spec hP t ⟨.holds, pa ∪ h₃, hL₅⟩ x' rfl hinS' io G₂ m₅ d₂
      hp₅)))
    rintro _ G₆ m₆ d₆ ⟨hd₆, hc₆, hi₆⟩
    simp only [StateT.run_pure]
    refine WP.pure' ?_
    exact hfin G₆ m₆ d₆ hL₅ (by omega) hc₆ hi₆
  · simp only [Bool.not_eq_true] at hgt
    rw [hgt]
    simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind]
    exact hfin G₂ m₅ d₂ hL₅ hd₂ hc₅ hi₅


/-- `post` by `t` at `x`, with the resource `h₃` of a permit in its part: it gives the permit and
`h₃` back (`hmv`); its part is `pa`, its ghost value `x'`. -/
theorem post_spec (hP : S.Fits P U) (t : ThreadId) (pa h₃ : Heap) (x x' : X) (io : Io)
    (hinS : S.inS x) (hinS' : S.inS x')
    (hmv : ∀ G m hL, P.inv (upd G t (⟨.holds, pa ∪ h₃, hL⟩, .pst, x)) m →
      S.pv (upd (xs fun u => (upd G t (⟨.holds, pa ∪ h₃, hL⟩, .pst, x) u).2) t x') =
        S.pv (xs fun u => (upd G t (⟨.holds, pa ∪ h₃, hL⟩, .pst, x) u).2) + 1 ∧
      (S.pv (xs fun u => (upd G t (⟨.holds, pa ∪ h₃, hL⟩, .pst, x) u).2)).toNat + 1 < 2 ^ 64 ∧
      ∀ hr, S.Res (xs fun u => (upd G t (⟨.holds, pa ∪ h₃, hL⟩, .pst, x) u).2) hr →
        Heap.Disjoint h₃ hr →
        S.Res (upd (xs fun u => (upd G t (⟨.holds, pa ∪ h₃, hL⟩, .pst, x) u).2) t x') (h₃ ∪ hr))
    (hU : ∀ G m h₁ h₂, U (upd G t (⟨.holds, pa ∪ h₃, h₁⟩, .pst, x)) m →
      U (upd G t (⟨.holds, pa, h₂⟩, .pst, x')) m)
    (hdj : Heap.Disjoint pa h₃) (G : ThreadId → SGh X) (m : Mem) (d : Nat)
    (hi : P.inv (upd G t (⟨.out, pa ∪ h₃, Heap.empty⟩, .none, x)) m) :
    P.WP t (Io_Semaphore_post S.ptr io) (fun _ G' m' d' => d' ≤ d ∧ m'.current = t ∧
      P.inv (upd G' t (⟨.out, pa, Heap.empty⟩, .none, x')) m') G m d := by
  unfold Io_Semaphore_post
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, pure_bind]
  refine WP.bind (WP.callMC_ptrProject (hP.projS hi (k := 8) (by decide)) ?_)
  rw [ptr_mutex]
  refine WP.bind (WP.callC (WP.mono ?_ (MutexOps.lock_specOn hP.lf rfl rfl t
    (⟨.out, pa ∪ h₃, Heap.empty⟩, .none, x) rfl ⟨rfl, hinS⟩ io G m d hi)))
  rintro _ G₁ m₁ d₁ ⟨hd₁, hc₁, hL₁, hi₁⟩
  have hp₁ := hP.toPst hinS hi₁ rfl
  refine WP.bind (wp_cntLoad hP hp₁ hc₁ fun m₂ hL₂ hc₂ hi₂ => ?_)
  obtain ⟨hpv, hlt, hres⟩ := hmv G₁ m₁ hL₁ hp₁
  refine WP.bind (WP.callRC_ok (add1_run hlt) ?_)
  have hxs := xs_eq G₁ t ⟨.holds, pa ∪ h₃, hL₂⟩ ⟨.holds, pa ∪ h₃, hL₁⟩ .pst .pst x
  refine WP.bind (wp_cnt hP (Mv := (· = pa)) (x' := x') (r₀ := ()) hi₂ hc₂
    (TTriple.conseq (TTriple.store (by decide) _) (fun _ h => h) fun _ _ hq => sep_lift.mpr ⟨Subsingleton.elim _ _, hq⟩)
    (by rw [hxs]) (fun hr hrr hdr => ?_) (.inr (.inr rfl))
    (fun m' h₁ h₂ pa' hpa hu => by subst hpa; exact hU _ _ _ _ hu)
    fun m₃ pa' hL₃ hpa hc₃ _ hi₃ => ?_)
  · rw [hxs] at hrr
    obtain ⟨hd3, hdr'⟩ := Heap.disjoint_union_left.mp hdr
    refine ⟨pa, h₃ ∪ hr, (Heap.union_assoc _ _ _).symm, Heap.disjoint_union_right.mpr ⟨hdj, hd3⟩,
      ?_, ?_, rfl⟩
    · rw [xs_upd G₁ t (⟨.holds, pa ∪ h₃, hL₁⟩, .pst, x)]; exact hres hr hrr hdr'
    · rw [xs_upd G₁ t (⟨.holds, pa ∪ h₃, hL₁⟩, .pst, x)]; exact hpv
  subst hpa
  refine WP.bind (WP.callMC_ptrProject (hP.projS hi₃ (k := 12) (by decide)) ?_)
  refine WP.bind (WP.callC (WP.mono ?_ (signal_spec hP t ⟨.holds, pa', hL₃⟩ x' rfl hinS' io G₁ m₃ d₁ hi₃)))
  rintro _ G₄ m₄ d₄ ⟨hd₄, hc₄, hi₄⟩
  refine WP.bind (WP.callMC_ptrProject (hP.projS hi₄ (k := 8) (by decide)) ?_)
  rw [ptr_mutex]
  refine WP.bind (WP.callC (WP.mono ?_ (MutexOps.unlock_specOn hP.lf rfl rfl t
    (⟨.holds, pa', hL₃⟩, .none, x') rfl ⟨rfl, hinS'⟩ io G₄ m₄ d₄ hi₄)))
  rintro _ G₅ m₅ d₅ ⟨hd₅, hc₅, hi₅⟩
  exact WP.pure' (WP.pure' ⟨by omega, hc₅, hi₅⟩)


/-- A word at the start: no atomic location, each access to it happened before every thread, and
the value 0. -/
theorem word_init {n nb : Nat} {W : Word n nb} {m : Mem} {b : BlockId} {blk : Block} (hW : W.b = b)
    (hb : m.blocks[b]? = some blk) (hl : blk.live = true) (hfit : W.o + nb ≤ blk.bytes.size)
    (hal : (blk.addr + W.o) % nb = 0) (hk : blk.kind = .stack) (hat : m.atomics = #[])
    (hv : (intOfBytes n (blk.bytes.extract W.o (W.o + nb))).run = some (.ok 0))
    (hfp : ∀ e ∈ m.footprint, W.Hits e → AllLe m e.clock) :
    W.Ok m ∧ (W.hist m).size = 1 ∧ (W.hist m)[0]!.Val (0 : BitVec n) := by
  have hno : ∀ i l, ¬ W.Loc m i l := fun i l hl => by
    have := (Word.loc_get hl).1; rw [hat] at this; simp at this
  have hu : W.Holds m 0 := by unfold Word.Holds curBytes; rw [hW, hb]; exact hv
  refine ⟨⟨⟨blk, by rw [hW]; exact hb, hl, hfit, hal, by rw [hk]; decide⟩,
    fun l hl' => by rw [hat] at hl'; simp at hl', fun i l h => absurd h (hno i l),
    fun e he hh => .inr (hfp e he hh), ⟨0, hu⟩, fun i l h => absurd h (hno i l)⟩, ?_, ?_⟩
  · rw [Word.hist_none hno]; rfl
  · rw [Word.hist_none hno]; exact hu

theorem allLe_nil (m : Mem) : AllLe m #[] := fun _ _ => VClock.le_iff.mpr fun i => by
  simp [VClock.get]

/-- The condition's invariant at the semaphore's start: each word has one write, `0`, and no
thread is in the condition's code. -/
theorem Inv.start {G : ThreadId → SGh X} {m : Mem} (hws : S.WS.Ok m) (hwe : S.WE.Ok m)
    (hsz : (S.WS.hist m).size = 1) (hs0 : (S.WS.hist m)[0]!.Val (0 : BitVec 32))
    (hez : (S.WE.hist m).size = 1) (hal : AllLe m (S.WE.hist m)[0]!.clock)
    (hnone : ∀ u, (G u).2.1 = .none) (hq : ∀ w ∈ m.waiters, w.2 ≠ S.WE.ptr)
    (hoff : ∀ u x, S.o + 12 ≤ x → x < S.o + 20 → (G u).1.part (S.b, x) = none) : S.Inv G m := by
  have hn : ∀ u p, (G u).2.1 = p → p = .none := fun u p h => h ▸ hnone u
  refine ⟨hws, hwe, fun k hk => ⟨0, .inl rfl, by rw [show k = 0 by omega]; exact hs0⟩,
    fun u _ _ _ _ _ _ _ _ _ hu => absurd (hn u _ hu) (by simp),
    fun _ => by simp only [last, hsz]; exact hs0,
    fun u _ _ _ _ hu => absurd (hn u _ hu) (by simp),
    .inr (.inr (by simp only [last, hez]; exact hal)),
    fun u hu => absurd hu (by rw [hnone u]; decide), fun u _ _ hu => absurd (hn u _ hu) (by simp),
    fun u hu => absurd (hn u _ hu) (by simp), fun u hu => absurd (hn u _ hu) (by simp),
    fun w hw he => absurd he (hq w hw), hoff⟩

end Sem
end Sync
