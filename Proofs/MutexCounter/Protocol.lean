import ZigLean.Sep.Full.Mutex
import ZigLean.Sep.Full.ThreadFacts
import ZigLean.Sep.Full.Local
import ZigLean.Sep.Full.Word
import ZigLean.Conc.Share
import ZigLean.Sep.Full.Auto
import ZigLean.Sep.Full.LockSteps

/-!
# The protocol of `mutexCounter`, once for every version

`mutexCounter` (examples/sync, Zig 0.16.0 and 0.17.0 `std.Io`; examples/threadsync, Zig 0.15.2
`std.Thread`) is the same program in each version: `main` spawns one thread; each of the two
threads adds 1 two times to a counter under a mutex; `main` joins the kid and reads 4. The
versions differ in the `Counter`'s layout (0.16.0 has `io` first), in the mutex's contended value,
and in the generated code of the mutex (proved once per version against the contract
`MutexImpl`). This file is the protocol of that program for every layout (`Layout`) and every
mutex implementation: each version's file (`Proofs/Sync/Mutex.lean`, `Proofs/Threadsync/Mutex.lean`)
walks `main` and `work` of its generated code with the steps here.

- **Ghost values** (`Gh = FLG × Ph`): the lock's part (`FLG`), and where the thread is in `main`
  or `work` (`Ph`), with its number of increments.
- **The lock** (`L`, `FLock.prod`): the mutex owns the counter, whose value is the number of
  increments of both threads (`R`).
- **The protocol's rest** (`IoRest`): the bytes of `io` (0.16.0 and 0.17.0: read-shared, `IoR`)
  and the `Counter`'s full extent, which pins the block for every thread's step (`blk_of`).
- **The rest of the invariant** (`U`): the threads (`Shape`), the read shares of `io`, and no
  thread has a part.
-/

namespace Zig
namespace MutexCounter

open Conc Conc.Proto Full Full.FAssn

/-- The `Counter`'s layout (module doc): its size and alignment, the length of the `io` prefix
(`0` when there is none), the offset of the mutex (the counter follows it), and the mutex's
contended value `c`. -/
structure Layout where
  size : Nat
  align : Nat
  io : Nat
  mo : Nat
  c : Nat
  c_ok : c = 1 ∨ c = 2 ∨ c = 3
  /-- `io`, then the mutex and the counter at the end, 4-aligned. -/
  ok : io ≤ mo ∧ mo + 8 = size ∧ mo % 4 = 0 ∧ 0 < align ∧ 4 ∣ align

/-- The `Counter` (block 0). -/
def cPtr : Ptr := ⟨some 0, 0⟩

/-- Where a thread is, outside the lock's code. -/
inductive Ph where
  | none
  /-- `main` before its spawn. -/
  | pre
  /-- A thread in `work`: it did `k` increments. -/
  | work (k : Nat)
  /-- `main` at its join. -/
  | joins
  /-- The kid has ended. -/
  | fin

/-- The increments of a thread. -/
def Ph.count : Ph → Nat
  | .work k => k
  | .joins | .fin => 2
  | _ => 0

abbrev Gh := FLG × Ph

/-- The increments of both threads. -/
def sum (X : ThreadId → Ph) : Nat := (X 0).count + (X 1).count

variable (Lo : Layout)

/-- The counter holds the increments of both threads. -/
def R (X : ThreadId → Ph) : FAssn := up (pts (cPtr.add (Lo.mo + 4)) 4 (BitVec.ofNat 32 (sum X)))

/-- The mutex. It owns the counter. -/
abbrev L : FLock Gh := FLock.prod 0 Lo.mo (R Lo) Lo.c Lo.c_ok

/-- The accesses to the bytes of `io` (`0 .. io` of the `Counter`; a zero-length access touches
none). -/
def IoR (e : FootprintEntry) : Prop := e.block = 0 ∧ 0 < e.len ∧ e.off < Lo.io

/-- The bytes of `io` and the `Counter`'s full extent: the protocol's rest. The extent pins the
block (its size and kind) in every memory of the protocol (`blk_of`). -/
def IoRest (r : Res) : Prop :=
  ∃ A bs, A % Lo.align = 0 ∧ bs.size = Lo.io ∧ (Lo.io = Enc.size Io → Enc.decode bs = pure (⟨⟩ : Io)) ∧
    (up (bytesAt cPtr A Lo.size .stack bs) ⋆ bext 0 Lo.size .stack) r

/-- Block 0 is the live `Counter`, `size` bytes on the stack. -/
def BlkOk (m : Mem) : Prop :=
  ∃ blk, m.blocks[0]? = some blk ∧ blk.live = true ∧ blk.bytes.size = Lo.size ∧ blk.kind = .stack

/-- The threads: `main` alone before its spawn; then `main` and the kid, which `main` spawned
and did not join yet. -/
def Shape (X : ThreadId → Ph) (m : Mem) : Prop :=
  m.threads[0]? = some { spawner := 0, joined := true } ∧
  ((m.threads.size = 1 ∧ X 0 = .pre ∧ ∀ u, 1 ≤ u → X u = .none) ∨
   (m.threads.size = 2 ∧ m.threads[1]? = some { spawner := 0, joined := false } ∧
    (X 0 = .joins ∨ ∃ k ≤ 2, X 0 = .work k) ∧ (X 1 = .fin ∨ ∃ k ≤ 2, X 1 = .work k) ∧
    ∀ u, 2 ≤ u → X u = .none))

/-- The rest of the invariant (module doc). -/
structure U (G : ThreadId → Gh) (rX : Res) (m : Mem) : Prop where
  shape : Shape (fun u => (G u).2) m
  io : ReadShared (IoR Lo) m
  parts : ∀ u, (G u).1.part = rnil
  rest : IoRest Lo rX

variable {Tgt : Type}

/-- The protocol, in strict mode; `workOf` reads the kid's argument from a spawn target. -/
def proto (workOf : Tgt → Option Ptr) : Proto Tgt Gh where
  inv G m := ∃ rX, (L Lo).Inv G rX m ∧ U Lo G rX m
  init tgt g := workOf tgt = some cPtr ∧ g = (⟨.out, rnil, rnil⟩, .work 0)
  fin g := g.1.ph = .gone ∧ g.2 = .fin
  strict := true
  joins g := g.1.ph = .out ∧ g.2 = .joins

/-- `main`'s post: the result. -/
def QM : Except ErrName (BitVec 32) → (ThreadId → Gh) → Mem → Nat → Prop :=
  fun v _ m _ => v = .ok 4 ∧ joinedAll 0 m

variable {Lo} {workOf : Tgt → Option Ptr}

/-! ## The protocol has the lock -/

/-- The access `e` of the mutex's word is not to `io`. -/
theorem io_notL {e : FootprintEntry} (h : e.off = (L Lo).o) : ¬ IoR Lo e := fun ⟨_, _, h2⟩ => by
  have := Lo.ok; simp [L, FLock.prod] at h; omega

theorem stable (G : ThreadId → Gh) (rX : Res) (m m' : Mem) (t : ThreadId) (p : LPh) (h : Res)
    (_ : (L Lo).ph (G t) ≠ .gone) (hu : U Lo G rX m) (hs : (L Lo).Step t m m')
    (_ : (L Lo).ph (G t) = .holds → p ≠ .holds → (L Lo).Before m' (m.clocks[t]!)) :
    U Lo (upd G t ((L Lo).set (G t) p h)) rX m' := by
  obtain ⟨hsh, hio, hpart, hrest⟩ := hu
  have hX : ∀ u, (upd G t ((L Lo).set (G t) p h) u).1.part = (G u).1.part := fun u => by
    unfold upd; split
    · rename_i e; subst e; rfl
    · rfl
  refine ⟨?_, fun e he hr => ?_, fun u => by rw [hX]; exact hpart u, hrest⟩
  · rw [FLock.snd_set]; unfold Shape at hsh ⊢; rw [hs.threads]; exact hsh
  · rcases hs.fp e he with h' | ⟨-, ho', -⟩
    · rcases hio e h' hr with ⟨hk, h''⟩ | h''
      · exact .inl ⟨hk, hs.someLe h''⟩
      · exact .inr (hs.allLe h'')
    · exact absurd hr (io_notL ho')

theorem fits : (L Lo).Fits (FPrim.empty Gh) (proto Lo workOf) (U Lo) fun _ => True :=
  .ofLockAll (fun _ _ => Iff.rfl) (fun _ h => h.1) (fun _ h => h.1) stable

/-- The protocol's invariant at a stop of `t`. -/
theorem inv_cur {G : ThreadId → Gh} {m : Mem} (t : ThreadId) (hi : (proto Lo workOf).inv G m)
    (hph : (G t).1.ph ≠ .gone) : (proto Lo workOf).inv G { m with current := t } := by
  obtain ⟨-, -, -, h⟩ := (fits (Lo := Lo) (workOf := workOf)).cur t hi hph
  exact h

/-! ## The `Counter` -/

/-- **The `Counter` is block 0**: live, `size` bytes on the stack (the extent in the rest). -/
theorem blk_of {G : ThreadId → Gh} {rX : Res} {m : Mem} (hi : (L Lo).Inv G rX m)
    (hr : IoRest Lo rX) : BlkOk Lo m := by
  obtain ⟨rL, ho, -⟩ := hi.rest
  obtain ⟨rT, -, hh⟩ := ho.holds
  have he := hh.swap.extTrue
  obtain ⟨A, bs, -, -, -, r₁, r₂, -, rfl, -, h2⟩ := hr
  simp only at he
  rw [Ghost.add_comm] at he; replace he := ExtTrue.of_add he
  rw [Ghost.add_comm] at he; replace he := ExtTrue.of_add he
  rw [Ghost.add_comm] at he; replace he := ExtTrue.of_add he
  rw [bauth_eq h2] at he
  obtain ⟨blk, h1, h2, h3, h4, -⟩ := (he 0).1 Lo.size .stack (by simp [Ghost.atExt, ECell.auth1])
  exact ⟨blk, h1, h2, h3, h4⟩

/-- The `Counter` is block 0, from the protocol's invariant. -/
theorem blk_inv {G : ThreadId → Gh} {m : Mem} (hi : (proto Lo workOf).inv G m) : BlkOk Lo m := by
  obtain ⟨rX, hiL, hu⟩ := hi; exact blk_of hiL hu.rest

/-- A field pointer of the `Counter` (block 0) is formed (`ptrProject`, MM-3). -/
theorem proj {m : Mem} (hb : BlkOk Lo m) {k : Nat} (hk : k ≤ Lo.size) :
    (ptrProject cPtr (·.add k)).run m = pure (cPtr.add k, m) := by
  obtain ⟨blk, hb, -, hsz, -⟩ := hb
  exact ptrProject_block_run hb rfl (by decide) (by simp [cPtr, hsz]; omega)

/-- A field pointer of the `Counter` from the protocol's invariant. -/
theorem projI {G : ThreadId → Gh} {m : Mem} (hi : (proto Lo workOf).inv G m) {k : Nat}
    (hk : k ≤ Lo.size) : (ptrProject cPtr (·.add k)).run m = pure (cPtr.add k, m) :=
  proj (blk_inv hi) hk

/-- A field pointer of the `Counter` from `main`'s part before its spawn (the `Counter`'s bytes
and its extent). -/
theorem projO {own : ThreadId → Res} {rO : Res} {m : Mem} (ho : FOwned own rO m)
    (ht : 0 < m.threads.size) {A S : Nat} {bs : Array Byte}
    (h : (up (bytesAt cPtr A S .stack bs) ⋆ bext 0 S .stack) (own 0)) {k : Nat} (hk : k ≤ S) :
    (ptrProject cPtr (·.add k)).run m = pure (cPtr.add k, m) := by
  obtain ⟨blk, hb, -, hsz, -⟩ := ho.blkOf ht (Full.sep_comm h)
  exact ptrProject_block_run hb rfl (by decide) (by simp [cPtr, hsz]; omega)

/-- The rest has the bytes of `io`. -/
theorem rest_io {rX : Res} (hr : IoRest Lo rX) {x : Nat} (hx : x < Lo.io) :
    rX.heap (0, x) ≠ none := by
  obtain ⟨A, bs, -, hbs, -, r₁, r₂, -, rfl, h1, -⟩ := hr
  have := (up_bytesAt_some h1 rfl (0, x)).mpr ⟨rfl, by simp [cPtr], by simp [cPtr, hbs]; omega⟩
  simp only [FHeap.union_apply, ne_eq, Option.or_eq_none_iff, not_and]
  intro h; exact absurd h this

/-! ## `io` -/

/-- **A read of `n` bytes of `io`** by the current thread keeps `U` (`io` is read-shared). -/
theorem U_rec {G : ThreadId → Gh} {rX : Res} {m : Mem} (n : Nat) (hu : U Lo G rX m)
    (ht : m.current < m.threads.size) (hcs : m.clocks.size = m.threads.size) :
    U Lo G rX (m.recordAt 0 0 n .read) :=
  ⟨hu.shape, hu.io.read ht hcs 0 0 n, hu.parts, hu.rest⟩

/-- **`io` is in the rest** (the obligation of `FLock.Fits.wp_readRest`, the read of `io`), for
a layout with an `io` prefix of `Io`'s size whose load alignment `a` divides the `Counter`'s: its
bytes, which decode to `io`, at the `Counter`'s aligned address. -/
theorem io_rest {a : Nat} (hio : Lo.io = Enc.size Io) (ha : a ∣ Lo.align) (G : ThreadId → Gh)
    (rX : Res) (m : Mem) (hu : U Lo G rX m) :
    ∃ r A S K' bs, up (bytesAt cPtr A S K' bs) r ∧
      (∀ l fc, r.heap l = some fc → rX.heap l = some fc) ∧ bs.size = Enc.size Io ∧
      Enc.decode bs = pure (⟨⟩ : Io) ∧ (A + cPtr.off.toNat) % a = 0 ∧ K' ≠ .constGlobal := by
  obtain ⟨A, bs, hA, hbs, hdec, r₁, r₂, -, hrX, h₁, -⟩ := hu.rest
  refine ⟨r₁, A, _, _, bs, h₁, fun l fc hl => by rw [hrX]; simp [FHeap.union_apply, hl],
    by rw [hbs, hio], hdec hio, ?_, by decide⟩
  simpa [cPtr] using Nat.mod_eq_zero_of_dvd (Nat.dvd_trans ha (Nat.dvd_of_mod_eq_zero hA))

/-- `io`'s accesses cover its bytes (`FLock.Fits.wp_readRest`). -/
theorem io_cov (hio : Lo.io = Enc.size Io) : Conc.Covers (IoR Lo) 0 cPtr.off.toNat (Enc.size Io) :=
  fun _ hb hl _ h2 => ⟨hb, hl, by simp [cPtr] at h2; omega⟩

/-! ## The threads -/

theorem shape_work {X : ThreadId → Ph} {m : Mem} {t k : Nat} (h : Shape X m) (hx : X t = .work k) :
    t < 2 ∧ m.threads.size = 2 ∧ k ≤ 2 := by
  obtain ⟨-, ⟨-, h0, h1⟩ | ⟨hs, -, h0, h1, h2⟩⟩ := h
  · by_cases ht : t = 0
    · subst ht; rw [h0] at hx; cases hx
    · rw [h1 t (Nat.pos_of_ne_zero ht)] at hx; cases hx
  · have htl : t < 2 := by
      by_cases hc : t < 2
      · exact hc
      · rw [h2 t (Nat.le_of_not_lt hc)] at hx; cases hx
    refine ⟨htl, hs, ?_⟩
    rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl
    · rcases h0 with h0 | ⟨k', hk, h0⟩ <;> rw [h0] at hx <;> cases hx; exact hk
    · rcases h1 with h1 | ⟨k', hk, h1⟩ <;> rw [h1] at hx <;> cases hx; exact hk

/-- A thread in `work` goes to `work k'` (`k' ≤ 2`), or to its end. -/
theorem shape_upd {X : ThreadId → Ph} {m : Mem} {t k k' : Nat} (h : Shape X m)
    (hx : X t = .work k) (hk : k' ≤ 2) (p : Ph) (hp : p = .work k' ∨ (t = 0 ∧ p = .joins) ∨
      (t = 1 ∧ p = .fin)) : Shape (upd X t p) m := by
  obtain ⟨htl, -, -⟩ := shape_work h hx
  obtain ⟨h00, ⟨-, h0, h1⟩ | ⟨hs, hr, h0, h1, h2⟩⟩ := h
  · rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl
    · rw [h0] at hx; cases hx
    · rw [h1 1 (Nat.le_refl _)] at hx; cases hx
  refine ⟨h00, .inr ⟨hs, hr, ?_, ?_, fun u hu => ?_⟩⟩
  · by_cases ht : t = 0
    · subst ht; rw [upd_self]
      rcases hp with rfl | ⟨-, rfl⟩ | ⟨h, -⟩
      · exact .inr ⟨k', hk, rfl⟩
      · exact .inl rfl
      · cases h
    · rw [upd_ne _ _ (Ne.symm ht)]; exact h0
  · by_cases ht : t = 1
    · subst ht; rw [upd_self]
      rcases hp with rfl | ⟨h, -⟩ | ⟨-, rfl⟩
      · exact .inr ⟨k', hk, rfl⟩
      · cases h
      · exact .inl rfl
    · rw [upd_ne _ _ (Ne.symm ht)]; exact h1
  · rw [upd_ne _ _ (by unfold ThreadId at *; omega)]; exact h2 u hu

/-- The sum, when one thread did `k` increments: at most `k + 2`. -/
theorem sum_le {X : ThreadId → Ph} {m : Mem} {t k : Nat} (h : Shape X m) (hx : X t = .work k) :
    sum X ≤ k + 2 := by
  obtain ⟨htl, hs2, -⟩ := shape_work h hx
  obtain ⟨-, ⟨hs1, -, -⟩ | ⟨-, -, h0, h1, -⟩⟩ := h
  · omega
  have c0 : (X 0).count ≤ 2 := by
    rcases h0 with h0 | ⟨k', hk, h0⟩
    · rw [h0]; decide
    · rw [h0]; exact hk
  have c1 : (X 1).count ≤ 2 := by
    rcases h1 with h1 | ⟨k', hk, h1⟩
    · rw [h1]; decide
    · rw [h1]; exact hk
  unfold sum
  rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl
  · rw [hx]; exact Nat.add_le_add_left c1 k
  · rw [hx, Nat.add_comm]; exact Nat.add_le_add_left c0 k

/-- One more increment of thread `t`: the sum is one more. -/
theorem sum_succ {X : ThreadId → Ph} {t k : Nat} (ht : t < 2) (hx : X t = .work k) :
    sum (upd X t (.work (k + 1))) = sum X + 1 := by
  unfold sum
  rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl
  · rw [upd_self, upd_ne _ _ (by decide : (1 : Nat) ≠ 0), hx]; simp only [Ph.count]; omega
  · rw [upd_self, upd_ne _ _ (by decide : (0 : Nat) ≠ 1), hx]; simp only [Ph.count]; omega

/-- `main` spawned every thread. -/
theorem spawners {X : ThreadId → Ph} {m : Mem} (h : Shape X m) : ∀ r ∈ m.threads, r.spawner = 0 :=
  spawners_of_getElem fun i hi => by
    obtain ⟨h0, ⟨h1, -⟩ | ⟨h2, h1, -⟩⟩ := h
    · obtain rfl : i = 0 := by omega
      rw [Array.getElem?_eq_getElem hi] at h0; rw [Option.some.inj h0]
    · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · rw [Array.getElem?_eq_getElem hi] at h0; rw [Option.some.inj h0]
      · rw [Array.getElem?_eq_getElem hi] at h1; rw [Option.some.inj h1]

/-! ## The holder's increment -/

/-- A thread in `work` out of the lock's code, after `k` increments. -/
def gOut (k : Nat) : Gh := (⟨.out, rnil, rnil⟩, .work k)

/-- A thread in `work` that holds the mutex and the counter `rL`, after `k` increments. -/
def gHold (k : Nat) (rL : Res) : Gh := (⟨.holds, rnil, rL⟩, .work k)

/-! The ghost values of the lock's product (`rfl`), for the walks of `work`. -/
theorem set_out (k : Nat) (rL : Res) : (L Lo).set (gOut k) .holds rL = gHold k rL := rfl
theorem set_hold (k : Nat) (rL : Res) : (L Lo).set (gHold k rL) .out rnil = gOut k := rfl
theorem ph_out (k : Nat) : (L Lo).ph (gOut k) = .out := rfl
theorem ph_hold (k : Nat) (rL : Res) : (L Lo).ph (gHold k rL) = .holds := rfl

/-- A step of thread `t` (not joined) that keeps the protocol's rest `rX` (`FStepIn`) keeps `U`,
with `t`'s new ghost value `g` (no part) and the shape `hsh`. -/
theorem U_step {G : ThreadId → Gh} {rX : Res} {m m' : Mem} {t : ThreadId} {g : Gh}
    (hu : U Lo G rX m) (hs : FStepIn rX.heap.erase m m') (hpart : g.1.part = rnil)
    (hsh : Shape (upd (fun u => (G u).2) t g.2) m) : U Lo (upd G t g) rX m' := by
  refine ⟨?_, fun e he hr => ?_, fun u => ?_, hu.rest⟩
  · rw [FLock.snd_upd]; unfold Shape at hsh ⊢; rw [hs.threads]; exact hsh
  · rcases hs.fp e he with ⟨e₀, he₀, hn⟩ | ⟨-, hnt, -⟩
    · obtain ⟨-, hb, hk, ho, hl, hcl⟩ := hn
      rcases hu.io e₀ he₀ ⟨hb.symm.trans hr.1, by have := hr.2.1; omega,
        by have := hr.2.2; omega⟩ with ⟨hk', h''⟩ | h''
      · exact .inl ⟨hk.trans hk', LockWord.someLe_mono hs.threads (fun u _ => hs.clock u)
          (LockWord.someLe_le hcl h'')⟩
      · exact .inr (LockWord.allLe_mono hs.threads (fun u _ => hs.clock u)
          fun u hu => VClock.le_trans hcl (h'' u hu))
    · refine absurd ⟨e.off, Nat.le_refl _, by have := hr.2.1; omega, ?_⟩ hnt
      rw [hr.1]
      simpa [FHeap.erase] using rest_io hu.rest hr.2.2
  · unfold upd; split
    · exact hpart
    · exact hu.parts u

/-- The counter's load by the holder after `k < 2` increments: the counter's value, at most 3. -/
theorem wp_load {t : ThreadId} {rL : Res} {k : Nat} (hk : k < 2)
    {G : ThreadId → Gh} {m : Mem} {d : Nat} {Q : BitVec 32 → (ThreadId → Gh) → Mem → Nat → Prop}
    (hi : (proto Lo workOf).inv (upd G t (gHold k rL)) m) (hc : m.current = t)
    (h : ∀ m' rQ, m'.current = t → sum (upd (fun u => (G u).2) t (.work k)) ≤ 3 →
      (proto Lo workOf).inv (upd G t (gHold k rQ)) m' →
      Q (BitVec.ofNat 32 (sum (upd (fun u => (G u).2) t (.work k)))) G m' d) :
    (proto Lo workOf).WP t
      (ConcM.liftMem (load (BitVec 32) 4 (cPtr.add (Lo.mo + 4))) : ConcM Tgt (BitVec 32)) Q G m d := by
  have e : ∀ r, (fun u => (upd G t (gHold k r) u).2) = upd (fun u => (G u).2) t (.work k) :=
    fun _ => FLock.snd_upd _ _ _
  have hsh : Shape (upd (fun u => (G u).2) t (.work k)) m := by
    obtain ⟨rX, -, hU⟩ := hi; rw [← e rL]; exact hU.shape
  refine (fits (Lo := Lo) (workOf := workOf)).wp_hold (g' := gHold k)
    (by fsym : FTTriple
      (up (pts (cPtr.add (Lo.mo + 4)) 4 (BitVec.ofNat 32 (sum (upd (fun u => (G u).2) t (.work k))))))
      _ _)
    (fun r h => by change R Lo _ r at h; unfold R at h; rwa [e] at h)
    (fun _ => ⟨rfl, by rw [upd_self]; rfl, rfl⟩)
    (fun a r h => by change R Lo _ r; unfold R; rw [upd_upd, e]; exact (Full.sep_lift.mp h).2)
    (fun rX m' r hU _ hs _ => U_step hU hs rfl (by rw [FLock.snd_upd, upd_upd]; exact hsh))
    hi hc (by rw [upd_self]; rfl) fun a m' rQ hc' _ hq hi' => ?_
  obtain ⟨rfl, -⟩ := Full.sep_lift.mp hq
  rw [upd_upd] at hi'
  exact h m' rQ hc' (by have := sum_le hsh (upd_self _ _ _); omega) hi'

/-- The counter's store of its next value by the holder after `k < 2` increments: then `k + 1`. -/
theorem wp_store {t : ThreadId} {rL : Res} {k : Nat} (hk : k < 2)
    {G : ThreadId → Gh} {m : Mem} {d : Nat} {v : BitVec 32}
    {Q : Unit → (ThreadId → Gh) → Mem → Nat → Prop}
    (hi : (proto Lo workOf).inv (upd G t (gHold k rL)) m) (hc : m.current = t)
    (hv : v.toNat = sum (upd (fun u => (G u).2) t (.work k)) + 1)
    (h : ∀ m' rQ, m'.current = t → (proto Lo workOf).inv (upd G t (gHold (k + 1) rQ)) m' →
      Q () G m' d) :
    (proto Lo workOf).WP t (ConcM.liftMem (store 4 (cPtr.add (Lo.mo + 4)) v) : ConcM Tgt Unit)
      Q G m d := by
  have e : ∀ k r, (fun u => (upd G t (gHold k r) u).2) = upd (fun u => (G u).2) t (.work k) :=
    fun _ _ => FLock.snd_upd _ _ _
  have hsh : Shape (upd (fun u => (G u).2) t (.work k)) m := by
    obtain ⟨rX, -, hU⟩ := hi; rw [← e k rL]; exact hU.shape
  have hx : upd (fun u => (G u).2) t (.work k) t = .work k := upd_self _ _ _
  have hsum := sum_le hsh hx
  have hsucc := sum_succ (shape_work hsh hx).1 hx
  have hsh₁ := shape_upd hsh hx (k' := k + 1) (by omega) _ (.inl rfl)
  rw [upd_upd] at hsucc hsh₁
  refine (fits (Lo := Lo) (workOf := workOf)).wp_hold (g' := gHold (k + 1))
    (by fsym : FTTriple
      (up (pts (cPtr.add (Lo.mo + 4)) 4 (BitVec.ofNat 32 (sum (upd (fun u => (G u).2) t (.work k))))))
      _ _)
    (fun r h => by change R Lo _ r at h; unfold R at h; rwa [e] at h)
    (fun _ => ⟨rfl, by rw [upd_self]; rfl, rfl⟩) (fun a r h => ?_)
    (fun rX m' r hU _ hs _ => U_step hU hs rfl (by rw [FLock.snd_upd, upd_upd]; exact hsh₁))
    hi hc (by rw [upd_self]; rfl) fun a m' rQ hc' _ _ hi' => h m' rQ hc' (by rwa [upd_upd] at hi')
  change R Lo _ r; unfold R; rw [upd_upd, e, hsucc]
  have : v = BitVec.ofNat 32 (sum (upd (fun u => (G u).2) t (.work k)) + 1) := by
    apply BitVec.eq_of_toNat_eq; rw [hv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [← this]; exact h

/-! ## `main`'s start -/

/-- The start: no thread. -/
def G0 : ThreadId → Gh := fun _ => (⟨.gone, rnil, rnil⟩, .none)

/-- `main` before its spawn. -/
def gPre : Gh := (⟨.out, rnil, rnil⟩, .pre)

/-- `main` at its join. -/
def gJoin : Gh := (⟨.out, rnil, rnil⟩, .joins)

/-- The `Counter`'s bytes `bs` in three parts: `io`, the mutex, the counter. -/
theorem split3 {A : Nat} {bs : Array Byte} {r : Res} (hs : bs.size = Lo.size)
    (h : up (bytesAt cPtr A Lo.size .stack bs) r) :
    (up (bytesAt cPtr A Lo.size .stack (bs.extract 0 Lo.io)) ⋆
      (up (bytesAt (cPtr.add Lo.io) A Lo.size .stack ((bs.extract Lo.io bs.size).extract 0 4)) ⋆
       up (bytesAt ((cPtr.add Lo.io).add 4) A Lo.size .stack
        ((bs.extract Lo.io bs.size).extract 4 (bs.extract Lo.io bs.size).size)))) r := by
  have hok := Lo.ok
  exact sep_mono_right (fun _ h => up_sep ⟨bytesAt_split h.1 (k := 4) (by simp; omega), h.2⟩)
    (up_sep ⟨bytesAt_split h.1 (k := Lo.io) (by omega), h.2⟩)

theorem sep_start {I W C b : FAssn} {r : Res} (h : ((I ⋆ (W ⋆ C)) ⋆ b) r) :
    ((C ⋆ W) ⋆ (I ⋆ b)) r := by
  have e : ((I ⋆ (W ⋆ C)) ⋆ b) = ((C ⋆ W) ⋆ (I ⋆ b)) := by ac_rfl
  rw [e] at h; exact h

theorem sep_word {I W C b : FAssn} {r : Res} (h : ((C ⋆ W) ⋆ (I ⋆ b)) r) :
    ((W ⋆ b) ⋆ (C ⋆ I)) r := by
  have e : ((C ⋆ W) ⋆ (I ⋆ b)) = ((W ⋆ b) ⋆ (C ⋆ I)) := by ac_rfl
  rw [e] at h; exact h

/-- **Before the spawn**: `main` owns the `Counter` after its stores (the bytes `bs`, whose mutex
and counter are 0, and `io`), with its extent. It gives `io` and the extent to the protocol's
rest (`FOwned.give`), and the mutex and the counter to the lock (`FLock.Inv.make`). -/
theorem inv_start {m : Mem} {r : Res} {A : Nat} {bs : Array Byte}
    (ho : FOwned (upd (fun _ => rnil) 0 r) rnil m)
    (hF : (up (bytesAt cPtr A Lo.size .stack bs) ⋆ bext 0 Lo.size .stack) r)
    (hs : bs.size = Lo.size) (hio : Lo.io = Lo.mo)
    (hW : (bs.extract Lo.io bs.size).extract 0 4 = Enc.encode (0 : BitVec 32))
    (hC : (bs.extract Lo.io bs.size).extract 4 (bs.extract Lo.io bs.size).size =
      Enc.encode (0 : BitVec 32))
    (hIo : Lo.io = Enc.size Io → bs.extract 0 Lo.io = Enc.encode (⟨⟩ : Io))
    (hA : A % Lo.align = 0) (hth : m.threads = #[{ spawner := 0, joined := true }])
    (hat : m.atomics = #[]) (hq : m.waiters = #[]) :
    (proto Lo workOf).inv (upd G0 0 gPre) m := by
  have hok := Lo.ok
  have hA4 : A % 4 = 0 := Nat.mod_eq_zero_of_dvd (Nat.dvd_trans hok.2.2.2.2 (Nat.dvd_of_mod_eq_zero hA))
  have h1 : m.threads.size = 1 := by rw [hth]; rfl
  have ht : 0 < m.threads.size := by rw [h1]; decide
  have hs4 : (Enc.encode (0 : BitVec 32)).size = 4 := LawfulEnc.size_encode _
  have hpW : cPtr.add Lo.io = cPtr.add Lo.mo := by rw [hio]
  have hpC : (cPtr.add Lo.io).add 4 = cPtr.add (Lo.mo + 4) := by
    simp only [cPtr, Ptr.add, hio]; congr 1
  have hF' := sep_start (sep_mono_left (fun _ h => split3 hs h) hF)
  rw [hW, hC, hpC, hpW] at hF'
  obtain ⟨_, rIO, hd, rfl, ⟨rC, rW, hdCW, rfl, hC₁, hW₁⟩, hIO⟩ := hF'
  -- the word's block and bytes
  have hown0 := sep_word (show (((up (bytesAt (cPtr.add (Lo.mo + 4)) A Lo.size .stack
      (Enc.encode (0 : BitVec 32)))) ⋆ up (bytesAt (cPtr.add Lo.mo) A Lo.size .stack
      (Enc.encode (0 : BitVec 32)))) ⋆ (up (bytesAt cPtr A Lo.size .stack (bs.extract 0 Lo.io)) ⋆
      bext 0 Lo.size .stack)) (upd (fun _ => rnil) 0 (rsum (rsum rC rW) rIO) 0) by
    rw [upd_self]; exact ⟨_, _, hd, rfl, ⟨_, _, hdCW, rfl, hC₁, hW₁⟩, hIO⟩)
  obtain ⟨blk, hblk, hl, hA', hS', hK', hx⟩ :=
    ho.bytesOf ht (rfl : (cPtr.add Lo.mo).block = some 0) (by rw [hs4]; decide) hown0
  have hoff : (cPtr.add Lo.mo).off.toNat = Lo.mo := by simp [cPtr, Ptr.add]
  rw [hoff, hs4] at hx
  have h0 : (L Lo).U32 m 0 := by
    show (intOfBytes 32 (curBytes m 0 Lo.mo 4)).run = _
    unfold curBytes; rw [hblk]
    simp only [Option.map_some, Option.getD_some]
    rw [hx]; exact intOfBytes_rmw 0
  -- `io` and the extent to the rest
  have ho' := ho.give (t := 0) ht (by rw [upd_self]) hd
  rw [upd_upd, rsum_rnil] at ho'
  have hGu : ∀ u, u ≠ 0 → upd G0 0 gPre u = G0 u := fun u h => upd_ne _ _ h
  have hjb : ∀ u, joinedB m u = false := by
    intro u; unfold joinedB
    by_cases hu : u = 0
    · subst hu; rw [hth]; rfl
    · have : m.threads.size ≤ u := by rw [h1]; unfold ThreadId at *; omega
      simp [Array.getElem?_eq_none this]
  refine ⟨rIO, FLock.Inv.make (t := 0) (rL := rC) (rW := rW) ho' (hjb 0) ht (fun u hu => ?_)
    (by rw [upd_self, upd_self]; exact (rnil_rsum _).symm)
    (by rw [upd_self]; exact (FHeap.disjoint_empty _).symm)
    hdCW (fun l => ?_) hW₁.2.1 hW₁.2.2
    (fun u => ?_) (fun u => ?_) ?_ ⟨blk, hblk, hl, by rw [hS']; show Lo.mo + 4 ≤ Lo.size; omega,
      by show (blk.addr + Lo.mo) % 4 = 0; rw [hA']; omega, by rw [hK']; decide,
      by rw [hK']; simp [BlockKind.mappedLo]⟩ h0 (by rw [hat]; simp) hq
      (allLe_of_one h1 (VClock.le_refl _)), ?_⟩
  · rw [upd_ne _ _ hu]
    unfold FLock.own; rw [hGu u hu]; split <;> simp [G0, FLock.prod, rnil_rsum]
  · rw [up_bytesAt_some hW₁ rfl l, hoff, hs4]
    show _ ↔ l.1 = 0 ∧ Lo.mo ≤ l.2 ∧ l.2 < Lo.mo + 4
    rfl
  · by_cases hu : u = 0
    · subst hu; rw [upd_self]; exact .inl ⟨rfl, ht, hjb 0⟩
    · rw [hGu u hu]; exact .inr rfl
  · by_cases hu : u = 0
    · subst hu; rw [upd_self]; rfl
    · rw [hGu u hu]; rfl
  · -- the counter holds `0`
    show R Lo _ rC
    have hsum : sum (fun u => (upd G0 0 gPre u).2) = 0 := by
      show (upd G0 0 gPre 0).2.count + (upd G0 0 gPre 1).2.count = 0
      rw [upd_self, hGu 1 (by decide)]; rfl
    unfold R; rw [hsum]
    exact ⟨⟨A, Lo.size, .stack, Enc.encode (0 : BitVec 32), by simp [cPtr, Ptr.add]; omega,
      LawfulEnc.size_encode _, LawfulEnc.decode_encode _, hC₁.1, by decide⟩, hC₁.2.1, hC₁.2.2⟩
  · refine ⟨⟨by rw [hth]; rfl, .inl ⟨h1, by show (upd G0 0 gPre 0).2 = _; rw [upd_self]; rfl,
      fun u hu => ?_⟩⟩, fun e he hr => .inr fun u hu => ?_, fun u => ?_,
      ⟨A, _, hA, by simp; omega, fun h => by rw [hIo h]; exact LawfulEnc.decode_encode _, hIO⟩⟩
    · show (upd G0 0 gPre u).2 = _; rw [hGu u (by unfold ThreadId at *; omega)]; rfl
    · -- every access to `io` happened before `main`, which owned it
      obtain rfl : u = 0 := by rw [h1] at hu; omega
      have hx : rIO.heap (e.block, e.off) ≠ none := by
        obtain ⟨r₁, r₂, hd₁, rfl, h₁, -⟩ := hIO
        have := (up_bytesAt_some h₁ rfl (e.block, e.off)).mpr
          ⟨hr.1, by simp [cPtr], by have := hr.2.2; simp [cPtr, hs]; omega⟩
        simp only [FHeap.union_apply, ne_eq, Option.or_eq_none_iff, not_and]
        intro h; exact absurd h this
      refine ho.owns 0 ht e he (.inl ⟨e.off, Nat.le_refl _, by have := hr.2.1; omega, ?_⟩)
      rw [upd_self]
      cases e' : (rsum rC rW).heap (e.block, e.off) <;> simp [FHeap.erase, FHeap.union_apply, hx]
    · by_cases hu : u = 0
      · subst hu; rw [upd_self]; rfl
      · rw [hGu u hu]; rfl

/-! ## The spawn, the ends -/

/-- **The spawn** of the kid by `main` at `pre`: both threads go to `work 0` (the kid's part is
empty). -/
theorem inv_spawn {G : ThreadId → Gh} {m m' : Mem} {c : ThreadId}
    (hi : (proto Lo workOf).inv G m) (hg : G 0 = gPre)
    (hf : (Thread.fork.run { m with current := 0 }).run = some (.ok (c, m'))) :
    c = 1 ∧ m'.current = 0 ∧ (proto Lo workOf).inv (upd (upd G 1 (gOut 0)) 0 (gOut 0)) m' := by
  obtain ⟨rX, hL, hu⟩ := hi
  obtain ⟨h00, ⟨hs1, -, hnone⟩ | ⟨-, -, h0, -⟩⟩ := hu.shape
  rotate_left
  · exfalso
    have e : (G 0).2 = .pre := by rw [hg]; rfl
    rcases h0 with h0 | ⟨_, _, h0⟩ <;> (change (G 0).2 = _ at h0; rw [e] at h0; cases h0)
  have hcs : m.clocks.size = m.threads.size := hL.w.csize
  have hG1 : (G 1).2 = .none := hnone 1 (Nat.le_refl _)
  have hf' := hf
  rw [Proto.fork_run] at hf'
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hf'
  obtain ⟨rfl, rfl⟩ := hf'
  have hX : ∀ u, (upd (upd G 1 (gOut 0)) 0 (gOut 0) u).2 =
      if u = 0 then .work 0 else if u = 1 then .work 0 else (G u).2 := fun u => by
    unfold upd; split
    · rfl
    · split <;> rfl
  have hL' := hL.fork (t := 0) (g₁ := gOut 0) (g₀ := gOut 0) (gt := false)
    (by rw [hg]; rfl) hf (by rw [hg]; exact (rsum_rnil rnil).symm) (FHeap.disjoint_empty _) rfl rfl
    rfl rfl fun r hR => by
      have hR' : R Lo (fun u => (G u).2) r := hR
      show R Lo (fun u => (upd (upd G m.threads.size (gOut 0)) 0 (gOut 0) u).2) r
      rw [hs1]
      have e : sum (fun u => (upd (upd G 1 (gOut 0)) 0 (gOut 0) u).2) = sum fun u => (G u).2 := by
        show (upd (upd G 1 (gOut 0)) 0 (gOut 0) 0).2.count +
          (upd (upd G 1 (gOut 0)) 0 (gOut 0) 1).2.count = (G 0).2.count + (G 1).2.count
        rw [hX, hX, hg, hG1]; rfl
      unfold R at hR' ⊢; rw [e]; exact hR'
  rw [hs1] at hL'
  refine ⟨hs1, rfl, rX, hL', ⟨⟨?_, .inr ⟨by simp [hs1], ?_,
      .inr ⟨0, by decide, by dsimp only; rw [hX]; rfl⟩,
      .inr ⟨0, by decide, by dsimp only; rw [hX]; rfl⟩, fun u hu => ?_⟩⟩, ?_, fun u => ?_, hu.rest⟩⟩
  · simp only [Array.getElem?_push]; rw [ite_eq_right (by omega)]; exact h00
  · simp only [Array.getElem?_push, hs1, ↓reduceIte]
  · dsimp only
    rw [hX, ite_eq_right (by unfold ThreadId at *; omega),
      ite_eq_right (by unfold ThreadId at *; omega)]
    exact hnone u (by unfold ThreadId at *; omega)
  · obtain ⟨hcl, hcn, -⟩ := LockWord.fork_clocks (cs := m.clocks) (t := 0) (by rw [hcs, hs1]; decide)
    exact hu.io.fork (t := 0) (by rw [hs1]; decide) (by simp)
      (fun u hu => hcl u (by rw [hcs]; exact hu)) (by rw [← hcs]; exact hcn) fun _ he _ => he
  · unfold upd; split
    · rfl
    · split
      · rfl
      · exact hu.parts u

/-- **A thread at the end of `work`**: `main` to its join, the kid to its end (`gone`). -/
theorem inv_end {G : ThreadId → Gh} {m : Mem} {t : ThreadId} {g : Gh}
    (hi : (proto Lo workOf).inv (upd G t (gOut 2)) m)
    (hp : (t = 0 ∧ g = gJoin) ∨ (t = 1 ∧ g = (⟨.gone, rnil, rnil⟩, .fin))) :
    (proto Lo workOf).inv (upd G t g) m := by
  obtain ⟨rX, hiL, hU⟩ := hi
  have hx : (fun u => (upd G t (gOut 2) u).2) t = .work 2 := by
    show (upd G t (gOut 2) t).2 = _; rw [upd_self]; rfl
  have hsum : sum (fun u => (upd (upd G t (gOut 2)) t g u).2) =
      sum (fun u => (upd G t (gOut 2) u).2) := by
    rw [FLock.snd_upd]; unfold sum
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [upd_self, upd_ne _ _ (by decide : (1 : Nat) ≠ 0)]; show 2 + _ = _; rw [hx]; rfl
    · rw [upd_self, upd_ne _ _ (by decide : (0 : Nat) ≠ 1)]; show _ + 2 = _; rw [hx]; rfl
  have hl := hiL.ghost (t := t) (g := g) (by rw [upd_self]; rfl)
    (by rcases hp with ⟨-, rfl⟩ | ⟨-, rfl⟩
        · exact .inl rfl
        · exact .inr (.inl rfl))
    (by rw [upd_self]; rcases hp with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> rfl)
    (by rcases hp with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> rfl)
    (fun _ => hiL.ht (by rw [upd_self]; exact (by decide : LPh.out ≠ LPh.gone)))
    (fun r hR => by
      have hR' : R Lo (fun u => (upd G t (gOut 2) u).2) r := hR
      show R Lo _ r; unfold R at hR' ⊢; rw [hsum]; exact hR')
  rw [upd_upd] at hl
  refine ⟨rX, hl, ?_, hU.io, fun u => ?_, hU.rest⟩
  · rw [FLock.snd_upd]
    have := shape_upd hU.shape hx (Nat.le_refl 2) g.2 (by
      rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact .inr (.inl ⟨rfl, rfl⟩)
      · exact .inr (.inr ⟨rfl, rfl⟩))
    rw [FLock.snd_upd, upd_upd] at this; exact this
  · unfold upd; split
    · rcases hp with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> rfl
    · rename_i h; have := hU.parts u; rwa [upd_ne _ _ h] at this

/-- **The kid's end** (`QKid`): it is `gone` at `fin` and spawned no thread. -/
theorem qkid {G : ThreadId → Gh} {m : Mem} {d : Nat}
    (hi : (proto Lo workOf).inv (upd G 1 (gOut 2)) m) : (proto Lo workOf).QKid 1 () G m d := by
  have hi' := inv_end hi (.inr ⟨rfl, rfl⟩)
  refine ⟨_, hi', ⟨rfl, rfl⟩, fun _ => ?_⟩
  obtain ⟨rX, -, hu⟩ := hi'
  exact joinedAll_of_main (spawners hu.shape) (by decide)

/-! ## `main`'s join and free -/

/-- **`main`'s join of the kid** at `joins`: then it takes the counter (4) and the mutex's word back
(`FLock.Inv.take`); every thread is joined, the `Counter` is block 0 and every clock is below
`main`'s. -/
theorem wp_join {σ : Type} {s : σ} {G : ThreadId → Gh} {m : Mem} {n : Nat}
    (hi : (proto Lo workOf).inv (upd G 0 gJoin) m)
    {Q : Unit × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ k G₁ m' (own : ThreadId → Res) (rX r : Res), n = k + 1 → m'.current = 0 →
      FOwned (upd own 0 r) rX m' →
      ((fun r => r = own 0) ⋆ (up (pts (cPtr.add (Lo.mo + 4)) 4 (BitVec.ofNat 32 4)) ⋆
        fun r => r = (L Lo).wordR m')) r →
      BlkOk Lo m' → m'.ClocksLe → joinedAll 0 m' → m'.threads.size = 2 →
      (∃ w, (L Lo).U32 m' (BitVec.ofNat 32 w)) → Q ((), s) G₁ m' k) :
    (proto Lo workOf).WP 0 ((joinC 1 : CM Tgt σ Unit).run s) Q G m n := by
  refine WP.joinC fun k hk => ⟨_, hi, fun G₁ m₁ hg hi₁ => ?_⟩
  obtain ⟨rX, hL, hu⟩ := hi₁
  obtain ⟨h00, ⟨-, h0, -⟩ | ⟨hs2, hr1, -⟩⟩ := hu.shape
  · exfalso; change (G₁ 0).2 = _ at h0; rw [hg] at h0; cases h0
  refine ⟨fun _ => ⟨by show (0 : Nat) < 1; decide, by rw [hs2]; decide, ⟨rfl, rfl⟩,
    by simp [Thread.joinValid, Mem.isGated, hr1]⟩, fun hfin => ⟨fun _ =>
    join_run (m := { m₁ with current := 0 }) hr1 rfl rfl, fun m' hj => ?_⟩⟩
  have hcs : m₁.clocks.size = 2 := by rw [hL.w.csize, hs2]
  have hcl := Mem.ClocksLe.join2 hj hcs
  obtain ⟨rec, -, -, hm'⟩ := join_eq hj
  have hc' : m'.current = 0 := by rw [hm']
  have hth : m'.threads = m₁.threads.set! 1 { rec with joined := true } := by rw [hm']
  have hs2' : m'.threads.size = 2 := by rw [hth, Array.size_set!, hs2]
  -- `main` takes the kid's (empty) part
  have hjb1 : joinedB m₁ 1 = false := by simp [joinedB, hr1]
  have hown1 : (L Lo).own G₁ m₁ 1 = rnil := by
    rw [FLock.own_live (L := L Lo) hjb1]
    show rsum (G₁ 1).1.part ((L Lo).held (G₁ 1)) = _
    rw [hu.parts 1, hL.idle 1 (by rw [show (L Lo).ph (G₁ 1) = .gone from hfin.1]; decide),
      rsum_rnil]
  have hG : upd G₁ 0 gJoin = G₁ := by rw [← hg, upd_same]
  have hL' := hL.join (t := 0) (u := 1) (g := gJoin) (by decide) (by decide) (by rw [hg]; rfl)
    hfin.1 hj (by rw [hown1, rsum_rnil, hg]) rfl rfl (fun r hR => by rw [hG]; exact hR)
  rw [hG] at hL'
  have hF : (L Lo).Free G₁ := by
    intro u hu'
    by_cases h0 : u = 0
    · subst h0; simp only [FLock.pl] at hu'; rw [hg] at hu'; cases hu'
    · by_cases h1 : u = 1
      · subst h1; simp only [FLock.pl] at hu'
        rw [show (L Lo).ph (G₁ 1) = .gone from hfin.1] at hu'; cases hu'
      · have := (hL'.w.live u (by rw [hu']; decide)).1
        rw [hs2'] at this; unfold ThreadId at *; omega
  have hall : ∀ u < m'.threads.size, VClock.le (m'.clocks[u]!) (m'.clocks[0]!) = true :=
    fun u hu' => by
      have := hcl u (by rw [hL'.w.csize]; exact hu'); rwa [hc'] at this
  obtain ⟨rL, hR, hsep, ho⟩ := hL'.take (t := 0) hF
    (by rw [hg]; exact (by decide : LPh.out ≠ LPh.gone)) hall
  have hR4 : up (pts (cPtr.add (Lo.mo + 4)) 4 (BitVec.ofNat 32 4)) rL := by
    have : R Lo (fun u => (G₁ u).2) rL := hR
    have h4 : sum (fun u => (G₁ u).2) = 4 := by
      show (G₁ 0).2.count + (G₁ 1).2.count = 4
      rw [hg, hfin.2]; rfl
    unfold R at this; rw [h4] at this; exact this
  refine h k G₁ m' _ rX _ hk hc' ho (sep_mono_right (fun _ h => sep_mono_left
    (fun r (h : r = rL) => by subst h; exact hR4) h) hsep) (blk_of hL' hu.rest) hcl
    (fun r hr hsp => ?_) hs2' (by obtain ⟨w, -, hw, -⟩ := hL'.w.word; exact ⟨w, hw⟩)
  simp only [hth] at hr
  obtain ⟨i, hi', rfl⟩ := Array.mem_iff_getElem.mp hr
  simp only [Array.size_set!] at hi'
  simp only [Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds hi'] at hsp ⊢
  split
  · rfl
  · obtain rfl : i = 0 := by omega
    rw [Array.getElem?_eq_getElem (by omega)] at h00
    rw [Option.some.inj h00]

/-- **`main`'s mutex and counter after its join** (`wp_join`): block 0 holds the mutex's word
`w` and the counter 4 at an address that is a multiple of 4, and an access by `main` to them
does not race (`main` owns their bytes). For a version whose `main` reads the whole `Counter`
(0.15.2). -/
theorem main_counter {own : ThreadId → Res} {rX r : Res} {m : Mem} {w : Nat}
    (ho : FOwned (upd own 0 r) rX m) (hc : m.current = 0) (ht : 0 < m.threads.size)
    (hp : ((fun r => r = own 0) ⋆ (up (pts (cPtr.add (Lo.mo + 4)) 4 (BitVec.ofNat 32 4)) ⋆
      fun r => r = (L Lo).wordR m)) r) (hb : BlkOk Lo m) (hw : (L Lo).U32 m (BitVec.ofNat 32 w)) :
    ∃ blk, m.blocks[0]? = some blk ∧ blk.live = true ∧ blk.bytes.size = Lo.size ∧
      blk.kind = .stack ∧ blk.addr % 4 = 0 ∧
      (intOfBytes 32 (blk.bytes.extract Lo.mo (Lo.mo + 4))).run = some (.ok (BitVec.ofNat 32 w)) ∧
      Enc.decode (blk.bytes.extract (Lo.mo + 4) (Lo.mo + 4 + 4)) = pure (BitVec.ofNat 32 4) ∧
      ∀ k, NoRace m 0 Lo.mo 8 k := by
  have hok := Lo.ok
  obtain ⟨blk, hblk, hl, hsz, hk⟩ := hb
  obtain ⟨rR, -, -, hh⟩ := ho.part ht
  rw [upd_self] at hh
  have hp' := Full.sep_comm hp
  obtain ⟨r₁₂, r₀, hd, e, ⟨r₁, r₂, hd', e', hpts, hr₂⟩, hr₀⟩ := hp'
  obtain ⟨⟨A, S, K, bs, hal, hbs, hdec, hbA, -⟩, hkn, hgh⟩ := hpts
  rw [e] at hh
  have hh₀ := Holds.split (r₁ := r₁₂) (r₂ := r₀) hd hh
  rw [e'] at hh₀
  have hh₁ := Holds.split (r₁ := r₁) (r₂ := r₂) hd' hh₀
  obtain ⟨b, blk', hpb, hblk', -, -, -, -, hA, -, hx⟩ :=
    hh₁.bytesAt_block (p := cPtr.add (Lo.mo + 4)) ⟨hbA, hkn, hgh⟩ (by rw [hbs]; decide)
  obtain rfl : b = 0 := by cases hpb; rfl
  rw [hblk] at hblk'; cases hblk'
  have hoff : (cPtr.add (Lo.mo + 4)).off.toNat = Lo.mo + 4 := by simp [cPtr, Ptr.add]; omega
  have h4 : Enc.size (BitVec 32) = 4 := rfl
  rw [hoff, hbs, h4] at hx
  refine ⟨blk, hblk, hl, hsz, hk, by rw [hA]; rw [hoff] at hal; omega,
    ((L Lo).u32_bytes hblk).mp hw, by rw [hx]; exact hdec, fun k => ?_⟩
  -- `main` owns the word's and the counter's bytes
  refine Mem.Owns.noRace (h := (upd own 0 r 0).heap.erase) (by rw [hc]; exact ho.owns 0 ht)
    fun x h1 h2 => ?_
  have hne : ∀ {a b : Res} {l : Zig.Loc}, a.heap l ≠ none ∨ b.heap l ≠ none →
      (rsum a b).heap.erase l ≠ none := fun h => by
    simp only [FHeap.erase, FHeap.union_apply, ne_eq, Option.map_eq_none_iff,
      Option.or_eq_none_iff, not_and]
    rcases h with h | h
    · exact fun h' => absurd h' h
    · exact fun _ => h
  rw [upd_self, e, e']
  show (rsum (rsum r₁ r₂) r₀).heap.erase (0, x) ≠ none
  refine hne (.inl ?_)
  have hsome : ∀ {a b : Res} {l : Zig.Loc}, a.heap l ≠ none ∨ b.heap l ≠ none →
      (rsum a b).heap l ≠ none := fun h => by
    simpa [FHeap.erase] using hne h
  by_cases hx4 : x < Lo.mo + 4
  · have hcell : m.heap (0, x) ≠ none := by
      simp [Mem.heap, hblk, hl, hk, BlockKind.mappedLo]; omega
    refine hsome (.inr ?_)
    rw [hr₂]; exact cellsAt_some ⟨rfl, h1, hx4⟩ hcell
  · refine hsome (.inl ?_)
    exact (up_bytesAt_some ⟨hbA, hkn, hgh⟩ (rfl : (cPtr.add (Lo.mo + 4)).block = some 0) (0, x)).mpr
      ⟨rfl, by rw [hoff]; omega, by rw [hoff, hbs, h4]; omega⟩

/-- **`main`'s free of the `Counter`** after its join: its end races with no access. -/
theorem wp_free {G : ThreadId → Gh} {m : Mem} {n : Nat} (hb : BlkOk Lo m) (hcl : m.ClocksLe)
    {Q : Unit → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ m', m'.threads = m.threads → Q () G m' n) :
    (proto Lo workOf).WP 0 (ConcM.liftMem (free cPtr) : ConcM Tgt Unit) Q G m n := by
  obtain ⟨blk, hblk, hl, -, hk⟩ := hb
  refine WP.liftMem (fun e he => (free_noErr hblk hl (hcl.freeRaces _ _) (by rw [hk]; nofun) e
    he).elim) fun _ m' hfr => ?_
  obtain ⟨b', blk', -, -, rfl⟩ := free_ok hfr
  exact ⟨rfl, h _ rfl⟩

end MutexCounter
end Zig
