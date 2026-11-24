import Proofs.RwRead.Protocol
import ZigLean.Sep.Full.LockSteps
import ZigLean.Sep.Full.Cond

/-!
# The steps of `rwLockRead` and `rwLockSnapshotPair` around the lock's entry points

The client's steps under the protocol (`Proofs/RwRead/Protocol.lean`), each from the contract
(`RwLockImpl`) or from a rule for every protocol with the lock; the walks use them as `fsym`
rules. No rule here is about an implementation.

- **The memory**: a field pointer of the `Shared` (`projI`, from the base's pin), the read of
  `io` (`wp_io`, `FRw.Base.wp_readIo`).
- **The writer**: `lockUncancelable` gives it `n` with its own increments (`wp_lock`; the room
  from the two threads, `FRw.nwi_le`); it loads and stores `n` in its part (`wp_ownN`, `wp_own`:
  a thread's step on its part, `FCond.wp_liftPart` at the semaphore's view); before `unlock` it
  moves to its next increment (`FRw.Base.inv_setX`) and gives `n` back (`wp_unlockN`).
- **The reader**: `lockSharedUncancelable` gives it a share of a heap with `n` at the writer's
  increments at that time (`wp_lockShared`; the room from the two threads, `FRw.nrd_le`); it loads
  `n` through the share (`wp_loadShare`, `FTTotalTriple.load_sheap`), any number of times, and
  gives the share back (`wp_unlockShared`).
-/

namespace Zig
namespace RwRead

open Conc Conc.Proto Full Full.FAssn

variable {Tgt : Type} {wOf : Tgt → Option Ptr}

/-! ## The invariant's facts -/

/-- The threads' fact, from the invariant. -/
theorem thr_of {G : ThreadId → Gh} {m : Mem} (hi : (proto wOf).inv G m) :
    Thr (fun u => (G u).2.x) m.threads :=
  FRw.Base.inv_thr (W := W) (E := E) hi

/-- A thread at a place of the writer is thread 1, with at most two increments. -/
theorem wr1 {G : ThreadId → Gh} {m : Mem} {t : ThreadId} {g : Gh} {k : Nat}
    (hi : (proto wOf).inv (upd G t g) m) (hx : g.2.x = .wr k) : t = 1 ∧ k ≤ 2 :=
  (thr_of hi).wr (u := t) (by show (upd G t g t).2.x = _; rw [upd_self]; exact hx)

/-- The writer's increments are those of thread 1's ghost value. -/
theorem cnt_upd1 (G : ThreadId → Gh) (g : Gh) :
    cnt (fun u => (upd G 1 g u).2.x) = g.2.x.count := by
  show ((upd G 1 g 1).2.x).count = _
  rw [upd_self]

/-- `n` at thread 1's ghost value. -/
theorem R_upd1 (G : ThreadId → Gh) (g : Gh) :
    R (fun u => (upd G 1 g u).2.x) = up (pts nPtr 4 (BitVec.ofNat 32 g.2.x.count)) := by
  unfold R; rw [cnt_upd1]

/-- The lock's address is the `Shared`'s field at 16. -/
theorem pW : cPtr.add 16 = W.p := rfl

/-! ## Field pointers and `io` -/

/-- A field pointer of the `Shared` (block 0, 64 bytes) is formed (`ptrProject`, MM-3). -/
theorem projI {G : ThreadId → Gh} {m : Mem} (hi : (proto wOf).inv G m) {k : Nat} (hk : k ≤ 64) :
    (ptrProject cPtr (·.add k)).run m = pure (cPtr.add k, m) := by
  obtain ⟨blk, hb, -, hsz, -⟩ := FRw.Base.inv_blk (W := W) (E := E) hi
  have hb' : m.blocks[0]? = some blk := hb
  exact ptrProject_block_run hb' rfl (by decide) (by simp [cPtr, hsz]; omega)

/-- **The read of `io`** by a thread that has not ended (`FRw.Base.wp_readIo`). -/
theorem wp_io {G G' : ThreadId → Gh} {t : ThreadId} {m : Mem} {d : Nat}
    {Q : Io → (ThreadId → Gh) → Mem → Nat → Prop}
    (hi : (proto wOf).inv G' m) (hc : m.current = t) (hg : (G' t).1.phA ≠ .gone)
    (h : ∀ m', m'.current = t → m'.threads = m.threads → (proto wOf).inv G' m' → Q ⟨⟩ G m' d) :
    (proto wOf).WP t (ConcM.liftMem (load Io 8 cPtr) : ConcM Tgt Io) Q G m d :=
  FRw.Base.wp_readIo (fits (wOf := wOf)) io_off (p := cPtr) (b := 0) (a := 8) (v := (⟨⟩ : Io)) rfl
    (by decide)
    (fun r₀ h₀ => by
      obtain ⟨A, bs, hA, hbs, hdec, hb⟩ := h₀
      exact ⟨r₀, A, _, _, bs, hb, fun _ _ h => h, by rw [hbs]; rfl, hdec,
        by simpa [cPtr] using hA, by decide⟩)
    (FClient.pre_covers (by rw [o0]; decide)) hi hc hg h

/-- A thread outside the locks has not ended. -/
theorem gO_live (r : Res) (x : Ph) : (gO r x).1.phA ≠ .gone := nofun

/-- The writer with the write lock has not ended. -/
theorem gW_live (r rM : Res) (x : Ph) : (gW r rM x).1.phA ≠ .gone := nofun

/-- A reader with its share has not ended. -/
theorem gR_live (r : Res) (q : Frac) (H : FHeap) (x : Ph) : (gR r q H x).1.phA ≠ .gone := nofun

/-- **The read of `io`** by the thread with the ghost value `g`, which has not ended (`wp_io`
with the thread's value named: the rule of the walks, at `gO_live`, `gW_live`, `gR_live`). -/
theorem wp_ioAt {G : ThreadId → Gh} {t : ThreadId} {g : Gh} (hg : g.1.phA ≠ .gone) {m : Mem}
    {d : Nat} {Q : Io → (ThreadId → Gh) → Mem → Nat → Prop}
    (hi : (proto wOf).inv (upd G t g) m) (hc : m.current = t)
    (h : ∀ m', m'.current = t → m'.threads = m.threads → (proto wOf).inv (upd G t g) m' →
      Q ⟨⟩ G m' d) :
    (proto wOf).WP t (ConcM.liftMem (load Io 8 cPtr) : ConcM Tgt Io) Q G m d :=
  wp_io hi hc (by rw [upd_self]; exact hg) h

/-! ## A step on the thread's own part -/

/-- **A step of the writer on its own part** while it holds the write lock (`FCond.wp_liftPart`
at the semaphore's view): its part after the step is the step's post. -/
theorem wp_own {α : Type} {x : MemM α} {Pa : FAssn} {Qa : α → FAssn}
    {Q : α → (ThreadId → Gh) → Mem → Nat → Prop} {G : ThreadId → Gh} {m : Mem} {d : Nat}
    {t : ThreadId} {r rM : Res} {y : Ph}
    (hi : (proto wOf).inv (upd G t (gW r rM y)) m) (hc : m.current = t)
    (htt : FTTriple Pa x Qa) (hp : Pa r)
    (h : ∀ a m' r', (x.run m).run = some (.ok (a, m')) → Qa a r' → m'.current = t →
      (proto wOf).inv (upd G t (gW r' rM y)) m' → Q a G m' d) :
    (proto wOf).WP t (ConcM.liftMem x : ConcM Tgt α) Q G m d :=
  FCond.wp_liftPart (fits (wOf := wOf)).s.toC.toFits (.inl rfl) hi hc htt hp
    (fun a m' r' hx hq hc' _ _ hi' => h a m' r' hx hq hc' hi')

/-- **The writer's first step on its own part** after `lockUncancelable` (`wp_lock`'s post): it
owns `n` with its increments, next to its part `rp`. -/
theorem wp_ownN {α : Type} {x : MemM α} {Qa : α → FAssn}
    {Q : α → (ThreadId → Gh) → Mem → Nat → Prop} {G : ThreadId → Gh} {m : Mem} {d : Nat}
    {t : ThreadId} {rp r rM : Res} {k : Nat}
    (hi : (proto wOf).inv (upd G t (gW (rsum rp r) rM (.wr k))) m) (hc : m.current = t)
    (hr : up (pts nPtr 4 (BitVec.ofNat 32 k)) r) (hdj : FHeap.Disjoint rp.heap r.heap)
    (htt : FTTriple ((fun x => x = rp) ⋆ up (pts nPtr 4 (BitVec.ofNat 32 k))) x Qa)
    (h : ∀ a m' r', (x.run m).run = some (.ok (a, m')) → Qa a r' → m'.current = t →
      (proto wOf).inv (upd G t (gW r' rM (.wr k))) m' → Q a G m' d) :
    (proto wOf).WP t (ConcM.liftMem x : ConcM Tgt α) Q G m d :=
  wp_own hi hc htt ⟨rp, r, hdj, rfl, rfl, hr⟩ h

/-! ## The writer -/

/-- **`lockUncancelable` of the writer after `k` increments** (`RwLockImpl.lock_wp`): it gets `n`
with the value `k` in its part, at `wr`. -/
theorem wp_lock (I : RwLockImpl Tgt) (hIc : I.c = 2) {p : Ptr} (hp : p = cPtr.add 16)
    (t : ThreadId) {k : Nat} {rp : Res} (hpl : rp.Plain) (io : Io) (G : ThreadId → Gh) (m : Mem)
    (d : Nat) (hi : (proto wOf).inv (upd G t (gO rp (.wr k))) m) (hc : m.current = t) :
    (proto wOf).WP t (I.lock p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧ ∃ r rM,
      up (pts nPtr 4 (BitVec.ofNat 32 k)) r ∧ FHeap.Disjoint rp.heap r.heap ∧
      (proto wOf).inv (upd G' t (gW (rsum rp r) rM (.wr k))) m') G m d := by
  have hroom : ∀ G m, (proto wOf).inv G m → W.ph (G t) = .out →
      W.nwi G m + 1 < RwState.countBound := fun G m hi _ =>
    Nat.lt_of_le_of_lt (Nat.add_le_add_right
      (Nat.le_trans (FRw.nwi_le G m) (thr_of hi).size_le) 1) (by decide)
  refine WP.mono (fun _ G' m' d' hq => ?_)
    (I.lock_wp (fits (wOf := wOf)) rfl hIc.symm hIc.symm (hp.trans pW) t (gO rp (.wr k))
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ trivial ⟨rfl, .inl rfl⟩ hpl.2 hroom io G m d hi hc)
  obtain ⟨hd, hc', r, rM, ⟨G₀, hR⟩, hdj, hi'⟩ := hq
  have hi'' : (proto wOf).inv (upd G' t (gW (rsum rp r) rM (.wr k))) m' := hi'
  obtain ⟨rfl, -⟩ := wr1 hi'' rfl
  have hR' : R (fun u => (upd G₀ 1 (gO rp (.wr k)) u).2.x) r := hR
  rw [R_upd1] at hR'
  exact ⟨hd, hc', r, rM, hR', hdj, hi''⟩

/-- **`unlock` of the writer after its increment** (`RwLockImpl.unlock_wp`): its part is `rp`
and `n`, one increment further; it moves to its next increment (`FRw.Base.inv_setX`) and gives
`n` back. -/
theorem wp_unlockN (I : RwLockImpl Tgt) (hIc : I.c = 2) {p : Ptr} (hp : p = cPtr.add 16)
    (t : ThreadId) {k : Nat} (hk : k < 2) {rp r' rM : Res} (hpl : rp.Plain)
    (hr' : ((fun x => x = rp) ⋆ up (pts nPtr 4 (BitVec.ofNat 32 (k + 1)))) r')
    (io : Io) (G : ThreadId → Gh) (m : Mem) (d : Nat)
    (hi : (proto wOf).inv (upd G t (gW r' rM (.wr k))) m) (hc : m.current = t) :
    (proto wOf).WP t (I.unlock p io) (fun _ G' m' d' => d' ≤ d ∧ m'.current = t ∧
      (proto wOf).inv (upd G' t (gO rp (.wr (k + 1)))) m') G m d := by
  obtain ⟨rp', rT, hdj, rfl, hrp, hrT⟩ := hr'
  have e : rp = rp' := (hrp : rp' = rp).symm
  subst e
  obtain ⟨rfl, -⟩ := wr1 hi rfl
  have hi' : (proto wOf).inv (upd G 1 (gW (rsum rp rT) rM (.wr (k + 1)))) m :=
    FRw.Base.inv_setX (W := W) (E := E) hi rfl rfl rfl rfl rfl rfl rfl
      ((thr_of hi).step (k := k) (k' := k + 1)
        (by show (upd G 1 _ 1).2.x = _; rw [upd_self]; rfl) (by omega)
        (by show (upd G 1 _ 1).2.x = _; rw [upd_self]; rfl)
        (fun u hu => by
          show (upd G 1 _ u).2.x = (upd G 1 _ u).2.x
          rw [upd_ne _ _ hu, upd_ne _ _ hu]))
  exact I.unlock_wp (fits (wOf := wOf)) rfl hIc.symm hIc.symm (hp.trans pW) 1
    (gW (rsum rp rT) rM (.wr (k + 1))) rp rT rfl rfl rfl rfl rfl rfl rfl hdj trivial
    ⟨rfl, .inl rfl⟩ hpl.2
    (fun G₁ => by
      show R (fun u => (upd G₁ 1 (gW (rsum rp rT) rM (.wr (k + 1))) u).2.x) rT
      rw [R_upd1]; exact hrT)
    io G m d hi' hc

/-! ## The reader -/

/-- **`lockSharedUncancelable`** of a thread at the place `y` (`RwLockImpl.lockShared_wp`): it
gets a share `q` of a heap `H` with `n` at the writer's increments at that time (`cnt Y`, at
client parts `Y` with the threads' fact and the caller at `y`), at `rd q H`. -/
theorem wp_lockShared (I : RwLockImpl Tgt) (hIc : I.c = 2) {p : Ptr} (hp : p = cPtr.add 16)
    (t : ThreadId) {y : Ph} {rp : Res} (hpl : rp.Plain) (io : Io) (G : ThreadId → Gh) (m : Mem)
    (d : Nat) (hi : (proto wOf).inv (upd G t (gO rp y)) m) (hc : m.current = t) :
    (proto wOf).WP t (I.lockShared p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ (q : Frac) (H : FHeap) (Y : ThreadId → Ph), 0 < q.val ∧
        up (pts nPtr 4 (BitVec.ofNat 32 (cnt Y))) ⟨H, Know.none, Ghost.unit⟩ ∧
        Thr Y m'.threads ∧ Y t = y ∧
        (proto wOf).inv (upd G' t (gR (rsum rp (shareRes H q)) q H y)) m') G m d := by
  have hroom : ∀ G m, (proto wOf).inv G m → W.ph (G t) = .out →
      W.nrd G m + 1 < RwState.countBound := fun G m hi _ =>
    Nat.lt_of_le_of_lt (Nat.add_le_add_right
      (Nat.le_trans (FRw.nrd_le G m) (thr_of hi).size_le) 1) (by decide)
  refine WP.mono (fun _ G' m' d' hq => ?_)
    (I.lockShared_wp (fits (wOf := wOf)) rfl hIc.symm hIc.symm (hp.trans pW) t (gO rp y)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ trivial ⟨rfl, .inl rfl⟩ hpl.2 hroom io G m d hi hc)
  obtain ⟨hd, hc', q, H, hq, hR, hi'⟩ := hq
  have hi'' : (proto wOf).inv (upd G' t (gR (rsum rp (shareRes H q)) q H y)) m' := hi'
  have e : (fun u => (upd G' t (gO rp y) u).2.x) =
      fun u => (upd G' t (gR (rsum rp (shareRes H q)) q H y) u).2.x :=
    upd_map (fun g : Gh => g.2.x) G' t rfl
  refine ⟨hd, hc', q, H, fun u => (upd G' t (gO rp y) u).2.x, hq, hR, ?_, ?_, hi''⟩
  · rw [e]; exact thr_of hi''
  · show (upd G' t (gO rp y) t).2.x = y
    rw [upd_self]; rfl

/-- **The reader's load of `n` through its share** (`FTTotalTriple.load_sheap` on its part): the
value of the heap its share is of; the share stays. -/
theorem wp_loadShare {Q : BitVec 32 → (ThreadId → Gh) → Mem → Nat → Prop} {G : ThreadId → Gh}
    {m : Mem} {d : Nat} {t : ThreadId} {rp : Res} {q : Frac} {H : FHeap} {y : Ph} {v : BitVec 32}
    (hi : (proto wOf).inv (upd G t (gR (rsum rp (shareRes H q)) q H y)) m) (hc : m.current = t)
    (hq : 0 < q.val) (hH : up (pts nPtr 4 v) ⟨H, Know.none, Ghost.unit⟩)
    (h : ∀ m', m'.current = t →
      (proto wOf).inv (upd G t (gR (rsum rp (shareRes H q)) q H y)) m' → Q v G m' d) :
    (proto wOf).WP t (ConcM.liftMem (load (BitVec 32) 4 nPtr) : ConcM Tgt (BitVec 32)) Q G m d := by
  have htt := (FTTotalTriple.load_sheap (T := BitVec 32) (p := nPtr) (a := 4) hq (by decide)
    hH).1.frameL (R := fun r => r = rp)
  refine FCond.wp_liftPart (fits (wOf := wOf)).s.toC.toFits (.inl rfl) hi hc htt
    ⟨rp, shareRes H q, fun _ => .inr rfl, rfl, rfl, shareRes_sheap H q⟩
    (fun a m' r' _ hq' hc' _ _ hi' => ?_)
  obtain ⟨_, r₂, -, rfl, rfl, h₂⟩ := hq'
  obtain ⟨e, hs⟩ := Full.sep_lift.mp h₂
  rw [sheap_eq hs] at hi'
  rw [e]
  exact h m' hc' hi'

/-- **`unlockShared`** of a reader (`RwLockImpl.unlockShared_wp`): it gives its share back. -/
theorem wp_unlockShared (I : RwLockImpl Tgt) (hIc : I.c = 2) {p : Ptr} (hp : p = cPtr.add 16)
    (t : ThreadId) {y : Ph} {rp : Res} {q : Frac} {H : FHeap} (hpl : rp.Plain) (io : Io)
    (G : ThreadId → Gh) (m : Mem) (d : Nat)
    (hi : (proto wOf).inv (upd G t (gR (rsum rp (shareRes H q)) q H y)) m) (hc : m.current = t) :
    (proto wOf).WP t (I.unlockShared p io) (fun _ G' m' d' => d' ≤ d ∧ m'.current = t ∧
      (proto wOf).inv (upd G' t (gO rp y)) m') G m d :=
  I.unlockShared_wp (fits (wOf := wOf)) rfl hIc.symm hIc.symm (hp.trans pW) t
    (gR (rsum rp (shareRes H q)) q H y) rp q H rfl rfl rfl rfl rfl rfl rfl rfl trivial
    ⟨rfl, .inl rfl⟩ hpl.2 io G m d hi hc

end RwRead
end Zig
