import Proofs.Handoff.Start
import ZigLean.Sep.Full.Local
import ZigLean.Sep.Full.Event
import ZigLean.Sep.Full.Auto
import ZigLean.Sep.Full.LockSteps

/-!
# The operations of `handoff`, once for every version

Each version's walk of `main` and the producer (`Proofs/Sync/Handoff.lean`,
`Proofs/Threadsync/Handoff.lean`) is its generated code; every step of it is a lemma here, for
every layout (`Layout`) and every implementation of the sync objects (`MutexImpl`, `CondImpl`,
`EventImpl`):

- **`io`** (0.16.0 and 0.17.0 only): a read of the `Box`'s `io` prefix, which is read-shared in the
  protocol's rest (`io_rest`, read by the library's `FLock.Fits.wp_readRest`). Its alignment comes from the rest's bytes of `io` (`IoRest`), so the
  layout needs an `io` prefix whose load alignment divides the `Box`'s.
- **Field pointers** (`proj`): the `Box` is block 0 (`BlkOk`).
- **The sync objects**: `main`'s and the producer's `lock` and `unlock`, `main`'s condition wait
  (`wp_cwait`, with the contract's client premises from `Proofs/Handoff/Steps.lean`), the
  producer's `signal` and `set`, `main`'s event wait.
- **`v` and `ready`**: the producer's stores and `main`'s loads, on the mutex's resource: the
  library's `FLock.Fits.wp_hold`, which the walks apply, with `U_holdStep` and `U_storeHeld`.
- **The producer's end** (`QKid`) and **`main`'s join and free**.
-/

namespace Zig
namespace Handoff

open Conc Conc.Proto Full Full.FAssn

variable {Lo : Layout} {Tgt : Type} {prodOf : Tgt → Option Ptr}

/-! ## A read of `io` -/

/-- **A read of `n` bytes of `io`** (`n ≤ io`) by the current thread `t` keeps `U`: `io` is
read-shared, the three words and the futex queue stay. -/
theorem U_rec {G : ThreadId → Gh} {rX : Res} {m : Mem} {t : ThreadId} {n : Nat}
    (hu : U Lo G rX m) (hcs : m.clocks.size = m.threads.size) (hc : m.current = t)
    (ht : t < m.threads.size) (hn : 0 < n) (hio : n ≤ Lo.io) :
    U Lo G rX (m.recordAt 0 0 n .read) := by
  have hok := Lo.ok
  have hclk := LockWord.recordAt_le m 0 0 n .read
  have hk : ∀ W : Word 32 4, Three Lo W → W.Keep m (m.recordAt 0 0 n .read) := fun W hW =>
    Word.keep_read m (.inr (.inl (by have := three_o hW; omega)))
  have hhS := Word.hist_keep hu.ws (hk _ (.inl rfl))
  have hhE := Word.hist_keep hu.we (hk _ (.inr (.inl rfl)))
  have hhV := Word.hist_keep hu.wv (hk _ (.inr (.inr rfl)))
  refine ⟨hu.shape, hu.io.read (hc ▸ ht) hcs 0 0 n, hu.rest.congr fun _ _ => rfl, hu.blk,
    hu.ws.keep (hk _ (.inl rfl)), hu.we.keep (hk _ (.inr (.inl rfl))),
    hu.wv.keep (hk _ (.inr (.inr rfl))),
    hu.cinv.stay t hhS hhE apE.ptr_ne (fun _ _ h => h) hclk,
    hu.einv.frame (t := t) (fun _ _ => rfl) rfl rfl hhV rfl hclk id id, hu.places,
    fun h => by rw [hhE]; exact hu.ep1 h, by rw [hhE]; exact VClock.le_trans hu.ep0 (hclk 0),
    hu.ent, hu.hold, fun i jr sn e hr => ?_, fun h0 h1 => ?_, fun h1 => ?_, hu.q, hu.xc⟩
  · rw [hhS]
    rcases hu.reg i jr sn e hr with h' | ⟨hlk, h'⟩
    · exact .inl (VClock.le_trans h' (hclk 1))
    · refine .inr ⟨hlk, ?_⟩
      rcases h' with ⟨hh, hle⟩ | hb
      · exact .inl ⟨hh, VClock.le_trans hle (hclk 0)⟩
      · exact .inr (before_atomics rfl hb)
  · show ((Lo.WS.hist _)[(Lo.WS.hist _).size - 1]!).Val _; rw [hhS]; exact hu.lvc h0 h1
  · show ((Lo.WV.hist _)[(Lo.WV.hist _).size - 1]!).Val _; rw [hhV]; exact hu.fin h1

/-- **`io` is in the protocol's rest** (the obligation of `FLock.Fits.wp_readRest`, the read of
`io`), for a layout with an `io` prefix of `Io`'s size whose load alignment `a` divides the
`Box`'s: its bytes, which decode to `io`, at the `Box`'s aligned address. -/
theorem io_rest {a : Nat} (hio : Lo.io = Enc.size Io) (ha : a ∣ Lo.align) (G : ThreadId → Gh)
    (rX : Res) (m : Mem) (hu : U Lo G rX m) :
    ∃ r A S K' bs, up (bytesAt bPtr A S K' bs) r ∧
      (∀ l fc, r.heap l = some fc → rX.heap l = some fc) ∧ bs.size = Enc.size Io ∧
      Enc.decode bs = pure (⟨⟩ : Io) ∧ (A + bPtr.off.toNat) % a = 0 ∧ K' ≠ .constGlobal := by
  obtain ⟨rIO, ⟨A, bs, hA, hbs, hdec, r₁, r₂, -, rfl, h₁, -⟩, hIOoff, hrX⟩ := hu.rest
  refine ⟨r₁, A, _, _, bs, h₁, fun l fc hl => ?_, by rw [hbs, hio], hdec hio, ?_, by decide⟩
  · have hb : ¬ Lo.BoxW l := fun hb => by
      have := hIOoff l hb; simp [FHeap.union_apply, hl] at this
    rw [hrX]; simp [FHeap.union_apply, cellsAt_none hb, hl]
  · simpa [bPtr] using Nat.mod_eq_zero_of_dvd (Nat.dvd_trans ha (Nat.dvd_of_mod_eq_zero hA))

/-- `io`'s accesses cover its bytes (`FLock.Fits.wp_readRest`). -/
theorem io_cov (hio : Lo.io = Enc.size Io) : Conc.Covers (IoR Lo) 0 bPtr.off.toNat (Enc.size Io) :=
  fun _ hb hl _ h2 => ⟨hb, hl, by simp [bPtr] at h2; omega⟩

/-! ## Field pointers -/

/-- A field pointer of the `Box` (block 0) is formed (`ptrProject`, MM-3). -/
theorem proj {m : Mem} (hb : BlkOk Lo m) {k : Nat} (hk : k ≤ Lo.size) :
    (ptrProject bPtr (·.add k)).run m = pure (bPtr.add k, m) := by
  obtain ⟨blk, hb, -, hsz, -⟩ := hb
  exact ptrProject_block_run hb rfl (by decide) (by simp [bPtr, hsz]; omega)

/-- The `Box` is block 0, from the protocol's invariant. -/
theorem blk_inv {G : ThreadId → Gh} {m : Mem} (hi : (proto Lo prodOf).inv G m) : BlkOk Lo m := by
  obtain ⟨rX, -, hu⟩ := hi; exact hu.blk

/-- A field pointer of the `Box` from the protocol's invariant. -/
theorem projI {G : ThreadId → Gh} {m : Mem} (hi : (proto Lo prodOf).inv G m) {k : Nat}
    (hk : k ≤ Lo.size) : (ptrProject bPtr (·.add k)).run m = pure (bPtr.add k, m) :=
  proj (blk_inv hi) hk

/-! ## The threads -/

/-- The invariant at a stop of a live thread `t`. -/
theorem inv_cur {G : ThreadId → Gh} {m : Mem} (t : ThreadId) (hi : (proto Lo prodOf).inv G m)
    (hph : (G t).1.ph ≠ .gone) : (proto Lo prodOf).inv G { m with current := t } := by
  obtain ⟨-, -, -, h⟩ := (fitsL (Lo := Lo) (prodOf := prodOf)).cur t hi hph
  exact h

/-- `main` spawned every thread. -/
theorem spawners {Y : ThreadId → X} {m : Mem} (h : Shape Y m) : ∀ r ∈ m.threads, r.spawner = 0 :=
  spawners_of_getElem fun i hi => by
    obtain ⟨h0, ⟨h1, -⟩ | ⟨h2, h1, -⟩⟩ := h
    · obtain rfl : i = 0 := by omega
      rw [Array.getElem?_eq_getElem hi] at h0; rw [Option.some.inj h0]
    · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · rw [Array.getElem?_eq_getElem hi] at h0; rw [Option.some.inj h0]
      · rw [Array.getElem?_eq_getElem hi] at h1; rw [Option.some.inj h1]

/-! ## `main`'s start -/

/-- A field pointer of the `Box` from `main`'s part before its spawn (the `Box`'s extent, next to
`R`: the plain mode). -/
theorem projO {own : ThreadId → Res} {rO : Res} {m : Mem} (ho : FOwned own rO m)
    (ht : 0 < m.threads.size) {A S : Nat} {bs : Array Byte} {R : FAssn}
    (h : ((up (bytesAt bPtr A S .stack bs) ⋆ bext 0 S .stack) ⋆ R) (own 0)) {k : Nat}
    (hk : k ≤ S) :
    (ptrProject bPtr (·.add k)).run m = pure (bPtr.add k, m) := by
  obtain ⟨blk, hb, -, hsz, -⟩ := ho.blkOf ht
    (Full.sep_assoc (Full.sep_mono_left (fun _ h => Full.sep_comm h) h))
  exact ptrProject_block_run hb rfl (by decide) (by simp [bPtr, hsz]; omega)

/-- The bytes `a .. c` of `bs` at `a` are the bytes `a .. b` and `b .. c`. -/
theorem split_at {bs : Array Byte} {A S a b c : Nat} {r : Res}
    (h : up (bytesAt (bPtr.add a) A S .stack (bs.extract a c)) r) (hab : a ≤ b) (hbc : b ≤ c)
    (hc : c ≤ bs.size) :
    (up (bytesAt (bPtr.add a) A S .stack (bs.extract a b)) ⋆
      up (bytesAt (bPtr.add b) A S .stack (bs.extract b c))) r := by
  have hsz : (bs.extract a c).size = c - a := by simp; omega
  have := up_sep ⟨bytesAt_split h.1 (k := b - a) (by omega), h.2⟩
  have e1 : (bs.extract a c).extract 0 (b - a) = bs.extract a b := by
    rw [Array.extract_extract]; congr 1 <;> omega
  have e2 : (bs.extract a c).extract (b - a) (bs.extract a c).size = bs.extract b c := by
    rw [Array.extract_extract, hsz]; congr 1 <;> omega
  have e3 : (bPtr.add (a : Int)).add ((b - a : Nat) : Int) = bPtr.add (b : Int) := by
    rw [Ptr.add_add]; congr 1; omega
  rwa [e1, e2, e3] at this

/-- **The `Box`'s bytes after `main`'s stores**, in the pieces of `inv_start` (a layout whose
parts follow each other: `io`, the mutex, the three words, `v`, `ready`, the padding). -/
theorem box_split {r : Res} {A : Nat} {bs : Array Byte} (hs : bs.size = Lo.size)
    (hc : Lo.io = Lo.mo ∧ Lo.mo + 4 = Lo.so ∧ Lo.so + 12 = Lo.xo ∧ Lo.xo + 4 = Lo.ro)
    (h : up (bytesAt bPtr A Lo.size .stack bs) r) :
    (up (bytesAt bPtr A Lo.size .stack (bs.extract 0 Lo.io)) ⋆
      (up (bytesAt (bPtr.add Lo.mo) A Lo.size .stack (bs.extract Lo.mo (Lo.mo + 4))) ⋆
      (up (bytesAt (bPtr.add Lo.so) A Lo.size .stack (bs.extract Lo.so (Lo.so + 12))) ⋆
      (up (bytesAt (bPtr.add Lo.xo) A Lo.size .stack (bs.extract Lo.xo (Lo.xo + 4))) ⋆
      (up (bytesAt (bPtr.add Lo.ro) A Lo.size .stack (bs.extract Lo.ro (Lo.ro + 1))) ⋆
       up (bytesAt (bPtr.add (Lo.ro + 1)) A Lo.size .stack
        (bs.extract (Lo.ro + 1) Lo.size))))))) r := by
  obtain ⟨h1, h2, h3, h4⟩ := hc
  have hok := Lo.ok
  have h0 := up_sep ⟨bytesAt_split h.1 (k := Lo.io) (by omega), h.2⟩
  rw [hs] at h0
  refine sep_mono_right (fun _ hr => ?_) h0
  rw [h1] at hr
  refine sep_mono_right (fun _ hr => ?_) (split_at hr (b := Lo.mo + 4) (by omega) (by omega)
    (by omega))
  rw [h2] at hr
  refine sep_mono_right (fun _ hr => ?_) (split_at hr (b := Lo.so + 12) (by omega) (by omega)
    (by omega))
  rw [h3] at hr
  refine sep_mono_right (fun _ hr => ?_) (split_at hr (b := Lo.xo + 4) (by omega) (by omega)
    (by omega))
  rw [h4] at hr
  exact split_at hr (b := Lo.ro + 1) (by omega) (by omega) (by omega)

theorem sep_box {I W B V Rd P b pl : FAssn} {r : Res}
    (h : (((I ⋆ (W ⋆ (B ⋆ (V ⋆ (Rd ⋆ P))))) ⋆ b) ⋆ pl) r) :
    (((P ⋆ pl) ⋆ ((V ⋆ Rd) ⋆ W)) ⋆ (B ⋆ (I ⋆ b))) r := by
  have e : (((I ⋆ (W ⋆ (B ⋆ (V ⋆ (Rd ⋆ P))))) ⋆ b) ⋆ pl) =
      (((P ⋆ pl) ⋆ ((V ⋆ Rd) ⋆ W)) ⋆ (B ⋆ (I ⋆ b))) := by
    ac_rfl
  rw [e] at h; exact h

/-- **Before the spawn**: `main` owns the `Box` after its stores (the bytes `bs`, whose mutex,
three words, `v` and `ready` are 0 and `false`), with its extent, and the plain mode. The
protocol's invariant holds with `main`'s part the padding and the plain mode (`Res.Plain`: its
sync waits may use stack blocks, `CondImpl.wait_wp`, `EventImpl.wait_wp`). -/
theorem inv_of_box {m : Mem} {r : Res} {A : Nat} {bs : Array Byte}
    (ho : FOwned (upd (fun _ => rnil) 0 r) rnil m)
    (hF : ((up (bytesAt bPtr A Lo.size .stack bs) ⋆ bext 0 Lo.size .stack) ⋆ plain) r)
    (hs : bs.size = Lo.size)
    (hc : Lo.io = Lo.mo ∧ Lo.mo + 4 = Lo.so ∧ Lo.so + 12 = Lo.xo ∧ Lo.xo + 4 = Lo.ro)
    (hW : bs.extract Lo.mo (Lo.mo + 4) = Enc.encode (0 : BitVec 32))
    (hS : bs.extract Lo.so (Lo.so + 4) = Enc.encode (0 : BitVec 32))
    (hE : bs.extract (Lo.so + 4) (Lo.so + 8) = Enc.encode (0 : BitVec 32))
    (hV' : bs.extract (Lo.so + 8) (Lo.so + 12) = Enc.encode (0 : BitVec 32))
    (hV : bs.extract Lo.xo (Lo.xo + 4) = Enc.encode (0 : BitVec 32))
    (hR : bs.extract Lo.ro (Lo.ro + 1) = Enc.encode false)
    (hIo : Lo.io = Enc.size Io → bs.extract 0 Lo.io = Enc.encode (⟨⟩ : Io))
    (hA : A % Lo.align = 0) (hth : m.threads = #[{ spawner := 0, joined := true }])
    (hat : m.atomics = #[]) (hq : m.waiters = #[]) :
    ∃ rM, rM.Plain ∧ (proto Lo prodOf).inv (upd G0 0 (gO rM { ph := .pre })) m := by
  have hok := Lo.ok
  obtain ⟨_, _, hd, rfl, ⟨rM, _, hdM, rfl, hpM, ⟨_, rW, hdRW, rfl, ⟨rV, rRd, hdVR, rfl, hV₁, hR₁⟩,
    hW₁⟩⟩, ⟨rB, rIO, hdB, rfl, hB₁, hIO⟩⟩ :=
    sep_box (sep_mono_left (fun _ h => sep_mono_left (fun _ h => box_split hs hc h) h) hF)
  refine ⟨rM, Res.plain_of_sep hpM, ?_⟩
  rw [hW] at hW₁; rw [hV] at hV₁; rw [hR] at hR₁
  have hsz : (bs.extract Lo.so (Lo.so + 12)).size = 12 := by simp; omega
  have hx : ∀ k, k ≤ 8 → (bs.extract Lo.so (Lo.so + 12)).extract k (k + 4) =
      bs.extract (Lo.so + k) (Lo.so + k + 4) := fun k hk => by
    rw [Array.extract_extract]; congr 1 <;> omega
  exact inv_start (own := fun _ => rnil) ho (fun _ _ => rfl) hd hdM hdRW hdVR hdB
    ⟨A, _, hA, by simp; omega, fun h => by rw [hIo h]; exact LawfulEnc.decode_encode _, hIO⟩ hW₁ hB₁ hV₁ hR₁ hsz (by rw [hx 0 (by omega)]; exact hS)
    (by rw [hx 4 (by omega)]; exact hE) (by rw [hx 8 (by omega)]; exact hV') hA hth hat hq

/-! ## The sync objects -/

section Sync

variable (mi : MutexImpl Tgt) (ci : CondImpl Tgt) (ei : EventImpl Tgt)

/-- **The producer's `lock`**: it holds the mutex, at `hl`. -/
theorem wp_lockP (hLc : Lo.c = mi.c) {p : Ptr} (hp : p = (L Lo).ptr) (io : Io)
    {G : ThreadId → Gh} {m : Mem} {d : Nat}
    (hi : (proto Lo prodOf).inv (upd G 1 (gO rnil { ph := .lk })) m) :
    (proto Lo prodOf).WP 1 (mi.lock p io) (fun _ G' m' d' => d' < d ∧ m'.current = 1 ∧
      ∃ rL, (proto Lo prodOf).inv (upd G' 1 (gH rnil rL { ph := .hl })) m') G m d :=
  WP.mono (fun _ _ _ _ ⟨hd, hc, rL, hi'⟩ => ⟨hd, hc, rL, inv_hl hi'⟩)
    (mi.lock_wp fitsL rfl hp hLc 1 (gO rnil { ph := .lk }) rfl ⟨rfl, rfl, nofun, nofun⟩
      io G m d hi)

/-- **The producer's `unlock`** at `rdy`: it is out of the mutex, to its `signal`. -/
theorem wp_unlockP (hLc : Lo.c = mi.c) {p : Ptr} (hp : p = (L Lo).ptr) (io : Io)
    {G : ThreadId → Gh} {m : Mem} {d : Nat} {rL : Res}
    (hi : (proto Lo prodOf).inv (upd G 1 (gH rnil rL { ph := .rdy })) m) (hc : m.current = 1) :
    (proto Lo prodOf).WP 1 (mi.unlock p io) (fun _ G' m' d' => d' ≤ d ∧ m'.current = 1 ∧
      (proto Lo prodOf).inv (upd G' 1 (gO rnil { ph := .sg })) m') G m d :=
  WP.mono (fun _ _ _ _ ⟨hd, hc', hi'⟩ => ⟨hd, hc', inv_sg hi'⟩)
    (mi.unlock_wp fitsL rfl hp hLc 1 (gH rnil rL { ph := .rdy }) rfl
      ⟨rfl, rfl, nofun, nofun⟩ io G m d hi hc)

/-- **`main`'s `lock`** at `run`. -/
theorem wp_lockM (hLc : Lo.c = mi.c) {p : Ptr} (hp : p = (L Lo).ptr) (io : Io)
    {G : ThreadId → Gh} {m : Mem} {d : Nat} {rM : Res}
    (hi : (proto Lo prodOf).inv (upd G 0 (gO rM { ph := .run })) m) :
    (proto Lo prodOf).WP 0 (mi.lock p io) (fun _ G' m' d' => d' < d ∧ m'.current = 0 ∧
      ∃ rL, (proto Lo prodOf).inv (upd G' 0 (gH rM rL { ph := .run })) m') G m d :=
  mi.lock_wp fitsL rfl hp hLc 0 (gO rM { ph := .run }) rfl ⟨rfl, rfl, nofun, nofun⟩ io G
    m d hi

/-- **`main`'s `unlock`** at `run`: out of the mutex, to the event's wait. -/
theorem wp_unlockM (hLc : Lo.c = mi.c) {p : Ptr} (hp : p = (L Lo).ptr) (io : Io)
    {G : ThreadId → Gh} {m : Mem} {d : Nat} {rM rL : Res}
    (hi : (proto Lo prodOf).inv (upd G 0 (gH rM rL { ph := .run })) m) (hc : m.current = 0) :
    (proto Lo prodOf).WP 0 (mi.unlock p io) (fun _ G' m' d' => d' ≤ d ∧ m'.current = 0 ∧
      (proto Lo prodOf).inv (upd G' 0 (gO rM { ph := .ev })) m') G m d :=
  WP.mono (fun _ _ _ _ ⟨hd, hc', hi'⟩ => ⟨hd, hc', inv_ev hi'⟩)
    (mi.unlock_wp fitsL rfl hp hLc 0 (gH rM rL { ph := .run }) rfl
      ⟨rfl, rfl, nofun, nofun⟩ io G m d hi hc)

/-- **`main`'s condition wait**, holding the mutex at `run` after it read `ready = false`. -/
theorem wp_cwait (hLc : Lo.c = ci.c) {p q : Ptr} (hp : p = Lo.WS.ptr) (hq : q = (L Lo).ptr)
    (io : Io) {G : ThreadId → Gh} {m : Mem} {d : Nat} {rM rL : Res} (hpl : rM.Plain)
    (hi : (proto Lo prodOf).inv (upd G 0 (gH rM rL { ph := .run })) m) (hc : m.current = 0)
    (hr : (G 1).2.ph.hasR = false) :
    (proto Lo prodOf).WP 0 (ci.wait p io q) (fun _ G' m' d' => d' < d ∧ m'.current = 0 ∧
      ∃ rL', (proto Lo prodOf).inv (upd G' 0 (gH rM rL' { ph := .run })) m') G m d := by
  obtain ⟨hone, hhb, hent⟩ := cwait_ok hi hr
  exact ci.wait_wp fitsC rfl hp hq hLc 0 (gH rM rL { ph := .run }) rfl rfl
    ⟨rfl, rfl, nofun, nofun⟩ io G m d
    hone hhb hent cwait_live hpl hi hc

/-- **The producer's `signal`** at `sg`: a registered `main` is signalled; to the event's `set`. -/
theorem wp_signal {p : Ptr} (hp : p = Lo.WS.ptr) (io : Io) {G : ThreadId → Gh} {m : Mem}
    {d : Nat} (hi : (proto Lo prodOf).inv (upd G 1 (gO rnil { ph := .sg })) m) :
    (proto Lo prodOf).WP 1 (ci.signal p io) (fun _ G' m' d' => d' < d ∧ m'.current = 1 ∧
      (proto Lo prodOf).inv (upd G' 1 (gO rnil { ph := .st })) m') G m d :=
  WP.mono (fun _ _ _ _ ⟨hd, hc, hi', hs⟩ => ⟨hd, hc, inv_st hi' fun i jr sn e h => hs 0 i jr sn e h⟩)
    (ci.signal_wp fitsC rfl hp 1 (gO rnil { ph := .sg }) rfl rfl rfl io G m d
      (fun G₁ rX m₁ hg hu u i jr sn e hr => signal_seen G₁ rX m₁ hg hu u i jr sn e hr) hi)

/-- **The producer's `set`** at `st`: the event is set; the producer's end. -/
theorem wp_set {p : Ptr} (hp : p = Lo.WV.ptr) (io : Io) {G : ThreadId → Gh} {m : Mem} {d : Nat}
    (hi : (proto Lo prodOf).inv (upd G 1 (gO rnil { ph := .st })) m) :
    (proto Lo prodOf).WP 1 (ei.set p io) (fun _ G' m' d' => d' < d ∧ m'.current = 1 ∧
      (proto Lo prodOf).inv (upd G' 1 (⟨.gone, rnil, rnil⟩, { ph := .fin })) m') G m d :=
  WP.mono (fun _ _ _ _ ⟨hd, hc, hs, hi'⟩ => ⟨hd, hc, inv_end hi' hs⟩)
    (ei.set_wp fitsE rfl hp 1 (gO rnil { ph := .st }) rfl rfl (.inl rfl) io G m d hi)

/-- **`main`'s event wait** at `ev`: to its join. -/
theorem wp_ewait {p : Ptr} (hp : p = Lo.WV.ptr) (io : Io) {G : ThreadId → Gh} {m : Mem} {d : Nat}
    {rM : Res} (hpl : rM.Plain) (hi : (proto Lo prodOf).inv (upd G 0 (gO rM { ph := .ev })) m) :
    (proto Lo prodOf).WP 0 (ei.wait p io) (fun _ G' m' d' => d' < d ∧ m'.current = 0 ∧
      (proto Lo prodOf).inv (upd G' 0 (gO rM { ph := .joins })) m') G m d := by
  obtain ⟨hone, hhb⟩ := ewait_ok hi
  exact WP.mono (fun _ _ _ _ ⟨hd, hc, _, hi'⟩ => ⟨hd, hc, inv_joins hi'⟩)
    (ei.wait_wp fitsE rfl hp 0 (gO rM { ph := .ev }) rfl rfl (.inl rfl) io G m d hone hhb
      ewait_live hpl hi)

end Sync

/-! ## `v` and `ready` -/

/-! The mutex's holder steps on `v` and `ready` are the library's `FLock.Fits.wp_hold`, which the
walks apply with the holder's new place: `main`'s loads keep `U` by `U_holdStep`, the producer's
stores by `U_storeHeld`; `main` reads `v = 7` once the producer stored `ready` (`vOf_ready`). -/

/-- **The producer's stores of `v` and `ready`**, holding the mutex, keep `U` (the obligation of
`FLock.Fits.wp_hold` from `x₀` to `x₁`). -/
theorem U_storeHeld {G : ThreadId → Gh} {rX : Res} {m m' : Mem} {rp rL r : Res} {x₀ x₁ : X}
    (hu : U Lo (upd G 1 (gH rp rL x₀)) rX m) (hiL : (L Lo).Inv (upd G 1 (gH rp rL x₀)) rX m)
    (hs : FStepIn (rsum ((L Lo).wordR m) rX).heap.erase m m')
    (hL : (L Lo).Inv (upd G 1 (gH rp r x₁)) rX m')
    (hp₀ : x₀ = { ph := .hl } ∨ x₀ = { ph := .v7 }) (hp₁ : x₁ = { ph := .v7 } ∨ x₁ = { ph := .rdy }) :
    U Lo (upd G 1 (gH rp r x₁)) rX m' :=
  U_store hp₀ hp₁ hL (U_holdStep hiL hu hs hL)

/-- `v` is 7 once the producer stored `ready`. -/
theorem vOf_ready {x : X} (hr : x.ph.hasR = true) : vOf x = 7 := by
  unfold vOf; revert hr; cases x.ph <;> decide

/-! ## The producer's end and `main`'s join -/

/-- **The producer's end** (`QKid`): it is `gone` at `fin` and spawned no thread. -/
theorem qkid {G : ThreadId → Gh} {m : Mem} {d : Nat}
    (hi : (proto Lo prodOf).inv (upd G 1 (⟨.gone, rnil, rnil⟩, { ph := .fin })) m) :
    (proto Lo prodOf).QKid 1 () G m d := by
  refine ⟨_, hi, ⟨rfl, rfl⟩, fun _ => ?_⟩
  obtain ⟨rX, -, hu⟩ := hi
  exact joinedAll_of_main (spawners hu.shape) (by decide)

/-- **`main`'s join of the producer** at `joins`: then every thread is joined, the `Box` is
block 0 and every clock is below `main`'s. -/
theorem wp_join {σ : Type} {s : σ} {G : ThreadId → Gh} {m : Mem} {n : Nat} {rM : Res}
    (hi : (proto Lo prodOf).inv (upd G 0 (gO rM { ph := .joins })) m)
    {Q : Unit × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ k G₁ m', n = k + 1 → BlkOk Lo m' → m'.ClocksLe → joinedAll 0 m' → Q ((), s) G₁ m' k) :
    (proto Lo prodOf).WP 0 ((joinC 1 : CM Tgt σ Unit).run s) Q G m n := by
  refine WP.joinC fun k hk => ⟨_, hi, fun G₁ m₁ hg hi₁ => ?_⟩
  obtain ⟨rX, hL, hu⟩ := hi₁
  obtain ⟨h00, ⟨-, h0, -⟩ | ⟨hs2, hr1, -⟩⟩ := hu.shape
  · exfalso; change (G₁ 0).2 = _ at h0; rw [hg] at h0; cases h0
  refine ⟨fun _ => ⟨by show (0 : Nat) < 1; decide, by rw [hs2]; decide, ⟨rfl, rfl⟩,
    by simp [Thread.joinValid, Mem.isGated, hr1]⟩, fun _ => ⟨fun _ =>
    join_run (m := { m₁ with current := 0 }) hr1 rfl rfl, fun m' hj => ?_⟩⟩
  obtain ⟨rec, -, -, hm'⟩ := join_eq hj
  refine h k G₁ m' hk (by rw [hm']; exact hu.blk)
    (Mem.ClocksLe.join2 hj (by rw [hL.w.csize, hs2])) fun r hr hsp => ?_
  have hth : m'.threads = m₁.threads.set! 1 { rec with joined := true } := by rw [hm']
  simp only [hth] at hr
  obtain ⟨i, hi', rfl⟩ := Array.mem_iff_getElem.mp hr
  simp only [Array.size_set!] at hi'
  simp only [Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds hi'] at hsp ⊢
  split
  · rfl
  · obtain rfl : i = 0 := by omega
    rw [Array.getElem?_eq_getElem (by omega)] at h00
    rw [Option.some.inj h00]

/-- **`main`'s free of the `Box`** after its join: its end races with no access. -/
theorem wp_free {G : ThreadId → Gh} {m : Mem} {n : Nat} (hb : BlkOk Lo m) (hcl : m.ClocksLe)
    {Q : Unit → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ m', m'.threads = m.threads → Q () G m' n) :
    (proto Lo prodOf).WP 0 (ConcM.liftMem (free bPtr) : ConcM Tgt Unit) Q G m n := by
  obtain ⟨blk, hblk, hl, -, hk⟩ := hb
  refine WP.liftMem (fun e he => (free_noErr hblk hl (hcl.freeRaces _ _) (by rw [hk]; nofun) e
    he).elim) fun _ m' hfr => ?_
  obtain ⟨b', blk', -, -, rfl⟩ := free_ok hfr
  exact ⟨rfl, h _ rfl⟩

end Handoff
end Zig
