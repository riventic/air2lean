import Proofs.Threadsync.WaitGroup.Protocol
import ZigLean.Sep.Full.Local
import ZigLean.Sep.Full.Auto
import ZigLean.Sep.Full.AutoWP
import ZigLean.Sep.Full.LockSteps

/-!
# The start of `waitGroup`'s protocol

`main`, before `startMany`, owns the `Tally` after its store (`inv_of_box`): it gives the group's
16 bytes (the state, the event, the padding) with the `Tally`'s extent to the protocol's rest
(`FOwned.give`; the bytes are then read as their cells, `Rest`), and the mutex with the counter to
the lock (`FLock.Inv.make`). The event starts with every thread out of its code
(`FEvent.Inv.start`). Once for every version; each version's walk gives the `Tally`'s bytes after
its store.
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Full Zig.Full.FAssn

namespace Threadsync.WG

/-- No thread at the start. -/
def G0 : ThreadId → Gh := fun _ => (⟨.gone, rnil, rnil⟩, {})

/-- A shared word at the start, of every width: no atomic location, each access to it happened
before every thread, and the value 0, written at no clock. -/
theorem word_init {n nb : Nat} {W : Word n nb} {m : Mem} {blk : Block} (hW : W.b = 0)
    (hal : (blk.addr + W.o) % nb = 0) (hsz : W.o + nb ≤ blk.bytes.size)
    (hb : m.blocks[0]? = some blk) (hl : blk.live = true) (hk : blk.kind = .stack)
    (hat : m.atomics = #[])
    (hv : (intOfBytes n (blk.bytes.extract W.o (W.o + nb))).run = some (.ok 0))
    (hfp : ∀ e ∈ m.footprint, W.Hits e → AllLe m e.clock) :
    W.Ok m ∧ (W.hist m).size = 1 ∧ (W.hist m)[0]!.Val (0 : BitVec n) := by
  have hno : ∀ i l, ¬ W.Loc m i l := fun i l hl => by
    have := (Word.loc_get hl).1; rw [hat] at this; simp at this
  have hu : W.Holds m 0 := by unfold Word.Holds curBytes; rw [hW, hb]; exact hv
  refine ⟨⟨⟨blk, by rw [hW]; exact hb, hl, hsz, hal, by rw [hk]; simp⟩,
    fun l hl' => by rw [hat] at hl'; simp at hl', fun i l h => absurd h (hno i l),
    fun e he hh => .inr ((hfp e he hh).on _), ⟨0, hu⟩, fun i l h => absurd h (hno i l)⟩, ?_, ?_⟩
  · rw [Word.hist_none hno]; rfl
  · rw [Word.hist_none hno]; exact hu

theorem heap_ne_l {a b : Res} {l : Zig.Loc} (h : a.heap l ≠ none) : (rsum a b).heap l ≠ none := by
  simp only [FHeap.union_apply, ne_eq, Option.or_eq_none_iff, not_and]
  intro h'; exact absurd h' h

theorem heap_ne_r {a b : Res} {l : Zig.Loc} (h : b.heap l ≠ none) : (rsum a b).heap l ≠ none := by
  simp only [FHeap.union_apply, ne_eq, Option.or_eq_none_iff, not_and]
  intro _; exact h

theorem erase_ne {a : Res} {l : Zig.Loc} (h : a.heap l ≠ none) : a.heap.erase l ≠ none := by
  simpa [FHeap.erase] using h

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

/-- **The `Tally`'s bytes after `main`'s store**: the group's 16 bytes, the mutex, the counter. -/
theorem tally_split {r : Res} {A : Nat} {bs : Array Byte} (hs : bs.size = 24)
    (h : up (bytesAt bPtr A 24 .stack bs) r) :
    (up (bytesAt (bPtr.add (0 : Nat)) A 24 .stack (bs.extract 0 16)) ⋆
      (up (bytesAt (bPtr.add (16 : Nat)) A 24 .stack (bs.extract 16 20)) ⋆
       up (bytesAt (bPtr.add (20 : Nat)) A 24 .stack (bs.extract 20 24)))) r := by
  have h0 : up (bytesAt (bPtr.add (0 : Nat)) A 24 .stack (bs.extract 0 24)) r := by
    have e1 : bPtr.add ((0 : Nat) : Int) = bPtr := by simp [bPtr, Ptr.add]
    have e2 : bs.extract 0 24 = bs := by rw [Array.extract_eq_self_iff]; omega
    rw [e1, e2]; exact h
  exact sep_mono_right (fun _ hr => split_at hr (b := 20) (by omega) (by omega) (by omega))
    (split_at h0 (b := 16) (by omega) (by omega) (by omega))

theorem sep_tally {P0 PW PN E pl : FAssn} {r : Res}
    (h : (((P0 ⋆ (PW ⋆ PN)) ⋆ E) ⋆ pl) r) : ((pl ⋆ (PN ⋆ PW)) ⋆ (P0 ⋆ E)) r := by
  have e : (((P0 ⋆ (PW ⋆ PN)) ⋆ E) ⋆ pl) = ((pl ⋆ (PN ⋆ PW)) ⋆ (P0 ⋆ E)) := by ac_rfl
  rw [e] at h; exact h

/-- **Before `startMany`**: `main` owns the `Tally` after its store (the bytes `bs`: the group's
state, the event, the mutex and the counter 0) with its extent, and the plain mode. The protocol's
invariant holds with `main`'s part the plain mode (`Res.Plain`: its event wait may use stack
blocks, `EventImpl.wait_wp`). -/
theorem inv_of_box {m : Mem} {r : Res} {A : Nat} {bs : Array Byte}
    (ho : FOwned (upd (fun _ => rnil) 0 r) rnil m)
    (hF : ((up (bytesAt bPtr A 24 .stack bs) ⋆ bext 0 24 .stack) ⋆ plain) r)
    (hs : bs.size = 24)
    (hG : bs.extract 0 8 = Enc.encode (0 : BitVec 64))
    (hE : bs.extract 8 12 = Enc.encode (0 : BitVec 32))
    (hM : bs.extract 16 20 = Enc.encode (0 : BitVec 32))
    (hN : bs.extract 20 24 = Enc.encode (0 : BitVec 32))
    (hA : A % 8 = 0) (hth : m.threads = #[{ spawner := 0, joined := true }])
    (hat : m.atomics = #[]) (hq : m.waiters = #[]) :
    ∃ rM, rM.Plain ∧ proto.inv (upd G0 0 (gO rM { ph := .pre })) m := by
  have h1 : m.threads.size = 1 := by rw [hth]; rfl
  have ht : 0 < m.threads.size := by rw [h1]; decide
  -- the block: every byte of the `Tally` is `main`'s
  obtain ⟨blk, hblk, hl, hAd, hS, hK, hx⟩ :=
    ho.bytesOf ht (rfl : bPtr.block = some 0) (by rw [hs]; decide) (by rw [upd_self]; exact hF)
  have hx' : blk.bytes.extract 0 24 = bs := by
    have : bPtr.off.toNat = 0 := rfl
    rw [this, hs] at hx; exact hx
  have hext : ∀ a b, b ≤ 24 → blk.bytes.extract a b = bs.extract a b := fun a b hb => by
    rw [← hx', Array.extract_extract]; congr 1 <;> omega
  have hown24 : ∀ x, x < 24 → r.heap (0, x) ≠ none := fun x hx24 => by
    obtain ⟨_, _, -, rfl, ⟨rBy, _, -, rfl, hBy, -⟩, -⟩ := hF
    refine heap_ne_l (heap_ne_l ((up_bytesAt_some hBy rfl (0, x)).mpr ⟨rfl, ?_, ?_⟩))
    · show bPtr.off.toNat ≤ x; exact Nat.zero_le _
    · show x < bPtr.off.toNat + bs.size; rw [hs]; exact hx24
  -- each access to a byte of `main`'s part happened before `main`
  have hown0 : ∀ e ∈ m.footprint, e.block = 0 → (∃ x, e.off ≤ x ∧ x < e.off + e.len ∧ x < 24) →
      VClock.le e.clock (m.clocks[0]!) = true := fun e he hb ⟨x, h1x, h2x, h3x⟩ =>
    ho.owns 0 ht e he (.inl ⟨x, h1x, h2x, by rw [hb, upd_self]; exact Res.owned_of_heap (hown24 x h3x)⟩)
  -- the pieces
  obtain ⟨_, _, hd, rfl, ⟨rM, _, hdM, rfl, hpM, ⟨rN, rW, hdNW, rfl, hN₁, hW₁⟩⟩,
      ⟨rB, rE, hdB, rfl, hB₁, hE₁⟩⟩ :=
    sep_tally (sep_mono_left (fun _ h => sep_mono_left (fun _ h => tally_split hs h) h) hF)
  refine ⟨rM, Res.plain_of hpM, ?_⟩
  have hFresh : EV.Fresh m := by
    intro i l hl
    have hloc := hl.2
    simp [hat] at hloc
  -- the two words
  have hfpW : ∀ {n nb : Nat} (W : Word n nb), W.b = 0 → W.o + nb ≤ 24 →
      ∀ e ∈ m.footprint, W.Hits e → AllLe m e.clock := fun W hb hw e he hh =>
    allLe_of_one h1 (by
      obtain ⟨heb, x, h1x, h2x, h3x, h4x⟩ := hh
      exact hown0 e he (by rw [heb, hb]) ⟨x, h1x, h2x, by omega⟩)
  obtain ⟨hwgOk, hwgz, hwgv⟩ := word_init (W := WG) rfl
    (by show (blk.addr + 0) % 8 = 0; rw [hAd]; omega) (by show 0 + 8 ≤ _; rw [hS]; decide)
    hblk hl hK hat (by
      show (intOfBytes 64 (blk.bytes.extract 0 (0 + 8))).run = _
      rw [hext 0 8 (by decide), hG]; exact intOfBytes_rmw 0)
    (hfpW WG rfl (by decide))
  obtain ⟨hevOk, hevz, hevv⟩ := word_init (W := EV) rfl
    (by show (blk.addr + 8) % 4 = 0; rw [hAd]; omega) (by show 8 + 4 ≤ _; rw [hS]; decide)
    hblk hl hK hat (by
      show (intOfBytes 32 (blk.bytes.extract 8 (8 + 4))).run = _
      rw [hext 8 12 (by decide), hE]; exact intOfBytes_rmw 0)
    (hfpW EV rfl (by decide))
  -- the mutex holds 0
  have h0 : L.U32 m 0 := by
    show (intOfBytes 32 (curBytes m 0 16 4)).run = _
    unfold curBytes; rw [hblk]
    simp only [Option.map_some, Option.getD_some]
    rw [hext 16 20 (by decide), hM]; exact intOfBytes_rmw 0
  -- the rest: `rB` (the group's 16 bytes) and `rE` (the extent); read `rB` as the cells
  have hBin : ∀ l, rB.heap l ≠ none ↔ BoxW l := fun l => by
    rw [up_bytesAt_some hB₁ rfl l]
    have e : (bPtr.add ((0 : Nat) : Int)).off.toNat = 0 := by simp [bPtr, Ptr.add]
    rw [e, Array.size_extract, hs]; simp [BoxW]
  have hEoff : ∀ l, rE.heap l = none := fun l => by rw [hE₁.1]; rfl
  have ho' := ho.give (t := 0) ht (by rw [upd_self]) hd
  rw [upd_upd, rsum_rnil] at ho'
  have ho'' : FOwned (upd (fun _ => rnil) 0 (rsum rM (rsum rN rW)))
      (rsum (cellsAt BoxW m) rE) m := by
    have hBoff : ∀ l, ¬ BoxW l → rB.heap l = none := fun l hb => by
      cases e : rB.heap l with
      | none => rfl
      | some _ => exact absurd ((hBin l).mp (by rw [e]; simp)) hb
    refine ho'.congrRestU (fun l => ?_) (fun l fc' hl' => ?_) ?_ ?_
    · by_cases hb : BoxW l
      · obtain ⟨fc, hfc⟩ := Option.ne_none_iff_exists'.mp ((hBin l).mpr hb)
        have := ho'.rest_cell (l := l) (fc := fc) (by simp [FHeap.union_apply, hfc])
        simp only [FHeap.union_apply, cellsAt_of hb, hEoff l, hfc, Option.or_none]
        cases e : m.heap l with
        | none => rw [e] at this; cases this
        | some c => rw [e] at this; simpa [Cell.norm] using this
      · simp [FHeap.union_apply, cellsAt_none hb, hBoff l hb, hEoff l]
    · by_cases hb : BoxW l
      · simp only [FHeap.union_apply, cellsAt_of hb, hEoff l, Option.or_none,
          Option.map_eq_some_iff] at hl'
        obtain ⟨c, -, rfl⟩ := hl'
        exact .inl rfl
      · simp [FHeap.union_apply, cellsAt_none hb, hEoff l] at hl'
    · simp [cellsAt, hB₁.2.1, Know.none_union]
    · simp [cellsAt, hB₁.2.2]
  -- the ghost values
  have hGu : ∀ u, u ≠ 0 → upd G0 0 (gO rM { ph := .pre }) u = G0 u := fun u h => upd_ne _ _ h
  have hX0 : (upd G0 0 (gO rM { ph := .pre }) 0).2 = { ph := .pre } := by rw [upd_self]; rfl
  have hXu : ∀ u, u ≠ 0 → (upd G0 0 (gO rM { ph := .pre }) u).2 = {} := fun u h => by
    rw [hGu u h]; rfl
  have hX : ∀ u, (upd G0 0 (gO rM { ph := .pre }) u).2 = { ph := .pre } ∨
      (upd G0 0 (gO rM { ph := .pre }) u).2 = {} := fun u => by
    by_cases h : u = 0
    · subst h; exact .inl hX0
    · exact .inr (hXu u h)
  have hsx : ∀ u, (upd G0 0 (gO rM { ph := .pre }) u).2.sx = false := fun u => by
    rcases hX u with h | h <;> rw [h]
  have hwk : ∀ u, (upd G0 0 (gO rM { ph := .pre }) u).2.wk = false := fun u => by
    rcases hX u with h | h <;> rw [h]
  have hfd : ∀ u, (upd G0 0 (gO rM { ph := .pre }) u).2.ph.fd = false := fun u => by
    rcases hX u with h | h <;> rw [h] <;> rfl
  have hwa : ∀ u, (upd G0 0 (gO rM { ph := .pre }) u).2.ph.wa = false := fun u => by
    rcases hX u with h | h <;> rw [h] <;> rfl
  have he : ∀ u, (upd G0 0 (gO rM { ph := .pre }) u).2.e = .out := fun u => by
    rcases hX u with h | h <;> rw [h]
  have hp1 : (upd G0 0 (gO rM { ph := .pre }) 1).2.ph = .none := by rw [hXu 1 (by decide)]
  have hp2 : (upd G0 0 (gO rM { ph := .pre }) 2).2.ph = .none := by rw [hXu 2 (by decide)]
  have hset0 : ∀ j, j < (EV.hist m).size → ¬ IsSetW m j := fun j hj hs2 => by
    rw [hevz] at hj
    obtain rfl : j = 0 := by omega
    unfold IsSetW at hs2
    have := hevv.symm.trans hs2
    exact absurd (Except.ok.inj (Option.some.inj this)) (by decide)
  refine ⟨rsum (cellsAt BoxW m) rE, FLock.Inv.make (t := 0) (rL := rN) (rW := rW) ho''
    rfl ht (fun u hu => ?_) (by rw [upd_self, upd_self]; rfl) (by rw [upd_self]; exact hdM) hdNW
    (fun l => ?_) hW₁.2.1 hW₁.2.2 (fun u => ?_) (fun u => ?_) ?_
    ⟨blk, hblk, hl, by rw [hS]; decide, by show (blk.addr + 16) % 4 = 0; rw [hAd]; omega,
      by rw [hK]; decide, by rw [hK]; simp [BlockKind.mappedLo]⟩
    h0 (by rw [hat]; simp) hq (allLe_of_one h1 (VClock.le_refl _)), ?_⟩
  · rw [upd_ne _ _ hu]
    unfold FLock.own; rw [hGu u hu]; split <;> simp [G0, FLock.prod, rnil_rsum]
  · rw [up_bytesAt_some hW₁ rfl l]
    have e : (bPtr.add ((16 : Nat) : Int)).off.toNat = 16 := by simp [bPtr, Ptr.add]
    rw [e, Array.size_extract, hs]
    show _ ↔ l.1 = 0 ∧ 16 ≤ l.2 ∧ l.2 < 16 + 4
    simp
  · by_cases hu : u = 0
    · subst hu; rw [upd_self]; exact .inl ⟨rfl, ht, rfl⟩
    · rw [hGu u hu]; exact .inr rfl
  · by_cases hu : u = 0
    · subst hu; rw [upd_self]; rfl
    · rw [hGu u hu]; rfl
  · -- the counter: 0
    show R (fun u => (upd G0 0 (gO rM { ph := .pre }) u).2) rN
    unfold R X.cnt
    rw [hp1, hp2]
    rw [hN] at hN₁
    exact ⟨⟨A, 24, .stack, Enc.encode (0 : BitVec 32), by simp [bPtr, Ptr.add]; omega,
      LawfulEnc.size_encode _, LawfulEnc.decode_encode _, hN₁.1, by decide⟩, hN₁.2.1, hN₁.2.2⟩
  · refine ⟨⟨by rw [hth]; rfl, by show (upd G0 0 _ 0).2.ph.isMain = true; rw [hX0]; rfl,
        fun u hu => hXu u (by unfold ThreadId at *; omega),
        .inl ⟨h1, by show (upd G0 0 _ 0).2.ph.rank ≤ 1; rw [hX0]; decide,
          hXu 1 (by decide), hXu 2 (by decide)⟩⟩,
      ⟨rE, hE₁, fun l _ => hEoff l, rfl⟩, ⟨blk, hblk, hl, hS, hK⟩, hwgOk.on _, hevOk.on _,
      FEvent.Inv.start (E := E) hevz hevv he hq hFresh, ?_,
      fun u h => absurd h (by rw [hfd u]; decide),
      fun u h => absurd h (by rw [hsx u]; decide),
      fun h => absurd h (by rw [hX0]; decide),
      fun j hj hs2 => absurd hs2 (hset0 j hj),
      fun i hi j hj hsi _ => absurd hsi (hset0 i hi),
      fun u h => absurd h (by rw [hsx u]; decide),
      fun u h => absurd h (by rw [hfd u]; decide),
      fun u hu => by rw [hGu u (by unfold ThreadId at *; omega)]; rfl,
      fun u h => absurd h (by rw [hwa u]; decide),
      fun u h => absurd h (by rw [hwk u]; decide),
      fun u _ h => absurd h (by rw [hsx u]; decide),
      fun e hfe hb _ hlen hoff => .inl (hown0 e hfe hb ⟨e.off, Nat.le_refl _, by omega, hoff⟩),
      fun h => absurd h (by rw [hX0]; decide),
      fun w hw => by simp [hq] at hw⟩
    -- the group's state: 0
    show (newest WG m).Val _
    unfold newest
    rw [hwgz]
    have e : wgv (upd G0 0 (gO rM { ph := .pre }) 0).2 (upd G0 0 (gO rM { ph := .pre }) 1).2
        (upd G0 0 (gO rM { ph := .pre }) 2).2 = 0 := by
      unfold wgv; rw [hX0]; rfl
    rw [e]; exact hwgv

/-! ## Field pointers and the threads -/

/-- A field pointer of the `Tally` (block 0) is formed (`ptrProject`, MM-3). -/
theorem proj {m : Mem} (hb : BlkOk m) {k : Nat} (hk : k ≤ 24) :
    (ptrProject bPtr (·.add k)).run m = pure (bPtr.add k, m) := by
  obtain ⟨blk, hb, -, hsz, -⟩ := hb
  exact ptrProject_block_run hb rfl (by decide) (by simp [bPtr, hsz]; omega)

/-- The `Tally` is block 0, from the protocol's invariant. -/
theorem blk_inv {G : ThreadId → Gh} {m : Mem} (hi : proto.inv G m) : BlkOk m := by
  obtain ⟨rX, -, hu⟩ := hi; exact hu.blk

/-- A field pointer of the `Tally` from the protocol's invariant. -/
theorem projI {G : ThreadId → Gh} {m : Mem} (hi : proto.inv G m) {k : Nat} (hk : k ≤ 24) :
    (ptrProject bPtr (·.add k)).run m = pure (bPtr.add k, m) :=
  proj (blk_inv hi) hk

/-- The invariant at a stop of a live thread `t`. -/
theorem inv_cur {G : ThreadId → Gh} {m : Mem} (t : ThreadId) (hi : proto.inv G m)
    (hph : (G t).1.ph ≠ .gone) : proto.inv G { m with current := t } := by
  obtain ⟨-, -, -, h⟩ := fitsL.cur t hi hph
  exact h

/-- `main` spawned every thread. -/
theorem spawners {Y : ThreadId → X} {m : Mem} (h : Shape Y m) : ∀ r ∈ m.threads, r.spawner = 0 :=
  spawners_of_getElem fun i hi => by
    obtain ⟨h0, -, -, ⟨h1, -⟩ | ⟨h2, -, h1, -⟩ | ⟨h3, -, -, -, h1, h2⟩⟩ := h
    · obtain rfl : i = 0 := by omega
      rw [Array.getElem?_eq_getElem hi] at h0; rw [Option.some.inj h0]
    · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · rw [Array.getElem?_eq_getElem hi] at h0; rw [Option.some.inj h0]
      · rw [Array.getElem?_eq_getElem hi] at h1; rw [Option.some.inj h1]
    · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
      · rw [Array.getElem?_eq_getElem hi] at h0; rw [Option.some.inj h0]
      · rw [Array.getElem?_eq_getElem hi] at h1; rw [Option.some.inj h1]
      · rw [Array.getElem?_eq_getElem hi] at h2; rw [Option.some.inj h2]

/-- **`main`'s free of the `Tally`**, which races with no access (`hfr`: every other thread is
joined, `freeRaces_of_joined`). -/
theorem wp_free {G : ThreadId → Gh} {m : Mem} {n : Nat} (hb : BlkOk m)
    (hfr : ∀ b k, m.freeRaces b k = false)
    {Q : Unit → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ m', m'.threads = m.threads → Q () G m' n) :
    proto.WP 0 (ConcM.liftMem (free bPtr) : ConcM Tgt Unit) Q G m n := by
  obtain ⟨blk, hblk, hl, -, hk⟩ := hb
  refine WP.liftMem (fun e he => (free_noErr hblk hl (hfr _ _) (by rw [hk]; nofun) e
    he).elim) fun _ m' hf => ?_
  obtain ⟨b', blk', -, -, rfl⟩ := free_ok hf
  exact ⟨rfl, h _ rfl⟩

end Threadsync.WG
