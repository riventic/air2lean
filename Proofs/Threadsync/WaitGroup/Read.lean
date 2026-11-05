import Proofs.Threadsync.WaitGroup.Wait
import ZigLean.ResultRun
import ZigLean.Sep.Full.LockSteps

/-!
# `main`'s read of the whole `Tally` in `waitGroup`'s protocol

After its wait (`rd`), `main` reads the whole `Tally` (`wp_read`): every other thread is `gone` for
the lock (`gone6`), so the read may span the group's state, the event, the mutex and the counter
(`FLock.Inv.loadMem`). It races with no write: each write access to the `Tally` is below `main`'s
clock, a finished task's finish clock or an `is_set` write, which are all below `main`'s clock
(`U.attr`, `U.done`). The counter holds the stores of both tasks: the read's `n` is 2.
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Full Zig.Full.FAssn

namespace Threadsync.WG

/-- `main` after its wait (`6 ≤ rank`): every other thread is `gone` for the lock. -/
theorem gone6 {G : ThreadId → Gh} {rX : Res} {m : Mem} (hu : U G rX m)
    (h6 : 6 ≤ (G 0).2.ph.rank) (u : ThreadId) (h0 : u ≠ 0) : (G u).1.ph = .gone := by
  obtain ⟨h1, h2, -⟩ := hu.done h6
  by_cases h3 : 3 ≤ u
  · exact hu.out3 u h3
  · rcases (by unfold ThreadId at *; omega : u = 1 ∨ u = 2) with rfl | rfl
    · exact hu.lg 1 h1
    · exact hu.lg 2 h2

/-- `main` after its wait: three threads. -/
theorem size6 {G : ThreadId → Gh} {rX : Res} {m : Mem} (hu : U G rX m)
    (h6 : 6 ≤ (G 0).2.ph.rank) : m.threads.size = 3 := by
  obtain ⟨-, -, -, ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨h, -⟩⟩ := hu.shape
  · change (G 0).2.ph.rank ≤ 1 at h; omega
  · change (G 0).2.ph = .sp1 at h; rw [h] at h6; exact absurd h6 (by decide)
  · exact h

/-- `main` after its wait is the only thread of the words' live sets. -/
theorem live6 {G : ThreadId → Gh} {rX : Res} {m : Mem} (hu : U G rX m)
    (h6 : 6 ≤ (G 0).2.ph.rank) (u : ThreadId) (hu3 : u < m.threads.size) (hl : ELive (G u)) :
    u = 0 := by
  rw [size6 hu h6] at hu3
  obtain ⟨h1, h2, -, -, -, hsx⟩ := hu.done h6
  have hfd : ∀ v, (v = 1 ∨ v = 2) → ¬ ELive (G v) := by
    rintro v hv (hw | ⟨hx, hS⟩)
    · have : (G v).2.ph.fd = true := by rcases hv with rfl | rfl; exact h1; exact h2
      unfold WLive at hw; rw [this] at hw; cases hw
    · rcases hx with hx | ⟨hx, hst⟩
      · have := (hu.wk0 v hx).1; rcases hv with rfl | rfl <;> cases this
      · rcases hsx v hx with h | h
        · exact hS h
        · rw [h] at hst; cases hst
  rcases (by unfold ThreadId at *; omega : u = 0 ∨ u = 1 ∨ u = 2) with rfl | rfl | rfl
  · rfl
  · exact absurd hl (hfd 1 (.inl rfl))
  · exact absurd hl (hfd 2 (.inr rfl))

/-- The `Tally`'s decode, from the values of its four words. -/
theorem tally_decode {bs : Array Byte} {a : BitVec 64} {b c d : BitVec 32}
    (ha : (intOfBytes 64 (bs.extract 0 8)).run = some (.ok a))
    (hb : (intOfBytes 32 (bs.extract 8 12)).run = some (.ok b))
    (hc : (intOfBytes 32 (bs.extract 16 20)).run = some (.ok c))
    (hd : (intOfBytes 32 (bs.extract 20 24)).run = some (.ok d)) :
    ∃ v : Tally, Enc.decode bs = pure v ∧ v.n = d := by
  refine ⟨?v, ?hd, ?hn⟩
  case hd =>
    have ha' := Result.eq_pure_of_run ha
    have hb' := Result.eq_pure_of_run hb
    have hc' := Result.eq_pure_of_run hc
    have hd' := Result.eq_pure_of_run hd
    simp only [Enc.decode, Enc.decodeAt, Enc.size, Array.extract_extract, intSize,
      show alignUp ((64 + 7) / 8) (intAlign 64) = 8 from rfl,
      show alignUp ((32 + 7) / 8) (intAlign 32) = 4 from rfl]
    rw [show Min.min 8 (Min.min 8 16) = 8 from rfl,
      show Min.min (8 + 4) (Min.min (8 + 4) (Min.min (8 + 4) (Min.min (8 + 4) 16))) = 12 from rfl,
      show Min.min (16 + 4) (Min.min (16 + 4) (Min.min (16 + 4) (16 + 4))) = 20 from rfl,
      show (20 + 4 : Nat) = 24 from rfl, ha', hb', hc', hd']
    rfl
  case hn => rfl

/-- `main` after its wait: the `Tally` (block 0) decodes, and its counter is 2 (both tasks
stored it). -/
theorem tally_val {G : ThreadId → Gh} {rX : Res} {m : Mem} (hL : L.Inv G rX m) (hu : U G rX m)
    (h6 : 6 ≤ (G 0).2.ph.rank) (hm : (G 0).1.ph = .out) {blk : Block}
    (hb : m.blocks[0]? = some blk) :
    ∃ v : Tally, Enc.decode (blk.bytes.extract 0 (0 + Enc.size Tally)) = pure v ∧ v.n = 2 := by
  obtain ⟨a, ha⟩ := hu.wg.val
  rw [Word.holds_bytes (W := WG) hb] at ha
  obtain ⟨b, hb'⟩ := hu.ev.val
  rw [Word.holds_bytes (W := EV) hb] at hb'
  obtain ⟨w, -, hU, -⟩ := hL.w.word
  unfold LockWord.U32 curBytes at hU
  rw [show L.b = 0 from rfl, show L.o = 16 from rfl, hb] at hU
  simp only [Option.map_some, Option.getD_some] at hU
  -- the counter: the free lock's resource
  have hfree : L.Free G := fun u => by
    by_cases h0 : u = 0
    · subst h0; show (G 0).1.ph ≠ .holds; rw [hm]; decide
    · show (G u).1.ph ≠ .holds; rw [gone6 hu h6 u h0]; decide
  obtain ⟨rL, ho, hLoff, -, hF, -⟩ := hL.rest
  obtain ⟨hR, -⟩ := hF hfree
  obtain ⟨h1, h2, -⟩ := hu.done h6
  have hc2 : (G 1).2.cnt + (G 2).2.cnt = 2 := by
    unfold X.cnt; rw [if_pos (by unfold Ph.fd at h1; revert h1; cases (G 1).2.ph <;> simp [Ph.stored]),
      if_pos (by unfold Ph.fd at h2; revert h2; cases (G 2).2.ph <;> simp [Ph.stored])]
  change up (pts (bPtr.add 20) 4 (BitVec.ofNat 32 ((G 1).2.cnt + (G 2).2.cnt))) rL at hR
  rw [hc2] at hR
  obtain ⟨A, S, K, bs, ⟨-, hbs, hdv, -⟩, hbytes⟩ := FTotalTriple.up_pts_iff_bytesAt.mp hR
  -- a byte of the counter is the lock resource's in the complete rest (not the word's)
  have hsub : ∀ l fc, rL.heap l = some fc → ∃ fc',
      (rsum (L.wordR m) (rsum rL rX)).heap l = some fc' ∧ fc'.cell.norm = fc.cell.norm := by
    intro l fc h
    have hnw : ¬ L.In l := fun hin => by
      obtain ⟨b', x⟩ := l
      obtain ⟨h1, h2, h3⟩ := hin
      have := hLoff x h2 h3
      simp only at h1; subst h1
      simp [FHeap.erase, h] at this
    refine ⟨fc, ?_, rfl⟩
    simp only [FHeap.union_apply, LockWord.wordR, cellsAt_none hnw, Option.none_or, h,
      Option.some_or]
  obtain ⟨blk', hb'', hx⟩ := ho.rest_bytes hbytes rfl hsub (by rw [hbs]; decide)
  rw [hb] at hb''; cases hb''
  have hd : (intOfBytes 32 (blk.bytes.extract 20 24)).run = some (.ok (BitVec.ofNat 32 2)) := by
    have e : blk.bytes.extract 20 24 = bs := by
      rw [← hx, hbs]; rfl
    rw [e]; exact Result.run_of_eq_pure hdv
  have e : ∀ i j, (blk.bytes.extract 0 (0 + Enc.size Tally)).extract i j =
      blk.bytes.extract i (min j 24) := fun i j => by
    rw [Array.extract_extract]; simp [Enc.size]
  exact tally_decode (a := a) (b := b) (c := BitVec.ofNat 32 w)
    (by rw [e]; exact ha) (by rw [e]; exact hb') (by rw [e]; exact hU) (by rw [e]; exact hd)

/-- **`U` after `main`'s read** at the same places: the record is a read by `main`, the only
thread of the words' live sets (`live6`), and adds no write access. -/
theorem U_read {G : ThreadId → Gh} {rX : Res} {m : Mem} {o n : Nat} (hu : U G rX m)
    (h6 : 6 ≤ (G 0).2.ph.rank) (hc : m.current = 0) (hcs : m.clocks.size = m.threads.size) :
    U G rX (m.recordAt 0 o n .read) := by
  have h0 : 0 < m.clocks.size := by rw [hcs, size6 hu h6]; decide
  have hclk := Conc.recordAt_le m 0 o n .read
  obtain ⟨hwG, hhG⟩ := hu.wg.record_sole_native (b := 0) (o := o) (len := n) (k := .read) hc h0
    (fun u hu3 h => live6 hu h6 u hu3 (.inl h)) rfl
  obtain ⟨hwE, hhE⟩ := hu.ev.record_sole_native (b := 0) (o := o) (len := n) (k := .read) hc h0
    (fun u hu3 h => live6 hu h6 u hu3 h) rfl
  refine hu.congrX (fun _ => rfl) hhG hhE hclk rfl (hu.rest.congr fun _ _ => rfl) hu.blk hwG hwE
    (hu.einv.frame (t := 0) (fun _ _ => rfl) rfl rfl hhE rfl hclk (Nat.le_refl _) id id
      (hu.einv.fresh.of_eq rfl (Nat.le_refl _)))
    (fun u h => hu.lg u h) hu.out3 (fun e he _ hk => ?_) hu.q
  simp only [Mem.recordAt, Array.mem_push] at he
  rcases he with he | rfl
  · exact .inl ⟨e, he, .refl e⟩
  · simp [AccessKind.isWrite] at hk

/-- `main` after its wait, out of the lock's code: no thread holds the mutex. -/
theorem free6 {G : ThreadId → Gh} {rX : Res} {m : Mem} (hu : U G rX m)
    (h6 : 6 ≤ (G 0).2.ph.rank) (hm : (G 0).1.ph = .out) : L.Free G := fun u => by
  by_cases h0 : u = 0
  · subst h0; show (G 0).1.ph ≠ .holds; rw [hm]; decide
  · show (G u).1.ph ≠ .holds; rw [gone6 hu h6 u h0]; decide

/-- The `Tally`'s bytes are live (`BlkOk`). -/
theorem heap0 {m : Mem} (hb : BlkOk m) {x : Nat} (hx : x < 24) : m.heap (0, x) ≠ none := by
  obtain ⟨blk, h1, hl, hsz, hk⟩ := hb
  rw [Mem.heap_of h1, dif_pos ⟨hl, by omega, by rw [hk]; exact Nat.zero_le _⟩]
  simp

/-- **`main`'s read of the whole `Tally`** at `rd` (`FLock.Fits.wp_loadWith`, `FLock.Inv.loadMem`):
it reads the `Tally` with the counter 2 and goes to `rdd`. Every other thread is `gone` for the
lock; the read races with no write (`U.attr`: each write access is below `main`'s clock, a
finished task's finish clock or an `is_set` write, all below `main`'s clock by `U.done`). -/
theorem wp_read {G : ThreadId → Gh} {m : Mem} {d : Nat} {rM : Res} {w : Bool}
    (hi : proto.inv (upd G 0 (gO rM { ph := .rd, wk := w })) m) (hc : m.current = 0)
    {Q : Tally → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ v m', v.n = 2 → m'.current = 0 →
      proto.inv (upd G 0 (gO rM { ph := .rdd, wk := w })) m' → Q v G m' d) :
    proto.WP 0 (ConcM.liftMem (load Tally 8 bPtr) : ConcM Tgt Tally) Q G m d := by
  have h10 : (1 : ThreadId) ≠ 0 := by decide
  have h20 : (2 : ThreadId) ≠ 0 := by decide
  obtain ⟨rX, hL, hu⟩ := id hi
  have hg0 : upd G 0 (gO rM { ph := .rd, wk := w }) 0 = gO rM { ph := .rd, wk := w } :=
    upd_self _ _ _
  have h6 : 6 ≤ (upd G 0 (gO rM { ph := .rd, wk := w }) 0).2.ph.rank := by
    rw [hg0]; show 6 ≤ Ph.rd.rank; decide
  have hm : (upd G 0 (gO rM { ph := .rd, wk := w }) 0).1.ph = .out := by rw [hg0]; rfl
  obtain ⟨blk, hb, hl, hsz, hk⟩ := hu.blk
  obtain ⟨v, hdec, hv2⟩ := tally_val hL hu h6 hm hb
  have e24 : bPtr.off.toNat + Enc.size Tally = 24 := rfl
  refine fitsL.wp_loadWith (b := 0) (o := 0) (n := Enc.size Tally) (v := v)
    (fun rX' hL' hU' _ => ?_) (fun rX' hU' _ _ hcs => U_read hU' h6 hc hcs) hi hc
    (by rw [hg0]; show LPh.out ≠ LPh.gone; decide) fun m' hc' _ hi' => h v m' hv2 hc' ?_
  · -- the load: the bytes of the complete rest, no race
    obtain ⟨blk', hb', -, -, ha, hK, -⟩ := hU'.wg.blk
    change m.blocks[0]? = _ at hb'
    rw [hb] at hb'; cases hb'
    refine hL'.loadMem (p := bPtr) (blk := blk) rfl (Int.le_refl _) (by decide) hb hl
      (by rw [hsz]; exact Nat.le_of_eq e24) (by rw [hk]; exact Nat.zero_le _) hdec ha hK
      (fun rL hF _ _ _ x _ hx => ?_) hc (by rw [hg0]; show LPh.out ≠ LPh.gone; decide)
      (fun u _ h0 => gone6 hU' h6 u h0) ?_
    · rw [e24] at hx
      by_cases h16 : x < 16
      · obtain ⟨rB, -, -, rfl⟩ := hU'.rest
        refine heap_ne_r (heap_ne_r (heap_ne_l ?_))
        rw [cellsAt_of (W := BoxW) ⟨rfl, h16⟩]
        simpa using heap0 hU'.blk hx
      by_cases h20' : x < 20
      · exact heap_ne_l (L.wordR_some hL'.w.blk ⟨rfl, by show 16 ≤ x; omega, by show x < 20; omega⟩)
      · have hR := hF (free6 hU' h6 hm)
        change up (pts (bPtr.add 20) 4 _) rL at hR
        obtain ⟨_, _, _, bs, ⟨-, hbs, -, -⟩, hbytes⟩ := FTotalTriple.up_pts_iff_bytesAt.mp hR
        refine heap_ne_r (heap_ne_l ((up_bytesAt_some hbytes rfl (0, x)).mpr ⟨rfl, ?_, ?_⟩))
        · show 20 ≤ x; omega
        · rw [hbs]; show x < 20 + 4; omega
    · -- no race: each write access is below `main`'s clock
      refine noRace_of_pos fun e he hb0 hl0 _ h2 => ?_
      cases hw : e.kind.isWrite
      · exact .inr (by unfold racePair; rw [hw]; rfl)
      · left; rw [hc]
        obtain ⟨d1, d2, c1, c2, cj, -⟩ := hU'.done h6
        rcases hU'.attr e he hb0 hw hl0 (by rw [e24] at h2; exact h2) with
          h' | ⟨u, hu12, h'⟩ | ⟨j, hj, hs, h'⟩
        · exact h'
        · rcases hu12 with rfl | rfl
          · unfold bnd at h'; rw [if_pos d1] at h'; exact VClock.le_trans h' c1
          · unfold bnd at h'; rw [if_pos d2] at h'; exact VClock.le_trans h' c2
        · exact VClock.le_trans h' (cj j hj hs)
  · -- `main` to `rdd`
    refine inv_main0 hi' rfl rfl rfl rfl rfl (by simp [wgv, Ph.wa]) rfl
      (fun h => absurd h (by show ¬ Ph.rd.rank ≤ 1; decide)) (fun h => by cases h)
      (fun _ => ⟨by show 3 ≤ Ph.rdd.rank; decide, by show Ph.rd = Ph.j1 ↔ Ph.rdd = Ph.j1; decide⟩)
      fun _ => ?_
    obtain ⟨rX'', -, hu''⟩ := id hi'
    obtain ⟨a, b, c, d', f, k⟩ := hu''.done h6
    rw [upd_ne _ _ h10] at a c
    rw [upd_ne _ _ h20] at b d'
    refine ⟨a, b, c, d', f, fun u hu0 hx => ?_⟩
    have := k u (by rw [upd_ne _ _ hu0]; exact hx)
    rwa [upd_ne _ _ hu0] at this

end Threadsync.WG
