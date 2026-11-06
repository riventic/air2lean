import Proofs.Sync.Mailbox.Steps

/-!
# `main`'s side of the mailbox's protocol

The steps of `main` (`mailMain`, `Proofs/Sync/Mailbox/Code.lean`) that its walk uses, besides its
wait (`wp_waitM`, `Proofs/Sync/Mailbox/Steps.lean`), for every mutex value of the semaphore
(`Cfg`), with the ports of `handoff`'s (`Proofs/Handoff/{Start,Ops,Steps}.lean`):

- **The start** (`inv_of_box`): `main` owns the mailbox after its stores. It gives the condition's
  two words and the padding with the block's extent to the protocol's rest (`Rest`), the count and
  the mutex's word to the lock (`FLock.Inv.make`), and keeps the plain mode `rM` and the message
  `rc` (`Msg 0`). The condition and the semaphore start with every thread out of their code
  (`FCond.Inv.start`, `FSem.Inv.start`).
- **The spawn** (`inv_spawn`): `main` copies its plain mode (`EUpd.plain_split`) and hands it with
  the message to the producer (`proto.init`), to its wait (`wt`). The semaphore's invariant and the
  epoch's `WordHB` carry over the fork: no thread holds the mutex before it, and what happened
  before `main` happened before both threads after it.
- **The message** (`wp_loadA`, `wp_loadB`): `main`'s loads of `a` and `b` on its own part after its
  take (`FCond.wp_liftPart`): 3 and 4.
- **The join and the free** (`inv_joins`, `wp_join`, `wp_free`), and the threads (`inv_cur`,
  `spawners`, `qkid`).
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Full Zig.Full.FAssn

namespace Sync.Mailbox

variable {K : Cfg}

theorem empty_disj (h : FHeap) : FHeap.Disjoint FHeap.empty h := (FHeap.disjoint_empty h).symm

/-! ## `main`'s start -/

theorem heap_ne_l {a b : Res} {l : Zig.Loc} (h : a.heap l ≠ none) : (rsum a b).heap l ≠ none := by
  simp only [FHeap.union_apply, ne_eq, Option.or_eq_none_iff, not_and]
  intro h'; exact absurd h' h

theorem heap_ne_r {a b : Res} {l : Zig.Loc} (h : b.heap l ≠ none) : (rsum a b).heap l ≠ none := by
  simp only [FHeap.union_apply, ne_eq, Option.or_eq_none_iff, not_and]
  intro _; exact h

/-- A shared word at the start: no atomic location, each access to it happened before every
thread, and the value 0, written at no clock. -/
theorem word_init {W : Word 32 4} {m : Mem} {blk : Block} (hW : W.b = 0)
    (h4 : (blk.addr + W.o) % 4 = 0) (hsz : W.o + 4 ≤ blk.bytes.size) (hb : m.blocks[0]? = some blk)
    (hl : blk.live = true) (hk : blk.kind = .stack) (hat : m.atomics = #[])
    (hv : (intOfBytes 32 (blk.bytes.extract W.o (W.o + 4))).run = some (.ok 0))
    (hfp : ∀ e ∈ m.footprint, W.Hits e → AllLe m e.clock) :
    W.Ok m ∧ (W.hist m).size = 1 ∧ (W.hist m)[0]!.Val (0 : BitVec 32) ∧
      ∀ c, VClock.le (W.hist m)[0]!.clock c = true := by
  have hno : ∀ i l, ¬ W.Loc m i l := fun i l hl => by
    have := (Word.loc_get hl).1; rw [hat] at this; simp at this
  have hu : W.Holds m 0 := by unfold Word.Holds curBytes; rw [hW, hb]; exact hv
  refine ⟨⟨⟨blk, by rw [hW]; exact hb, hl, hsz, h4, by rw [hk]; simp⟩,
    fun l hl' => by rw [hat] at hl'; simp at hl', fun i l h => absurd h (hno i l),
    fun e he hh => .inr ((hfp e he hh).on _), ⟨0, hu⟩, fun i l h => absurd h (hno i l)⟩, ?_, ?_, ?_⟩
  · rw [Word.hist_none hno]; rfl
  · rw [Word.hist_none hno]; exact hu
  · intro c; rw [Word.hist_none hno]; exact VClock.le_default c

/-- The bytes `a .. c` of `bs` at `a` are the bytes `a .. b` and `b .. c`. -/
theorem split_at {bs : Array Byte} {A S a b c : Nat} {r : Res}
    (h : up (bytesAt (cPtr.add a) A S .stack (bs.extract a c)) r) (hab : a ≤ b) (hbc : b ≤ c)
    (hc : c ≤ bs.size) :
    (up (bytesAt (cPtr.add a) A S .stack (bs.extract a b)) ⋆
      up (bytesAt (cPtr.add b) A S .stack (bs.extract b c))) r := by
  have hsz : (bs.extract a c).size = c - a := by simp; omega
  have := up_sep ⟨bytesAt_split h.1 (k := b - a) (by omega), h.2⟩
  have e1 : (bs.extract a c).extract 0 (b - a) = bs.extract a b := by
    rw [Array.extract_extract]; congr 1 <;> omega
  have e2 : (bs.extract a c).extract (b - a) (bs.extract a c).size = bs.extract b c := by
    rw [Array.extract_extract, hsz]; congr 1 <;> omega
  have e3 : (cPtr.add (a : Int)).add ((b - a : Nat) : Int) = cPtr.add (b : Int) := by
    rw [Ptr.add_add]; congr 1; omega
  rwa [e1, e2, e3] at this

/-- **The mailbox's bytes after `main`'s stores**: the count, the mutex, the condition's words,
the padding, `a` and `b`. -/
theorem box_split {r : Res} {A : Nat} {bs : Array Byte} (hs : bs.size = 32)
    (h : up (bytesAt cPtr A 32 .stack bs) r) :
    (up (bytesAt cPtr A 32 .stack (bs.extract 0 8)) ⋆
      (up (bytesAt (cPtr.add 8) A 32 .stack (bs.extract 8 12)) ⋆
      (up (bytesAt (cPtr.add 12) A 32 .stack (bs.extract 12 20)) ⋆
      (up (bytesAt (cPtr.add 20) A 32 .stack (bs.extract 20 24)) ⋆
      (up (bytesAt (cPtr.add 24) A 32 .stack (bs.extract 24 28)) ⋆
       up (bytesAt (cPtr.add 28) A 32 .stack (bs.extract 28 32))))))) r := by
  have h0 := up_sep ⟨bytesAt_split h.1 (k := 8) (by omega), h.2⟩
  rw [hs] at h0
  refine sep_mono_right (fun _ hr => ?_) h0
  refine sep_mono_right (fun _ hr => ?_) (split_at hr (a := 8) (c := 32) (b := 12) (by omega) (by omega) (by omega))
  refine sep_mono_right (fun _ hr => ?_) (split_at hr (a := 12) (c := 32) (b := 20) (by omega) (by omega) (by omega))
  refine sep_mono_right (fun _ hr => ?_) (split_at hr (a := 20) (c := 32) (b := 24) (by omega) (by omega) (by omega))
  exact split_at hr (a := 24) (c := 32) (b := 28) (by omega) (by omega) (by omega)

theorem sep_box {I W B P Ma Mb b pl : FAssn} {r : Res}
    (h : (((I ⋆ (W ⋆ (B ⋆ (P ⋆ (Ma ⋆ Mb))))) ⋆ b) ⋆ pl) r) :
    (((pl ⋆ (Ma ⋆ Mb)) ⋆ (I ⋆ W)) ⋆ (B ⋆ (P ⋆ b))) r := by
  have e : (((I ⋆ (W ⋆ (B ⋆ (P ⋆ (Ma ⋆ Mb))))) ⋆ b) ⋆ pl) =
      (((pl ⋆ (Ma ⋆ Mb)) ⋆ (I ⋆ W)) ⋆ (B ⋆ (P ⋆ b))) := by
    ac_rfl
  rw [e] at h; exact h

/-- Bytes on the stack that encode `v`, at an aligned address: `pts`. -/
theorem pts_of {T : Type} [Enc T] [LawfulEnc T] {p : Ptr} {A a : Nat} {v : T} {r : Res}
    (h : up (bytesAt p A 32 .stack (Enc.encode v)) r) (ha : (A + p.off.toNat) % a = 0) :
    up (pts p a v) r :=
  ⟨⟨A, 32, .stack, Enc.encode v, ha, LawfulEnc.size_encode _, LawfulEnc.decode_encode _, h.1,
    by decide⟩, h.2.1, h.2.2⟩

/-- **Before the spawn**: `main` owns the mailbox after its stores (the bytes `bs`: the
semaphore with no permit, `a = 0`, `b = 0`), with its extent, and the plain mode. It gives the
condition's words and the padding with the extent to the protocol's rest (`Rest`), the count
and the mutex's word to the lock (`FLock.Inv.make`), and keeps the plain mode `rM` and the
message `rc`. The condition and the semaphore start with every thread out of their code
(`FCond.Inv.start`, `FSem.Inv.start`). -/
theorem inv_of_box {m : Mem} {r : Res} {A : Nat} {bs : Array Byte}
    (ho : FOwned (upd (fun _ => rnil) 0 r) rnil m)
    (hF : ((up (bytesAt cPtr A 32 .stack bs) ⋆ bext 0 32 .stack) ⋆ plain) r)
    (hs : bs.size = 32)
    (hC : bs.extract 0 8 = Enc.encode (0 : BitVec 64))
    (hW : bs.extract 8 12 = Enc.encode (0 : BitVec 32))
    (hS : bs.extract 12 16 = Enc.encode (0 : BitVec 32))
    (hE : bs.extract 16 20 = Enc.encode (0 : BitVec 32))
    (ha : bs.extract 24 28 = Enc.encode (0 : BitVec 32))
    (hb : bs.extract 28 32 = Enc.encode (0 : BitVec 32))
    (hA : A % 8 = 0) (hth : m.threads = #[{ spawner := 0, joined := true }])
    (hat : m.atomics = #[]) (hq : m.waiters = #[]) :
    ∃ rM rc, rM.Plain ∧ Msg 0 rc ∧ FHeap.Disjoint rM.heap rc.heap ∧
      (proto K).inv (upd G0 0 (gO (rsum rM rc) { ph := .pre })) m := by
  have h1 : m.threads.size = 1 := by rw [hth]; rfl
  have ht : 0 < m.threads.size := by rw [h1]; decide
  -- the block: block 0, at `A`, 32 bytes on the stack, its bytes `bs`
  obtain ⟨blk, hblk, hl, hAd, hS32, hK, hxB⟩ :=
    ho.bytesOf ht (rfl : cPtr.block = some 0) (by rw [hs]; decide)
      (by rw [upd_self]; exact hF)
  rw [show cPtr.off.toNat = 0 from rfl, hs, Nat.zero_add] at hxB
  have hbyte : ∀ o e, o ≤ e → e ≤ 32 → blk.bytes.extract o e = bs.extract o e := fun o e h1 h2 => by
    rw [← hxB, Array.extract_extract]; congr 1 <;> omega
  -- the pieces
  obtain ⟨_, _, hd, rfl, ⟨_, _, hdK, rfl, ⟨rM, rc, hdMc, rfl, hpM, hMsg⟩, ⟨rI, rW, hdIW, rfl, hI, hW₁⟩⟩,
    ⟨rB, rP, hdB, rfl, hB, hP⟩⟩ :=
    sep_box (sep_mono_left (fun _ h => sep_mono_left (fun _ h => box_split hs h) h) hF)
  refine ⟨rM, rc, Res.plain_of hpM, ?_, hdMc, ?_⟩
  · rw [ha, hb] at hMsg
    rw [msg0]
    exact sep_mono (fun _ h => pts_of h (by simp [aPtr, cPtr, Ptr.add]; omega))
      (fun _ h => pts_of h (by simp [bPtr, cPtr, Ptr.add]; omega)) hMsg
  rw [hC] at hI; rw [hW] at hW₁
  have hs4 : (Enc.encode (0 : BitVec 32)).size = 4 := LawfulEnc.size_encode _
  have hs8 : (Enc.encode (0 : BitVec 64)).size = 8 := LawfulEnc.size_encode _
  -- each access to a byte of `main`'s part happened before `main`
  have hown0 : ∀ e ∈ m.footprint, e.Touches (upd (fun _ => rnil) 0
      (rsum (rsum (rsum rM rc) (rsum rI rW)) (rsum rB rP)) 0).owned → AllLe m e.clock :=
    fun e he htc => allLe_of_one h1 (ho.owns 0 ht e he (.inl htc))
  have hBin : ∀ l, rB.heap l ≠ none ↔ BoxW l := fun l => by
    rw [up_bytesAt_some hB rfl l, show (cPtr.add 12).off.toNat = 12 from rfl]
    simp only [Array.size_extract, hs]
    show _ ↔ l.1 = 0 ∧ 12 ≤ l.2 ∧ l.2 < 20
    constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨h1, by omega, by omega⟩
  have hPoff : ∀ l, BoxW l → rP.heap l = none := fun l hl =>
    (hdB l).resolve_left ((hBin l).mpr hl)
  -- the condition's two words
  have hfpW : ∀ W : Word 32 4, W = WS ∨ W = WE → ∀ e ∈ m.footprint, W.Hits e → AllLe m e.clock :=
    fun W hW' e he hh => hown0 e he (Word.touches_of hh fun x a b => by
      have hb0 : W.b = 0 := by rcases hW' with rfl | rfl <;> rfl
      rw [hb0, upd_self]
      exact Res.owned_of_heap (heap_ne_r (heap_ne_l ((hBin _).mpr (two_box hW' _ ⟨hb0.symm, a, b⟩)))))
  obtain ⟨hwsOk, hwsz, hwsv, -⟩ := word_init (W := WS) rfl
    (by show (blk.addr + 12) % 4 = 0; rw [hAd]; omega) (by show 12 + 4 ≤ _; rw [hS32]; omega)
    hblk hl hK hat
    (by show (intOfBytes 32 (blk.bytes.extract 12 16)).run = _
        rw [hbyte 12 16 (by omega) (by omega), hS]; exact intOfBytes_rmw 0)
    (hfpW _ (.inl rfl))
  obtain ⟨hweOk, hwez, hwev, hwel⟩ := word_init (W := WE) rfl
    (by show (blk.addr + 16) % 4 = 0; rw [hAd]; omega) (by show 16 + 4 ≤ _; rw [hS32]; omega)
    hblk hl hK hat
    (by show (intOfBytes 32 (blk.bytes.extract 16 20)).run = _
        rw [hbyte 16 20 (by omega) (by omega), hE]; exact intOfBytes_rmw 0)
    (hfpW _ (.inr rfl))
  -- the mutex holds 0
  have h0 : (L K).U32 m 0 := by
    show (intOfBytes 32 (curBytes m 0 8 4)).run = _
    unfold curBytes; rw [hblk]
    simp only [Option.map_some, Option.getD_some]
    rw [hbyte 8 12 (by omega) (by omega), hW]; exact intOfBytes_rmw 0
  -- the rest: `rB` and `rP`; read `rB` as the words' cells
  have ho' := ho.give (t := 0) ht (by rw [upd_self]) hd
  rw [upd_upd, rsum_rnil] at ho'
  have ho'' : FOwned (upd (fun _ => rnil) 0 (rsum (rsum rM rc) (rsum rI rW)))
      (rsum (cellsAt BoxW m) rP) m := by
    have hBoff : ∀ l, ¬ BoxW l → rB.heap l = none := fun l hb => by
      cases e : rB.heap l with
      | none => rfl
      | some _ => exact absurd ((hBin l).mp (by rw [e]; simp)) hb
    refine ho'.congrRestU (fun l => ?_) (fun l fc' hl => ?_) ?_ ?_
    · by_cases hb : BoxW l
      · obtain ⟨fc, hfc⟩ := Option.ne_none_iff_exists'.mp ((hBin l).mpr hb)
        have := ho'.rest_cell (l := l) (fc := fc) (by simp [FHeap.union_apply, hfc])
        simp only [FHeap.union_apply, cellsAt_of hb, hPoff l hb, hfc, Option.or_none]
        cases e : m.heap l with
        | none => rw [e] at this; cases this
        | some c => rw [e] at this; simpa [Cell.norm] using this
      · simp [FHeap.union_apply, cellsAt_none hb, hBoff l hb]
    · by_cases hb : BoxW l
      · simp only [FHeap.union_apply, cellsAt_of hb, hPoff l hb, Option.or_none,
          Option.map_eq_some_iff] at hl
        obtain ⟨c, -, rfl⟩ := hl
        exact .inl rfl
      · simp only [FHeap.union_apply, cellsAt_none hb, Option.none_or] at hl
        exact .inr ⟨fc', by simp [FHeap.union_apply, hBoff l hb, hl], rfl⟩
    · simp [cellsAt, hB.2.1, Know.none_union]
    · simp [cellsAt, hB.2.2]
  -- the ghost values at the start
  have hGu : ∀ u, u ≠ 0 → upd G0 0 (gO (rsum rM rc) { ph := .pre }) u = G0 u :=
    fun u h => upd_ne _ _ h
  have hX0 : (upd G0 0 (gO (rsum rM rc) { ph := .pre }) 0).2 = { ph := .pre } := by
    rw [upd_self]; rfl
  have hXu : ∀ u, u ≠ 0 → (upd G0 0 (gO (rsum rM rc) { ph := .pre }) u).2 = {} := fun u h => by
    rw [hGu u h]; rfl
  have hc : ∀ u, (upd G0 0 (gO (rsum rM rc) { ph := .pre }) u).2.c = .out ∧
      (upd G0 0 (gO (rsum rM rc) { ph := .pre }) u).2.s = .out := fun u => by
    by_cases h : u = 0
    · subst h; rw [hX0]; exact ⟨rfl, rfl⟩
    · rw [hXu u h]; exact ⟨rfl, rfl⟩
  have hp1 : (upd G0 0 (gO (rsum rM rc) { ph := .pre }) 1).2.ph = .none := by
    rw [hXu 1 (by decide)]
  refine ⟨rsum (cellsAt BoxW m) rP, FLock.Inv.make (t := 0) (rL := rI) (rW := rW) ho''
    rfl ht (fun u hu => ?_) (by rw [upd_self, upd_self]; rfl) (by rw [upd_self]; exact hdK) hdIW
    (fun l => ?_) hW₁.2.1 hW₁.2.2 (fun u => ?_) (fun u => ?_) ?_
    ⟨blk, hblk, hl, by rw [hS32]; show 8 + 4 ≤ 32; decide, by show (blk.addr + 8) % 4 = 0; rw [hAd]; omega,
      by rw [hK]; decide, by rw [hK]; simp [BlockKind.mappedLo]⟩
    h0 (by rw [hat]; simp) hq (allLe_of_one h1 (VClock.le_refl _)), ?_⟩
  · rw [upd_ne _ _ hu]
    unfold FLock.own; rw [hGu u hu]; split <;> simp [G0, FLock.prod, rnil_rsum]
  · rw [up_bytesAt_some hW₁ rfl l, show (cPtr.add 8).off.toNat = 8 from rfl, hs4]
    show _ ↔ l.1 = 0 ∧ 8 ≤ l.2 ∧ l.2 < 8 + 4
    rfl
  · by_cases hu : u = 0
    · subst hu; rw [upd_self]; exact .inl ⟨rfl, ht, rfl⟩
    · rw [hGu u hu]; exact .inr rfl
  · by_cases hu : u = 0
    · subst hu; rw [upd_self]; rfl
    · rw [hGu u hu]; rfl
  · -- the count 0, no free permit
    show R (fun u => (upd G0 0 (gO (rsum rM rc) { ph := .pre }) u).2) rI
    unfold R
    rw [pool_off (by simp [avail, hp1, Ph.posted]), pv_npost (by simp [hp1, Ph.posted])]
    exact sep_emp.mpr (pts_of hI (by simp [cPtr]; omega))
  · refine ⟨⟨by rw [hth]; rfl, .inl ⟨h1, by show (upd G0 0 _ 0).2.ph = .pre; rw [hX0], fun u hu => hXu u (by simp only [ThreadId] at *; omega)⟩⟩,
      ⟨rP, ⟨A, bs.extract 20 24, hA, by simp [hs], hP⟩, hPoff, rfl⟩, ⟨blk, hblk, hl, hS32, hK⟩,
      hwsOk, hweOk, FCond.Inv.start hwsz hwsv hwez hwev (fun u => (hc u).1) hq,
      FSem.Inv.start hwsz hwsv (fun u => (hc u).1) (fun u => (hc u).2),
      fun u h => absurd h (by rw [(hc u).2]; nofun),
      fun k hk => ?_,
      fun u _ _ h => absurd h (by rw [(hc u).1]; nofun),
      fun u _ _ _ _ h => absurd h (by rw [(hc u).1]; nofun),
      fun u _ _ _ h => absurd h (by rw [(hc u).1]; nofun),
      fun w hw => by simp [hq] at hw⟩
    rw [hwez] at hk
    obtain rfl : k = 0 := by omega
    exact .inr (.inr fun _ _ _ => hwel _)

/-- A fork by `t` moves no thread's clock back. -/
theorem clk_fork {cs : Array VClock} {t : ThreadId} (ht : t < cs.size) (u : ThreadId) :
    VClock.le (cs[u]!) (((cs.set! t (VClock.bump (cs[t]!) t)).push
      (VClock.bump (cs[t]!) t))[u]!) = true := by
  by_cases hu : u < cs.size
  · exact (Conc.fork_clocks ht).1 u hu
  · rw [getElem!_neg cs u hu]; exact VClock.le_default _

theorem inv_spawn {G : ThreadId → Gh} {m m' : Mem} {c : ThreadId} {rM rc : Res}
    (hp : rM.Plain) (hd : FHeap.Disjoint rM.heap rc.heap)
    (hi : (proto K).inv G m) (hg : G 0 = gO (rsum rM rc) { ph := .pre })
    (hf : (Thread.fork.run { m with current := 0 }).run = some (.ok (c, m'))) :
    c = 1 ∧ m'.current = 0 ∧ ∃ rp, plain rp ∧ FHeap.Disjoint rp.heap rc.heap ∧
      (proto K).inv (upd (upd G 1 (⟨.out, rsum rp rc, rnil⟩, { ph := .pr 0 })) 0
        (gO rM { ph := .wt })) m' := by
  obtain ⟨rX, hL, hU⟩ := hi
  obtain ⟨h00, ⟨hs1, -, hnone⟩ | ⟨-, -, -, h0, -⟩⟩ := hU.shape
  rotate_left
  · exfalso; apply h0; show (G 0).2.ph = _; rw [hg]; rfl
  have hcs : m.clocks.size = m.threads.size := hL.w.csize
  have hG1 : (G 1).2 = {} := hnone 1 (Nat.le_refl _)
  -- every thread is out of the condition's and the semaphore's code; none holds the mutex
  have hcG : ∀ u, (G u).2.c = .out ∧ (G u).2.s = .out := fun u => by
    by_cases e : u = 0
    · subst e; rw [hg]; exact ⟨rfl, rfl⟩
    · have h : (G u).2 = {} := hnone u (by simp only [ThreadId] at *; omega)
      rw [h]; exact ⟨rfl, rfl⟩
  have hnh : ∀ u, ((L K).ph (G u)).held ≠ true := fun u h => by
    by_cases e : u = 0
    · subst e; rw [hg] at h; cases h
    · have := (hL.w.live u (LPh.ne_gone_of_held h)).1
      rw [hs1] at this; exact e (by simp only [ThreadId] at *; omega)
  -- the plain mode, copied off `main`'s part
  have hpl : (rsum rM rc).Plain :=
    ⟨by simp only [Ghost.add_ac, ACell.add_frag]; have := hp.1; omega,
     by simp only [Ghost.add_ac, ACell.add_frag]; have := hp.2; omega⟩
  have hL₀ : (L K).Inv (upd G 0 (G 0)) rX { m with current := 0 } := by
    rw [upd_same]; exact hL.cur 0
  obtain ⟨r, ⟨r₁, rP, hdP, rfl, hr₁, hpP⟩, hL'⟩ := hL₀.eupdPart (proto K) rfl
    (by rw [hg]; exact fun h => nomatch h) (EUpd.plain_split (P := fun r => r = (L K).part (G 0))
      fun r hr => by rw [hr, hg]; exact hpl)
  have hr₁' : r₁ = rsum rM rc := by rw [hr₁, hg]; rfl
  subst hr₁'
  have hP0 : rP.heap = FHeap.empty := (plain_ghost hpP).1
  have hdPc : FHeap.Disjoint rP.heap rc.heap := by rw [hP0]; exact empty_disj _
  -- the fork
  obtain ⟨hc1, hm'⟩ := fork_eq hf
  have hc1 : c = 1 := hc1.trans hs1
  subst hc1
  obtain ⟨hwS, hhS⟩ := hU.ws.fork_native (t := 0) (gt := false) (by rw [hs1]; decide) hcs hf
  obtain ⟨hwE, hhE⟩ := hU.we.fork_native (t := 0) (gt := false) (by rw [hs1]; decide) hcs hf
  have hL'' := hL'.fork (t := 0) (c := 1) (g₁ := gO rM { ph := .wt })
    (g₀ := (⟨.out, rsum rP rc, rnil⟩, { ph := .pr 0 })) (by rw [upd_self, hg]; rfl) hf
    (by
      rw [upd_self, hg]
      show rsum (rsum rM rc) rP = rsum rM (rsum rP rc)
      rw [rsum_assoc, rsum_comm (a := rc) hdPc.symm])
    (fun l => by
      rcases hd l with h | h
      · exact .inl h
      · right; show (rP.heap ∪ rc.heap) l = none
        rw [FHeap.union_apply, hP0, h]; rfl)
    rfl rfl rfl rfl
    (fun r' hR => by
      show R _ r'
      have hR' : R (fun u => (upd G 0 ((L K).setPart (G 0) (rsum (rsum rM rc) rP)) u).2) r' := hR
      rw [R_avail (Y := fun u => (upd G 0 ((L K).setPart (G 0) (rsum (rsum rM rc) rP)) u).2)
        (by simp [avail, upd_self, upd0_1, hG1, hg, gO, Ph.posted, Ph.took])]
      exact hR')
  have he : upd (upd (upd G 0 ((L K).setPart (G 0) (rsum (rsum rM rc) rP))) 1
      (⟨.out, rsum rP rc, rnil⟩, { ph := .pr 0 })) 0 (gO rM { ph := .wt }) =
      upd (upd G 1 (⟨.out, rsum rP rc, rnil⟩, { ph := .pr 0 })) 0 (gO rM { ph := .wt }) := by
    rw [upd_comm G _ _ (by decide : (0 : ThreadId) ≠ 1), upd_upd]
  rw [he] at hL''
  refine ⟨rfl, by rw [hm'], rP, hpP, hdPc, rX, hL'', ?_⟩
  -- `U` after the spawn
  obtain ⟨G', hG'⟩ : ∃ G', G' = upd (upd G 1 (⟨.out, rsum rP rc, rnil⟩, { ph := .pr 0 })) 0
      (gO rM { ph := .wt }) := ⟨_, rfl⟩
  rw [← hG']
  have hX0 : (G' 0).2 = { ph := .wt } := by rw [hG', upd_self]; rfl
  have hX1 : (G' 1).2 = { ph := .pr 0 } := by rw [hG', upd0_1, upd_self]
  have hXu : ∀ u, 2 ≤ u → G' u = G u := fun u hu => by
    rw [hG', upd_ne _ _ (by simp only [ThreadId] at *; omega),
      upd_ne _ _ (by simp only [ThreadId] at *; omega)]
  have hc' : ∀ u, (G' u).2.c = .out ∧ (G' u).2.s = .out := fun u => by
    by_cases e0 : u = 0
    · subst e0; rw [hX0]; exact ⟨rfl, rfl⟩
    · by_cases e1 : u = 1
      · subst e1; rw [hX1]; exact ⟨rfl, rfl⟩
      · rw [hXu u (by simp only [ThreadId] at *; omega)]; exact hcG u
  have hclk : ∀ u : ThreadId, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true := fun u => by
    rw [hm']; exact clk_fork (cs := m.clocks) (t := 0) (by rw [hcs, hs1]; decide) u
  -- what happened before every thread before the spawn happened before both after it
  have hhb : ∀ c, (L K).HB G m c → (L K).HB G' m' c := by
    intro c hc
    subst hm'
    rcases hc with ⟨u, hu, -⟩ | hb | hlive
    · exact absurd hu (hnh u)
    · exact .inr (.inl hb)
    · refine .inr (.inr fun u hu _ => ?_)
      have h0 : VClock.le c (m.clocks[0]!) = true :=
        hlive 0 (by rw [hs1]; decide)
          (by show (L K).ph (G 0) ≠ .gone; rw [hg]; exact fun h => nomatch h)
      obtain ⟨hcl, hcn, -⟩ := Conc.fork_clocks (cs := m.clocks) (t := 0) (by rw [hcs, hs1]; decide)
      simp only [Array.size_push, hs1] at hu
      rcases (by omega : u = 0 ∨ u = 1) with rfl | rfl
      · exact VClock.le_trans h0 (hcl 0 (by rw [hcs, hs1]; decide))
      · have := hcn; rw [hcs, hs1] at this; exact VClock.le_trans h0 this
  have hI := hU.cinv.stay hhS hhE (by rw [hm']; rfl) (by rw [hm']; rfl) (by rw [hm'])
    (fun _ hw _ => by rw [hm'] at hw; exact hw)
    (fun _ _ h => by rw [hm']; exact h) (by rw [hm']; simp) hclk
  have hI' : C.Inv (L K) G' m' := by
    rw [hG']
    exact cinv_out (cinv_out hI (t := 1) (g := (⟨.out, rsum rP rc, rnil⟩, { ph := .pr 0 }))
      (hcG 1).1 rfl) (t := 0) (g := gO rM { ph := .wt }) (by rw [upd1_0]; exact (hcG 0).1) rfl
  have hS' : (S K).Inv G' m' :=
    { ex := fun u hu => absurd (hc' u).2 hu
      pst := fun u hu => by
        have h : ((G' u).2.s).isPst = true := hu
        rw [(hc' u).2] at h; cases h
      crit := fun u hu => by
        have h : ((G' u).2.c).crit = true := hu
        rw [(hc' u).1] at h; cases h
      wt := fun u hu => by
        have h : ((G' u).2.c).waits = true := hu
        rw [(hc' u).1] at h; cases h
      cp := fun u _ hu _ => by
        have h : ((G' u).2.c).crit = true := hu
        rw [(hc' u).1] at h; cases h
      tq := fun _ _ hk => by
        have h : (G' _).2.s = .wt := hk.1
        rw [(hc' _).2] at h; cases h
      hw := fun p h0 hp => by
        have hS0 : C.S.hist _ = C.S.hist m := hhS
        rw [hS0] at hp ⊢
        rcases hU.sinv.hw p h0 hp with h | h | ⟨u, hu, -⟩
        · exact .inl h
        · exact .inr (.inl (hhb _ h))
        · have h : (G u).2.s = .wt := hu.1
          rw [(hcG u).2] at h; cases h
      sp := fun u _ _ hu => by
        have h : (G' u).2.s = _ := hu
        rw [(hc' u).2] at h; cases h
      sb := fun u _ _ hu => by
        have h : (G' u).2.s = _ := hu
        rw [(hc' u).2] at h; cases h
      sa := fun u _ _ hu => by
        have h : (G' u).2.s = _ := hu
        rw [(hc' u).2] at h; cases h
      live := fun hc _ => absurd (pv_npost (by show (G' 1).2.ph.posted = false; rw [hX1]; rfl)) hc }
  have hq' : ∀ w ∈ m'.waiters, w.2 = (L K).key m' ∨ w.2 = WE.key m' := by rw [hm']; exact hU.q
  subst hm'
  refine ⟨⟨?_, .inr ⟨by simp [hs1], ?_, (by dsimp only; rw [hX0]; rfl),
      (by dsimp only; rw [hX0]; decide), (by dsimp only; rw [hX1]; rfl),
      (fun h => by dsimp only at h; rw [hX0] at h; cases h),
      (fun u hu => by dsimp only; rw [hXu u hu]; exact hnone u (by simp only [ThreadId] at *; omega))⟩⟩,
    hU.rest.congr fun _ _ => rfl, hU.blk, hwS, hwE, hI', hS',
    fun u h => absurd h (by rw [(hc' u).2]; nofun), hU.hbE.step hhb (.inl hhE),
    fun u _ _ h => absurd h (by rw [(hc' u).1]; nofun),
    fun u _ _ _ _ h => absurd h (by rw [(hc' u).1]; nofun),
    fun u _ _ _ h => absurd h (by rw [(hc' u).1]; nofun), hq'⟩
  · simp only [Array.getElem?_push]; rw [ite_eq_right (by omega)]; exact h00
  · simp only [Array.getElem?_push, hs1, ↓reduceIte]

/-- A load of a `u32` that the thread owns. -/
theorem ld32 (p : Ptr) (v : BitVec 32) :
    FTTriple (up (pts p 4 v)) (Zig.load (BitVec 32) 4 p) (fun x => ⟪x = v⟫ ⋆ up (pts p 4 v)) :=
  (FTTotalTriple.ofSeq (FTotalTriple.load (by decide)) (ThreadLocal.load OwnsPtr.pts)).toPartial

/-- **A load of `main`'s message field** (its part `rM` and the written message `Msg 2`, at the
program place `x`): the field's value `v`, and the same part. -/
theorem wp_loadPart {G : ThreadId → Gh} {m : Mem} {n : Nat} {rM r : Res} {x : X} {p : Ptr}
    {v : BitVec 32}
    (htt : FTTriple ((· = rM) ⋆ Msg 2) (Zig.load (BitVec 32) 4 p)
      (fun a => ⟪a = v⟫ ⋆ ((· = rM) ⋆ Msg 2)))
    (hr : Msg 2 r) (hd : FHeap.Disjoint rM.heap r.heap)
    (hi : (proto K).inv (upd G 0 (gO (rsum rM r) x)) m) (hc : m.current = 0)
    {Q : BitVec 32 → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ m' r', m'.current = 0 → Msg 2 r' → FHeap.Disjoint rM.heap r'.heap →
      (proto K).inv (upd G 0 (gO (rsum rM r') x)) m' → Q v G m' n) :
    (proto K).WP 0 (ConcM.liftMem (Zig.load (BitVec 32) 4 p) : ConcM Tgt (BitVec 32)) Q G m n :=
  FCond.wp_liftPart (fitsS (K := K)).toC.toFits (.inl rfl) hi hc htt ⟨rM, r, hd, rfl, rfl, hr⟩
    fun a m' r' _ hq hc' _ _ hi' => by
      obtain ⟨rfl, r₁, r₂, hd', rfl, rfl, h2⟩ := sep_lift.mp hq
      exact h m' r₂ hc' h2 hd' hi'

/-- **`main`'s load of `a`**: 3. -/
theorem wp_loadA {G : ThreadId → Gh} {m : Mem} {n : Nat} {rM r : Res} {x : X}
    (hr : Msg 2 r) (hd : FHeap.Disjoint rM.heap r.heap)
    (hi : (proto K).inv (upd G 0 (gO (rsum rM r) x)) m) (hc : m.current = 0)
    {Q : BitVec 32 → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ m' r', m'.current = 0 → Msg 2 r' → FHeap.Disjoint rM.heap r'.heap →
      (proto K).inv (upd G 0 (gO (rsum rM r') x)) m' → Q 3 G m' n) :
    (proto K).WP 0 (ConcM.liftMem (Zig.load (BitVec 32) 4 (cPtr.add 24)) : ConcM Tgt (BitVec 32))
      Q G m n := by
  refine wp_loadPart ?_ hr hd hi hc h
  rw [msg2]
  refine (FTTriple.frameL (FTTriple.frame (ld32 aPtr 3))).post fun a r h => ?_
  obtain ⟨r₁, r₂, hd, rfl, h1, h2⟩ := h
  obtain ⟨hv, h2⟩ := sep_lift.mp (sep_assoc h2)
  exact sep_lift.mpr ⟨hv, r₁, r₂, hd, rfl, h1, h2⟩

/-- **`main`'s load of `b`**: 4. -/
theorem wp_loadB {G : ThreadId → Gh} {m : Mem} {n : Nat} {rM r : Res} {x : X}
    (hr : Msg 2 r) (hd : FHeap.Disjoint rM.heap r.heap)
    (hi : (proto K).inv (upd G 0 (gO (rsum rM r) x)) m) (hc : m.current = 0)
    {Q : BitVec 32 → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ m' r', m'.current = 0 → Msg 2 r' → FHeap.Disjoint rM.heap r'.heap →
      (proto K).inv (upd G 0 (gO (rsum rM r') x)) m' → Q 4 G m' n) :
    (proto K).WP 0 (ConcM.liftMem (Zig.load (BitVec 32) 4 (cPtr.add 28)) : ConcM Tgt (BitVec 32))
      Q G m n := by
  refine wp_loadPart ?_ hr hd hi hc h
  rw [msg2]
  refine (FTTriple.frameL (FTTriple.frameL (ld32 bPtr 4))).post fun a r h => ?_
  obtain ⟨r₁, r₂, hd, rfl, h1, s₁, s₂, hd', rfl, hA, hB⟩ := h
  obtain ⟨hv, hB⟩ := sep_lift.mp hB
  exact sep_lift.mpr ⟨hv, r₁, _, hd, rfl, h1, s₁, s₂, hd', rfl, hA, hB⟩

theorem inv_joins {G : ThreadId → Gh} {m : Mem} {r : Res}
    (hi : (proto K).inv (upd G 0 (gO r { ph := .got })) m) :
    (proto K).inv (upd G 0 (gO r { ph := .joins })) m :=
  inv_move hi rfl rfl rfl rfl (.inl rfl) (by simp [avail, upd_self, gO, Ph.took]) fun _ hu => by
    have hs := hu.shape
    refine hs.main (by show (upd G 0 _ 0).2.ph ≠ .pre; rw [upd_self]; simp [gO])
      (by show (upd G 0 _ 0).2.ph.isMain = true; rw [upd_self]; rfl)
      (by show (upd G 0 _ 0).2.ph ≠ .pre; rw [upd_self]; simp [gO])
      (fun _ => hs.took (by show (upd G 0 _ 0).2.ph.took = true; rw [upd_self]; rfl))
      (fun _ e => upd_ne₂ e)

theorem wp_join {σ : Type} {s : σ} {G : ThreadId → Gh} {m : Mem} {n : Nat} {rM : Res}
    (hi : (proto K).inv (upd G 0 (gO rM { ph := .joins })) m)
    {Q : Unit × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ k G₁ m', n = k + 1 → BlkOk m' → m'.ClocksLe → joinedAll 0 m' → Q ((), s) G₁ m' k) :
    (proto K).WP 0 ((joinC 1 : CM Tgt σ Unit).run s) Q G m n := by
  refine WP.joinC fun k hk => ⟨_, hi, fun G₁ m₁ hg hi₁ => ?_⟩
  obtain ⟨rX, hL, hu⟩ := hi₁
  obtain ⟨h00, ⟨-, h0, -⟩ | ⟨hs2, hr1, -⟩⟩ := hu.shape
  · exfalso; change (G₁ 0).2.ph = _ at h0; rw [hg] at h0; cases h0
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

/-- **`main`'s free of the mailbox** after its join: its end races with no access. -/
theorem wp_free {G : ThreadId → Gh} {m : Mem} {n : Nat} {p : Ptr} (hp : p = cPtr) (hb : BlkOk m)
    (hcl : m.ClocksLe) {Q : Unit → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ m', m'.threads = m.threads → Q () G m' n) :
    (proto K).WP 0 (ConcM.liftMem (free p) : ConcM Tgt Unit) Q G m n := by
  subst hp
  obtain ⟨blk, hblk, hl, -, hk⟩ := hb
  refine WP.liftMem (fun e he => (free_noErr hblk hl (hcl.freeRaces _ _) (by rw [hk]; nofun) e
    he).elim) fun _ m' hfr => ?_
  obtain ⟨b', blk', -, -, rfl⟩ := free_ok hfr
  exact ⟨rfl, h _ rfl⟩

/-! ## The threads -/

/-- The invariant at a stop of a live thread `t`. -/
theorem inv_cur {G : ThreadId → Gh} {m : Mem} (t : ThreadId) (hi : (proto K).inv G m)
    (hph : (G t).1.ph ≠ .gone) : (proto K).inv G { m with current := t } := by
  obtain ⟨-, -, -, h⟩ := (fitsL (K := K)).cur t hi hph
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

/-- **The producer's end** (`QKid`): it is `gone` at `fin` and spawned no thread. -/
theorem qkid {G : ThreadId → Gh} {m : Mem} {d : Nat} {rp : Res}
    (hi : (proto K).inv (upd G 1 (⟨.gone, rp, rnil⟩, { ph := .fin })) m) :
    (proto K).QKid 1 () G m d := by
  refine ⟨_, hi, ⟨rfl, rfl⟩, fun _ => ?_⟩
  obtain ⟨rX, -, hu⟩ := hi
  exact joinedAll_of_main (spawners hu.shape) (by decide)

end Sync.Mailbox
