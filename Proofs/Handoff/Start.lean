import Proofs.Handoff.Steps

/-!
# The start of `handoff`'s protocol

`main`, before its spawn, owns the `Box` after its stores (`inv_start`): it gives `io` and the
three shared words (the condition's state and epoch, the event) to the protocol's rest
(`FOwned.give`; the words' bytes are then read as their cells, `Rest`), and the mutex with `v`
and `ready` to the lock (`FLock.Inv.make`). The sync objects start with every thread out of their
code (`FCond.Inv.start`, `FEvent.Inv.start`). Once for every layout; each version's walk gives the
`Box`'s pieces after its stores.
-/

namespace Zig
namespace Handoff

open Conc Conc.Proto Full Full.FAssn

variable {Lo : Layout} {Tgt : Type} {prodOf : Tgt → Option Ptr}

/-- No thread at the start. -/
def G0 : ThreadId → Gh := fun _ => (⟨.gone, rnil, rnil⟩, {})

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
    fun e he hh => .inr (hfp e he hh), ⟨0, hu⟩, fun i l h => absurd h (hno i l)⟩, ?_, ?_, ?_⟩
  · rw [Word.hist_none hno]; rfl
  · rw [Word.hist_none hno]; exact hu
  · intro c; rw [Word.hist_none hno]; exact le_nil c

/-- `A`, aligned for the `Box`, is 4-aligned. -/
theorem mod4 {A : Nat} (hA : A % Lo.align = 0) : A % 4 = 0 := by
  have h := Nat.mod_mod_of_dvd A Lo.ok.2.2.2.2.2.2.2.2.2.2
  rw [hA] at h; omega

theorem off_add (k : Nat) : (bPtr.add k).off.toNat = k := by simp [bPtr, Ptr.add]

theorem heap_ne_l {a b : Res} {l : Zig.Loc} (h : a.heap l ≠ none) : (rsum a b).heap l ≠ none := by
  simp only [FHeap.union_apply, ne_eq, Option.or_eq_none_iff, not_and]
  intro h'; exact absurd h' h

theorem heap_ne_r {a b : Res} {l : Zig.Loc} (h : b.heap l ≠ none) : (rsum a b).heap l ≠ none := by
  simp only [FHeap.union_apply, ne_eq, Option.or_eq_none_iff, not_and]
  intro _; exact h

theorem erase_ne_r {a b : Res} {l : Zig.Loc} (h : (rsum a b).heap l ≠ none) :
    (rsum a b).heap.erase l ≠ none := by
  simpa [FHeap.erase] using h

/-- **Before the spawn**: `main` owns the `Box` after its stores: its part `rM`, `v = 0` (`rV`),
`ready = false` (`rRd`), the mutex `0` (`rW`), the three shared words `0` (`rB`) and `io` with
the `Box`'s extent (`rIO`). It gives `rB` and `rIO` to the protocol's rest and `rV`, `rRd`, `rW`
to the lock, and keeps `rM`. -/
theorem inv_start {m : Mem} {own : ThreadId → Res} {A : Nat} {wb : Array Byte}
    {rM rV rRd rW rB rIO : Res}
    (ho : FOwned (upd own 0 (rsum (rsum rM (rsum (rsum rV rRd) rW)) (rsum rB rIO))) rnil m)
    (hown : ∀ u, u ≠ 0 → own u = rnil)
    (hd : FHeap.Disjoint (rsum rM (rsum (rsum rV rRd) rW)).heap (rsum rB rIO).heap)
    (hdM : FHeap.Disjoint rM.heap (rsum (rsum rV rRd) rW).heap)
    (hdRW : FHeap.Disjoint (rsum rV rRd).heap rW.heap) (hdVR : FHeap.Disjoint rV.heap rRd.heap)
    (hdB : FHeap.Disjoint rB.heap rIO.heap) (hIO : IoRest Lo rIO)
    (hW : up (bytesAt (bPtr.add Lo.mo) A Lo.size .stack (Enc.encode (0 : BitVec 32))) rW)
    (hB : up (bytesAt (bPtr.add Lo.so) A Lo.size .stack wb) rB)
    (hV : up (bytesAt (bPtr.add Lo.xo) A Lo.size .stack (Enc.encode (0 : BitVec 32))) rV)
    (hRd : up (bytesAt (bPtr.add Lo.ro) A Lo.size .stack (Enc.encode false)) rRd)
    (hwb : wb.size = 12) (hw0 : wb.extract 0 4 = Enc.encode (0 : BitVec 32))
    (hw1 : wb.extract 4 8 = Enc.encode (0 : BitVec 32))
    (hw2 : wb.extract 8 12 = Enc.encode (0 : BitVec 32))
    (hA : A % Lo.align = 0) (hth : m.threads = #[{ spawner := 0, joined := true }])
    (hat : m.atomics = #[]) (hq : m.waiters = #[]) :
    (proto Lo prodOf).inv (upd G0 0 (gO rM { ph := .pre })) m := by
  have hok := Lo.ok
  have h1 : m.threads.size = 1 := by rw [hth]; rfl
  have ht : 0 < m.threads.size := by rw [h1]; decide
  have hA4 := mod4 hA
  obtain ⟨A', bs, hA', hbs, hio⟩ := hIO
  -- the `Box`'s block and bytes
  have hP : (((fun r => r = rM) ⋆ ((up (bytesAt (bPtr.add Lo.xo) A Lo.size .stack
      (Enc.encode (0 : BitVec 32))) ⋆ up (bytesAt (bPtr.add Lo.ro) A Lo.size .stack
      (Enc.encode false))) ⋆ up (bytesAt (bPtr.add Lo.mo) A Lo.size .stack
      (Enc.encode (0 : BitVec 32))))) ⋆ (up (bytesAt (bPtr.add Lo.so) A Lo.size .stack wb) ⋆
      (up (bytesAt bPtr A' Lo.size .stack bs) ⋆ bext 0 Lo.size .stack)))
      (upd own 0 (rsum (rsum rM (rsum (rsum rV rRd) rW)) (rsum rB rIO)) 0) := by
    rw [upd_self]
    exact ⟨_, _, hd, rfl, ⟨_, _, hdM, rfl, rfl, ⟨_, _, hdRW, rfl, ⟨_, _, hdVR, rfl, hV, hRd⟩, hW⟩⟩,
      ⟨_, _, hdB, rfl, hB, hio⟩⟩
  have hPW := hP
  have hPB := hP
  have eW : (((fun r => r = rM) ⋆ ((up (bytesAt (bPtr.add Lo.xo) A Lo.size .stack
      (Enc.encode (0 : BitVec 32))) ⋆ up (bytesAt (bPtr.add Lo.ro) A Lo.size .stack
      (Enc.encode false))) ⋆ up (bytesAt (bPtr.add Lo.mo) A Lo.size .stack
      (Enc.encode (0 : BitVec 32))))) ⋆ (up (bytesAt (bPtr.add Lo.so) A Lo.size .stack wb) ⋆
      (up (bytesAt bPtr A' Lo.size .stack bs) ⋆ bext 0 Lo.size .stack))) =
      ((up (bytesAt (bPtr.add Lo.mo) A Lo.size .stack (Enc.encode (0 : BitVec 32))) ⋆
        bext 0 Lo.size .stack) ⋆ (((fun r => r = rM) ⋆ (up (bytesAt (bPtr.add Lo.xo) A Lo.size
        .stack (Enc.encode (0 : BitVec 32))) ⋆ up (bytesAt (bPtr.add Lo.ro) A Lo.size .stack
        (Enc.encode false)))) ⋆ (up (bytesAt (bPtr.add Lo.so) A Lo.size .stack wb) ⋆
        up (bytesAt bPtr A' Lo.size .stack bs)))) := by ac_rfl
  have eB : (((fun r => r = rM) ⋆ ((up (bytesAt (bPtr.add Lo.xo) A Lo.size .stack
      (Enc.encode (0 : BitVec 32))) ⋆ up (bytesAt (bPtr.add Lo.ro) A Lo.size .stack
      (Enc.encode false))) ⋆ up (bytesAt (bPtr.add Lo.mo) A Lo.size .stack
      (Enc.encode (0 : BitVec 32))))) ⋆ (up (bytesAt (bPtr.add Lo.so) A Lo.size .stack wb) ⋆
      (up (bytesAt bPtr A' Lo.size .stack bs) ⋆ bext 0 Lo.size .stack))) =
      ((up (bytesAt (bPtr.add Lo.so) A Lo.size .stack wb) ⋆ bext 0 Lo.size .stack) ⋆
        (((fun r => r = rM) ⋆ (up (bytesAt (bPtr.add Lo.xo) A Lo.size
        .stack (Enc.encode (0 : BitVec 32))) ⋆ up (bytesAt (bPtr.add Lo.ro) A Lo.size .stack
        (Enc.encode false)))) ⋆ (up (bytesAt (bPtr.add Lo.mo) A Lo.size .stack
        (Enc.encode (0 : BitVec 32))) ⋆ up (bytesAt bPtr A' Lo.size .stack bs)))) := by ac_rfl
  rw [eW] at hPW
  rw [eB] at hPB
  have hs4 : (Enc.encode (0 : BitVec 32)).size = 4 := LawfulEnc.size_encode _
  obtain ⟨blk, hblk, hl, hAd, hS, hK, hxW⟩ :=
    ho.bytesOf ht (rfl : (bPtr.add Lo.mo).block = some 0) (by rw [hs4]; decide) hPW
  obtain ⟨blk', hblk', -, -, -, -, hxB⟩ :=
    ho.bytesOf ht (rfl : (bPtr.add Lo.so).block = some 0) (by rw [hwb]; decide) hPB
  rw [hblk] at hblk'; cases hblk'
  rw [off_add, hs4] at hxW
  rw [off_add, hwb] at hxB
  -- each access to a byte of `main`'s part happened before `main`
  have hown0 : ∀ e ∈ m.footprint, e.Touches (upd own 0 (rsum (rsum rM (rsum (rsum rV rRd) rW))
      (rsum rB rIO)) 0).heap.erase → AllLe m e.clock :=
    fun e he htc => allLe_of_one h1 (ho.owns 0 ht e he (.inl htc))
  have hBin : ∀ l, rB.heap l ≠ none ↔ Lo.BoxW l := fun l => by
    rw [up_bytesAt_some hB rfl l, off_add, hwb]; rfl
  have hIOoff : ∀ l, Lo.BoxW l → rIO.heap l = none := fun l hl =>
    (hdB l).resolve_left ((hBin l).mpr hl)
  -- the three words
  have hword : ∀ k, k ≤ 8 → blk.bytes.extract (Lo.so + k) (Lo.so + k + 4) = wb.extract k (k + 4) :=
    fun k hk => by
      rw [← hxB, Array.extract_extract]; congr 1 <;> omega
  have hwi : ∀ W : Word 32 4, W.b = 0 → Lo.so ≤ W.o → W.o + 4 ≤ Lo.so + 12 → W.o % 4 = 0 →
      wb.extract (W.o - Lo.so) (W.o - Lo.so + 4) = Enc.encode (0 : BitVec 32) →
      W.Ok m ∧ (W.hist m).size = 1 ∧ (W.hist m)[0]!.Val (0 : BitVec 32) ∧
        ∀ c, VClock.le (W.hist m)[0]!.clock c = true := fun W hb h1' h2' h4 he =>
    word_init hb (by rw [hAd]; omega) (by rw [hS]; omega) hblk hl hK hat
      (by
        have := hword (W.o - Lo.so) (by omega)
        rw [show Lo.so + (W.o - Lo.so) = W.o by omega] at this
        rw [this, he]; exact intOfBytes_rmw 0)
      (fun e he' hh => hown0 e he' (Word.touches_of hh fun x a b => by
        rw [hb, upd_self]
        exact erase_ne_r (heap_ne_r (heap_ne_l ((hBin _).mpr ⟨rfl, by omega, by omega⟩)))))
  obtain ⟨hwsOk, hwsz, hwsv, -⟩ := hwi Lo.WS rfl (Nat.le_refl _) (by simp [Layout.WS])
    hok.2.2.2.2.2.2.2.1 (by simp [Layout.WS]; exact hw0)
  obtain ⟨hweOk, hwez, hwev, hwec⟩ := hwi Lo.WE rfl (by simp [Layout.WE]) (by simp [Layout.WE])
    (by simp [Layout.WE]; omega) (by simp [Layout.WE]; exact hw1)
  obtain ⟨hwvOk, hwvz, hwvv, -⟩ := hwi Lo.WV rfl (by simp [Layout.WV]; omega)
    (by simp [Layout.WV]; omega) (by simp [Layout.WV]; omega)
    (by simp [Layout.WV]; rw [show Lo.vo - Lo.so = 8 by omega]; exact hw2)
  -- the mutex holds 0
  have h0 : (L Lo).U32 m 0 := by
    show (intOfBytes 32 (curBytes m 0 Lo.mo 4)).run = _
    unfold curBytes; rw [hblk]
    simp only [Option.map_some, Option.getD_some]
    rw [hxW]; exact intOfBytes_rmw 0
  -- the rest: `rB` and `rIO`; read `rB` as the words' cells
  have ho' := ho.give (t := 0) ht (by rw [upd_self]) hd
  rw [upd_upd, rsum_rnil] at ho'
  have ho'' : FOwned (upd own 0 (rsum rM (rsum (rsum rV rRd) rW)))
      (rsum (cellsAt Lo.BoxW m) rIO) m := by
    have hBoff : ∀ l, ¬ Lo.BoxW l → rB.heap l = none := fun l hb => by
      cases e : rB.heap l with
      | none => rfl
      | some _ => exact absurd ((hBin l).mp (by rw [e]; simp)) hb
    refine ho'.congrRestU (fun l => ?_) (fun l fc' hl => ?_) ?_ ?_
    · by_cases hb : Lo.BoxW l
      · obtain ⟨fc, hfc⟩ := Option.ne_none_iff_exists'.mp ((hBin l).mpr hb)
        have := ho'.rest_cell (l := l) (fc := fc) (by simp [FHeap.union_apply, hfc])
        simp only [FHeap.union_apply, cellsAt_of hb, hIOoff l hb, hfc, Option.or_none]
        cases e : m.heap l with
        | none => rw [e] at this; cases this
        | some c => rw [e] at this; simpa [Cell.norm] using this
      · simp [FHeap.union_apply, cellsAt_none hb, hBoff l hb]
    · by_cases hb : Lo.BoxW l
      · simp only [FHeap.union_apply, cellsAt_of hb, hIOoff l hb, Option.or_none,
          Option.map_eq_some_iff] at hl
        obtain ⟨c, -, rfl⟩ := hl
        exact .inl rfl
      · simp only [FHeap.union_apply, cellsAt_none hb, Option.none_or] at hl
        exact .inr ⟨fc', by simp [FHeap.union_apply, hBoff l hb, hl], rfl⟩
    · simp [cellsAt, hB.2.1, Know.none_union]
    · simp [cellsAt, hB.2.2]
  have hGu : ∀ u, u ≠ 0 → upd G0 0 (gO rM { ph := .pre }) u = G0 u := fun u h => upd_ne _ _ h
  have hX0 : (upd G0 0 (gO rM { ph := .pre }) 0).2 = { ph := .pre } := by rw [upd_self]; rfl
  have hXu : ∀ u, u ≠ 0 → (upd G0 0 (gO rM { ph := .pre }) u).2 = {} := fun u h => by
    rw [hGu u h]; rfl
  have hc : ∀ u, (upd G0 0 (gO rM { ph := .pre }) u).2.c = .out := fun u => by
    by_cases h : u = 0
    · subst h; rw [hX0]
    · rw [hXu u h]
  have he : ∀ u, (upd G0 0 (gO rM { ph := .pre }) u).2.e = .out := fun u => by
    by_cases h : u = 0
    · subst h; rw [hX0]
    · rw [hXu u h]
  have hp1 : (upd G0 0 (gO rM { ph := .pre }) 1).2.ph = .none := by rw [hXu 1 (by decide)]
  have hBk : Lo.mo + 4 ≤ blk.bytes.size := by rw [hS]; omega
  refine ⟨rsum (cellsAt Lo.BoxW m) rIO, FLock.Inv.make (t := 0) (rL := rsum rV rRd) (rW := rW) ho''
    rfl ht (fun u hu => ?_) (by rw [upd_self, upd_self]; rfl) (by rw [upd_self]; exact hdM) hdRW
    (fun l => ?_) hW.2.1 hW.2.2 (fun u => ?_) (fun u => ?_) ?_
    ⟨blk, hblk, hl, hBk, by show (blk.addr + Lo.mo) % 4 = 0; rw [hAd]; omega, by rw [hK]; decide, by rw [hK]; simp [BlockKind.mappedLo]⟩
    h0 (by rw [hat]; simp) hq (allLe_of_one h1 (VClock.le_refl _)), ?_⟩
  · rw [upd_ne _ _ hu, hown u hu]
    unfold FLock.own; rw [hGu u hu]; split <;> simp [G0, FLock.prod, rnil_rsum]
  · rw [up_bytesAt_some hW rfl l, off_add, hs4]
    show _ ↔ l.1 = 0 ∧ Lo.mo ≤ l.2 ∧ l.2 < Lo.mo + 4
    rfl
  · by_cases hu : u = 0
    · subst hu; rw [upd_self]; exact .inl ⟨rfl, ht, rfl⟩
    · rw [hGu u hu]; exact .inr rfl
  · by_cases hu : u = 0
    · subst hu; rw [upd_self]; rfl
    · rw [hGu u hu]; rfl
  · -- `v = 0`, `ready = false`
    show R Lo (fun u => (upd G0 0 (gO rM { ph := .pre }) u).2) (rsum rV rRd)
    unfold R vOf
    rw [hp1]
    exact ⟨rV, rRd, hdVR, rfl,
      ⟨⟨A, Lo.size, .stack, Enc.encode (0 : BitVec 32), by rw [off_add]; omega,
        LawfulEnc.size_encode _, LawfulEnc.decode_encode _, hV.1, by decide⟩, hV.2.1, hV.2.2⟩,
      ⟨⟨A, Lo.size, .stack, Enc.encode false, Nat.mod_one _, LawfulEnc.size_encode _,
        LawfulEnc.decode_encode _, hRd.1, by decide⟩, hRd.2.1, hRd.2.2⟩⟩
  · refine ⟨⟨by rw [hth]; rfl, .inl ⟨h1, hX0, fun u hu => hXu u (by unfold ThreadId at *; omega)⟩⟩,
      fun e he hr => .inr fun u hu => ?_, ⟨rIO, ⟨A', bs, hA', hbs, hio⟩, hIOoff, rfl⟩,
      ⟨blk, hblk, hl, hS, hK⟩, hwsOk, hweOk, hwvOk,
      FCond.Inv.start _ hwsz hwsv hc hq, FEvent.Inv.start _ hwvz hwvv he hq,
      by show ((upd G0 0 _ 1).2.c).waits = false; rw [hc]; rfl, fun _ => hwez, hwec _,
      fun h => ?_, fun h => ?_, fun _ _ _ _ h => ?_, fun h => ?_, fun h => ?_,
      fun w hw => by simp [hq] at hw, fun u h => absurd (hc u) h⟩
    · -- every access to `io` happened before `main`, which owned it
      obtain rfl : u = 0 := by rw [h1] at hu; omega
      have hx : rIO.heap (e.block, e.off) ≠ none := by
        obtain ⟨r₁, r₂, hd₁, rfl, h₁, -⟩ := hio
        exact heap_ne_l (b := r₂) ((up_bytesAt_some h₁ rfl (e.block, e.off)).mpr
          ⟨hr.1, by simp [bPtr], by simp [bPtr, hbs]; exact hr.2.2⟩)
      refine ho.owns 0 ht e he (.inl ⟨e.off, Nat.le_refl _, by have := hr.2.1; omega, ?_⟩)
      rw [upd_self]
      exact erase_ne_r (heap_ne_r (heap_ne_r hx))
    · rw [hc] at h; exact absurd h (by decide)
    · rw [hp1] at h; rcases h with h | h <;> cases h
    · rw [hc] at h; cases h
    · rw [hc] at h; exact absurd h (by decide)
    · rw [hp1] at h; cases h

end Handoff
end Zig
