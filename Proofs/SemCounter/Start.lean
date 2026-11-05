import Proofs.SemCounter.Ops
import ZigLean.Sep.Full.Local

/-!
# The start and the end of `semaphoreCounter`'s protocol

- **The start** (`inv_start`): `main`, before its spawn, owns the `SemCounter` after its stores. It
  gives `io` and the extent and the condition's two words (as their cells, `Rest`) to the
  protocol's rest (`FOwned.give`), and the count with `n` (`R`: no thread has the permit, so the
  pool owns `n = 0`) and the mutex's word to the lock (`FLock.Inv.make`). The condition and the
  semaphore start with every thread out of their code (`FCond.Inv.start`, `FSem.Inv.start`).
- **The spawn** (`inv_spawn`): `main` copies its plain mode for the kid; both threads go to
  `semWork` with no increment and no permit (`gW rp 0 false 0`). The fork keeps the condition's
  and the semaphore's facts (`hb_fork`: a write that happened before every live thread happened
  before the kid, whose clock is its parent's).
- **The ends** (`inv_end`): after `semWork` (two increments, no permit) `main` goes to its join
  and the kid ends (`gone`). **`main`'s join** (`wp_join`) takes `n`, then 4, back from the lock
  (`FLock.Inv.take`), and **`main`'s free** (`wp_free`) ends the `SemCounter`.
-/

namespace Zig
namespace SemCounter

open Conc Conc.Proto Full Full.FAssn

variable {Tgt : Type} {semOf : Tgt → Option Ptr}

/-- No thread at the start. -/
def G0 : ThreadId → Gh := fun _ => (⟨.gone, rnil, rnil⟩, {})

/-- A thread out of the lock's code with its part `r` and its places `x`. -/
def gO (r : Res) (x : X) : Gh := (⟨.out, r, rnil⟩, x)

/-! ## Bytes -/


theorem o16 : (cPtr.add 16).off.toNat = 16 := by simp [cPtr, Ptr.add]
theorem o24 : (cPtr.add 24).off.toNat = 24 := by simp [cPtr, Ptr.add]
theorem o28 : (cPtr.add 28).off.toNat = 28 := by simp [cPtr, Ptr.add]
theorem o40 : nPtr.off.toNat = 40 := by simp [nPtr, cPtr, Ptr.add]

theorem heap_ne_l {a b : Res} {l : Zig.Loc} (h : a.heap l ≠ none) : (rsum a b).heap l ≠ none := by
  simp only [FHeap.union_apply, ne_eq, Option.or_eq_none_iff, not_and]
  intro h'; exact absurd h' h

theorem heap_ne_r {a b : Res} {l : Zig.Loc} (h : b.heap l ≠ none) : (rsum a b).heap l ≠ none := by
  simp only [FHeap.union_apply, ne_eq, Option.or_eq_none_iff, not_and]
  intro _; exact h

theorem erase_ne_r {a b : Res} {l : Zig.Loc} (h : (rsum a b).heap l ≠ none) :
    (rsum a b).heap.erase l ≠ none := by
  simpa [FHeap.erase] using h

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

/-- **The `SemCounter`'s bytes** in its pieces: `io`, the count, the mutex, the condition's two
words, the semaphore's padding, `n`, the padding. -/
theorem box_split {r : Res} {A : Nat} {bs : Array Byte} (hs : bs.size = 48)
    (h : up (bytesAt cPtr A 48 .stack bs) r) :
    (up (bytesAt (cPtr.add 0) A 48 .stack (bs.extract 0 16)) ⋆
      (up (bytesAt (cPtr.add 16) A 48 .stack (bs.extract 16 24)) ⋆
      (up (bytesAt (cPtr.add 24) A 48 .stack (bs.extract 24 28)) ⋆
      (up (bytesAt (cPtr.add 28) A 48 .stack (bs.extract 28 36)) ⋆
      (up (bytesAt (cPtr.add 36) A 48 .stack (bs.extract 36 40)) ⋆
      (up (bytesAt (cPtr.add 40) A 48 .stack (bs.extract 40 44)) ⋆
       up (bytesAt (cPtr.add 44) A 48 .stack (bs.extract 44 48)))))))) r := by
  have h' : up (bytesAt (cPtr.add (0 : Nat)) A 48 .stack (bs.extract 0 48)) r := by
    have e : cPtr.add ((0 : Nat) : Int) = cPtr := rfl
    rw [e, show bs.extract 0 48 = bs by rw [← hs]; exact Array.extract_size]; exact h
  refine sep_mono_right (fun _ hr => ?_)
    (split_at (a := 0) (b := 16) (c := 48) h' (by omega) (by omega) (by omega))
  refine sep_mono_right (fun _ hr => ?_)
    (split_at (a := 16) (b := 24) (c := 48) hr (by omega) (by omega) (by omega))
  refine sep_mono_right (fun _ hr => ?_)
    (split_at (a := 24) (b := 28) (c := 48) hr (by omega) (by omega) (by omega))
  refine sep_mono_right (fun _ hr => ?_)
    (split_at (a := 28) (b := 36) (c := 48) hr (by omega) (by omega) (by omega))
  refine sep_mono_right (fun _ hr => ?_)
    (split_at (a := 36) (b := 40) (c := 48) hr (by omega) (by omega) (by omega))
  exact split_at (a := 40) (b := 44) (c := 48) hr (by omega) (by omega) (by omega)

theorem sep_box {I C W B P1 N P2 b pl : FAssn} {r : Res}
    (h : (((I ⋆ (C ⋆ (W ⋆ (B ⋆ (P1 ⋆ (N ⋆ P2)))))) ⋆ b) ⋆ pl) r) :
    ((((P1 ⋆ P2) ⋆ pl) ⋆ ((C ⋆ N) ⋆ W)) ⋆ (B ⋆ (I ⋆ b))) r := by
  have e : (((I ⋆ (C ⋆ (W ⋆ (B ⋆ (P1 ⋆ (N ⋆ P2)))))) ⋆ b) ⋆ pl) =
      ((((P1 ⋆ P2) ⋆ pl) ⋆ ((C ⋆ N) ⋆ W)) ⋆ (B ⋆ (I ⋆ b))) := by
    ac_rfl
  rw [e] at h; exact h

/-- A word of the condition at the start: no atomic location, each access to it happened before
every thread, and the value 0, written at no clock. -/
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

/-! ## The start -/

/-- **Before the spawn**: `main` owns the `SemCounter` after its stores (the bytes `bs`: `io`, the
count 1, the mutex 0, the condition's words 0, `n = 0`), with its extent, and the plain mode
(module doc). The protocol's invariant holds with `main`'s part the paddings and the plain
mode. -/
theorem inv_start {m : Mem} {r : Res} {A : Nat} {bs : Array Byte}
    (ho : FOwned (upd (fun _ => rnil) 0 r) rnil m)
    (hF : ((up (bytesAt cPtr A 48 .stack bs) ⋆ bext 0 48 .stack) ⋆ plain) r)
    (hs : bs.size = 48)
    (hIo : bs.extract 0 16 = Enc.encode (⟨⟩ : Io))
    (hC : bs.extract 16 24 = Enc.encode (1 : BitVec 64))
    (hW : bs.extract 24 28 = Enc.encode (0 : BitVec 32))
    (hS : bs.extract 28 32 = Enc.encode (0 : BitVec 32))
    (hE : bs.extract 32 36 = Enc.encode (0 : BitVec 32))
    (hN : bs.extract 40 44 = Enc.encode (0 : BitVec 32))
    (hA : A % 8 = 0) (hth : m.threads = #[{ spawner := 0, joined := true }])
    (hat : m.atomics = #[]) (hq : m.waiters = #[]) :
    ∃ rM, rM.Plain ∧ (proto semOf).inv (upd G0 0 (gO rM { ph := .pre })) m := by
  obtain ⟨_, _, hd, rfl, ⟨rM, _, hdM, rfl, hpM, ⟨_, rW, hdLW, rfl, ⟨rCn, rN, hdCN, rfl, hCn, hN₁⟩,
    hW₁⟩⟩, ⟨rB, rIO, hdB, rfl, hB₁, hIO⟩⟩ :=
    sep_box (sep_mono_left (fun _ h => sep_mono_left (fun _ h => box_split hs h) h) hF)
  refine ⟨rM, Res.plain_of_sep hpM, ?_⟩
  rw [hW] at hW₁; rw [hC] at hCn; rw [hN] at hN₁
  have h1 : m.threads.size = 1 := by rw [hth]; rfl
  have ht : 0 < m.threads.size := by rw [h1]; decide
  have hs4 : (Enc.encode (0 : BitVec 32)).size = 4 := LawfulEnc.size_encode _
  have hs8 : (bs.extract 28 36).size = 8 := by simp [hs]
  -- the block and its bytes
  have hP : ((((fun r => r = rM) ⋆ ((up (bytesAt (cPtr.add 16) A 48 .stack
      (Enc.encode (1 : BitVec 64))) ⋆ up (bytesAt (cPtr.add 40) A 48 .stack
      (Enc.encode (0 : BitVec 32)))) ⋆ up (bytesAt (cPtr.add 24) A 48 .stack
      (Enc.encode (0 : BitVec 32))))) ⋆ (up (bytesAt (cPtr.add 28) A 48 .stack (bs.extract 28 36)) ⋆
      (up (bytesAt (cPtr.add 0) A 48 .stack (bs.extract 0 16)) ⋆ bext 0 48 .stack))))
      (upd (fun _ => rnil) 0 (rsum (rsum rM (rsum (rsum rCn rN) rW)) (rsum rB rIO)) 0) := by
    rw [upd_self]
    obtain ⟨r₁, r₂, hd₁, rfl, h₁, h₂⟩ := hIO
    exact ⟨_, _, hd, rfl, ⟨_, _, hdM, rfl, rfl, ⟨_, _, hdLW, rfl, ⟨_, _, hdCN, rfl, hCn, hN₁⟩, hW₁⟩⟩,
      ⟨_, _, hdB, rfl, hB₁, ⟨r₁, r₂, hd₁, rfl, h₁, h₂⟩⟩⟩
  have eW : ∀ (Rm Cn N W B I b : FAssn), ((Rm ⋆ ((Cn ⋆ N) ⋆ W)) ⋆ (B ⋆ (I ⋆ b))) =
      ((W ⋆ b) ⋆ ((Rm ⋆ (Cn ⋆ N)) ⋆ (B ⋆ I))) := by intros; ac_rfl
  have eB : ∀ (Rm Cn N W B I b : FAssn), ((Rm ⋆ ((Cn ⋆ N) ⋆ W)) ⋆ (B ⋆ (I ⋆ b))) =
      ((B ⋆ b) ⋆ ((Rm ⋆ (Cn ⋆ N)) ⋆ (W ⋆ I))) := by intros; ac_rfl
  have hPW := hP; rw [eW] at hPW
  have hPB := hP; rw [eB] at hPB
  obtain ⟨blk, hblk, hl, hAd, hSz, hK, hxW⟩ :=
    ho.bytesOf ht (rfl : (cPtr.add 24).block = some 0) (by rw [hs4]; decide) hPW
  obtain ⟨blk', hblk', -, -, -, -, hxB⟩ :=
    ho.bytesOf ht (rfl : (cPtr.add 28).block = some 0) (by rw [hs8]; decide) hPB
  rw [hblk] at hblk'; cases hblk'
  rw [o24, hs4] at hxW
  rw [o28, hs8] at hxB
  -- each access to a byte of `main`'s part happened before `main`
  have hown0 : ∀ e ∈ m.footprint, e.Touches (upd (fun _ => rnil) 0 (rsum (rsum rM (rsum (rsum rCn rN)
      rW)) (rsum rB rIO)) 0).heap.erase → AllLe m e.clock :=
    fun e he htc => allLe_of_one h1 (ho.owns 0 ht e he (.inl htc))
  have hBin : ∀ l, rB.heap l ≠ none ↔ BoxW l := fun l => by
    rw [up_bytesAt_some hB₁ rfl l, o28, hs8]; rfl
  have hIOoff : ∀ l, BoxW l → rIO.heap l = none := fun l hl =>
    (hdB l).resolve_left ((hBin l).mpr hl)
  -- the two words
  have hwi : ∀ W : Word 32 4, W.b = 0 → 28 ≤ W.o → W.o + 4 ≤ 36 → W.o % 4 = 0 →
      bs.extract W.o (W.o + 4) = Enc.encode (0 : BitVec 32) →
      W.Ok m ∧ (W.hist m).size = 1 ∧ (W.hist m)[0]!.Val (0 : BitVec 32) ∧
        ∀ c, VClock.le (W.hist m)[0]!.clock c = true := fun W hb h1' h2' h4 he =>
    word_init hb (by rw [hAd]; omega) (by rw [hSz]; omega) hblk hl hK hat
      (by
        have e1 : ∀ as : Array Byte, (as.extract 28 36).extract (W.o - 28) (W.o - 28 + 4) =
            as.extract W.o (W.o + 4) := fun as => by
          rw [Array.extract_extract]; congr 1 <;> omega
        rw [← e1, hxB, e1, he]; exact intOfBytes_rmw 0)
      (fun e he' hh => hown0 e he' (Word.touches_of hh fun x a b => by
        rw [hb, upd_self]
        exact erase_ne_r (heap_ne_r (heap_ne_l ((hBin _).mpr ⟨rfl, by omega, by omega⟩)))))
  obtain ⟨hwsOk, hwsz, hwsv, -⟩ := hwi WS rfl (by decide) (by decide) (by decide) hS
  obtain ⟨hweOk, hwez, hwev, hwec⟩ := hwi WE rfl (by decide) (by decide) (by decide) hE
  -- the mutex holds 0
  have h0 : L.U32 m 0 := by
    show (intOfBytes 32 (curBytes m 0 24 4)).run = _
    unfold curBytes; rw [hblk]
    simp only [Option.map_some, Option.getD_some]
    rw [hxW]; exact intOfBytes_rmw 0
  -- the rest: `rB` and `rIO`; read `rB` as the words' cells
  have ho' := ho.give (t := 0) ht (by rw [upd_self]) hd
  rw [upd_upd, rsum_rnil] at ho'
  have ho'' : FOwned (upd (fun _ => rnil) 0 (rsum rM (rsum (rsum rCn rN) rW)))
      (rsum (cellsAt BoxW m) rIO) m := by
    have hBoff : ∀ l, ¬ BoxW l → rB.heap l = none := fun l hb => by
      cases e : rB.heap l with
      | none => rfl
      | some _ => exact absurd ((hBin l).mp (by rw [e]; simp)) hb
    refine ho'.congrRestU (fun l => ?_) (fun l fc' hl => ?_) ?_ ?_
    · by_cases hb : BoxW l
      · obtain ⟨fc, hfc⟩ := Option.ne_none_iff_exists'.mp ((hBin l).mpr hb)
        have := ho'.rest_cell (l := l) (fc := fc) (by simp [FHeap.union_apply, hfc])
        simp only [FHeap.union_apply, cellsAt_of hb, hIOoff l hb, hfc, Option.or_none]
        cases e : m.heap l with
        | none => rw [e] at this; cases this
        | some c => rw [e] at this; simpa [Cell.norm] using this
      · simp [FHeap.union_apply, cellsAt_none hb, hBoff l hb]
    · by_cases hb : BoxW l
      · simp only [FHeap.union_apply, cellsAt_of hb, hIOoff l hb, Option.or_none,
          Option.map_eq_some_iff] at hl
        obtain ⟨c, -, rfl⟩ := hl
        exact .inl rfl
      · simp only [FHeap.union_apply, cellsAt_none hb, Option.none_or] at hl
        exact .inr ⟨fc', by simp [FHeap.union_apply, hBoff l hb, hl], rfl⟩
    · simp [cellsAt, hB₁.2.1, Know.none_union]
    · simp [cellsAt, hB₁.2.2]
  -- the ghost values
  have hGu : ∀ u, u ≠ 0 → upd G0 0 (gO rM { ph := .pre }) u = G0 u := fun u h => upd_ne _ _ h
  have hX0 : (upd G0 0 (gO rM { ph := .pre }) 0).2 = { ph := .pre } := by rw [upd_self]; rfl
  have hXu : ∀ u, u ≠ 0 → (upd G0 0 (gO rM { ph := .pre }) u).2 = {} := fun u h => by
    rw [hGu u h]; rfl
  have hc : ∀ u, (upd G0 0 (gO rM { ph := .pre }) u).2.c = .out := fun u => by
    by_cases h : u = 0
    · subst h; rw [hX0]
    · rw [hXu u h]
  have hsp : ∀ u, (upd G0 0 (gO rM { ph := .pre }) u).2.sp = .out := fun u => by
    by_cases h : u = 0
    · subst h; rw [hX0]
    · rw [hXu u h]
  have hp1 : (upd G0 0 (gO rM { ph := .pre }) 1).2.ph = .none := by rw [hXu 1 (by decide)]
  have hp0 : (upd G0 0 (gO rM { ph := .pre }) 0).2.ph = .pre := by rw [hX0]
  have hnw : ∀ u k b s, (upd G0 0 (gO rM { ph := .pre }) u).2.ph ≠ .work k b s := fun u k b s h => by
    by_cases e : u = 0
    · subst e; rw [hp0] at h; cases h
    · rw [hXu u e] at h; cases h
  have hheld : held (xs (upd G0 0 (gO rM { ph := .pre }))) = false := by
    show (((upd G0 0 _ 0).2.ph).holds || ((upd G0 0 _ 1).2.ph).holds) = false
    rw [hp0, hp1]; rfl
  have hsum : sum (xs (upd G0 0 (gO rM { ph := .pre }))) = 0 := by
    show ((upd G0 0 _ 0).2.ph).count + ((upd G0 0 _ 1).2.ph).count = 0
    rw [hp0, hp1]; rfl
  refine ⟨rsum (cellsAt BoxW m) rIO, FLock.Inv.make (t := 0) (rL := rsum rCn rN) (rW := rW) ho''
    (by simp [joinedB, hth]) ht (fun u hu => ?_) (by rw [upd_self, upd_self]; rfl)
    (by rw [upd_self]; exact hdM) hdLW
    (fun l => ?_) hW₁.2.1 hW₁.2.2 (fun u => ?_) (fun u => ?_) ?_
    ⟨blk, hblk, hl, by rw [hSz]; decide, by show (blk.addr + 24) % 4 = 0; rw [hAd]; omega,
      by rw [hK]; decide, by rw [hK]; simp [BlockKind.mappedLo]⟩
    h0 (by rw [hat]; simp) hq (allLe_of_one h1 (VClock.le_refl _)), ?_⟩
  · rw [upd_ne _ _ hu]
    unfold FLock.own; rw [hGu u hu]; split <;> simp [G0, FLock.prod, rnil_rsum]
  · rw [up_bytesAt_some hW₁ rfl l, o24, hs4]
    show _ ↔ l.1 = 0 ∧ 24 ≤ l.2 ∧ l.2 < 24 + 4
    rfl
  · by_cases hu : u = 0
    · subst hu; rw [upd_self]; exact .inl ⟨rfl, ht, by simp [joinedB, hth]⟩
    · rw [hGu u hu]; exact .inr rfl
  · by_cases hu : u = 0
    · subst hu; rw [upd_self]; rfl
    · rw [hGu u hu]; rfl
  · -- the count 1, the pool `n = 0`
    show R (fun u => (upd G0 0 (gO rM { ph := .pre }) u).2) (rsum rCn rN)
    unfold R
    have hpv : pv (fun u => ((fun u => (upd G0 0 (gO rM { ph := .pre }) u).2) u).ph) = 1 := by
      unfold pv; rw [show held _ = false from hheld]; rfl
    have hpool : Pool (fun u => ((fun u => (upd G0 0 (gO rM { ph := .pre }) u).2) u).ph) =
        up (pts nPtr 4 (BitVec.ofNat 32 0)) := by
      unfold Pool; rw [show held _ = false from hheld, show sum _ = 0 from hsum]; rfl
    rw [hpv, hpool]
    exact ⟨rCn, rN, hdCN, rfl,
      ⟨⟨A, 48, .stack, Enc.encode (1 : BitVec 64), by rw [o16]; omega,
        LawfulEnc.size_encode _, LawfulEnc.decode_encode _, hCn.1, by decide⟩, hCn.2.1, hCn.2.2⟩,
      ⟨⟨A, 48, .stack, Enc.encode (0 : BitVec 32), by rw [o40]; omega,
        LawfulEnc.size_encode _, LawfulEnc.decode_encode _, hN₁.1, by decide⟩, hN₁.2.1, hN₁.2.2⟩⟩
  · -- the rest
    have hio : ReadShared IoR m := fun e he hr => .inr fun u hu => by
      obtain rfl : u = 0 := by rw [h1] at hu; omega
      have hx : rIO.heap (e.block, e.off) ≠ none := by
        obtain ⟨r₁, r₂, hd₁, rfl, h₁, -⟩ := hIO
        have hsz16 : (bs.extract 0 16).size = 16 := by simp [hs]
        exact heap_ne_l (b := r₂) ((up_bytesAt_some h₁ rfl (e.block, e.off)).mpr
          ⟨hr.1, by simp [cPtr, Ptr.add], by rw [hsz16]; simp [cPtr, Ptr.add]; exact hr.2.2⟩)
      refine ho.owns 0 ht e he (.inl ⟨e.off, Nat.le_refl _, by have := hr.2.1; omega, ?_⟩)
      rw [upd_self]
      exact erase_ne_r (heap_ne_r (heap_ne_r hx))
    refine ⟨⟨⟨by rw [hth]; rfl, .inl ⟨h1, hp0, fun u hu => ?_⟩⟩, hio,
        ⟨rIO, ⟨A, bs.extract 0 16, hA, by simp [hs], by rw [hIo]; exact LawfulEnc.decode_encode _,
          ?_⟩, hIOoff,
          rfl⟩, ⟨blk, hblk, hl, hSz, hK⟩, hwsOk, hweOk, fun w hw => by simp [hq] at hw⟩,
      FCond.Inv.start hwsz hwsv hwez hwev hc hq,
      FSem.Inv.start (S := S) hwsz hwsv hc hsp,
      ⟨.inr (by rw [hp1]; rfl), fun u k s h => absurd h (hnw u k true s),
        fun u h => (by rw [hsp u] at h; cases h),
        fun k hk => .inr (.inr fun u _ _ => by
          obtain rfl : k = 0 := by rw [hwez] at hk; omega
          exact hwec _),
        fun u i e h => (by rw [hc u] at h; cases h),
        fun u _ hr _ => absurd hr (by rw [hc u]; decide),
        fun u i jr sn e h => (by rw [hc u] at h; cases h),
        fun u i jr sn e v q n h' h => (by rw [hc u] at h; cases h),
        fun u i jr sn e h => (by rw [hc u] at h; cases h),
        fun v q n h' h => (by rw [hc v] at h; cases h)⟩⟩
    · show (upd G0 0 _ u).2.ph = _; rw [hXu u (by unfold ThreadId at *; omega)]
    · rw [show cPtr = cPtr.add 0 from rfl]; exact hIO

/-! ## Field pointers and `io` -/

/-- A field pointer of the `SemCounter` (block 0) is formed (`ptrProject`, MM-3). -/
theorem proj {m : Mem} (hb : BlkOk m) {k : Nat} (hk : k ≤ 48) :
    (ptrProject cPtr (·.add k)).run m = pure (cPtr.add k, m) := by
  obtain ⟨blk, hb, -, hsz, -⟩ := hb
  exact ptrProject_block_run hb rfl (by decide) (by simp [cPtr, hsz]; omega)

/-- A field pointer of the `SemCounter` from the protocol's invariant. -/
theorem projI {G : ThreadId → Gh} {m : Mem} (hi : (proto semOf).inv G m) {k : Nat}
    (hk : k ≤ 48) : (ptrProject cPtr (·.add k)).run m = pure (cPtr.add k, m) := by
  obtain ⟨rX, -, hu⟩ := hi
  exact proj hu.um.blk hk

/-- **A read of `n` bytes of `io`** (`n ≤ 16`) by the current thread keeps `U`: `io` is
read-shared, the condition's words, the places and the futex queue stay. -/
theorem U_rec {G : ThreadId → Gh} {rX : Res} {m : Mem} {t : ThreadId} {n : Nat}
    (hu : U G rX m) (hcs : m.clocks.size = m.threads.size) (hc : m.current = t)
    (ht : t < m.threads.size) (hio : n ≤ 16) :
    U G rX (m.recordAt 0 0 n .read) := by
  have hclk := Conc.recordAt_le m 0 0 n .read
  obtain ⟨hwS, hhS⟩ := hu.um.ws.record_apart_native (b := 0) (o := 0) (len := n) (k := .read)
    (.inr (.inl (by show 0 + n ≤ 28; omega)))
  obtain ⟨hwE, hhE⟩ := hu.um.we.record_apart_native (b := 0) (o := 0) (len := n) (k := .read)
    (.inr (.inl (by show 0 + n ≤ 32; omega)))
  exact ⟨⟨hu.um.shape, hu.um.io.read (hc ▸ ht) hcs 0 0 n, hu.um.rest.congr fun _ _ => rfl,
      hu.um.blk, hwS, hwE, hu.um.q⟩,
    hu.cinv.stay hhS hhE rfl (fun _ hw _ => hw) (fun _ _ h => h) (Nat.le_refl _) hclk,
    hu.sinv.mono (fun _ => rfl) (fun _ => rfl) rfl hu.sinv.pst (fun _ h => .inl h) hclk
      (fun _ h => h) rfl (fun _ h => h) (fun _ h => .inl h) hhS,
    hu.lg.congr (fun _ => rfl) (fun _ => rfl) hhS hhE hu.lg.wtx
      (fun j hj => by
        rw [hhE] at hj ⊢
        exact (hu.lg.ehb j hj).mono (fun _ h => .inl h) hclk (fun _ h => h) rfl (fun _ h => h))⟩

/-- **`io` is in the protocol's rest** (the obligation of `FLock.Fits.wp_readRest`, the read of
`io`): its bytes, which decode to `io`, at the `SemCounter`'s 8-aligned address. -/
theorem io_rest (G : ThreadId → Gh) (rX : Res) (m : Mem) (hu : U G rX m) :
    ∃ r A S K' bs, up (bytesAt cPtr A S K' bs) r ∧
      (∀ l fc, r.heap l = some fc → rX.heap l = some fc) ∧ bs.size = Enc.size Io ∧
      Enc.decode bs = pure (⟨⟩ : Io) ∧ (A + cPtr.off.toNat) % 8 = 0 ∧ K' ≠ .constGlobal := by
  obtain ⟨rIO, ⟨A, bs, hA, hbs, hdec, r₁, r₂, -, rfl, h₁, -⟩, hIOoff, hrX⟩ := hu.um.rest
  refine ⟨r₁, A, _, _, bs, h₁, fun l fc hl => ?_, by rw [hbs]; rfl, hdec, ?_, by decide⟩
  · have hb : ¬ BoxW l := fun hb => by
      have := hIOoff l hb; simp [FHeap.union_apply, hl] at this
    rw [hrX]; simp [FHeap.union_apply, cellsAt_none hb, hl]
  · simpa [cPtr] using hA

/-- `io`'s accesses cover its bytes (`FLock.Fits.wp_readRest`). -/
theorem io_cov : Conc.Covers IoR 0 cPtr.off.toNat (Enc.size Io) :=
  fun _ hb hl _ h2 => ⟨hb, hl, by
    have : Enc.size Io = 16 := rfl
    simp [cPtr] at h2; omega⟩

/-! ## The threads -/

theorem upd0_1 (G : ThreadId → Gh) (g : Gh) : upd G 0 g 1 = G 1 := upd_ne _ _ (by decide)
theorem upd1_0 (G : ThreadId → Gh) (g : Gh) : upd G 1 g 0 = G 0 := upd_ne _ _ (by decide)

/-- `main` spawned every thread. -/
theorem spawners {Y : ThreadId → Ph} {m : Mem} (h : Shape Y m) : ∀ r ∈ m.threads, r.spawner = 0 :=
  spawners_of_getElem fun i hi => by
    obtain ⟨h0, ⟨h1, -⟩ | ⟨h2, h1, -⟩⟩ := h
    · obtain rfl : i = 0 := by omega
      rw [Array.getElem?_eq_getElem hi] at h0; rw [Option.some.inj h0]
    · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · rw [Array.getElem?_eq_getElem hi] at h0; rw [Option.some.inj h0]
      · rw [Array.getElem?_eq_getElem hi] at h1; rw [Option.some.inj h1]

/-- The invariant at a stop of a live thread `t`. -/
theorem inv_cur {G : ThreadId → Gh} {m : Mem} (t : ThreadId) (hi : (proto semOf).inv G m)
    (hph : (G t).1.ph ≠ .gone) : (proto semOf).inv G { m with current := t } := by
  obtain ⟨-, -, -, h⟩ := (fits (semOf := semOf)).cur t hi hph
  exact h

/-- `R` reads only whether a thread has the permit and the increments. -/
theorem R_eq_of {Y Y' : ThreadId → X} (hh : held (fun u => (Y' u).ph) = held (fun u => (Y u).ph))
    (hs : sum (fun u => (Y' u).ph) = sum (fun u => (Y u).ph)) : R Y' = R Y := by
  unfold R pv Pool; rw [hh, hs]

/-- A thread out of the condition's code gets another ghost value out of it, at the same memory
(`FCond.Inv.frame`). -/
theorem cinv_out {G : ThreadId → Gh} {m : Mem} {t : ThreadId} {g : Gh}
    (hI : C.Inv L G m) (h₀ : (G t).2.c = .out) (h₁ : g.2.c = .out) :
    C.Inv L (upd G t g) m := by
  have hcg : C.ph g = .out := h₁
  have hct : C.ph (G t) = .out := h₀
  refine hI.frame rfl rfl rfl (fun w hw _ _ => hw) (Nat.le_refl _) (fun _ => VClock.le_refl _)
    (fun h => by rw [hcg, hct] at h; rcases h with h | h <;> cases h)
    (fun _ _ h => by rw [hcg] at h; cases h) (fun _ _ _ _ h => by rw [hcg] at h; cases h)
    (fun h => by obtain ⟨_, _, _, h'⟩ := hI.qd_reg h; rw [hct] at h'; cases h')
    (fun h => by rw [hcg] at h; cases h) (fun h => by rw [hcg] at h; cases h)
    (fun h => absurd hcg h)
    (hI.cnt_frame rfl rfl (fun _ => rfl) (fun _ _ _ h => h) (by rw [hcg, hct]) (by rw [hcg, hct])
      (by simp [FCond.cl, hcg, hct, FCond.regCl, CPh.incN]))

/-- **A change of `t`'s part keeps `U`**, at the same memory: the places stay. -/
theorem U_part {G : ThreadId → Gh} {rX : Res} {m : Mem} {t : ThreadId} {r : Res} (hu : U G rX m) :
    U (upd G t (L.setPart (G t) r)) rX m := by
  have hX : ∀ u, (upd G t (L.setPart (G t) r) u).2 = (G u).2 := fun u => by
    by_cases e : u = t
    · subst e; rw [upd_self]; rfl
    · rw [upd_ne _ _ e]
  have hP : ∀ u, (upd G t (L.setPart (G t) r) u).1.ph = (G u).1.ph := fun u => by
    by_cases e : u = t
    · subst e; rw [upd_self]; rfl
    · rw [upd_ne _ _ e]
  have hxs : xs (upd G t (L.setPart (G t) r)) = xs G := funext fun u => congrArg X.ph (hX u)
  have hcnt : S.cnt (upd G t (L.setPart (G t) r)) = S.cnt G := by
    show pv (xs _) = pv (xs _); rw [hxs]
  refine ⟨⟨by rw [hxs]; exact hu.um.shape, hu.um.io, hu.um.rest, hu.um.blk, hu.um.ws, hu.um.we,
      hu.um.q⟩,
    hu.cinv.other rfl (fun _ => rfl) (fun _ h => h) id rfl rfl rfl (fun w hw _ => .inl hw)
      (fun _ _ _ h => h) (Nat.le_refl _) (fun _ => VClock.le_refl _),
    hu.sinv.mono (fun u => congrArg X.sp (hX u)) (fun u => congrArg X.c (hX u)) hcnt
      (fun u h => by show (upd G t _ u).1.ph = _; rw [hP u]; exact hu.sinv.pst u h)
      (fun u h => .inl (by show ((upd G t _ u).1.ph).held = _; rw [hP u]; exact h))
      (fun _ => VClock.le_refl _) (fun _ h => h) rfl
      (fun u h => by show (G u).1.ph ≠ _; rw [← hP u]; exact h) (fun _ h => .inl h) rfl,
    hu.lg.congr (fun u => congrArg X.ph (hX u)) (fun u => congrArg X.c (hX u)) rfl rfl
      (fun u h => by rw [hX u] at h ⊢; exact hu.lg.wtx u h)
      (fun j hj => hb_same hP (hu.lg.ehb j hj))⟩

/-! ## The spawn -/

/-- A fork by `t` moves no thread's clock back. -/
theorem clk_fork {cs : Array VClock} {t : ThreadId} (ht : t < cs.size) (u : ThreadId) :
    VClock.le (cs[u]!) (((cs.set! t (VClock.bump (cs[t]!) t)).push
      (VClock.bump (cs[t]!) t))[u]!) = true := by
  by_cases hu : u < cs.size
  · exact (Conc.fork_clocks ht).1 u hu
  · rw [getElem!_neg cs u hu]; exact VClock.le_default _

/-- **`HB` over a spawn by `main`**: the kid's clock is above `main`'s, so a clock below every
thread that has not ended is below the kid's too. -/
theorem hb_fork {G G' : ThreadId → Gh} {m m' : Mem} {c : VClock} (h : L.HB G m c)
    (hcl : ∀ u : ThreadId, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (hnew : VClock.le (m.clocks[0]!) (m'.clocks[m.threads.size]!) = true)
    (hsz : m'.threads.size = m.threads.size + 1) (hbef : ∀ c, L.Before m c → L.Before m' c)
    (hhold : ∀ u, (L.ph (G u)).held = true → (L.ph (G' u)).held = true)
    (h0 : 0 < m.threads.size) (hg0 : L.ph (G 0) ≠ .gone)
    (hgone : ∀ u, u < m.threads.size → L.ph (G' u) ≠ .gone → L.ph (G u) ≠ .gone) :
    L.HB G' m' c := by
  rcases h with ⟨u, hu, hle⟩ | hb | hlive
  · exact .inl ⟨u, hhold u hu, VClock.le_trans hle (hcl u)⟩
  · exact .inr (.inl (hbef c hb))
  · refine .inr (.inr fun u hu hg => ?_)
    by_cases hu' : u < m.threads.size
    · exact VClock.le_trans (hlive u hu' (hgone u hu' hg)) (hcl u)
    · obtain rfl : u = m.threads.size := by omega
      exact VClock.le_trans (hlive 0 h0 hg0) hnew

/-- **The semaphore's invariant over a step that grows the threads** (a spawn): `FSem.Inv.mono`
with the threads' growth and `HB` over the step given. -/
theorem sinv_grow {G G' : ThreadId → Gh} {m m' : Mem} (hI : S.Inv G m)
    (hsph : ∀ u, S.ph (G' u) = S.ph (G u)) (hcph : ∀ u, C.ph (G' u) = C.ph (G u))
    (hpv : S.cnt G' = S.cnt G)
    (hpst : ∀ u, (S.ph (G u)).isPst → L.ph (G' u) = .holds)
    (hHB : ∀ c, L.HB G m c → L.HB G' m' c)
    (hcl : ∀ u : ThreadId, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (ht : m.threads.size ≤ m'.threads.size)
    (hwq : ∀ w ∈ m'.waiters, w ∈ m.waiters ∨ w.2 = L.ptr)
    (hS : C.S.hist m' = C.S.hist m) : S.Inv G' m' := by
  have hTk : ∀ v, S.Tk G' v ↔ S.Tk G v := fun v => by unfold FSem.Tk; rw [hsph, hcph]
  have hlast : C.lastS m' = C.lastS m := by unfold FCond.lastS; rw [hS]
  refine ⟨fun u hu => ?_, fun u hu => hpst u (by rw [← hsph u]; exact hu),
    fun u hu => by rw [hpv]; exact hI.crit u (by rw [← hcph u]; exact hu),
    fun u hu => by rw [hsph]; exact hI.wt u (by rw [← hcph u]; exact hu),
    fun u v hu hv => hI.cp u v (by rw [← hcph u]; exact hu) (by rw [← hsph v]; exact hv),
    fun w hw hk => ?_, fun p h0 hp => ?_, fun u h c hu => ?_, fun u h c hu p h0 hp => ?_,
    fun u h c hu p h0 hp => ?_, fun hc hpw => ?_⟩
  · exact Nat.lt_of_lt_of_le (hI.ex u (by rw [← hsph u]; exact hu)) ht
  · rcases hwq w hw with hw | hw
    · exact hI.tq w hw ((hTk _).mp hk)
    · exact hw
  · rw [hS] at hp ⊢
    rcases hI.hw p h0 hp with h | h | ⟨u, hu, hle⟩
    · exact .inl h
    · exact .inr (.inl (hHB _ h))
    · exact .inr (.inr ⟨u, (hTk u).mpr hu, VClock.le_trans hle (hcl u)⟩)
  · obtain ⟨⟨r, hr⟩, hc⟩ := hI.sp u h c (by rw [← hsph u]; exact hu)
    exact ⟨⟨r, by rw [hS]; exact hr⟩, VClock.le_trans hc (hcl u)⟩
  · rcases hI.sb u h c (by rw [← hsph u]; exact hu) p h0 hp with h | h | ⟨v, hv⟩
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr ⟨v, (hTk v).mpr hv⟩)
  · rw [hS] at hp ⊢
    rcases hI.sa u h c (by rw [← hsph u]; exact hu) p h0 hp with h | ⟨v, hv⟩
    · exact .inl h
    · exact .inr ⟨v, (hTk v).mpr hv⟩
  · rw [hlast] at hpw ⊢
    rcases hI.live (by rwa [← hpv]) hpw with h | ⟨u, hu⟩ | ⟨v, hv⟩
    · exact .inl h
    · exact .inr (.inl ⟨u, by rw [hsph]; exact hu⟩)
    · exact .inr (.inr ⟨v, (hTk v).mpr hv⟩)

/-- Spawn after the parent's caller part has been split: the kid gets the copied plain part, and
both threads go to `semWork` with no increment and no permit. -/
theorem inv_spawnParts {G : ThreadId → Gh} {m m' : Mem} {c : ThreadId} {rM rP : Res}
    (hP : plain rP) (hi : (proto semOf).inv G m) (hg : G 0 = gO (rsum rM rP) { ph := .pre })
    (hf : (Thread.fork.run { m with current := 0 }).run = some (.ok (c, m'))) :
    c = 1 ∧ m'.current = 0 ∧
      (proto semOf).inv (upd (upd G 1 (gW rP 0 false 0)) 0 (gW rM 0 false 0)) m' := by
  obtain ⟨rX, hL, hu⟩ := hi
  obtain ⟨h00, ⟨hs1, -, hnone⟩ | ⟨-, -, h0, -⟩⟩ := hu.um.shape
  rotate_left
  · exfalso
    have e : (G 0).2.ph = .pre := by rw [hg]; rfl
    rcases h0 with h0 | ⟨_, _, _, _, h0⟩ <;> (change (G 0).2.ph = _ at h0; rw [e] at h0; cases h0)
  have hcs : m.clocks.size = m.threads.size := hL.w.csize
  have hG1 : (G 1).2.ph = .none := hnone 1 (Nat.le_refl _)
  have hG1c : (G 1).2.c = .out := Classical.byContradiction fun hne => by
    have := hu.cinv.ex 1 hne; rw [hs1] at this; exact Nat.lt_irrefl _ this
  have hG1s : (G 1).2.sp = .out := Classical.byContradiction fun hne => by
    have := hu.sinv.ex 1 hne; rw [hs1] at this; exact Nat.lt_irrefl _ this
  have hG1L : L.ph (G 1) = .gone := Classical.byContradiction fun hne => by
    have := (hL.w.live 1 hne).1; rw [hs1] at this; exact Nat.lt_irrefl _ this
  have hG0c : (G 0).2.c = .out := by rw [hg]; rfl
  have hG0s : (G 0).2.sp = .out := by rw [hg]; rfl
  have hG0L : L.ph (G 0) = .out := by rw [hg]; rfl
  obtain ⟨hwS, hhS⟩ := hu.um.ws.fork_native (t := 0) (gt := false) (by rw [hs1]; decide) hcs hf
  obtain ⟨hwE, hhE⟩ := hu.um.we.fork_native (t := 0) (gt := false) (by rw [hs1]; decide) hcs hf
  have hfork := hf
  change ((Thread.forkWith false).run { m with current := 0 }).run = some (.ok (c, m')) at hfork
  rw [Proto.forkWith_run] at hfork
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hfork
  -- the client parts: no permit, no increment, before and after
  have hheld0 : held (fun u => (G u).2.ph) = false := by
    show ((G 0).2.ph.holds || (G 1).2.ph.holds) = false
    rw [show (G 0).2.ph = .pre by rw [hg]; rfl, hG1]; rfl
  have hsum0 : sum (fun u => (G u).2.ph) = 0 := by
    show (G 0).2.ph.count + (G 1).2.ph.count = 0
    rw [show (G 0).2.ph = .pre by rw [hg]; rfl, hG1]; rfl
  have hL' := hL.fork (t := 0) (g₁ := gW rM 0 false 0) (g₀ := gW rP 0 false 0)
    hG0L hf (by rw [hg]; rfl)
    (by show rM.heap.Disjoint rP.heap; rw [(plain_ghost hP).1]; exact FHeap.disjoint_empty _)
    rfl rfl rfl rfl fun r hR => by
      rw [← hfork.1, hs1]
      have hR' : R (fun u => (G u).2) r := hR
      show R (fun u => (upd (upd G 1 (gW rP 0 false 0)) 0 (gW rM 0 false 0) u).2) r
      rw [R_eq_of (Y := fun u => (G u).2) (by
          show (((upd (upd G 1 _) 0 _ 0).2.ph).holds || ((upd (upd G 1 _) 0 _ 1).2.ph).holds) = _
          rw [upd_self, upd0_1, upd_self, hheld0]; rfl)
        (by
          show ((upd (upd G 1 _) 0 _ 0).2.ph).count + ((upd (upd G 1 _) 0 _ 1).2.ph).count = _
          rw [upd_self, upd0_1, upd_self, hsum0]; rfl)]
      exact hR'
  obtain ⟨rfl, rfl⟩ := hfork
  have hclk := clk_fork (cs := m.clocks) (t := 0) (by rw [hcs, hs1]; decide)
  obtain ⟨hcl, hcn, -⟩ := Conc.fork_clocks (cs := m.clocks) (t := 0) (by rw [hcs, hs1]; decide)
  -- the new ghost values
  have hX0 : (upd (upd G 1 (gW rP 0 false 0)) 0 (gW rM 0 false 0) 0).2 = { ph := .work 0 false 0 } := by
    rw [upd_self]; rfl
  have hX1 : (upd (upd G 1 (gW rP 0 false 0)) 0 (gW rM 0 false 0) 1).2 = { ph := .work 0 false 0 } := by
    rw [upd0_1, upd_self]; rfl
  have hXu : ∀ u, 2 ≤ u → upd (upd G 1 (gW rP 0 false 0)) 0 (gW rM 0 false 0) u = G u := fun u hu' => by
    rw [upd_ne _ _ (by unfold ThreadId at *; omega), upd_ne _ _ (by unfold ThreadId at *; omega)]
  have h01 : ∀ u, u < 2 → u = 0 ∨ u = 1 := fun u hu' => by unfold ThreadId at *; omega
  have hcph : ∀ u, (upd (upd G 1 (gW rP 0 false 0)) 0 (gW rM 0 false 0) u).2.c = (G u).2.c := fun u => by
    by_cases hu' : u < 2
    · rcases h01 u hu' with rfl | rfl
      · rw [hX0, hG0c]
      · rw [hX1, hG1c]
    · rw [hXu u (by unfold ThreadId at *; omega)]
  have hsph : ∀ u, (upd (upd G 1 (gW rP 0 false 0)) 0 (gW rM 0 false 0) u).2.sp = (G u).2.sp := fun u => by
    by_cases hu' : u < 2
    · rcases h01 u hu' with rfl | rfl
      · rw [hX0, hG0s]
      · rw [hX1, hG1s]
    · rw [hXu u (by unfold ThreadId at *; omega)]
  have hheld1 : held (xs (upd (upd G 1 (gW rP 0 false 0)) 0 (gW rM 0 false 0))) = false := by
    show (((upd (upd G 1 _) 0 _ 0).2.ph).holds || ((upd (upd G 1 _) 0 _ 1).2.ph).holds) = false
    rw [hX0, hX1]; rfl
  have hcnt : S.cnt (upd (upd G 1 (gW rP 0 false 0)) 0 (gW rM 0 false 0)) = S.cnt G := by
    show pv (xs (upd (upd G 1 (gW rP 0 false 0)) 0 (gW rM 0 false 0))) = pv (xs G)
    unfold pv; rw [hheld1, show held (xs G) = false from hheld0]
  have hHB : ∀ c, L.HB G m c → L.HB (upd (upd G 1 (gW rP 0 false 0)) 0 (gW rM 0 false 0))
      { m with
        current := 0,
        clocks := (m.clocks.set! 0 (VClock.bump (m.clocks[0]!) 0)).push (VClock.bump (m.clocks[0]!) 0),
        threads := m.threads.push { spawner := 0, joined := false, gated := false } } c :=
    fun c h => hb_fork h hclk (by rw [← hcs]; exact hcn) (by simp) (fun _ h => h)
      (fun u hh => by
        by_cases hu' : u < 2
        · rcases h01 u hu' with rfl | rfl
          · rw [hG0L] at hh; cases hh
          · rw [hG1L] at hh; cases hh
        · rw [hXu u (by unfold ThreadId at *; omega)]; exact hh)
      (by rw [hs1]; decide) (by rw [hG0L]; decide)
      (fun u hu' _ => by
        rw [hs1] at hu'; obtain rfl : u = 0 := by unfold ThreadId at *; omega
        rw [hG0L]; decide)
  have hI := hu.cinv.stay hhS hhE rfl (fun _ hw _ => hw) (fun _ _ h => h) (by simp) hclk
  have hI' := cinv_out (cinv_out hI (t := 1) (g := gW rP 0 false 0) hG1c rfl)
    (t := 0) (g := gW rM 0 false 0) (by rw [upd1_0]; exact hG0c) rfl
  have hsat := FCond.Sated.congr (C := C) hhS
  refine ⟨hs1, rfl, rX, by rw [hs1] at hL'; exact hL', ⟨⟨⟨?_, .inr ⟨by simp [hs1], ?_,
      .inr ⟨0, by decide, false, 0, by show (upd (upd G 1 _) 0 _ 0).2.ph = _; rw [hX0]⟩,
      .inr ⟨0, by decide, false, 0, by show (upd (upd G 1 _) 0 _ 1).2.ph = _; rw [hX1]⟩,
      fun u hu' => by
        show (upd (upd G 1 _) 0 _ u).2.ph = _
        rw [hXu u hu']; exact hnone u (by unfold ThreadId at *; omega)⟩⟩, ?_,
      hu.um.rest.congr fun _ _ => rfl, hu.um.blk, hwS, hwE, fun w hw => hu.um.q w hw⟩,
    hI', sinv_grow hu.sinv hsph hcph hcnt (fun u h => ?_) hHB hclk (by simp) (fun w hw => .inl hw)
      hhS, ⟨.inl (by rw [hX0]; rfl), fun u k s h => ?_, fun u h => ?_,
      fun k hk => by rw [hhE] at hk ⊢; exact hHB _ (hu.lg.ehb k hk),
      fun u i e h => by rw [hcph u] at h; rw [hhE]; exact hu.lg.f0 u i e h,
      fun u v hr hc' => by rw [hcph u] at hr; rw [hcph v] at hc'; exact hu.lg.rc u v hr hc',
      fun u i jr sn e h => by rw [hcph u] at h; rw [hhE]; exact hu.lg.f2 u i jr sn e h,
      fun u i jr sn e v q n h hu' hv => by
        rw [hcph u] at hu'; rw [hcph v] at hv; rw [hhE]; exact hu.lg.f3 u i jr sn e v q n h hu' hv,
      fun u i jr sn e h hs => by
        rw [hcph u] at h; rw [hhE] at hs; exact hsat.mpr (hu.lg.f4 u i jr sn e h hs),
      fun v q n h hv => by rw [hcph v] at hv; exact hsat.mpr (hu.lg.incS v q n h hv)⟩⟩⟩
  · simp only [Array.getElem?_push]; rw [ite_eq_right (by omega)]; exact h00
  · simp only [Array.getElem?_push, hs1, ↓reduceIte]
  · exact hu.um.io.fork (t := 0) (by rw [hs1]; decide) (by simp)
      (fun u hu' => hcl u (by rw [hcs]; exact hu')) (by rw [← hcs]; exact hcn) fun _ he _ => he
  · -- `pst`: no thread is in the semaphore's code
    by_cases hu' : u < 2
    · rcases h01 u hu' with rfl | rfl
      · rw [show S.ph (G 0) = (G 0).2.sp from rfl, hG0s] at h; cases h
      · rw [show S.ph (G 1) = (G 1).2.sp from rfl, hG1s] at h; cases h
    · show (upd (upd G 1 _) 0 _ u).1.ph = _; rw [hXu u (by unfold ThreadId at *; omega)]; exact hu.sinv.pst u h
  · by_cases hu' : u < 2
    · rcases h01 u hu' with rfl | rfl
      · rw [hX0] at h; cases h
      · rw [hX1] at h; cases h
    · rw [hXu u (by unfold ThreadId at *; omega),
        show (G u).2.ph = .none from hnone u (by unfold ThreadId at *; omega)] at h
      cases h
  · by_cases hu' : u < 2
    · rcases h01 u hu' with rfl | rfl
      · rw [hX0] at h; cases h
      · rw [hX1] at h; cases h
    · rw [hXu u (by unfold ThreadId at *; omega)] at h ⊢; exact hu.lg.wtx u h

/-- `main` copies its duplicable plain mode before spawning; both threads own their plain
parts. -/
theorem inv_spawn {G : ThreadId → Gh} {m m' : Mem} {c : ThreadId} {rM : Res}
    (hp : rM.Plain) (hi : (proto semOf).inv G m) (hg : G 0 = gO rM { ph := .pre })
    (hf : (Thread.fork.run { m with current := 0 }).run = some (.ok (c, m'))) :
    c = 1 ∧ m'.current = 0 ∧ ∃ rP, plain rP ∧
      (proto semOf).inv (upd (upd G 1 (gW rP 0 false 0)) 0 (gW rM 0 false 0)) m' := by
  obtain ⟨rX, hL, hU⟩ := hi
  have hL₀ : L.Inv (upd G 0 (G 0)) rX { m with current := 0 } := by
    rw [upd_same]
    exact hL.cur 0
  obtain ⟨r, ⟨r₁, rP, hd, rfl, hr₁, hpP⟩, hL'⟩ := hL₀.eupdPart (proto semOf) rfl
    (by rw [hg]; exact fun h => nomatch h) (EUpd.plain_split (P := fun r => r = L.part (G 0))
      fun r hr => by rw [hr, hg]; exact hp)
  have hrM : rM = r₁ := by rw [hr₁, hg]; rfl
  subst hrM
  have hU' := U_part (t := 0) (r := rsum rM rP) (atStop 0 hU)
  have hG' : upd G 0 (L.setPart (G 0) (rsum rM rP)) 0 = gO (rsum rM rP) { ph := .pre } := by
    rw [upd_self, hg]; rfl
  obtain ⟨hc, hcur, hi'⟩ := inv_spawnParts (semOf := semOf) hpP
    ⟨rX, by simpa only [upd_upd] using hL', hU'⟩ hG' hf
  refine ⟨hc, hcur, rP, hpP, ?_⟩
  have he : upd (upd (upd G 0 (L.setPart (G 0) (rsum rM rP))) 1 (gW rP 0 false 0))
      0 (gW rM 0 false 0) = upd (upd G 1 (gW rP 0 false 0)) 0 (gW rM 0 false 0) := by
    rw [upd_comm G _ _ (by decide : (0 : ThreadId) ≠ 1), upd_upd]
  rwa [he] at hi'

/-! ## The ends -/

/-- **A thread at the end of `semWork`** (two increments, no permit): `main` to its join, the kid
to its end (`gone`). -/
theorem inv_end {G : ThreadId → Gh} {m : Mem} {t : ThreadId} {g : Gh} {rp : Res}
    (hi : (proto semOf).inv (upd G t (gW rp 2 false 0)) m)
    (hp : (t = 0 ∧ g = gO rp { ph := .joins }) ∨ (t = 1 ∧ g = (⟨.gone, rp, rnil⟩, { ph := .fin }))) :
    (proto semOf).inv (upd G t g) m := by
  obtain ⟨rX, hiL, hU⟩ := hi
  have hgc : g.2.c = .out := by rcases hp with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> rfl
  have hgs : g.2.sp = .out := by rcases hp with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> rfl
  have hgh : g.2.ph.holds = false := by rcases hp with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> rfl
  have hgk : g.2.ph.count = 2 := by rcases hp with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> rfl
  have hne : ∀ u, u ≠ t → upd G t g u = upd G t (gW rp 2 false 0) u := fun u e => by
    rw [upd_ne _ _ e, upd_ne _ _ e]
  have hheld : held (xs (upd G t g)) = held (xs (upd G t (gW rp 2 false 0))) := by
    unfold held xs
    by_cases h0 : t = 0
    · subst h0; rw [upd_self, upd_self, upd0_1, upd0_1, hgh]; rfl
    · rw [hne 0 (Ne.symm h0)]
      by_cases h1 : t = 1
      · subst h1; rw [upd_self, upd_self, hgh]; rfl
      · rw [hne 1 (Ne.symm h1)]
  have hsum : sum (xs (upd G t g)) = sum (xs (upd G t (gW rp 2 false 0))) := by
    unfold sum xs
    by_cases h0 : t = 0
    · subst h0; rw [upd_self, upd_self, upd0_1, upd0_1, hgk]; rfl
    · rw [hne 0 (Ne.symm h0)]
      by_cases h1 : t = 1
      · subst h1; rw [upd_self, upd_self, hgk]; rfl
      · rw [hne 1 (Ne.symm h1)]
  have hl := hiL.ghost (t := t) (g := g) (by rw [upd_self]; rfl)
    (by rcases hp with ⟨-, rfl⟩ | ⟨-, rfl⟩
        · exact .inl rfl
        · exact .inr (.inl rfl))
    (by rw [upd_self]; rcases hp with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> rfl)
    (by rcases hp with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> rfl)
    (fun _ => hiL.ht (by rw [upd_self]; exact (by decide : LPh.out ≠ LPh.gone)))
    (fun r hR => by
      have hR' : R (fun u => (upd G t (gW rp 2 false 0) u).2) r := hR
      show R (fun u => (upd (upd G t (gW rp 2 false 0)) t g u).2) r
      rw [upd_upd, R_eq_of (Y := fun u => (upd G t (gW rp 2 false 0) u).2) hheld hsum]; exact hR')
  rw [upd_upd] at hl
  have hX : ∀ u, u ≠ t → (upd G t g u).2 = (upd G t (gW rp 2 false 0) u).2 := fun u e => by
    rw [hne u e]
  have hcph : ∀ u, (upd G t g u).2.c = (upd G t (gW rp 2 false 0) u).2.c := fun u => by
    by_cases e : u = t
    · subst e; rw [upd_self, upd_self, hgc]; rfl
    · rw [hX u e]
  have hsph : ∀ u, (upd G t g u).2.sp = (upd G t (gW rp 2 false 0) u).2.sp := fun u => by
    by_cases e : u = t
    · subst e; rw [upd_self, upd_self, hgs]; rfl
    · rw [hX u e]
  have hlph : ∀ u, (upd G t g u).1.ph ≠ .gone → (upd G t (gW rp 2 false 0) u).1.ph ≠ .gone :=
    fun u h => by
      by_cases e : u = t
      · subst e; rw [upd_self]; exact (by decide : LPh.out ≠ LPh.gone)
      · rw [hne u e] at h; exact h
  have hhold : ∀ u, (upd G t (gW rp 2 false 0) u).1.ph = .holds → (upd G t g u).1.ph = .holds :=
    fun u h => by
      by_cases e : u = t
      · subst e; rw [upd_self] at h; cases h
      · rw [hne u e]; exact h
  have hlheld : ∀ u, ((upd G t (gW rp 2 false 0) u).1.ph).held = true →
      ((upd G t g u).1.ph).held = true := fun u h => by
    by_cases e : u = t
    · subst e; rw [upd_self] at h; cases h
    · rw [hne u e]; exact h
  have hcnt : S.cnt (upd G t g) = S.cnt (upd G t (gW rp 2 false 0)) := by
    show pv (xs _) = pv (xs _); unfold pv; rw [hheld]
  have hshape := hU.um.shape
  have ht2 := (hshape.lt (u := t) (k := 2) (b := false) (s := 0)
    (by show (upd G t (gW rp 2 false 0) t).2.ph = _; rw [upd_self]; rfl))
  have hsh : Shape (xs (upd G t g)) m := by
    obtain ⟨h0, ⟨hsz, hy0, -⟩ | ⟨hsz, h1, hm, hk, hyu⟩⟩ := hshape
    · exfalso; rw [ht2.2] at hsz; cases hsz
    refine ⟨h0, .inr ⟨hsz, h1, ?_, ?_, fun u hu => ?_⟩⟩
    · rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact .inl (by show (upd G 0 _ 0).2.ph = _; rw [upd_self] <;> rfl)
      · show (upd G 1 _ 0).2.ph = .joins ∨ _
        rw [upd1_0]; have := hm; rwa [show xs (upd G 1 (gW rp 2 false 0)) 0 = (G 0).2.ph from by
          show (upd G 1 _ 0).2.ph = _; rw [upd1_0]] at this
    · rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · show (upd G 0 _ 1).2.ph = .fin ∨ _
        rw [upd0_1]; have := hk; rwa [show xs (upd G 0 (gW rp 2 false 0)) 1 = (G 1).2.ph from by
          show (upd G 0 _ 1).2.ph = _; rw [upd0_1]] at this
      · exact .inl (by show (upd G 1 _ 1).2.ph = _; rw [upd_self] <;> rfl)
    · have e : u ≠ t := by have := ht2.1; unfold ThreadId at *; omega
      show (upd G t g u).2.ph = _; rw [hne u e]; exact hyu u hu
  refine ⟨rX, hl, ⟨hsh, hU.um.io, hU.um.rest, hU.um.blk, hU.um.ws, hU.um.we, hU.um.q⟩,
    by have := cinv_out (t := t) (g := g) hU.cinv (by rw [upd_self]; rfl) hgc
       rwa [upd_upd] at this,
    hU.sinv.mono hsph hcph hcnt
      (fun u h => hhold u (hU.sinv.pst u h)) (fun u h => .inl (hlheld u h))
      (fun _ => VClock.le_refl _) (fun _ h => h) rfl hlph (fun _ h => .inl h) rfl,
    hU.lg.relabel hcph rfl rfl ?_ ?_ ?_
      (fun j hj => (hU.lg.ehb j hj).mono (fun u h => .inl (hlheld u h)) (fun _ => VClock.le_refl _)
        (fun _ h => h) rfl hlph)⟩
  · by_cases h0 : t = 0
    · subst h0; exact .inl (by rw [upd_self]; exact hgh)
    · have h1 : t = 1 := by have := ht2.1; unfold ThreadId at *; omega
      subst h1; exact .inr (by rw [upd_self]; exact hgh)
  · intro u k s h
    by_cases e : u = t
    · subst e; rw [upd_self] at h; rw [h] at hgh; cases hgh
    · rw [hne u e] at h; rw [hsum]; exact hU.lg.tot u k s h
  · intro u h
    by_cases e : u = t
    · subst e; rw [upd_self, hgs] at h; cases h
    · rw [hne u e] at h ⊢; exact hU.lg.wtx u h

/-- **The kid's end** (`QKid`): it is `gone` at `fin` and spawned no thread. -/
theorem qkid {G : ThreadId → Gh} {m : Mem} {d : Nat} {rp : Res}
    (hi : (proto semOf).inv (upd G 1 (gW rp 2 false 0)) m) : (proto semOf).QKid 1 () G m d := by
  have hi' := inv_end hi (.inr ⟨rfl, rfl⟩)
  refine ⟨_, hi', ⟨rfl, rfl⟩, fun _ => ?_⟩
  obtain ⟨rX, -, hu⟩ := hi'
  exact joinedAll_of_main (spawners hu.um.shape) (by decide)

/-- **`main`'s join of the kid** at `joins`: then it takes the lock's resource back
(`FLock.Inv.take`): the count 1 and `n`, which is 4 (both threads did two increments); every
thread is joined, the `SemCounter` is block 0 and every clock is below `main`'s. -/
theorem wp_join {σ : Type} {s : σ} {G : ThreadId → Gh} {m : Mem} {n : Nat} {rp : Res}
    (hi : (proto semOf).inv (upd G 0 (gO rp { ph := .joins })) m)
    {Q : Unit × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ k G₁ m' (own : ThreadId → Res) (rX r : Res), n = k + 1 → m'.current = 0 →
      FOwned (upd own 0 r) rX m' →
      ((fun r => r = own 0) ⋆ ((up (pts (cPtr.add 16) 8 (1 : BitVec 64)) ⋆
        up (pts nPtr 4 (BitVec.ofNat 32 4))) ⋆ fun r => r = L.wordR m')) r →
      BlkOk m' → m'.ClocksLe → joinedAll 0 m' → m'.threads.size = 2 → Q ((), s) G₁ m' k) :
    (proto semOf).WP 0 ((joinC 1 : CM Tgt σ Unit).run s) Q G m n := by
  refine WP.joinC fun k hk => ⟨_, hi, fun G₁ m₁ hg hi₁ => ?_⟩
  obtain ⟨rX, hL, hu⟩ := hi₁
  obtain ⟨h00, ⟨-, h0, -⟩ | ⟨hs2, hr1, -⟩⟩ := hu.um.shape
  · exfalso; change (G₁ 0).2.ph = _ at h0; rw [hg] at h0; cases h0
  refine ⟨fun _ => ⟨by show (0 : Nat) < 1; decide, by rw [hs2]; decide, ⟨rfl, rfl⟩,
    by simp [Thread.joinValid, Mem.isGated, hr1]⟩, fun hfin => ⟨fun _ =>
    join_run (m := { m₁ with current := 0 }) hr1 rfl rfl, fun m' hj => ?_⟩⟩
  have hcs : m₁.clocks.size = 2 := by rw [hL.w.csize, hs2]
  have hcl := Mem.ClocksLe.join2 hj hcs
  obtain ⟨rec, -, -, hm'⟩ := join_eq hj
  have hc' : m'.current = 0 := by rw [hm']
  have hth : m'.threads = m₁.threads.set! 1 { rec with joined := true } := by rw [hm']
  have hs2' : m'.threads.size = 2 := by rw [hth, Array.size_set!, hs2]
  -- `main` takes the kid's entire part, with its copied plain fragments
  let g := gO (rsum rp (L.own G₁ m₁ 1)) { ph := .joins }
  have hX : (fun u => (upd G₁ 0 g u).2) = fun u => (G₁ u).2 := by
    funext u
    by_cases e : u = 0
    · subst e; rw [upd_self, hg]; rfl
    · rw [upd_ne _ _ e]
  have hL' := hL.join (t := 0) (u := 1) (g := g) (by decide) (by decide) (by rw [hg]; rfl)
    hfin.1 hj (by rw [hg]; rfl) rfl rfl (fun r hR => by
      show R (fun u => (upd G₁ 0 g u).2) r
      rw [hX]; exact hR)
  have hF : L.Free (upd G₁ 0 g) := by
    intro u hu'
    by_cases h0 : u = 0
    · subst h0; simp only [FLock.pl, upd_self] at hu'; cases hu'
    · by_cases h1 : u = 1
      · subst h1; simp only [FLock.pl, upd_ne _ _ (by decide : (1 : ThreadId) ≠ 0)] at hu'
        rw [show L.ph (G₁ 1) = .gone from hfin.1] at hu'; cases hu'
      · have := (hL'.w.live u (LPh.ne_gone_of_held hu')).1
        rw [hs2'] at this; unfold ThreadId at *; omega
  have hall : ∀ u < m'.threads.size, VClock.le (m'.clocks[u]!) (m'.clocks[0]!) = true :=
    fun u hu' => by
      have := hcl u (by rw [hL'.w.csize]; exact hu'); rwa [hc'] at this
  obtain ⟨rL, hR, hsep, ho⟩ := hL'.take (t := 0) hF
    (by rw [upd_self]; exact (by decide : LPh.out ≠ LPh.gone)) hall
  have hR4 : (up (pts (cPtr.add 16) 8 (1 : BitVec 64)) ⋆ up (pts nPtr 4 (BitVec.ofNat 32 4))) rL := by
    have hR' : R (fun u => (upd G₁ 0 g u).2) rL := hR
    rw [hX] at hR'
    have hh : held (fun u => (G₁ u).2.ph) = false := by
      show ((G₁ 0).2.ph.holds || (G₁ 1).2.ph.holds) = false
      rw [hg, hfin.2]; rfl
    have h4 : sum (fun u => (G₁ u).2.ph) = 4 := by
      show (G₁ 0).2.ph.count + (G₁ 1).2.ph.count = 4
      rw [hg, hfin.2]; rfl
    change (up (pts (cPtr.add 16) 8 (pv fun u => (G₁ u).2.ph)) ⋆ Pool fun u => (G₁ u).2.ph) rL at hR'
    unfold pv Pool at hR'; rw [hh, h4] at hR'; exact hR'
  refine h k G₁ m' _ rX _ hk hc' ho (sep_mono_right (fun _ h => sep_mono_left
    (fun r (h : r = rL) => by subst h; exact hR4) h) hsep) (blk_of hL' hu.um.rest) hcl
    (fun r hr hsp => ?_) hs2'
  simp only [hth] at hr
  obtain ⟨i, hi', rfl⟩ := Array.mem_iff_getElem.mp hr
  simp only [Array.size_set!] at hi'
  simp only [Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds hi'] at hsp ⊢
  split
  · rfl
  · obtain rfl : i = 0 := by omega
    rw [Array.getElem?_eq_getElem (by omega)] at h00
    rw [Option.some.inj h00]

/-- **`main`'s free of the `SemCounter`** after its join: its end races with no access. -/
theorem wp_free {G : ThreadId → Gh} {m : Mem} {n : Nat} (hb : BlkOk m) (hcl : m.ClocksLe)
    {Q : Unit → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ m', m'.threads = m.threads → Q () G m' n) :
    (proto semOf).WP 0 (ConcM.liftMem (free cPtr) : ConcM Tgt Unit) Q G m n := by
  obtain ⟨blk, hblk, hl, -, hk⟩ := hb
  refine WP.liftMem (fun e he => (free_noErr hblk hl (hcl.freeRaces _ _) (by rw [hk]; nofun) e
    he).elim) fun _ m' hfr => ?_
  obtain ⟨b', blk', -, -, rfl⟩ := free_ok hfr
  exact ⟨rfl, h _ rfl⟩

end SemCounter
end Zig
