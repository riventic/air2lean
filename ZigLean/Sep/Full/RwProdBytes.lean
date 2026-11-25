import ZigLean.Sep.Full.RwProdStart
import ZigLean.Sep.Full.BytesCut

/-!
# The start of a program with a reader/writer lock, from the lock's bytes

(ledger #two-lock-product, item (5).) `RwProd.start` (`ZigLean/Sep/Full/RwProdStart.lean`) takes
the start thread's part already split into the lock's words, the protected resource and the rest.
A program has something else right after its stores: its start thread owns the block that holds
the lock as bytes, with the block's extent. This file does the split once for every program.

- `RwProd.start_bytes`: thread `t` owns the bytes `bs` of block `b` from its start, the block's
  full extent and the rest of its part `Q`. The 40 bytes of the lock at `o` are a fresh
  `Io.RwLock`: the state word (`o`), the semaphore's count (`o + 8`), its mutex (`o + 16`), the
  condition's state (`o + 20`) and the outer mutex (`o + 32`) encode `0`, the epoch (`o + 24`)
  any value. Then `t`'s part is some `rM` with `Q`, and for every ghost value `G` with that part
  the invariant holds. The program says what the bytes before and after the lock are (`hrest`:
  the protected resource `R` and the rest `I`, which holds the bytes every thread reads, `hI`);
  the lock's two paddings and the block's extent go to the rest.
-/

namespace Zig
namespace Full

open FAssn Conc Proto

namespace RwProd

variable {Xc : Type} {b o : Nat} {R : (ThreadId → Xc) → FAssn}
  {R_plain : ∀ xs r, R xs r → r.know = Know.none ∧ r.gh = Ghost.unit}
  {R_fixed : ∀ xs, (R xs).FixedDom} {E : FClient Xc} {Sz : Nat} {K : BlockKind}

/-- The pointer `k` bytes after the block's start. -/
theorem p_add (b k : Nat) : (p b 0).add (k : Int) = p b k := by simp [p, Ptr.add]

theorem p_off (b k : Nat) : (p b k).off.toNat = k := Int.toNat_natCast k

/-- The pieces of the block in the order of the invariant: the start thread's part, the outer
mutex's word, the count and the semaphore's mutex's word, the three words of the rest, the bytes
outside the lock, the paddings and the extent. -/
private theorem regroup {Pre St Cnt WL S Ep P1 WM P2 Suf bx Q : FAssn} :
    (((Pre ⋆ (St ⋆ (Cnt ⋆ (WL ⋆ (S ⋆ (Ep ⋆ (P1 ⋆ (WM ⋆ (P2 ⋆ Suf))))))))) ⋆ bx) ⋆ Q) =
      (Q ⋆ (WM ⋆ ((Cnt ⋆ WL) ⋆ ((St ⋆ (S ⋆ Ep)) ⋆ ((Pre ⋆ Suf) ⋆ ((P1 ⋆ P2) ⋆ bx)))))) := by
  ac_rfl

private theorem rsum_heap_ne {a c : Res} {l : Zig.Loc} :
    (rsum a c).heap l ≠ none ↔ a.heap l ≠ none ∨ c.heap l ≠ none := by
  rw [ne_eq, rsum_heap_none]; exact Classical.not_and_iff_not_or_not

/-- **The start of a program with a reader/writer lock, from the lock's bytes** (module doc). -/
theorem start_bytes {own : ThreadId → Res} {rO : Res} {m : Mem} {t : ThreadId} {A : Nat}
    {bs : Array Byte} {Q : FAssn} {e0 : BitVec 32}
    (ho : FOwned own rO m) (hjt : joinedB m t = false) (ht : t < m.threads.size)
    (hF : ((up (bytesAt (p b 0) A Sz K bs) ⋆ bext b Sz K) ⋆ Q) (own t))
    (hsz : o + 40 ≤ bs.size) (hal : (A + o) % 8 = 0) (hK : K ≠ .constGlobal)
    (hlo : K.mappedLo ≤ o)
    (hst : bs.extract o (o + 8) = Enc.encode (0 : BitVec 64))
    (hcnt : bs.extract (o + 8) (o + 16) = Enc.encode (0 : BitVec 64))
    (hL : bs.extract (o + 16) (o + 20) = Enc.encode (0 : BitVec 32))
    (hS : bs.extract (o + 20) (o + 24) = Enc.encode (0 : BitVec 32))
    (hEp : bs.extract (o + 24) (o + 28) = Enc.encode e0)
    (hM : bs.extract (o + 32) (o + 36) = Enc.encode (0 : BitVec 32))
    (hat : ∀ l ∈ m.atomics, l.block = b → o + 40 ≤ l.off ∨ (l.off < o ∧ l.off + l.len ≤ o))
    (hq : m.waiters = #[])
    (hall : AllLe m (m.clocks[t]!)) :
    ∃ rM, Q rM ∧ ∀ (G : ThreadId → Gh Xc) (I : FAssn), (G t).1.part = rM →
      (∀ u, u ≠ t → (M b o).own G m u = own u) →
      (∀ r, (up (bytesAt (p b 0) A Sz K (bs.extract 0 o)) ⋆
          up (bytesAt (p b (o + 40)) A Sz K (bs.extract (o + 40) bs.size))) r →
        (R (fun u => (G u).2.x) ⋆ I) r) →
      (∀ r, I r → ∃ r', E.Io r' ∧ ∀ l fc, r'.heap l = some fc → r.heap l = some fc) →
      (∀ u, (G u).2.w = .out ∧ (G u).2.c = .out ∧ (G u).2.sp = .out ∧
        (G u).1.heldA = rnil ∧ (G u).1.heldB = rnil) →
      (∀ u, ((G u).1.phA = .out ∧ u < m.threads.size ∧ joinedB m u = false) ∨
        (G u).1.phA = .gone) →
      (∀ u, ((G u).1.phB = .out ∧ u < m.threads.size ∧ joinedB m u = false) ∨
        (G u).1.phB = .gone) →
      E.T (fun u => (G u).2.x) m.threads →
      ∃ rX, (M b o).Inv G rX m ∧
        FLock.Pair.U (L b o R) ((W b o R R_plain R_fixed).Base E Sz K) G rX m := by
  -- the block and its bytes
  obtain ⟨blk, hb, hlv, hA, hSz, hKd, hx⟩ :=
    ho.bytesOf ht (rfl : (p b 0).block = some b) (by omega) hF
  rw [p_off, Nat.zero_add] at hx
  have hle : bs.size ≤ blk.bytes.size := by
    have := congrArg Array.size hx
    simp only [Array.size_extract] at this; omega
  have hcur : ∀ x n, x + n ≤ bs.size → curBytes m b x n = bs.extract x (x + n) := fun x n h => by
    have := congrArg (·.extract x (x + n)) hx
    simp only [Array.extract_extract] at this
    unfold curBytes; rw [hb]
    simp only [Option.map_some, Option.getD_some]
    rw [← this]; congr 1 <;> omega
  have hs4 : ∀ v : BitVec 32, (Enc.encode v).size = 4 := fun v => LawfulEnc.size_encode v
  have hs8 : ∀ v : BitVec 64, (Enc.encode v).size = 8 := fun v => LawfulEnc.size_encode v
  have hu32 : ∀ x (v : BitVec 32), x + 4 ≤ bs.size → bs.extract x (x + 4) = Enc.encode v →
      (intOfBytes 32 (curBytes m b x 4)).run = some (.ok v) := fun x v h e => by
    rw [hcur x 4 h, e]; exact intOfBytes_rmw v
  -- the pieces
  have hc := sep_mono_left (fun _ h => sep_mono_left (fun _ h => up_bytesAt_cuts0
    (l := [o, o + 8, o + 16, o + 20, o + 24, o + 28, o + 32, o + 36, o + 40]) h
    ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      hsz⟩) h) hF
  simp only [bytesCut, p_add] at hc
  rw [regroup, hst, hcnt, hL, hS, hEp, hM] at hc
  obtain ⟨rM, _, hdP, e, hQ, rWM, _, hdAB, rfl, hWM, _, _, hdBY, rfl,
    ⟨rCnt, rWL, hdB, rfl, hCn, hWL⟩, rYw, _, hdY, rfl, hYw, rPS, rX, hdPX, rfl, hPS, hX⟩ := hc
  have hYu := sep_up (sep_mono_right (fun _ => sep_up) hYw)
  obtain ⟨rSt, _, -, rfl, hSt, rS, rEp, -, rfl, hS1, hEp1⟩ := hYw
  refine ⟨rM, hQ, fun G I hGp hown hrest hI hG hphA hphB hthr => ?_⟩
  obtain ⟨rR, rIp, hdRI, rfl, hR, hIp⟩ := hrest _ hPS
  obtain ⟨r', hr', hsub⟩ := hI _ hIp
  have e' : own t = rsum rM (rsum rWM (rsum (rsum rCnt rWL)
      (rsum (rsum rSt (rsum rS rEp)) (rsum (rsum rR rIp) rX)))) := e
  have hdP' : FHeap.Disjoint rM.heap (rsum rWM (rsum (rsum rCnt rWL)
      (rsum (rsum rSt (rsum rS rEp)) (rsum (rsum rR rIp) rX)))).heap := hdP
  have hdAB' : FHeap.Disjoint rWM.heap (rsum (rsum rCnt rWL)
      (rsum (rsum rSt (rsum rS rEp)) (rsum (rsum rR rIp) rX))).heap := hdAB
  have hdBY' : FHeap.Disjoint (rsum rCnt rWL).heap
      (rsum (rsum rSt (rsum rS rEp)) (rsum (rsum rR rIp) rX)).heap := hdBY
  have hdY' : FHeap.Disjoint (rsum rSt (rsum rS rEp)).heap (rsum (rsum rR rIp) rX).heap := hdY
  have hdPX' : FHeap.Disjoint (rR.heap ∪ rIp.heap) rX.heap := hdPX
  have h0 : RwState.encode 0 0 false = (0 : BitVec 64) := rfl
  refine start (rO := rO) (rWM := rWM) (rCnt := rCnt) (rWL := rWL)
    (rYw := rsum rSt (rsum rS rEp)) (rR := rR) (rI := rsum rIp rX) (e0 := e0) ho hjt ht hown
    (by rw [hGp, rnil_rsum, ← rsum_assoc (a := rR)]; exact e')
    (by rw [hGp, rnil_rsum, ← rsum_assoc (a := rR)]; exact hdP')
    (by rw [rnil_rsum, ← rsum_assoc (a := rR)]; exact hdAB')
    hdB (by rw [← rsum_assoc (a := rR)]; exact hdBY')
    (by rw [← rsum_assoc (a := rR)]; exact hdY')
    (FHeap.disjoint_union_right.mpr ⟨hdRI, (FHeap.disjoint_union_left.mp hdPX').1⟩)
    (fun l => by rw [up_bytesAt_some hWM rfl l, p_off, hs4]; exact Iff.rfl) hWM.2.1 hWM.2.2
    (fun l => by rw [up_bytesAt_some hWL rfl l, p_off, hs4]; exact Iff.rfl) hWL.2.1 hWL.2.2
    (fun l => by
      rw [rsum_heap_ne, rsum_heap_ne, up_bytesAt_some hSt rfl l, up_bytesAt_some hS1 rfl l,
        up_bytesAt_some hEp1 rfl l, p_off, p_off, p_off, hs8, hs4, hs4]
      exact Iff.rfl)
    hYu.2.1 hYu.2.2
    (by
      have e8 : (p b o).add 8 = p b (o + 8) := by
        show (⟨some b, (o : Int) + 8⟩ : Ptr) = ⟨some b, ((o + 8 : Nat) : Int)⟩
        exact congrArg (Ptr.mk (some b)) (by omega)
      rw [e8]
      exact ⟨⟨A, Sz, K, Enc.encode (0 : BitVec 64), by rw [p_off]; omega,
        LawfulEnc.size_encode _, LawfulEnc.decode_encode _, hCn.1, hK⟩, hCn.2.1, hCn.2.2⟩)
    hR (Res.Pins.right (Res.Pins.of_bauth (q := Frac.one) (sep_comm hX))) hG hphA hphB
    ⟨blk, hb, hlv, by omega, by rw [hA]; exact hal, by rw [hKd]; exact hK, by rw [hKd]; exact hlo⟩
    hat hq
    (by
      show (intOfBytes 64 (curBytes m b o 8)).run = some (.ok (RwState.encode 0 0 false))
      rw [hcur o 8 (by omega), hst, h0]; exact intOfBytes_rmw 0)
    (hu32 (o + 20) 0 (by omega) hS) (hu32 (o + 24) e0 (by omega) hEp)
    (hu32 (o + 32) 0 (by omega) hM) (hu32 (o + 16) 0 (by omega) hL) hall hthr
    ⟨r', hr', fun l fc h => by
      show (rIp.heap l).or (rX.heap l) = some fc
      rw [hsub l fc h]; rfl⟩

end RwProd

end Full
end Zig
