import AllocTranslated.PageMacos
import ZigLean.Sep.Mmap
import ZigLean.Sep.AllocSpec.Ops
import ZigLean.Sep.AllocSpec.Norm
import ZigLean.Sep.Full.AllocSpec
import ZigLean.Sep.Full.Tame

/-!
# The translated `PageAllocator` on aarch64-macos: `resize`, `remap` and `free` against `FAllocSpec`

The macOS counterpart of `PageSpec.lean` (same token, invariant and statements), for
`AllocTranslated/PageMacos.lean` (Zig 0.16.0, aarch64-macos, 16 KiB pages). macOS has no
`mremap` (`posix.MREMAP` is `void`), so `remap` is `resize` with `may_move`: a page-count shrink
unmaps the cut pages in place, a growth returns `null`/`false`, and every result keeps the grant's
pointer. Proved from the generated code and OSM-01 only.
-/

namespace AllocTranslated.PageSpecMacos

open Zig Zig.Region AllocTranslated.PageMacos Assn
open Zig.Ops (two_pow_lt toNat_two_pow add_ok gt_eq lt_eq)

abbrev P : Nat := 16384

theorem P_eq : Os.Target.macos.pageSize = P := rfl

/-- The token's facts: the grant is the start of the live range of a mapping (kind
`.mapped p.off`), which ends at the grant's page end; addresses are page-aligned; the length
leaves room for the page arithmetic. -/
def TokOk (p : Ptr) (n A S : Nat) (K : BlockKind) (tail : Array Byte) : Prop :=
  0 ≤ p.off ∧ K = .mapped p.off.toNat ∧ S = p.off.toNat + alignUp n P ∧ A % P = 0 ∧
    p.off.toNat % P = 0 ∧ tail.size = alignUp n P - n ∧ n + P ≤ 2 ^ 64

/-- The page allocator's token: the rest of the grant's last page. -/
def tok (p : Ptr) (n _k A S : Nat) (K : BlockKind) : Assn :=
  Assn.ex fun tail => ⌜TokOk p n A S K tail⌝ ∗ regionIn (p.add n) A S K 1 tail

/-- The legacy invariant for the vtable entries that do not touch the hint (`resize`, `remap`,
`free`): the allocator owns nothing else. -/
def legacy : AllocInv where
  own := emp
  tok := tok
  fits n k := n + 2 ^ k + P ≤ 2 ^ 64

/-! ## A grant is a mapping -/

theorem grant_mapping {p : Ptr} {k n A S : Nat} {K : BlockKind} {bs tail : Array Byte} {h : Heap}
    (hn : bs.size = n) (hpos : 0 < n) (ht : TokOk p n A S K tail)
    (hr : (regionIn p A S K (2 ^ k) bs ∗ regionIn (p.add n) A S K 1 tail) h) :
    mapping P p A p.off.toNat (bs ++ tail) h := by
  obtain ⟨h0, hK, hS, hA, hlo, htl, -⟩ := ht
  subst hn
  obtain ⟨-, -, hb⟩ := regionIn_join hr
  have hal := alignUp_lt (n := bs.size) (P := P) (by decide)
  have hge : bs.size ≤ alignUp bs.size P := by
    unfold alignUp; rw [if_neg (by decide)]
    have := Nat.lt_div_mul_add (a := bs.size + P - 1) (b := P) (by decide); omega
  refine ⟨by omega, by simp; omega, hA, hlo, ?_⟩
  rw [show p.off.toNat + (bs ++ tail).size = S by simp; omega, ← hK]
  exact hb


/-! ## Page arithmetic of the generated helpers -/

theorem alignUp_eq (n : Nat) : alignUp n P = (n + 16383) - (n + 16383) % 16384 := by
  unfold alignUp; rw [if_neg (by decide)]
  have := Nat.mod_add_div (n + 16383) 16384
  rw [show n + P - 1 = n + 16383 from rfl, show (P : Nat) = 16384 from rfl, Nat.mul_comm]
  omega

theorem toNat_and_not_16383 (z : BitVec 64) : (z &&& ~~~(16383 : BitVec 64)).toNat = z.toNat - z.toNat % 16384 := by
  have h0 : (z &&& ~~~(16383 : BitVec 64)) &&& (z &&& 16383) = 0#64 := by
    ext i; simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_zero]
    cases z[i] <;> cases (16383 : BitVec 64)[i] <;> rfl
  have h1 := BitVec.toNat_add_of_and_eq_zero h0
  rw [BitVec.add_eq_or_of_and_eq_zero _ _ h0] at h1
  have h2 : ((z &&& ~~~(16383 : BitVec 64)) ||| (z &&& 16383)) = z := by
    ext i; simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_or]
    cases z[i] <;> cases (16383 : BitVec 64)[i] <;> rfl
  rw [h2] at h1
  have h3 : (z &&& 16383).toNat = z.toNat % 16384 := by
    rw [BitVec.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod z.toNat 14
  omega

theorem validAlign16384 : mem_isValidAlignGeneric__anon_32d5b5f10ec2 16384 = pure true := rfl

theorem debug_assert_true : debug_assert true = pure () := rfl

theorem alignBackward_eq (x : BitVec 64) :
    mem_alignBackward__anon_f056e98f6fd2 x 16384 = pure (x &&& ~~~16383) := by
  unfold mem_alignBackward__anon_f056e98f6fd2
  simp only [StateT.run'_eq, StateT.run_bind, StateT.run_pure, StateT.run_lift, Zig.call, liftM,
    monadLift, MonadLift.monadLift, pure_bind, bind_assoc, map_pure, map_bind, validAlign16384]
  rfl

theorem alignForward_eq {n : BitVec 64} (h : n.toNat + P ≤ 2 ^ 64) :
    mem_alignForward__anon_589277751031 n 16384 = pure (BitVec.ofNat 64 (alignUp n.toNat P)) := by
  unfold mem_alignForward__anon_589277751031
  simp only [StateT.run'_eq, StateT.run_bind, StateT.run_pure, StateT.run_lift, Zig.call, liftM,
    monadLift, MonadLift.monadLift, pure_bind, bind_assoc, map_pure, map_bind, validAlign16384]
  rw [show Zig.sub false 16384 1 = pure 16383 from rfl]
  simp only [pure_bind, debug_assert_true]
  have hP : (P : Nat) = 16384 := rfl
  rw [hP] at h
  rw [add_ok (by simp; omega)]
  simp only [pure_bind, alignBackward_eq]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [toNat_and_not_16383, BitVec.toNat_add, alignUp_eq, BitVec.toNat_ofNat]
  simp only [show (16383 : BitVec 64).toNat = 16383 from rfl]
  have e : (n.toNat + 16383) % 2 ^ 64 = n.toNat + 16383 := Nat.mod_eq_of_lt (by omega)
  rw [e]
  exact (Nat.mod_eq_of_lt (by omega)).symm

/-! ## Opening a grant -/

/-- A grant as its mapping: the precondition of `free`, `resize` and `remap`. -/
theorem open_grant {α : Type} {p : Ptr} {k : Nat} {bs : Array Byte} {c : MemM α} {Q : α → Assn}
    (hpos : 0 < bs.size)
    (h : ∀ A S K tail, TokOk p bs.size A S K tail → (A + p.off.toNat) % 2 ^ k = 0 →
      TotalTriple (mapping P p A p.off.toNat (bs ++ tail)) c Q) :
    TotalTriple (granted legacy p k bs) c Q := by
  refine TotalTriple.ex fun A => TotalTriple.ex fun S => TotalTriple.ex fun K => ?_
  refine TotalTriple.conseq (P := Assn.ex fun tail =>
      ⌜TokOk p bs.size A S K tail ∧ (A + p.off.toNat) % 2 ^ k = 0⌝ ∗
        mapping P p A p.off.toNat (bs ++ tail))
    (TotalTriple.ex fun tail => TotalTriple.lift fun ⟨hok, hal⟩ => h A S K tail hok hal)
    (fun hh hp => ?_) (fun _ _ x => x)
  obtain ⟨h₁, h₂, hd₁₂, rfl, hr, tail, hq⟩ := hp
  obtain ⟨hok, ht⟩ := sep_lift.mp hq
  exact ⟨tail, sep_lift.mpr ⟨⟨hok, hr.1⟩,
    grant_mapping rfl hpos hok ⟨h₁, h₂, hd₁₂, rfl, hr, ht⟩⟩⟩

/-! ## Facts of a grant's mapping -/

theorem alignUp_ge (n : Nat) : n ≤ alignUp n P := by
  rw [alignUp_eq]; have := Nat.mod_lt (n + 16383) (by decide : 0 < 16384); omega

theorem alignUp_pos {n : Nat} (h : 0 < n) : 0 < alignUp n P := by
  have := alignUp_ge n; omega

theorem toNat_alignUp {n : Nat} (h : n + P ≤ 2 ^ 64) :
    (BitVec.ofNat 64 (alignUp n P)).toNat = alignUp n P := by
  have := alignUp_lt (n := n) (P := P) (by decide)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem mapping_block {p : Ptr} {A lo : Nat} {bs : Array Byte} {h : Heap}
    (hm : mapping P p A lo bs h) : ∃ b, p.block = some b ∧ OwnsIn b A h :=
  bytesAt_ownsIn hm.2.2.2.2 hm.2.1

theorem addr_mask {A : Nat} {off : Int} (h0 : 0 ≤ off) (hA : A % P = 0) (ho : off.toNat % P = 0) :
    (BitVec.ofInt 64 ((A : Int) + off) &&& 16383) = 0 := by
  have := Ops.and_mask_eq_zero (x := (A : Int) + off) (k := 14) (by decide) (by omega)
    (by
      have : ((A + off.toNat : Nat) : Int) % ((2 ^ 14 : Nat) : Int) = 0 := by
        exact_mod_cast (show (A + off.toNat) % 16384 = 0 by
          have hA' : A % 16384 = 0 := hA; have ho' : off.toNat % 16384 = 0 := ho; omega)
      rw [Int.natCast_add, Int.toNat_of_nonneg h0] at this
      exact_mod_cast this)
  exact this

/-! ## `free` -/

theorem free_total (c : Ptr) (s : Slice) (k : Nat) (ra : BitVec 64) (bs : Array Byte)
    (hs : s.len.toNat = bs.size) (hpos : 0 < bs.size) :
    TotalTriple (granted legacy s.ptr k bs) (heap_PageAllocator_free c s ⟨BitVec.ofNat 6 k⟩ ra)
      (fun _ => emp) := by
  refine open_grant hpos fun A S K tail hok _ => ?_
  obtain ⟨h0, -, -, hA, hlo, htl, hfit⟩ := hok
  simp only [heap_PageAllocator_free, heap_PageAllocator_unmap]
  gen_norm
  refine TotalTriple.of_pure (φ := ∃ b, s.ptr.block = some b)
    (fun h hp => (mapping_block hp).imp fun _ x => x.1) fun ⟨b, hb⟩ => ?_
  refine TotalTriple.bind (ptrAddr_owned (A := A) hb fun h hp => by
    obtain ⟨b', hb', ho⟩ := mapping_block hp
    rw [hb] at hb'; cases hb'; exact ho) fun x => TotalTriple.lift fun hx => ?_
  subst hx
  rw [addr_mask h0 hA hlo]
  simp only [beq_self_eq_true, Bool.or_true, ↓reduceIte]
  rw [alignForward_eq (by rw [hs]; omega), Norm.lift_pure, pure_bind]
  have hn := toNat_alignUp (n := bs.size) (by omega)
  have hsz : (bs ++ tail).size = alignUp bs.size P := by
    have := alignUp_ge bs.size; simp; omega
  rw [hs]
  exact TotalTriple.munmapWhole Os.Target.macos (by rw [hn]; exact alignUp_pos hpos)
    (by rw [hn, hsz, P_eq, alignUp_of_mod (by decide) (alignUp_mod_self (by decide))])

/-! ## Granting the start of a mapping -/

/-- The first `n` bytes of a whole mapping whose live range ends at their page end, granted. -/
theorem regrant {p : Ptr} {A k n : Nat} {all : Array Byte} {h : Heap}
    (hm : mapping P p A p.off.toNat all h) (hsz : all.size = alignUp n P)
    (hfit : n + P ≤ 2 ^ 64) (hal : (A + p.off.toNat) % 2 ^ k = 0) :
    granted legacy p k (all.extract 0 n) h := by
  obtain ⟨hoff, -, hA, hlo, hb⟩ := hm
  have hge := alignUp_ge n
  have hr : regionIn p A (p.off.toNat + all.size) (.mapped p.off.toNat) (2 ^ k) all h :=
    ⟨hal, by simp, hb⟩
  obtain ⟨h₁, h₂, hd, rfl, h1, h2⟩ := regionIn_split hr (k := n) (a' := 1) (by omega) (Nat.mod_one _)
  have hn' : (all.extract 0 n).size = n := by simp; omega
  refine ⟨A, _, _, h₁, h₂, hd, rfl, h1, all.extract n all.size, sep_lift.mpr ⟨⟨?_, rfl, ?_, hA, hlo,
    ?_, by rw [hn']; exact hfit⟩, ?_⟩⟩
  · omega
  · rw [hn', hsz]
  · rw [hn']; simp; omega
  · rw [hn']; exact h2

theorem keepsPrefix_of {bs all : Array Byte} {n : Nat} (hp : all.extract 0 bs.size = bs) :
    keepsPrefix bs (all.extract 0 n) := by
  unfold keepsPrefix
  rw [Array.extract_extract, ← hp, Array.extract_extract]
  simp only [Nat.zero_add, Array.size_extract, Nat.sub_zero]
  congr 1
  omega

/-- `realloc`'s result: `null` and the old grant, or the new grant (at the same pointer unless
the mapping may move). -/
def reallocPost (p : Ptr) (k : Nat) (bs : Array Byte) (n : Nat) (mm : Bool) : Option Ptr → Assn
  | none => granted legacy p k bs
  | some q => ⌜mm = false → q = p⌝ ∗ Assn.ex fun bs' =>
      ⌜bs'.size = n ∧ keepsPrefix bs bs'⌝ ∗ granted legacy q k bs'

theorem extract_min {bs all : Array Byte} {n : Nat} (hp : all.extract 0 bs.size = bs) :
    all.extract 0 (min n bs.size) = bs.extract 0 n := by
  have e := congrArg (fun a : Array Byte => a.extract 0 n) hp
  simp only [Array.extract_extract, Nat.zero_add] at e
  rw [← e]

/-- A grant of the first `n` bytes of a whole mapping is `realloc`'s `some` result. -/
theorem post_some {p q : Ptr} {k n : Nat} {mm : Bool} {bs all : Array Byte} {A : Nat} {h : Heap}
    (hm : mapping P q A q.off.toNat all h) (hsz : all.size = alignUp n P) (hfit : n + P ≤ 2 ^ 64)
    (hal : (A + q.off.toNat) % 2 ^ k = 0) (hpre : all.extract 0 (min n bs.size) = bs.extract 0 n)
    (hq : mm = false → q = p) : reallocPost p k bs n mm (some q) h := by
  have hge := alignUp_ge n
  refine sep_lift.mpr ⟨hq, all.extract 0 n, sep_lift.mpr ⟨⟨by simp; omega, ?_⟩,
    regrant hm hsz hfit hal⟩⟩
  unfold keepsPrefix
  rw [Array.extract_extract, Array.size_extract]
  simp only [Nat.zero_add]
  rw [show min bs.size n = min n bs.size by omega, hpre]
  congr 1; omega

/-! ## `realloc` -/

theorem toByteUnits_eq {k : Nat} (hk : k < 64) :
    mem_Alignment_toByteUnits ⟨BitVec.ofNat 6 k⟩ = pure (BitVec.ofNat 64 (2 ^ k)) := by
  have hk6 : (BitVec.ofNat 6 k).toNat = k := by simp [BitVec.toNat_ofNat]; omega
  have e : Zig.shl (1 : BitVec 64) (BitVec.ofNat 6 k) = BitVec.ofNat 64 (2 ^ k) := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_two_pow hk]
    simp only [Zig.shl, BitVec.toNat_shiftLeft, hk6]
    simp [Nat.shiftLeft_eq, Nat.mod_eq_of_lt (two_pow_lt hk)]
  unfold mem_Alignment_toByteUnits
  simp only [StateT.run'_eq, StateT.run_pure, pure_bind, map_pure]
  simp only [mem_Alignment.toBits, e]

theorem realloc_total (s : Slice) (k : Nat) (n : BitVec 64) (mm : Bool) (bs : Array Byte)
    (hk : k < 64) (hn : 0 < n.toNat) (hfit : n.toNat + 2 ^ k + P ≤ 2 ^ 64)
    (hs : s.len.toNat = bs.size) (hpos : 0 < bs.size) :
    TotalTriple (granted legacy s.ptr k bs) (heap_PageAllocator_realloc s ⟨BitVec.ofNat 6 k⟩ n mm)
      (reallocPost s.ptr k bs n.toNat mm) := by
  refine open_grant hpos fun A S K tail hok hal => ?_
  have hok' := hok
  obtain ⟨h0, -, -, hA, hlo, htl, hfit₀⟩ := hok
  simp only [heap_PageAllocator_realloc]
  gen_norm
  refine TotalTriple.of_pure (φ := ∃ b, s.ptr.block = some b)
    (fun h hp => (mapping_block hp).imp fun _ x => x.1) fun ⟨b, hb⟩ => ?_
  refine TotalTriple.bind (ptrAddr_owned (A := A) hb fun h hp => by
    obtain ⟨b', hb', ho⟩ := mapping_block hp
    rw [hb] at hb'; cases hb'; exact ho) fun x => TotalTriple.lift fun hx => ?_
  subst hx
  rw [addr_mask h0 hA hlo]
  simp only [beq_self_eq_true, Bool.or_true, ↓reduceIte]
  rw [toByteUnits_eq hk, Norm.lift_pure, pure_bind, gt_eq, toNat_two_pow hk]
  have hsz : (bs ++ tail).size = alignUp bs.size P := by
    have := alignUp_ge bs.size; simp; omega
  have hclose : ∀ h, mapping P s.ptr A s.ptr.off.toNat (bs ++ tail) h →
      reallocPost s.ptr k bs n.toNat mm none h := fun h hm => by
    have := regrant (n := bs.size) hm hsz (by omega) hal
    rwa [show (bs ++ tail).extract 0 bs.size = bs by simp] at this
  by_cases hbig : 16384 < 2 ^ k
  · rw [if_pos (by simpa using hbig)]
    exact TotalTriple.conseq (TotalTriple.ret (Q := reallocPost s.ptr k bs n.toNat mm) none)
      hclose (fun _ _ x => x)
  rw [if_neg (by simpa using hbig)]
  rw [alignForward_eq (by omega), alignForward_eq (by rw [hs]; omega), Norm.lift_pure, pure_bind,
    Norm.lift_pure, pure_bind, hs]
  have hk12 : k ≤ 14 := by
    rcases Nat.lt_or_ge 14 k with hc | hc
    · exact absurd (Nat.lt_of_lt_of_le (by decide : 16384 < 2 ^ 15)
        (Nat.pow_le_pow_right (by decide) hc)) hbig
    · exact hc
  have hdvd : 2 ^ k ∣ P := Nat.pow_dvd_pow 2 hk12
  have hNlt := alignUp_lt (n := n.toNat) (P := P) (by decide)
  have hMlt := alignUp_lt (n := bs.size) (P := P) (by decide)
  have hN := toNat_alignUp (n := n.toNat) (by omega)
  have hM := toNat_alignUp (n := bs.size) (by omega)
  have hfitn : n.toNat + P ≤ 2 ^ 64 := by omega
  have hpre₀ : (bs ++ tail).extract 0 bs.size = bs := by simp
  by_cases heq : alignUp n.toNat P = alignUp bs.size P
  · rw [if_pos (by rw [heq])]
    exact TotalTriple.conseq (TotalTriple.ret (Q := reallocPost s.ptr k bs n.toNat mm) _)
      (fun h hm => post_some hm (by rw [hsz, heq]) hfitn hal (extract_min hpre₀) fun _ => rfl)
      (fun _ _ x => x)
  rw [if_neg (fun e => heq (by rw [← hN, ← hM, e]))]
  have hP0 : 0 < P := by decide
  have hNmod := alignUp_mod_self (n := n.toNat) hP0
  have hMmod := alignUp_mod_self (n := bs.size) hP0
  have hNpos := alignUp_pos hn
  have hMpos := alignUp_pos hpos
  have hNge := alignUp_ge n.toNat
  rw [lt_eq, hN, hM]
  by_cases hlt : alignUp n.toNat P < alignUp bs.size P
  · rw [if_pos (by simpa using hlt)]
    have hsub : Zig.sub false (BitVec.ofNat 64 (alignUp bs.size P))
        (BitVec.ofNat 64 (alignUp n.toNat P)) =
        pure (BitVec.ofNat 64 (alignUp bs.size P - alignUp n.toNat P)) := by
      simp only [Zig.sub, BitVec.usubOverflow, Bool.false_eq_true, ↓reduceIte, hN, hM]
      rw [if_neg (by simp; omega)]
      congr 1
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hN, hM]; omega), hN, hM,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [hsub, Norm.lift_pure, pure_bind]
    have hel : s.ptr.elem 1 (BitVec.ofNat 64 (alignUp n.toNat P)) =
        s.ptr.add ((alignUp n.toNat P : Nat) : Int) := by
      rw [Ptr.elem_eq, hN, Nat.one_mul]
    rw [hel]
    refine TotalTriple.of_pure (φ := ∃ b, s.ptr.block = some b)
      (fun h hp => (mapping_block hp).imp fun _ x => x.1) fun ⟨b, hb⟩ => ?_
    have hb' : (s.ptr.add ((alignUp n.toNat P : Nat) : Int)).block = some b := by
      simp [Ptr.add, hb]
    refine TotalTriple.bind (ptrAddr_owned (A := A) hb' fun h hp => by
      obtain ⟨b', hb'', ho⟩ := mapping_block hp
      rw [hb] at hb''; cases hb''; exact ho) fun x => TotalTriple.lift fun hx => ?_
    subst hx
    have hoff : (s.ptr.add ((alignUp n.toNat P : Nat) : Int)).off =
        ((s.ptr.off.toNat + alignUp n.toNat P : Nat) : Int) := by
      show s.ptr.off + _ = _
      rw [Int.natCast_add, Int.toNat_of_nonneg h0]
    rw [hoff, addr_mask (by omega) hA (by
      rw [Int.toNat_natCast]
      exact Nat.mod_eq_zero_of_dvd (Nat.dvd_add (Nat.dvd_of_mod_eq_zero hlo)
        (Nat.dvd_of_mod_eq_zero hNmod)))]
    simp only [beq_self_eq_true, Bool.or_true, ↓reduceIte]
    have hdiff : (BitVec.ofNat 64 (alignUp bs.size P - alignUp n.toNat P)).toNat =
        alignUp bs.size P - alignUp n.toNat P := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine TotalTriple.bind (TotalTriple.munmapTail Os.Target.macos (k := alignUp n.toNat P)
      hNmod hNpos (by rw [hsz]; exact hlt) (by rw [hdiff]; omega) ?_) fun _ => ?_
    · have h1 : alignUp (alignUp bs.size P - alignUp n.toNat P) P =
          alignUp bs.size P - alignUp n.toNat P :=
        alignUp_of_mod hP0 (Nat.sub_mod_eq_zero_of_mod_eq (by rw [hMmod, hNmod]))
      have h2 : alignUp (alignUp bs.size P) P = alignUp bs.size P := alignUp_of_mod hP0 hMmod
      rw [hdiff, hsz, P_eq, h1, h2]
      omega
    refine TotalTriple.conseq (TotalTriple.ret (Q := reallocPost s.ptr k bs n.toNat mm) _)
      (fun h hm => post_some hm (by rw [Array.size_extract, hsz]; omega) hfitn hal ?_
        (fun _ => rfl))
      (fun _ _ x => x)
    rw [Array.extract_extract]
    simp only [Nat.zero_add]
    rw [show Min.min (Min.min n.toNat bs.size) (alignUp n.toNat P) = Min.min n.toNat bs.size by
      omega]
    exact extract_min hpre₀
  · rw [if_neg (by simpa using hlt)]
    exact TotalTriple.conseq (TotalTriple.ret (Q := reallocPost s.ptr k bs n.toNat mm) none)
      hclose (fun _ _ x => x)

theorem sep_emp_left {Q : Assn} {h : Heap} : (emp ∗ Q) h ↔ Q h :=
  ⟨fun x => sep_emp.mp (sep_comm x), fun x => sep_comm (sep_emp.mpr x)⟩

/-! ## The vtable entries -/

/-- The translated vtable entries, as `RawVTable` fields. `alloc` reaches sync ops (the atomics on
`addr_hint`); a sequential call is the scheduler's run of one thread (`PageObstruction.lean`). -/
def vt : RawVTable where
  alloc c len k ra := fun m =>
    Sched.run dispatch 16 (fun _ => 0) (heap_PageAllocator_alloc c len ⟨BitVec.ofNat 6 k⟩ ra) m
  resize c s k n ra := heap_PageAllocator_resize c s ⟨BitVec.ofNat 6 k⟩ n ra
  remap c s k n ra := heap_PageAllocator_remap c s ⟨BitVec.ofNat 6 k⟩ n ra
  free c s k ra := heap_PageAllocator_free c s ⟨BitVec.ofNat 6 k⟩ ra

theorem resize_total (c : Ptr) (s : Slice) (k : Nat) (n ra : BitVec 64) (bs : Array Byte)
    (hk : k < 64) (hn : 0 < n.toNat) (hfit : legacy.fits n.toNat k) (hs : s.len.toNat = bs.size)
    (hpos : 0 < bs.size) :
    TotalTriple (granted legacy s.ptr k bs) (vt.resize c s k n ra)
      (fun v => resizePost legacy s.ptr k bs n.toNat v) := by
  simp only [vt, heap_PageAllocator_resize]
  gen_norm
  refine TotalTriple.bind (realloc_total s k n false bs hk hn hfit hs hpos) fun r => ?_
  cases r with
  | none =>
    exact TotalTriple.conseq (TotalTriple.ret (Q := fun v => resizePost legacy s.ptr k bs n.toNat v)
      false) (fun h hp => sep_emp_left.mpr hp) (fun _ _ x => x)
  | some q =>
    refine TotalTriple.lift fun hq => ?_
    rw [hq rfl]
    exact TotalTriple.conseq (TotalTriple.ret (Q := fun v => resizePost legacy s.ptr k bs n.toNat v)
      true) (fun h hp => sep_emp_left.mpr hp) (fun _ _ x => x)

theorem remap_total (c : Ptr) (s : Slice) (k : Nat) (n ra : BitVec 64) (bs : Array Byte)
    (hk : k < 64) (hn : 0 < n.toNat) (hfit : legacy.fits n.toNat k) (hs : s.len.toNat = bs.size)
    (hpos : 0 < bs.size) :
    TotalTriple (granted legacy s.ptr k bs) (vt.remap c s k n ra)
      (fun v => remapPost legacy s.ptr k bs n.toNat v) := by
  simp only [vt, heap_PageAllocator_remap]
  gen_norm
  rw [bind_pure]
  refine TotalTriple.conseq (realloc_total s k n true bs hk hn hfit hs hpos) (fun _ x => x)
    fun v h hp => ?_
  cases v with
  | none => exact sep_emp_left.mpr hp
  | some q => exact sep_emp_left.mpr (sep_lift.mp hp).2

/-! ## The full-state specification of `resize`, `remap` and `free` -/

open Zig.Full Zig.Full.FAssn in
/-- The page allocator's invariant over full-state resources, for an allocator state `own`
(the hint word with its atomic layout and the knowledge of the hinted mapping). `resize`,
`remap` and `free` never touch it. -/
def inv (own : FAssn) : FAllocInv where
  own := own
  tok p n k A S K := FAssn.up (tok p n k A S K)
  fits := legacy.fits

section Full

open Zig.Full Zig.Full.FAssn

theorem tame_realloc (s : Slice) (a : mem_Alignment) (n : BitVec 64) (mm : Bool) :
    Tame (heap_PageAllocator_realloc s a n mm) := by
  simp only [heap_PageAllocator_realloc]; gen_norm; tame

theorem tame_free (c : Ptr) (s : Slice) (k : Nat) (ra : BitVec 64) : Tame (vt.free c s k ra) := by
  simp only [vt, heap_PageAllocator_free, heap_PageAllocator_unmap]; gen_norm; tame

theorem tame_resize (c : Ptr) (s : Slice) (k : Nat) (n ra : BitVec 64) :
    Tame (vt.resize c s k n ra) := by
  have := tame_realloc
  simp only [vt, heap_PageAllocator_resize]; gen_norm; tame

theorem tame_remap (c : Ptr) (s : Slice) (k : Nat) (n ra : BitVec 64) :
    Tame (vt.remap c s k n ra) := by
  have := tame_realloc
  simp only [vt, heap_PageAllocator_remap]; gen_norm; tame

variable {own : FAssn} {r : Res}

/-- The page allocator's invariant is the legacy one with the allocator state `own` added, so
every `std.mem.Allocator` wrapper contract holds for it (`ZigLean/Sep/Full/Wrappers.lean`). -/
theorem inv_legacy (own : FAssn) : LegacyTokens (inv own) legacy own :=
  ⟨fun _ _ _ _ _ _ => rfl,
    fun _ => ⟨fun h => sep_mono_right (fun _ y => up_emp.mpr y) (sep_emp.mpr h),
      fun h => sep_emp.mp (sep_mono_right (fun _ y => up_emp.mp y) h)⟩,
    fun _ _ => Iff.rfl⟩

theorem pre_up {p : Ptr} {k : Nat} {bs : Array Byte}
    (h : (own ⋆ (inv own).granted p k bs) r) : (own ⋆ up (granted legacy p k bs)) r :=
  sep_mono_right (fun _ x => up_granted (I := legacy).mp x) h

theorem post_own {X : FAssn} (h : (own ⋆ (up emp ⋆ X)) r) : (own ⋆ X) r :=
  sep_mono_right (fun _ x => sep_emp.mp (sep_comm (sep_mono_left (fun _ y => up_emp.mp y) x))) h

/-- **`free`** of a granted region: the region and its token go, the allocator state stays. -/
theorem free_spec (c : Ptr) (s : Slice) (k : Nat) (ra : BitVec 64) (bs : Array Byte)
    (hs : s.len.toNat = bs.size) (hpos : 0 < bs.size) :
    FTotalTriple (own ⋆ (inv own).granted s.ptr k bs) (vt.free c s k ra) (fun _ => own) :=
  (FLogic.total.frameL (R := own) (FTotalTriple.ofTotal (free_total c s k ra bs hs hpos)
    (tame_free c s k ra))).conseq (fun _ h => pre_up h)
    fun _ _ h => sep_emp.mp (sep_mono_right (fun _ y => up_emp.mp y) h)

/-- **`resize`**: in place, or `false` and nothing changed. -/
theorem resize_spec (c : Ptr) (s : Slice) (k : Nat) (n ra : BitVec 64) (bs : Array Byte)
    (hk : k < 64) (hn : 0 < n.toNat) (hfit : (inv own).fits n.toNat k)
    (hs : s.len.toNat = bs.size) (hpos : 0 < bs.size) :
    FTotalTriple (own ⋆ (inv own).granted s.ptr k bs) (vt.resize c s k n ra)
      ((inv own).resizePost s.ptr k bs n.toNat) :=
  (FLogic.total.frameL (R := own) (FTotalTriple.ofTotal (resize_total c s k n ra bs hk hn hfit hs hpos)
    (tame_resize c s k n ra))).conseq (fun _ h => pre_up h)
    fun v _ h => by
      have h' := sep_mono_right (fun _ y => up_resizePost (I := legacy) y) h
      cases v <;> exact post_own h'

/-- **`remap`**: in place (macOS has no `mremap`), or `null` and nothing changed. -/
theorem remap_spec (c : Ptr) (s : Slice) (k : Nat) (n ra : BitVec 64) (bs : Array Byte)
    (hk : k < 64) (hn : 0 < n.toNat) (hfit : (inv own).fits n.toNat k)
    (hs : s.len.toNat = bs.size) (hpos : 0 < bs.size) :
    FTotalTriple (own ⋆ (inv own).granted s.ptr k bs) (vt.remap c s k n ra)
      ((inv own).remapPost s.ptr k bs n.toNat) :=
  (FLogic.total.frameL (R := own) (FTotalTriple.ofTotal (remap_total c s k n ra bs hk hn hfit hs hpos)
    (tame_remap c s k n ra))).conseq (fun _ h => pre_up h)
    fun v _ h => by
      have h' := sep_mono_right (fun _ y => up_remapPost (I := legacy) y) h
      cases v <;> exact post_own h'

end Full

end AllocTranslated.PageSpecMacos