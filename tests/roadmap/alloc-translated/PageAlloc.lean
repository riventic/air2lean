import PageSpec
import ZigLean.Sep.Full.Conc
import ZigLean.Sep.Full.AtomicPtr

/-!
# The translated `PageAllocator` against `FAllocSpec`, `alloc` included (P4b)

`fallocSpec`: the translated `std.heap.PageAllocator` (`AllocTranslated/PageLinux.lean`, Zig
0.16.0, x86_64-linux) satisfies `FAllocSpec FLogic.partial vt c ainv`, from the generated code
and the OS mapping model only (premise OSM-01). No model of the allocator is used.

* **The allocator state** `own`: the hint word `addr_hint` as a pointer-valued atomic points-to
  (`aptsE`, O3), and for a non-null hint the knowledge of its block's address, page-aligned
  (`known`, O1). `alloc` reads the hint (`FTriple.atomicLoadUnorderedEnc`), takes `@intFromPtr`
  of it (`FTriple.ptrAddr`: the block may be unmapped), checks the derived address and turns it
  back into a pointer (`@ptrFromInt`, which never fails since the O4 fix), maps the pages
  (`TotalTriple.mmap`), and publishes the new mapping with a `cmpxchg` that succeeds
  (`FTriple.cmpxchgPtr`): the new hint's knowledge comes from owning the mapping
  (`know_intro`). `resize`, `remap` and `free` frame `own` (`PageSpec.lean`).
* **The call.** `alloc` is a concurrent function (its hint is an atomic). A sequential caller
  runs it in its own thread, each atomic op's oracle choice `0` (`Sched.soloRun`,
  `CTriple`, `ZigLean/Sep/Full/Conc.lean`). `alloc_threadFree` and `alloc_run`: the one-thread
  scheduler run is the same tree read sequentially (`Sched.run_eq_seqRun`). The scheduler's run
  itself (`PageObstruction.vt`) is not a `FAllocSpec` entry: it starts thread `0` from any
  memory and ends it (`checkJoinedByChild`), which an `FSeq` memory with another current thread
  or an unjoined child fails, whatever the allocator does.
* **Every alignment** (`ainv.fits` is `legacy.fits`, O5 fixed). For an alignment `2 ^ k` above
  a page, `map` maps `2 ^ k - 4096` extra bytes, `std.mem.alignPointer` moves `drop A (2 ^ k)`
  bytes up from the mapping's address `A` (`alignPointer_gen`; its overflow check passes because
  `mmap` never maps above `Os.Target.addrLimit = 2 ^ 47`, OSM-01), and `map` unmaps the pages
  below (`TotalTriple.munmapPrefix`, `munmap_drop`) and above (`TotalTriple.munmapTail`,
  `munmap_rest`) the granted ones. `alloc_high` (kernel-checked) is the regression of the old
  counterexample: from a `nextAddr` near `2 ^ 64` the mapping now fails and `alloc` returns
  `null` instead of panicking; `alloc_top` runs the prefix `munmap` at the end of the address
  space.
* **Partial correctness.** The atomic rules are partial (`FTriple`); `free`, `resize` and
  `remap` are total (`PageSpec.lean`).
-/

namespace AllocTranslated.PageAlloc

open Zig Zig.Region AllocTranslated.PageLinux AllocTranslated.PageSpec Zig.Full Zig.Full.FAssn

/-! ## `std.mem.alignPointer` up to a page: the pointer itself -/

theorem two_pow_le {k : Nat} (hk : k ≤ 12) : 2 ^ k ≤ 4096 :=
  Nat.le_trans (Nat.pow_le_pow_right (n := 2) (by decide) hk) (by decide)

theorem alignPointerOffset_small {k : Nat} (hk : k ≤ 12) (p : Ptr) :
    mem_alignPointerOffset__anon_1 p (BitVec.ofNat 64 (2 ^ k)) = pure (some 0) := by
  have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨
    k = 10 ∨ k = 11 ∨ k = 12 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · unfold mem_alignPointerOffset__anon_1
    gen_norm
    rfl

theorem mapping_owns {p : Ptr} {b : BlockId} {A lo : Nat} {bs : Array Byte} (hb : p.block = some b) :
    ∀ h, mapping P p A lo bs h → OwnsIn b A h := fun h hm => by
  obtain ⟨b', hb', ho⟩ := PageSpec.mapping_block hm
  rw [hb] at hb'; cases hb'; exact ho

/-- `std.mem.alignPointer` of a page-aligned owned pointer, to at most a page: the pointer. -/
theorem alignPointer_total {p : Ptr} {A : Nat} {bs : Array Byte} {k : Nat} (hk : k ≤ 12)
    (h0 : p.off = 0) :
    TotalTriple (mapping P p A 0 bs) (mem_alignPointer__anon_1 p (BitVec.ofNat 64 (2 ^ k)))
      (fun r => ⌜r = some p⌝ ∗ mapping P p A 0 bs) := by
  unfold mem_alignPointer__anon_1
  gen_norm
  rw [alignPointerOffset_small hk]
  have e0 : p.elem 1 0 = p := by simp [Ptr.elem, Ptr.add]
  simp only [pure_bind, Option.elim_some, e0]
  refine TotalTriple.of_pure (φ := (∃ b, p.block = some b) ∧ A % P = 0)
    (fun h hp => ⟨(PageSpec.mapping_block hp).imp fun _ x => x.1, hp.2.2.1⟩) fun ⟨⟨b, hb⟩, hA⟩ => ?_
  refine TotalTriple.bind (ptrAddr_owned (A := A) hb (mapping_owns hb)) fun x =>
    TotalTriple.lift fun hx => ?_
  subst hx
  rw [addr_mask (by omega) hA (by rw [h0]; rfl)]
  simp only [↓reduceIte]
  exact TotalTriple.conseq (TotalTriple.ret (Q := fun r => ⌜r = some p⌝ ∗ mapping P p A 0 bs) _)
    (fun h hm => sep_lift.mpr ⟨rfl, hm⟩) (fun _ _ x => x)

/-! ## `std.mem.alignPointer` above a page -/

/-- The bytes that `std.mem.alignPointer` skips from the address `A` to alignment `K`. -/
def drop (A K : Nat) : Nat := alignUp A K - A

theorem sub_pow_one {k : Nat} (hk : k < 64) :
    Zig.sub false (BitVec.ofNat 64 (2 ^ k)) 1 = pure (BitVec.ofNat 64 (2 ^ k) - 1) := by
  have := Nat.two_pow_pos k
  have := Ops.toNat_two_pow hk
  simp only [Zig.sub, BitVec.usubOverflow, Bool.false_eq_true, ↓reduceIte]
  rw [if_neg (by simp; omega)]

theorem toNat_pow_sub_one {k : Nat} (hk : k < 64) :
    (BitVec.ofNat 64 (2 ^ k) - 1).toNat = 2 ^ k - 1 := by
  have := Nat.two_pow_pos k
  have := Ops.toNat_two_pow hk
  rw [BitVec.toNat_sub_of_le (by simp; omega)]; simp; omega

theorem toNat_and_mask {k : Nat} (hk : k < 64) (z : BitVec 64) :
    (z &&& (BitVec.ofNat 64 (2 ^ k) - 1)).toNat = z.toNat % 2 ^ k := by
  rw [BitVec.toNat_and, toNat_pow_sub_one hk, Nat.and_two_pow_sub_one_eq_mod]

theorem toNat_and_not_mask {k : Nat} (hk : k < 64) (z : BitVec 64) :
    (z &&& ~~~(BitVec.ofNat 64 (2 ^ k) - 1)).toNat = z.toNat - z.toNat % 2 ^ k := by
  have h0 : (z &&& ~~~(BitVec.ofNat 64 (2 ^ k) - 1)) &&& (z &&& (BitVec.ofNat 64 (2 ^ k) - 1)) =
      0#64 := by
    ext i; simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_zero]
    cases z[i] <;> cases (BitVec.ofNat 64 (2 ^ k) - 1)[i] <;> rfl
  have h1 := BitVec.toNat_add_of_and_eq_zero h0
  rw [BitVec.add_eq_or_of_and_eq_zero _ _ h0] at h1
  have h2 : ((z &&& ~~~(BitVec.ofNat 64 (2 ^ k) - 1)) ||| (z &&& (BitVec.ofNat 64 (2 ^ k) - 1))) =
      z := by
    ext i; simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_or]
    cases z[i] <;> cases (BitVec.ofNat 64 (2 ^ k) - 1)[i] <;> rfl
  rw [h2, toNat_and_mask hk] at h1
  omega

theorem isValidAlign_pow {k : Nat} (hk : k < 64) :
    mem_isValidAlign (BitVec.ofNat 64 (2 ^ k)) = pure true := by
  have h2 := Ops.toNat_two_pow hk
  have hpos := Nat.two_pow_pos k
  have hand : BitVec.ofNat 64 (2 ^ k) &&& (BitVec.ofNat 64 (2 ^ k) - 1) = 0 := by
    apply BitVec.eq_of_toNat_eq; rw [toNat_and_mask hk, h2, Nat.mod_self]; rfl
  have hgt : Zig.gt false (BitVec.ofNat 64 (2 ^ k)) 0 = true := by
    rw [Ops.gt_eq, h2]; simpa using hpos
  unfold mem_isValidAlign mem_isValidAlignGeneric__anon_1 math_isPowerOfTwo__anon_1
  have hm : 2 ^ k % 18446744073709551616 = 2 ^ k := Nat.mod_eq_of_lt (Ops.two_pow_lt hk)
  have hne : 2 ^ k ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
  simp [hm, hpos, debug_assert_true, Zig.call]
  rw [show BitVec.ofNat 64 (2 ^ k) &&& BitVec.ofNat 64 (2 ^ k) - 1#64 = 0#64 from hand]; rfl

theorem le_big {k : Nat} (hk : k < 64) (hk12 : 12 < k) :
    Zig.le false (BitVec.ofNat 64 (2 ^ k)) 4096 = false := by
  have h2 := Ops.toNat_two_pow hk
  have : 2 ^ 13 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk12
  simp [Zig.le, BitVec.ule, h2]; omega

theorem alignUp_eq_sub {A K : Nat} (hK : 0 < K) : alignUp A K = (A + K - 1) - (A + K - 1) % K := by
  unfold alignUp; rw [if_neg (by omega)]
  have := Nat.mod_add_div (A + K - 1) K
  rw [Nat.mul_comm] at this; omega

theorem alignUp_bounds {A K : Nat} (hK : 0 < K) : A ≤ alignUp A K ∧ alignUp A K < A + K := by
  have := alignUp_eq_sub (A := A) hK
  exact ⟨le_alignUp A K, by omega⟩

theorem rem_one (x : BitVec 64) : Zig.rem false x 1 = pure 0 := by
  simp [Zig.rem]

theorem divTrunc_one (x : BitVec 64) : Zig.divTrunc false x 1 = pure x := by
  simp [Zig.divTrunc]

/-- The overflow check of `alignPointerOffset` passes, and the aligned address is `alignUp`. -/
theorem align_add {k A : Nat} (hk : k < 64) (hfit : A + 2 ^ k ≤ 2 ^ 64) :
    Zig.addWithOverflow false (BitVec.ofInt 64 ((A : Int) + 0)) (BitVec.ofNat 64 (2 ^ k) - 1) =
      (BitVec.ofNat 64 (A + 2 ^ k - 1), 0) := by
  have hpos := Nat.two_pow_pos k
  have h1 := toNat_pow_sub_one hk
  have hA : (BitVec.ofInt 64 ((A : Int) + 0)).toNat = A := by
    rw [Int.add_zero, BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp only [Zig.addWithOverflow, Bool.false_eq_true, ↓reduceIte, BitVec.uaddOverflow, hA, h1]
  rw [if_neg (by simp; omega)]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, hA, h1, BitVec.toNat_ofNat]
  congr 1; omega

theorem align_sub {k A : Nat} (hk : k < 64) (hfit : A + 2 ^ k ≤ 2 ^ 64) :
    Zig.sub false (BitVec.ofNat 64 (A + 2 ^ k - 1) &&& ~~~(BitVec.ofNat 64 (2 ^ k) - 1))
      (BitVec.ofInt 64 ((A : Int) + 0)) = pure (BitVec.ofNat 64 (drop A (2 ^ k))) := by
  have hpos := Nat.two_pow_pos k
  have hA : (BitVec.ofInt 64 ((A : Int) + 0)).toNat = A := by
    rw [Int.add_zero, BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx : (BitVec.ofNat 64 (A + 2 ^ k - 1) &&& ~~~(BitVec.ofNat 64 (2 ^ k) - 1)).toNat =
      alignUp A (2 ^ k) := by
    rw [toNat_and_not_mask hk, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      alignUp_eq_sub hpos]
  have hle := le_alignUp A (2 ^ k)
  simp only [Zig.sub, BitVec.usubOverflow, Bool.false_eq_true, ↓reduceIte, hx, hA]
  rw [if_neg (by simp only [decide_eq_true_eq]; omega)]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hx, hA]; exact hle), hx, hA, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := (alignUp_bounds (A := A) hpos).2; unfold drop; omega)]
  rfl

/-- `std.mem.alignPointerOffset` of a page-aligned mapping start to `2 ^ k > 4096`: no overflow
(the mapping ends in the address space), the offset `drop A (2 ^ k)`. -/
theorem alignPointerOffset_big {k : Nat} (hk : k < 64) (hk12 : 12 < k) {p : Ptr} {A : Nat}
    {bs : Array Byte} (h0 : p.off = 0) (hfit : A + 2 ^ k ≤ 2 ^ 64) :
    TotalTriple (mapping P p A 0 bs) (mem_alignPointerOffset__anon_1 p (BitVec.ofNat 64 (2 ^ k)))
      (fun r => ⌜r = some (BitVec.ofNat 64 (drop A (2 ^ k)))⌝ ∗ mapping P p A 0 bs) := by
  have hpos := Nat.two_pow_pos k
  have h2 := Ops.toNat_two_pow hk
  unfold mem_alignPointerOffset__anon_1
  gen_norm
  rw [isValidAlign_pow hk]
  gen_norm
  rw [debug_assert_true, le_big hk hk12]
  gen_norm
  refine TotalTriple.of_pure (φ := ∃ b, p.block = some b)
    (fun h hp => let ⟨b, hb, _⟩ := PageSpec.mapping_block hp; ⟨b, hb⟩) fun ⟨b, hb⟩ => ?_
  refine TotalTriple.bind (ptrAddr_owned hb (mapping_owns hb)) fun x =>
    TotalTriple.lift fun hx => ?_
  subst hx
  rw [h0, sub_pow_one hk]
  gen_norm
  rw [align_add hk hfit]
  simp only [show ((0 : BitVec 1) != 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  rw [align_sub hk hfit]
  gen_norm
  rw [rem_one]
  gen_norm
  simp only [show ((0 : BitVec 64) != 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  rw [divTrunc_one]
  gen_norm
  exact TotalTriple.conseq (TotalTriple.ret _) (fun h hm => Zig.sep_lift.mpr ⟨rfl, hm⟩) (fun _ _ x => x)

theorem drop_bounds {A k : Nat} (hk12 : 12 < k) (hA : A % P = 0) :
    drop A (2 ^ k) % P = 0 ∧ drop A (2 ^ k) + P ≤ 2 ^ k ∧ (A + drop A (2 ^ k)) % 2 ^ k = 0 := by
  have hpos := Nat.two_pow_pos k
  have hPk : P ∣ 2 ^ k := by
    show 2 ^ 12 ∣ 2 ^ k; exact Nat.pow_dvd_pow 2 (by omega)
  have hb := alignUp_bounds (A := A) hpos
  have hm : alignUp A (2 ^ k) % 2 ^ k = 0 := alignUp_mod_self hpos
  have hmP : alignUp A (2 ^ k) % P = 0 :=
    Nat.mod_eq_zero_of_dvd (Nat.dvd_trans hPk (Nat.dvd_of_mod_eq_zero hm))
  have hkP : 2 ^ k % P = 0 := Nat.mod_eq_zero_of_dvd hPk
  have e : (P : Nat) = 4096 := rfl
  rw [e] at hA hmP hkP ⊢
  unfold drop
  refine ⟨by omega, by omega, by rw [Nat.add_sub_cancel' hb.1]; exact hm⟩

theorem drop_small {A k : Nat} (hk : k ≤ 12) (hA : A % P = 0) : drop A (2 ^ k) = 0 := by
  have hpos := Nat.two_pow_pos k
  have : A % 2 ^ k = 0 := Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.pow_dvd_pow 2 hk)
    (Nat.dvd_of_mod_eq_zero (by simpa using hA)))
  unfold drop; rw [alignUp_of_mod hpos this]; simp

/-- `std.mem.alignPointer` of a page-aligned mapping start, to any alignment: the pointer
`drop A (2 ^ k)` bytes in (`0` up to a page). -/
theorem alignPointer_gen {p : Ptr} {A : Nat} {bs : Array Byte} {k : Nat} (hk : k < 64)
    (h0 : p.off = 0) (hfit : A + 2 ^ k ≤ 2 ^ 64) :
    TotalTriple (mapping P p A 0 bs) (mem_alignPointer__anon_1 p (BitVec.ofNat 64 (2 ^ k)))
      (fun r => ⌜r = some (p.add (drop A (2 ^ k)))⌝ ∗ mapping P p A 0 bs) := by
  refine TotalTriple.of_pure (φ := A % P = 0) (fun h hp => hp.2.2.1) fun hA => ?_
  by_cases hk12 : k ≤ 12
  · rw [drop_small hk12 hA, Int.natCast_zero, Ptr.add_zero']
    exact alignPointer_total hk12 h0
  have hb := drop_bounds (k := k) (by omega) hA
  unfold mem_alignPointer__anon_1
  gen_norm
  refine TotalTriple.bind (alignPointerOffset_big hk (by omega) h0 hfit) fun r =>
    TotalTriple.lift fun hr => ?_
  subst hr
  have hdl : drop A (2 ^ k) < 2 ^ 64 := by have := Ops.two_pow_lt hk; omega
  have he : p.elem 1 (BitVec.ofNat 64 (drop A (2 ^ k))) = p.add (drop A (2 ^ k)) := by
    simp [Ptr.elem, Nat.mod_eq_of_lt hdl]
  simp only [Option.elim_some, he]
  refine TotalTriple.of_pure (φ := ∃ b, p.block = some b)
    (fun h hp => let ⟨b, hb, _⟩ := PageSpec.mapping_block hp; ⟨b, hb⟩) fun ⟨b, hb'⟩ => ?_
  refine TotalTriple.bind (ptrAddr_owned (q := p.add (drop A (2 ^ k))) hb' (mapping_owns hb')) fun x =>
    TotalTriple.lift fun hx => ?_
  subst hx
  have hP : (A + drop A (2 ^ k)) % 4096 = 0 :=
    Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega : 12 ≤ k))
      (Nat.dvd_of_mod_eq_zero hb.2.2))
  have hoff : (p.add (drop A (2 ^ k))).off = (drop A (2 ^ k) : Int) := by
    simp [Ptr.add, h0]
  have hm := Ops.and_mask_eq_zero (k := 12) (x := (A : Int) + (p.add (drop A (2 ^ k))).off)
    (by decide) (by rw [hoff]; omega) (by rw [hoff]; omega)
  rw [show BitVec.ofNat 64 (2 ^ 12 - 1) = 4095 from rfl] at hm
  rw [if_pos hm]
  exact TotalTriple.conseq (TotalTriple.ret _) (fun h hm => Zig.sep_lift.mpr ⟨rfl, hm⟩)
    (fun _ _ x => x)

/-! ## `map`'s arithmetic and its `munmap`s -/

theorem and4095 (x : BitVec 64) : x &&& 4095 = 0 ↔ x.toNat % 4096 = 0 := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_and] at this
    rw [show (4095 : BitVec 64).toNat = 2 ^ 12 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod] at this
    exact this
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and,
      show (4095 : BitVec 64).toNat = 2 ^ 12 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    exact h

theorem sub_and4095 {x y : BitVec 64} (hx : x &&& 4095 = 0) (hy : y &&& 4095 = 0) :
    (x - y) &&& 4095 = 0 := by
  rw [and4095] at *
  rw [BitVec.toNat_sub]
  have := x.isLt; have := y.isLt
  omega

theorem andNot_and4095 {x : BitVec 64} (m : BitVec 64) (hx : x &&& 4095 = 0) :
    (x &&& ~~~m) &&& 4095 = 0 := by
  rw [BitVec.and_assoc, BitVec.and_comm (~~~m), ← BitVec.and_assoc, hx]; simp

theorem addr64_total {X : Assn} {q : Ptr} {b : BlockId} {A : Nat} (hqb : q.block = some b)
    (hown : ∀ h, X h → OwnsIn b A h) :
    TotalTriple X (do let d ← ptrAddr q; pure (BitVec.ofInt 64 d))
      (fun v => ⌜v = BitVec.ofInt 64 ((A : Int) + q.off)⌝ ∗ X) :=
  TotalTriple.bind (ptrAddr_owned hqb hown) fun _ => TotalTriple.lift fun hd => by
    subst hd
    exact TotalTriple.conseq (TotalTriple.ret _) (fun _ hx => Zig.sep_lift.mpr ⟨rfl, hx⟩)
      (fun _ _ x => x)

theorem tame_addr64 (q : Ptr) : Full.Tame (do let d ← ptrAddr q; pure (BitVec.ofInt 64 d)) :=
  Full.Tame.bind (Full.Tame.ptrAddr q) fun _ => Full.Tame.pure' _

/-- `alignment_bytes -| page_size`: the extra bytes `map` asks for. -/
theorem subSat_pow {k : Nat} (hk : k < 64) :
    Zig.subSat false (BitVec.ofNat 64 (2 ^ k)) 4096 = BitVec.ofNat 64 (2 ^ k - P) := by
  have := Ops.toNat_two_pow hk
  simp only [Zig.subSat, Zig.clamp, Zig.val, Bool.false_eq_true, ↓reduceIte, this]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  have hlt := Ops.two_pow_lt hk
  have e : max (0 : Int) (min (2 ^ 64 - 1) ((2 ^ k : Nat) - (4096 : BitVec 64).toNat)) =
      ((2 ^ k - 4096 : Nat) : Int) := by
    simp only [show (4096 : BitVec 64).toNat = 4096 from rfl]; omega
  rw [e]; show _ = (2 ^ k - 4096) % 2 ^ 64; omega

/-- The extra bytes `2 ^ k -| P` are a page multiple. -/
theorem extra_mod (k : Nat) : (2 ^ k - P) % P = 0 := by
  show (2 ^ k - 4096) % 4096 = 0
  by_cases hk12 : k ≤ 12
  · have := two_pow_le hk12; rw [show 2 ^ k - 4096 = 0 by omega]
  · have := Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 (by omega : 12 ≤ k)); omega

/-- The page check of the derived hint address passes for a page-aligned hint. -/
theorem hint_check {v L G m : BitVec 64} (hv : v &&& 4095 = 0) (hL : L &&& 4095 = 0)
    (hG : G &&& 4095 = 0) : Zig.subWrap (Zig.subWrap v L &&& ~~~m) G &&& 4095 = 0 :=
  sub_and4095 (andNot_and4095 m (sub_and4095 hv hL)) hG

theorem tame_alignPointer {k : Nat} (hk : k < 64) (p : Ptr) :
    Full.Tame (mem_alignPointer__anon_1 p (BitVec.ofNat 64 (2 ^ k))) := by
  unfold mem_alignPointer__anon_1 mem_alignPointerOffset__anon_1
  gen_norm
  rw [isValidAlign_pow hk]
  gen_norm
  tame

/-- `drop` of a page-aligned address: a page multiple, within the extra bytes, to an aligned
address. -/
theorem drop_facts {A k : Nat} (hA : A % P = 0) :
    drop A (2 ^ k) % P = 0 ∧ drop A (2 ^ k) ≤ 2 ^ k - P ∧ (A + drop A (2 ^ k)) % 2 ^ k = 0 := by
  by_cases hk12 : k ≤ 12
  · rw [drop_small hk12 hA]
    refine ⟨rfl, Nat.zero_le _, ?_⟩
    rw [Nat.add_zero]
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.pow_dvd_pow 2 hk12)
      (Nat.dvd_of_mod_eq_zero (by simpa using hA)))
  · obtain ⟨h1, h2, h3⟩ := drop_bounds (k := k) (by omega) hA
    exact ⟨h1, by omega, h3⟩

theorem addr_diff {p : Ptr} {A d : Nat} (h0 : p.off = 0) :
    Zig.subWrap (BitVec.ofInt 64 ((A : Int) + (p.add d).off)) (BitVec.ofInt 64 ((A : Int) + p.off)) =
      BitVec.ofNat 64 d := by
  simp only [Ptr.add, h0, Int.zero_add, Int.add_zero, Zig.subWrap]
  rw [BitVec.ofInt_add, BitVec.add_comm, BitVec.add_sub_cancel, BitVec.ofInt_natCast]

theorem divExact_one (x : BitVec 64) : Zig.divExact false x 1 = pure x := by
  simp only [Zig.divExact, divTrunc_one, pure_bind]
  rw [if_pos (by simp)]

theorem sub_ofNat {M d : Nat} (h : d ≤ M) (hM : M < 2 ^ 64) :
    Zig.sub false (BitVec.ofNat 64 M) (BitVec.ofNat 64 d) = pure (BitVec.ofNat 64 (M - d)) := by
  simp only [Zig.sub, BitVec.usubOverflow, Bool.false_eq_true, ↓reduceIte, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hM, Nat.mod_eq_of_lt (show d < 2 ^ 64 by omega)]
  rw [if_neg (by simp; omega)]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp [Nat.mod_eq_of_lt hM,
    Nat.mod_eq_of_lt (show d < 2 ^ 64 by omega)]; omega)]
  simp [Nat.mod_eq_of_lt hM, Nat.mod_eq_of_lt (show d < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show M - d < 2 ^ 64 by omega)]

theorem le_ofNat {a b : Nat} (h : a ≤ b) (hb : b < 2 ^ 64) :
    Zig.le false (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = true := by
  simp [Zig.le, BitVec.ule, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega), h]

theorem gt_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    Zig.gt false (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (b < a) := by
  rw [Ops.gt_eq]; simp [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt ha]

theorem elem_one {p : Ptr} {n : Nat} (hn : n < 2 ^ 64) : p.elem 1 (BitVec.ofNat 64 n) = p.add n := by
  simp [Ptr.elem, Nat.mod_eq_of_lt hn]

/-- `map`'s first `munmap`: the `d` bytes below the aligned address. -/
theorem munmap_drop {p : Ptr} {A d M : Nat} (hd0 : 0 < d) (hdP : d % P = 0) (hdM : d < M)
    (hMP : M % P = 0) (hM : M < 2 ^ 64) :
    TotalTriple (mapping P p A 0 (Array.replicate M (.int 0)))
      (Os.munmap Os.Target.linux ⟨p, BitVec.ofNat 64 d⟩)
      (fun _ => mapping P (p.add d) A d (Array.replicate (M - d) (.int 0))) := by
  have hdn : (BitVec.ofNat 64 d).toNat = d := by simp; omega
  have hal : alignUp d P = d := alignUp_of_mod (by decide) hdP
  refine TotalTriple.conseq (TotalTriple.munmapPrefix Os.Target.linux (p := p) (lo := 0)
    (bs := Array.replicate M (.int 0)) (len := BitVec.ofNat 64 d) (by omega) ?_) (fun _ x => x)
    fun _ h x => ?_
  · rw [hdn, P_eq, hal, Array.size_replicate, alignUp_of_mod (by decide) hMP]; exact hdM
  · rw [hdn, P_eq, hal, Nat.zero_add, Array.size_replicate, Array.extract_replicate,
      Nat.min_self] at x
    exact x

/-- `map`'s second `munmap`: the pages above the `L` granted bytes. -/
theorem munmap_rest {q : Ptr} {A d L R : Nat} (hL0 : 0 < L) (hLP : L % P = 0) (hLR : L < R)
    (hRP : R % P = 0) (hR : R < 2 ^ 64) :
    TotalTriple (mapping P q A d (Array.replicate R (.int 0)))
      (Os.munmap Os.Target.linux ⟨q.add L, BitVec.ofNat 64 (R - L)⟩)
      (fun _ => mapping P q A d (Array.replicate L (.int 0))) := by
  have hn : (BitVec.ofNat 64 (R - L)).toNat = R - L := by simp; omega
  refine TotalTriple.conseq (TotalTriple.munmapTail Os.Target.linux (p := q) (lo := d) (k := L)
    (bs := Array.replicate R (.int 0)) (len := BitVec.ofNat 64 (R - L)) hLP hL0
    (by simpa using hLR) (by rw [hn]; omega) ?_) (fun _ x => x) fun _ h x => ?_
  · rw [hn, P_eq, Array.size_replicate, alignUp_of_mod (by decide) hRP,
      alignUp_of_mod (by decide) (by
        have h1 : L % 4096 = 0 := hLP; have h2 : R % 4096 = 0 := hRP
        show (R - L) % 4096 = 0; omega)]
    omega
  · rw [Array.extract_replicate, Nat.min_eq_left (Nat.le_of_lt hLR), Nat.sub_zero] at x
    exact x

/-- Weaken the legacy part of a precondition. -/
theorem pre_up_mono {β : Type} {H : FAssn} {X Y : Assn} {c : ConcM Tgt β} {Q : β → FAssn}
    (hxy : ∀ h, X h → Y h) (ht : CTriple (H ⋆ up Y) c Q) : CTriple (H ⋆ up X) c Q :=
  CTriple.pre ht fun _ hr => Full.sep_mono_right (fun _ y => up_mono hxy y) hr

/-- `@ptrFromInt` to `?*T` changes nothing (`FTriple.ptrFromAddr`). -/
theorem optPtrFromAddr_frame {R : Full.FAssn} (n : Nat) :
    Full.FTriple R (optPtrFromAddr n) (fun _ => R) := by
  refine Full.FTriple.of_pure_run (fun m _ => ?_) (fun _ _ h => h)
  unfold optPtrFromAddr
  split
  · exact ⟨_, rfl⟩
  · obtain ⟨v, hv⟩ := Full.ptrFromAddr_run n m
    exact ⟨some v, by simp only [Functor.map, StateT.map, StateT.run] at hv ⊢; rw [hv]; rfl⟩

/-! ## Rearranging full-state assertions -/

section Rearrange

variable {P Q R : FAssn} {r : Res}

theorem lift_out {φ : Prop} (h : (P ⋆ (⟪φ⟫ ⋆ Q)) r) : (⟪φ⟫ ⋆ (P ⋆ Q)) r := by
  obtain ⟨r₁, r₂, hd, rfl, hp, hq⟩ := h
  obtain ⟨hφ, hq⟩ := Full.sep_lift.mp hq
  exact Full.sep_lift.mpr ⟨hφ, ⟨r₁, r₂, hd, rfl, hp, hq⟩⟩

theorem up_lift_out {φ : Prop} {X : Assn} (h : (P ⋆ up (⌜φ⌝ ∗ X)) r) : (⟪φ⟫ ⋆ (P ⋆ up X)) r :=
  lift_out (sep_mono_right (fun _ y => Full.sep_lift.mpr (up_lift.mp y)) h)

/-- A legacy step that returns a known value `a`. -/
theorem step_eq {H : FAssn} {X X' : Assn} {α β : Type} {c : MemM α} {a : α}
    {f : α → ConcM Tgt β} {S : β → FAssn} (ht : TotalTriple X c (fun v => ⌜v = a⌝ ∗ X'))
    (hc : Full.Tame c) (hf : CTriple (H ⋆ up X') (f a) S) :
    CTriple (H ⋆ up X) (ConcM.liftMem c >>= f) S :=
  CTriple.step ht hc fun _ => CTriple.pre (CTriple.lift fun hv => hv ▸ hf) fun _ h => up_lift_out h

theorem swap_last (h : ((P ⋆ Q) ⋆ R) r) : ((P ⋆ R) ⋆ Q) r :=
  Full.sep_assoc' (Full.sep_mono_right (fun _ y => Full.sep_comm y) (Full.sep_assoc h))

/-- An owned byte of block `b` with address `A` in the legacy part gives `know_intro`'s cell. -/
theorem own_cell {X : Assn} {b : BlockId} {A : Nat} (hx : ∀ h, X h → OwnsIn b A h)
    (h : (P ⋆ up X) r) : ∃ x fc, r.heap (b, x) = some fc ∧ fc.cell.addr = A := by
  obtain ⟨r₁, r₂, hd, rfl, -, hX, -⟩ := h
  obtain ⟨o, c, hc, hA⟩ := hx _ hX
  simp only [FHeap.erase, Option.map_eq_some_iff] at hc
  obtain ⟨fc, hfc, rfl⟩ := hc
  refine ⟨o, fc, ?_, hA⟩
  show (r₁.heap (b, o)).or (r₂.heap (b, o)) = some fc
  rcases hd (b, o) with e | e
  · rw [e, hfc]; rfl
  · rw [hfc] at e; cases e

theorem rearr_final {φ : Prop} {X Hk K M : FAssn} (h : ((⟪φ⟫ ⋆ X) ⋆ ((Hk ⋆ K) ⋆ M)) r) :
    ((X ⋆ (K ⋆ M)) ⋆ Hk) r := by
  have h' := Full.sep_mono_left (fun _ y => (Full.sep_lift.mp y).2) h
  exact Full.sep_assoc' (Full.sep_mono_right (fun _ y => Full.sep_comm (Full.sep_assoc y)) h')

end Rearrange

/-! ## The allocator state: the hint word -/

/-- `PageAllocator`'s hint word `addr_hint` (global block 0). -/
abbrev hint : Ptr := ⟨some 0, 0⟩

/-- What the allocator knows of the hinted mapping: its block's address, page-aligned. -/
def HintKn : Option Ptr → FAssn
  | none => FAssn.emp
  | some h => FAssn.ex fun b => FAssn.ex fun A : Nat =>
      ⟪h.block = some b ∧ 0 ≤ h.off ∧ ((A : Int) + h.off) % 4096 = 0⟫ ⋆ known b A

/-- The allocator state: the hint word with its atomic layout, and the knowledge of its target. -/
def own : FAssn := FAssn.ex fun h : Option Ptr => aptsE hint h ⋆ HintKn h

theorem up_pure {φ : Prop} {r : Res} (h : up ⌜φ⌝ r) : FAssn.emp r :=
  up_emp.mp ⟨h.1.2, h.2⟩

theorem hintKn_some {b : BlockId} {A : Nat} {h : Ptr} {r : Res}
    (hr : (⟪h.block = some b ∧ 0 ≤ h.off ∧ ((A : Int) + h.off) % 4096 = 0⟫ ⋆ known b A) r) :
    HintKn (some h) r := by
  unfold HintKn FAssn.ex; exact ⟨b, A, hr⟩

/-- The page allocator's invariant for every entry, for every alignment. -/
def ainv : FAllocInv := inv own

theorem hintKn_heap (e : Option Ptr) (r : Res) (h : HintKn e r) : r.heap = FHeap.empty := by
  cases e with
  | none => exact h.1
  | some p =>
    obtain ⟨b, A, r₁, r₂, -, rfl, ⟨-, h1, -⟩, h2, -⟩ := h
    show r₁.heap ∪ r₂.heap = FHeap.empty
    rw [h1, h2]; rfl

/-- The state after a granted mapping: the hint points to it, and the caller owns it. -/
theorem final_post {p : Ptr} {b : BlockId} {A d L k : Nat} {all : Array Byte} {r : Res}
    (hp : p.block = some b) (hoff : p.off = d) (hA : A % P = 0) (hdP : d % P = 0)
    (hal : (A + d) % 2 ^ k = 0) (hsz : all.size = alignUp L P) (hfit : L + P ≤ 2 ^ 64)
    (h : (aptsE hint (some p) ⋆ (known b A ⋆ up (mapping P p A d all))) r) :
    ainv.allocPost L k (some p) r := by
  have hA' : A % 4096 = 0 := hA
  have hdP' : d % 4096 = 0 := hdP
  have hoff' : p.off.toNat = d := by rw [hoff]; rfl
  have hge := alignUp_ge L
  refine Full.sep_mono (fun _ x => ⟨some p, Full.sep_mono_right (fun _ y =>
      hintKn_some (Full.sep_lift.mpr ⟨⟨hp, by omega, by rw [hoff]; omega⟩, y⟩)) x⟩)
    (fun r' y => (lift_granted_up (J := ainv) (I := legacy) (fun _ _ _ _ _ _ => rfl)).mpr (by
      have hm : mapping P p A p.off.toNat all r'.heap.erase := by rw [hoff']; exact y.1
      exact up_ex.mpr ⟨all.extract 0 L, up_lift.mpr ⟨by simp; omega,
        regrant hm hsz (by omega) (by rw [hoff']; exact hal), y.2⟩⟩))
    (Full.sep_assoc' h)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
theorem alloc_ct (c : Ptr) (len : BitVec 64) (k : Nat) (ra : BitVec 64) (hlen : 0 < len.toNat)
    (hk : k < 64) (hfit : len.toNat + 2 ^ k + P ≤ 2 ^ 64) :
    CTriple (Tgt := Tgt) own (heap_PageAllocator_alloc c len ⟨BitVec.ofNat 6 k⟩ ra)
      (ainv.allocPost len.toNat k) := by
  have h2p : 0 < 2 ^ k := Nat.two_pow_pos k
  have hL := toNat_alignUp (n := len.toNat) (by omega)
  have hLlt := alignUp_lt (n := len.toNat) (P := P) (by decide)
  have hLge := alignUp_ge len.toNat
  have hLm : alignUp len.toNat P % P = 0 := alignUp_mod_self (by decide)
  have hG : (BitVec.ofNat 64 (2 ^ k - P)).toNat = 2 ^ k - P := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hM : (BitVec.ofNat 64 (alignUp len.toNat P + (2 ^ k - P))).toNat =
      alignUp len.toNat P + (2 ^ k - P) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold heap_PageAllocator_alloc heap_PageAllocator_map
  conc_norm
  rw [toByteUnits_eq hk, alignForward_eq (by omega)]
  conc_norm
  rw [subSat_pow hk, Ops.add_ok (by rw [hL, hG]; omega), ← BitVec.ofNat_add, Ops.gt_eq,
    show decide ((0 : BitVec 64).toNat < len.toNat) = true by simpa using hlen, debug_assert_true]
  conc_norm
  by_cases hbig : ge false len 18446744073709547519 = true
  · simp only [hbig, ↓reduceIte]
    exact CTriple.ret' none fun r h => h
  simp only [hbig, Bool.false_eq_true, ↓reduceIte]
  refine CTriple.ex fun e => CTriple.pick_bind ?_
  refine CTriple.bind (CTriple.liftMem (FTriple.atomicLoadUnorderedEnc hint e).frame) fun w => ?_
  refine CTriple.pre (CTriple.lift fun hw => ?_) fun r h => sep_assoc h
  subst hw
  cases w
  case' none => simp only [Option.isNone_none, ↓reduceIte]
  case' some h =>
    simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte, optPtrAddr]
    rw [sub_pow_one hk]
    conc_norm
    refine CTriple.pre (P := FAssn.ex fun b => FAssn.ex fun A : Nat =>
        ⟪h.block = some b ∧ 0 ≤ h.off ∧ ((A : Int) + h.off) % 4096 = 0⟫ ⋆
          (aptsE hint (some h) ⋆ known b A)) ?_ fun r hr => by
      obtain ⟨b, hb⟩ := Full.sep_ex.mp (Full.sep_comm hr)
      obtain ⟨A, hA⟩ := Full.sep_ex.mp hb
      exact ⟨b, A, Full.sep_mono_right (fun _ y => Full.sep_comm y) (Full.sep_assoc hA)⟩
    refine CTriple.ex fun b => CTriple.ex fun A => CTriple.lift fun ⟨hb, ho, hal⟩ => ?_
    obtain ⟨hblk, off⟩ := h
    simp only at hb ho hal
    subst hb
    refine CTriple.bind (CTriple.liftMem (Full.FTriple.bind (Full.FTriple.ptrAddr (A := A) off)
      fun a => Full.FTriple.lift fun ha => Full.FTriple.ret' (Q := fun v =>
        ⟪v = BitVec.ofInt 64 ((A : Int) + off)⟫ ⋆ known b A) _
        fun _ hk => Full.sep_lift.mpr ⟨by rw [ha], hk⟩)).frameL fun v => ?_
    refine CTriple.pre (CTriple.lift fun hv => ?_) fun _ h => lift_out h
    subst hv
    have hv : BitVec.ofInt 64 ((A : Int) + off) &&& 4095 = 0 :=
      Ops.and_mask_eq_zero (k := 12) (by decide) (by omega) hal
    have hL4 : BitVec.ofNat 64 (alignUp len.toNat P) &&& 4095 = 0 := by
      rw [and4095, hL]; exact hLm
    have hG4 : BitVec.ofNat 64 (2 ^ k - P) &&& 4095 = 0 := by
      rw [and4095, hG]; exact extra_mod k
    have hc := hint_check (m := BitVec.ofNat 64 (2 ^ k) - 1) hv hL4 hG4
    simp only [hc, ↓reduceIte]
    refine CTriple.bind (CTriple.liftMem (optPtrFromAddr_frame _)) fun x => ?_
    have hpre : ∀ r, (aptsE hint (some (⟨some b, off⟩ : Ptr)) ⋆ known b A) r →
        (aptsE hint (some (⟨some b, off⟩ : Ptr)) ⋆ HintKn (some (⟨some b, off⟩ : Ptr))) r :=
      fun r hr => Full.sep_mono_right (fun _ hk => hintKn_some (Full.sep_lift.mpr ⟨⟨rfl, ho, hal⟩, hk⟩)) hr
    refine CTriple.pre ?_ hpre
  all_goals
    refine CTriple.pre (CTriple.step (X := Assn.emp) (TotalTriple.mmap Os.Target.linux _
      (BitVec.ofNat 64 (alignUp len.toNat P + (2 ^ k - P))) (by rw [hM]; omega))
      (Full.Tame.mmap _ _ _ _ _ _ _) fun v => ?_)
      fun r hr => Full.sep_mono_right (fun _ y => up_emp.mpr y) (Full.sep_emp.mpr hr)
    rcases v with err | s
    · simp only [isNonErr, isErr, Bool.not_true, Bool.false_eq_true, ↓reduceIte, unwrapErr,
        CNorm.liftMem_lift_pure, pure_bind]
      exact CTriple.ret' none fun r hr =>
        ⟨_, Full.sep_emp.mp (Full.sep_mono_right (fun _ y => up_pure y) hr)⟩
    · simp only [isNonErr, isErr, Bool.not_false, ↓reduceIte, unwrapPayload,
        CNorm.liftMem_lift_pure, pure_bind]
      refine CTriple.pre (P := FAssn.ex fun A : Nat => ⟪s.ptr.off = 0 ∧
          s.len = BitVec.ofNat 64 (alignUp len.toNat P + (2 ^ k - P)) ∧
          A + alignUp (BitVec.ofNat 64 (alignUp len.toNat P + (2 ^ k - P))).toNat
            Os.Target.linux.pageSize ≤ Os.Target.linux.addrLimit⟫ ⋆
          ((aptsE hint _ ⋆ HintKn _) ⋆ up (mapping P s.ptr A 0
            (Array.replicate (BitVec.ofNat 64 (alignUp len.toNat P + (2 ^ k - P))).toNat (.int 0))))) ?_
        fun r hr => by
          obtain ⟨r₁, r₂, hd, rfl, h1, ⟨hsl, ho, A, hAb, hm⟩, hk⟩ := hr
          exact ⟨A, Full.sep_lift.mpr ⟨⟨ho, hsl, hAb⟩, r₁, r₂, hd, rfl, h1, hm, hk⟩⟩
      refine CTriple.ex fun A => CTriple.lift fun ⟨hso, hsl, hAb⟩ => ?_
      rw [hM] at hAb ⊢
      have hMm : (alignUp len.toNat P + (2 ^ k - P)) % P = 0 := by
        have h1 : (2 ^ k - 4096) % 4096 = 0 := extra_mod k
        have h2 : alignUp len.toNat P % 4096 = 0 := hLm
        show (alignUp len.toNat P + (2 ^ k - 4096)) % 4096 = 0; omega
      rw [P_eq, alignUp_of_mod (by decide) hMm] at hAb
      have hAb' : A + (alignUp len.toNat P + (2 ^ k - P)) ≤ 2 ^ 47 := hAb
      refine CTriple.of_pure (φ := ∃ b, s.ptr.block = some b ∧ A % P = 0) (fun r hr => by
        obtain ⟨-, r₂, -, -, -, hm, -⟩ := hr
        obtain ⟨b, hb, -⟩ := PageSpec.mapping_block hm
        exact ⟨b, hb, hm.2.2.1⟩) fun ⟨b, hb, hA⟩ => ?_
      have hfA : A + 2 ^ k ≤ 2 ^ 64 := by
        have : 2 ^ 47 + 4096 ≤ 2 ^ 64 := by decide
        have hP' : (P : Nat) = 4096 := rfl
        omega
      obtain ⟨hdP, hdG, hal'⟩ := drop_facts (k := k) hA
      have hdlt : drop A (2 ^ k) < 2 ^ 64 := by omega
      refine CTriple.know_intro (b := b) (A := A) (fun r hr => own_cell (mapping_owns hb) hr) ?_
      refine CTriple.pre (step_eq (alignPointer_gen hk hso hfA) (tame_alignPointer hk _) ?_)
        fun r hr => swap_last hr
      simp only [Option.isSome_some, ↓reduceIte, optPayload, CNorm.liftMem_lift_pure, pure_bind]
      have hbd : (s.ptr.add (drop A (2 ^ k) : Nat)).block = some b := by simpa [Ptr.add] using hb
      refine step_eq (addr64_total hbd (mapping_owns hb)) (tame_addr64 _) ?_
      refine step_eq (addr64_total hb (mapping_owns hb)) (tame_addr64 _) ?_
      rw [addr_diff hso, divExact_one]
      simp only [CNorm.liftMem_lift_pure, pure_bind]
      have hM64 : alignUp len.toNat P + (2 ^ k - P) < 2 ^ 64 := by omega
      have hLM : alignUp len.toNat P ≤ alignUp len.toNat P + (2 ^ k - P) - drop A (2 ^ k) := by
        omega
      by_cases hd0 : drop A (2 ^ k) = 0
      case' pos =>
        have hz : (BitVec.ofNat 64 (drop A (2 ^ k)) != 0) = false := by rw [hd0]; rfl
        simp only [hz, Bool.false_eq_true, ↓reduceIte]
        refine pre_up_mono (Y := mapping P (s.ptr.add (drop A (2 ^ k) : Nat)) A (drop A (2 ^ k))
          (Array.replicate (alignUp len.toNat P + (2 ^ k - P) - drop A (2 ^ k)) (.int 0)))
          (fun h y => by rw [hd0, Int.natCast_zero, Ptr.add_zero', Nat.sub_zero]; exact y) ?_
      case' neg =>
        have hnz : (BitVec.ofNat 64 (drop A (2 ^ k)) != 0) = true := by
          simp only [bne_iff_ne, ne_eq]
          intro h
          have := congrArg BitVec.toNat h
          simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdlt] at this
          exact hd0 (by simpa using this)
        simp only [hnz, ↓reduceIte, hsl, le_ofNat (by omega : drop A (2 ^ k) ≤
          alignUp len.toNat P + (2 ^ k - P)) hM64]
        refine CTriple.step (munmap_drop (Nat.pos_of_ne_zero hd0) hdP (by omega) hMm hM64)
          (Full.Tame.munmap _ _) fun _ => ?_
      all_goals
        rw [sub_ofNat (by omega) hM64]
        simp only [CNorm.liftMem_lift_pure, pure_bind]
        rw [gt_ofNat (by omega) (by omega)]
        by_cases htl : alignUp len.toNat P < alignUp len.toNat P + (2 ^ k - P) - drop A (2 ^ k)
        case' pos =>
          simp only [htl, decide_true, ↓reduceIte, le_ofNat (Nat.le_of_lt htl) (by omega)]
          rw [sub_ofNat (Nat.le_of_lt htl) (by omega)]
          simp only [CNorm.liftMem_lift_pure, pure_bind]
          rw [elem_one (by omega)]
          have hbq : ((s.ptr.add (drop A (2 ^ k) : Nat)).add (alignUp len.toNat P : Nat)).block =
              some b := by simpa [Ptr.add] using hb
          refine step_eq (addr64_total hbq (mapping_owns hbd)) (tame_addr64 _) ?_
          have hpage : BitVec.ofInt 64 ((A : Int) +
              ((s.ptr.add (drop A (2 ^ k) : Nat)).add (alignUp len.toNat P : Nat)).off) &&& 4095 = 0 := by
            have e : ((s.ptr.add (drop A (2 ^ k) : Nat)).add (alignUp len.toNat P : Nat)).off =
                ((drop A (2 ^ k) + alignUp len.toNat P : Nat) : Int) := by
              simp [Ptr.add, hso]
            have h1 : A % 4096 = 0 := hA
            have h2 : drop A (2 ^ k) % 4096 = 0 := hdP
            have h3 : alignUp len.toNat P % 4096 = 0 := hLm
            have := Ops.and_mask_eq_zero (k := 12) (x := (A : Int) +
              ((s.ptr.add (drop A (2 ^ k) : Nat)).add (alignUp len.toNat P : Nat)).off) (by decide)
              (by rw [e]; omega) (by rw [e]; omega)
            exact this
          simp only [hpage, beq_self_eq_true, Bool.or_true, ↓reduceIte]
          refine CTriple.step (munmap_rest (by omega) hLm htl ?_ (by omega))
            (Full.Tame.munmap _ _) fun _ => ?_
          have h1 : (alignUp len.toNat P + (2 ^ k - P)) % 4096 = 0 := hMm
          have h2 : drop A (2 ^ k) % 4096 = 0 := hdP
          show (alignUp len.toNat P + (2 ^ k - P) - drop A (2 ^ k)) % 4096 = 0
          omega
        case' neg =>
          simp only [htl, decide_false, Bool.false_eq_true, ↓reduceIte]
          refine pre_up_mono (Y := mapping P (s.ptr.add (drop A (2 ^ k) : Nat)) A (drop A (2 ^ k))
            (Array.replicate (alignUp len.toNat P) (.int 0)))
            (fun h y => by
              rw [show alignUp len.toNat P + (2 ^ k - P) - drop A (2 ^ k) = alignUp len.toNat P by
                omega] at y
              exact y) ?_
      all_goals
        refine CTriple.pick_bind ?_
        refine CTriple.pre ?_ fun r hr =>
          Full.sep_mono_right (fun _ y => Full.sep_assoc' y) (Full.sep_assoc (Full.sep_assoc hr))
        refine CTriple.bind (CTriple.liftMem
          (FTriple.cmpxchgPtr rfl hint _ (some (s.ptr.add (drop A (2 ^ k) : Nat))) .relaxed
            .relaxed).frame) fun _ => ?_
        refine CTriple.pre ?_ fun r hr => rearr_final hr
        exact CTriple.forget (hintKn_heap _) (CTriple.ret' _ fun r hr =>
          final_post (all := Array.replicate (alignUp len.toNat P) (.int 0)) hbd
            (by simp [Ptr.add, hso]) hA hdP hal' (by rw [Array.size_replicate]) (by omega) hr)

/-! ## The vtable -/

/-- The translated vtable: `alloc` (a concurrent function: its hint is an atomic) is called in the
caller's thread (`Sched.soloRun`); `resize`, `remap` and `free` as in `PageSpec.vt`. -/
def vt : RawVTable :=
  { PageSpec.vt with
    alloc := fun c len k ra =>
      Sched.soloRun 16 (heap_PageAllocator_alloc c len ⟨BitVec.ofNat 6 k⟩ ra) }

/-- **`alloc`**, for every alignment. -/
theorem alloc_spec (c : Ptr) (len : BitVec 64) (k : Nat) (ra : BitVec 64) (hlen : 0 < len.toNat)
    (hk : k < 64) (hfit : ainv.fits len.toNat k) :
    FTriple ainv.own (vt.alloc c len k ra) (ainv.allocPost len.toNat k) :=
  alloc_ct c len k ra hlen hk hfit 16

/-- **The translated `PageAllocator` satisfies `FAllocSpec`** (partial correctness), for every
alignment, from the generated code and OSM-01 only. -/
theorem fallocSpec (c : Ptr) : FAllocSpec FLogic.partial vt c ainv where
  alloc len k ra hlen hk hfit := alloc_spec c len k ra hlen hk hfit
  resize s k n ra bs hk hn hfit hs hpos :=
    (resize_spec (own := own) c s k n ra bs hk hn hfit hs hpos).toPartial
  remap s k n ra bs hk hn hfit hs hpos :=
    (remap_spec (own := own) c s k n ra bs hk hn hfit hs hpos).toPartial
  free s k ra bs _ hs hpos := (free_spec (own := own) c s k ra bs hs hpos).toPartial

/-! ## O5 regression: alignments above a page -/

/-- `mem0`, with the next mapping at the last page below `2 ^ 64`. -/
def high : Mem := { mem0 with nextAddr := 2 ^ 64 - 4096 }

/-- **O5, fixed.** Before the OS model bounded the address space, `alloc(1, align 8192)` from
`high` mapped two pages at `2 ^ 64 - 4096`, the alignment `@intFromPtr(p) + 8191` of
`std.mem.alignPointer` overflowed and `PageAllocator.map` panicked. Now that `mmap` fails with
`ENOMEM` above `Os.Target.addrLimit` (OSM-01), `alloc` returns `null`, as natively. -/
theorem alloc_high : (((vt.alloc ⟨none, 0⟩ 1 13 0).run high).run.map fun r =>
    match r with | .ok (v, _) => decide (v = none) | _ => false) = some true := by
  decide +kernel

/-- `mem0`, with the next mapping three pages below the end of the address space. -/
def top : Mem := { mem0 with nextAddr := 2 ^ 47 - 12288 }

/-- Near the end of the address space, `alloc(1, align 8192)` maps two pages at
`2 ^ 47 - 12288`, unmaps the first one (`TotalTriple.munmapPrefix`) and returns the second. -/
theorem alloc_top : (((vt.alloc ⟨none, 0⟩ 1 13 0).run top).run.map fun r =>
    match r with | .ok (some p, _) => decide (p.off = 4096) | _ => false) = some true := by
  decide +kernel

/-! ## The scheduler's reading -/

/-- `alloc` stops only at its two atomic ops' oracle picks, which one thread answers itself. -/
theorem alloc_threadFree (c : Ptr) (len : BitVec 64) (a : mem_Alignment) (ra : BitVec 64) :
    ConcM.ThreadFree (heap_PageAllocator_alloc c len a ra) := by
  unfold heap_PageAllocator_alloc heap_PageAllocator_map
  conc_norm
  set_option maxRecDepth 8192 in repeat' (first
    | apply Sched.ThreadFreeC.bind
    | apply Sched.ThreadFreeC.ite
    | apply Sched.ThreadFreeC.liftMem
    | apply Sched.ThreadFreeC.pure'
    | apply Sched.ThreadFreeC.throw
    | exact Sched.ThreadFreeC.sync rfl
    | split
    | (guard_target = ∀ _, _; intro _))

/-- So a one-thread scheduler run of `alloc` is its sequential reading (`Sched.run_eq_seqRun`). -/
theorem alloc_run (c : Ptr) (len : BitVec 64) (a : mem_Alignment) (ra : BitVec 64) (m : Mem) :
    Sched.run dispatch 16 (fun _ => 0) (heap_PageAllocator_alloc c len a ra) m =
      (Sched.seqRun 16 (heap_PageAllocator_alloc c len a ra)).run m :=
  Sched.run_eq_seqRun dispatch 16 (alloc_threadFree c len a ra) m

end AllocTranslated.PageAlloc
