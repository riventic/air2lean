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
* **Alignments up to a page** (`ainv.fits`: `k ≤ 12`, obstruction O5). For a larger alignment,
  `map` asks for extra pages and `std.mem.alignPointer` adds `alignment - 1` to the mapping's
  address with an overflow check. The model's addresses are unbounded (`Mem.nextAddr` is a
  `Nat`; `mmap` places a mapping at any page address), so the check can fail and `map` panics:
  `alloc_high` (kernel-checked) is such a run from `mem0` with a high `nextAddr`. Natively the
  kernel never maps that high. The fix is in the OS model (an `mmap` that ends above the address
  space fails with `ENOMEM`); with it, larger alignments need the prefix and tail `munmap`s,
  which `TotalTriple.munmapPrefix`/`munmapTail` already cover.
* **Partial correctness.** The atomic rules are partial (`FTriple`); `free`, `resize` and
  `remap` are total (`PageSpec.lean`).
-/

namespace AllocTranslated.PageAlloc

open Zig Zig.Region AllocTranslated.PageLinux AllocTranslated.PageSpec Zig.Full Zig.Full.FAssn

/-! ## Page arithmetic for alignments up to a page -/

theorem two_pow_le {k : Nat} (hk : k ≤ 12) : 2 ^ k ≤ 4096 :=
  Nat.le_trans (Nat.pow_le_pow_right (n := 2) (by decide) hk) (by decide)

theorem subSat_small {k : Nat} (hk : k ≤ 12) :
    Zig.subSat false (BitVec.ofNat 64 (2 ^ k)) 4096 = 0 := by
  have := two_pow_le hk
  simp only [Zig.subSat, Zig.clamp, Zig.val, Bool.false_eq_true, ↓reduceIte]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt]
  have e : max (0 : Int) (min (2 ^ 64 - 1) ((2 ^ k : Nat) - (4096 : BitVec 64).toNat)) = 0 := by
    simp only [show (4096 : BitVec 64).toNat = 4096 from rfl]; omega
  rw [e]; rfl

theorem alignPointerOffset_small {k : Nat} (hk : k ≤ 12) (p : Ptr) :
    mem_alignPointerOffset__anon_1 p (BitVec.ofNat 64 (2 ^ k)) = pure (some 0) := by
  have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨
    k = 10 ∨ k = 11 ∨ k = 12 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · unfold mem_alignPointerOffset__anon_1
    gen_norm
    rfl


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
  refine TotalTriple.bind (ptrAddr_owned (A := A) hb fun h hp => by
    obtain ⟨b', hb', ho⟩ := PageSpec.mapping_block hp
    rw [hb] at hb'; cases hb'; exact ho) fun x => TotalTriple.lift fun hx => ?_
  subst hx
  rw [addr_mask (by omega) hA (by rw [h0]; rfl)]
  simp only [↓reduceIte]
  exact TotalTriple.conseq (TotalTriple.ret (Q := fun r => ⌜r = some p⌝ ∗ mapping P p A 0 bs) _)
    (fun h hm => sep_lift.mpr ⟨rfl, hm⟩) (fun _ _ x => x)


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

/-- The page check of the derived hint address passes for a page-aligned hint. -/
theorem hint_check {v L m : BitVec 64} (hv : v &&& 4095 = 0) (hL : L &&& 4095 = 0) :
    Zig.subWrap (Zig.subWrap v L &&& ~~~m) 0 &&& 4095 = 0 := by
  have e : ∀ y : BitVec 64, y - 0 = y := fun y => by simp
  simp only [Zig.subWrap, e]
  exact andNot_and4095 m (sub_and4095 hv hL)

theorem sub_two_pow_one {k : Nat} (hk : k ≤ 12) :
    Zig.sub false (BitVec.ofNat 64 (2 ^ k)) 1 = pure (BitVec.ofNat 64 (2 ^ k) - 1) := by
  have := Nat.two_pow_pos k
  have := two_pow_le hk
  simp only [Zig.sub, BitVec.usubOverflow, Bool.false_eq_true, ↓reduceIte]
  rw [if_neg (by simp; rw [Nat.mod_eq_of_lt (by omega)]; omega)]

theorem divExact_self (v : BitVec 64) : Zig.divExact false (Zig.subWrap v v) 1 = pure 0 := by
  simp only [Zig.subWrap, BitVec.sub_self]; rfl

theorem gt_self (v : BitVec 64) : Zig.gt false v v = false := by
  simp [Zig.gt, Zig.lt, BitVec.ult]

/-- `@intFromPtr` of an owned pointer, as the generated `usize`. -/
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

theorem tame_alignPointer {k : Nat} (hk : k ≤ 12) (p : Ptr) :
    Full.Tame (mem_alignPointer__anon_1 p (BitVec.ofNat 64 (2 ^ k))) := by
  unfold mem_alignPointer__anon_1
  gen_norm
  rw [alignPointerOffset_small hk]
  simp only [pure_bind, Option.elim_some]
  tame

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

/-- The page allocator's invariant for every entry: alignments up to a page. -/
def ainv : FAllocInv := { inv own with fits := fun n k => n + 2 ^ k + P ≤ 2 ^ 64 ∧ k ≤ 12 }

theorem hintKn_heap (e : Option Ptr) (r : Res) (h : HintKn e r) : r.heap = FHeap.empty := by
  cases e with
  | none => exact h.1
  | some p =>
    obtain ⟨b, A, r₁, r₂, -, rfl, ⟨-, h1, -⟩, h2, -⟩ := h
    show r₁.heap ∪ r₂.heap = FHeap.empty
    rw [h1, h2]; rfl

/-- The state after a granted mapping: the hint points to it, and the caller owns it. -/
theorem final_post {p : Ptr} {b : BlockId} {A L k : Nat} {all : Array Byte} {r : Res}
    (hp : p.block = some b) (hoff : p.off = 0) (hA : A % P = 0) (hk : k ≤ 12)
    (hsz : all.size = alignUp L P) (hfit : L + P ≤ 2 ^ 64)
    (h : (aptsE hint (some p) ⋆ (known b A ⋆ up (mapping P p A 0 all))) r) :
    ainv.allocPost L k (some p) r := by
  have hA' : A % 4096 = 0 := hA
  have hal : (A + p.off.toNat) % 2 ^ k = 0 := by
    rw [hoff]
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.pow_dvd_pow 2 hk)
      (Nat.dvd_of_mod_eq_zero (by simpa using hA')))
  have hge := alignUp_ge L
  refine Full.sep_mono (fun _ x => ⟨some p, Full.sep_mono_right (fun _ y =>
      hintKn_some (Full.sep_lift.mpr ⟨⟨hp, by omega, by rw [hoff]; omega⟩, y⟩)) x⟩)
    (fun r' y => (lift_granted_up (J := ainv) (I := legacy) (fun _ _ _ _ _ _ => rfl)).mpr (by
      have hm : mapping P p A p.off.toNat all r'.heap.erase := by simpa [hoff] using y.1
      exact up_ex.mpr ⟨all.extract 0 L, up_lift.mpr ⟨by simp; omega,
        regrant hm hsz (by omega) hal, y.2⟩⟩))
    (Full.sep_assoc' h)

theorem alloc_ct (c : Ptr) (len : BitVec 64) (k : Nat) (ra : BitVec 64) (hlen : 0 < len.toNat)
    (hk : k ≤ 12) (hfit : len.toNat + 2 ^ k + P ≤ 2 ^ 64) :
    CTriple (Tgt := Tgt) own (heap_PageAllocator_alloc c len ⟨BitVec.ofNat 6 k⟩ ra)
      (ainv.allocPost len.toNat k) := by
  have h2 := two_pow_le hk
  have h2p : 0 < 2 ^ k := Nat.two_pow_pos k
  have hL := toNat_alignUp (n := len.toNat) (by omega)
  have hLlt := alignUp_lt (n := len.toNat) (P := P) (by decide)
  unfold heap_PageAllocator_alloc heap_PageAllocator_map
  conc_norm
  rw [toByteUnits_eq (by omega), alignForward_eq (by omega)]
  conc_norm
  have hadd : BitVec.ofNat 64 (alignUp len.toNat P) + 0 = BitVec.ofNat 64 (alignUp len.toNat P) :=
    BitVec.add_zero _
  rw [subSat_small hk, Ops.add_ok (by rw [hL]; simp; omega), hadd, Ops.gt_eq,
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
    rw [sub_two_pow_one hk]
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
      rw [and4095, hL]; exact alignUp_mod_self (by decide)
    rw [if_pos (hint_check hv hL4)]
    refine CTriple.bind (CTriple.liftMem (optPtrFromAddr_frame _)) fun x => ?_
    refine CTriple.pre (P := aptsE hint (some (⟨some b, off⟩ : Ptr)) ⋆ HintKn (some (⟨some b, off⟩ : Ptr))) ?_
      fun r hr => Full.sep_mono_right (fun _ hk => hintKn_some (Full.sep_lift.mpr ⟨⟨rfl, ho, hal⟩, hk⟩)) hr
  all_goals
    refine CTriple.pre (CTriple.step (X := Assn.emp) (TotalTriple.mmap Os.Target.linux _
      (BitVec.ofNat 64 (alignUp len.toNat P)) (by rw [hL]; exact alignUp_pos hlen))
      (Full.Tame.mmap _ _ _ _ _ _ _) fun v => ?_)
      fun r hr => Full.sep_mono_right (fun _ y => up_emp.mpr y) (Full.sep_emp.mpr hr)
    rcases v with err | s
    · simp only [isNonErr, isErr, Bool.not_true, Bool.false_eq_true, ↓reduceIte, unwrapErr,
        CNorm.liftMem_lift_pure, pure_bind]
      exact CTriple.ret' none fun r hr =>
        ⟨_, Full.sep_emp.mp (Full.sep_mono_right (fun _ y => up_pure y) hr)⟩
    · simp only [isNonErr, isErr, Bool.not_false, ↓reduceIte, unwrapPayload,
        CNorm.liftMem_lift_pure, pure_bind]
      refine CTriple.pre (P := FAssn.ex fun A : Nat => ⟪s.ptr.off = 0⟫ ⋆
          ((aptsE hint _ ⋆ HintKn _) ⋆ up (mapping P s.ptr A 0
            (Array.replicate (BitVec.ofNat 64 (alignUp len.toNat P)).toNat (.int 0))))) ?_
        fun r hr => by
          obtain ⟨r₁, r₂, hd, rfl, h1, ⟨-, ho, A, hm⟩, hk⟩ := hr
          exact ⟨A, Full.sep_lift.mpr ⟨ho, r₁, r₂, hd, rfl, h1, hm, hk⟩⟩
      refine CTriple.ex fun A => CTriple.lift fun hso => ?_
      refine CTriple.of_pure (φ := ∃ b, s.ptr.block = some b ∧ A % P = 0) (fun r hr => by
        obtain ⟨-, r₂, -, -, -, hm, -⟩ := hr
        obtain ⟨b, hb, -⟩ := PageSpec.mapping_block hm
        exact ⟨b, hb, hm.2.2.1⟩) fun ⟨b, hb, hA⟩ => ?_
      have hown : ∀ h, mapping P s.ptr A 0
          (Array.replicate (BitVec.ofNat 64 (alignUp len.toNat P)).toNat (.int 0)) h →
          OwnsIn b A h := fun h hm => by
        obtain ⟨b', hb', ho⟩ := PageSpec.mapping_block hm
        rw [hb] at hb'; cases hb'; exact ho
      refine CTriple.know_intro (b := b) (A := A) (fun r hr => own_cell hown hr) ?_
      refine CTriple.pre (step_eq (alignPointer_total hk hso) (tame_alignPointer hk _) ?_)
        fun r hr => swap_last hr
      simp only [Option.isSome_some, ↓reduceIte, optPayload, CNorm.liftMem_lift_pure, pure_bind]
      refine step_eq (addr64_total hb hown) (tame_addr64 _) ?_
      refine step_eq (addr64_total hb hown) (tame_addr64 _) ?_
      simp only [divExact_self, CNorm.liftMem_lift_pure, pure_bind, bne_self_eq_false,
        Bool.false_eq_true, ↓reduceIte, Norm.sub_zero, gt_self]
      refine CTriple.pick_bind ?_
      refine CTriple.pre ?_ fun r hr =>
        Full.sep_mono_right (fun _ y => Full.sep_assoc' y) (Full.sep_assoc (Full.sep_assoc hr))
      refine CTriple.bind (CTriple.liftMem
        (FTriple.cmpxchgPtr rfl hint _ (some s.ptr) .relaxed .relaxed).frame) fun _ => ?_
      refine CTriple.pre ?_ fun r hr => rearr_final hr
      exact CTriple.forget (hintKn_heap _) (CTriple.ret' _ fun r hr =>
        final_post (all := Array.replicate (BitVec.ofNat 64 (alignUp len.toNat P)).toNat (.int 0))
          hb hso hA hk (by rw [Array.size_replicate, hL]) (by omega) hr)

/-! ## The vtable -/

/-- The translated vtable: `alloc` (a concurrent function: its hint is an atomic) is called in the
caller's thread (`Sched.soloRun`); `resize`, `remap` and `free` as in `PageSpec.vt`. -/
def vt : RawVTable :=
  { PageSpec.vt with
    alloc := fun c len k ra =>
      Sched.soloRun 16 (heap_PageAllocator_alloc c len ⟨BitVec.ofNat 6 k⟩ ra) }

/-- **`alloc`**, for alignments up to a page. -/
theorem alloc_spec (c : Ptr) (len : BitVec 64) (k : Nat) (ra : BitVec 64) (hlen : 0 < len.toNat)
    (hfit : ainv.fits len.toNat k) :
    FTriple ainv.own (vt.alloc c len k ra) (ainv.allocPost len.toNat k) :=
  alloc_ct c len k ra hlen hfit.2 hfit.1 16

/-- **The translated `PageAllocator` satisfies `FAllocSpec`** (partial correctness), for
alignments up to a page, from the generated code and OSM-01 only. -/
theorem fallocSpec (c : Ptr) : FAllocSpec FLogic.partial vt c ainv where
  alloc len k ra hlen _ hfit := alloc_spec c len k ra hlen hfit
  resize s k n ra bs hk hn hfit hs hpos :=
    (resize_spec (own := own) c s k n ra bs hk hn hfit.1 hs hpos).toPartial
  remap s k n ra bs hk hn hfit hs hpos :=
    (remap_spec (own := own) c s k n ra bs hk hn hfit.1 hs hpos).toPartial
  free s k ra bs _ hs hpos := (free_spec (own := own) c s k ra bs hs hpos).toPartial

/-! ## O5: alignments above a page -/

/-- `mem0`, with the next mapping at the last page below `2 ^ 64`. The model's addresses are
unbounded, and `mmap` places a mapping at any page address. -/
def high : Mem := { mem0 with nextAddr := 2 ^ 64 - 4096 }

/-- **O5.** `alloc(1, align 8192)` from `high` maps two pages at `2 ^ 64 - 4096`; the alignment
`@intFromPtr(p) + 8191` of `std.mem.alignPointer` overflows, `alignPointer` returns `null`, and
`PageAllocator.map` panics. So no invariant that `high` satisfies admits `k = 13`. -/
theorem alloc_high : (((vt.alloc ⟨none, 0⟩ 1 13 0).run high).run.map fun r =>
    match r with | .error e => decide (e = .panic) | _ => false) = some true := by
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
