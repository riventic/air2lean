import AllocFba.Full
import Proofs.Lists.Append
import ZigLean.Sep.Full.AllocBridge
import ZigLean.Sep.Full.WitnessStart
import ZigLean.Witness

/-!
# The list theorems' premises hold for the real `FixedBufferAllocator`

`Lists.Append.append_spec` and `Lists.Alloc.push_spec` hold for every allocator whose environment
entries meet `CAllocSpec` (`Proofs/Lists/Append.lean`, `Alloc.lean`). Here that assumption and the
precondition are met by a concrete program and memory, so the theorems are not vacuous:

* **The environment** (`ext`, `env0`): the functions at the vtable entries `fns` run the
  translated `FixedBufferAllocator` (`tests/roadmap/alloc-fba/AllocFba/Gen.lean`), every other
  pointer is `.illegal` (`env_runs`). Its contract comes from the allocator's proof
  (`AllocFba.FBA.fallocSpec`) through the library bridge `CAllocSpec.env_ofRaw`
  (`ZigLean/Sep/Full/AllocBridge.lean`): nothing here is assumed about the allocator.
* **The memory** (`gs`): the program's globals at start, under any placement: the allocator
  struct (`end_index = 0`, its 16-byte buffer), the buffer, the vtable (a `const`), an empty list
  header. `start_admissible` shows the precondition there: the start resources with the claims of every
  global (`FAdmit.init_claims`) become, by updates that keep the memory (`FAdmit.eupd`), the
  allocator's invariant (`AllocFba.FBA.fown`: the struct's words, the free tail and its claim,
  half of the buffer's extent lent off its authority, junk), the fee (the allocator charges none:
  `FAllocInv.fee` is `emp`), the list (`alist` of `[]`, whose items pointer is the header's own
  block) and the vtable (`vtR_intro`); the rest joins the frame (`FAdmit.frame`). The buffer's
  region view and its bound close by `fsym_entail` (`buffer_parts`, `MemFacts.regionIn_bound`).
* `Lists.Append.append_spec.nonvacuous`, `Lists.Alloc.push_spec.nonvacuous`: the companions
  that the claims extractor checks against the statements (`docs/claim-strength.md`);
  `check.sh` runs the extractor over the two proof modules and this one.
-/

namespace ListsFba

open Zig Zig.Full Zig.Witness Zig.Full.FAssn AllocFba.FBA

/-! ## The environment: the translated `FixedBufferAllocator` at the vtable `fns` -/

/-- The function pointers of the vtable. -/
def fns : VTableFns := ⟨⟨none, 4096⟩, ⟨none, 4112⟩, ⟨none, 4128⟩, ⟨none, 4144⟩⟩

def ctx : Ptr := ⟨some 0, 0⟩
def bufp : Ptr := ⟨some 1, 0⟩
def vtp : Ptr := ⟨some 2, 0⟩
def hdr : Ptr := ⟨some 3, 0⟩

/-- The environment of the lists program: the allocator's entries at `fns`, nothing elsewhere. -/
instance ext : Lists.Open.Ext where
  call0 f c n a ra := if f = fns.alloc then
    ConcM.liftMem (AllocFba.Gen.heap_FixedBufferAllocator_alloc c n ⟨a.bits⟩ ra) else throw .illegal
  call1 f c s a n ra := if f = fns.remap then
    ConcM.liftMem (AllocFba.Gen.heap_FixedBufferAllocator_remap c s ⟨a.bits⟩ n ra) else throw .illegal
  call2 f c s a ra := if f = fns.free then
    ConcM.liftMem (AllocFba.Gen.heap_FixedBufferAllocator_free c s ⟨a.bits⟩ ra) else throw .illegal

/-- The environment's `resize` (the program never calls it). -/
def env0 : AllocEnv Lists.Open.Tgt :=
  { AllocEnv.closed with
    resize := fun f a => if f = fns.resize then
      ConcM.liftMem (AllocFba.impl.resize a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2) else throw .illegal }

/-- The environment's allocator at `fns` runs the translated `FixedBufferAllocator`. -/
theorem env_runs : CVTable.env (Lists.Alloc.env env0) fns = CVTable.ofRaw AllocFba.impl := by
  simp only [CVTable.env, CVTable.ofRaw, Lists.Alloc.env, env0, Lists.Alloc.al, extCall, AllocFba.impl,
    CVTable.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext <;> first | rfl | simp [ext]

/-! ## The globals -/

/-- A `Result` that the kernel evaluates to `v`. -/
theorem result_eq {ε α : Type} [DecidableEq α] (r : Option (Except ε α)) {v : α}
    (h : (match r with | some (.ok w) => decide (w = v) | _ => false) = true) : r = some (.ok v) := by
  match r, h with
  | some (.ok w), h => simp only [decide_eq_true_eq] at h; subst h; rfl

/-- The allocator struct: `end_index = 0` and the buffer slice. -/
def bs0 : Array Byte := Enc.encode (0 : BitVec 64) ++ Enc.encode (⟨bufp, 16⟩ : Slice)
/-- The vtable. -/
def bs2 : Array Byte :=
  Enc.encode fns.alloc ++ Enc.encode fns.resize ++ Enc.encode fns.remap ++ Enc.encode fns.free
/-- The header of an empty list whose items pointer is the header's own block. -/
def bs3 : Array Byte := Enc.encode (Lists.Append.hdrVal hdr 0 0)

theorem bs0_size : bs0.size = 24 := by decide +kernel
theorem bs2_size : bs2.size = 32 := by decide +kernel
theorem bs3_size : bs3.size = 32 := by decide +kernel

theorem bs3_decode : Enc.decode bs3 = pure (Lists.Append.hdrVal hdr 0 0) := result_eq _ (by decide +kernel)
theorem bs0_decode1 : Enc.decode (bs0.extract 0 8) = pure (0 : BitVec 64) := result_eq _ (by decide +kernel)
theorem bs0_decode2 : Enc.decode (bs0.extract 8 24) = pure (⟨bufp, 16⟩ : Slice) :=
  result_eq _ (by decide +kernel)
theorem bs2_decode : ∀ i (hi : i < fns.toList.length),
    Enc.decode (bs2.extract (8 * i) (8 * i + 8)) = pure fns.toList[i] := by
  intro i hi
  simp only [VTableFns.toList, List.length_cons, List.length_nil] at hi
  match i, hi with
  | 0, _ => simp only [VTableFns.toList, List.getElem_cons_zero]; exact result_eq _ (by decide +kernel)
  | 1, _ => simp only [VTableFns.toList, List.getElem_cons_succ, List.getElem_cons_zero]
            exact result_eq _ (by decide +kernel)
  | 2, _ => simp only [VTableFns.toList, List.getElem_cons_succ, List.getElem_cons_zero]
            exact result_eq _ (by decide +kernel)
  | 3, _ => simp only [VTableFns.toList, List.getElem_cons_succ, List.getElem_cons_zero]
            exact result_eq _ (by decide +kernel)

/-- The program's globals: the allocator struct, its buffer, the vtable (a `const`), the list
header. -/
def gs : List (Array Byte × Nat × BlockKind) :=
  [(bs0, 8, .global), (Array.replicate 16 .undef, 8, .global), (bs2, 8, .constGlobal), (bs3, 8, .global)]

theorem fit : Mem.GlobalsFit gs := by
  unfold Mem.GlobalsFit; simp [gs, bs0_size, bs2_size, bs3_size]

theorem lo : ∀ g ∈ gs, g.2.2.mappedLo = 0 := by simp [gs, BlockKind.mappedLo]

/-! ## The precondition at program start -/

/-- The buffer (global 1, address `A1`) of the allocator struct (global 0, address `A0`). -/
def B (A1 A0 : Nat) : FBuf := ⟨bufp, 16, A1, 16, .global, A0⟩

/-- Global 0 holds the allocator struct's two words. -/
theorem struct_words (A1 A0 : Nat) (h0 : A0 % 8 = 0) {r : Res}
    (h : up (bytesAt ⟨some 0, 0⟩ A0 24 .global bs0) r) : (wEnd ctx 0 ⋆ wBuf ctx (B A1 A0)) r := by
  refine up_sep (up_imp (fun _ hb => ?_) h)
  obtain ⟨h₁, h₂, hd, he, hb₁, hb₂⟩ := bytesAt_split (k := 8) hb (by rw [bs0_size]; omega)
  rw [bs0_size] at hb₂
  refine ⟨h₁, h₂, hd, he, ⟨A0, 24, .global, _, by simpa [ctx] using h0, by decide +kernel,
    bs0_decode1, hb₁, by decide⟩, ⟨A0, 24, .global, _, ?_, by decide +kernel, bs0_decode2, hb₂, by decide⟩⟩
  simp only [ctx, Ptr.add]; omega

attribute [local fsym_facts] MemFacts.bytesAt_bound MemFacts.regionIn_bound in
/-- Global 1 is the free buffer: its bytes and claim, half of its extent lent off its authority,
and the bound of its block (`MemFacts.bytesAt_bound`). -/
theorem buffer_parts (A1 A0 : Nat) :
    EUpd (up (bytesAt ⟨some 1, 0⟩ A1 16 .global (Array.replicate 16 .undef)) ⋆
        (bext 1 16 .global ⋆ bclaim 1 0 16))
      (⟪A1 + 0 + 16 ≤ 2 ^ 63⟫ ⋆ ((ftail (B A1 A0) 0 (Array.replicate 16 .undef) ⋆ fclaim (B A1 A0) 0 1) ⋆
        (bshare 1 Frac.one.half (bnd (B A1 A0)) ⋆ bauth 1 16 .global Frac.one.half))) := by
  fsym_entail

/-- Global 3 is an empty list: the header, the address of its items pointer's block, and the
list's unspent fee. -/
theorem header_parts (I : FAllocInv) (φ : Frac) (A3 : Nat) (h3 : A3 % 8 = 0) {r : Res}
    (h : (up (bytesAt ⟨some 3, 0⟩ A3 32 .global bs3) ⋆ (known 3 A3 ⋆ I.fee φ)) r) :
    Lists.Append.alist I φ hdr [] r := by
  refine ⟨hdr, 0, 0, Full.sep_lift.mpr ⟨⟨rfl, Nat.le_refl _, by decide⟩, ?_⟩⟩
  simp only [Lists.Append.buf]
  refine sep_mono_left (fun _ h => up_imp (fun _ hb => ?_) h)
    (sep_mono_right (fun _ h => sep_mono_left (fun _ h => ⟨3, A3, Full.sep_lift.mpr ⟨rfl, h⟩⟩) h) h)
  exact ⟨A3, 32, .global, bs3, by simpa [hdr] using h3, bs3_size, bs3_decode, hb, by decide⟩

/-- What is left of the start resources besides the precondition (it joins the frame). -/
def left (A2 : Nat) : FAssn :=
  bauth 1 16 .global Frac.one.half ⋆ (up (bytesAt vtp A2 32 .constGlobal bs2) ⋆
    (known 2 A2 ⋆ (bext 0 24 .global ⋆ (bext 2 32 .constGlobal ⋆ (bext 3 32 .global ⋆
      (bclaim 3 0 32 ⋆ (bclaim 2 0 32 ⋆ bclaim 0 0 24)))))))

/-- **The precondition of `append` (and of `push`) over the real `FixedBufferAllocator` holds in
the memory at program start**: the allocator's invariant over the struct and its buffer, the
fee (the allocator charges none: `emp`), an empty list, the vtable. -/
theorem start_admissible (φ : Frac) : ∃ A1 A0, FAdmit ((finv ctx (B A1 A0)).own ⋆
    ((finv ctx (B A1 A0)).fee φ ⋆ (Lists.Append.alist (finv ctx (B A1 A0)) φ hdr [] ⋆
      vtR vtp fns.toList))) := by
  have h := FAdmit.init_claims Placement.fresh gs fit lo
  simp only [globals, gclaims, gs, List.length_cons, List.length_nil, sepN, gblock, gext,
    List.getElem?_cons_succ, List.getElem?_cons_zero, Nat.reduceAdd, bs0_size, bs2_size, bs3_size,
    Array.size_replicate, sep_ex_eq, sep_ex_eq_right] at h
  simp only [Nat.reduceLT, ↓reduceIte, true_implies, Full.sep_emp_eq] at h
  obtain ⟨A0, h⟩ := FAdmit.ex h
  obtain ⟨A1, h⟩ := FAdmit.ex h
  obtain ⟨A2, h⟩ := FAdmit.ex h
  obtain ⟨A3, h⟩ := FAdmit.ex h
  refine ⟨A1, A0, FAdmit.frame (R := left A2) (h.eupd ?_)⟩
  -- the address facts first; the buffer's and the vtable's parts next to each other
  refine EUpd.trans (EUpd.of_imp fun r h => ac_cast h
    (Q := ⟪A3 % 8 = 0⟫ ⋆ (⟪A2 % 8 = 0⟫ ⋆ (⟪A1 % 8 = 0⟫ ⋆ (⟪A0 % 8 = 0⟫ ⋆
      ((up (bytesAt ⟨some 1, 0⟩ A1 16 .global (Array.replicate 16 .undef)) ⋆
          (bext 1 16 .global ⋆ bclaim 1 0 16)) ⋆
        (up (bytesAt ⟨some 2, 0⟩ A2 32 .constGlobal bs2) ⋆
          (up (bytesAt ⟨some 0, 0⟩ A0 24 .global bs0) ⋆ ((up (bytesAt ⟨some 3, 0⟩ A3 32 .global bs3) ⋆
            known 3 A3) ⋆ (known 0 A0 ⋆ (known 1 A1 ⋆ (known 2 A2 ⋆ (bext 0 24 .global ⋆
              (bext 2 32 .constGlobal ⋆ (bext 3 32 .global ⋆
                (bclaim 3 0 32 ⋆ (bclaim 2 0 32 ⋆ bclaim 0 0 24)))))))))))))))) (by ac_rfl)) ?_
  refine EUpd.lift fun h3 => EUpd.lift fun h2 => EUpd.lift fun _ => EUpd.lift fun h0 => ?_
  refine EUpd.trans (EUpd.frame (buffer_parts A1 A0)) ?_
  refine EUpd.trans (EUpd.frameL (EUpd.frame (vtR_intro (vtp := vtp) (fns := fns.toList)
    (by simpa [vtp] using h2) (by rw [bs2_size]; rfl) (by decide) bs2_decode))) ?_
  refine EUpd.trans (EUpd.of_imp fun _ h => sep_assoc h) (EUpd.lift fun hb => EUpd.of_imp fun r h => ?_)
  -- the struct's words and the list header
  have h := ac_cast h (Q := (up (bytesAt ⟨some 0, 0⟩ A0 24 .global bs0) ⋆
    (up (bytesAt ⟨some 3, 0⟩ A3 32 .global bs3) ⋆ known 3 A3)) ⋆
      ((ftail (B A1 A0) 0 (Array.replicate 16 .undef) ⋆ fclaim (B A1 A0) 0 1) ⋆
        ((bshare 1 Frac.one.half (bnd (B A1 A0)) ⋆ bauth 1 16 .global Frac.one.half) ⋆
          ((up (bytesAt vtp A2 32 .constGlobal bs2) ⋆ vtR vtp fns.toList) ⋆
            (known 0 A0 ⋆ (known 1 A1 ⋆ (known 2 A2 ⋆ (bext 0 24 .global ⋆
              (bext 2 32 .constGlobal ⋆ (bext 3 32 .global ⋆
                (bclaim 3 0 32 ⋆ (bclaim 2 0 32 ⋆ bclaim 0 0 24)))))))))))) (by ac_rfl)
  -- the list's unspent fee and the client's fee: the allocator charges none (`emp`)
  have h := sep_mono_left
    (Q := (wEnd ctx 0 ⋆ wBuf ctx (B A1 A0)) ⋆ Lists.Append.alist (finv ctx (B A1 A0)) φ hdr [])
    (fun _ h => sep_mono_right (R := Lists.Append.alist (finv ctx (B A1 A0)) φ hdr [])
      (fun _ h => header_parts (finv ctx (B A1 A0)) φ A3 h3
        (sep_mono_right (fun _ h => Full.sep_emp.mpr h) h))
      (sep_mono_left (Q := wEnd ctx 0 ⋆ wBuf ctx (B A1 A0)) (fun _ h => struct_words A1 A0 h0 h) h)) h
  have h : (_ ⋆ (finv ctx (B A1 A0)).fee φ) _ := Full.sep_emp.mpr h
  -- junk: nothing yet
  have h := sep_mono_right (R := Junk) (fun _ h => junk_emp h) (Full.sep_emp.mpr h)
  have h := ac_cast h (Q := ((wEnd ctx 0 ⋆ (wBuf ctx (B A1 A0) ⋆ (known 0 A0 ⋆ (known 1 A1 ⋆
      (bshare 1 Frac.one.half (bnd (B A1 A0)) ⋆ Junk))))) ⋆
      (ftail (B A1 A0) 0 (Array.replicate 16 .undef) ⋆ fclaim (B A1 A0) 0 1)) ⋆
    (((finv ctx (B A1 A0)).fee φ ⋆ (Lists.Append.alist (finv ctx (B A1 A0)) φ hdr [] ⋆
      vtR vtp fns.toList)) ⋆ left A2)) (by
      simp only [left]; ac_rfl)
  refine ac_cast (sep_mono_left (Q := (finv ctx (B A1 A0)).own) (fun _ h => ?_) h) (by ac_rfl)
  exact ⟨0, Array.replicate 16 .undef, Frac.one.half, 1, 0, Full.sep_lift.mpr
    ⟨⟨⟨Nat.zero_le _, rfl, by simp [B, bufp]; omega, by simp [B, bufp], by simpa [B, ctx] using h0,
      by simp [ctx]⟩, rfl, rfl⟩, h⟩⟩

/-! ## The premises are met -/

/-- The real allocator meets the contract that the list theorems assume. -/
theorem fba_spec (A1 A0 : Nat) :
    CAllocSpec (CVTable.env (Lists.Alloc.env env0) fns) ctx (finv ctx (B A1 A0)) :=
  CAllocSpec.env_ofRaw env_runs (fallocSpec ctx (B A1 A0))

nonvacuity_witness Lists.Append.append_spec := by
  obtain ⟨A1, A0, h⟩ := start_admissible Frac.one
  exact ⟨ext, ctx, vtp, fns, finv ctx (B A1 A0), env0, Frac.one, hdr, [], 0,
    by simp [finv, ffits, B, Lists.Append.growTo], fba_spec A1 A0, 0, h⟩

nonvacuity_witness Lists.Alloc.push_spec := by
  obtain ⟨A1, A0, h⟩ := start_admissible Frac.one
  exact ⟨ext, ctx, vtp, fns, finv ctx (B A1 A0), env0, Frac.one, none, 0,
    by simp [finv, ffits, B], fba_spec A1 A0, 0,
    FAdmit.frame (R := Lists.Append.alist (finv ctx (B A1 A0)) Frac.one hdr [])
      (h.mono fun _ h => ac_cast h (by ac_rfl))⟩

end ListsFba
