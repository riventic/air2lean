import AllocFba.Full
import Proofs.Lists.Append
import ZigLean.Sep.Full.AllocBridge
import ZigLean.Sep.Full.WitnessStart
import ZigLean.Witness

/-!
# The list theorems' premises hold for the real `FixedBufferAllocator`

`Lists.Append.append_spec`, `Lists.Alloc.push_spec` and `Lists.Alloc.freeAll_spec` hold for every
allocator whose environment
entries meet `CAllocSpec` (`Proofs/Lists/Append.lean`, `Alloc.lean`). Here that assumption and the
precondition are met by a concrete program and memory, so the theorems are not vacuous:

* **The environment** (`ext`, `env0`): the functions at the vtable entries `fns` run the
  translated `FixedBufferAllocator` (`tests/roadmap/alloc-fba/AllocFba/Gen.lean`), every other
  pointer is `.illegal` (`env_runs`). Its contract comes from the allocator's proof, its entries
  as thread triples (`AllocFba.FBA.fthread_*`), through the library bridge `CAllocSpec.env_ofRaw`
  (`ZigLean/Sep/Full/AllocBridge.lean`): nothing here is assumed about the allocator.
* **The memory** (`gs`): the program's globals at start, under any placement: the allocator
  struct (`end_index = 0`, its 16-byte buffer), the buffer, the vtable (a `const`), an empty list
  header. `start_admissible` shows the precondition there: the start resources with the claims of every
  global (`FAdmit.Start.init_claims`: no access recorded yet, so the thread owns every heap and
  the input is a concurrent claim's, `FAdmit.Start.cadmit`) become, by updates that keep the
  memory (`FAdmit.Start.eupd`), the
  allocator's invariant at the start of a new reset ledger (`AllocFba.FBA.fown_init`: the struct's
  words, the buffer's region and claim, half of the buffer's extent lent off its authority), the
  fee and the list's unspent fee (each half of the new epoch's token: `FAllocInv.fee` is
  `epFee`), the list (`alist` of `[]`, whose items pointer is the header's own block) and the
  vtable (`vtR_intro`); the rest joins the frame (`FAdmit.Start.frame`). The buffer's region view
  and its bound close by `fsym_entail` (`buffer_parts`, `MemFacts.regionIn_bound`).
* `Lists.Append.append_spec.nonvacuous`, `Lists.Alloc.push_spec.nonvacuous`,
  `Lists.Alloc.freeAll_spec.nonvacuous` (the empty list): the companions
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
def bs0 : Array Byte :=
  Enc.encode ({ end_index := 0, buffer := ⟨bufp, 16⟩ } : AllocFba.Gen.heap_FixedBufferAllocator)
/-- The vtable. -/
def bs2 : Array Byte :=
  Enc.encode fns.alloc ++ Enc.encode fns.resize ++ Enc.encode fns.remap ++ Enc.encode fns.free
/-- The header of an empty list whose items pointer is the header's own block. -/
def bs3 : Array Byte := Enc.encode (Lists.Append.hdrVal hdr 0 0)

theorem bs0_size : bs0.size = 24 := by decide +kernel
theorem bs2_size : bs2.size = 32 := by decide +kernel
theorem bs3_size : bs3.size = 32 := by decide +kernel

theorem bs3_decode : Enc.decode bs3 = pure (Lists.Append.hdrVal hdr 0 0) := result_eq _ (by decide +kernel)
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

/-- The free buffer as the allocator's start takes it (`fown_init`): its region and its untagged
claim. -/
def bufStart (A1 A0 : Nat) : FAssn :=
  up (regionIn (B A1 A0).ptr (B A1 A0).A (B A1 A0).S (B A1 A0).K 1 (Array.replicate 16 .undef)) ⋆
    bclaim 1 (B A1 A0).ptr.off.toNat (bnd (B A1 A0)) none

attribute [local fsym_facts] MemFacts.bytesAt_bound MemFacts.regionIn_bound in
/-- Global 1 is the free buffer: its region and claim, half of its extent lent off its authority,
and the bound of its block (`MemFacts.bytesAt_bound`). -/
theorem buffer_parts (A1 A0 : Nat) :
    EUpd (up (bytesAt ⟨some 1, 0⟩ A1 16 .global (Array.replicate 16 .undef)) ⋆
        (bext 1 16 .global ⋆ bclaim 1 0 16))
      (⟪A1 + 0 + 16 ≤ 2 ^ 63⟫ ⋆ (bufStart A1 A0 ⋆
        (bshare 1 Frac.one.half (bnd (B A1 A0)) ⋆ bauth 1 16 .global Frac.one.half))) := by
  unfold bufStart
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

/-- The allocator at the start of the epoch `0` of the ledger `γ`. -/
abbrev I0 (A1 A0 γ : Nat) : FAllocInv := finv ctx (B A1 A0) γ 0

/-- What the start resources become: the allocator's invariant, the client's fee, an empty list
(with its own fee) and the vtable. -/
def startPre (A1 A0 γ : Nat) : FAssn :=
  (I0 A1 A0 γ).own ⋆ ((I0 A1 A0 γ).fee Frac.one.half ⋆
    (Lists.Append.alist (I0 A1 A0 γ) Frac.one.half hdr [] ⋆ vtR vtp fns.toList))

/-- **The precondition of `append` (and of `push`) over the real `FixedBufferAllocator` holds in
the memory at program start**: the allocator's invariant over the struct and its buffer at the
start of a new ledger (`fown_init`), the fee and the list's fee (each half of the epoch's token),
an empty list, the vtable. -/
theorem start_admissible : ∃ A1 A0 γ, FAdmit.Start (startPre A1 A0 γ ⋆ plain) := by
  have h := (FAdmit.Start.init_claims Placement.fresh gs fit lo).mono fun _ h =>
    ac_cast h (Q := (globals gs ⋆ gclaims gs) ⋆ plain) (by ac_rfl)
  simp only [globals, gclaims, gs, List.length_cons, List.length_nil, sepN, gblock, gext,
    List.getElem?_cons_succ, List.getElem?_cons_zero, Nat.reduceAdd, bs0_size, bs2_size, bs3_size,
    Array.size_replicate, sep_ex_eq, sep_ex_eq_right] at h
  simp only [Nat.reduceLT, ↓reduceIte, true_implies, Full.sep_emp_eq] at h
  obtain ⟨A0, h⟩ := FAdmit.Start.ex h
  obtain ⟨A1, h⟩ := FAdmit.Start.ex h
  obtain ⟨A2, h⟩ := FAdmit.Start.ex h
  obtain ⟨A3, h⟩ := FAdmit.Start.ex h
  -- the ledger is new: its name `γ` comes out of the update
  suffices hs : FAdmit.Start ((FAssn.ex fun γ => startPre A1 A0 γ ⋆ left A2) ⋆ plain) by
    rw [sep_ex_eq] at hs
    obtain ⟨γ, hs⟩ := FAdmit.Start.ex hs
    exact ⟨A1, A0, γ, FAdmit.Start.frame (R := left A2) (hs.mono fun _ h => ac_cast h (by ac_rfl))⟩
  refine h.eupd (EUpd.frame ?_)
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
  refine EUpd.trans (EUpd.of_imp fun _ h => sep_assoc h) (EUpd.lift fun hb => ?_)
  -- the struct's words (its bytes are its encoding: its fields' `pts`); the allocator's parts
  -- next to each other
  refine EUpd.trans (EUpd.of_imp fun r h => ac_cast h (Q := up (bytesAt ⟨some 0, 0⟩ A0 24 .global bs0) ⋆
      (bufStart A1 A0 ⋆ ((known 0 A0 ⋆ (known 1 A1 ⋆ bshare 1 Frac.one.half (bnd (B A1 A0)))) ⋆
        ((up (bytesAt ⟨some 3, 0⟩ A3 32 .global bs3) ⋆ known 3 A3) ⋆
          (vtR vtp fns.toList ⋆ (bauth 1 16 .global Frac.one.half ⋆
            (up (bytesAt vtp A2 32 .constGlobal bs2) ⋆ (known 2 A2 ⋆ (bext 0 24 .global ⋆
              (bext 2 32 .constGlobal ⋆ (bext 3 32 .global ⋆
                (bclaim 3 0 32 ⋆ (bclaim 2 0 32 ⋆ bclaim 0 0 24))))))))))))) (by ac_rfl)) ?_
  refine EUpd.trans (EUpd.frame (P' := wEnd ctx 0 ⋆ wBuf ctx (B A1 A0))
    (by unfold wEnd wBuf bs0; fsym_entail)) ?_
  refine EUpd.trans (EUpd.of_imp (P' := (wEnd ctx 0 ⋆ (fparts ctx (B A1 A0) Frac.one.half 1 0 ⋆
      bufStart A1 A0)) ⋆ ((up (bytesAt ⟨some 3, 0⟩ A3 32 .global bs3) ⋆ known 3 A3) ⋆
        (vtR vtp fns.toList ⋆ left A2))) fun r h => ac_cast h (by simp only [fparts, left, B]; ac_rfl)) ?_
  -- a new ledger whose epoch `0` holds the buffer's claim (`fown_init`)
  refine EUpd.trans (EUpd.frame (fown_init (by simp [B]) (by simp [B, bufp]; omega)
    (by simp [B, bufp]) (by simpa [B, ctx] using h0) (by simp [ctx]) rfl rfl)) ?_
  refine EUpd.ex fun γ => EUpd.of_imp fun r h => ⟨γ, ?_⟩
  -- the epoch's token: half is the client's fee, half the list's unspent fee
  rw [← Frac.half_add_half Frac.one, epTok_add] at h
  have fee : ∀ r, epTok γ 0 Frac.one.half r → (I0 A1 A0 γ).fee Frac.one.half r :=
    fun _ x => sep_comm (sep_lift.mpr ⟨Frac.half_pos (show (0 : Rat) < 1 by decide), x⟩)
  have h := ac_cast h (Q := (up (bytesAt ⟨some 3, 0⟩ A3 32 .global bs3) ⋆
      (known 3 A3 ⋆ epTok γ 0 Frac.one.half)) ⋆
    (fown ctx (B A1 A0) γ 0 ⋆ (epTok γ 0 Frac.one.half ⋆ (vtR vtp fns.toList ⋆ left A2)))) (by ac_rfl)
  have h : (Lists.Append.alist (I0 A1 A0 γ) Frac.one.half hdr [] ⋆ ((I0 A1 A0 γ).own ⋆
      ((I0 A1 A0 γ).fee Frac.one.half ⋆ (vtR vtp fns.toList ⋆ left A2)))) r :=
    sep_mono_right (fun _ x => sep_mono_right (fun _ y => sep_mono_left fee y) x)
      (sep_mono_left (fun _ x => header_parts (I0 A1 A0 γ) Frac.one.half A3 h3
        (sep_mono_right (fun _ y => sep_mono_right fee y) x)) h)
  exact ac_cast h (by simp only [startPre]; ac_rfl)

/-! ## The premises are met -/

/-- The real allocator meets the contract that the list theorems assume. -/
theorem fba_spec (A1 A0 γ : Nat) :
    CAllocSpec (CVTable.env (Lists.Alloc.env env0) fns) ctx (I0 A1 A0 γ) :=
  CAllocSpec.env_ofRaw env_runs (CAllocSpec.ofRaw
    (fun len k ra φ h1 h2 h3 => (fthread_alloc ctx (B A1 A0) γ 0 len k ra φ h1 h2 h3).toPartial)
    (fun s k n ra A S K q q' φ tl h1 h2 h3 h4 h5 _ =>
      (fthread_resize ctx (B A1 A0) γ 0 s k n ra A S K q q' φ tl h1 h2 h3 h4 h5).toPartial)
    (fun s k n ra φ bs h1 h2 h3 h4 h5 =>
      (fthread_remap ctx (B A1 A0) γ 0 s k n ra φ bs h1 h2 h3 h4 h5).toPartial)
    (fun s k ra φ bs _ h2 h3 => (fthread_free ctx (B A1 A0) γ 0 s k ra φ bs h2 h3).toPartial.post
      fun _ _ h => Full.sep_emp.mpr h))

nonvacuity_witness Lists.Append.append_spec := by
  obtain ⟨A1, A0, γ, h⟩ := start_admissible
  exact ⟨ext, ctx, vtp, fns, I0 A1 A0 γ, env0, Frac.one.half, hdr, [], 0,
    by simp [finv, ffits, B, Lists.Append.growTo], fba_spec A1 A0 γ,
    (FAdmit.Start.frame (R := plain) h).cadmit⟩

nonvacuity_witness Lists.Alloc.push_spec := by
  obtain ⟨A1, A0, γ, h⟩ := start_admissible
  exact ⟨ext, ctx, vtp, fns, I0 A1 A0 γ, env0, Frac.one.half, none, 0,
    by simp [finv, ffits, B], fba_spec A1 A0 γ,
    (FAdmit.Start.frame (R := Lists.Append.alist (I0 A1 A0 γ) Frac.one.half hdr [])
      (h.mono fun _ h => ac_cast h (by simp only [startPre]; ac_rfl))).cadmit⟩

-- `freeAll` of the empty list (`list I φ none []` is `⟪none = none⟫`): the allocator's
-- invariant and the vtable; the fee, the header and `plain` join the frame.
nonvacuity_witness Lists.Alloc.freeAll_spec := by
  obtain ⟨A1, A0, γ, h⟩ := start_admissible
  exact ⟨ext, ctx, vtp, fns, I0 A1 A0 γ, env0, Frac.one.half, none, [], fba_spec A1 A0 γ,
    (FAdmit.Start.frame (R := ((I0 A1 A0 γ).fee Frac.one.half ⋆
        Lists.Append.alist (I0 A1 A0 γ) Frac.one.half hdr []) ⋆ plain)
      (h.mono fun _ h => sep_mono_left (fun _ h => sep_mono_right (fun _ h =>
        Full.sep_lift.mpr ⟨rfl, h⟩) h)
        (ac_cast h (Q := ((I0 A1 A0 γ).own ⋆ vtR vtp fns.toList) ⋆ (((I0 A1 A0 γ).fee Frac.one.half ⋆
          Lists.Append.alist (I0 A1 A0 γ) Frac.one.half hdr []) ⋆ plain))
          (by simp only [startPre]; ac_rfl)))).cadmit⟩

end ListsFba
