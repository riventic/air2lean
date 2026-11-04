import AllocFba.Wrappers
import ZigLean.Sep.Full.AutoAll
import ZigLean.Sep.Full.Local
import ZigLean.Sep.Full.WitnessStart

/-!
# The translated FBA client in the full-state logic

`client_spec`: the generated client is walked by `fsym`, using the generated wrappers' contracts
over `FAllocSpec`, the initialized FBA invariant and its reset contract. The buffer's authority is
a positive extent share at bound 12 and an untagged claim on `[0,12)`; the other four bytes remain
the client's. Stack allocation is paid by the running thread's token and room resource.

`client_start` is the strength example: from the program's actual start memory (`Gen.mem0`) with
a stack budget, the client runs to a result that satisfies `Res`. The precondition of
`client_spec` is derived from the start resources (`FTotalTriple.run_init_stack_claims`), so the
contract is not vacuous.
-/

open Zig Zig.Full Zig.Witness Zig.Full.FAssn AllocFba AllocFba.Gen AllocFba.FBA

namespace AllocFba.Client

abbrev bufp : Ptr := ⟨some 0, 0⟩
abbrev vtp : Ptr := ⟨some 5, 0⟩

abbrev buf (A₀ Ac : Nat) : FBuf := ⟨bufp, 12, A₀, 16, .global, Ac⟩

def expected (v : BitVec 8) : BitVec 32 :=
  BitVec.ofNat 32 (v.toNat + v.toNat + (v + 1).toNat)

def Res (v : BitVec 8) (r : BitVec 32) : Prop :=
  r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = expected v

set_option maxHeartbeats 4000000 in
/-- The full-state client contract: the stack room is an owned resource, and the buffer carries
only the extent share and claim approved for the native invariant. -/
theorem client_spec (v : BitVec 8) (A₀ S D : Nat) (q : Frac) (bs : Array Byte)
    (hs : bs.size = 16) (hA : A₀ + 16 ≤ 2 ^ 64) :
    FTotalTriple
      (up (regionIn bufp A₀ 16 .global 1 bs) ⋆ (vtR vtp fns.toList ⋆
        (cur 0 ⋆ (sp 0 S D ⋆ (⟪D + stackCharge 24 8 ≤ S⟫ ⋆
          (bshare 0 q 12 ⋆ bclaim 0 0 12 none))))))
      (fba_client v)
      (fun r => ⟪Res v r⟫ ⋆ (sp 0 S D ⋆ Junk)) := by
  have hprefix : (bs.extract 0 12).size = 12 := by simp [Array.size_extract, hs]
  have init := fun (ctx : Ptr) (Ac : Nat) (cb : BlockId) =>
    @fallocator_init ctx (buf A₀ Ac) q 0 cb (bs.extract 0 12) hprefix
  have reset := freset_spec
  have halfFees (γ e : Nat) :
      epTok γ e Frac.one = (epFee γ e Frac.one.half ⋆ epFee γ e Frac.one.half) := by
    calc
      epTok γ e Frac.one = epFee γ e Frac.one := by
        funext r
        apply propext
        constructor
        · intro h
          exact sep_comm (sep_lift.mpr ⟨by decide, h⟩)
        · intro h
          exact (sep_lift.mp (sep_comm h)).2
      _ = _ := by
        simpa only [Frac.half_add_half] using
          (epFee_add γ e (a := Frac.one.half) (b := Frac.one.half) (Frac.half_pos (by decide)) (Frac.half_pos (by decide)))
  simp only [halfFees] at init reset
  fsym [init,
    fun ctx Ac γ e n => Wrappers.alloc_of (vtp := vtp) (fallocSpec ctx (buf A₀ Ac) γ e)
      Frac.one.half n,
    fun ctx Ac γ e s n bs => Wrappers.realloc_of (vtp := vtp) (fallocSpec ctx (buf A₀ Ac) γ e)
      Frac.one.half s n bs,
    fun ctx Ac γ e s bs => Wrappers.free_of (vtp := vtp) (fallocSpec ctx (buf A₀ Ac) γ e)
      Frac.one.half s bs,
    reset, fun (h : Heap) => EUpd.of_imp (@JunkAt.junk h)]

/-! ## The strength example: the client from the program's start -/

/-- The vtable's bytes (global 5). -/
def vtBytes : Array Byte :=
  Enc.encode (mem_Allocator_VTable.mk ⟨some 1, 0⟩ ⟨some 2, 0⟩ ⟨some 3, 0⟩ ⟨some 4, 0⟩)

theorem vtBytes_size : vtBytes.size = 32 := by decide +kernel

theorem vtBytes_decode : ∀ i (hi : i < fns.toList.length),
    Enc.decode (vtBytes.extract (8 * i) (8 * i + 8)) = pure fns.toList[i] := by
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

/-- The program's globals: the buffer, the four entry functions, the vtable. -/
def gs : List (Array Byte × Nat × BlockKind) :=
  [(Array.replicate 16 .undef, 1, .global), (#[.undef], 1, .constGlobal), (#[.undef], 1, .constGlobal),
    (#[.undef], 1, .constGlobal), (#[.undef], 1, .constGlobal), (vtBytes, 8, .constGlobal)]

/-- The generated start memory is the start memory of these globals. -/
theorem mem0_eq (σ : Placement) : mem0 σ = Mem.ofGlobals σ gs := rfl

theorem gs_fit : Mem.GlobalsFit gs := by
  unfold Mem.GlobalsFit; simp [gs, vtBytes_size]

theorem gs_lo : ∀ g ∈ gs, g.2.2.mappedLo = 0 := by simp [gs, BlockKind.mappedLo]

attribute [local fsym_facts] MemFacts.bytesAt_bound MemFacts.regionIn_bound in
/-- Global 0 is the buffer: its region, half of its extent lent off its authority at the
allocator's bound `12`, and the bound of its block. -/
theorem buffer_parts (A₀ : Nat) :
    EUpd (up (bytesAt bufp A₀ 16 .global (Array.replicate 16 .undef)) ⋆ bext 0 16 .global)
      (⟪A₀ + 0 + 16 ≤ 2 ^ 63⟫ ⋆ (up (regionIn bufp A₀ 16 .global 1 (Array.replicate 16 .undef)) ⋆
        (bshare 0 Frac.one.half 12 ⋆ bauth 0 16 .global Frac.one.half))) := by
  fsym_entail

/-- The four entry functions' globals (blocks 1–4), which the client does not touch. -/
def fnBlocks (a1 a2 a3 a4 : Nat) : FAssn :=
  (up (bytesAt ⟨some 4, 0⟩ a4 1 .constGlobal #[.undef]) ⋆ (known 4 a4 ⋆ bext 4 1 .constGlobal)) ⋆
    ((up (bytesAt ⟨some 3, 0⟩ a3 1 .constGlobal #[.undef]) ⋆ (known 3 a3 ⋆ bext 3 1 .constGlobal)) ⋆
      ((up (bytesAt ⟨some 2, 0⟩ a2 1 .constGlobal #[.undef]) ⋆ (known 2 a2 ⋆ bext 2 1 .constGlobal)) ⋆
        ((up (bytesAt ⟨some 1, 0⟩ a1 1 .constGlobal #[.undef]) ⋆ (known 1 a1 ⋆ bext 1 1 .constGlobal)) ⋆
          (bclaim 4 0 1 ⋆ (bclaim 3 0 1 ⋆ (bclaim 2 0 1 ⋆ bclaim 1 0 1))))))

/-- **The client from the program's start.** With a stack budget that covers its frame and a
placement that has room for the stack, the client run from `Gen.mem0` returns a result that
satisfies `Res`. -/
theorem client_start (σ : Placement) (S : Nat) (hS : stackCharge 24 8 ≤ S)
    (hr : ((mem0 σ).reserveAt? 0 S).isSome) (v : BitVec 8) :
    ∃ x m', (fba_client v).run ((mem0 σ).withStack S) = pure (x, m') ∧ Res v x := by
  rw [mem0_eq] at hr ⊢
  suffices ht : FTotalTriple ((globals gs ⋆ stackStart S) ⋆ gclaims gs) (fba_client v)
      (fun x => FAssn.ex fun R : FAssn => ⟪Res v x⟫ ⋆ R) by
    obtain ⟨x, m', r', hrun, -, ⟨R, hq⟩, -⟩ :=
      FTotalTriple.run_init_stack_claims σ gs gs_fit gs_lo S hr ht
    exact ⟨x, m', hrun, (sep_lift.mp hq).1⟩
  simp only [globals, gclaims, stackStart, gs, List.length_cons, List.length_nil, sepN, gblock, gext,
    List.getElem?_cons_succ, List.getElem?_cons_zero, Nat.reduceAdd, vtBytes_size,
    Array.size_replicate, List.size_toArray, sep_ex_eq, sep_ex_eq_right]
  simp only [Nat.reduceLT, ↓reduceIte, true_implies, Full.sep_emp_eq, Nat.zero_lt_one]
  refine FTotalTriple.ex fun a0 => FTotalTriple.ex fun a1 => FTotalTriple.ex fun a2 =>
    FTotalTriple.ex fun a3 => FTotalTriple.ex fun a4 => FTotalTriple.ex fun a5 => ?_
  -- the address facts first; the buffer's and the vtable's parts next to each other
  refine FTotalTriple.pre (P := ⟪a5 % 8 = 0⟫ ⋆ (⟪a4 % 1 = 0⟫ ⋆ (⟪a3 % 1 = 0⟫ ⋆ (⟪a2 % 1 = 0⟫ ⋆
      (⟪a1 % 1 = 0⟫ ⋆ (⟪a0 % 1 = 0⟫ ⋆
      ((up (bytesAt bufp a0 16 .global (Array.replicate 16 .undef)) ⋆ bext 0 16 .global) ⋆
        (up (bytesAt vtp a5 32 .constGlobal vtBytes) ⋆
          (bclaim 0 0 16 ⋆ (cur 0 ⋆ (sp 0 S 0 ⋆ (known 0 a0 ⋆ (known 5 a5 ⋆
            (bext 5 32 .constGlobal ⋆ (bclaim 5 0 32 ⋆ (unmetered ⋆ fnBlocks a1 a2 a3 a4))))))))))))))))
    ?_ fun _ h => ac_cast h (by simp only [fnBlocks, bufp, vtp]; ac_rfl)
  refine FTotalTriple.lift fun h5 => FTotalTriple.lift fun _ => FTotalTriple.lift fun _ =>
    FTotalTriple.lift fun _ => FTotalTriple.lift fun _ => FTotalTriple.lift fun _ => ?_
  refine FTotalTriple.eupd (EUpd.frame (buffer_parts a0)) ?_
  refine FTotalTriple.eupd (EUpd.frameL (EUpd.frame (vtR_intro (vtp := vtp) (fns := fns.toList)
    (by simpa [vtp] using h5) (by rw [vtBytes_size]; rfl) (by decide) vtBytes_decode))) ?_
  refine FTotalTriple.eupd (EUpd.of_imp fun _ h => sep_assoc h) ?_
  refine FTotalTriple.lift fun hA => ?_
  -- the client's contract with an empty stack, framed; its claim is the allocator's part
  -- `[0,12)` of the buffer's claim
  exact FTotalTriple.pre
    (((client_spec v a0 S 0 Frac.one.half (Array.replicate 16 .undef) (by simp) (by omega)).frame
      (R := bauth 0 16 .global Frac.one.half ⋆ (bclaim 0 12 16 ⋆
        (up (bytesAt vtp a5 32 .constGlobal vtBytes) ⋆ (known 0 a0 ⋆ (known 5 a5 ⋆
          (bext 5 32 .constGlobal ⋆ (bclaim 5 0 32 ⋆ (unmetered ⋆ fnBlocks a1 a2 a3 a4))))))))).post
      fun _ _ h => ⟨_, sep_assoc h⟩)
    fun _ h => by
      rw [← bclaim_split (lo := 0) (m := 12) (hi := 16) (by omega) (by omega)] at h
      have h := sep_lift.mpr ⟨(by omega : 0 + stackCharge 24 8 ≤ S), h⟩
      exact ac_cast h (by ac_rfl)

end AllocFba.Client
