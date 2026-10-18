import PageThread
import Proofs.Lists.Alloc
import ZigLean.Sep.Full.WitnessStart

/-!
# Refuted clients of the memory-safety tutorial, over the translated `PageAllocator`

`tutorials/memory-safety/Main.lean` proves, for every allocator that meets the
`std.mem.Allocator` contract (`CAllocSpec`), that its client of the generated list functions
(`Proofs/Lists/Open.lean`) never throws `.illegal` (`buildThenFree_no_illegal`) and leaks nothing
(`buildThenFree_no_leak`). `NoIllegal` and `NoLeak` below are those two statements for a client
of one item. This file shows that they are not vacuous: three wrong clients violate them.

* `doubleFree`: `push` a node, `freeAll` it, then `destroy` it again: `.illegal`;
* `useAfterFree`: `push` a node, `freeAll` it, then `sum` the list (it reads the node): `.illegal`;
* `forgetFree`: `push` a node and never free it: the run returns with the node's page live, and
  no resource that holds the memory after it with the same frame is the precondition (the
  allocator's state, the fee and the vtable): the node is leaked.

A violation is one concrete run inside the theorems' premises:

* **the allocator** is the translated `std.heap.PageAllocator` (`AllocTranslated/PageLinux.lean`,
  Zig 0.16.0, x86_64-linux) as the environment of the open allocator parameter (`ext`: the vtable
  entries are the page allocator's functions); it meets the contract (`page_spec`, from
  `PageThread.cAllocSpec`: nothing about it is assumed), and its `free` unmaps the grant, so the
  freed node's block is dead;
* **the memory** is the program's memory at start (`mem0 σ`, the page allocator's globals) with the
  precondition held (`start`): the allocator's state (its hint word, `PageAlloc.own`), the item's
  fee and the vtable (`vtR`), in the plain mode;
* **the run** (`Sched.soloRun`, the reading of `Main.lean`'s theorems) is computed by the kernel
  (`decide +kernel`). A loop (`freeAll`, `sum`) is a `partial_fixpoint`, which the kernel does
  not compute: its defining equation (`Zig.loop.eq_1`) unfolds it once per iteration the run
  takes (two for a list of one node), and the kernel never reaches the loop left in the branch
  that would repeat again.

The bugs stay bugs under address reuse (`*Reuse_unsafe`): under a placement that maps a second
`push`'s page at the freed page's address, the stale pointer still names the freed block, so the
second free and the read are `.illegal` although a live block now has that address
(`reuse_happens`). `pushThenFree`, the right client, has both properties and returns in the same
memory (`pushThenFree_returns`). `controls` collects the results.

The runs need the kernel to evaluate writes into a 4 KiB mapping: `writeBytes` is stated on lists
for that (`ZigLean/Mem/Basic.lean`, engine ledger #77).
-/

namespace AllocTranslated.ListsPage

open Zig Zig.Full Zig.Full.FAssn Zig.Witness Lists.Open Lists.Alloc

/-! ## The properties of `Main.lean`, for a client of one item -/

/-- The precondition of `Main.lean`'s theorems for one item: the allocator's state, one fee and
the vtable, in the plain mode. -/
abbrev pre (I : FAllocInv) (φ : Frac) (vtp : Ptr) (fns : VTableFns) : FAssn :=
  I.own ⋆ (fees I φ 1 ⋆ vtR vtp fns.toList) ⋆ plain

/-- **No use after free, no double free** (`buildThenFree_no_illegal`): for every environment,
every allocator that meets the contract, every memory that holds the precondition with any frame,
and every depth, the run of `c` never throws `.illegal`. -/
def NoIllegal {α : Type} (c : ∀ [Ext], mem_Allocator → ConcM Tgt α) : Prop :=
  ∀ (_ : Ext) (ctx vtp : Ptr) (fns : VTableFns) (I : FAllocInv) (e : AllocEnv Tgt) (φ : Frac),
    I.fits (16 : BitVec 64).toNat 3 → CAllocSpec (CVTable.env (env e) fns) ctx I →
    ∀ (n : Nat) (m : Mem) (r rF : Res), Holds m r rF → pre I φ vtp fns r → m.FSeq →
      ((Sched.soloRun n (c ⟨ctx, vtp⟩)).run m).run ≠ some (.error .illegal)

/-- **No leak** (`buildThenFree_no_leak`): a run that returns ends holding the precondition again,
with the same frame. -/
def NoLeak {α : Type} (c : ∀ [Ext], mem_Allocator → ConcM Tgt α) : Prop :=
  ∀ (_ : Ext) (ctx vtp : Ptr) (fns : VTableFns) (I : FAllocInv) (e : AllocEnv Tgt) (φ : Frac),
    I.fits (16 : BitVec 64).toNat 3 → CAllocSpec (CVTable.env (env e) fns) ctx I →
    ∀ (n : Nat) (m : Mem) (r rF : Res), Holds m r rF → pre I φ vtp fns r → m.FSeq →
      ∀ (v : α) (m' : Mem), ((Sched.soloRun n (c ⟨ctx, vtp⟩)).run m).run = some (.ok (v, m')) →
        ∃ r', Holds m' r' rF ∧ pre I φ vtp fns r'

/-! ## The clients -/

section Clients
variable [Ext]

/-- `const n = try push(a, null, 7); freeAll(a, n); a.destroy(n);` -/
def doubleFree (a : mem_Allocator) : ConcM Tgt Unit := do
  match ← push a none 7 with
  | .error _ => pure ()
  | .ok p => do freeAll a (some p); mem_Allocator_destroy__anon_a9add1f02861 a p

/-- `const n = try push(a, null, 7); freeAll(a, n); _ = sum(n);` -/
def useAfterFree (a : mem_Allocator) : ConcM Tgt Unit := do
  match ← push a none 7 with
  | .error _ => pure ()
  | .ok p => do freeAll a (some p); let _ ← ConcM.liftMem (sum (some p))

/-- `_ = try push(a, null, 7);`: `pushThenFree` without the free. -/
def forgetFree (a : mem_Allocator) : ConcM Tgt Unit := do
  match ← push a none 7 with
  | .error _ => pure ()
  | .ok _ => pure ()

/-- The right client: `const n = try push(a, null, 7); freeAll(a, n);` (`Main.lean`'s
`buildThenFree` of one item). -/
def pushThenFree (a : mem_Allocator) : ConcM Tgt Unit := do
  match ← push a none 7 with
  | .error _ => pure ()
  | .ok p => freeAll a (some p)

/-- `doubleFree` with a second `push` before the second free: its node may reuse the address. -/
def doubleFreeReuse (a : mem_Allocator) : ConcM Tgt Unit := do
  match ← push a none 7 with
  | .error _ => pure ()
  | .ok p => do
    freeAll a (some p)
    match ← push a none 8 with
    | .error _ => pure ()
    | .ok _ => mem_Allocator_destroy__anon_a9add1f02861 a p

/-- `useAfterFree` with a second `push` before the read. -/
def useAfterFreeReuse (a : mem_Allocator) : ConcM Tgt Unit := do
  match ← push a none 7 with
  | .error _ => pure ()
  | .ok p => do
    freeAll a (some p)
    match ← push a none 8 with
    | .error _ => pure ()
    | .ok _ => do let _ ← ConcM.liftMem (sum (some p))

/-- The nodes of `doubleFreeReuse` before the second free. -/
def pushFreePush (a : mem_Allocator) : ConcM Tgt (Option (Ptr × Ptr)) := do
  match ← push a none 7 with
  | .error _ => pure none
  | .ok p => do
    freeAll a (some p)
    match ← push a none 8 with
    | .error _ => pure none
    | .ok q => pure (some (p, q))

end Clients

/-! ## The right client has both properties -/

/-- `pushThenFree` ends with what it started with. -/
theorem pushThenFree_spec [Ext] (ctx vtp : Ptr) (fns : VTableFns) (I : FAllocInv) (e : AllocEnv Tgt)
    (φ : Frac) (hfit : I.fits (16 : BitVec 64).toNat 3) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (pre I φ vtp fns) (pushThenFree ⟨ctx, vtp⟩) (fun _ => pre I φ vtp fns) := by
  have hpre : pre I φ vtp fns = (I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList) ⋆ plain) := by
    simp only [pre, fees, sepN, Full.sep_emp_eq]
  rw [hpre]
  refine CTriple.bind (push_spec ctx vtp fns I e φ none 7 hfit h) fun r => ?_
  cases r with
  | error e' =>
    exact CTriple.ret' _ fun _ hr => by
      simp only [pushed] at hr
      exact (Full.sep_lift.mp (ac_cast hr (Q := ⟪e' = "OutOfMemory"⟫ ⋆
        (I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList) ⋆ plain)) (by ac_rfl))).2
  | ok p =>
    -- the new node is the list of `[7]`
    have hl : ∀ r, node I φ p 7 none r → list I φ (some p) [7] r := fun _ h =>
      ⟨p, none, Full.sep_lift.mpr ⟨rfl, Full.sep_comm (Full.sep_lift.mpr ⟨rfl, h⟩)⟩⟩
    refine (((freeAll_spec ctx vtp fns I e φ (some p) [7] h).frame (R := plain)).pre fun _ hr => ?_).post
      fun _ _ hr => ac_cast hr (by simp only [List.length_singleton, fees, sepN, Full.sep_emp_eq]; ac_rfl)
    have hr' : (I.own ⋆ ((list I φ (some p) [7] ⋆ vtR vtp fns.toList) ⋆ plain)) _ :=
      sep_mono_right (fun _ h => sep_mono_left (fun _ h => sep_mono_left hl h) h) hr
    exact ac_cast hr' (by ac_rfl)

theorem pushThenFree_noIllegal : NoIllegal @pushThenFree := by
  intro _ ctx vtp fns I e φ hfit h n m r rF hh hr hs he
  have t := (pushThenFree_spec ctx vtp fns I e φ hfit h).toSolo n m r rF hh hr hs
  rw [he] at t
  cases t

theorem pushThenFree_noLeak : NoLeak @pushThenFree := by
  intro _ ctx vtp fns I e φ hfit h n m r rF hh hr hs v m' hrun
  have t := (pushThenFree_spec ctx vtp fns I e φ hfit h).toSolo n m r rF hh hr hs
  rw [hrun] at t
  obtain ⟨r', hh', hq, -⟩ := t
  exact ⟨r', hh', hq⟩

/-! ## The allocator: the translated `PageAllocator` -/

/-- The vtable's entries: the page allocator's functions (globals 2 to 5 of `PageLinux.mem0`). -/
def fns : VTableFns := ⟨⟨some 2, 0⟩, ⟨some 3, 0⟩, ⟨some 4, 0⟩, ⟨some 5, 0⟩⟩

/-- `std.heap.page_allocator`: no context, and the page allocator's vtable (global 1). -/
def ctx : Ptr := ⟨none, 0⟩
def vtp : Ptr := ⟨some 1, 0⟩

/-- The environment of the lists program: the page allocator's entries at `fns`, nothing
elsewhere. -/
instance ext : Ext where
  call0 f c n a ra := if f = fns.alloc then ConcM.liftMem (Sched.soloRun 16
    (PageLinux.heap_PageAllocator_alloc c n ⟨a.bits⟩ ra)) else throw .illegal
  call1 f c s a n ra := if f = fns.remap then
    ConcM.liftMem (PageLinux.heap_PageAllocator_remap c s ⟨a.bits⟩ n ra) else throw .illegal
  call2 f c s a ra := if f = fns.free then
    ConcM.liftMem (PageLinux.heap_PageAllocator_free c s ⟨a.bits⟩ ra) else throw .illegal

/-- The environment's `resize` (the program never calls it). -/
def env0 : AllocEnv Tgt :=
  { AllocEnv.closed with
    resize := fun f a => if f = fns.resize then
      ConcM.liftMem (PageAlloc.vt.resize a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2) else throw .illegal }

/-- The environment's allocator at `fns` runs the translated `PageAllocator`. -/
theorem env_runs : CVTable.env (env env0) fns = CVTable.ofRaw PageAlloc.vt := by
  simp only [CVTable.env, CVTable.ofRaw, env, env0, al, extCall, CVTable.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext <;> first | rfl | simp [ext, PageAlloc.vt, PageSpec.vt]

/-- **The translated `PageAllocator` meets the contract** that `Main.lean`'s theorems assume. -/
theorem page_spec : CAllocSpec (CVTable.env (env env0) fns) ctx PageAlloc.ainv :=
  CAllocSpec.env_ofRaw env_runs (PageThread.cAllocSpec ctx)

theorem page_fits : PageAlloc.ainv.fits (16 : BitVec 64).toNat 3 := by
  simp only [PageAlloc.ainv, PageSpec.P]; decide

/-! ## The memory at program start holds the precondition -/

/-- The page allocator's hint word (`addr_hint = null`). -/
def bs0 : Array Byte := Enc.encode (none : Option Ptr)
/-- The page allocator's vtable. -/
def bs1 : Array Byte :=
  Enc.encode (⟨fns.alloc, fns.resize, fns.remap, fns.free⟩ : PageLinux.mem_Allocator_VTable)

/-- The program's globals (`PageLinux.mem0`). -/
def gs : List (Array Byte × Nat × BlockKind) :=
  [(bs0, 8, .global), (bs1, 8, .constGlobal), (#[.undef], 1, .constGlobal),
    (#[.undef], 1, .constGlobal), (#[.undef], 1, .constGlobal), (#[.undef], 1, .constGlobal)]

/-- The memory at program start under the placement `σ`. -/
abbrev mem0 (σ : Placement) : Mem := PageLinux.mem0 σ

theorem mem0_eq (σ : Placement) : mem0 σ = Mem.ofGlobals σ gs := by
  unfold mem0 PageLinux.mem0; rfl

theorem bs0_size : bs0.size = 8 := by decide +kernel
theorem bs1_size : bs1.size = 32 := by decide +kernel

theorem bs0_decode : Enc.decode bs0 = pure (none : Option Ptr) := result_eq _ (by decide +kernel)

theorem bs1_decode : ∀ i (hi : i < fns.toList.length),
    Enc.decode (bs1.extract (8 * i) (8 * i + 8)) = pure fns.toList[i] := by
  intro i hi
  simp only [VTableFns.toList, List.length_cons, List.length_nil] at hi
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ =>
    -- `fns.toList[i]` carries the bound proof; simp drops it so `decide` sees a closed goal.
    simp only [VTableFns.toList, List.getElem_cons_succ, List.getElem_cons_zero]
    exact result_eq _ (by decide +kernel)

theorem fit : Mem.GlobalsFit gs := by
  unfold Mem.GlobalsFit; simp [gs, bs0_size, bs1_size]

theorem lo : ∀ g ∈ gs, g.2.2.mappedLo = 0 := by simp [gs, BlockKind.mappedLo]

/-- The globals' resources besides the precondition (they join the frame). -/
def rest (A0 A1 : Nat) : FAssn :=
  (known 1 A1 ⋆ bext 1 32 .constGlobal) ⋆ ((known 0 A0 ⋆ bext 0 8 .global) ⋆ emp)

/-- The precondition from the hint word (`null`: no knowledge), the vtable and the plain mode;
the page allocator's fee is `emp`. -/
theorem pre_intro {r : Res} (h : (aptsE PageAlloc.hint (none : Option Ptr) ⋆ (vtR vtp fns.toList ⋆ plain)) r) :
    pre PageAlloc.ainv Frac.one vtp fns r := by
  have e : pre PageAlloc.ainv Frac.one vtp fns =
      (PageAlloc.own ⋆ ((FAssn.emp ⋆ FAssn.emp) ⋆ vtR vtp fns.toList) ⋆ plain) := rfl
  rw [e, Full.sep_emp_eq, Full.emp_sep_eq]
  unfold PageAlloc.own
  exact sep_ex.mpr ⟨none, sep_mono_left (fun _ h => Full.sep_emp.mpr h) h⟩

/-- **The precondition holds at program start**, under every placement: the hint word (`null`)
as the allocator's state, the fee (the page allocator charges none) and the vtable. -/
theorem start (σ : Placement) : FAdmit.At (mem0 σ) (pre PageAlloc.ainv Frac.one vtp fns) := by
  rw [mem0_eq]
  have hs : (Mem.ofGlobals σ gs).FSeq := Mem.init_fseq σ gs fit
  have h : FAdmit.At (Mem.ofGlobals σ gs) (globals gs ⋆ plain) := by
    obtain ⟨hh, hg⟩ := initRes_holds_plain σ gs lo
    exact ⟨_, _, hh, hg⟩
  simp only [globals, gs, List.length_cons, List.length_nil, sepN, gblock, gext,
    List.getElem?_cons_succ, List.getElem?_cons_zero, Nat.reduceAdd, bs0_size, bs1_size,
    List.size_toArray, Nat.reduceLT, ↓reduceIte, true_implies, sep_ex_eq, sep_ex_eq_right] at h
  obtain ⟨A0, h⟩ := h.ex
  obtain ⟨A1, h⟩ := h.ex
  obtain ⟨_, h⟩ := h.ex
  obtain ⟨_, h⟩ := h.ex
  obtain ⟨_, h⟩ := h.ex
  obtain ⟨_, h⟩ := h.ex
  -- the function globals 2 to 5 join the frame
  have h := ((((h.mono fun _ h => Full.sep_assoc h).dropL.mono fun _ h => Full.sep_assoc h).dropL.mono
    fun _ h => Full.sep_assoc h).dropL.mono fun _ h => Full.sep_assoc h).dropL
  -- the addresses' alignment
  have h := h.mono fun _ h => ac_cast h (Q := ⟪A1 % 8 = 0⟫ ⋆ (⟪A0 % 8 = 0⟫ ⋆
    (up (bytesAt ⟨some 1, 0⟩ A1 32 .constGlobal bs1) ⋆ (up (bytesAt ⟨some 0, 0⟩ A0 8 .global bs0) ⋆
      (plain ⋆ rest A0 A1))))) (by simp only [rest]; ac_rfl)
  obtain ⟨h1, h⟩ := h.lift
  obtain ⟨h0, h⟩ := h.lift
  -- the vtable: a `const` global
  have h := h.eupd hs (EUpd.frame (vtR_intro (vtp := vtp) (fns := fns.toList)
    (by simpa [vtp] using h1) (by rw [bs1_size]; rfl) (by decide) bs1_decode))
  have h := h.mono fun _ h => ac_cast h (Q := up (bytesAt ⟨some 0, 0⟩ A0 8 .global bs0) ⋆
    (vtR vtp fns.toList ⋆ (plain ⋆ (up (bytesAt vtp A1 32 .constGlobal bs1) ⋆ rest A0 A1))))
    (by ac_rfl)
  -- the hint word: an atomic
  have h := h.aptsE (v := (none : Option Ptr)) rfl (by simpa using h0) (by decide) bs0_size bs0_decode
  exact (h.mono fun _ h => sep_mono_left (fun _ h => pre_intro (Full.sep_assoc h))
    (Full.sep_assoc' (Full.sep_assoc' h))).frame

/-! ## The runs, by the kernel -/

/-- `true` for a run that throws `.illegal`. -/
def isIllegal {α : Type} : Option (Except Error α) → Bool
  | some (.error .illegal) => true
  | _ => false

theorem eq_of_isIllegal {α : Type} {r : Option (Except Error α)} (h : isIllegal r = true) :
    r = some (.error .illegal) := by
  match r, h with
  | some (.error .illegal), _ => rfl

/-- The node's mapping (block 7, after the six globals and `push`'s stack slot). -/
abbrev nodeBlock : BlockId := 7

/-- `true` for a run that returns in a memory where the first byte of the node's mapping is
live. -/
def nodeLive {α : Type} : Option (Except Error (α × Mem)) → Bool
  | some (.ok (_, m)) => (m.heap (nodeBlock, 0)).isSome
  | _ => false

/-- The address of the node's mapping is the address of the second `push`'s (block 9): the
second mapping reuses the freed page, and only the second one is live. -/
def reused : Option (Except Error (Option (Ptr × Ptr) × Mem)) → Bool
  | some (.ok (some (p, q), m)) => match m.blocks[nodeBlock]?, m.blocks[9]? with
    | some b, some b' => p.block == some nodeBlock && q.block == some 9 && b.addr == b'.addr &&
        !b.live && b'.live
    | _, _ => false
  | _ => false

attribute [local instance] ext

theorem doubleFree_run :
    isIllegal ((Sched.soloRun 100 (doubleFree ⟨ctx, vtp⟩)).run (mem0 .fresh)).run = true := by
  unfold doubleFree freeAll
  rw [Zig.loop.eq_1, Zig.loop.eq_1]
  decide +kernel

theorem useAfterFree_run :
    isIllegal ((Sched.soloRun 100 (useAfterFree ⟨ctx, vtp⟩)).run (mem0 .fresh)).run = true := by
  unfold useAfterFree freeAll sum
  rw [Zig.loop.eq_1 (freeAll.loop5 _), Zig.loop.eq_1 (freeAll.loop5 _), Zig.loop.eq_1 sum.loop6]
  decide +kernel

theorem forgetFree_run :
    nodeLive ((Sched.soloRun 100 (forgetFree ⟨ctx, vtp⟩)).run (mem0 .fresh)).run = true := by
  decide +kernel

/-- A placement that maps the second `push`'s page (block 9) at the address of the first
(block 7). -/
def σReuse : Placement := { propose := fun b => if b == 7 || b == 9 then some (2 ^ 40) else none }

theorem reuse_happens :
    reused ((Sched.soloRun 100 (pushFreePush ⟨ctx, vtp⟩)).run (mem0 σReuse)).run = true := by
  unfold pushFreePush freeAll
  rw [Zig.loop.eq_1, Zig.loop.eq_1]
  decide +kernel

theorem doubleFreeReuse_run :
    isIllegal ((Sched.soloRun 100 (doubleFreeReuse ⟨ctx, vtp⟩)).run (mem0 σReuse)).run = true := by
  unfold doubleFreeReuse freeAll
  rw [Zig.loop.eq_1, Zig.loop.eq_1]
  decide +kernel

theorem useAfterFreeReuse_run :
    isIllegal ((Sched.soloRun 100 (useAfterFreeReuse ⟨ctx, vtp⟩)).run (mem0 σReuse)).run = true := by
  unfold useAfterFreeReuse freeAll sum
  rw [Zig.loop.eq_1 (freeAll.loop5 _), Zig.loop.eq_1 (freeAll.loop5 _), Zig.loop.eq_1 sum.loop6]
  decide +kernel

/-- `true` for a run that returns. -/
def returns {α : Type} : Option (Except Error α) → Bool
  | some (.ok _) => true
  | _ => false

/-- The right client returns from the same memory. -/
theorem pushThenFree_returns :
    returns ((Sched.soloRun 100 (pushThenFree ⟨ctx, vtp⟩)).run (mem0 .fresh)).run = true := by
  unfold pushThenFree freeAll
  rw [Zig.loop.eq_1, Zig.loop.eq_1]
  decide +kernel

/-! ## The refutations -/

theorem fseq (σ : Placement) : (mem0 σ).FSeq := mem0_eq σ ▸ Mem.init_fseq σ gs fit

/-- A run of `c` from the start memory under `σ` that throws `.illegal` refutes `NoIllegal c`:
the page allocator and that memory meet the property's premises. -/
theorem not_noIllegal {α : Type} {c : ∀ [Ext], mem_Allocator → ConcM Tgt α} (σ : Placement)
    (hrun : isIllegal ((Sched.soloRun 100 (c ⟨ctx, vtp⟩)).run (mem0 σ)).run = true) :
    ¬ NoIllegal c := fun h => by
  obtain ⟨r, rF, hh, hp⟩ := start σ
  exact h ext ctx vtp fns _ env0 Frac.one page_fits page_spec 100 _ r rF hh hp (fseq σ)
    (eq_of_isIllegal hrun)

/-- **Double free**: `Main.lean`'s memory-safety property is false for `doubleFree`. -/
theorem doubleFree_unsafe : ¬ NoIllegal @doubleFree := not_noIllegal _ doubleFree_run

/-- **Use after free**: `Main.lean`'s memory-safety property is false for `useAfterFree`. -/
theorem useAfterFree_unsafe : ¬ NoIllegal @useAfterFree := not_noIllegal _ useAfterFree_run

/-- **Under address reuse**: the second free of the stale pointer is `.illegal`, although a live
block now has its address (`reuse_happens`). -/
theorem doubleFreeReuse_unsafe : ¬ NoIllegal @doubleFreeReuse := not_noIllegal _ doubleFreeReuse_run

/-- **Under address reuse**: the read through the stale pointer is `.illegal`. -/
theorem useAfterFreeReuse_unsafe : ¬ NoIllegal @useAfterFreeReuse :=
  not_noIllegal _ useAfterFreeReuse_run

/-- A separating conjunction of two parts without the byte `l` has no byte `l`. -/
theorem sep_heap_none {P Q : FAssn} {r : Res} {l : Loc} (h : (P ⋆ Q) r)
    (hP : ∀ r, P r → r.heap l = none) (hQ : ∀ r, Q r → r.heap l = none) : r.heap l = none := by
  obtain ⟨r₁, r₂, -, rfl, h1, h2⟩ := h
  simp [FHeap.union_apply, hP _ h1, hQ _ h2]

theorem Persistent.heap_none {P : FAssn} (hP : Persistent P) {l : Loc} :
    ∀ r, P r → r.heap l = none := fun r h => by rw [(hP r h).1]; rfl

/-- **The precondition owns no byte of the node's mapping**: the hint word is global 0, and the
fee, the vtable and the plain mode own no bytes. -/
theorem pre_avoids {r : Res} (h : pre PageAlloc.ainv Frac.one vtp fns r) (o : Nat) :
    r.heap (nodeBlock, o) = none := by
  refine sep_heap_none h (fun r h => ?_) fun r h => sep_heap_none h
    (Persistent.heap_none (Persistent.sep (Persistent.sep Persistent.emp Persistent.emp) Persistent.vtR))
    fun r h => sep_heap_none h (fun r h => by rw [h.1]; rfl) fun r h => by rw [h.1]; rfl
  obtain ⟨hv, h⟩ := h
  refine sep_heap_none h (fun r h => ?_) fun r h => ?_
  · obtain ⟨A, S, K, bs, -, -, -, -, -, -, b, hb, -, hl⟩ := h
    rw [hl]
    simp only [Option.some.injEq] at hb
    subst hb
    simp
  · cases hv with
    | none => rw [h.1]; rfl
    | some _ => exact Persistent.heap_none (Persistent.ex fun _ => Persistent.ex fun _ =>
        Persistent.sep Persistent.lift Persistent.known) r h

/-- **Leak**: `Main.lean`'s no-leak property is false for `forgetFree`. The run returns with the
node's mapping live; the frame owned none of its bytes at start (the block did not exist), and the
precondition owns none (`pre_avoids`), so no resource that holds the memory after the run is the
precondition with the same frame. -/
theorem forgetFree_leaks : ¬ NoLeak @forgetFree := fun h => by
  obtain ⟨r, rF, hh, hp⟩ := start .fresh
  have hk := forgetFree_run
  unfold nodeLive at hk
  split at hk
  · rename_i v m' hrun
    obtain ⟨r', hh', hp'⟩ := h ext ctx vtp fns _ env0 Frac.one page_fits page_spec 100 _ r rF hh hp
      (fseq _) v m' hrun
    -- block 7 does not exist at start, so the frame owns none of its bytes
    have h0 : ((mem0 .fresh).heap (nodeBlock, 0)).isNone = true := by decide +kernel
    have hF : rF.heap (nodeBlock, 0) = none := by
      have := hh.heap.1 (nodeBlock, 0)
      rw [Option.isNone_iff_eq_none.mp h0] at this
      simp only [Option.map_none, FHeap.union_apply] at this
      cases e : rF.heap (nodeBlock, 0) with
      | none => rfl
      | some _ => cases e' : r.heap (nodeBlock, 0) <;> simp [e, e'] at this
    have := hh'.heap.1 (nodeBlock, 0)
    rw [FHeap.union_apply, pre_avoids hp' 0, hF] at this
    simp only [Option.none_or, Option.map_none, Option.map_eq_none_iff] at this
    rw [this] at hk
    cases hk
  · cases hk

/-- **The controls**: each wrong client violates one of `Main.lean`'s properties, also under
address reuse, while the right client has both and returns in the same memory. -/
theorem controls :
    ¬ NoIllegal @doubleFree ∧ ¬ NoIllegal @useAfterFree ∧ ¬ NoLeak @forgetFree ∧
      ¬ NoIllegal @doubleFreeReuse ∧ ¬ NoIllegal @useAfterFreeReuse ∧
      NoIllegal @pushThenFree ∧ NoLeak @pushThenFree :=
  ⟨doubleFree_unsafe, useAfterFree_unsafe, forgetFree_leaks, doubleFreeReuse_unsafe,
    useAfterFreeReuse_unsafe, pushThenFree_noIllegal, pushThenFree_noLeak⟩

end AllocTranslated.ListsPage
