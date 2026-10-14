import ZigLean.Sep.Full.Dispatch

/-!
# Persistent knowledge of `const` globals: regressions (`docs/sep-full-state.md` §Const globals)

1. `two_handles`: two allocators whose invariants **each** hold the same vtable (`vtR`, as an
   arena holds its child's), called one after the other through it, the way generated code calls
   `a.rawAlloc`: load the entry, dispatch. `two_handles_one_vtable`: a client with one vtable
   gives a copy to both (`vtR_dup`).
2. `vtOwn_twice`: the exclusive form cannot be held twice: two owners of the same vtable bytes
   (`up (vtOwn …)`) are never a resource. That is why `vtR` is knowledge.
3. Counterexamples of the model fact that makes the knowledge persistent: a store to a `const`
   global (`store_const_illegal`) and a `free` of one (`free_const_illegal`) throw `.illegal`.

Kernel-checked; the expected axioms are `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Zig.Full.ConstKnow

open Zig Zig.Full Zig.Full.FAssn

variable {Tgt : Type}

/-- `a.rawAlloc(n, k, ra)` through the `Allocator` value `{ .ptr = ctx, .vtable = vtp }`: load
the `alloc` entry, call it through the program's table. -/
def allocVia (t : AllocTables Tgt) (ctx vtp : Ptr) (n : BitVec 64) (k : Nat) (ra : BitVec 64) :
    ConcM Tgt (Option Ptr) :=
  ConcM.liftMem (load Ptr 8 vtp) >>= fun f => t.alloc.call f (ctx, n, k, ra)

/-- One call through a handle whose invariant holds the vtable: it reads the vtable and keeps it. -/
theorem allocVia_spec {t : AllocTables Tgt} {fns : VTableFns} {impl : CVTable Tgt} {ctx vtp : Ptr}
    {I : FAllocInv} (hs : Selects t fns impl) (h : CAllocSpec impl ctx I) (n : BitVec 64) (k : Nat)
    (ra : BitVec 64) (φ : Frac) (h1 : 0 < n.toNat) (h2 : k < 64) (h3 : I.fits n.toNat k) :
    CTriple ((I.own ⋆ I.fee φ) ⋆ vtR vtp fns.toList) (allocVia t ctx vtp n k ra)
      (fun p => I.allocPost n.toNat k φ p ⋆ vtR vtp fns.toList) := by
  have hl : FTTriple (vtR vtp fns.toList) (load Ptr 8 vtp)
      (fun f => ⟪f = fns.alloc⟫ ⋆ vtR vtp fns.toList) := by
    simpa [VTableFns.toList] using
      (vtR_load (vtp := vtp) (fns := fns.toList) (i := 0) (by simp [VTableFns.toList])).toPartial
  refine CTriple.bind (CTriple.liftMem hl.frameL) fun f => ?_
  refine CTriple.pre (CTriple.lift fun hf => ?_) fun _ hp => by rwa [sep_left_comm_eq] at hp
  subst hf
  show CTriple _ (t.alloc.call fns.alloc (ctx, n, k, ra)) _
  rw [Table.call_of_sel hs.alloc]
  exact (h.alloc n k ra φ h1 h2 h3).frame

/-- **Two handles, one vtable, each invariant holding it.** -/
theorem two_handles {t : AllocTables Tgt} {fns : VTableFns} {impl : CVTable Tgt} {c₁ c₂ vtp : Ptr}
    {I₁ I₂ : FAllocInv} (hs : Selects t fns impl) (h₁ : CAllocSpec impl c₁ I₁)
    (h₂ : CAllocSpec impl c₂ I₂) (n : BitVec 64) (k : Nat) (ra : BitVec 64) (φ₁ φ₂ : Frac)
    (hn : 0 < n.toNat) (hk : k < 64) (f₁ : I₁.fits n.toNat k) (f₂ : I₂.fits n.toNat k) :
    CTriple (((I₁.own ⋆ I₁.fee φ₁) ⋆ vtR vtp fns.toList) ⋆ ((I₂.own ⋆ I₂.fee φ₂) ⋆ vtR vtp fns.toList))
      (allocVia t c₁ vtp n k ra >>= fun a => allocVia t c₂ vtp n k ra >>= fun b => pure (a, b))
      (fun ab => (I₁.allocPost n.toNat k φ₁ ab.1 ⋆ vtR vtp fns.toList) ⋆
        (I₂.allocPost n.toNat k φ₂ ab.2 ⋆ vtR vtp fns.toList)) :=
  CTriple.bind (allocVia_spec hs h₁ n k ra φ₁ hn hk f₁).frame fun a =>
    CTriple.bind (allocVia_spec hs h₂ n k ra φ₂ hn hk f₂).frameL fun b =>
      CTriple.ret' (a, b) fun _ h => h

/-- **A client with one vtable gives a copy to both handles** (`vtR_dup`). -/
theorem two_handles_one_vtable {t : AllocTables Tgt} {fns : VTableFns} {impl : CVTable Tgt}
    {c₁ c₂ vtp : Ptr} {I₁ I₂ : FAllocInv} (hs : Selects t fns impl) (h₁ : CAllocSpec impl c₁ I₁)
    (h₂ : CAllocSpec impl c₂ I₂) (n : BitVec 64) (k : Nat) (ra : BitVec 64) (φ₁ φ₂ : Frac)
    (hn : 0 < n.toNat) (hk : k < 64) (f₁ : I₁.fits n.toNat k) (f₂ : I₂.fits n.toNat k) :
    CTriple (vtR vtp fns.toList ⋆ ((I₁.own ⋆ I₁.fee φ₁) ⋆ (I₂.own ⋆ I₂.fee φ₂)))
      (allocVia t c₁ vtp n k ra >>= fun a => allocVia t c₂ vtp n k ra >>= fun b => pure (a, b))
      (fun ab => (I₁.allocPost n.toNat k φ₁ ab.1 ⋆ vtR vtp fns.toList) ⋆
        (I₂.allocPost n.toNat k φ₂ ab.2 ⋆ vtR vtp fns.toList)) :=
  (two_handles hs h₁ h₂ n k ra φ₁ φ₂ hn hk f₁ f₂).pre fun _ h => by
    obtain ⟨r₁, r₂, hd, rfl, hv, h12⟩ := h
    have hvv := vtR_dup hv
    -- `vtR ⋆ (I₁ ⋆ I₂)` with `vtR = vtR ⋆ vtR` is `(I₁ ⋆ vtR) ⋆ (I₂ ⋆ vtR)`
    have : ((vtR vtp fns.toList ⋆ vtR vtp fns.toList) ⋆ ((I₁.own ⋆ I₁.fee φ₁) ⋆ (I₂.own ⋆ I₂.fee φ₂)))
        ⟨r₁.heap ∪ r₂.heap, r₁.know.union r₂.know, r₁.gh.add r₂.gh⟩ := ⟨r₁, r₂, hd, rfl, hvv, h12⟩
    have e : ((vtR vtp fns.toList ⋆ vtR vtp fns.toList) ⋆ ((I₁.own ⋆ I₁.fee φ₁) ⋆ (I₂.own ⋆ I₂.fee φ₂))) =
        (((I₁.own ⋆ I₁.fee φ₁) ⋆ vtR vtp fns.toList) ⋆ ((I₂.own ⋆ I₂.fee φ₂) ⋆ vtR vtp fns.toList)) := by
      ac_rfl
    rwa [e] at this

/-- **The exclusive form cannot be held twice**: two owners of the bytes of one nonempty vtable. -/
theorem vtOwn_twice {vtp f : Ptr} {fns : List Ptr} {r : Res} :
    ¬ (up (vtOwn vtp (f :: fns)) ⋆ up (vtOwn vtp (f :: fns))) r := by
  rintro ⟨r₁, r₂, hd, -, ⟨h1, -⟩, ⟨h2, -⟩⟩
  -- both own the first byte of entry 0
  have first : ∀ h : FHeap, vtOwn vtp (f :: fns) h.erase → ∃ b, vtp.block = some b ∧
      h (b, vtp.off.toNat) ≠ none := by
    intro h hv
    obtain ⟨h₁, h₂, hd', he, ⟨A, S, K, bs, -, hsz, -, b, hb, -, hl⟩, -⟩ := hv
    refine ⟨b, hb, fun hn => ?_⟩
    have e := congrFun he (b, vtp.off.toNat)
    rw [show h.erase (b, vtp.off.toNat) = none by simp [FHeap.erase, hn], Heap.union_apply,
      hl, if_pos ⟨rfl, Nat.le_refl _, by rw [hsz]; exact Nat.lt_add_of_pos_right (by decide)⟩] at e
    cases e
  obtain ⟨b, hb, n1⟩ := first _ h1
  obtain ⟨b', hb', n2⟩ := first _ h2
  rw [hb] at hb'; cases hb'
  rcases hd (b, vtp.off.toNat) with e | e
  · exact n1 e
  · exact n2 e

/-! ## The model fact: `const` storage is never written or freed -/

/-- A live `const` global of 8 bytes at 4096. -/
def cblk : Block :=
  { bytes := Enc.encode (7 : BitVec 64), align := 8, kind := .constGlobal, live := true, addr := 4096 }

/-- A memory whose block 0 is `cblk`. -/
def cmem : Mem := { blocks := #[cblk] }

theorem cmem_block : cmem.blocks[0]? = some cblk := rfl

theorem cmem_access : cmem.access ⟨some 0, 0⟩ (Enc.size (BitVec 64)) 8 = pure (0, cblk, 0) :=
  access_of rfl cmem_block rfl (by decide)
    (by rw [show cblk.bytes.size = 8 from LawfulEnc.size_encode _]; decide) (by decide)
    (by simp [cblk])

/-- **A store to a `const` global is `.illegal`.** -/
theorem store_const_illegal :
    (store 8 ⟨some 0, 0⟩ (1 : BitVec 64)).run cmem = throw .illegal :=
  store_constGlobal (1 : BitVec 64) cmem_access rfl

/-- **A `free` of a `const` global is `.illegal`** (`Zig.free`, the model correction that makes
`const` knowledge persistent: without it, the owner of all of a `const` global's bytes could end
the block under a frame that knows it). -/
theorem free_const_illegal : ((Zig.free ⟨some 0, 0⟩).run cmem).run = some (.error .illegal) := by
  simp [Zig.free, cmem_block, cblk, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get,
    StateT.get, throw, throwThe, MonadExceptOf.throw, StateT.lift, ExceptT.mk, ExceptT.run,
    ExceptT.bind, ExceptT.bindCont, pure, ExceptT.pure]

/-- The block is still live with its bytes after the failed `free`: the knowledge of it stays. -/
theorem cmem_kn : Know.Sub (cknow 0 4096 0 (Enc.encode (7 : BitVec 64))) cmem.kn :=
  Mem.kn_const (b := 0) (blk := cblk) (o := 0) cmem_block rfl rfl fun i hi => by
    simp [cblk, Array.getElem?_eq_getElem hi]

end Zig.Full.ConstKnow

#print axioms Zig.Full.ConstKnow.two_handles
#print axioms Zig.Full.ConstKnow.two_handles_one_vtable
#print axioms Zig.Full.ConstKnow.vtOwn_twice
#print axioms Zig.Full.ConstKnow.store_const_illegal
#print axioms Zig.Full.ConstKnow.free_const_illegal
#print axioms Zig.Full.ConstKnow.cmem_kn
