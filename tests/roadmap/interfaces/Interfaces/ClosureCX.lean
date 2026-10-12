import Interfaces.MixSpec
import ZigLean.Sep.Full.Init

/-!
# The environment's contract never speaks for a function of the program (kernel-checked)

A call through an open interface's vtable runs the program's function when the pointer is one
(`docs/interfaces.md`, semantics 2) and the environment only for any other pointer (3). So a
proof may assume the environment's contract (premise EXT-05) only for a vtable none of whose
entries is a function of the program (`CAllocSpec.dispatch_env` and its `AllocTables.Fresh`).

1. `mix_fba_dispatch`: in `mix.zig`, the dispatch through the FixedBufferAllocator's vtable is
   the FixedBufferAllocator's translated code for every environment (`Ext`): no assumption
   about the environment says anything about it (`CVTable.dispatch_closure_env`).
2. `naive_unsound`: dropping the freshness premise is unsound. A program whose closure holds a
   double-issuing allocator (every `alloc` returns the same pointer), and an environment whose
   allocator meets `CAllocSpec` (it never grants): the environment's contract holds at the
   closure allocator's vtable, but the dispatch through that vtable (the closure allocator)
   does not meet it. A rule that lifted the environment's contract to any vtable would prove
   the double-issuing allocator correct.
-/

namespace Interfaces.ClosureCX

open Zig Zig.Full Zig.Full.FAssn Interfaces.Mix

/-! ## 1. `mix.zig`: the FixedBufferAllocator's vtable -/

/-- The FixedBufferAllocator's entries, the program's translated functions. -/
def fba : CVTable Tgt where
  alloc c n k ra := ConcM.liftMem (heap_FixedBufferAllocator_alloc c n (MixSpec.al k) ra)
  resize c s k n ra := ConcM.liftMem (heap_FixedBufferAllocator_resize c s (MixSpec.al k) n ra)
  remap c s k n ra := ConcM.liftMem (heap_FixedBufferAllocator_remap c s (MixSpec.al k) n ra)
  free c s k ra := ConcM.liftMem (heap_FixedBufferAllocator_free c s (MixSpec.al k) ra)

/-- The vtable that `heap_FixedBufferAllocator_allocator` returns (global 4 of `mem0`). -/
def fbaFns : VTableFns := ⟨⟨some 0, 0⟩, ⟨some 1, 0⟩, ⟨some 2, 0⟩, ⟨some 3, 0⟩⟩

/-- **The dispatch through the FixedBufferAllocator's vtable is its translated code, whatever
the environment.** -/
theorem mix_fba_dispatch [Ext] (e : AllocEnv Tgt) :
    CVTable.dispatch (MixSpec.tables e) fbaFns = fba :=
  CVTable.dispatch_of_selects ⟨rfl, rfl, rfl, rfl⟩

/-- No two environments differ there. -/
theorem mix_fba_env_indep (E₁ E₂ : Ext) (e₁ e₂ : AllocEnv Tgt) :
    @CVTable.dispatch Tgt (@MixSpec.tables E₁ e₁) fbaFns =
      @CVTable.dispatch Tgt (@MixSpec.tables E₂ e₂) fbaFns := by
  rw [@mix_fba_dispatch E₁ e₁, @mix_fba_dispatch E₂ e₂]

/-! ## 2. The naive rule -/

section Naive

variable {Tgt : Type}

/-- Every `alloc` returns the same pointer `p`. -/
def double (p : Ptr) : CVTable Tgt where
  alloc _ _ _ _ := pure (some p)
  resize _ _ _ _ _ := pure false
  remap _ _ _ _ _ := pure none
  free _ _ _ _ := pure ()

/-- An environment that never grants: every `alloc` fails. -/
def never : AllocEnv Tgt where
  alloc _ _ := pure none
  resize _ _ := pure false
  remap _ _ := pure none
  free _ _ := pure ()

/-- A closure with the double-issuing allocator at `fbaFns`, and the environment `never`. -/
def tables (p : Ptr) : AllocTables Tgt where
  alloc := [(fbaFns.alloc, fun a => (double p).alloc a.1 a.2.1 a.2.2.1 a.2.2.2)]
  resize := [(fbaFns.resize, fun a => (double p).resize a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)]
  remap := [(fbaFns.remap, fun a => (double p).remap a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)]
  free := [(fbaFns.free, fun a => (double p).free a.1 a.2.1 a.2.2.1 a.2.2.2)]
  env := never

/-- The invariant of an allocator that grants nothing: it owns nothing, and no token exists. -/
def I : FAllocInv where
  own := emp
  tok _ _ _ _ _ _ _ _ := ⟪False⟫

theorem tok_false {p : Ptr} {n k A S : Nat} {K : BlockKind} {q φ : Frac} {R : FAssn} {r : Res}
    (h : (I.tok p n k A S K q φ ⋆ R) r) : False := by
  obtain ⟨r₁, -, -, -, h₁, -⟩ := h
  exact h₁.1

theorem granted_false {p : Ptr} {k : Nat} {φ : Frac} {bs : Array Byte} {r : Res}
    (h : I.granted p k φ bs r) : False := by
  obtain ⟨A, S, K, q, -, r₂, -, -, -, h₂⟩ := h
  exact tok_false h₂

theorem of_false {α : Type} {P : FAssn} {x : ConcM Tgt α} {Q : α → FAssn}
    (h : ∀ r, P r → False) : CTriple P x Q :=
  fun _ _ r _ _ hp _ => (h r hp).elim

/-- **The environment's contract holds at every vtable**: `never` meets `CAllocSpec` for `I`. -/
theorem never_spec (fns : VTableFns) (ctx : Ptr) :
    CAllocSpec (CVTable.env (never (Tgt := Tgt)) fns) ctx I := by
  refine CAllocSpec.of_ctriples
    (fun _ _ _ _ _ _ _ => show CTriple _ (pure none) _ from CTriple.ret' _ fun _ h => h)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => of_false fun _ h => ?_)
    (fun _ _ _ _ _ _ _ _ _ _ _ => of_false fun _ h => ?_)
    (fun _ _ _ _ _ _ _ _ => of_false fun _ h => ?_)
  · obtain ⟨-, r₂, -, -, -, r₃, -, -, -, h₃, -⟩ := h
    exact tok_false h₃
  · obtain ⟨-, r₂, -, -, -, h₂⟩ := h
    exact granted_false h₂
  · obtain ⟨-, r₂, -, -, -, h₂⟩ := h
    exact granted_false h₂

/-- **The double-issuing allocator does not meet `CAllocSpec` for `I`**: its `alloc` returns a
pointer, which `I` cannot grant (in the memory at program start). -/
theorem double_not_spec (p ctx : Ptr) : ¬ CAllocSpec (double (Tgt := Tgt) p) ctx I := by
  intro h
  obtain ⟨hh, hg⟩ := initRes_holds Placement.fresh [] (by simp)
  have t := h.alloc 1 0 0 Frac.zero (by decide) (by decide) trivial 0 _ _ _ hh (sep_emp.mpr hg)
    (Mem.init_fseq Placement.fresh [] (by decide))
  obtain ⟨_, -, ⟨-, r₂, -, -, -, bs, hb⟩, -⟩ := t
  obtain ⟨_, r₄, -, -, -, h₄⟩ := hb
  exact granted_false h₄

/-- **Lifting the environment's contract to a vtable of the program is unsound.** -/
theorem naive_unsound :
    ¬ ∀ (t : AllocTables Tgt) (fns : VTableFns) (ctx : Ptr) (J : FAllocInv),
      CAllocSpec (CVTable.env t.env fns) ctx J → CAllocSpec (CVTable.dispatch t fns) ctx J := by
  intro naive
  have h := naive (tables ⟨none, 0⟩) fbaFns ⟨none, 0⟩ I (never_spec fbaFns ⟨none, 0⟩)
  rw [CVTable.dispatch_of_selects (t := tables ⟨none, 0⟩) (fns := fbaFns)
    (impl := double ⟨none, 0⟩) ⟨rfl, rfl, rfl, rfl⟩] at h
  exact double_not_spec ⟨none, 0⟩ ⟨none, 0⟩ h

end Naive

end Interfaces.ClosureCX
