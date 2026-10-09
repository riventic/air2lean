import AllocFba.Gen
import ZigLean.Sep.AllocSpec.Wrap
import ZigLean.Sep.AllocSpec.Dispatch
import ZigLean.Sep.AllocSpec.Norm

/-!
# The generated `std.mem.Allocator` wrappers are `Wrap.*`

Each wrapper that the translator emitted for `client.zig` (`--allocator-model translated`) is
equal, as a `MemM` program, to its `Wrap.*` step semantics over `vt a` — the dispatch through
the `Allocator`'s vtable pointer `a.vtable` to the translated `FixedBufferAllocator`
(`dispatch`). The vtable load and the indirect call are inside `vt a`, so the equalities hold
for every argument and every memory.
-/

namespace AllocFba

open Zig Gen

/-- The translated `FixedBufferAllocator` entries, with the alignment as a `Nat` log2. -/
def impl : RawVTable where
  alloc c n k ra := heap_FixedBufferAllocator_alloc c n ⟨BitVec.ofNat 6 k⟩ ra
  resize c s k n ra := heap_FixedBufferAllocator_resize c s ⟨BitVec.ofNat 6 k⟩ n ra
  remap c s k n ra := heap_FixedBufferAllocator_remap c s ⟨BitVec.ofNat 6 k⟩ n ra
  free c s k ra := heap_FixedBufferAllocator_free c s ⟨BitVec.ofNat 6 k⟩ ra

/-- The function pointers in the generated vtable constant (globals 1 to 4 of `mem0`). -/
abbrev fns : VTableFns := ⟨⟨some 1, 0⟩, ⟨some 2, 0⟩, ⟨some 3, 0⟩, ⟨some 4, 0⟩⟩

/-- The allocator behind the `Allocator` value `a`. -/
abbrev vt (a : mem_Allocator) : RawVTable := dispatch impl fns a.vtable

theorem ctz1 : (1 : BitVec 64).ctz = 0 := ctz_twoPow (k := 0) (by decide)
theorem ctz4 : (4 : BitVec 64).ctz = 2 := ctz_twoPow (k := 2) (by decide)

theorem fromByteUnits_one : mem_Alignment_fromByteUnits 1 = pure ⟨0⟩ := by
  unfold mem_Alignment_fromByteUnits
  simp only [Zig.ctz, ctz1]
  rfl

theorem fromByteUnits_four : mem_Alignment_fromByteUnits 4 = pure ⟨2⟩ := by
  unfold mem_Alignment_fromByteUnits
  simp only [Zig.ctz, ctz4]
  rfl

theorem mul_one (x : BitVec 64) : math_mul__anon_1 1 x = pure (.ok x) := by
  unfold math_mul__anon_1
  rw [Norm.mulWithOverflow_one]
  rfl

theorem isSome_ite {α β : Type} (o : Option α) (f : α → MemM β) (g : MemM β) :
    (if o.isSome = true then (StateT.lift (optPayload o) : MemM α) >>= f else g) =
      match o with
      | none => g
      | some p => f p := by cases o <;> rfl

/-- Normalize a generated wrapper and its `Wrap.*` counterpart. -/
macro "bridge_norm" : tactic => `(tactic| (
  simp only [Wrap.allocBytes, Wrap.allocItems_one, Wrap.allocAdvanced, Wrap.allocSlice, Wrap.create,
    Wrap.destroy, Wrap.freeBytes, Wrap.free_one, Wrap.freeSentinel, Wrap.dupe, Wrap.copyChecked,
    Wrap.allocSentinel, Wrap.reallocAdvanced, Wrap.realloc, Wrap.alignCast, Wrap.liftR, dispatch,
    impl, Wrap.byteLen_one, Zig.isNonErr, Zig.isErr, Zig.unwrapPayload, Zig.unwrapErr,
    Bool.not_false, Bool.not_true, ↓reduceIte, Nat.pow_zero, Bool.false_eq_true,
    StateT.run'_eq, StateT.run_bind, StateT.run_pure, Norm.run_callM, Norm.run_callR,
    Norm.run_liftM, Norm.run_liftR, Norm.run_ite, Norm.ite_bind, Norm.run_throw,
    Norm.throw_bind, Norm.lift_pure, Norm.lift_throw, Norm.sub_zero, Norm.elem_zero,
    Norm.run_get, Norm.run_modify,
    bind_assoc, pure_bind, map_pure, bind_map_left, map_bind, Norm.beq_true_iff,
    fromByteUnits_one, fromByteUnits_four, mul_one]
  try simp only [isSome_ite, bind_assoc, pure_bind, Norm.ite_bind]))

theorem bind_ext {α β : Type} {x : MemM α} {f g : α → MemM β} (h : ∀ a, f a = g a) :
    x >>= f = x >>= g := by
  simp only [funext h]

/-- Close a normalized bridge goal: walk both sides bind by bind, split the matches on the
results of the allocator calls, and normalize again. -/
macro "bridge_close" : tactic => `(tactic| (
  repeat' (first
    | rfl
    | (refine bind_ext fun _ => ?_)
    | (split <;> (try simp only [↓reduceIte, *])))))

theorem allocBytes4_eq (a : mem_Allocator) (n ra : BitVec 64) :
    mem_Allocator_allocBytesWithAlignment__anon_1 a n ra = Wrap.allocBytes (vt a) a.ptr 2 n ra := by
  simp only [mem_Allocator_allocBytesWithAlignment__anon_1]; bridge_norm; bridge_close

theorem allocBytes1_eq (a : mem_Allocator) (n ra : BitVec 64) :
    mem_Allocator_allocBytesWithAlignment__anon_2 a n ra = Wrap.allocBytes (vt a) a.ptr 0 n ra := by
  simp only [mem_Allocator_allocBytesWithAlignment__anon_2]; bridge_norm; bridge_close

theorem alloc_eq (a : mem_Allocator) (n : BitVec 64) :
    mem_Allocator_alloc__anon_1 a n = Wrap.allocSlice (vt a) a.ptr 1 0 n := by
  simp only [mem_Allocator_alloc__anon_1, mem_Allocator_allocWithSizeAndAlignment__anon_1,
    allocBytes1_eq]
  bridge_norm
  bridge_close
  done

end AllocFba
