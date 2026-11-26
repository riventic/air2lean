import ListsFba.Witness
import Interfaces.WideSpec

/-!
# The wide sentinel theorems' allocator premise holds for the real `FixedBufferAllocator`

`Interfaces.WideSpec` (`tests/roadmap/interfaces`, M04) proves `make`, `append`, `resize` and
`release` of a `[:0]T` for `T` = `u16`, `u32` and `u64` for every allocator whose environment
entries meet `CAllocSpec`. Here that premise is met by the translated `FixedBufferAllocator`, as
for the `u8` program (`ListsFba.Sentinel`):

* **The environment** (`ext`, `env0`): the functions at the vtable entries `fns` run the
  translated `FixedBufferAllocator`, every other pointer is `.illegal` (`env_runs`); its contract
  comes from the allocator's proof through `CAllocSpec.env_ofRaw` (`fba_spec`), so every theorem
  of `WideSpec` has a satisfiable allocator premise.
* `Interfaces.WideSpec.make{16,32,64}_spec.nonvacuous`: `make` of zero items at each alignment
  (`2 ^ 1`, `2 ^ 2`, `2 ^ 3`), with the precondition at program start
  (`ListsFba.start_admissible`; the empty list joins the frame).

`append`, `resize` and `release` take a grant of the allocator in their precondition. A witness
for them needs a state in which the real allocator has granted one, that is, that its `alloc`
succeeded from the start state; the contract's `allocPost` allows `null`, so this needs a theorem
about the `FixedBufferAllocator` itself and is not shown here.
-/

namespace ListsFba.Wide

open Zig Zig.Full Zig.Witness Zig.Full.FAssn AllocFba.FBA ListsFba

/-- The environment of the wide program: the allocator's entries at `fns`, nothing elsewhere. -/
instance ext : Interfaces.Wide.Ext where
  call0 f c n a ra := if f = fns.alloc then
    ConcM.liftMem (AllocFba.Gen.heap_FixedBufferAllocator_alloc c n ⟨a.bits⟩ ra) else throw .illegal
  call1 f c s a n ra := if f = fns.remap then
    ConcM.liftMem (AllocFba.Gen.heap_FixedBufferAllocator_remap c s ⟨a.bits⟩ n ra) else throw .illegal
  call2 f c s a ra := if f = fns.free then
    ConcM.liftMem (AllocFba.Gen.heap_FixedBufferAllocator_free c s ⟨a.bits⟩ ra) else throw .illegal

/-- The environment's `resize` (the program never calls it). -/
def env0 : AllocEnv Interfaces.Wide.Tgt :=
  { AllocEnv.closed with
    resize := fun f a => if f = fns.resize then
      ConcM.liftMem (AllocFba.impl.resize a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2) else throw .illegal }

/-- The environment's allocator at `fns` runs the translated `FixedBufferAllocator`. -/
theorem env_runs : CVTable.env (Interfaces.WideSpec.env env0) fns = CVTable.ofRaw AllocFba.impl := by
  simp only [CVTable.env, CVTable.ofRaw, Interfaces.WideSpec.env, env0, Interfaces.WideSpec.al,
    extCall, AllocFba.impl, CVTable.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext <;> first | rfl | simp [ext]

/-- The real allocator meets the contract that the wide sentinel theorems assume. -/
theorem fba_spec (A1 A0 γ : Nat) :
    CAllocSpec (CVTable.env (Interfaces.WideSpec.env env0) fns) ctx (I0 A1 A0 γ) :=
  CAllocSpec.env_ofRaw env_runs (CAllocSpec.ofRaw
    (fun len k ra φ h1 h2 h3 => (fthread_alloc ctx (B A1 A0) γ 0 len k ra φ h1 h2 h3).toPartial)
    (fun s k n ra A S K q q' φ tl h1 h2 h3 h4 h5 _ =>
      (fthread_resize ctx (B A1 A0) γ 0 s k n ra A S K q q' φ tl h1 h2 h3 h4 h5).toPartial)
    (fun s k n ra φ bs h1 h2 h3 h4 h5 =>
      (fthread_remap ctx (B A1 A0) γ 0 s k n ra φ bs h1 h2 h3 h4 h5).toPartial)
    (fun s k ra φ bs _ h2 h3 => (fthread_free ctx (B A1 A0) γ 0 s k ra φ bs h2 h3).toPartial.post
      fun _ _ h => Full.sep_emp.mpr h))

-- `make` of zero items at each alignment: the allocator's invariant, the fee and the vtable at
-- program start; the empty list joins the frame.
nonvacuity_witness Interfaces.WideSpec.make16_spec := by
  obtain ⟨A1, A0, γ, h⟩ := start_admissible
  exact ⟨ext, ctx, vtp, fns, I0 A1 A0 γ, env0, Frac.one.half, 0, by decide,
    by simp [finv, ffits, B], fba_spec A1 A0 γ,
    (FAdmit.Start.frame (R := Lists.Append.alist (I0 A1 A0 γ) Frac.one.half hdr [])
      (h.mono fun _ h => ac_cast h (by simp only [startPre]; ac_rfl))).cadmit⟩

nonvacuity_witness Interfaces.WideSpec.make32_spec := by
  obtain ⟨A1, A0, γ, h⟩ := start_admissible
  exact ⟨ext, ctx, vtp, fns, I0 A1 A0 γ, env0, Frac.one.half, 0, by decide,
    by simp [finv, ffits, B], fba_spec A1 A0 γ,
    (FAdmit.Start.frame (R := Lists.Append.alist (I0 A1 A0 γ) Frac.one.half hdr [])
      (h.mono fun _ h => ac_cast h (by simp only [startPre]; ac_rfl))).cadmit⟩

nonvacuity_witness Interfaces.WideSpec.make64_spec := by
  obtain ⟨A1, A0, γ, h⟩ := start_admissible
  exact ⟨ext, ctx, vtp, fns, I0 A1 A0 γ, env0, Frac.one.half, 0, by decide,
    by simp [finv, ffits, B], fba_spec A1 A0 γ,
    (FAdmit.Start.frame (R := Lists.Append.alist (I0 A1 A0 γ) Frac.one.half hdr [])
      (h.mono fun _ h => ac_cast h (by simp only [startPre]; ac_rfl))).cadmit⟩

end ListsFba.Wide
