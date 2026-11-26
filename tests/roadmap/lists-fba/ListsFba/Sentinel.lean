import ListsFba.Witness
import Interfaces.SentinelSpec

/-!
# The sentinel theorems' allocator premise holds for the real `FixedBufferAllocator`

`Interfaces.SentinelSpec` (`tests/roadmap/interfaces`, M04) proves `make`, `append`, `resize` and
`release` of `tests/roadmap/sentinel-realloc/source.zig` for every allocator whose environment
entries meet `CAllocSpec`. Here that premise is met by the translated `FixedBufferAllocator`, as
for the list theorems (`ListsFba.Witness`):

* **The environment** (`ext`, `env0`): the functions at the vtable entries `fns` run the
  translated `FixedBufferAllocator`, every other pointer is `.illegal` (`env_runs`); its contract
  comes from the allocator's proof through `CAllocSpec.env_ofRaw` (`fba_spec`), so every theorem
  of `SentinelSpec` has a satisfiable allocator premise.
* `Interfaces.SentinelSpec.make_spec.nonvacuous`: `make` of one item, with the precondition at
  program start (`ListsFba.make_admissible`; the empty list joins the frame).
* `append_grant.nonvacuous`, `resize_grant.nonvacuous`, `release_spec.nonvacuous`: an empty
  buffer whose one-byte grant the real allocator made (`ListsFba.granted_admissible`: its `alloc`
  run from program start returns a grant, `AllocFba.FBA.fthread_alloc_room`).
-/

namespace ListsFba.Sentinel

open Zig Zig.Full Zig.Witness Zig.Full.FAssn AllocFba.FBA ListsFba

/-- The environment of the sentinel program: the allocator's entries at `fns`, nothing elsewhere. -/
instance ext : Interfaces.Sentinel.Ext where
  call0 f c n a ra := if f = fns.alloc then
    ConcM.liftMem (AllocFba.Gen.heap_FixedBufferAllocator_alloc c n ⟨a.bits⟩ ra) else throw .illegal
  call1 f c s a n ra := if f = fns.remap then
    ConcM.liftMem (AllocFba.Gen.heap_FixedBufferAllocator_remap c s ⟨a.bits⟩ n ra) else throw .illegal
  call2 f c s a ra := if f = fns.free then
    ConcM.liftMem (AllocFba.Gen.heap_FixedBufferAllocator_free c s ⟨a.bits⟩ ra) else throw .illegal

/-- The environment's `resize` (the program never calls it). -/
def env0 : AllocEnv Interfaces.Sentinel.Tgt :=
  { AllocEnv.closed with
    resize := fun f a => if f = fns.resize then
      ConcM.liftMem (AllocFba.impl.resize a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2) else throw .illegal }

/-- The environment's allocator at `fns` runs the translated `FixedBufferAllocator`. -/
theorem env_runs : CVTable.env (Interfaces.SentinelSpec.env env0) fns = CVTable.ofRaw AllocFba.impl := by
  simp only [CVTable.env, CVTable.ofRaw, Interfaces.SentinelSpec.env, env0, Interfaces.SentinelSpec.al,
    extCall, AllocFba.impl, CVTable.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext <;> first | rfl | simp [ext]

/-- The real allocator meets the contract that the sentinel theorems assume. -/
theorem fba_spec (A1 A0 γ : Nat) :
    CAllocSpec (CVTable.env (Interfaces.SentinelSpec.env env0) fns) ctx (I0 A1 A0 γ) :=
  CAllocSpec.env_ofRaw env_runs (CAllocSpec.ofRaw
    (fun len k ra φ h1 h2 h3 => (fthread_alloc ctx (B A1 A0) γ 0 len k ra φ h1 h2 h3).toPartial)
    (fun s k n ra A S K q q' φ tl h1 h2 h3 h4 h5 _ =>
      (fthread_resize ctx (B A1 A0) γ 0 s k n ra A S K q q' φ tl h1 h2 h3 h4 h5).toPartial)
    (fun s k n ra φ bs h1 h2 h3 h4 h5 =>
      (fthread_remap ctx (B A1 A0) γ 0 s k n ra φ bs h1 h2 h3 h4 h5).toPartial)
    (fun s k ra φ bs _ h2 h3 => (fthread_free ctx (B A1 A0) γ 0 s k ra φ bs h2 h3).toPartial.post
      fun _ _ h => Full.sep_emp.mpr h))

-- `make` of one item at program start (`make_admissible`).
nonvacuity_witness Interfaces.SentinelSpec.make_spec := by
  obtain ⟨A1, A0, γ, h⟩ := make_admissible
  exact ⟨ext, ctx, vtp, fns, I0 A1 A0 γ, env0, Frac.one.half, 1, by decide,
    fits16 A1 A0 γ (by decide) (by decide), fba_spec A1 A0 γ, h⟩

-- `append`, `resize` and `release` of an empty buffer: its grant of one byte (the sentinel's) is
-- the real allocator's, after its `alloc` ran from program start (`granted_admissible`).
nonvacuity_witness Interfaces.SentinelSpec.append_grant := by
  obtain ⟨A1, A0, γ, p, bs, hbs, h⟩ := granted_admissible 1 0 (by decide) (by decide) (by decide)
  exact ⟨ext, ctx, vtp, fns, I0 A1 A0 γ, env0, Frac.one.half.half, ⟨p, 0⟩, 0, bs, hbs.symm,
    by simp, fits16 A1 A0 γ (by decide) (by simp), fba_spec A1 A0 γ, CAdmit.of h⟩

nonvacuity_witness Interfaces.SentinelSpec.resize_grant := by
  obtain ⟨A1, A0, γ, p, bs, hbs, h⟩ := granted_admissible 1 0 (by decide) (by decide) (by decide)
  exact ⟨ext, ctx, vtp, fns, I0 A1 A0 γ, env0, Frac.one.half.half, ⟨p, 0⟩, 1, bs, hbs.symm,
    by simp, by decide, fits16 A1 A0 γ (by decide) (by decide), fba_spec A1 A0 γ, CAdmit.of h⟩

nonvacuity_witness Interfaces.SentinelSpec.release_spec := by
  obtain ⟨A1, A0, γ, p, bs, hbs, h⟩ := granted_admissible' 1 0 (by decide) (by decide) (by decide)
  exact ⟨ext, ctx, vtp, fns, I0 A1 A0 γ, env0, Frac.one.half.half, ⟨p, 0⟩, bs, hbs.symm,
    by rw [hbs]; decide, fba_spec A1 A0 γ, CAdmit.of h⟩

end ListsFba.Sentinel
