import ZigLean.Sep.Full.Dispatch

/-!
# A proved sequential allocator behind an open `std.mem.Allocator`

A client over an open `std.mem.Allocator` (`docs/interfaces.md`) assumes the contract
`CAllocSpec (CVTable.env e fns) ctx I` of the environment's allocator at the vtable `fns` (premise
EXT-05). A translated allocator (the `FixedBufferAllocator`, an arena, the page allocator) is
proved once against the sequential contract `FAllocSpec L vt ctx I` of its four entries
`vt : RawVTable` (`MemM` code). This module connects the two, once for every allocator:

* `CVTable.ofRaw vt`: the entries of `vt` as concurrent functions (each runs its `MemM` code,
  `ConcM.liftMem`);
* `CAllocSpec.ofRaw`: a proved `FAllocSpec` (partial or total: `FAllocSpec.toPartial`) gives
  `CAllocSpec (CVTable.ofRaw vt)`;
* `CAllocSpec.env_ofRaw`: an environment whose functions at the vtable `fns` run `vt`'s code
  (`CVTable.env e fns = CVTable.ofRaw vt`) meets the contract that the client assumes. This
  discharges EXT-05 for that environment: a client theorem over `CAllocSpec` applies to the real
  allocator, and its premise is satisfiable (the non-vacuity witnesses of such clients).

Proof-only: not reachable from `ZigLean.lean`.
-/

namespace Zig
namespace Full

variable {Tgt : Type}

/-- The four entries of a sequential allocator as concurrent functions: each entry runs its
`MemM` code in one step. -/
def CVTable.ofRaw (vt : RawVTable) : CVTable Tgt where
  alloc c n k ra := ConcM.liftMem (vt.alloc c n k ra)
  resize c s k n ra := ConcM.liftMem (vt.resize c s k n ra)
  remap c s k n ra := ConcM.liftMem (vt.remap c s k n ra)
  free c s k ra := ConcM.liftMem (vt.free c s k ra)

/-- **A proved sequential allocator meets the concurrent contract** (in either logic). -/
theorem CAllocSpec.ofRaw {L : FLogic} {vt : RawVTable} {ctx : Ptr} {I : FAllocInv}
    (h : FAllocSpec L vt ctx I) : CAllocSpec (CVTable.ofRaw vt : CVTable Tgt) ctx I :=
  have h := h.toPartial
  CAllocSpec.of_ctriples
    (fun len k ra h1 h2 h3 => CTriple.liftMem (h.alloc len k ra h1 h2 h3))
    (fun s k n ra A S K q q' tl h1 h2 h3 h4 h5 h6 =>
      CTriple.liftMem (h.resize s k n ra A S K q q' tl h1 h2 h3 h4 h5 h6))
    (fun s k n ra bs h1 h2 h3 h4 h5 => CTriple.liftMem (h.remap s k n ra bs h1 h2 h3 h4 h5))
    (fun s k ra bs h1 h2 h3 => CTriple.liftMem (h.free s k ra bs h1 h2 h3))

/-- **The environment's allocator at `fns` meets the contract** when its functions there run a
proved allocator's code (premise EXT-05 discharged for that environment). -/
theorem CAllocSpec.env_ofRaw {L : FLogic} {vt : RawVTable} {e : AllocEnv Tgt} {fns : VTableFns}
    {ctx : Ptr} {I : FAllocInv} (he : CVTable.env e fns = CVTable.ofRaw vt)
    (h : FAllocSpec L vt ctx I) : CAllocSpec (CVTable.env e fns) ctx I :=
  he ▸ CAllocSpec.ofRaw h

end Full
end Zig
