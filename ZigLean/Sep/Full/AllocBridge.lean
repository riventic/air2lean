import ZigLean.Sep.Full.Dispatch

/-!
# A proved allocator's code behind an open `std.mem.Allocator`

A client over an open `std.mem.Allocator` (`docs/interfaces.md`) assumes the contract
`CAllocSpec (CVTable.env e fns) ctx I` of the environment's allocator at the vtable `fns` (premise
EXT-05): four `CTriple`s, the concurrent form of `FAllocSpec`. A translated allocator (the
`FixedBufferAllocator`, an arena, the page allocator) has four entries `vt : RawVTable` (`MemM`
code). This module connects the two, once for every allocator:

* `CVTable.ofRaw vt`: the entries of `vt` as concurrent functions (each runs its `MemM` code,
  `ConcM.liftMem`);
* `CAllocSpec.ofRaw`: the entries' **thread triples** (`FTTriple`, with `FAllocSpec`'s pre- and
  postconditions) give `CAllocSpec (CVTable.ofRaw vt)`. A sequential `FAllocSpec` alone is not
  enough: a thread runs an entry while other threads run, so each step of the code must also be
  local to the thread (`ThreadLocal`, `FTTriple.ofSeq`). `fsym` proves the thread triples of
  translated code as it proves the sequential ones, discharging each primitive's locality with
  its providers (`ZigLean/Sep/Full/AutoThread.lean`); the `FixedBufferAllocator`'s are in
  `tests/roadmap/alloc-fba` (`FBA.fthread_*`).
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

/-- **An allocator whose entries meet `FAllocSpec`'s contract as thread triples meets the
concurrent contract.** -/
theorem CAllocSpec.ofRaw {vt : RawVTable} {ctx : Ptr} {I : FAllocInv}
    (ha : ∀ len k ra φ, 0 < len.toNat → k < 64 → I.fits len.toNat k →
      FTTriple (I.own ⋆ I.fee φ) (vt.alloc ctx len k ra) (I.allocPost len.toNat k φ))
    (hr : ∀ s k n ra A S K q q' φ tl, k < 64 → 0 < n.toNat → I.fits n.toNat k → 0 < s.len.toNat →
      q'.val ≤ q.val → (n.toNat < s.len.toNat → q' = q) →
      FTTriple (I.own ⋆ (I.held s.ptr s.len.toNat k A S K q q' φ ⋆
          I.relBytes s.ptr A S K n.toNat s.len.toNat tl))
        (vt.resize ctx s k n ra) (I.rresizePost s.ptr k s.len.toNat n.toNat A S K q q' φ tl))
    (hm : ∀ s k n ra φ bs, k < 64 → 0 < n.toNat → I.fits n.toNat k → s.len.toNat = bs.size →
      0 < bs.size → FTTriple (I.own ⋆ I.granted s.ptr k φ bs) (vt.remap ctx s k n ra)
        (I.remapPost s.ptr k φ bs n.toNat))
    (hf : ∀ s k ra φ bs, k < 64 → s.len.toNat = bs.size → 0 < bs.size →
      FTTriple (I.own ⋆ I.granted s.ptr k φ bs) (vt.free ctx s k ra) (fun _ => I.own ⋆ I.fee φ)) :
    CAllocSpec (CVTable.ofRaw vt : CVTable Tgt) ctx I :=
  CAllocSpec.of_ctriples
    (fun len k ra φ h1 h2 h3 => CTriple.liftMem (ha len k ra φ h1 h2 h3))
    (fun s k n ra A S K q q' φ tl h1 h2 h3 h4 h5 h6 =>
      CTriple.liftMem (hr s k n ra A S K q q' φ tl h1 h2 h3 h4 h5 h6))
    (fun s k n ra φ bs h1 h2 h3 h4 h5 => CTriple.liftMem (hm s k n ra φ bs h1 h2 h3 h4 h5))
    (fun s k ra φ bs h1 h2 h3 => CTriple.liftMem (hf s k ra φ bs h1 h2 h3))

/-- **The environment's allocator at `fns` meets the contract** when its functions there run the
code of an allocator that meets it (premise EXT-05 discharged for that environment). -/
theorem CAllocSpec.env_ofRaw {vt : RawVTable} {e : AllocEnv Tgt} {fns : VTableFns} {ctx : Ptr}
    {I : FAllocInv} (he : CVTable.env e fns = CVTable.ofRaw vt)
    (h : CAllocSpec (CVTable.ofRaw vt : CVTable Tgt) ctx I) : CAllocSpec (CVTable.env e fns) ctx I :=
  he ▸ h

end Full
end Zig
