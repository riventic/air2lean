import ZigLean.Sep.Full.Ops
import ZigLean.Sep.Full.AutoAttr
import ZigLean.Mem.AbiLemmas

/-!
# Full-state rules of the C-ABI conversion at a bound extern call (X01)

`Zig.abiPtrCheck` (`ZigLean/Mem/Abi.lean`) checks what an extern definition's pointer type
asserts about a value the declaration passes (non-null, alignment, sentinel byte) and reads
only. Its rules, in a thread and sequentially, as `checkAlign_of` is (`Full/Ops.lean`):

* `abiPtrCheck_of`: a value that every memory holding the precondition admits
  (`Mem.abiPtrOk`); the general rule, for a sentinel too (the caller shows the byte).
* `abiPtrCheck_null_of`: null into a pointer that admits it.
* `abiPtrCheck_addr_of`: a pointer into a block at a known nonzero address that the target's
  alignment divides, for a target without a sentinel (`AddrOf`, as `checkAlign_of`).

The last two are `@[fsym]`. A value the target does not admit has no rule: the conversion is
`.illegal` there (`abiPtrCheck_null_nonNull`, `abiPtrCheck_misaligned`,
`abiPtrCheck_no_sentinel`).
-/

namespace Zig
namespace Full

open FAssn

namespace FTTotalTriple

variable {P : FAssn} {q : Ptr} {b : BlockId} {A : Nat}

/-- **The C-ABI conversion check** of a value that every memory holding `P` admits. -/
theorem abiPtrCheck_of {req : AbiPtrReq}
    (h : ∀ m r rF, Holds m r rF → P r → m.abiPtrOk req q = true) :
    FTTotalTriple P (abiPtrCheck req q) (fun _ => P) :=
  conseq (of_read fun m r rF hh hp _ => by rw [abiPtrCheck_run, h m r rF hh hp]; rfl)
    (fun _ h => h) (fun _ _ h => (sep_lift.mp h).2)

/-- `abiPtrCheck_of` for null into a pointer that admits it. -/
theorem abiPtrCheck_null_of {req : AbiPtrReq} (h : req.nonNull = false) :
    FTTotalTriple P (abiPtrCheck req Ptr.null) (fun _ => P) :=
  abiPtrCheck_of fun _ _ _ _ _ => by simp [Mem.abiPtrOk, addrIn, Ptr.null, h]

/-- `abiPtrCheck_of` for a pointer into block `b` at a nonzero address that the target's
alignment divides, for a target without a sentinel. -/
theorem abiPtrCheck_addr_of {req : AbiPtrReq} (hqb : q.block = some b) (h : AddrOf b A P)
    (h0 : (A : Int) + q.off ≠ 0) (hal : ((A : Int) + q.off) % req.align = 0)
    (hs : req.sentinel = none) : FTTotalTriple P (abiPtrCheck req q) (fun _ => P) :=
  abiPtrCheck_of fun m r rF hh hp => by
    obtain ⟨blk, hb, rfl⟩ := h m r rF hh hp
    obtain ⟨qb, qo⟩ := q
    simp only at hqb h0 hal; subst hqb
    simp [Mem.abiPtrOk, addrIn, hb, h0, hal, hs]

end FTTotalTriple

namespace FTotalTriple

variable {P : FAssn} {q : Ptr} {b : BlockId} {A : Nat}

/-- **The C-ABI conversion check** of a value that every memory holding `P` admits. -/
theorem abiPtrCheck_of {req : AbiPtrReq}
    (h : ∀ m r rF, Holds m r rF → P r → m.abiPtrOk req q = true) :
    FTotalTriple P (abiPtrCheck req q) (fun _ => P) :=
  (FTTotalTriple.abiPtrCheck_of h).toFTotalTriple

/-- `abiPtrCheck_of` for null into a pointer that admits it. -/
theorem abiPtrCheck_null_of {req : AbiPtrReq} (h : req.nonNull = false) :
    FTotalTriple P (abiPtrCheck req Ptr.null) (fun _ => P) :=
  (FTTotalTriple.abiPtrCheck_null_of h).toFTotalTriple

/-- `abiPtrCheck_of` at a nonzero aligned address, for a target without a sentinel. -/
theorem abiPtrCheck_addr_of {req : AbiPtrReq} (hqb : q.block = some b) (h : AddrOf b A P)
    (h0 : (A : Int) + q.off ≠ 0) (hal : ((A : Int) + q.off) % req.align = 0)
    (hs : req.sentinel = none) : FTotalTriple P (abiPtrCheck req q) (fun _ => P) :=
  (FTTotalTriple.abiPtrCheck_addr_of hqb h h0 hal hs).toFTotalTriple

end FTotalTriple

attribute [fsym] FTotalTriple.abiPtrCheck_null_of FTotalTriple.abiPtrCheck_addr_of
  FTTotalTriple.abiPtrCheck_null_of FTTotalTriple.abiPtrCheck_addr_of

end Full
end Zig
