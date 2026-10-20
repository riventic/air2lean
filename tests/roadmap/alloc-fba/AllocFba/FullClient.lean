import AllocFba.Wrappers
import ZigLean.Sep.Full.AutoAll
import ZigLean.Sep.Full.Local

/-!
# The translated FBA client in the full-state logic

The generated client is walked by `fsym`, using the generated wrappers' contracts over
`FAllocSpec`, the initialized FBA invariant and its reset contract. The buffer's authority is a
positive extent share at bound12 and an untagged claim on `[0,12)`; the other four bytes remain
the client's. Stack allocation is paid by the running thread's token and room resource.

The result predicate is unchanged from the legacy client. Its replacement and the real-start
strength example must check before the legacy proof and its last library imports are retired.
-/

open Zig Zig.Full Zig.Full.FAssn AllocFba AllocFba.Gen AllocFba.FBA

namespace AllocFba.ClientFull

abbrev bufp : Ptr := ⟨some 0, 0⟩
abbrev vtp : Ptr := ⟨some 5, 0⟩

def buf (A₀ Ac : Nat) : FBuf := ⟨bufp, 12, A₀, 16, .global, Ac⟩

def expected (v : BitVec 8) : BitVec 32 :=
  BitVec.ofNat 32 (v.toNat + v.toNat + (v + 1).toNat)

def Res (v : BitVec 8) (r : BitVec 32) : Prop :=
  r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = expected v

/-- The full-state client contract: the old stack-room premise is an owned resource, and the
buffer carries only the extent share and claim approved for the native invariant. -/
theorem client_spec (v : BitVec 8) (A₀ S D : Nat) (q : Frac) (bs : Array Byte)
    (hs : bs.size = 16) (hA : A₀ + 16 ≤ 2 ^ 64) :
    FTotalTriple
      (up (regionIn bufp A₀ 16 .global 1 bs) ⋆ (vtR vtp fns.toList ⋆
        (cur 0 ⋆ (sp 0 S D ⋆ (⟪D + stackCharge 24 8 ≤ S⟫ ⋆
          (bshare 0 q 12 ⋆ bclaim 0 0 12 none))))))
      (fba_client v)
      (fun r => ⟪Res v r⟫ ⋆ (sp 0 S D ⋆ Junk)) := by
  have init := fun (ctx : Ptr) (Ac : Nat) =>
    @fallocator_init ctx (buf A₀ Ac) q
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
    fun ctx Ac γ e n => Wrappers.alloc_of (fallocSpec ctx (buf A₀ Ac) γ e)
      Frac.one.half n,
    fun ctx Ac γ e s n bs => Wrappers.realloc_of (fallocSpec ctx (buf A₀ Ac) γ e)
      Frac.one.half s n bs,
    fun ctx Ac γ e s bs => Wrappers.free_of (fallocSpec ctx (buf A₀ Ac) γ e)
      Frac.one.half s bs,
    reset, fun (h : Heap) => EUpd.of_imp (@JunkAt.junk h)]

end AllocFba.ClientFull
