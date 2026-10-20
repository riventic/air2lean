import AllocFba.Full

/-!
# Creation from the translated fixed-buffer allocator's initialized resources

The program is the generated `allocator` helper, with the existing `fallocator_init` rule.
Creation retains its actual context/vtable and the fresh ledger at epoch zero. The raw input
is exactly the existing initializer's backed-buffer domain; it does not cover a zero-byte
backing block. Program-start admission and binding a client's fresh ledger remain separate
obligations, so this module supplies no admission witness.
-/

namespace AllocFba.FBA

open Zig Zig.Full Zig.Full.FAssn Gen

attribute [local fsym_facts] MemFacts.bshare_bound

/-- The raw resources consumed by the landed translated initializer, without a ghost seed. -/
def creationInput (ctx : Ptr) (B : FBuf) (q : Frac) (b cb : BlockId) (bs : Array Byte) : FAssn :=
  wEnd ctx 0 ⋆ (fparts ctx B q b cb ⋆ (up (regionIn B.ptr B.A B.S B.K 1 bs) ⋆
    bclaim b B.ptr.off.toNat (bnd B) none))

/-- An accepted positive request follows from the real extent bound, including capacity zero.
Acceptance permits allocation failure; it does not assert that the buffer can grant one byte. -/
theorem creation_upd {ctx : Ptr} {B : FBuf} {γ e : Nat} (hcap : B.cap ≤ 2 ^ 63) :
    EUpd (fown ctx B γ e ⋆ epTok γ e Frac.one) (finv ctx B γ e).creationPost := by
  apply (ledger ctx B γ e).creationPost
  refine ⟨(1 : BitVec 64), 0, by decide, by decide, ?_⟩
  change B.cap + 2 ^ 0 + 1 ≤ 2 ^ 64
  omega

/-- The actual generated return and the created ledger refer to the same initialized buffer.
The fresh ledger is existentially chosen by `fown_init`; its epoch is exactly zero. -/
theorem fallocator_creation {ctx : Ptr} {B : FBuf} {q : Frac} {b cb : BlockId} {bs : Array Byte}
    (hs : bs.size = B.cap) (hA : B.A + B.ptr.off.toNat + B.cap < 2 ^ 64) (hp0 : 0 ≤ B.ptr.off)
    (hal : (B.cA + ctx.off.toNat) % 8 = 0) (hc0 : 0 ≤ ctx.off) (hb : B.ptr.block = some b)
    (hcb : ctx.block = some cb) :
    FTotalTriple (creationInput ctx B q b cb bs)
      (heap_FixedBufferAllocator_allocator ctx)
      (fun a => ⟪ a = (⟨ctx, ⟨some 5, 0⟩⟩ : mem_Allocator) ⟫ ⋆
        FAssn.ex fun γ => (finv ctx B γ 0).creationPost) := by
  fsym [fallocator_init, creation_upd]

/-- The initializer's original side conditions stay inside the exact creation precondition. -/
def creationPre (ctx : Ptr) (B : FBuf) : FAssn :=
  FAssn.ex fun (q : Frac) => FAssn.ex fun (b : BlockId) => FAssn.ex fun (cb : BlockId) =>
    FAssn.ex fun (bs : Array Byte) =>
    ⟪ bs.size = B.cap ∧ B.A + B.ptr.off.toNat + B.cap < 2 ^ 64 ∧ 0 ≤ B.ptr.off ∧
      (B.cA + ctx.off.toNat) % 8 = 0 ∧ 0 ≤ ctx.off ∧ B.ptr.block = some b ∧
      ctx.block = some cb ⟫ ⋆ creationInput ctx B q b cb bs

/-- Context and buffer are visible; only the initialized ledger and epoch are ghost results.
These roles alone do not establish admission at a client's actual fresh arguments. -/
def fallocSpec.creationParameters : FAllocCreationParameters := ⟨[0, 1], [2, 3]⟩

/-- Creation of the existing invariant family. The stronger preceding rule retains the actual
return and epoch-zero equation; this family projection supplies no admissibility companion. -/
theorem fallocSpec.creation (ctx : Ptr) (B : FBuf) :
    FTotalTriple (creationPre ctx B) (heap_FixedBufferAllocator_allocator ctx)
      (fun _ => FAssn.ex fun γ => FAssn.ex fun e => (finv ctx B γ e).creationPost) := by
  fsym [fallocator_creation]

end AllocFba.FBA
