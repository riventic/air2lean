import AllocFba.Wrappers
import ZigLean.Sep.Full.Local

open Zig Zig.Full Zig.Full.FAssn AllocFba AllocFba.Gen AllocFba.FBA

abbrev bufp : Ptr := ⟨some 0, 0⟩

def B (A₀ Ac : Nat) : FBuf := ⟨bufp, 12, A₀, 16, .global, Ac⟩

example (s1 : Ptr) (A₀ Ac : Nat) (b : BlockId) (h0 : s1.off = 0) (hb : s1.block = some b) (hAc : Ac % 8 = 0)
  (hsz : (Enc.encode (⟨0, ⟨bufp, 12⟩⟩ : heap_FixedBufferAllocator)).size = 24) :
  FTotalTriple (up (bytesAt s1 Ac 24 .stack (Array.replicate 24 .undef)) ⋆ bext b 24 .stack)
    (Zig.store (α := heap_FixedBufferAllocator) 8 s1 ⟨0, ⟨bufp, 12⟩⟩)
    (fun _ => up (pts s1 8 (⟨0, ⟨bufp, 12⟩⟩ : heap_FixedBufferAllocator)) ⋆ bext b 24 .stack) := by
  fsym

example (s1 : Ptr) (A₀ Ac : Nat) :
  EUpd (up (pts s1 8 (⟨0, ⟨bufp, 12⟩⟩ : heap_FixedBufferAllocator))) (wEnd s1 0 ⋆ wBuf s1 (B A₀ Ac)) := by
  unfold wEnd wBuf
  fsym_entail
