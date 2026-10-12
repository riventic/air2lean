import ZigLean.Sep.Full.Init

/-!
# The memory at program start (`ZigLean/Sep/Full/Init.lean`), library-only

Two globals (a `var` and a `const`): the start memory is a `Mem.FSeq` memory under every
placement, and it holds `globals` with the empty frame.
-/

namespace OneLogic.Init

open Zig Zig.Full

def gs : List (Array Byte × Nat × BlockKind) :=
  [(Enc.encode (7 : BitVec 32), 4, .global), (Enc.encode (1 : BitVec 8), 1, .constGlobal)]

theorem start_fseq (σ : Placement) : (Mem.ofGlobals σ gs).FSeq :=
  Mem.init_fseq σ gs (by decide)

theorem start_holds (σ : Placement) :
    Holds (Mem.ofGlobals σ gs) (initRes σ gs) ⟨FHeap.empty, Know.none, Ghost.unit⟩ ∧
      globals gs (initRes σ gs) :=
  initRes_holds σ gs (by decide)

end OneLogic.Init
