import ZigLean.Mem.Enc

/-! Kernel regressions for writes into large blocks. These use the actual memory
operations; no native evaluator or raised recursion limit participates. -/

namespace SepAuto.KernelBytes
open Zig

def writePage (n : Nat) (v : Option (BitVec 8)) : MemM Bool := do
  let p ← Zig.alloc .heap n 8
  Zig.memset (α := BitVec 8) 1 p 16 v
  Zig.store (α := BitVec 32) 4 p 7
  pure true

def succeeded {α : Type} (r : Result (α × Mem)) : Bool :=
  match r.run with | some (.ok _) => true | _ => false

theorem undefined_page : succeeded ((writePage 4096 none).run {}) = true := by
  decide +kernel

theorem zero_page : succeeded ((writePage 4096 (some 0)).run {}) = true := by
  decide +kernel

theorem large_page : succeeded ((writePage 16384 none).run {}) = true := by
  decide +kernel

theorem suffix_preserved :
    (writeBytes (Array.replicate 4096 Byte.undef) 0 #[.int 7])[4095]? = some .undef := by
  decide +kernel

theorem end_write :
    (writeBytes (Array.replicate 4096 Byte.undef) 4092 #[.int 7, .int 0, .int 0, .int 0]).size =
      4096 := by
  decide +kernel

end SepAuto.KernelBytes
