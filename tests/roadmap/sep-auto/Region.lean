import ZigLean.Sep.Full.Auto
import ZigLean.Sep.Full.Region

/-!
# `fsym` with the region library (`ZigLean/Sep/Full/Region.lean`)

Library-only examples of the byte operations on regions that allocator wrappers run: the store
of a sentinel item and its read-back, `@memset(_, undefined)` of a whole region, `@memcpy`
between two separate regions, the pointer order (`ptrLe`) inside a region, and the `@memcpy`
aliasing check of `dupe` (`ptrLe(src + n, dst) or ptrLe(dst + n, src)`), whose panic is
unreachable by the memory fact `MemFacts.regions_apart` (`@[fsym_facts]`, plain `fsym`). The programs are written by hand in the
shape the translator generates.
-/

namespace SepAuto.Region

open Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto

variable (p q : Ptr) (A S A' S' : Nat) (K K' : BlockKind)

/-- Store a sentinel at item `n` and read it back. -/
def sentinel (n : BitVec 64) : MemM (BitVec 8) := do
  Zig.store 1 (p.elem 1 n) (7 : BitVec 8)
  Zig.load (BitVec 8) 1 (p.elem 1 n)

theorem sentinel_total (n : BitVec 64) (bs : Array Byte) (h : n.toNat < bs.size) :
    FTotalTriple (up (regionIn p A S K 1 bs)) (sentinel p n)
      (fun r => ⟪r = 7#8⟫ ⋆ up (regionIn p A S K 1
        (writeBytes bs (Enc.size (BitVec 8) * n.toNat) (Enc.encode 7#8)))) := by
  unfold sentinel
  fsym

/-- The same through a formed pointer, as generated code does it (bounds check, `ptrProject`). -/
def sentinelAt (n len : BitVec 64) : MemM (BitVec 8) := do
  let q ← Zig.checkIndex len n >>= fun _ => Zig.ptrProject p (·.elem 1 n)
  Zig.store 1 q (7 : BitVec 8)
  Zig.checkSentinelIndex len n
  Zig.load (BitVec 8) 1 q

theorem sentinelAt_total (n len : BitVec 64) (bs : Array Byte) (h : n.toNat < len.toNat)
    (hl : len.toNat = bs.size) :
    FTotalTriple (up (regionIn p A S K 1 bs)) (sentinelAt p n len)
      (fun r => ⟪r = 7#8⟫ ⋆ up (regionIn p A S K 1 (writeBytes bs n.toNat (Enc.encode 7#8)))) := by
  unfold sentinelAt
  fsym

/-- Every byte of a region becomes undefined. -/
theorem memsetUndef_total (n : BitVec 64) (bs : Array Byte) (h : n.toNat = bs.size) :
    FTotalTriple (up (regionIn p A S K 1 bs)) (Zig.memset (α := BitVec 8) 1 p n none)
      (fun _ => up (regionIn p A S K 1 (Array.replicate n.toNat .undef))) := by
  fsym

/-- A whole region copied onto a separate one of the same size. -/
theorem memcpy_total (n : BitVec 64) (bd bs : Array Byte) (h1 : n.toNat = bd.size)
    (h2 : n.toNat = bs.size) :
    FTotalTriple (up (regionIn q A' S' K' 1 bs) ⋆ up (regionIn p A S K 1 bd))
      (Zig.memcpy 1 1 1 p q n n)
      (fun _ => up (regionIn p A S K 1 bs) ⋆ up (regionIn q A' S' K' 1 bs)) := by
  fsym

/-- A pointer into a region is not below the region's start. -/
theorem ptrLe_total (n : BitVec 64) (bs : Array Byte) (hpos : 0 < bs.size) :
    FTotalTriple (up (regionIn p A S K 1 bs)) (Zig.ptrLe p (p.elem 1 n))
      (fun r => ⟪r = true⟫ ⋆ up (regionIn p A S K 1 bs)) := by
  fsym

/-- The aliasing check of a `@memcpy` between two separate regions (`dupe`). -/
def aliasCheck (n : BitVec 64) : MemM Unit := do
  let a ← Zig.ptrLe (q.elem 1 n) p
  let b ← Zig.ptrLe (p.elem 1 n) q
  if a || b then pure () else throw .panic

/-- Its panic is unreachable: two separately owned regions lie apart (a memory fact of the pair
of regions, `@[fsym_facts] MemFacts.regions_apart`, which `fsym` adds when the panic needs it). -/
theorem aliasCheck_total (n : BitVec 64) (bd bs : Array Byte) (h1 : n.toNat = bd.size)
    (h2 : n.toNat = bs.size) (hpos : 0 < n.toNat) :
    FTotalTriple (up (regionIn p A S K 1 bd) ⋆ up (regionIn q A' S' K' 1 bs)) (aliasCheck p q n)
      (fun _ => up (regionIn p A S K 1 bd) ⋆ up (regionIn q A' S' K' 1 bs)) := by
  unfold aliasCheck
  fsym

/-- The memory fact by hand, in any logic (`MemFacts.pre`). -/
theorem aliasCheck_pre (n : BitVec 64) (bd bs : Array Byte) (h1 : n.toNat = bd.size)
    (h2 : n.toNat = bs.size) (hpos : 0 < n.toNat) :
    FTotalTriple (up (regionIn p A S K 1 bd) ⋆ up (regionIn q A' S' K' 1 bs)) (aliasCheck p q n)
      (fun _ => up (regionIn p A S K 1 bd) ⋆ up (regionIn q A' S' K' 1 bs)) := by
  refine MemFacts.pre FLogic.total MemFacts.regions_apart fun _ => ?_
  unfold aliasCheck
  fsym

set_option linter.unusedVariables false

/-- Rejected: a region checked against itself overlaps, so the panic is reachable (the facts of
a pair are about two separately owned atoms). -/
example (n : BitVec 64) (bd : Array Byte) (h1 : n.toNat = bd.size) (hpos : 0 < n.toNat) : True := by
  fail_if_success
    have : FTotalTriple (up (regionIn p A S K 1 bd)) (aliasCheck p p n)
        (fun _ => up (regionIn p A S K 1 bd)) := by
      unfold aliasCheck
      fsym
  trivial

/-- A copy needs the source: one region alone is not copied onto itself. -/
example (n : BitVec 64) (bd : Array Byte) (h1 : n.toNat = bd.size) (hpos : 0 < n.toNat) : True := by
  fail_if_success
    have : FTotalTriple (up (regionIn p A S K 1 bd)) (Zig.memcpy 1 1 1 p p n n)
        (fun _ => up (regionIn p A S K 1 bd)) := by
      fsym
  trivial

/-- A read-back is the stored value, not another. -/
example (n : BitVec 64) (bs : Array Byte) (h : n.toNat < bs.size) : True := by
  fail_if_success
    have : FTotalTriple (up (regionIn p A S K 1 bs)) (sentinel p n)
        (fun r => ⟪r = 8#8⟫ ⋆ up (regionIn p A S K 1
          (writeBytes bs (Enc.size (BitVec 8) * n.toNat) (Enc.encode 7#8)))) := by
      unfold sentinel
      fsym
  trivial

end SepAuto.Region
