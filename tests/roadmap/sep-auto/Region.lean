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

/-- A grant: its bytes, as a region (the child allocator's `free` precondition). -/
def Granted (p : Ptr) (bs : Array Byte) : FAssn :=
  FAssn.ex fun A => FAssn.ex fun S => FAssn.ex fun K =>
    up (regionIn p A S K 8 bs) ⋆ ⟪bs.size = 40⟫

/-- An allocator's `free` (a stand-in that keeps what it is given). -/
@[irreducible] def giveBack (_p : Ptr) : MemM Unit := pure ()

theorem giveBack_spec {p : Ptr} {bs : Array Byte} :
    FTotalTriple (Granted p bs) (giveBack p) (fun _ => Granted p bs) := by
  unfold giveBack; exact FTotalTriple.ret (Q := fun _ => _) ()

set_option maxHeartbeats 600000 in
/-- **A node given back in a large state** (ledger #60, the arena's `free` of a node among the
other nodes): its words viewed and joined into the grant, next to six regions of three other
blocks. Each pair of regions is apart (`regions_apart`, a disjunction): a planner's probe that
the plain facts refute does not search their cases, the facts of all pairs are added at once,
and pointers whose offsets differ are not compared by a tactic. Over 4M heartbeats before,
about 300k now. -/
theorem free_large (r u : Ptr) (b : BlockId) (sz ei : BitVec 64) (nxt : Option Ptr)
    (buf c1 c2 c3 c4 c5 c6 : Array Byte) (hb : p.block = some b) (hal : (A + p.off.toNat) % 8 = 0)
    (hbuf : buf.size = 16) (h1 : c1.size = 16) (h2 : c2.size = 16) (h3 : c3.size = 16)
    (h4 : c4.size = 24) (h5 : c5.size = 24) (h6 : c6.size = 24) :
    FTotalTriple (apts p sz ⋆ apts (p.add 8) ei ⋆ up (regionIn (p.add 16) A S K 8 (Enc.encode nxt)) ⋆
        up (regionIn (p.add 24) A S K 1 buf) ⋆ up (regionIn q A S K 8 c1) ⋆ up (regionIn r A S K 8 c2) ⋆
        up (regionIn u A S K 8 c3) ⋆ up (regionIn (q.add 24) A S K 8 c4) ⋆
        up (regionIn (r.add 24) A S K 8 c5) ⋆ up (regionIn (u.add 24) A S K 8 c6))
      (giveBack p) (fun _ => (FAssn.ex fun bs => Granted p bs) ⋆ up (regionIn q A S K 8 c1) ⋆
        up (regionIn r A S K 8 c2) ⋆ up (regionIn u A S K 8 c3) ⋆ up (regionIn (q.add 24) A S K 8 c4) ⋆
        up (regionIn (r.add 24) A S K 8 c5) ⋆ up (regionIn (u.add 24) A S K 8 c6)) := by
  fsym [giveBack_spec]

end SepAuto.Region
