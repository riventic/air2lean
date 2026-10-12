import ZigLean.Sep.Full.Auto

/-!
# `fsym` providers over the whole precondition (`docs/proof-automation.md` §Providers)

A rule's provider goal (`AddrOf`, `Reaches`, `Live`, `Active`) is proved by an atom lemma on one
of the precondition's parts, or by a lemma about the whole precondition whose hypotheses are
solved in turn: a part found by `Within` (`withinCands`), another provider, a block, arithmetic.
The cases come from the arena allocator's `free` (`tests/roadmap/alloc-arena`):

* the end of a node's buffer, formed from a node pointer whose block reaches the node's end only
  through a **tagged** share (the buffer's tail may be empty), which counts while its tag is
  active: a ledger at its epoch (`gauthP`, `Active.gauthP`) or an allocator's own state
  (`FAllocInv.own`, `Active.allocOwn`);
* pointer `==` of pointers into two live blocks that may differ (`ptrEqAddr_live`), with the
  comparison's Boolean result split into facts (`b = b'` substitutes the block);
* two regions of one block apart by offsets (`facts_regions_block`, block premises from the
  context);
* `Within X P` goals of `fsym_entail` (the arena's former `within` tactic).

The programs are written by hand in the shape the translator generates.
-/

namespace SepAuto.Providers

open Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto

/-- The end of a node's used buffer: the node's header is 24 bytes, `ei` bytes are used. -/
def bufEnd (N : Ptr) (ei : BitVec 64) : MemM Ptr := Zig.ptrProject (N.add 24) (·.elem 1 ei)

/-- The node's block reaches its end by a share tagged with a ledger's epoch; the ledger's
authority (under the root) keeps the tag active. The tail region alone does not reach the end
when it is empty. -/
theorem buf_end_ledger (N : Ptr) (b : BlockId) (ei : BitVec 64) (sz A S γ e : Nat) (K : BlockKind)
    (q : Frac) (M : GMap) (tail : Array Byte) (hb : N.block = some b) (h0 : 0 ≤ N.off)
    (hei : 24 + ei.toNat ≤ sz) :
    FTotalTriple (up (regionIn (N.add (24 + ei.toNat)) A S K 1 tail) ⋆
        bshare b q (N.off.toNat + sz) (some (γ, e)) ⋆ gauthP γ e M none) (bufEnd N ei)
      (fun _ => up (regionIn (N.add (24 + ei.toNat)) A S K 1 tail) ⋆
        bshare b q (N.off.toNat + sz) (some (γ, e)) ⋆ gauthP γ e M none) := by
  unfold bufEnd
  fsym

/-- The same with the share tagged by an allocator's invariant, active by its own state. -/
theorem buf_end_alloc (I : FAllocInv) (N : Ptr) (b : BlockId) (ei : BitVec 64) (sz : Nat) (q : Frac)
    (hb : N.block = some b) (h0 : 0 ≤ N.off) (hei : 24 + ei.toNat ≤ sz) :
    FTotalTriple (I.own ⋆ bshare b q (N.off.toNat + sz) I.tag) (bufEnd N ei)
      (fun _ => I.own ⋆ bshare b q (N.off.toNat + sz) I.tag) := by
  unfold bufEnd
  fsym

set_option linter.unusedVariables false in
/-- Rejected: without the ledger the tag may be inactive, and the share gives nothing. -/
example (N : Ptr) (b : BlockId) (ei : BitVec 64) (sz γ e : Nat) (q : Frac) (hb : N.block = some b)
    (h0 : 0 ≤ N.off) (hei : 24 + ei.toNat ≤ sz) : True := by
  fail_if_success
    have : FTotalTriple (bshare b q (N.off.toNat + sz) (some (γ, e))) (bufEnd N ei)
        (fun _ => bshare b q (N.off.toNat + sz) (some (γ, e))) := by
      unfold bufEnd
      fsym
  trivial

/-- `free`'s test whether a slice is the last allocation: the buffer's end `p + n` against the
slice's end `q + m`, in blocks that may differ; when they are equal, a second comparison in the
(then known) one block must hold. -/
def lastTest (p q : Ptr) (n m : BitVec 64) : MemM (BitVec 8) := do
  let e ← Zig.ptrProject p (·.elem 1 n)
  let f ← Zig.ptrProject q (·.elem 1 m)
  let eq ← Zig.ptrEqAddr e f
  if eq = true then do
    let d ← Zig.ptrEqAddr f e
    if d = true then pure 1 else throw .panic
  else pure 0

theorem last_test (p q : Ptr) (n m : BitVec 64) (A S A' S' : Nat) (K K' : BlockKind)
    (bs cs : Array Byte) (hn : n.toNat = bs.size) (hm : m.toNat = cs.size) (hpos : 0 < bs.size)
    (hpos' : 0 < cs.size) :
    FTotalTriple (up (regionIn p A S K 1 bs) ⋆ up (regionIn q A' S' K' 1 cs)) (lastTest p q n m)
      (fun _ => up (regionIn p A S K 1 bs) ⋆ up (regionIn q A' S' K' 1 cs)) := by
  unfold lastTest
  fsym

set_option linter.unusedVariables false in
/-- Rejected: a start against an end may be equal across two blocks (adjacent blocks), so the
comparison is not decided by the blocks and offsets. -/
example (p q : Ptr) (n : BitVec 64) (A S A' S' : Nat) (K K' : BlockKind) (bs cs : Array Byte)
    (hn : n.toNat = bs.size) (hpos : 0 < bs.size) (hpos' : 0 < cs.size) : True := by
  fail_if_success
    have : FTotalTriple (up (regionIn p A S K 1 bs) ⋆ up (regionIn q A' S' K' 1 cs))
        (do let e ← Zig.ptrProject p (·.elem 1 n); Zig.ptrEqAddr e q)
        (fun _ => up (regionIn p A S K 1 bs) ⋆ up (regionIn q A' S' K' 1 cs)) := by
      fsym
  trivial

/-- An offset test that holds because two regions of one block do not overlap. -/
def apartTest (p q : Ptr) (n m : Nat) : MemM Unit :=
  if p.off.toNat + n ≤ q.off.toNat ∨ q.off.toNat + m ≤ p.off.toNat then pure () else throw .panic

theorem apart_test (p q : Ptr) (b : BlockId) (A S A' S' : Nat) (K K' : BlockKind) (bs cs : Array Byte)
    (hp : p.block = some b) (hq : q.block = some b) (hpos : 0 < bs.size) (hpos' : 0 < cs.size) :
    FTotalTriple (up (regionIn p A S K 1 bs) ⋆ up (regionIn q A' S' K' 1 cs))
      (apartTest p q bs.size cs.size)
      (fun _ => up (regionIn p A S K 1 bs) ⋆ up (regionIn q A' S' K' 1 cs)) := by
  unfold apartTest
  fsym

/-- Two words at `p`, a definition of an assertion. -/
def two (p : Ptr) (v w : BitVec 64) : FAssn := up (pts p 8 v) ⋆ up (pts (p.add 8) 8 w)

/-- A part behind a definition and `emp`. -/
theorem within_def (p : Ptr) (v w : BitVec 64) (R : FAssn) :
    Within (up (pts (p.add 8) 8 w)) (emp ⋆ two p v w ⋆ R) := by
  fsym_entail

/-- The definition itself as a part. -/
theorem within_whole (p : Ptr) (v w : BitVec 64) (R : FAssn) : Within (two p v w) (R ⋆ two p v w) := by
  fsym_entail

set_option linter.unusedVariables false in
/-- Rejected: not a part. -/
example (p : Ptr) (v w : BitVec 64) (R : FAssn) : True := by
  fail_if_success
    have : Within (up (pts (p.add 16) 8 w)) (two p v w ⋆ R) := by fsym_entail
  trivial

end SepAuto.Providers
