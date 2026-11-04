import ZigLean.Sep.Full.Auto

/-!
# `fsym` on variable pointers (`docs/proof-automation.md`)

Pointers whose block is not in the context: `fsym` reads the block, the offset and the alignment
of a pointer off the precondition's atoms that own memory at it (`@[fsym_facts]`), when a rule's
side goal or an `if` needs them; a pointer kept in an optional field of the locals is found by
splitting the field (its equation replaces the field in the facts and in the precondition).
Facts that need the memory or a pair of atoms (`MemFacts`: a token's grant in its authority's
map) close an unreachable panic. The programs are written by hand in the shape the translator
generates.
-/

namespace SepAuto.Facts

open Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto

/-- `@intFromPtr` of a pointer and its alignment check (`std.mem.isAligned`). -/
def checkAligned (p : Ptr) : MemM Unit := do
  let a ← Zig.ptrAddr p
  if a % 8 = 0 then pure () else throw .panic

/-- The address of a variable pointer into an owned, 8-aligned region whose block the context
does not know: the region gives the block (for `ptrAddr`), and the alignment decides the check. -/
theorem aligned (p : Ptr) (A S : Nat) (K : BlockKind) (bs : Array Byte) (hs : 0 < bs.size) :
    FTotalTriple (up (regionIn p A S K 8 bs)) (checkAligned p) (fun _ => up (regionIn p A S K 8 bs)) := by
  unfold checkAligned
  fsym

/-- A word field at offset 8 of a node at a variable pointer: the pointer formation needs the
node's block and a nonnegative offset, both from the owned words. -/
def secondField (p : Ptr) : MemM (BitVec 64) := do
  let q ← Zig.ptrProject p (·.add 8)
  Zig.load (BitVec 64) 8 q

theorem second_field (p : Ptr) (v w : BitVec 64) :
    FTotalTriple (up (pts p 8 v) ⋆ up (pts (p.add 8) 8 w)) (secondField p)
      (fun r => ⟪r = w⟫ ⋆ up (pts p 8 v) ⋆ up (pts (p.add 8) 8 w)) := by
  unfold secondField
  fsym

/-- The bytes of a struct of `n` pointer fields, each `q` (a user definition by `Enc.fields`, as
a generated struct's encoding). -/
def ptrFields (q : Ptr) (n : Nat) : Array Byte :=
  Enc.fields (8 * n) ((List.range n).map fun i => (8 * i, Enc.encode q))

set_option linter.unusedVariables false in
/-- A fact of the context about concrete bytes (a field read back from a struct's bytes, as the
arena's child allocator from the arena struct) is no block fact: the block search of the pointer
formation does not unify it with `p.block = some ?b`, which evaluated the bytes (ledger #55). -/
theorem second_field_bytes_fact (p q : Ptr) (v w : BitVec 64)
    (hd : (Enc.decodeAt (ptrFields q 64) 8 : Result Ptr) = pure q) :
    FTotalTriple (up (pts p 8 v) ⋆ up (pts (p.add 8) 8 w)) (secondField p)
      (fun r => ⟪r = w⟫ ⋆ up (pts p 8 v) ⋆ up (pts (p.add 8) 8 w)) := by
  unfold secondField
  fsym

/-- The locals of a generated function with an optional pointer. -/
structure Locals where
  cur : Option Ptr

/-- `if (s.cur) |p| p.* else 0`, as generated (`.?` after the test). -/
def firstWord (s : Locals) : MemM (BitVec 64) := do
  if s.cur.isSome then
    let p ← StateT.lift (optPayload s.cur)
    Zig.load (BitVec 64) 8 p
  else pure 0

/-- The precondition matches on the field: the test splits it. -/
theorem first_word (s : Locals) (v : BitVec 64) :
    FTotalTriple (match s.cur with | none => emp | some p => up (pts p 8 v)) (firstWord s)
      (fun r => match s.cur with | none => ⟪r = 0⟫ | some p => ⟪r = v⟫ ⋆ up (pts p 8 v)) := by
  unfold firstWord
  fsym

/-- The state of an allocator with grants: a first node, if any, and the grant map (which is
empty without a first node). -/
structure Grants where
  first : Option Ptr
  M : GMap

/-- `const node = self.first orelse unreachable` of a `free` that holds a grant's token. -/
def firstNode (w : Grants) : MemM Unit :=
  if w.first.isSome then pure () else throw .panic

/-- The panic is unreachable from a pair of atoms (`MemFacts`, `facts_gfrag`): a token names a
grant of its authority's map, and the map is empty without a first node. The test `isSome`
becomes `w.first = none`, which reduces the `match`, whose fact `w.M = GMap.empty` replaces the
field. -/
theorem first_node (w : Grants) (γ e i : Nat) (g : GRegion) :
    FTotalTriple (⟪match w.first with | none => w.M = GMap.empty | some _ => True⟫ ⋆
        gauthP γ e w.M none ⋆ gfrag γ e i g) (firstNode w)
      (fun _ => gauthP γ e w.M none ⋆ gfrag γ e i g) := by
  unfold firstNode
  fsym

set_option linter.unusedVariables false in
/-- Rejected: without the token the panic is reachable. -/
example (w : Grants) (γ e : Nat) : True := by
  fail_if_success
    have : FTotalTriple (⟪match w.first with | none => w.M = GMap.empty | some _ => True⟫ ⋆
        gauthP γ e w.M none) (firstNode w) (fun _ => gauthP γ e w.M none) := by
      unfold firstNode
      fsym
  trivial

/-- The block of a pointer value (`⟨some b, o⟩`, a mapping's start) is its first component, by
evaluation, also with no fact about it: the planner joins two regions of it. -/
theorem block_of_value (b : BlockId) (A S : Nat) (K : BlockKind) (bs cs : Array Byte)
    (hb : bs.size = 8) :
    EUpd (up (regionIn ⟨some b, 0⟩ A S K 8 bs) ⋆ up (regionIn (Ptr.add ⟨some b, 0⟩ 8) A S K 8 cs))
      (up (regionIn ⟨some b, 0⟩ A S K 8 (bs ++ cs))) := by
  fsym_entail

/-- **A conjunction split after its left conjunct substituted a local** that the right one
mentions (a token's facts `A = B.A ∧ S = B.S ∧ …`): the substitution reintroduces the right
conjunct as a new local, which is still split, so its `k = .global` fixes the kind. -/
theorem conj_after_subst (T : BlockKind → FAssn) (a b : Nat) (k : BlockKind) (c : MemM Unit)
    (rule : FTotalTriple (T .global) c (fun _ => T .global)) :
    FTotalTriple (⟪a = b ∧ (k = .global ∧ a + b = 8)⟫ ⋆ T k) c (fun _ => T k) := by
  fsym [rule]

/-- A buffer record at a global pointer (`⟨some 0, 0⟩`), as a client names its allocator's
buffer. -/
structure Buf where
  ptr : Ptr
  cap : Nat

abbrev gbuf (n : Nat) : Buf := ⟨⟨some 0, 0⟩, n⟩

/-- A block variable of a pointer whose block is a value is that block: the invariant's share of
`b` with `(gbuf n).ptr.block = some b` meets a rule at block `0` (an allocator's granted region,
whose share the planner opens at the evaluated block). -/
theorem value_block (n : Nat) (q : Frac) (c : MemM Unit)
    (rule : FTotalTriple (bshare 0 q n) c (fun _ => bshare 0 q n)) :
    FTotalTriple (FAssn.ex fun b => ⟪(gbuf n).ptr.block = some b⟫ ⋆ bshare b q n) c
      (fun _ => bshare 0 q n) := by
  fsym [rule]

/-- The same through a fact between two pointers' blocks: a grant at `p` in the buffer (its
token's `p.block = (gbuf n).ptr.block`) has its share at block `0`. -/
theorem value_block_linked (p : Ptr) (n : Nat) (q : Frac) (c : MemM Unit)
    (hp : p.block = (gbuf n).ptr.block)
    (rule : FTotalTriple (bshare 0 q n) c (fun _ => bshare 0 q n)) :
    FTotalTriple (FAssn.ex fun b => ⟪p.block = some b⟫ ⋆ bshare b q n) c
      (fun _ => bshare 0 q n) := by
  fsym [rule]

/-- The same from a fact `p.block = some 0` (no evaluation). -/
theorem value_block_fact (p : Ptr) (n : Nat) (q : Frac) (c : MemM Unit) (hp : p.block = some 0)
    (rule : FTotalTriple (bshare 0 q n) c (fun _ => bshare 0 q n)) :
    FTotalTriple (FAssn.ex fun b => ⟪p.block = some b⟫ ⋆ bshare b q n) c
      (fun _ => bshare 0 q n) := by
  fsym [rule]

/-- The same from `some 0 = some b` of a block variable `b` (one declared at `BlockId`, no block
fact needed: `isBlockVar`). -/
theorem value_block_eq (b : BlockId) (n : Nat) (q : Frac) (c : MemM Unit) (hb : some 0 = some b)
    (rule : FTotalTriple (bshare 0 q n) c (fun _ => bshare 0 q n)) :
    FTotalTriple (bshare b q n) c (fun _ => bshare 0 q n) := by
  fsym [rule]

/-- The same from `some b = some 0`. -/
theorem value_block_eq_symm (p : Ptr) (b : BlockId) (n : Nat) (q : Frac) (c : MemM Unit)
    (hp : p.block = some b) (hb : some b = some 0)
    (rule : FTotalTriple (bshare 0 q n) c (fun _ => bshare 0 q n)) :
    FTotalTriple (bshare b q n) c (fun _ => bshare 0 q n) := by
  fsym [rule]

/-- A caller's term that names the substituted block variable takes its value (the
substitution is recorded, `substRecorded`). -/
theorem value_block_caller_term (b : BlockId) (n : Nat) (q : Frac) (c : MemM Unit)
    (hb : (gbuf n).ptr.block = some b)
    (rule : FTotalTriple (bshare b q n) c (fun _ => bshare b q n)) :
    FTotalTriple (bshare b q n) c (fun _ => bshare 0 q n) := by
  fsym [rule]

/-- Two block variables of one block (`hxy`), one of them equal to a value: both are that value
(one variable per block first, then its value). -/
theorem value_block_chain (x y : Ptr) (b1 b2 : BlockId) (n : Nat) (q : Frac) (c : MemM Unit)
    (h1 : x.block = some b1) (h2 : y.block = some b2) (hxy : x.block = y.block)
    (hb : some 0 = some b1)
    (rule : FTotalTriple (bshare 0 q n) c (fun _ => bshare 0 q n)) :
    FTotalTriple (bshare b2 q n) c (fun _ => bshare 0 q n) := by
  fsym [rule]

/-- The block of a pointer formed from a base whose block is a fact (`Ptr.add`: of one base). -/
theorem value_block_add (p : Ptr) (b : BlockId) (n : Nat) (q : Frac) (c : MemM Unit)
    (hp : p.block = some 0) (h : (p.add 4).block = some b)
    (rule : FTotalTriple (bshare 0 q n) c (fun _ => bshare 0 q n)) :
    FTotalTriple (bshare b q n) c (fun _ => bshare 0 q n) := by
  fsym [rule]

end SepAuto.Facts
