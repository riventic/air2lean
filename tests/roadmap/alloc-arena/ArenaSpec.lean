import AllocArena.ArenaLinux
import ZigLean.Sep.AllocSpec.Region
import ZigLean.Sep.AllocSpec.Ops
import ZigLean.Sep.Full.AllocSpec
import ZigLean.Sep.Full.Conc
import ZigLean.Sep.Full.AtomicRules
import ZigLean.Sep.Full.Ghost
import ZigLean.Range

/-!
# The translated `ArenaAllocator`'s `free`, `resize` and `remap` against `FAllocSpec`

`free_spec`, `resize_spec`, `remap_spec`: the entries of the translated `std.heap.ArenaAllocator`
(Zig 0.16.0, x86_64-linux, `AllocArena/ArenaLinux.lean`) meet `FAllocSpec`'s contracts for the
arena invariant `inv CI γ e ctx` below, read in the caller's thread (`CTriple`, `Sched.soloRun`),
from the generated code only. No model of the arena is used. `alloc` is not here: the stock arena
does not meet `FAllocSpec`'s `alloc` field for any child (O-E, O-B in `docs/alloc-arena.md`).

**The invariant** `own CI γ e ctx` (for a child allocator invariant `CI`, ghost name `γ`, epoch `e`):

* the arena struct at `ctx`: the child allocator (16 bytes, not read here), `used_list` and
  `free_list` as pointer-valued atomic words (`aptsE`);
* the ghost authority `gauth γ e M`: the grant map `M` of epoch `e`, grant id ↦ region
  (`docs/sep-full-state.md` §Ghost state);
* the first node of `used_list`, if any (`FirstPart`): its header words (`size` and `end_index`
  atomic, `next` plain), the unused tail of its buffer (from `end_index` on), and the child's
  token for the node; the other used nodes and the free list (`Chain`): headers and tokens, the
  free nodes with their whole buffers;
* the child's state `CI.own`, and `Junk`: bytes that frees which were not the last allocation
  leaked back (any bytes; the arena never touches them until `reset`).

With no first node, `M` is empty. A token for the slice `(p, n)` is `gfrag γ e i (p, n)` for some
grant id `i`: it names exactly that region, so a token of the current epoch shows `M i = some (p,
n)` (`gfrag_mem`), hence a first node: **O-A is excluded by ghost state**, not by a premise, and a
`free` of a slice that this arena did not grant has no token: a permission violation. A token of
an older epoch (after `reset`) is stale: it belongs to `inv … e'` for `e' < e`, whose `own` needs
the authority of epoch `e'`, which no longer exists.

**`free`** loads the first node, compares `buf + end_index` with the slice's end by address
(`ptrEqAddr`), and on a match moves `end_index` back by a strong `cmpxchg`. The comparison is
decided by ownership alone (O-F): a slice of another block lies at disjoint addresses
(`FTriple.apart`, `Mem.LiveDisjoint` in `Mem.FSeq`), and a slice of the node's block that ends at
`buf + end_index` lies past the header, which the arena owns. On a match the slice's bytes rejoin
the tail; otherwise (a grant that is not the last one) they become junk. Either way the grant is
retired (`Upd.retire`).

**`resize`** has the same prefix. A slice that is not the first node's last one only shrinks (the
cut bytes become junk); the last one moves `end_index` back (a shrink: the cut bytes rejoin the
tail) or forward into the tail when it has room (`Node.loadBuf` reads the `size` word:
`FTriple.atomicLoadAs`, `toInt_ofBits`). A successful resize re-points the grant at the new length
(`Upd.reassign`). **`remap`** is `resize` and returns `memory.ptr`.

**O-E** (`ArenaObstruction.oob_free_illegal`): the invariant keeps `end_index` within the first
node's buffer (`OV.Facts`: `24 + ei ≤ sz`). A failed `alloc` leaves it past the buffer, so the reachable
states this specification covers end at the first failed `alloc`.
-/

namespace AllocArena.ArenaSpec

open Zig Zig.Region Zig.Full Zig.Full.FAssn AllocArena.ArenaLinux

/-! ## Owned cells -/

/-- `P` owns byte `x` of block `b`, whose cell records address `A`, size `S` and kind `K`. -/
def Owns (b x : Nat) (A S : Nat) (K : BlockKind) (P : FAssn) : Prop :=
  ∀ r, P r → ∃ fc, r.heap (b, x) = some fc ∧ fc.cell.addr = A ∧ fc.cell.size = S ∧ fc.cell.kind = K

theorem Owns.sepL {b x A S K} {P R : FAssn} (h : Owns b x A S K P) : Owns b x A S K (P ⋆ R) := by
  rintro _ ⟨r₁, r₂, hd, rfl, h1, -⟩
  obtain ⟨fc, hx, e⟩ := h r₁ h1
  exact ⟨fc, by show (r₁.heap (b, x)).or _ = _; rw [hx]; rfl, e⟩

theorem Owns.sepR {b x A S K} {P R : FAssn} (h : Owns b x A S K P) : Owns b x A S K (R ⋆ P) :=
  fun r hr => (Owns.sepL h) r (sep_comm hr)

/-- Byte `i` of a `regionIn` is owned. -/
theorem Owns.region {p : Ptr} {b : BlockId} {A S : Nat} {K : BlockKind} {a : Nat} {bs : Array Byte}
    (hb : p.block = some b) {i : Nat} (hi : i < bs.size) :
    Owns b (p.off.toNat + i) A S K (up (regionIn p A S K a bs)) := by
  rintro r ⟨⟨-, -, b', hb', -, hl⟩, -⟩
  rw [hb] at hb'; cases hb'
  have := hl (b, p.off.toNat + i)
  simp only [FHeap.erase] at this
  rw [if_pos (by simp only [true_and]; omega)] at this
  cases e : r.heap (b, p.off.toNat + i) with
  | none => rw [e] at this; cases this
  | some fc =>
    rw [e] at this
    simp only [Option.map_some, Option.some.injEq] at this
    exact ⟨fc, rfl, by rw [this], by rw [this], by rw [this]⟩

/-- An owned cell is a cell of a live block of the memory, past the byte, with that block's
address, size and kind. -/
theorem Owns.block {b x A S K} {P : FAssn} (h : Owns b x A S K P) {m : Mem} {r rF : Res}
    (hh : Holds m r rF) (hp : P r) : ∃ blk, m.blocks[b]? = some blk ∧ blk.live = true ∧
      x < blk.bytes.size ∧ blk.addr = A ∧ blk.bytes.size = S ∧ blk.kind = K := by
  obtain ⟨fc, hx, rfl, rfl, rfl⟩ := h r hp
  obtain ⟨blk, hb, hl, hx', he⟩ := Mem.heap_some (hh.cell hx)
  rw [he]; exact ⟨blk, hb, hl, hx', rfl, rfl, rfl⟩

/-- Owned cells of two different blocks lie at disjoint addresses (`Holds.apart`). -/
theorem Owns.apart {b x A S K b' x' A' S' K'} {P : FAssn} (h : Owns b x A S K P)
    (h' : Owns b' x' A' S' K' P) (hbb : b ≠ b') {m : Mem} {r rF : Res} (hh : Holds m r rF)
    (hp : P r) (hs : m.FSeq) : A + S ≤ A' ∨ A' + S' ≤ A := by
  obtain ⟨fc, hx, rfl, rfl, -⟩ := h r hp
  obtain ⟨fc', hx', rfl, rfl, -⟩ := h' r hp
  exact hh.apart hs hbb hx hx'

/-- Two regions held separately in one block do not overlap. -/
theorem region_apart {p q : Ptr} {b : BlockId} {A S A₂ S₂ : Nat} {K K₂ : BlockKind} {a a₂ : Nat}
    {bs bs₂ : Array Byte} {r : Res} (hp : p.block = some b) (hq : q.block = some b)
    (hn : 0 < bs.size) (hn₂ : 0 < bs₂.size)
    (h : (up (regionIn p A S K a bs) ⋆ up (regionIn q A₂ S₂ K₂ a₂ bs₂)) r) :
    p.off.toNat + bs.size ≤ q.off.toNat ∨ q.off.toNat + bs₂.size ≤ p.off.toNat := by
  obtain ⟨r₁, r₂, hd, rfl, h1, h2⟩ := h
  refine Classical.byContradiction fun hc => ?_
  obtain ⟨x, hx1, hx2⟩ : ∃ x, (p.off.toNat ≤ x ∧ x < p.off.toNat + bs.size) ∧
      (q.off.toNat ≤ x ∧ x < q.off.toNat + bs₂.size) :=
    ⟨Nat.max p.off.toNat q.off.toNat, by simp only [Nat.max_def]; split <;> omega,
      by simp only [Nat.max_def]; split <;> omega⟩
  obtain ⟨f1, e1, -⟩ := Owns.region (a := a) (A := A) (S := S) (K := K) hp
    (i := x - p.off.toNat) (by omega) r₁ h1
  obtain ⟨f2, e2, -⟩ := Owns.region (a := a₂) (A := A₂) (S := S₂) (K := K₂) hq
    (i := x - q.off.toNat) (by omega) r₂ h2
  rw [show p.off.toNat + (x - p.off.toNat) = x by omega] at e1
  rw [show q.off.toNat + (x - q.off.toNat) = x by omega] at e2
  rcases hd (b, x) with e | e <;> simp_all

/-! ## The invariant -/

/-- The pure facts of a node at `N` of `sz` bytes in a block at address `A` of `S` bytes. -/
structure NodeFacts (N : Ptr) (A S sz : Nat) : Prop where
  off0 : 0 ≤ N.off
  al : (A + N.off.toNat) % 8 = 0
  fit : N.off.toNat + sz ≤ S
  hdr : 24 ≤ sz
  even : sz % 2 = 0
  small : S < 2 ^ 63

/-- The header of a node and the child's token for it: the `size` word (atomic; even, so its
`resizing` bit is clear), the `end_index` word (atomic) and the `next` pointer. -/
def Header (CI : FAllocInv) (N : Ptr) (A S : Nat) (K : BlockKind) (sz : Nat) (ei : BitVec 64)
    (nxt : Option Ptr) : FAssn :=
  apts N (BitVec.ofNat 64 sz) ⋆ apts (N.add 8) ei ⋆
    up (regionIn (N.add 16) A S K 8 (Enc.encode nxt)) ⋆ CI.tok N sz 3 A S K

/-- The used nodes after the first (`free = false`) or the free list (`free = true`) as a
`next`-linked chain: headers and tokens, and for the free list the whole buffer. -/
def Chain (CI : FAllocInv) (free : Bool) : List Ptr → Option Ptr → FAssn
  | [], none => FAssn.emp
  | N :: ns, some N' =>
    FAssn.ex fun A : Nat => FAssn.ex fun S : Nat => FAssn.ex fun K : BlockKind =>
    FAssn.ex fun sz : Nat => FAssn.ex fun ei : BitVec 64 => FAssn.ex fun nxt : Option Ptr =>
    FAssn.ex fun buf : Array Byte =>
      ⟪N = N' ∧ NodeFacts N A S sz ∧ buf.size = (if free then sz - 24 else 0)⟫ ⋆
        (Header CI N A S K sz ei nxt ⋆ up (regionIn (N.add 24) A S K 1 buf) ⋆ Chain CI free ns nxt)
  | _, _ => ⟪False⟫

/-- The used nodes after the first. -/
def UsedRest (CI : FAllocInv) (nxt : Option Ptr) : FAssn := FAssn.ex fun ns => Chain CI false ns nxt

/-- The free list. -/
def FreeList (CI : FAllocInv) (fl : Option Ptr) : FAssn := FAssn.ex fun ns => Chain CI true ns fl

/-- Bytes that frees of earlier allocations leaked back to the arena (the arena never reads
them before a `reset`). -/
def Junk : FAssn := FAssn.ex fun h : Heap => up (fun h' => h' = h)

theorem junk_absorb {X : Assn} {r : Res} (h : (up X ⋆ Junk) r) : Junk r := by
  obtain ⟨r₁, r₂, hd, rfl, h1, ⟨hj, h2⟩⟩ := h
  refine ⟨r₁.heap.erase ∪ hj, ?_⟩
  obtain ⟨-, k1, g1⟩ := h1
  obtain ⟨e2, k2, g2⟩ := h2
  refine ⟨?_, by simp [k1, k2, Know.union_none], by simp [g1, g2]⟩
  show (FHeap.union r₁.heap r₂.heap).erase = _
  rw [← e2]; exact FHeap.erase_union _ _

/-- The arena's variables: the struct (`Ac`, `Sc`, `Kc`, `cbs`: the child allocator's bytes), the
lists' heads, the grant map `M`, and the first node (`nxt`, `A`, `S`, `K`, `sz`, `ei`, `tail`;
unused without one). -/
structure OV where
  Ac : Nat
  Sc : Nat
  Kc : BlockKind
  cbs : Array Byte
  first : Option Ptr
  fl : Option Ptr
  M : GMap
  nxt : Option Ptr
  A : Nat
  S : Nat
  K : BlockKind
  sz : Nat
  ei : Nat
  tail : Array Byte

/-- The facts of the first node: none means no grant. -/
def OV.FirstFacts (w : OV) : Prop :=
  match w.first with
    | none => w.M = GMap.empty
    | some N => NodeFacts N w.A w.S w.sz ∧ 24 + w.ei ≤ w.sz ∧ w.tail.size = w.sz - 24 - w.ei

/-- The facts of the arena's variables. -/
def OV.Facts (w : OV) : Prop := w.cbs.size = 16 ∧ w.M.Fin ∧ w.FirstFacts

/-- The first node of `used_list`: header and token, and the unused tail of its buffer. -/
def FirstPart (CI : FAllocInv) (w : OV) : FAssn :=
  match w.first with
  | none => FAssn.emp
  | some N => Header CI N w.A w.S w.K w.sz (BitVec.ofNat 64 w.ei) w.nxt ⋆
      up (regionIn (N.add (24 + w.ei)) w.A w.S w.K 1 w.tail)

/-- The arena's resources. -/
def OV.body (CI : FAllocInv) (γ e : Nat) (ctx : Ptr) (w : OV) : FAssn :=
  up (regionIn ctx w.Ac w.Sc w.Kc 8 w.cbs) ⋆ aptsE (ctx.add 16) w.first ⋆ aptsE (ctx.add 24) w.fl ⋆
    gauth γ e w.M ⋆ CI.own ⋆ Junk ⋆ FirstPart CI w ⋆ UsedRest CI w.nxt ⋆ FreeList CI w.fl

/-- The arena's state (module doc). -/
def own (CI : FAllocInv) (γ e : Nat) (ctx : Ptr) : FAssn :=
  FAssn.ex fun w : OV => ⟪w.Facts⟫ ⋆ w.body CI γ e ctx

/-- The arena's invariant at epoch `e`: the token of a region is a ghost token of epoch `e` that
names it. -/
def inv (CI : FAllocInv) (γ e : Nat) (ctx : Ptr) : FAllocInv where
  own := own CI γ e ctx
  tok p n _ _ _ _ := FAssn.ex fun i => gfrag γ e i (p, n)

/-! ## `free` -/

/-- The variables of `free`'s precondition on an arena with a first node `N` (block `bN`), a
slice in block `bp` granted under id `i`, and the struct in block `bc`. -/
structure FV where
  w : OV
  i : Nat
  N : Ptr
  bc : BlockId
  bN : BlockId
  bp : BlockId
  A' : Nat
  S' : Nat
  K' : BlockKind

section Free

variable (CI : FAllocInv) (γ e : Nat) (ctx : Ptr) (s : Slice) (k : Nat) (bs : Array Byte)

def FV.Facts (v : FV) : Prop :=
  v.w.Facts ∧ v.w.first = some v.N ∧ ctx.block = some v.bc ∧ v.N.block = some v.bN ∧
    s.ptr.block = some v.bp ∧ (v.w.Ac + ctx.off.toNat) % 8 = 0 ∧ s.len.toNat = bs.size ∧
    0 < bs.size ∧ 0 ≤ ctx.off ∧ 0 ≤ s.ptr.off

/-- The atoms of `free`'s precondition. -/
def FV.gA (v : FV) : FAssn := gauth γ e v.w.M
def FV.uW (v : FV) : FAssn := aptsE (ctx.add 16) (some v.N)
def FV.eW (v : FV) (ei : Nat) : FAssn := apts (v.N.add 8) (BitVec.ofNat 64 ei)
def FV.nR (v : FV) : FAssn := up (regionIn (v.N.add 16) v.w.A v.w.S v.w.K 8 (Enc.encode v.w.nxt))
def FV.cR (v : FV) : FAssn := up (regionIn ctx v.w.Ac v.w.Sc v.w.Kc 8 v.w.cbs)
def FV.tR (v : FV) (ei : Nat) (tail : Array Byte) : FAssn :=
  up (regionIn (v.N.add (24 + ei)) v.w.A v.w.S v.w.K 1 tail)
def FV.rg (v : FV) : FAssn := up (regionIn s.ptr v.A' v.S' v.K' (2 ^ k) bs)
/-- What `free` does not touch. -/
def FV.F (v : FV) : FAssn :=
  apts v.N (BitVec.ofNat 64 v.w.sz) ⋆ CI.tok v.N v.w.sz 3 v.w.A v.w.S v.w.K ⋆
    aptsE (ctx.add 24) v.w.fl ⋆ CI.own ⋆ UsedRest CI v.w.nxt ⋆ FreeList CI v.w.fl

/-- What `free`'s steps do not change before the `cmpxchg`, besides the two words. -/
def FV.R0 (v : FV) : FAssn :=
  v.gA γ e ⋆ gfrag γ e v.i (s.ptr, bs.size) ⋆ v.nR ⋆ v.cR ctx ⋆ v.tR v.w.ei v.w.tail ⋆ v.rg s k bs ⋆ Junk ⋆ v.F CI ctx

/-- `free`'s precondition: the two words it reads, then the rest. -/
def FV.L (v : FV) : FAssn := v.uW ctx ⋆ (v.eW v.w.ei ⋆ v.R0 CI γ e ctx s k bs)

end Free

theorem region_facts {p : Ptr} {A S : Nat} {K : BlockKind} {a : Nat} {bs : Array Byte} {r : Res}
    (h : up (regionIn p A S K a bs) r) : (∃ b, p.block = some b) ∧ (A + p.off.toNat) % a = 0 ∧
      0 ≤ p.off := by
  obtain ⟨⟨ha, -, b, hb, h0, -⟩, -⟩ := h
  exact ⟨⟨b, hb⟩, ha, h0⟩

section Free

variable {CI : FAllocInv} {γ e : Nat} {ctx : Ptr} {s : Slice} {k : Nat} {bs : Array Byte}

/-- `free`'s precondition in normal form. A token of the current epoch rules out an arena
without a node (O-A). -/
theorem free_pre {m : Mem} {r rF : Res} (hh : Holds m r rF) (hlen : s.len.toNat = bs.size)
    (hpos : 0 < bs.size) (hp : ((inv CI γ e ctx).own ⋆ (inv CI γ e ctx).granted s.ptr k bs) r) :
    (FAssn.ex fun v : FV => ⟪v.Facts ctx s bs⟫ ⋆ v.L CI γ e ctx s k bs) r := by
  obtain ⟨w, hp⟩ := sep_ex.mp hp
  obtain ⟨hwf, hp⟩ := sep_lift.mp (sep_assoc hp)
  obtain ⟨A', hp⟩ := sep_ex.mp (sep_comm hp)
  obtain ⟨S', hp⟩ := sep_ex.mp hp
  obtain ⟨K', hp⟩ := sep_ex.mp hp
  obtain ⟨i, hp⟩ := sep_ex.mp (of_eq (Q := (FAssn.ex fun i => gfrag γ e i (s.ptr, bs.size)) ⋆
    (up (regionIn s.ptr A' S' K' (2 ^ k) bs) ⋆ w.body CI γ e ctx)) (by simp only [inv]; ac_rfl) hp)
  have hp := of_eq (Q := (up (regionIn s.ptr A' S' K' (2 ^ k) bs) ⋆ gfrag γ e i (s.ptr, bs.size)) ⋆
    w.body CI γ e ctx) (by ac_rfl) hp
  -- hp : ((up rg ⋆ gfrag) ⋆ body) r
  cases hfirst : w.first with
  | none =>
    exfalso
    have hn : w.M = GMap.empty := by have := hwf.2.2; unfold OV.FirstFacts at this; rw [hfirst] at this; exact this
    have hp' := of_eq (Q := (gauth γ e w.M ⋆ gfrag γ e i (s.ptr, bs.size)) ⋆ (up (regionIn s.ptr A' S' K' (2 ^ k) bs) ⋆
      up (regionIn ctx w.Ac w.Sc w.Kc 8 w.cbs) ⋆ aptsE (ctx.add 16) w.first ⋆ aptsE (ctx.add 24) w.fl ⋆
      CI.own ⋆ Junk ⋆ FirstPart CI w ⋆ UsedRest CI w.nxt ⋆ FreeList CI w.fl))
      (by simp only [OV.body, inv]; ac_rfl) hp
    obtain ⟨r₁, r₂, -, rfl, h1, -⟩ := hp'
    have := gfrag_mem h1 (Ghost.Ok.assoc.mp hh.ghost)
    rw [hn] at this; cases this
  | some N =>
    have hwf' := hwf.2.2
    unfold OV.FirstFacts at hwf'
    rw [hfirst] at hwf'
    -- the shape with dummy block ids, to read the blocks off the regions
    have hL : ∀ bc bN bp, (FV.L CI γ e ctx s k bs ⟨w, i, N, bc, bN, bp, A', S', K'⟩) r := by
      intro bc bN bp
      refine of_eq ?_ hp
      simp only [OV.body, inv, FirstPart, hfirst, Header, FV.L, FV.R0, FV.gA, FV.uW, FV.eW, FV.nR,
        FV.cR, FV.tR, FV.rg, FV.F]
      ac_rfl
    have h0 := hL 0 0 0
    unfold FV.L FV.R0 at h0
    obtain ⟨_, _, -, -, -, h1⟩ := h0
    obtain ⟨_, _, -, -, -, h2⟩ := h1
    obtain ⟨_, _, -, -, -, h3⟩ := h2
    obtain ⟨_, _, -, -, -, h4⟩ := h3
    obtain ⟨_, _, -, -, hn, h5⟩ := h4
    obtain ⟨_, _, -, -, hc, h6⟩ := h5
    obtain ⟨_, _, -, -, -, h7⟩ := h6
    obtain ⟨_, _, -, -, hg, -⟩ := h7
    obtain ⟨⟨bc, hbc⟩, hac, hc0⟩ := region_facts hc
    obtain ⟨⟨bN, hbN⟩, -, -⟩ := region_facts hn
    obtain ⟨⟨bp, hbp⟩, -, hp0⟩ := region_facts hg
    exact ⟨⟨w, i, N, bc, bN, bp, A', S', K'⟩, sep_lift.mpr ⟨⟨hwf, hfirst, hbc, by simpa [Ptr.add] using hbN,
      hbp, hac, hlen, hpos, hc0, hp0⟩, hL _ _ _⟩⟩

end Free

/-! ## Run lemmas -/

theorem ptrAddr_run' {m : Mem} {p : Ptr} {b : BlockId} {blk : Block} (hpb : p.block = some b)
    (hb : m.blocks[b]? = some blk) : (ptrAddr p).run m = pure ((blk.addr : Int) + p.off, m) := by
  obtain ⟨pb, po⟩ := p
  simp only at hpb; subst hpb
  exact ptrAddr_run hb po

theorem ptrEqAddr_run {m : Mem} {p q : Ptr} {b b' : BlockId} {blk blk' : Block}
    (hp : p.block = some b) (hb : m.blocks[b]? = some blk) (hq : q.block = some b')
    (hb' : m.blocks[b']? = some blk') :
    (ptrEqAddr p q).run m = pure (decide ((blk.addr : Int) + p.off = (blk'.addr : Int) + q.off), m) := by
  unfold ptrEqAddr
  simp only [StateT.run_bind, ptrAddr_run' hp hb, pure_bind, ptrAddr_run' hq hb', StateT.run_pure]

theorem ptrProject_add_run' {m : Mem} {p : Ptr} {b : BlockId} {blk : Block} {k : Int}
    (hpb : p.block = some b) (hb : m.blocks[b]? = some blk) (h0 : 0 ≤ p.off)
    (hk : 0 ≤ k) (hn : p.off + k ≤ blk.bytes.size) :
    (ptrProject p (·.add k)).run m = pure (p.add k, m) :=
  ptrProject_add_run (inBounds_of hpb hb h0 (by omega)) (inBounds_of (p := p.add k) hpb hb
    (by simp [Ptr.add]; omega) (by simp [Ptr.add]; omega))

theorem ptrProject_elem_run {m : Mem} {p : Ptr} {b : BlockId} {blk : Block} {i : BitVec 64}
    (hpb : p.block = some b) (hb : m.blocks[b]? = some blk) (h0 : 0 ≤ p.off)
    (hn : p.off + i.toNat ≤ blk.bytes.size) :
    (ptrProject p (·.elem 1 i)).run m = pure (p.add i.toNat, m) := by
  have e : (fun x : Ptr => x.elem 1 i) = (·.add (i.toNat : Int)) := by
    funext x; simp [Ptr.elem]
  rw [e]
  exact ptrProject_add_run' hpb hb h0 (by omega) hn

section FreeProof

variable {CI : FAllocInv} {γ e : Nat} {ctx : Ptr} {s : Slice} {k : Nat} {bs : Array Byte}

theorem encode_nxt_size (nxt : Option Ptr) : (Enc.encode nxt).size = 8 := LawfulEnc.size_encode nxt

/-- What the memory says about the blocks of `free`'s precondition. -/
theorem free_mem {v : FV} (hv : v.Facts ctx s bs) {m : Mem} {r rF : Res} (hh : Holds m r rF)
    (hp : v.L CI γ e ctx s k bs r) (hs : m.FSeq) :
    ∃ blkC blkN blkP, m.blocks[v.bc]? = some blkC ∧ blkC.addr = v.w.Ac ∧
      ctx.off.toNat + 16 ≤ blkC.bytes.size ∧
      m.blocks[v.bN]? = some blkN ∧ blkN.addr = v.w.A ∧ blkN.bytes.size = v.w.S ∧
      m.blocks[v.bp]? = some blkP ∧ blkP.addr = v.A' ∧ blkP.bytes.size = v.S' ∧
      s.ptr.off.toNat + bs.size ≤ v.S' ∧
      (v.bp ≠ v.bN → v.A' + v.S' ≤ v.w.A ∨ v.w.A + v.w.S ≤ v.A') ∧
      (v.bp = v.bN → v.A' = v.w.A ∧ v.S' = v.w.S ∧ v.K' = v.w.K) := by
  obtain ⟨⟨hc16, -, -⟩, -, hbc, hbN, hbp, -, -, hpos, -⟩ := hv
  have hoC : Owns v.bc (ctx.off.toNat + 15) v.w.Ac v.w.Sc v.w.Kc (v.L CI γ e ctx s k bs) :=
    Owns.sepR (Owns.sepR (Owns.sepR (Owns.sepR (Owns.sepR (Owns.sepL
      (Owns.region (a := 8) hbc (i := 15) (by omega)))))))
  have hbN' : (v.N.add 16).block = some v.bN := by simpa [Ptr.add] using hbN
  have hoN : Owns v.bN ((v.N.add 16).off.toNat + 0) v.w.A v.w.S v.w.K (v.L CI γ e ctx s k bs) :=
    Owns.sepR (Owns.sepR (Owns.sepR (Owns.sepR (Owns.sepL
      (Owns.region (a := 8) (bs := Enc.encode v.w.nxt) hbN' (i := 0)
        (by rw [encode_nxt_size]; omega))))))
  have hoP : Owns v.bp (s.ptr.off.toNat + (bs.size - 1)) v.A' v.S' v.K' (v.L CI γ e ctx s k bs) :=
    Owns.sepR (Owns.sepR (Owns.sepR (Owns.sepR (Owns.sepR (Owns.sepR (Owns.sepR (Owns.sepL
      (Owns.region (a := 2 ^ k) hbp (i := bs.size - 1) (by omega)))))))))
  obtain ⟨blkC, e1, -, x1, a1, -, -⟩ := hoC.block hh hp
  obtain ⟨blkN, e2, -, -, a2, s2, k2⟩ := hoN.block hh hp
  obtain ⟨blkP, e3, -, x3, a3, s3, k3⟩ := hoP.block hh hp
  refine ⟨blkC, blkN, blkP, e1, a1, by omega, e2, a2, s2, e3, a3, s3, by omega,
    fun hne => hoP.apart hoN hne hh hp hs, fun heq => ?_⟩
  rw [heq, e2] at e3
  cases e3
  exact ⟨a3.symm.trans a2, s3.symm.trans s2, k3.symm.trans k2⟩

/-- A slice whose end has the address of `buf + end_index` lies in the first node's buffer, right
before `end_index` (O-F: decided by ownership, `region_apart`, `Owns.apart`). -/
theorem last_facts {v : FV} (hv : v.Facts ctx s bs) (hnf : NodeFacts v.N v.w.A v.w.S v.w.sz)
    (hei : 24 + v.w.ei ≤ v.w.sz)
    (heq : ((v.w.A : Int) + (v.N.off + 24 + v.w.ei)) = (v.A' : Int) + (s.ptr.off + bs.size))
    {m : Mem} {r rF : Res} (hh : Holds m r rF) (hp : v.L CI γ e ctx s k bs r) (hs : m.FSeq) :
    v.bp = v.bN ∧ v.A' = v.w.A ∧ v.S' = v.w.S ∧ v.K' = v.w.K ∧
      v.N.off.toNat + 24 ≤ s.ptr.off.toNat ∧
      s.ptr.off.toNat + bs.size = v.N.off.toNat + 24 + v.w.ei := by
  obtain ⟨-, -, -, hbN, hbp, -, -, hpos, -, hp0⟩ := id hv
  obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, hsl, hap, hsame⟩ :=
    free_mem hv hh hp hs
  have hf := hnf.fit
  have h0 := hnf.off0
  by_cases hb : v.bp = v.bN
  · obtain ⟨hA, hS, hK⟩ := hsame hb
    rw [hA] at heq
    have hoff : s.ptr.off.toNat + bs.size = v.N.off.toNat + 24 + v.w.ei := by omega
    have hr := of_eq (Q := (v.nR ⋆ v.rg s k bs) ⋆ (v.uW ctx ⋆ v.eW v.w.ei ⋆ v.gA γ e ⋆
      gfrag γ e v.i (s.ptr, bs.size) ⋆ v.cR ctx ⋆ v.tR v.w.ei v.w.tail ⋆ Junk ⋆ v.F CI ctx))
      (by simp only [FV.L, FV.R0]; ac_rfl) hp
    obtain ⟨_, _, -, -, hr, -⟩ := hr
    have := region_apart (by simpa [Ptr.add] using hbN) (hb ▸ hbp)
      (by rw [encode_nxt_size]; decide) hpos hr
    rw [encode_nxt_size] at this
    simp only [Ptr.add] at this
    exact ⟨hb, hA, hS, hK, by omega, hoff⟩
  · rcases hap hb with h | h <;> omega

theorem debug_assert_true : debug_assert true = pure () := rfl

/-- `free`'s run, case by case (module doc). -/
theorem free_ct (CI : FAllocInv) (γ e : Nat) (ctx s : _) (k : Nat) (ra : BitVec 64) (bs : Array Byte)
    (hlen : s.len.toNat = bs.size) (hpos : 0 < bs.size) :
    CTriple (Tgt := Tgt) ((inv CI γ e ctx).own ⋆ (inv CI γ e ctx).granted s.ptr k bs)
      (heap_ArenaAllocator_free ctx s ⟨BitVec.ofNat 6 k⟩ ra) (fun _ => (inv CI γ e ctx).own) := by
  refine CTriple.preM (fun m r rF hh hp hs => free_pre hh hlen hpos hp) ?_
  refine CTriple.ex fun v => CTriple.lift fun hv => ?_
  have hv' := hv
  obtain ⟨⟨hc16, hfin, hwf⟩, hfirst, hbc, hbN, hbp, hac, -, -, hc0, hp0⟩ := hv'
  unfold OV.FirstFacts at hwf
  rw [hfirst] at hwf
  obtain ⟨hnf, hei, htail⟩ := hwf
  have hmem := fun m r rF (hh : Holds m r rF) hp hs => free_mem (CI := CI) (γ := γ) (e := e) (k := k) hv hh hp hs
  unfold heap_ArenaAllocator_free heap_ArenaAllocator_loadFirstNode
  simp only [atomicLoadPtrC, atomicLoadC, cmpxchgC]
  conc_norm
  -- `@intFromPtr(ctx) & 7 == 0`
  refine CTriple.pureStep (v := BitVec.ofInt 64 ((v.w.Ac : Int) + ctx.off)) (fun m r rF hh hp hs => ?_) ?_
  · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, hsl, -, -⟩ := hmem m r rF hh hp hs
    simp only [StateT.run_bind, ptrAddr_run' hbc e1, a1]; rfl
  have h7 : BitVec.ofInt 64 ((v.w.Ac : Int) + ctx.off) &&& 7 = 0 :=
    Ops.and_mask_eq_zero (k := 3) (by decide) (by omega) (by omega)
  simp only [h7, ↓reduceIte]
  -- `@alignCast(ctx)`
  refine CTriple.pureStep (v := ctx) (fun m r rF hh hp hs => ?_) ?_
  · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, hsl, -, -⟩ := hmem m r rF hh hp hs
    have h8 : ((v.w.Ac : Int) + ctx.off) % 8 = 0 := by omega
    unfold checkAlign
    simp only [StateT.run_bind, ptrAddr_run' hbc e1, a1, pure_bind]
    simp [h8]
  rw [Ops.gt_eq, show decide ((0 : BitVec 64).toNat < s.len.toNat) = true by simp; omega,
    debug_assert_true]
  conc_norm
  -- `&arena.state.used_list`
  refine CTriple.pureStep (v := ctx.add 16) (fun m r rF hh hp hs => ?_) ?_
  · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, hsl, -, -⟩ := hmem m r rF hh hp hs
    exact ptrProject_add_run' hbc e1 hc0 (by decide) (by omega)
  refine CTriple.pick_bind ?_
  refine CTriple.readStep (FTriple.atomicLoadPtr (ctx.add 16) (some v.N) _) rfl ?_
  simp only [Option.isSome_some, ↓reduceIte, optPayload]
  conc_norm
  have hei64 : (BitVec.ofNat 64 v.w.ei).toNat = v.w.ei := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]; have := hnf.fit; have := hnf.small; omega
  -- `buf_ptr`, `&node.end_index`, `end_index`
  refine CTriple.pureStep (v := v.N.add 24) (fun m r rF hh hp hs => ?_) ?_
  · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, hsl, -, -⟩ := hmem m r rF hh hp hs
    have := hnf.fit; have := hnf.off0
    rw [ptrProject_elem_run hbN e2 hnf.off0 (by simp; omega)]; rfl
  refine CTriple.pureStep (v := v.N.add 8) (fun m r rF hh hp hs => ?_) ?_
  · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, hsl, -, -⟩ := hmem m r rF hh hp hs
    have := hnf.fit; have := hnf.off0
    exact ptrProject_add_run' hbN e2 hnf.off0 (by decide) (by omega)
  refine CTriple.pick_bind ?_
  refine CTriple.readStep (FTriple.atomicLoad (v.N.add 8) (BitVec.ofNat 64 v.w.ei) _)
    (sep_left_comm_eq _ _ _) ?_
  -- `buf_ptr + end_index`, `memory.ptr + memory.len`, and their comparison
  refine CTriple.pureStep (v := (v.N.add 24).add v.w.ei) (fun m r rF hh hp hs => ?_) ?_
  · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, hsl, -, -⟩ := hmem m r rF hh hp hs
    have := hnf.fit; have := hnf.off0
    rw [ptrProject_elem_run (by simpa [Ptr.add] using hbN) e2 (by simp [Ptr.add]; omega)
      (by simp [Ptr.add, hei64]; omega), hei64]
  refine CTriple.pureStep (v := s.ptr.add bs.size) (fun m r rF hh hp hs => ?_) ?_
  · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, hsl, -, -⟩ := hmem m r rF hh hp hs
    rw [ptrProject_elem_run hbp e3 hp0 (by omega), hlen]
  refine CTriple.pureStep (v := !decide (((v.w.A : Int) + (v.N.off + 24 + v.w.ei)) =
    (v.A' : Int) + (s.ptr.off + bs.size))) (fun m r rF hh hp hs => ?_) ?_
  · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, hsl, -, -⟩ := hmem m r rF hh hp hs
    have := hnf.off0
    rw [StateT.run_bind, ptrEqAddr_run (q := s.ptr.add bs.size) (by simpa [Ptr.add] using hbN) e2
      (by simpa [Ptr.add] using hbp) e3, a2, a3]
    simp only [Ptr.add, pure_bind, StateT.run_pure]
    congr 4
  by_cases heq : ((v.w.A : Int) + (v.N.off + 24 + v.w.ei)) = (v.A' : Int) + (s.ptr.off + bs.size)
  · simp only [heq, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    -- the slice is the last allocation of the first node (O-F: decided by ownership)
    refine CTriple.facts (fun m r rF hh hp hs => last_facts hv hnf hei heq hh hp hs) ?_
    rintro ⟨hb, hA, hS, hK, hlo, hoff⟩
    have hle : s.len.toNat ≤ (BitVec.ofNat 64 v.w.ei).toNat := by rw [hei64, hlen]; omega
    have hd : (BitVec.ofNat 64 v.w.ei - s.len).toNat = v.w.ei - bs.size := by
      rw [BitVec.toNat_sub_of_le hle, hei64, hlen]
    rw [Zig.sub_unsigned_of_le hle]
    conc_norm
    -- `buf_ptr + new_end_index == memory.ptr`
    refine CTriple.pureStep (v := (v.N.add 24).add (v.w.ei - bs.size : Nat))
      (fun m r rF hh hp hs => ?_) ?_
    · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, -⟩ := hmem m r rF hh hp hs
      have := hnf.fit; have := hnf.off0
      rw [ptrProject_elem_run (by simpa [Ptr.add] using hbN) e2 (by simp [Ptr.add]; omega)
        (by simp [Ptr.add, hd]; omega), hd]
    refine CTriple.pureStep (v := true) (fun m r rF hh hp hs => ?_) ?_
    · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, -⟩ := hmem m r rF hh hp hs
      have := hnf.off0
      rw [ptrEqAddr_run (by simpa [Ptr.add] using hbN) e2 hbp e3, a2, a3, hA]
      have : (v.w.A : Int) + (v.N.add 24 |>.add (v.w.ei - bs.size : Nat)).off = v.w.A + s.ptr.off := by
        simp only [Ptr.add]; omega
      simp [this]
    rw [debug_assert_true]
    conc_norm
    refine CTriple.pureStep (v := v.N.add 8) (fun m r rF hh hp hs => ?_) ?_
    · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, -⟩ := hmem m r rF hh hp hs
      have := hnf.fit; have := hnf.off0
      exact ptrProject_add_run' hbN e2 hnf.off0 (by decide) (by omega)
    refine CTriple.pick_bind ?_
    -- the strong `cmpxchg` finds `end_index` and moves it back
    refine CTriple.pre (P := v.eW v.w.ei ⋆ (v.uW ctx ⋆ v.R0 CI γ e ctx s k bs)) ?_
      (fun r h => of_eq (sep_left_comm_eq _ _ _) h)
    refine CTriple.bind (CTriple.liftMem ((FTriple.cmpxchgHit (v.N.add 8) (BitVec.ofNat 64 v.w.ei)
      (BitVec.ofNat 64 v.w.ei - s.len) _ _).frame)) fun _ => ?_
    have hnew : BitVec.ofNat 64 v.w.ei - s.len = BitVec.ofNat 64 (v.w.ei - bs.size) := by
      apply BitVec.eq_of_toNat_eq; rw [hd, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
      have := hnf.fit; have := hnf.small; omega
    refine CTriple.upd (Upd.trans (Upd.of_imp fun r h => of_eq (by
        simp only [FV.R0, FV.gA]; ac_rfl) (sep_mono_left (fun _ x => (sep_lift.mp x).2) h))
      (Upd.frame (R := apts (v.N.add 8) (BitVec.ofNat 64 v.w.ei - s.len) ⋆ v.uW ctx ⋆ v.nR ⋆
          v.cR ctx ⋆ (v.rg s k bs ⋆ v.tR v.w.ei v.w.tail) ⋆ Junk ⋆ v.F CI ctx) Upd.retire)) ?_
    refine CTriple.ret' () fun r h => ?_
    have hpq : s.ptr = v.N.add (24 + ((v.w.ei - bs.size : Nat) : Int)) := by
      have hb' : s.ptr.block = v.N.block := by rw [hbp, hbN, hb]
      have ho : s.ptr.off = v.N.off + (24 + ((v.w.ei - bs.size : Nat) : Int)) := by
        have := hnf.off0; omega
      rw [show s.ptr = ⟨s.ptr.block, s.ptr.off⟩ from rfl, hb', ho]; rfl
    have hjoin : ∀ r, (v.rg s k bs ⋆ v.tR v.w.ei v.w.tail) r →
        up (regionIn (v.N.add (24 + ((v.w.ei - bs.size : Nat) : Int))) v.w.A v.w.S v.w.K 1
          (bs ++ v.w.tail)) r := by
      intro r hr
      obtain ⟨⟨h₁, h₂, hd₁, he, x1, x2⟩, hk, hg⟩ := sep_up hr
      refine ⟨?_, hk, hg⟩
      rw [he, ← hpq]
      refine regionIn_join (a' := 1) ⟨h₁, h₂, hd₁, rfl, ?_, ?_⟩
      · rw [hA, hS, hK] at x1; exact regionIn_weaken x1 (Nat.one_dvd _)
      · have : s.ptr.add bs.size = v.N.add (24 + (v.w.ei : Int)) := by
          rw [hpq]; simp only [Ptr.add, Ptr.mk.injEq, true_and]; omega
        rw [this]; exact x2
    have h' := of_eq (Q := (v.rg s k bs ⋆ v.tR v.w.ei v.w.tail) ⋆ (gauth γ e (v.w.M.set v.i none) ⋆
      apts (v.N.add 8) (BitVec.ofNat 64 v.w.ei - s.len) ⋆ v.uW ctx ⋆ v.nR ⋆ v.cR ctx ⋆ Junk ⋆
      v.F CI ctx)) (by ac_rfl) h
    have h'' := sep_mono_left hjoin h'
    refine ⟨{ v.w with M := v.w.M.set v.i none, ei := v.w.ei - bs.size, tail := bs ++ v.w.tail },
      sep_lift.mpr ⟨⟨hc16, hfin.set _ _, ?_⟩, of_eq ?_ h''⟩⟩
    · simp only [OV.FirstFacts, hfirst]
      exact ⟨hnf, by omega, by simp only [Array.size_append, htail]; have := hnf.hdr; omega⟩
    · rw [hnew]
      simp only [OV.body, FirstPart, hfirst, Header, FV.uW, FV.nR, FV.cR, FV.F]
      ac_rfl
  · -- not the last allocation: the slice leaks to the arena
    simp only [heq, decide_false, Bool.not_false, ↓reduceIte]
    refine CTriple.upd (Upd.trans (Upd.of_imp fun r h => of_eq (by
        simp only [FV.L, FV.R0, FV.gA]; ac_rfl) h) (Upd.frame (R := v.uW ctx ⋆ v.eW v.w.ei ⋆ v.nR ⋆
          v.cR ctx ⋆ v.tR v.w.ei v.w.tail ⋆ (v.rg s k bs ⋆ Junk) ⋆ v.F CI ctx) Upd.retire)) ?_
    refine CTriple.ret' () fun r h => ?_
    have h' := of_eq (Q := (v.rg s k bs ⋆ Junk) ⋆ (gauth γ e (v.w.M.set v.i none) ⋆ v.uW ctx ⋆ v.eW v.w.ei ⋆
      v.nR ⋆ v.cR ctx ⋆ v.tR v.w.ei v.w.tail ⋆ v.F CI ctx)) (by ac_rfl) h
    have h'' := sep_mono_left (Q := Junk) (fun _ x => junk_absorb x) h'
    refine ⟨{ v.w with M := v.w.M.set v.i none }, sep_lift.mpr ⟨⟨hc16, hfin.set _ _, ?_⟩,
      of_eq ?_ h''⟩⟩
    · simp only [OV.FirstFacts, hfirst]; exact ⟨hnf, hei, htail⟩
    · simp only [OV.body, FirstPart, hfirst, Header, FV.uW, FV.eW, FV.nR, FV.cR, FV.tR, FV.F]
      ac_rfl

/-- **`free` meets `FAllocSpec`'s `free` field** for the arena invariant at every epoch, every
child invariant `CI`, and every depth of the one-thread reading (`Sched.soloRun`). -/
theorem free_spec (CI : FAllocInv) (γ e : Nat) (ctx : Ptr) (fuel : Nat) (s : Slice) (k : Nat)
    (ra : BitVec 64) (bs : Array Byte) (hlen : s.len.toNat = bs.size) (hpos : 0 < bs.size) :
    FLogic.partial.T ((inv CI γ e ctx).own ⋆ (inv CI γ e ctx).granted s.ptr k bs)
      (Sched.soloRun fuel (heap_ArenaAllocator_free ctx s ⟨BitVec.ofNat 6 k⟩ ra))
      (fun _ => (inv CI γ e ctx).own) :=
  free_ct CI γ e ctx s k ra bs hlen hpos fuel

end FreeProof

/-! ## `resize` and `remap` -/

/-- The bits of an even size with the `resizing` bit clear are the size (`Node.Size.toInt`). -/
theorem bits_even (w : BitVec 64) (h : w.toNat % 2 = 0) :
    (Packed.toBits (false : Bool)).setWidth 64 <<< 0 ||| (Packed.toBits (w.extractLsb' 1 63)).setWidth 64 <<< 1 = w := by
  have h0 : w[0] = false := by
    simp [BitVec.getElem_eq_testBit_toNat, Nat.testBit_zero, h]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Packed.toBits, Bool.false_eq_true, ↓reduceIte, BitVec.shiftLeft_zero, BitVec.getLsbD_or,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_extractLsb']
  rcases i with _ | i
  · simp [h0]
  · simp [show i < 63 by omega, show i < 64 by omega, hi, Nat.add_comm 1 i]

/-- `Node.Size.toInt` of the decoded bits of an even size is the size. -/
theorem toInt_ofBits (w : BitVec 64) (h : w.toNat % 2 = 0) :
    heap_ArenaAllocator_Node_Size_toInt (Packed.ofBits w) = pure w := by
  unfold heap_ArenaAllocator_Node_Size_toInt
  simp only [Packed.ofBits, Packed.get]
  show (pure (Packed.toBits ({ resizing := false, «_» := BitVec.extractLsb' 1 63 w } :
    heap_ArenaAllocator_Node_Size)) : Result _) = pure w
  exact congrArg pure (bits_even w h)

theorem le_eq (a b : BitVec 64) : Zig.le false a b = decide (a.toNat ≤ b.toNat) := by
  simp [Zig.le, BitVec.ule]

/-- A saturating unsigned subtraction is the truncated one. -/
theorem subSat_toNat (a b : BitVec 64) : (Zig.subSat false a b).toNat = a.toNat - b.toNat := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [Zig.subSat, Zig.clamp, Zig.val, Bool.false_eq_true, ↓reduceIte]
  rw [BitVec.toNat_ofInt]
  have h64 : ((2 : Int) ^ 64) = 18446744073709551616 := by rfl
  have h64' : (2 : Nat) ^ 64 = 18446744073709551616 := by rfl
  simp only [h64, h64'] at *
  omega

/-- `Node.loadBuf` of a node whose `size` word holds the even size `sz`: the buffer after the
header, `sz - 24` bytes. -/
theorem loadBuf_ct {N : Ptr} {b : BlockId} {sz : Nat} {R : FAssn} (hb : N.block = some b)
    (h0 : 0 ≤ N.off) (hsz : 24 ≤ sz) (heven : sz % 2 = 0) (hsmall : sz < 2 ^ 63)
    (hmem : ∀ m r rF, Holds m r rF → (apts N (BitVec.ofNat 64 sz) ⋆ R) r → m.FSeq →
      ∃ blk, m.blocks[b]? = some blk ∧ N.off.toNat + sz ≤ blk.bytes.size) :
    CTriple (Tgt := Tgt) (apts N (BitVec.ofNat 64 sz) ⋆ R) (heap_ArenaAllocator_Node_loadBuf N)
      (fun sl => ⟪sl = ⟨N.add 24, BitVec.ofNat 64 (sz - 24)⟩⟫ ⋆ (apts N (BitVec.ofNat 64 sz) ⋆ R)) := by
  have hsz64 : (BitVec.ofNat 64 sz).toNat = sz := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]; omega
  unfold heap_ArenaAllocator_Node_loadBuf
  simp only [atomicLoadAsC]
  conc_norm
  refine CTriple.pick_bind ?_
  refine CTriple.readStep (FTriple.atomicLoadAs (α := heap_ArenaAllocator_Node_Size) N
    (BitVec.ofNat 64 sz) _ rfl) rfl ?_
  rw [toInt_ofBits _ (by rw [hsz64]; exact heven)]
  conc_norm
  refine CTriple.pureStep (v := N.add 24) (fun m r rF hh hp hs => ?_) ?_
  · obtain ⟨blk, hblk, hle⟩ := hmem m r rF hh hp hs
    rw [ptrProject_elem_run hb hblk h0 (by simp; omega)]; rfl
  have h24 : (24 : BitVec 64).toNat ≤ (BitVec.ofNat 64 sz).toNat := by rw [hsz64]; simp; omega
  simp only [le_eq, h24, decide_true, ↓reduceIte, Zig.sub_unsigned_of_le h24, Nat.le_refl]
  conc_norm
  have hce : checkSliceEnd (BitVec.ofNat 64 sz) 24 (BitVec.ofNat 64 sz - 24) 0 = pure () := by
    unfold checkSliceEnd; rw [if_pos (by rw [BitVec.toNat_sub_of_le h24]; simp; omega)]
  rw [hce]
  conc_norm
  have e : BitVec.ofNat 64 sz - 24 = BitVec.ofNat 64 (sz - 24) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub_of_le h24, hsz64, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]; rfl
  exact CTriple.ret' _ fun r h => sep_lift.mpr ⟨by rw [e], h⟩

/-- The arena's state from its variables. -/
theorem own_of {CI : FAllocInv} {γ e : Nat} {ctx : Ptr} {w : OV} (hw : w.Facts) {X : FAssn}
    {r : Res} (h : (w.body CI γ e ctx ⋆ X) r) : ((inv CI γ e ctx).own ⋆ X) r :=
  sep_mono_left (fun _ h => ⟨w, sep_lift.mpr ⟨hw, h⟩⟩) h

/-- A grant from its bytes and the token that names it. -/
theorem granted_of {CI : FAllocInv} {γ e : Nat} {ctx p : Ptr} {k : Nat} {A S : Nat}
    {K : BlockKind} {i : Nat} {bs : Array Byte} {r : Res}
    (h : (up (regionIn p A S K (2 ^ k) bs) ⋆ gfrag γ e i (p, bs.size)) r) :
    (inv CI γ e ctx).granted p k bs r :=
  ⟨A, S, K, sep_mono_right (fun _ h => ⟨i, h⟩) h⟩

/-- `resize`'s postcondition `true` from the arena's variables and the new grant. -/
theorem resizePost_true {CI : FAllocInv} {γ e : Nat} {ctx p : Ptr} {k n : Nat} {bs bs' : Array Byte}
    {w : OV} (hw : w.Facts) (hsz : bs'.size = n) (hkp : keepsPrefix bs bs') {A S : Nat}
    {K : BlockKind} {i : Nat} {r : Res}
    (h : (w.body CI γ e ctx ⋆ (up (regionIn p A S K (2 ^ k) bs') ⋆ gfrag γ e i (p, bs'.size))) r) :
    (inv CI γ e ctx).resizePost p k bs n true r :=
  own_of hw (sep_mono_right (fun _ h => ⟨bs', sep_lift.mpr ⟨⟨hsz, hkp⟩, granted_of h⟩⟩) h)

/-- `resize`'s postcondition `false`. -/
theorem resizePost_false {CI : FAllocInv} {γ e : Nat} {ctx p : Ptr} {k n : Nat} {bs : Array Byte}
    {w : OV} (hw : w.Facts) {A S : Nat} {K : BlockKind} {i : Nat} {r : Res}
    (h : (w.body CI γ e ctx ⋆ (up (regionIn p A S K (2 ^ k) bs) ⋆ gfrag γ e i (p, bs.size))) r) :
    (inv CI γ e ctx).resizePost p k bs n false r :=
  own_of hw (sep_mono_right (fun _ h => granted_of h) h)

/-- The first `n` bytes of a region keep its alignment; the rest is a region of alignment 1. -/
theorem up_region_split {p : Ptr} {A S : Nat} {K : BlockKind} {a n : Nat} {bs : Array Byte}
    {r : Res} (hn : n ≤ bs.size) (h : up (regionIn p A S K a bs) r) :
    (up (regionIn p A S K a (bs.extract 0 n)) ⋆
      up (regionIn (p.add n) A S K 1 (bs.extract n bs.size))) r := by
  obtain ⟨h1, hk, hg⟩ := h
  exact up_sep ⟨regionIn_split h1 hn (Nat.mod_one _), hk, hg⟩

/-- The keeps-prefix relation of a shrink and of a growth. -/
theorem keepsPrefix_extract (bs : Array Byte) (n : Nat) : keepsPrefix bs (bs.extract 0 n) := by
  unfold keepsPrefix; simp [Array.extract_extract]; congr 1; omega

theorem keepsPrefix_append (bs ext : Array Byte) : keepsPrefix bs (bs ++ ext) := by
  unfold keepsPrefix; simp [Array.extract_eq_self_of_le (as := bs) (Nat.le_add_right _ _)]

section ResizeProof

variable {CI : FAllocInv} {γ e : Nat} {ctx : Ptr} {s : Slice} {k : Nat} {bs : Array Byte}

/-- `resize`'s run, case by case: a slice that is not the first node's last one only shrinks (its
cut bytes become junk); the last one moves `end_index` (shrink, or growth into the tail when it
fits). A successful resize re-points the grant at the new length (`Upd.reassign`). -/
theorem resize_ct (CI : FAllocInv) (γ e : Nat) (ctx s : _) (k : Nat) (n ra : BitVec 64)
    (bs : Array Byte) (hlen : s.len.toNat = bs.size) (hpos : 0 < bs.size) (hn : 0 < n.toNat) :
    CTriple (Tgt := Tgt) ((inv CI γ e ctx).own ⋆ (inv CI γ e ctx).granted s.ptr k bs)
      (heap_ArenaAllocator_resize ctx s ⟨BitVec.ofNat 6 k⟩ n ra)
      ((inv CI γ e ctx).resizePost s.ptr k bs n.toNat) := by
  refine CTriple.preM (fun m r rF hh hp hs => free_pre hh hlen hpos hp) ?_
  refine CTriple.ex fun v => CTriple.lift fun hv => ?_
  have hv' := hv
  obtain ⟨⟨hc16, hfin, hwf⟩, hfirst, hbc, hbN, hbp, hac, -, -, hc0, hp0⟩ := hv'
  unfold OV.FirstFacts at hwf
  rw [hfirst] at hwf
  obtain ⟨hnf, hei, htail⟩ := hwf
  have hmem := fun m r rF (hh : Holds m r rF) hp hs => free_mem (CI := CI) (γ := γ) (e := e) (k := k) hv hh hp hs
  unfold heap_ArenaAllocator_resize heap_ArenaAllocator_loadFirstNode
  simp only [atomicLoadPtrC, atomicLoadC, cmpxchgC]
  conc_norm
  -- `@intFromPtr(ctx) & 7 == 0`
  refine CTriple.pureStep (v := BitVec.ofInt 64 ((v.w.Ac : Int) + ctx.off)) (fun m r rF hh hp hs => ?_) ?_
  · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, hsl, -, -⟩ := hmem m r rF hh hp hs
    simp only [StateT.run_bind, ptrAddr_run' hbc e1, a1]; rfl
  have h7 : BitVec.ofInt 64 ((v.w.Ac : Int) + ctx.off) &&& 7 = 0 :=
    Ops.and_mask_eq_zero (k := 3) (by decide) (by omega) (by omega)
  simp only [h7, ↓reduceIte]
  -- `@alignCast(ctx)`
  refine CTriple.pureStep (v := ctx) (fun m r rF hh hp hs => ?_) ?_
  · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, hsl, -, -⟩ := hmem m r rF hh hp hs
    have h8 : ((v.w.Ac : Int) + ctx.off) % 8 = 0 := by omega
    unfold checkAlign
    simp only [StateT.run_bind, ptrAddr_run' hbc e1, a1, pure_bind]
    simp [h8]
  simp only [Ops.gt_eq, show decide ((0 : BitVec 64).toNat < s.len.toNat) = true by simp; omega,
    show decide ((0 : BitVec 64).toNat < n.toNat) = true by simp; omega, debug_assert_true]
  conc_norm
  -- `&arena.state.used_list`
  refine CTriple.pureStep (v := ctx.add 16) (fun m r rF hh hp hs => ?_) ?_
  · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, hsl, -, -⟩ := hmem m r rF hh hp hs
    exact ptrProject_add_run' hbc e1 hc0 (by decide) (by omega)
  refine CTriple.pick_bind ?_
  refine CTriple.readStep (FTriple.atomicLoadPtr (ctx.add 16) (some v.N) _) rfl ?_
  simp only [Option.isSome_some, ↓reduceIte, optPayload]
  conc_norm
  have hei64 : (BitVec.ofNat 64 v.w.ei).toNat = v.w.ei := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]; have := hnf.fit; have := hnf.small; omega
  -- `buf_ptr`, `&node.end_index`, `end_index`
  refine CTriple.pureStep (v := v.N.add 24) (fun m r rF hh hp hs => ?_) ?_
  · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, hsl, -, -⟩ := hmem m r rF hh hp hs
    have := hnf.fit; have := hnf.off0
    rw [ptrProject_elem_run hbN e2 hnf.off0 (by simp; omega)]; rfl
  refine CTriple.pureStep (v := v.N.add 8) (fun m r rF hh hp hs => ?_) ?_
  · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, hsl, -, -⟩ := hmem m r rF hh hp hs
    have := hnf.fit; have := hnf.off0
    exact ptrProject_add_run' hbN e2 hnf.off0 (by decide) (by omega)
  refine CTriple.pick_bind ?_
  refine CTriple.readStep (FTriple.atomicLoad (v.N.add 8) (BitVec.ofNat 64 v.w.ei) _)
    (sep_left_comm_eq _ _ _) ?_
  -- `buf_ptr + end_index`, `memory.ptr + memory.len`, and their comparison
  refine CTriple.pureStep (v := (v.N.add 24).add v.w.ei) (fun m r rF hh hp hs => ?_) ?_
  · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, hsl, -, -⟩ := hmem m r rF hh hp hs
    have := hnf.fit; have := hnf.off0
    rw [ptrProject_elem_run (by simpa [Ptr.add] using hbN) e2 (by simp [Ptr.add]; omega)
      (by simp [Ptr.add, hei64]; omega), hei64]
  refine CTriple.pureStep (v := s.ptr.add bs.size) (fun m r rF hh hp hs => ?_) ?_
  · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, hsl, -, -⟩ := hmem m r rF hh hp hs
    rw [ptrProject_elem_run hbp e3 hp0 (by omega), hlen]
  refine CTriple.pureStep (v := !decide (((v.w.A : Int) + (v.N.off + 24 + v.w.ei)) =
    (v.A' : Int) + (s.ptr.off + bs.size))) (fun m r rF hh hp hs => ?_) ?_
  · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, hsl, -, -⟩ := hmem m r rF hh hp hs
    have := hnf.off0
    rw [StateT.run_bind, ptrEqAddr_run (q := s.ptr.add bs.size) (by simpa [Ptr.add] using hbN) e2
      (by simpa [Ptr.add] using hbp) e3, a2, a3]
    simp only [Ptr.add, pure_bind, StateT.run_pure]
    congr 4
  by_cases heq : ((v.w.A : Int) + (v.N.off + 24 + v.w.ei)) = (v.A' : Int) + (s.ptr.off + bs.size)
  · simp only [heq, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    -- the slice is the last allocation of the first node
    refine CTriple.facts (fun m r rF hh hp hs => last_facts hv hnf hei heq hh hp hs) ?_
    rintro ⟨hb, hA, hS, hK, hlo, hoff⟩
    have hbN' : (v.N.add 24).block = some v.bN := by simpa [Ptr.add] using hbN
    have hf := hnf.fit
    have h0 := hnf.off0
    have hsm := hnf.small
    have hlenei : bs.size ≤ v.w.ei := by omega
    simp only [le_eq, hlen]
    by_cases hle : n.toNat ≤ bs.size
    · -- shrink: `end_index` moves back by `len - n`; the cut bytes rejoin the tail
      simp only [hle, decide_true, ↓reduceIte]
      have h1 : n.toNat ≤ s.len.toNat := by rw [hlen]; exact hle
      have hd1 : (s.len - n).toNat = bs.size - n.toNat := by rw [BitVec.toNat_sub_of_le h1, hlen]
      have h2 : (s.len - n).toNat ≤ (BitVec.ofNat 64 v.w.ei).toNat := by rw [hd1, hei64]; omega
      have hd2 : (BitVec.ofNat 64 v.w.ei - (s.len - n)).toNat = v.w.ei - (bs.size - n.toNat) := by
        rw [BitVec.toNat_sub_of_le h2, hei64, hd1]
      rw [Zig.sub_unsigned_of_le h1]
      conc_norm
      rw [Zig.sub_unsigned_of_le h2]
      conc_norm
      refine CTriple.pureStep (v := (v.N.add 24).add (v.w.ei - (bs.size - n.toNat) : Nat))
        (fun m r rF hh hp hs => ?_) ?_
      · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, -⟩ := hmem m r rF hh hp hs
        rw [ptrProject_elem_run hbN' e2 (by simp [Ptr.add]; omega) (by simp [Ptr.add, hd2]; omega), hd2]
      refine CTriple.pureStep (v := s.ptr.add n.toNat) (fun m r rF hh hp hs => ?_) ?_
      · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, hsl, -⟩ := hmem m r rF hh hp hs
        rw [ptrProject_elem_run hbp e3 hp0 (by omega)]
      refine CTriple.pureStep (v := true) (fun m r rF hh hp hs => ?_) ?_
      · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, -⟩ := hmem m r rF hh hp hs
        rw [ptrEqAddr_run (by simpa [Ptr.add] using hbN) e2 (by simpa [Ptr.add] using hbp) e3, a2, a3, hA]
        have hx : (v.w.A : Int) + (v.N.off + 24 + ((v.w.ei - (bs.size - n.toNat) : Nat) : Int)) =
            v.w.A + (s.ptr.off + n.toNat) := by omega
        simp only [Ptr.add, hx, decide_true]
      rw [debug_assert_true]
      conc_norm
      refine CTriple.pureStep (v := v.N.add 8) (fun m r rF hh hp hs => ?_) ?_
      · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, -⟩ := hmem m r rF hh hp hs
        exact ptrProject_add_run' hbN e2 hnf.off0 (by decide) (by omega)
      refine CTriple.pick_bind ?_
      refine CTriple.pre (P := v.eW v.w.ei ⋆ (v.uW ctx ⋆ v.R0 CI γ e ctx s k bs)) ?_
        (fun r h => of_eq (sep_left_comm_eq _ _ _) h)
      refine CTriple.bind (CTriple.liftMem ((FTriple.cmpxchgHit (v.N.add 8) (BitVec.ofNat 64 v.w.ei)
        (BitVec.ofNat 64 v.w.ei - (s.len - n)) _ _).frame)) fun _ => ?_
      have hnew : BitVec.ofNat 64 v.w.ei - (s.len - n) =
          BitVec.ofNat 64 (v.w.ei - (bs.size - n.toNat)) := by
        apply BitVec.eq_of_toNat_eq; rw [hd2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]; omega
      refine CTriple.upd (Upd.trans (Upd.of_imp fun r h => of_eq (by
          simp only [FV.R0, FV.gA]; ac_rfl) (sep_mono_left (fun _ x => (sep_lift.mp x).2) h))
        (Upd.frame (R := apts (v.N.add 8) (BitVec.ofNat 64 v.w.ei - (s.len - n)) ⋆ v.uW ctx ⋆ v.nR ⋆
          v.cR ctx ⋆ v.rg s k bs ⋆ v.tR v.w.ei v.w.tail ⋆ Junk ⋆ v.F CI ctx)
          (Upd.reassign (s.ptr, n.toNat)))) ?_
      refine CTriple.ret' true fun r h => ?_
      -- the cut bytes `[n, len)` lie right before the tail
      have hcut : s.ptr.add n.toNat = v.N.add (24 + ((v.w.ei - (bs.size - n.toNat) : Nat) : Int)) := by
        have hb' : s.ptr.block = v.N.block := by rw [hbp, hbN, hb]
        have ho : s.ptr.off + n.toNat = v.N.off + (24 + ((v.w.ei - (bs.size - n.toNat) : Nat) : Int)) := by
          omega
        simp only [Ptr.add]; rw [hb', ho]
      have hjoin : ∀ r, (up (regionIn (s.ptr.add n.toNat) v.A' v.S' v.K' 1 (bs.extract n.toNat bs.size)) ⋆
          v.tR v.w.ei v.w.tail) r →
          up (regionIn (v.N.add (24 + ((v.w.ei - (bs.size - n.toNat) : Nat) : Int))) v.w.A v.w.S v.w.K 1
            (bs.extract n.toNat bs.size ++ v.w.tail)) r := by
        intro r hr
        obtain ⟨⟨h₁, h₂, hd₁, he, x1, x2⟩, hk, hg⟩ := sep_up hr
        refine ⟨?_, hk, hg⟩
        rw [he, ← hcut]
        refine regionIn_join (a' := 1) ⟨h₁, h₂, hd₁, rfl, ?_, ?_⟩
        · rw [hA, hS, hK] at x1; exact x1
        · have : (s.ptr.add n.toNat).add (bs.extract n.toNat bs.size).size = v.N.add (24 + (v.w.ei : Int)) := by
            rw [hcut]; simp only [Ptr.add, Array.size_extract, Ptr.mk.injEq, true_and]; omega
          rw [this]; exact x2
      have h1 := of_eq (Q := v.rg s k bs ⋆ (gauth γ e (v.w.M.set v.i (some (s.ptr, n.toNat))) ⋆
        gfrag γ e v.i (s.ptr, n.toNat) ⋆ apts (v.N.add 8) (BitVec.ofNat 64 v.w.ei - (s.len - n)) ⋆
        v.uW ctx ⋆ v.nR ⋆ v.cR ctx ⋆ v.tR v.w.ei v.w.tail ⋆ Junk ⋆ v.F CI ctx)) (by ac_rfl) h
      have h2 := sep_mono_left (Q := up (regionIn s.ptr v.A' v.S' v.K' (2 ^ k) (bs.extract 0 n.toNat)) ⋆
        up (regionIn (s.ptr.add n.toNat) v.A' v.S' v.K' 1 (bs.extract n.toNat bs.size)))
        (fun _ x => up_region_split hle x) h1
      have h3 := of_eq (Q := up (regionIn s.ptr v.A' v.S' v.K' (2 ^ k) (bs.extract 0 n.toNat)) ⋆
        ((up (regionIn (s.ptr.add n.toNat) v.A' v.S' v.K' 1 (bs.extract n.toNat bs.size)) ⋆
          v.tR v.w.ei v.w.tail) ⋆
        (gauth γ e (v.w.M.set v.i (some (s.ptr, n.toNat))) ⋆ gfrag γ e v.i (s.ptr, n.toNat) ⋆
          apts (v.N.add 8) (BitVec.ofNat 64 v.w.ei - (s.len - n)) ⋆ v.uW ctx ⋆ v.nR ⋆ v.cR ctx ⋆
          Junk ⋆ v.F CI ctx))) (by ac_rfl) h2
      have h4 := sep_mono_right (R := up (regionIn (v.N.add (24 + ((v.w.ei - (bs.size - n.toNat) : Nat) : Int)))
          v.w.A v.w.S v.w.K 1 (bs.extract n.toNat bs.size ++ v.w.tail)) ⋆
        (gauth γ e (v.w.M.set v.i (some (s.ptr, n.toNat))) ⋆ gfrag γ e v.i (s.ptr, n.toNat) ⋆
          apts (v.N.add 8) (BitVec.ofNat 64 v.w.ei - (s.len - n)) ⋆ v.uW ctx ⋆ v.nR ⋆ v.cR ctx ⋆
          Junk ⋆ v.F CI ctx))
        (fun _ x => sep_mono_left (fun _ y => hjoin _ y) x) h3
      have hsz : (bs.extract 0 n.toNat).size = n.toNat := by simp; omega
      refine resizePost_true (w := { v.w with M := v.w.M.set v.i (some (s.ptr, n.toNat)), ei := v.w.ei - (bs.size - n.toNat), tail := bs.extract n.toNat bs.size ++ v.w.tail })
        ⟨hc16, hfin.set _ _, by
          simp only [OV.FirstFacts, hfirst]
          exact ⟨hnf, by omega, by simp only [Array.size_append, Array.size_extract, htail]; omega⟩⟩
        hsz (keepsPrefix_extract _ _) (A := v.A') (S := v.S') (K := v.K') (i := v.i) (of_eq ?_ h4)
      rw [hsz, hnew]
      simp only [OV.body, FirstPart, hfirst, Header, FV.uW, FV.nR, FV.cR, FV.F]
      ac_rfl
    · -- growth into the tail, when the tail has room
      simp only [hle, decide_false, Bool.false_eq_true, ↓reduceIte]
      have hlt : s.len.toNat ≤ n.toNat := by rw [hlen]; omega
      have hd : (n - s.len).toNat = n.toNat - bs.size := by rw [BitVec.toNat_sub_of_le hlt, hlen]
      refine CTriple.pre (P := apts v.N (BitVec.ofNat 64 v.w.sz) ⋆ (v.uW ctx ⋆ v.eW v.w.ei ⋆ v.gA γ e ⋆ gfrag γ e v.i (s.ptr, bs.size) ⋆ v.nR ⋆ v.cR ctx ⋆
          v.tR v.w.ei v.w.tail ⋆ v.rg s k bs ⋆ Junk ⋆ (CI.tok v.N v.w.sz 3 v.w.A v.w.S v.w.K ⋆
          aptsE (ctx.add 24) v.w.fl ⋆ CI.own ⋆ UsedRest CI v.w.nxt ⋆ FreeList CI v.w.fl))) ?_
        (fun r h => of_eq (by simp only [FV.L, FV.R0, FV.F]; ac_rfl) h)
      refine CTriple.bind (loadBuf_ct (R := (v.uW ctx ⋆ v.eW v.w.ei ⋆ v.gA γ e ⋆ gfrag γ e v.i (s.ptr, bs.size) ⋆ v.nR ⋆ v.cR ctx ⋆
          v.tR v.w.ei v.w.tail ⋆ v.rg s k bs ⋆ Junk ⋆ (CI.tok v.N v.w.sz 3 v.w.A v.w.S v.w.K ⋆
          aptsE (ctx.add 24) v.w.fl ⋆ CI.own ⋆ UsedRest CI v.w.nxt ⋆ FreeList CI v.w.fl))) hbN hnf.off0 hnf.hdr hnf.even (by omega)
        (fun m r rF hh hp hs => ?_)) fun sl => CTriple.lift fun hsl => ?_
      · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, -⟩ := hmem m r rF hh
          (of_eq (by simp only [FV.L, FV.R0, FV.F]; ac_rfl) hp) hs
        exact ⟨blkN, e2, by rw [s2]; exact hnf.fit⟩
      subst hsl
      refine CTriple.pre (P := v.L CI γ e ctx s k bs) ?_
        (fun r h => of_eq (by simp only [FV.L, FV.R0, FV.F]; ac_rfl) h)
      rw [Zig.sub_unsigned_of_le hlt]
      conc_norm
      have hroom : (Zig.subSat false (BitVec.ofNat 64 (v.w.sz - 24)) (BitVec.ofNat 64 v.w.ei)).toNat =
          v.w.sz - 24 - v.w.ei := by
        rw [subSat_toNat, hei64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      simp only [Zig.ge, le_eq, hroom, hd]
      by_cases hfit : n.toNat - bs.size ≤ v.w.sz - 24 - v.w.ei
      · simp only [hfit, decide_true, ↓reduceIte]
        have hadd : (BitVec.ofNat 64 v.w.ei).toNat + (n - s.len).toNat < 2 ^ 64 := by
          rw [hei64, hd]; omega
        have hd2 : (BitVec.ofNat 64 v.w.ei + (n - s.len)).toNat = v.w.ei + (n.toNat - bs.size) := by
          rw [BitVec.toNat_add_of_lt hadd, hei64, hd]
        rw [Zig.add_unsigned_of_lt hadd]
        conc_norm
        refine CTriple.pureStep (v := (v.N.add 24).add (v.w.ei + (n.toNat - bs.size) : Nat))
          (fun m r rF hh hp hs => ?_) ?_
        · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, -⟩ := hmem m r rF hh hp hs
          rw [ptrProject_elem_run hbN' e2 (by simp [Ptr.add]; omega) (by simp [Ptr.add, hd2]; omega), hd2]
        refine CTriple.pureStep (v := s.ptr.add n.toNat) (fun m r rF hh hp hs => ?_) ?_
        · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, hsl, -⟩ := hmem m r rF hh hp hs
          rw [ptrProject_elem_run hbp e3 hp0 (by omega)]
        refine CTriple.pureStep (v := true) (fun m r rF hh hp hs => ?_) ?_
        · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, -⟩ := hmem m r rF hh hp hs
          rw [ptrEqAddr_run (by simpa [Ptr.add] using hbN) e2 (by simpa [Ptr.add] using hbp) e3, a2, a3, hA]
          have hx : (v.w.A : Int) + (v.N.off + 24 + ((v.w.ei + (n.toNat - bs.size) : Nat) : Int)) =
              v.w.A + (s.ptr.off + n.toNat) := by omega
          simp only [Ptr.add, hx, decide_true]
        rw [debug_assert_true]
        conc_norm
        refine CTriple.pureStep (v := v.N.add 8) (fun m r rF hh hp hs => ?_) ?_
        · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, -⟩ := hmem m r rF hh hp hs
          exact ptrProject_add_run' hbN e2 hnf.off0 (by decide) (by omega)
        refine CTriple.pick_bind ?_
        refine CTriple.pre (P := v.eW v.w.ei ⋆ (v.uW ctx ⋆ v.R0 CI γ e ctx s k bs)) ?_
          (fun r h => of_eq (sep_left_comm_eq _ _ _) h)
        refine CTriple.bind (CTriple.liftMem ((FTriple.cmpxchgHit (v.N.add 8) (BitVec.ofNat 64 v.w.ei)
          (BitVec.ofNat 64 v.w.ei + (n - s.len)) _ _).frame)) fun res => ?_
        refine CTriple.pre (CTriple.lift (P := apts (v.N.add 8) (BitVec.ofNat 64 v.w.ei + (n - s.len)) ⋆
          (v.uW ctx ⋆ v.R0 CI γ e ctx s k bs)) fun hres => ?_) (fun r h => sep_assoc h)
        subst hres
        simp only [Option.isNone_none]
        have hnew : BitVec.ofNat 64 v.w.ei + (n - s.len) = BitVec.ofNat 64 (v.w.ei + (n.toNat - bs.size)) := by
          apply BitVec.eq_of_toNat_eq; rw [hd2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]; omega
        refine CTriple.upd (Upd.trans (Upd.of_imp fun r h => of_eq (by
            simp only [FV.R0, FV.gA]; ac_rfl) h)
          (Upd.frame (R := apts (v.N.add 8) (BitVec.ofNat 64 v.w.ei + (n - s.len)) ⋆ v.uW ctx ⋆ v.nR ⋆
            v.cR ctx ⋆ v.rg s k bs ⋆ v.tR v.w.ei v.w.tail ⋆ Junk ⋆ v.F CI ctx)
            (Upd.reassign (s.ptr, n.toNat)))) ?_
        refine CTriple.ret' true fun r h => ?_
        -- the slice grows into the first `n - len` bytes of the tail
        have hend : s.ptr.add bs.size = v.N.add (24 + (v.w.ei : Int)) := by
          have hb' : s.ptr.block = v.N.block := by rw [hbp, hbN, hb]
          have ho : s.ptr.off + bs.size = v.N.off + (24 + (v.w.ei : Int)) := by omega
          simp only [Ptr.add]; rw [hb', ho]
        have hnt : (v.N.add (24 + (v.w.ei : Int))).add ((n.toNat - bs.size : Nat) : Int) =
            v.N.add (24 + ((v.w.ei + (n.toNat - bs.size) : Nat) : Int)) := by
          simp only [Ptr.add, Ptr.mk.injEq, true_and]; omega
        have hgrow : ∀ r, (v.rg s k bs ⋆ v.tR v.w.ei v.w.tail) r →
            (up (regionIn s.ptr v.A' v.S' v.K' (2 ^ k) (bs ++ v.w.tail.extract 0 (n.toNat - bs.size))) ⋆
              up (regionIn (v.N.add (24 + ((v.w.ei + (n.toNat - bs.size) : Nat) : Int))) v.w.A v.w.S v.w.K
                1 (v.w.tail.extract (n.toNat - bs.size) v.w.tail.size))) r := by
          intro r hr
          have h1 := sep_assoc' (sep_mono_right (Q := v.tR v.w.ei v.w.tail)
            (R := up (regionIn (v.N.add (24 + (v.w.ei : Int))) v.w.A v.w.S v.w.K 1
                (v.w.tail.extract 0 (n.toNat - bs.size))) ⋆
              up (regionIn ((v.N.add (24 + (v.w.ei : Int))).add ((n.toNat - bs.size : Nat) : Int)) v.w.A v.w.S v.w.K 1
                (v.w.tail.extract (n.toNat - bs.size) v.w.tail.size)))
            (fun _ x => up_region_split (bs := v.w.tail) (n := n.toNat - bs.size) (by omega) x) hr)
          rw [hnt] at h1
          refine sep_mono_left (fun r x => ?_) h1
          obtain ⟨⟨h₁, h₂, hd₁, he, x1, x2⟩, hk, hg⟩ := sep_up x
          refine ⟨?_, hk, hg⟩
          rw [he]
          rw [← hend, ← hA, ← hS, ← hK] at x2
          exact regionIn_join (a' := 1) ⟨h₁, h₂, hd₁, rfl, x1, x2⟩
        have h1 := of_eq (Q := (v.rg s k bs ⋆ v.tR v.w.ei v.w.tail) ⋆
          (gauth γ e (v.w.M.set v.i (some (s.ptr, n.toNat))) ⋆ gfrag γ e v.i (s.ptr, n.toNat) ⋆
            apts (v.N.add 8) (BitVec.ofNat 64 v.w.ei + (n - s.len)) ⋆ v.uW ctx ⋆ v.nR ⋆ v.cR ctx ⋆
            Junk ⋆ v.F CI ctx)) (by ac_rfl) h
        have h2 := sep_mono_left hgrow h1
        have hsz : (bs ++ v.w.tail.extract 0 (n.toNat - bs.size)).size = n.toNat := by simp; omega
        refine resizePost_true (w := { v.w with M := v.w.M.set v.i (some (s.ptr, n.toNat)), ei := v.w.ei + (n.toNat - bs.size), tail := v.w.tail.extract (n.toNat - bs.size) v.w.tail.size })
          ⟨hc16, hfin.set _ _, by
            simp only [OV.FirstFacts, hfirst]
            exact ⟨hnf, by omega, by simp only [Array.size_extract, htail]; omega⟩⟩
          hsz (keepsPrefix_append _ _) (A := v.A') (S := v.S') (K := v.K') (i := v.i) (of_eq ?_ h2)
        rw [hsz, hnew]
        simp only [OV.body, FirstPart, hfirst, Header, FV.uW, FV.nR, FV.cR, FV.F]
        ac_rfl
      · simp only [hfit, decide_false, Bool.false_eq_true, ↓reduceIte]
        refine CTriple.ret' false fun r h => resizePost_false (w := v.w) ⟨hc16, hfin, by
          simp only [OV.FirstFacts, hfirst]; exact ⟨hnf, hei, htail⟩⟩ (A := v.A') (S := v.S') (K := v.K')
          (i := v.i) (of_eq ?_ h)
        simp only [OV.body, FirstPart, hfirst, Header, FV.L, FV.R0, FV.gA, FV.uW, FV.eW, FV.nR, FV.cR,
          FV.tR, FV.rg, FV.F]
        ac_rfl
  · -- not the first node's last allocation: only a shrink succeeds; the cut bytes become junk
    simp only [heq, decide_false, Bool.not_false, ↓reduceIte, le_eq, hlen]
    by_cases hle : n.toNat ≤ bs.size
    · simp only [hle, decide_true]
      refine CTriple.upd (Upd.trans (Upd.of_imp fun r h => of_eq (by
          simp only [FV.L, FV.R0, FV.gA]; ac_rfl) h) (Upd.frame (R := v.uW ctx ⋆ v.eW v.w.ei ⋆
            v.nR ⋆ v.cR ctx ⋆ v.tR v.w.ei v.w.tail ⋆ v.rg s k bs ⋆ Junk ⋆ v.F CI ctx)
            (Upd.reassign (s.ptr, n.toNat)))) ?_
      refine CTriple.ret' true fun r h => ?_
      have h1 := of_eq (Q := v.rg s k bs ⋆ (gauth γ e (v.w.M.set v.i (some (s.ptr, n.toNat))) ⋆
        gfrag γ e v.i (s.ptr, n.toNat) ⋆ v.uW ctx ⋆ v.eW v.w.ei ⋆ v.nR ⋆ v.cR ctx ⋆
        v.tR v.w.ei v.w.tail ⋆ Junk ⋆ v.F CI ctx)) (by ac_rfl) h
      have h2 := sep_mono_left (Q := up (regionIn s.ptr v.A' v.S' v.K' (2 ^ k) (bs.extract 0 n.toNat)) ⋆
        up (regionIn (s.ptr.add n.toNat) v.A' v.S' v.K' 1 (bs.extract n.toNat bs.size)))
        (fun _ x => up_region_split hle x) h1
      have h3 := of_eq (Q := up (regionIn s.ptr v.A' v.S' v.K' (2 ^ k) (bs.extract 0 n.toNat)) ⋆
        ((up (regionIn (s.ptr.add n.toNat) v.A' v.S' v.K' 1 (bs.extract n.toNat bs.size)) ⋆ Junk) ⋆
        (gauth γ e (v.w.M.set v.i (some (s.ptr, n.toNat))) ⋆ gfrag γ e v.i (s.ptr, n.toNat) ⋆
          v.uW ctx ⋆ v.eW v.w.ei ⋆ v.nR ⋆ v.cR ctx ⋆ v.tR v.w.ei v.w.tail ⋆ v.F CI ctx)))
        (by ac_rfl) h2
      have h4 := sep_mono_right (R := Junk ⋆ (gauth γ e (v.w.M.set v.i (some (s.ptr, n.toNat))) ⋆
          gfrag γ e v.i (s.ptr, n.toNat) ⋆ v.uW ctx ⋆ v.eW v.w.ei ⋆ v.nR ⋆ v.cR ctx ⋆
          v.tR v.w.ei v.w.tail ⋆ v.F CI ctx))
        (fun _ x => sep_mono_left (Q := Junk) (fun _ y => junk_absorb y) x) h3
      have hsz : (bs.extract 0 n.toNat).size = n.toNat := by simp; omega
      refine resizePost_true (w := { v.w with M := v.w.M.set v.i (some (s.ptr, n.toNat)) })
        ⟨hc16, hfin.set _ _, by simp only [OV.FirstFacts, hfirst]; exact ⟨hnf, hei, htail⟩⟩ hsz
        (keepsPrefix_extract _ _) (A := v.A') (S := v.S') (K := v.K') (i := v.i) (of_eq ?_ h4)
      rw [hsz]
      simp only [OV.body, FirstPart, hfirst, Header, FV.uW, FV.eW, FV.nR, FV.cR, FV.tR, FV.F]
      ac_rfl
    · simp only [hle, decide_false]
      refine CTriple.ret' false fun r h => resizePost_false (w := v.w) ⟨hc16, hfin, by
        simp only [OV.FirstFacts, hfirst]; exact ⟨hnf, hei, htail⟩⟩ (A := v.A') (S := v.S') (K := v.K')
        (i := v.i) (of_eq ?_ h)
      simp only [OV.body, FirstPart, hfirst, Header, FV.L, FV.R0, FV.gA, FV.uW, FV.eW, FV.nR, FV.cR,
        FV.tR, FV.rg, FV.F]
      ac_rfl

/-- `remap` is `resize`, and returns `memory.ptr` when it succeeds. -/
theorem remap_ct (CI : FAllocInv) (γ e : Nat) (ctx s : _) (k : Nat) (n ra : BitVec 64)
    (bs : Array Byte) (hlen : s.len.toNat = bs.size) (hpos : 0 < bs.size) (hn : 0 < n.toNat) :
    CTriple (Tgt := Tgt) ((inv CI γ e ctx).own ⋆ (inv CI γ e ctx).granted s.ptr k bs)
      (heap_ArenaAllocator_remap ctx s ⟨BitVec.ofNat 6 k⟩ n ra)
      ((inv CI γ e ctx).remapPost s.ptr k bs n.toNat) := by
  unfold heap_ArenaAllocator_remap
  conc_norm
  refine CTriple.bind (resize_ct CI γ e ctx s k n ra bs hlen hpos hn) fun b => ?_
  cases b
  · exact CTriple.ret' _ fun _ h => h
  · exact CTriple.ret' _ fun _ h => h

end ResizeProof

/-- **`resize` meets `FAllocSpec`'s `resize` field** for the arena invariant at every epoch, every
child invariant `CI`, and every depth of the one-thread reading. -/
theorem resize_spec (CI : FAllocInv) (γ e : Nat) (ctx : Ptr) (fuel : Nat) (s : Slice) (k : Nat)
    (n ra : BitVec 64) (bs : Array Byte) (hlen : s.len.toNat = bs.size) (hpos : 0 < bs.size)
    (hn : 0 < n.toNat) :
    FLogic.partial.T ((inv CI γ e ctx).own ⋆ (inv CI γ e ctx).granted s.ptr k bs)
      (Sched.soloRun fuel (heap_ArenaAllocator_resize ctx s ⟨BitVec.ofNat 6 k⟩ n ra))
      ((inv CI γ e ctx).resizePost s.ptr k bs n.toNat) :=
  resize_ct CI γ e ctx s k n ra bs hlen hpos hn fuel

/-- **`remap` meets `FAllocSpec`'s `remap` field.** -/
theorem remap_spec (CI : FAllocInv) (γ e : Nat) (ctx : Ptr) (fuel : Nat) (s : Slice) (k : Nat)
    (n ra : BitVec 64) (bs : Array Byte) (hlen : s.len.toNat = bs.size) (hpos : 0 < bs.size)
    (hn : 0 < n.toNat) :
    FLogic.partial.T ((inv CI γ e ctx).own ⋆ (inv CI γ e ctx).granted s.ptr k bs)
      (Sched.soloRun fuel (heap_ArenaAllocator_remap ctx s ⟨BitVec.ofNat 6 k⟩ n ra))
      ((inv CI γ e ctx).remapPost s.ptr k bs n.toNat) :=
  remap_ct CI γ e ctx s k n ra bs hlen hpos hn fuel

end AllocArena.ArenaSpec

#print axioms AllocArena.ArenaSpec.free_spec
#print axioms AllocArena.ArenaSpec.resize_spec
#print axioms AllocArena.ArenaSpec.remap_spec
