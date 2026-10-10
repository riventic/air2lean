import AllocArena.ArenaLinux
import ZigLean.Sep.AllocSpec.Region
import ZigLean.Sep.AllocSpec.Ops
import ZigLean.Sep.Full.AllocSpec
import ZigLean.Sep.Full.Conc
import ZigLean.Sep.Full.AtomicRules
import ZigLean.Sep.Full.Ghost
import ZigLean.Range

/-!
# The translated `ArenaAllocator`'s `free` against `FAllocSpec` (allocator milestone 2)

`free_spec`: the `free` entry of the translated `std.heap.ArenaAllocator` (Zig 0.16.0,
x86_64-linux, `AllocArena/ArenaLinux.lean`) meets `FAllocSpec`'s `free` contract for the arena
invariant `inv CI γ e ctx` below, read in the caller's thread (`CTriple`, `Sched.soloRun`), from
the generated code only. No model of the arena is used.

**The invariant** `own CI γ e ctx` (for a child allocator invariant `CI`, ghost name `γ`, epoch `e`):

* the arena struct at `ctx`: the child allocator (16 bytes, not read here), `used_list` and
  `free_list` as pointer-valued atomic words (`aptsE`);
* the ghost authority `gauth γ e n`: `n` grants of epoch `e` outstanding
  (`docs/sep-full-state.md` §Ghost state);
* the first node of `used_list`, if any (`FirstPart`): its header words (`size` and `end_index`
  atomic, `next` plain), the unused tail of its buffer (from `end_index` on), and the child's
  token for the node; the other used nodes and the free list (`Chain`): headers and tokens, the
  free nodes with their whole buffers;
* the child's state `CI.own`, and `Junk`: bytes that frees which were not the last allocation
  leaked back (any bytes; the arena never touches them until `reset`).

With no first node, `n = 0`. A token is `gfrag γ e`, so a token of the current epoch shows `n ≥ 1`
(`gfrag_count`), hence a first node: **O-A is excluded by ghost state**, not by a premise. A
token of an older epoch (after `reset`) is stale: it belongs to `inv … e'` for `e' < e`, whose
`own` needs the authority of epoch `e'`, which no longer exists.

**`free`** loads the first node, compares `buf + end_index` with the slice's end by address
(`ptrEqAddr`), and on a match moves `end_index` back by a strong `cmpxchg`. The comparison is
decided by ownership alone (O-F): a slice of another block lies at disjoint addresses
(`FTriple.apart`, `Mem.LiveDisjoint` in `Mem.FSeq`), and a slice of the node's block that ends at
`buf + end_index` lies past the header, which the arena owns. On a match the slice's bytes rejoin
the tail; otherwise they become junk. Either way the token is retired (`Upd.retire`).

**O-E** (`ArenaObstruction.oob_free_illegal`): the invariant keeps `end_index` within the first
node's buffer (`OV.Facts`: `24 + ei ≤ sz`). A failed `alloc` leaves it past the buffer, so the reachable
states this specification covers end at the first failed `alloc`.
-/

namespace AllocArena.ArenaSpec

open Zig Zig.Region Zig.Full Zig.Full.FAssn AllocArena.ArenaLinux

/-! ## Steps that do not change the memory -/

section Steps

variable {α β : Type} {P : FAssn} {Q : β → FAssn}

/-- A `MemM` step that returns `v` and leaves the memory as it is. -/
theorem CTriple.pureStep {c : MemM α} {v : α} {f : α → ConcM Tgt β}
    (hc : ∀ m r rF, Holds m r rF → P r → m.FSeq → c.run m = pure (v, m))
    (hf : CTriple P (f v) Q) : CTriple P (ConcM.liftMem c >>= f) Q := by
  refine CTriple.bind (Q := fun w => ⟪w = v⟫ ⋆ P) (CTriple.liftMem (FTriple.of_run
    fun m r rF hh hp hs => ⟨v, m, r, hc m r rF hh hp hs, hh, sep_lift.mpr ⟨rfl, hp⟩, hs⟩)) ?_
  intro w
  exact CTriple.lift fun hw => hw ▸ hf

/-- Facts that hold of every memory holding `P` (and stay true: no memory in them). -/
theorem CTriple.facts {x : ConcM Tgt β} {φ : Prop}
    (hφ : ∀ m r rF, Holds m r rF → P r → m.FSeq → φ) (h : φ → CTriple P x Q) : CTriple P x Q :=
  fun n m r rF hh hp hs => h (hφ m r rF hh hp hs) n m r rF hh hp hs

end Steps

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
  aptsE N (BitVec.ofNat 64 sz) ⋆ apts (N.add 8) ei ⋆
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
lists' heads, the ghost count `n`, and the first node (`nxt`, `A`, `S`, `K`, `sz`, `ei`, `tail`;
unused without one). -/
structure OV where
  Ac : Nat
  Sc : Nat
  Kc : BlockKind
  cbs : Array Byte
  first : Option Ptr
  fl : Option Ptr
  n : Nat
  nxt : Option Ptr
  A : Nat
  S : Nat
  K : BlockKind
  sz : Nat
  ei : Nat
  tail : Array Byte

/-- The facts of the arena's variables. -/
def OV.Facts (w : OV) : Prop :=
  w.cbs.size = 16 ∧ match w.first with
    | none => w.n = 0
    | some N => NodeFacts N w.A w.S w.sz ∧ 24 + w.ei ≤ w.sz ∧ w.tail.size = w.sz - 24 - w.ei

/-- The first node of `used_list`: header and token, and the unused tail of its buffer. -/
def FirstPart (CI : FAllocInv) (w : OV) : FAssn :=
  match w.first with
  | none => FAssn.emp
  | some N => Header CI N w.A w.S w.K w.sz (BitVec.ofNat 64 w.ei) w.nxt ⋆
      up (regionIn (N.add (24 + w.ei)) w.A w.S w.K 1 w.tail)

/-- The arena's resources. -/
def OV.body (CI : FAllocInv) (γ e : Nat) (ctx : Ptr) (w : OV) : FAssn :=
  up (regionIn ctx w.Ac w.Sc w.Kc 8 w.cbs) ⋆ aptsE (ctx.add 16) w.first ⋆ aptsE (ctx.add 24) w.fl ⋆
    gauth γ e w.n ⋆ CI.own ⋆ Junk ⋆ FirstPart CI w ⋆ UsedRest CI w.nxt ⋆ FreeList CI w.fl

/-- The arena's state (module doc). -/
def own (CI : FAllocInv) (γ e : Nat) (ctx : Ptr) : FAssn :=
  FAssn.ex fun w : OV => ⟪w.Facts⟫ ⋆ w.body CI γ e ctx

/-- The arena's invariant at epoch `e`: its tokens are the ghost tokens of epoch `e`. -/
def inv (CI : FAllocInv) (γ e : Nat) (ctx : Ptr) : FAllocInv where
  own := own CI γ e ctx
  tok _ _ _ _ _ _ := gfrag γ e

/-! ## Rules -/

/-- A ghost update of a `CTriple`'s precondition (`FTriple.upd`). -/
theorem CTriple.upd {β : Type} {P P' : FAssn} {x : ConcM Tgt β} {Q : β → FAssn} (hu : Upd P P')
    (ht : CTriple P' x Q) : CTriple P x Q := fun n => FTriple.upd hu (ht n)

/-- An entailment that may use the memory (`Holds`, `FSeq`). -/
theorem CTriple.preM {β : Type} {P P' : FAssn} {x : ConcM Tgt β} {Q : β → FAssn}
    (hp : ∀ m r rF, Holds m r rF → P r → m.FSeq → P' r) (ht : CTriple P' x Q) : CTriple P x Q :=
  fun n m r rF hh h hs => ht n m r rF hh (hp m r rF hh h hs) hs

/-! ## `free` -/

/-- The variables of `free`'s precondition on an arena with a first node `N` (block `bN`), a
slice in block `bp`, and the struct in block `bc`. -/
structure FV where
  w : OV
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
def FV.gA (v : FV) : FAssn := gauth γ e v.w.n
def FV.uW (v : FV) : FAssn := aptsE (ctx.add 16) (some v.N)
def FV.eW (v : FV) (ei : Nat) : FAssn := apts (v.N.add 8) (BitVec.ofNat 64 ei)
def FV.nR (v : FV) : FAssn := up (regionIn (v.N.add 16) v.w.A v.w.S v.w.K 8 (Enc.encode v.w.nxt))
def FV.cR (v : FV) : FAssn := up (regionIn ctx v.w.Ac v.w.Sc v.w.Kc 8 v.w.cbs)
def FV.tR (v : FV) (ei : Nat) (tail : Array Byte) : FAssn :=
  up (regionIn (v.N.add (24 + ei)) v.w.A v.w.S v.w.K 1 tail)
def FV.rg (v : FV) : FAssn := up (regionIn s.ptr v.A' v.S' v.K' (2 ^ k) bs)
/-- What `free` does not touch. -/
def FV.F (v : FV) : FAssn :=
  aptsE v.N (BitVec.ofNat 64 v.w.sz) ⋆ CI.tok v.N v.w.sz 3 v.w.A v.w.S v.w.K ⋆
    aptsE (ctx.add 24) v.w.fl ⋆ CI.own ⋆ UsedRest CI v.w.nxt ⋆ FreeList CI v.w.fl

/-- What `free`'s steps do not change before the `cmpxchg`, besides the two words. -/
def FV.R0 (v : FV) : FAssn :=
  v.gA γ e ⋆ gfrag γ e ⋆ v.nR ⋆ v.cR ctx ⋆ v.tR v.w.ei v.w.tail ⋆ v.rg s k bs ⋆ Junk ⋆ v.F CI ctx

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
  -- hp : ((up rg ⋆ gfrag) ⋆ body) r
  cases hfirst : w.first with
  | none =>
    exfalso
    have hn : w.n = 0 := by have := hwf.2; rw [hfirst] at this; exact this
    have hp' := of_eq (Q := (gauth γ e w.n ⋆ gfrag γ e) ⋆ (up (regionIn s.ptr A' S' K' (2 ^ k) bs) ⋆
      up (regionIn ctx w.Ac w.Sc w.Kc 8 w.cbs) ⋆ aptsE (ctx.add 16) w.first ⋆ aptsE (ctx.add 24) w.fl ⋆
      CI.own ⋆ Junk ⋆ FirstPart CI w ⋆ UsedRest CI w.nxt ⋆ FreeList CI w.fl))
      (by simp only [OV.body, inv]; ac_rfl) hp
    obtain ⟨r₁, r₂, -, rfl, h1, -⟩ := hp'
    have := gfrag_count h1 (Ghost.Ok.assoc.mp hh.ghost)
    omega
  | some N =>
    have hwf' := hwf.2
    rw [hfirst] at hwf'
    -- the shape with dummy block ids, to read the blocks off the regions
    have hL : ∀ bc bN bp, (FV.L CI γ e ctx s k bs ⟨w, N, bc, bN, bp, A', S', K'⟩) r := by
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
    exact ⟨⟨w, N, bc, bN, bp, A', S', K'⟩, sep_lift.mpr ⟨⟨hwf, hfirst, hbc, by simpa [Ptr.add] using hbN,
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

/-! ## Reading a word in the middle of a precondition -/

/-- A step on the part `X` of `P = X ⋆ R` that returns `v` and keeps `X`. -/
theorem CTriple.readStep {α β : Type} {P X R : FAssn} {c : MemM α} {v : α} {f : α → ConcM Tgt β}
    {Q : β → FAssn} (ht : FTriple X c (fun w => ⟪w = v⟫ ⋆ X)) (hP : P = (X ⋆ R))
    (hf : CTriple P (f v) Q) : CTriple P (ConcM.liftMem c >>= f) Q := by
  subst hP
  refine CTriple.bind (CTriple.liftMem ht.frame) fun w => ?_
  refine CTriple.pre (CTriple.lift fun hw => hw ▸ hf) fun _ h => sep_assoc h

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
  obtain ⟨⟨hc16, -⟩, -, hbc, hbN, hbp, -, -, hpos, -⟩ := hv
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

theorem debug_assert_true : debug_assert true = pure () := rfl

/-- `free`'s run, case by case (module doc). -/
theorem free_ct (CI : FAllocInv) (γ e : Nat) (ctx s : _) (k : Nat) (ra : BitVec 64) (bs : Array Byte)
    (hlen : s.len.toNat = bs.size) (hpos : 0 < bs.size) :
    CTriple (Tgt := Tgt) ((inv CI γ e ctx).own ⋆ (inv CI γ e ctx).granted s.ptr k bs)
      (heap_ArenaAllocator_free ctx s ⟨BitVec.ofNat 6 k⟩ ra) (fun _ => (inv CI γ e ctx).own) := by
  refine CTriple.preM (fun m r rF hh hp hs => free_pre hh hlen hpos hp) ?_
  refine CTriple.ex fun v => CTriple.lift fun hv => ?_
  have hv' := hv
  obtain ⟨⟨hc16, hwf⟩, hfirst, hbc, hbN, hbp, hac, -, -, hc0, hp0⟩ := hv'
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
    refine CTriple.facts (φ := v.bp = v.bN ∧ v.A' = v.w.A ∧ v.S' = v.w.S ∧ v.K' = v.w.K ∧
        v.N.off.toNat + 24 ≤ s.ptr.off.toNat ∧
        s.ptr.off.toNat + bs.size = v.N.off.toNat + 24 + v.w.ei) (fun m r rF hh hp hs => ?_) ?_
    · obtain ⟨blkC, blkN, blkP, e1, a1, s1, e2, a2, s2, e3, a3, s3, hsl, hap, hsame⟩ :=
        hmem m r rF hh hp hs
      have hf := hnf.fit
      have h0 := hnf.off0
      by_cases hb : v.bp = v.bN
      · obtain ⟨hA, hS, hK⟩ := hsame hb
        rw [hA] at heq
        have hoff : s.ptr.off.toNat + bs.size = v.N.off.toNat + 24 + v.w.ei := by omega
        have hr := of_eq (Q := (v.nR ⋆ v.rg s k bs) ⋆ (v.uW ctx ⋆ v.eW v.w.ei ⋆ v.gA γ e ⋆ gfrag γ e ⋆
          v.cR ctx ⋆ v.tR v.w.ei v.w.tail ⋆ Junk ⋆ v.F CI ctx)) (by simp only [FV.L, FV.R0]; ac_rfl) hp
        obtain ⟨_, _, -, -, hr, -⟩ := hr
        have := region_apart (by simpa [Ptr.add] using hbN) (hb ▸ hbp)
          (by rw [encode_nxt_size]; decide) hpos hr
        rw [encode_nxt_size] at this
        simp only [Ptr.add] at this
        exact ⟨hb, hA, hS, hK, by omega, hoff⟩
      · rcases hap hb with h | h <;> omega
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
    have h' := of_eq (Q := (v.rg s k bs ⋆ v.tR v.w.ei v.w.tail) ⋆ (gauth γ e (v.w.n - 1) ⋆
      apts (v.N.add 8) (BitVec.ofNat 64 v.w.ei - s.len) ⋆ v.uW ctx ⋆ v.nR ⋆ v.cR ctx ⋆ Junk ⋆
      v.F CI ctx)) (by ac_rfl) h
    have h'' := sep_mono_left hjoin h'
    refine ⟨{ v.w with n := v.w.n - 1, ei := v.w.ei - bs.size, tail := bs ++ v.w.tail },
      sep_lift.mpr ⟨⟨hc16, ?_⟩, of_eq ?_ h''⟩⟩
    · simp only [hfirst]
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
    have h' := of_eq (Q := (v.rg s k bs ⋆ Junk) ⋆ (gauth γ e (v.w.n - 1) ⋆ v.uW ctx ⋆ v.eW v.w.ei ⋆
      v.nR ⋆ v.cR ctx ⋆ v.tR v.w.ei v.w.tail ⋆ v.F CI ctx)) (by ac_rfl) h
    have h'' := sep_mono_left (Q := Junk) (fun _ x => junk_absorb x) h'
    refine ⟨{ v.w with n := v.w.n - 1 }, sep_lift.mpr ⟨⟨hc16, ?_⟩, of_eq ?_ h''⟩⟩
    · simp only [hfirst]; exact ⟨hnf, hei, htail⟩
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

end AllocArena.ArenaSpec

#print axioms AllocArena.ArenaSpec.free_spec
