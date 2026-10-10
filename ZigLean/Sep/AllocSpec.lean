import ZigLean.Sep.AllocSpec.Region
import ZigLean.Sep.Full.Triple

/-!
# A generic allocator specification

`AllocSpec L vt ctx I` states what the four entries of a Zig 0.16.0 `std.mem.Allocator.VTable`
must do, for the allocator with context pointer `ctx`, as Hoare triples in the logic `L`
(partial `Triple` or total `TotalTriple`). It is stated over an abstract allocator invariant
`I.own` (the allocator's own state and its free memory) and region permissions (byte ranges,
`ZigLean/Sep/AllocSpec/Region.lean`), so that any allocator — a page allocator over `mmap`, a
fixed buffer, an arena, a user's own allocator — can be proved against it, and every client of
`std.mem.Allocator` can be proved once for every allocator that satisfies it
(`ZigLean/Sep/AllocSpec/Wrappers.lean`). `docs/alloc-spec.md` has the design.

The entries, as in `lib/std/mem/Allocator.zig` (alignment is `mem.Alignment`, a `u6` log2
value, here the `Nat` `k` with byte alignment `2 ^ k`; `ret_addr` is unconstrained):

* `alloc(ctx, len, k, ret_addr) ?[*]u8`: `null`, and the invariant holds again; or a region of
  `len` bytes (unspecified contents) at a `2 ^ k`-aligned address, with its grant token.
* `resize(ctx, memory, k, new_len, ret_addr) bool`: `true`, and the region at the same pointer
  now has `new_len` bytes with the common prefix kept; or `false` and nothing changed.
* `remap(ctx, memory, k, new_len, ret_addr) ?[*]u8`: `null` and nothing changed; or the region
  at the returned (maybe moved) pointer has `new_len` bytes, common prefix kept.
* `free(ctx, memory, k, ret_addr) void`: consumes the region and its token.

`memory` must be the whole last granted region (`memory.len` is its length, which is positive)
with the alignment it was allocated with: the precondition `granted I memory.ptr k bs`. The
token `I.tok p n k A S K` is the allocator's evidence that it issued the `n`-byte region at `p`
with alignment `k` from the block with address `A`, size `S` and kind `K` (a fact about the
buffer it lies in, the rest of a page mapping, …). It is part of the specification because a free
of a region that the allocator did not issue is illegal in Zig even if the caller owns the bytes,
and it sees the region's block so that it can pin which block a `free` releases (a page
allocator unmaps the whole mapping). `alloc`, `resize` and `remap` need `I.fits n k`: an
allocator may panic on a request beyond its arithmetic range.
-/

namespace Zig

open Assn

/-! ## Logics -/

/-- A Hoare logic over `MemM` with the structural rules of `Triple` and `TotalTriple`. A total
triple of a program that keeps the atomic layout and every block's address
(`Full.Tame`, `ZigLean/Sep/Full/Triple.lean`) is a triple of every such logic (`ofTotal`). Every
primitive of generated plain-memory code is `Tame`. `Triple` and `TotalTriple` are logics whose
triples are partial triples (`Logic.Sound`); so is the full-state logic seen through a fixed
allocator state (`FLogic.legacy`, `ZigLean/Sep/Full/AllocSpec.lean`), in its own sense. -/
structure Logic where
  T : {α : Type} → Assn → MemM α → (α → Assn) → Prop
  ofTotal : ∀ {α : Type} {P : Assn} {c : MemM α} {Q : α → Assn}, TotalTriple P c Q →
    Full.Tame c → T P c Q
  conseq : ∀ {α : Type} {P P' : Assn} {c : MemM α} {Q Q' : α → Assn}, T P c Q →
    (∀ h, P' h → P h) → (∀ v h, Q v h → Q' v h) → T P' c Q'
  frame : ∀ {α : Type} {P R : Assn} {c : MemM α} {Q : α → Assn}, T P c Q →
    T (P ∗ R) c (fun v => Q v ∗ R)
  bind : ∀ {α β : Type} {P : Assn} {c : MemM α} {Q : α → Assn} {R : β → Assn}
    {f : α → MemM β}, T P c Q → (∀ v, T (Q v) (f v) R) → T P (c >>= f) R
  ex : ∀ {α γ : Type} {P : γ → Assn} {c : MemM α} {Q : α → Assn}, (∀ x, T (P x) c Q) →
    T (Assn.ex P) c Q
  lift : ∀ {α : Type} {φ : Prop} {P : Assn} {c : MemM α} {Q : α → Assn}, (φ → T P c Q) →
    T (⌜φ⌝ ∗ P) c Q
  /-- Two programs with the same runs from every sequential memory. -/
  congr : ∀ {α : Type} {P : Assn} {c c' : MemM α} {Q : α → Assn},
    (∀ m, m.Seq → c'.run m = c.run m) → T P c Q → T P c' Q

theorem Triple.congr {α : Type} {P : Assn} {c c' : MemM α} {Q : α → Assn}
    (he : ∀ m, m.Seq → c'.run m = c.run m) (ht : Triple P c Q) : Triple P c' Q := by
  intro m hP hF hd hm hp hs
  rw [he m hs]; exact ht m hP hF hd hm hp hs

theorem TotalTriple.congr {α : Type} {P : Assn} {c c' : MemM α} {Q : α → Assn}
    (he : ∀ m, m.Seq → c'.run m = c.run m) (ht : TotalTriple P c Q) : TotalTriple P c' Q := by
  intro m hP hF hd hm hp hs
  rw [he m hs]; exact ht m hP hF hd hm hp hs

/-- Partial correctness: `Triple`. A diverging allocator satisfies it. -/
def Logic.partial : Logic where
  T := Triple
  ofTotal h _ := h.toPartial
  conseq := Triple.conseq
  frame := Triple.frame
  bind := Triple.bind
  ex := Triple.ex
  lift := Triple.lift
  congr := Triple.congr

/-- Total correctness: `TotalTriple`. Every call returns. -/
def Logic.total : Logic where
  T := TotalTriple
  ofTotal h _ := h
  conseq := TotalTriple.conseq
  frame := TotalTriple.frame
  bind := TotalTriple.bind
  ex := TotalTriple.ex
  lift := TotalTriple.lift
  congr := TotalTriple.congr

/-- Every triple of `L` is a partial triple. -/
def Logic.Sound (L : Logic) : Prop :=
  ∀ {α : Type} {P : Assn} {c : MemM α} {Q : α → Assn}, L.T P c Q → Triple P c Q

theorem Logic.partial_sound : Logic.partial.Sound := id

theorem Logic.total_sound : Logic.total.Sound := TotalTriple.toPartial

namespace Logic

variable (L : Logic) {α β : Type} {P R : Assn} {c : MemM α} {Q : α → Assn}

theorem ret (v : α) : L.T (Q v) (pure v : MemM α) Q :=
  L.ofTotal (TotalTriple.ret v) (Full.Tame.pure' v)

/-- `ret` with an entailment. -/
theorem ret' (v : α) (hq : ∀ h, P h → Q v h) : L.T P (pure v : MemM α) Q :=
  L.conseq (L.ret v) hq (fun _ _ h => h)

theorem pre {P' : Assn} (ht : L.T P c Q) (hp : ∀ h, P' h → P h) : L.T P' c Q :=
  L.conseq ht hp (fun _ _ h => h)

theorem post {Q' : α → Assn} (ht : L.T P c Q) (hq : ∀ v h, Q v h → Q' v h) : L.T P c Q' :=
  L.conseq ht (fun _ h => h) hq

/-- Frame on the left. -/
theorem frameL (ht : L.T P c Q) : L.T (R ∗ P) c (fun v => R ∗ Q v) :=
  L.conseq (L.frame (R := R) ht) (fun _ h => sep_comm h) (fun _ _ h => sep_comm h)

end Logic

/-! ## The vtable and the specification -/

/-- The semantics of the four entries of a `std.mem.Allocator.VTable`, each called with the
context pointer (`Allocator.ptr`). The alignment is the log2 value `k` of `mem.Alignment`
(byte alignment `2 ^ k`); the last argument is `ret_addr`. A translated allocator instantiates
this with its generated functions (the generated `Alignment` value `⟨BitVec.ofNat 6 k⟩`). -/
structure RawVTable where
  alloc : Ptr → BitVec 64 → Nat → BitVec 64 → MemM (Option Ptr)
  resize : Ptr → Slice → Nat → BitVec 64 → BitVec 64 → MemM Bool
  remap : Ptr → Slice → Nat → BitVec 64 → BitVec 64 → MemM (Option Ptr)
  free : Ptr → Slice → Nat → BitVec 64 → MemM Unit

/-- An allocator invariant: `own` is the allocator's state and the memory it has not handed
out; `tok p n k A S K` is its evidence that it issued the `n`-byte region at `p` with alignment
`2 ^ k`, in the block with address `A`, size `S` and kind `K`. Both are arbitrary assertions, so
a token may own memory (the rest of a page) and pin the block it was cut from (a page
allocator's `munmap` of the whole mapping). `fits n k`: a request of `n` bytes with alignment
`2 ^ k` is within the allocator's arithmetic range; a larger one may panic (Zig's
`FixedBufferAllocator` overflows `end_index + n`). -/
structure AllocInv where
  own : Assn
  tok : Ptr → Nat → Nat → Nat → Nat → BlockKind → Assn
  fits : Nat → Nat → Prop := fun _ _ => True

/-- A region that `I`'s allocator granted: the bytes at a `2 ^ k`-aligned `p` in some block, and
the token, which sees the block. -/
def granted (I : AllocInv) (p : Ptr) (k : Nat) (bs : Array Byte) : Assn :=
  Assn.ex fun A => Assn.ex fun S => Assn.ex fun K =>
    regionIn p A S K (2 ^ k) bs ∗ I.tok p bs.size k A S K

/-- `new` keeps the common prefix of `old` (both read up to the shorter length). -/
def keepsPrefix (old new : Array Byte) : Prop := new.extract 0 old.size = old.extract 0 new.size

theorem keepsPrefix_refl (bs : Array Byte) : keepsPrefix bs bs := rfl

/-- After `alloc` of `len` bytes. -/
def allocPost (I : AllocInv) (len k : Nat) : Option Ptr → Assn
  | none => I.own
  | some p => I.own ∗ Assn.ex fun bs => ⌜bs.size = len⌝ ∗ granted I p k bs

/-- After `resize` of the region `bs` at `p` to `n` bytes. -/
def resizePost (I : AllocInv) (p : Ptr) (k : Nat) (bs : Array Byte) (n : Nat) : Bool → Assn
  | true => I.own ∗ Assn.ex fun bs' => ⌜bs'.size = n ∧ keepsPrefix bs bs'⌝ ∗ granted I p k bs'
  | false => I.own ∗ granted I p k bs

/-- After `remap` of the region `bs` at `p` to `n` bytes. -/
def remapPost (I : AllocInv) (p : Ptr) (k : Nat) (bs : Array Byte) (n : Nat) : Option Ptr → Assn
  | none => I.own ∗ granted I p k bs
  | some q => I.own ∗ Assn.ex fun bs' => ⌜bs'.size = n ∧ keepsPrefix bs bs'⌝ ∗ granted I q k bs'

/-- The allocator `vt` with context `ctx` satisfies the `std.mem.Allocator` contract in the
logic `L`, with invariant `I` (module doc). -/
structure AllocSpec (L : Logic) (vt : RawVTable) (ctx : Ptr) (I : AllocInv) : Prop where
  alloc : ∀ (len : BitVec 64) (k : Nat) (ra : BitVec 64), 0 < len.toNat → k < 64 →
    I.fits len.toNat k → L.T I.own (vt.alloc ctx len k ra) (allocPost I len.toNat k)
  resize : ∀ (s : Slice) (k : Nat) (n ra : BitVec 64) (bs : Array Byte), k < 64 →
    0 < n.toNat → I.fits n.toNat k → s.len.toNat = bs.size → 0 < bs.size →
    L.T (I.own ∗ granted I s.ptr k bs) (vt.resize ctx s k n ra) (resizePost I s.ptr k bs n.toNat)
  remap : ∀ (s : Slice) (k : Nat) (n ra : BitVec 64) (bs : Array Byte), k < 64 →
    0 < n.toNat → I.fits n.toNat k → s.len.toNat = bs.size → 0 < bs.size →
    L.T (I.own ∗ granted I s.ptr k bs) (vt.remap ctx s k n ra) (remapPost I s.ptr k bs n.toNat)
  free : ∀ (s : Slice) (k : Nat) (ra : BitVec 64) (bs : Array Byte), k < 64 →
    s.len.toNat = bs.size → 0 < bs.size →
    L.T (I.own ∗ granted I s.ptr k bs) (vt.free ctx s k ra) (fun _ => I.own)

/-- An allocator in a sound logic (`Logic.total`, for instance) is a partial one. -/
theorem AllocSpec.toPartial {L : Logic} {vt : RawVTable} {ctx : Ptr} {I : AllocInv}
    (hL : L.Sound) (h : AllocSpec L vt ctx I) : AllocSpec Logic.partial vt ctx I where
  alloc len k ra h1 h2 h3 := hL (h.alloc len k ra h1 h2 h3)
  resize s k n ra bs h1 h2 h3 h4 h5 := hL (h.resize s k n ra bs h1 h2 h3 h4 h5)
  remap s k n ra bs h1 h2 h3 h4 h5 := hL (h.remap s k n ra bs h1 h2 h3 h4 h5)
  free s k ra bs h1 h2 h3 := hL (h.free s k ra bs h1 h2 h3)

/-- The spec only depends on the runs of the entries: an allocator with the same runs from
every sequential memory (the translated one, after unfolding) satisfies it too. -/
theorem AllocSpec.congr {L : Logic} {vt vt' : RawVTable} {ctx : Ptr} {I : AllocInv}
    (h : AllocSpec L vt ctx I)
    (ha : ∀ len k ra m, m.Seq → (vt'.alloc ctx len k ra).run m = (vt.alloc ctx len k ra).run m)
    (hr : ∀ s k n ra m, m.Seq → (vt'.resize ctx s k n ra).run m = (vt.resize ctx s k n ra).run m)
    (hm : ∀ s k n ra m, m.Seq → (vt'.remap ctx s k n ra).run m = (vt.remap ctx s k n ra).run m)
    (hf : ∀ s k ra m, m.Seq → (vt'.free ctx s k ra).run m = (vt.free ctx s k ra).run m) :
    AllocSpec L vt' ctx I where
  alloc len k ra h1 h2 h3 := L.congr (ha len k ra) (h.alloc len k ra h1 h2 h3)
  resize s k n ra bs h1 h2 h3 h4 h5 := L.congr (hr s k n ra) (h.resize s k n ra bs h1 h2 h3 h4 h5)
  remap s k n ra bs h1 h2 h3 h4 h5 := L.congr (hm s k n ra) (h.remap s k n ra bs h1 h2 h3 h4 h5)
  free s k ra bs h1 h2 h3 := L.congr (hf s k ra) (h.free s k ra bs h1 h2 h3)

end Zig
