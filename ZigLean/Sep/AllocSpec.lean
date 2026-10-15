import ZigLean.Sep.AllocSpec.Ops
import ZigLean.Sep.Base.Alloc
import ZigLean.Sep.Total
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

/-! ## Legacy total triples of the region and ownership operations

The `TotalTriple` rules of the byte and pointer operations on regions that the legacy wrappers
(`ZigLean/Sep/AllocSpec/Wrappers.lean`) and the legacy FBA proof use. Moved here from
`AllocSpec/Region` and `AllocSpec/Ops`, which keep only vocabulary; the full-state rules are in
`ZigLean/Sep/Full/Region.lean` and `ZigLean/Sep/Full/AutoRules.lean`. Deleted with this module
(legacy-retirement plan, lane L6). -/

/-- `@returnAddress()` reads the oracle and changes nothing else. -/
theorem returnAddress_triple {P : Assn} : TotalTriple P returnAddress (fun _ => P) := by
  intro m hP hF hd hm hp hst
  refine ⟨_, { m with arbitraryNext := m.arbitraryNext + 1 }, hP, rfl, hd, hm, hp, ?_⟩
  exact ⟨hst.1⟩

/-- `ptrAddr q` for `q` in a block of which the precondition owns a cell with address `A`. -/
theorem ptrAddr_owned {P : Assn} {q : Ptr} {b : BlockId} {A : Nat} (hqb : q.block = some b)
    (hown : ∀ h, P h → OwnsIn b A h) :
    TotalTriple P (ptrAddr q) (fun r => ⌜r = (A : Int) + q.off⌝ ∗ P) := by
  intro m hP hF hd hm hp hst
  obtain ⟨blk, hblk, hA⟩ := (hown hP hp).block hm
  refine ⟨_, m, hP, ?_, hd, hm, sep_lift.mpr ⟨rfl, hp⟩, hst⟩
  simp [ptrAddr, hqb, hblk, hA, zig_unfold, get, getThe, MonadStateOf.get, StateT.get]

/-- The model's `@alignCast` check (`Zig.checkAlign`, MM) of a pointer into a block of which the
precondition owns a cell, at an address that `al` divides: no effect. -/
theorem checkAlign_owned {P : Assn} {q : Ptr} {b : BlockId} {A al : Nat} (hqb : q.block = some b)
    (hown : ∀ h, P h → OwnsIn b A h) (hal : ((A : Int) + q.off) % al = 0) :
    TotalTriple P (checkAlign al q) (fun _ => P) := by
  unfold checkAlign
  refine TotalTriple.bind (ptrAddr_owned hqb hown) fun r => TotalTriple.lift fun hr => ?_
  subst hr
  rw [if_neg (by simp [hal])]
  exact TotalTriple.ret (Q := fun _ => P) ()

/-- Pointer formation (`ptrProject`, MM-3) of a byte offset `k ≥ 0` from `q`, when the
precondition owns a cell of `q`'s block at an offset at or past `q.off + k - 1`: the block reaches
`q + k`, so both are in bounds and the offset pointer is formed, with no effect. -/
theorem ptrProject_ownsAt {P : Assn} {q : Ptr} {b : BlockId} {j : Nat} {k : Int}
    (hqb : q.block = some b) (h0 : 0 ≤ q.off) (hk : 0 ≤ k) (hj : q.off + k ≤ (j : Int) + 1)
    (hown : ∀ h, P h → OwnsAt b j h) :
    TotalTriple P (ptrProject q (·.add k)) (fun r => ⌜r = q.add k⌝ ∗ P) := by
  intro m hP hF hd hm hp hst
  obtain ⟨c, hc⟩ := hown hP hp
  have : m.heap (b, j) = some c := by rw [hm]; simp [hc]
  obtain ⟨blk, hblk, -, hjs, -⟩ := Mem.heap_some this
  refine ⟨_, m, hP, ptrProject_add_run (inBounds_of hqb hblk h0 (by omega))
    (inBounds_of (p := q.add k) hqb hblk (by simp [Ptr.add]; omega) (by simp [Ptr.add]; omega)),
    hd, hm, sep_lift.mpr ⟨rfl, hp⟩, hst⟩

/-- `ptrProject_ownsAt` for an item pointer `q.elem size i`. -/
theorem ptrProject_elem_ownsAt {P : Assn} {q : Ptr} {b : BlockId} {j size : Nat} {i : BitVec 64}
    (hqb : q.block = some b) (h0 : 0 ≤ q.off) (hj : q.off + ((size * i.toNat : Nat) : Int) ≤ (j : Int) + 1)
    (hown : ∀ h, P h → OwnsAt b j h) :
    TotalTriple P (ptrProject q (·.elem size i)) (fun r => ⌜r = q.elem size i⌝ ∗ P) := by
  have e : (fun x : Ptr => x.elem size i) = (·.add ((size * i.toNat : Nat) : Int)) := by
    funext x; exact Ptr.elem_eq x size i
  rw [e, Ptr.elem_eq]
  exact ptrProject_ownsAt hqb h0 (by omega) hj hown

/-- `@memcpy` with equal counts whose ranges the precondition shows apart is `@memmove`. -/
theorem TotalTriple.memcpy_of {P : Assn} {Q : Unit → Assn} {size da sa : Nat} {d s : Ptr}
    {n : BitVec 64}
    (hsep : ∀ (m : Mem) (h hF : Heap), m.heap = h ∪ hF → P h → d.overlaps s (n.toNat * size) = false)
    (ht : TotalTriple P (memmove size da sa d s n) Q) : TotalTriple P (memcpy size da sa d s n n) Q := by
  intro m hP hF hd hm hp hst
  have := hsep m hP hF hm hp
  unfold memcpy
  rw [if_neg (by simp [this])]
  exact ht m hP hF hd hm hp hst

/-- `ptrLe x y` for `x`, `y` in blocks of which the precondition owns cells. -/
theorem ptrLe_owned {P : Assn} {x y : Ptr} {b₁ b₂ : BlockId} {A₁ A₂ : Nat}
    (hx : x.block = some b₁) (hy : y.block = some b₂) (h₁ : ∀ h, P h → OwnsIn b₁ A₁ h)
    (h₂ : ∀ h, P h → OwnsIn b₂ A₂ h) :
    TotalTriple P (ptrLe x y)
      (fun r => ⌜r = decide ((A₁ : Int) + x.off ≤ (A₂ : Int) + y.off)⌝ ∗ P) := by
  intro m hP hF hd hm hp hst
  obtain ⟨blk₁, hblk₁, hA₁⟩ := (h₁ hP hp).block hm
  obtain ⟨blk₂, hblk₂, hA₂⟩ := (h₂ hP hp).block hm
  refine ⟨_, m, hP, ?_, hd, hm, sep_lift.mpr ⟨rfl, hp⟩, hst⟩
  simp [ptrLe, ptrAddr, hx, hy, hblk₁, hblk₂, hA₁, hA₂, zig_unfold, get, getThe,
    MonadStateOf.get, StateT.get]

theorem ptsR_load {T : Type} [Enc T] {p : Ptr} {a : Nat} {v : T} (hn : 0 < Enc.size T) :
    TotalTriple (ptsR p a v) (load T a p) (fun r => ⌜r = v⌝ ∗ ptsR p a v) := by
  intro m hP hF hd hm hp hst
  obtain ⟨A, S, K, bs, ha, hs, hv, hb⟩ := id hp
  obtain ⟨b, blk, hacc, -, -, -, hx⟩ :=
    bytesAt_access (q := p) (k := 0) (n := Enc.size T) (a := a) hb hm (by simp [Ptr.add])
      hn (by omega) (by simpa using ha)
  simp only [Nat.add_zero] at hx
  have hv' : Enc.decode (blk.bytes.extract p.off.toNat (p.off.toNat + Enc.size T)) = pure v := by
    rw [hx, show bs.extract 0 (0 + Enc.size T) = bs by rw [← hs]; simp]; exact hv
  refine ⟨v, _, hP, load_read (by simpa using hacc) hv' (noRace_of_singleThread hst.single _ _ _ _),
    hd, ?_, sep_lift.mpr ⟨rfl, hp⟩, hst.readAt _ _ _ _ _⟩
  funext l; rw [Mem.heap_readAt]; exact congrFun hm l

theorem ptsM_load {T : Type} [Enc T] {p : Ptr} {A S : Nat} {K : BlockKind} {a : Nat} {v : T}
    (hn : 0 < Enc.size T) :
    TotalTriple (ptsM p A S K a v) (load T a p) (fun r => ⌜r = v⌝ ∗ ptsM p A S K a v) := by
  intro m hP hF hd hm hp hst
  obtain ⟨m', hr, hheap, hs'⟩ := pts_load_run (ptsM_pts hp) hm hn hst
  exact ⟨v, m', hP, hr, hd, hheap, sep_lift.mpr ⟨rfl, hp⟩, hs'⟩

theorem ptsM_store {T : Type} [Enc T] [LawfulEnc T] {p : Ptr} {A S : Nat} {K : BlockKind}
    {a : Nat} {v : T} (hn : 0 < Enc.size T) (w : T) :
    TotalTriple (ptsM p A S K a v) (store a p w) (fun _ => ptsM p A S K a w) := by
  intro m hP hF hd hm hp hst
  obtain ⟨ha, hK, bs, hs, -, hb⟩ := hp
  have hw := LawfulEnc.size_encode w
  obtain ⟨m', hrun, hst', h', hd', hm', hb'⟩ :=
    bytesAt_store (q := p) (k := 0) (a := a) (bs' := Enc.encode w) hb hm hd (by simp [Ptr.add])
      (by omega) (by omega) (by simpa using ha) hst hK
  refine ⟨(), m', h', hrun, hd', hm', ⟨ha, hK, _, ?_, ?_, hb'⟩, hst'⟩ <;>
    rw [writeBytes_all (by omega)]
  · exact hw
  · exact LawfulEnc.decode_encode w

/-- Use a pure fact that the precondition implies. -/
theorem TotalTriple.of_pure {α : Type} {P : Assn} {c : MemM α} {Q : α → Assn} {φ : Prop}
    (hφ : ∀ h, P h → φ) (ht : φ → TotalTriple P c Q) : TotalTriple P c Q := by
  intro m hP hF hd hm hp hst
  exact ht (hφ hP hp) m hP hF hd hm hp hst

/-- A load of an item from the bytes of a region. -/
theorem loadItemIn {T : Type} [Enc T] {p : Ptr} {A S : Nat} {K : BlockKind} {a al o : Nat}
    {bs : Array Byte} {v : T} (hpos : 0 < Enc.size T) (ho : o + Enc.size T ≤ bs.size)
    (hal : al ∣ a) (halo : al ∣ o) (hv : Enc.decode (bs.extract o (o + Enc.size T)) = pure v) :
    TotalTriple (regionIn p A S K a bs) (load T al (p.add o))
      (fun r => ⌜r = v⌝ ∗ regionIn p A S K a bs) := by
  intro m hP hF hd hm hp hst
  obtain ⟨hA, hK, hb⟩ := id hp
  have ha : (A + p.off.toNat + o) % al = 0 :=
    Nat.mod_eq_zero_of_dvd (Nat.dvd_add (Nat.dvd_trans hal (Nat.dvd_of_mod_eq_zero hA)) halo)
  obtain ⟨b, blk, hacc, -, -, -, hx⟩ :=
    bytesAt_access (q := p.add o) (k := o) (n := Enc.size T) (a := al) hb hm rfl hpos ho ha
  have hv' : Enc.decode (blk.bytes.extract (p.off.toNat + o) (p.off.toNat + o + Enc.size T)) =
      pure v := by rw [hx]; exact hv
  refine ⟨v, _, hP, load_read hacc hv' (noRace_of_singleThread hst.single _ _ _ _), hd, ?_,
    sep_lift.mpr ⟨rfl, hp⟩, hst.readAt _ _ _ _ _⟩
  funext l; rw [Mem.heap_readAt]; exact congrFun hm l

/-- Coverage survives a command whose frame keeps a byte `G` of the block: the block stays live
with its size and kind, so its bytes from the kind's first live offset on that the frame does not
have are still owned. -/
theorem TotalTriple.covers {α : Type} {P G : Assn} {c : MemM α} {Q : α → Assn} {b : BlockId}
    {S lo hi : Nat} {K : BlockKind} (ht : TotalTriple P c Q) (hG : ∀ h, G h → Pins b S K h)
    (hhi : hi ≤ S) (hK : K.mappedLo ≤ lo) :
    TotalTriple (fun h => (P ∗ G) h ∧ Covers b lo hi h) c
      (fun v h => (Q v ∗ G) h ∧ Covers b lo hi h) := by
  intro m hP hF hd hm ⟨hp, hcov⟩ hst
  obtain ⟨v, m', hQ, hr, hd', hm', hq, hst'⟩ := (TotalTriple.frame (R := G) ht) m hP hF hd hm hp hst
  refine ⟨v, m', hQ, hr, hd', hm', ⟨hq, ?_⟩, hst'⟩
  intro i hlo hlt
  obtain ⟨hq₁, hq₂, hd₁₂, rfl, -, hg⟩ := hq
  obtain ⟨o, c', hc', hcS, hcK⟩ := hG _ hg
  have hpin : m'.heap (b, o) = some c' := by rw [hm']; simp [Heap.union_of_right (hd₁₂ (b, o) |>.resolve_right (by simp [hc'])), hc']
  obtain ⟨blk, hblk, hlive, ho, hc⟩ := Mem.heap_some hpin
  have hsz : blk.bytes.size = S := by rw [← hcS, hc]
  have hk : blk.kind = K := by rw [← hcK, hc]
  have hin : m'.heap (b, i) ≠ none := by
    simp [Mem.heap, hblk, hlive, hsz, hk]; omega
  have hFi : hF (b, i) = none := (hd (b, i)).resolve_left (hcov i hlo hlt)
  rw [hm', Heap.union_apply, hFi, Option.or_none] at hin
  exact hin

/-- `free` of a whole block, not a `const` global: its bytes go. -/
theorem free_whole {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte} {R : Assn}
    (hS : bs.size = S) (h0 : p.off = 0) (hpos : 0 < S) (hK : K ≠ .constGlobal := by decide) :
    TotalTriple (bytesAt p A S K bs ∗ R) (free p) (fun _ => R) := by
  intro m hP hF hd hm hp hst
  obtain ⟨h₁, h₂, hd₁₂, rfl, hb, hr⟩ := hp
  obtain ⟨hd₁F, hd₂F⟩ := Heap.disjoint_union_left.mp hd
  have hm₁ : m.heap = h₁ ∪ (h₂ ∪ hF) := by rw [hm, Heap.union_assoc]
  obtain ⟨m', hrun, hm', hst', -⟩ := free_run hb hm₁ (Heap.disjoint_union_right.mpr ⟨hd₁₂, hd₁F⟩)
    hS h0 hpos hst hK
  exact ⟨(), m', h₂, hrun, hd₂F, by rw [hm', Heap.empty_union], hr, hst'⟩

/-- `ptrProject_elem_ownsAt` for an item pointer into a nonempty region, at most one past it. -/
theorem ptrProject_elem_region {p : Ptr} {A S : Nat} {K : BlockKind} {a size : Nat}
    {bs : Array Byte} {i : BitVec 64} (hpos : 0 < bs.size) (hi : size * i.toNat ≤ bs.size) :
    TotalTriple (regionIn p A S K a bs) (ptrProject p (·.elem size i))
      (fun r => ⌜r = p.elem size i⌝ ∗ regionIn p A S K a bs) := by
  refine TotalTriple.of_pure (φ := ∃ b, p.block = some b ∧ 0 ≤ p.off)
    (fun h hr => let ⟨b, hb, h0, _⟩ := bytesAt_ownsAt hr.2.2 hpos; ⟨b, hb, h0⟩)
    fun ⟨b, hb, h0⟩ => ptrProject_elem_ownsAt (j := p.off.toNat + (bs.size - 1)) hb h0
      (by push_cast; omega) fun h hr => ?_
  obtain ⟨b', hb', -, ho⟩ := bytesAt_ownsAt hr.2.2 hpos
  rw [hb] at hb'; cases hb'; exact ho

/-- Pointer formation (`ptrProject`, MM-3) of an offset of `q` that stays in `[0, S]` of a block
whose size `S` an owned cell records: formed, no effect. -/
theorem ptrProject_sized {P : Assn} {q : Ptr} {b : BlockId} {S : Nat} {k : Int}
    (hqb : q.block = some b) (h0 : 0 ≤ q.off) (hq : q.off ≤ S) (hk0 : 0 ≤ q.off + k)
    (hk : q.off + k ≤ S) (hown : ∀ h, P h → OwnsSz b S h) :
    TotalTriple P (ptrProject q (·.add k)) (fun r => ⌜r = q.add k⌝ ∗ P) := by
  intro m hP hF hd hm hp hst
  obtain ⟨o, c, hc, hS⟩ := hown hP hp
  have : m.heap (b, o) = some c := by rw [hm]; simp [hc]
  obtain ⟨blk, hblk, -, ho, hcb⟩ := Mem.heap_some this
  have hS' : blk.bytes.size = S := by rw [← hS, hcb]
  refine ⟨_, m, hP, ptrProject_add_run (inBounds_of hqb hblk h0 (by omega))
    (inBounds_of (p := q.add k) hqb hblk (by simp [Ptr.add]; omega) (by simp [Ptr.add]; omega)),
    hd, hm, sep_lift.mpr ⟨rfl, hp⟩, hst⟩

/-- `ptrProject_sized` for an item pointer `q.elem size i`. -/
theorem ptrProject_elem_sized {P : Assn} {q : Ptr} {b : BlockId} {S size : Nat} {i : BitVec 64}
    (hqb : q.block = some b) (h0 : 0 ≤ q.off) (hk : q.off + ((size * i.toNat : Nat) : Int) ≤ S)
    (hown : ∀ h, P h → OwnsSz b S h) :
    TotalTriple P (ptrProject q (·.elem size i)) (fun r => ⌜r = q.elem size i⌝ ∗ P) := by
  have e : (fun x : Ptr => x.elem size i) = (·.add ((size * i.toNat : Nat) : Int)) := by
    funext x; exact Ptr.elem_eq x size i
  rw [e, Ptr.elem_eq]
  exact ptrProject_sized hqb h0 (by omega) (by omega) hk hown

/-- `==` of two pointers into one block of which the precondition owns a cell (MM-4): their
offsets are equal. -/
theorem ptrEqAddr_owned {P : Assn} {p q : Ptr} {b : BlockId} {A : Nat} (hp : p.block = some b)
    (hq : q.block = some b) (hown : ∀ h, P h → OwnsIn b A h) :
    TotalTriple P (ptrEqAddr p q) (fun r => ⌜r = decide (p.off = q.off)⌝ ∗ P) := by
  unfold ptrEqAddr
  refine TotalTriple.bind (ptrAddr_owned hp hown) fun x => TotalTriple.lift fun hx => ?_
  refine TotalTriple.bind (ptrAddr_owned hq hown) fun y => TotalTriple.lift fun hy => ?_
  subst hx hy
  refine TotalTriple.conseq (TotalTriple.ret (Q := fun r => ⌜r = decide (p.off = q.off)⌝ ∗ P) _)
    (fun h hh => sep_lift.mpr ⟨?_, hh⟩) (fun _ _ h => h)
  simp

namespace Region

variable {p : Ptr} {A S : Nat} {K : BlockKind} {a : Nat} {bs : Array Byte}

/-- `@memset(region, v)` of all `n` bytes, in the region's block. -/
theorem memsetIn (v : Option (BitVec 8)) {n : BitVec 64} (hn : n.toNat = bs.size) :
    TotalTriple (regionIn p A S K a bs) (memset (α := BitVec 8) 1 p n v)
      (fun _ => regionIn p A S K a (Array.replicate n.toNat (memsetItem v)).flatten) := by
  intro m hP hF hd hm hp hst
  by_cases h0 : n.toNat = 0
  · have hbs : bs = #[] := Array.eq_empty_of_size_eq_zero (by omega)
    subst hbs
    refine ⟨(), m, hP, ?_, hd, hm, by rw [h0]; simpa using hp, hst⟩
    simp [memset, h0, StateT.run, pure, StateT.pure, ExceptT.pure, ExceptT.mk]
  obtain ⟨hA, hK, hb⟩ := hp
  let bs' : Array Byte := (Array.replicate n.toNat (memsetItem v)).flatten
  have hsz : bs'.size = bs.size := by
    simp only [bs', Array.size_flatten_replicate, memsetItem_size, Nat.mul_one]; exact hn
  have hp0 : p = p.add ((0 : Nat) : Int) := by simp [Ptr.add]
  have ha0 : (A + p.off.toNat + 0) % 1 = 0 := Nat.mod_one _
  obtain ⟨b, blk, hacc, -, -, -, -⟩ := bytesAt_access (q := p) (k := 0) (n := bs'.size) (a := 1)
    hb hm hp0 (by omega) (by omega) ha0
  obtain ⟨m', hrun, hst', h', hd', hm', hb'⟩ := bytesAt_store (q := p) (k := 0) (a := 1)
    (bs' := bs') hb hm hd hp0 (by omega) (by omega) ha0 hst hK
  rw [writeBytes_all hsz] at hb'
  refine ⟨(), m', h', ?_, hd', hm', ⟨hA, hK, hb'⟩, hst'⟩
  have e : n.toNat * Enc.size (BitVec 8) = bs'.size := by
    rw [hsz, enc_size_byte, Nat.mul_one]; exact hn
  have hne : ¬ Enc.size (BitVec 8) = 0 := by rw [enc_size_byte]; decide
  simp only [StateT.run] at hrun
  simp only [memset, h0, hne, or_self, ↓reduceIte, zig_unfold, e, hacc, ExceptT.bindCont]
  cases v <;> exact hrun

/-- `@memset(region, undefined)` of all `n` bytes, in the region's block. -/
theorem memsetUndefIn {n : BitVec 64} (hn : n.toNat = bs.size) :
    TotalTriple (regionIn p A S K a bs) (memset (α := BitVec 8) 1 p n none)
      (fun _ => regionIn p A S K a (Array.replicate n.toNat .undef)) :=
  TotalTriple.conseq (memsetIn none hn) (fun _ x => x) fun _ _ x => by
    rwa [show memsetItem none = #[Byte.undef] from rfl, flatten_replicate_single] at x

/-- A store of an item `v` at byte `o` of a region, aligned to `al`, in the region's block. -/
theorem storeItemIn {T : Type} [Enc T] [LawfulEnc T] {o al : Nat} (v : T) (hpos : 0 < Enc.size T)
    (ho : o + Enc.size T ≤ bs.size) (hal : al ∣ a) (halo : al ∣ o) :
    TotalTriple (regionIn p A S K a bs) (store al (p.add o) v)
      (fun _ => regionIn p A S K a (writeBytes bs o (Enc.encode v))) := by
  intro m hP hF hd hm hp hst
  obtain ⟨hA, hK, hb⟩ := hp
  have hw := LawfulEnc.size_encode v
  have ha : (A + p.off.toNat + o) % al = 0 :=
    Nat.mod_eq_zero_of_dvd (Nat.dvd_add (Nat.dvd_trans hal (Nat.dvd_of_mod_eq_zero hA)) halo)
  obtain ⟨m', hrun, hst', h', hd', hm', hb'⟩ :=
    bytesAt_store (q := p.add o) (k := o) (a := al) (bs' := Enc.encode v) hb hm hd rfl
      (by omega) (by omega) ha hst hK
  exact ⟨(), m', h', hrun, hd', hm', ⟨hA, hK, hb'⟩, hst'⟩

/-- `@memcpy`, in the regions' blocks, of `n` items of `sz` bytes from the region `src` to the start of the region `dst`
(two separate regions). -/
theorem memcpyIn {d s : Ptr} {A' S' : Nat} {K' : BlockKind} {a' da sa sz : Nat}
    {bd bsrc : Array Byte} {n : BitVec 64}
    (hnd : n.toNat * sz ≤ bd.size) (hns : n.toNat * sz ≤ bsrc.size) (hda : da ∣ a)
    (hsa : sa ∣ a') :
    TotalTriple (regionIn d A S K a bd ∗ regionIn s A' S' K' a' bsrc) (memmove sz da sa d s n)
      (fun _ => regionIn d A S K a (writeBytes bd 0 (bsrc.extract 0 (n.toNat * sz))) ∗
        regionIn s A' S' K' a' bsrc) := by
  intro m hP hF hd hm hp hst
  by_cases h0 : n.toNat = 0 ∨ sz = 0
  · have e : n.toNat * sz = 0 := by rcases h0 with h | h <;> simp [h]
    refine ⟨(), m, hP, ?_, hd, hm, ?_, hst⟩
    · simp [memmove, h0, StateT.run, pure, StateT.pure, ExceptT.pure, ExceptT.mk]
    · rw [e]; simpa [writeBytes_zero_empty] using hp
  have hpos : 0 < n.toNat * sz := Nat.mul_pos (by omega) (by omega)
  obtain ⟨h₁, h₂, hd₁₂, rfl, ⟨hA, hK, hb₁⟩, ⟨hA', hK', hb₂⟩⟩ := hp
  obtain ⟨hd₁F, hd₂F⟩ := Heap.disjoint_union_left.mp hd
  have hm₁ : m.heap = h₁ ∪ (h₂ ∪ hF) := by rw [hm, Heap.union_assoc]
  have hdd₁ : Heap.Disjoint h₁ (h₂ ∪ hF) := Heap.disjoint_union_right.mpr ⟨hd₁₂, hd₁F⟩
  have hm₂ : m.heap = h₂ ∪ (h₁ ∪ hF) := by
    rw [hm, Heap.union_assoc, Heap.union_left_comm hd₁₂]
  have hp0 : ∀ q : Ptr, q = q.add ((0 : Nat) : Int) := fun q => by simp [Ptr.add]
  have haD : (A + d.off.toNat + 0) % da = 0 :=
    Nat.mod_eq_zero_of_dvd (Nat.dvd_trans hda (Nat.dvd_of_mod_eq_zero (by simpa using hA)))
  have haS : (A' + s.off.toNat + 0) % sa = 0 :=
    Nat.mod_eq_zero_of_dvd (Nat.dvd_trans hsa (Nat.dvd_of_mod_eq_zero (by simpa using hA')))
  obtain ⟨b, blk, hacc, -, -, -, -⟩ := bytesAt_access (q := d) (k := 0) (n := n.toNat * sz)
    (a := da) hb₁ hm₁ (hp0 d) hpos (by omega) haD
  obtain ⟨b₂, blk₂, hacc₂, -, -, -, hx₂⟩ := bytesAt_access (q := s) (k := 0)
    (n := n.toNat * sz) (a := sa) hb₂ hm₂ (hp0 s) hpos (by omega) haS
  let src := bsrc.extract 0 (0 + n.toNat * sz)
  have hsrc : src.size = n.toNat * sz := by simp [src]; omega
  have hmr : (m.readAt blk₂ b₂ (s.off.toNat + 0) (n.toNat * sz) AccessKind.read).heap =
      h₁ ∪ (h₂ ∪ hF) := by
    funext l; rw [Mem.heap_readAt]; exact congrFun hm₁ l
  obtain ⟨m', hrun, hst', h', hd', hm', hb'⟩ := bytesAt_store (q := d) (k := 0) (a := da)
    (bs' := src) hb₁ hmr hdd₁ (hp0 d) (by omega) (by omega) haD (hst.readAt _ _ _ _ _) hK
  obtain ⟨hd'₂, hd'F⟩ := Heap.disjoint_union_right.mp hd'
  refine ⟨(), m', h' ∪ h₂, ?_, Heap.disjoint_union_left.mpr ⟨hd'F, hd₂F⟩,
    by rw [hm', Heap.union_assoc], ⟨h', h₂, hd'₂, rfl, ⟨hA, hK, ?_⟩,
      ⟨hA', hK', hb₂⟩⟩, hst'⟩
  · have hl := loadBytes_read hacc₂ (fun _ => rfl) (noRace_of_singleThread hst.single b₂
      (s.off.toNat + 0) (n.toNat * sz) AccessKind.read)
    rw [hx₂] at hl
    simp only [StateT.run] at hl hrun
    simp only [memmove, h0, ↓reduceIte, StateT.run, bind, StateT.bind, get, getThe,
      MonadStateOf.get, StateT.get, liftM, monadLift, MonadLift.monadLift, StateT.lift,
      ExceptT.bind, ExceptT.mk, ExceptT.bindCont, hacc, hl, pure, ExceptT.pure, Option.bind_some]
    exact hrun
  · simpa [src] using hb'

end Region

end Zig
