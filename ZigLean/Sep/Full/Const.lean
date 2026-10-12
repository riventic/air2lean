import ZigLean.Sep.Full.AutoAttr
import ZigLean.Sep.Full.Ops

/-!
# Persistent knowledge of `const` globals (`docs/sep-full-state.md` §Const globals)

A `const` global (a vtable, a string literal, any `const` data) is read-only static storage: a
write to it throws `.illegal` (`Mem.accessW`), and so does a `free` of it (`Zig.free`); every other
step that changes a block is reached only after a kind check (`munmap`/`mremap`: `.mapped`; byte
remap: `.heap`; owned remap and reset: `.owned`; an atomic write's message, `insertMsg`: its
`accessW`). Each primitive's `KMono` proof (`Tame`, the atomic and `mmap` rules) checks this, so a
new primitive cannot skip it. So a live `const` global keeps its bytes, its address and its life
in every later memory (`KMono`), and what a program has seen of it is knowledge, not ownership:
`Mem.kn` has a fact `.cbyte b o c` for every byte of a live `const` global.

* `cbytesAt p A bs`: **persistent**: the live `const` global at `p` (block address `A`) holds the
  bytes `bs`. It owns no bytes and no ghost state, so it is duplicable (`Persistent.dup`) and many
  owners can hold it at once: two allocator handles with the same vtable, every client of a
  string literal. It is forgotten by an update (`Persistent.drop`), not by entailment.
* `cpts p a v`: the typed read-only points-to (`ptsR` as knowledge).
* Introduction: from an owned `const` byte range (`cbytesAt_intro`: whoever owns the global's
  bytes, e.g. at program start, may hand out the knowledge and keep the bytes), or directly from
  the memory (`Holds.addKnow` with `Mem.ofGlobals_kn`: the initial memory's `const` globals).
* Reading: the provider `ConstAt` (every memory that holds the precondition has the bytes), the
  load rule `FTotalTriple.load_const`, and for `fsym` the atom rule `FTotalTriple.cload`
  (`@[fsym]`) and the providers `AddrOf.cpts`, `Reaches.cpts` (`@[fsym_provider]`).

Proof-only: not reachable from `ZigLean.lean`.
-/

namespace Zig
namespace Full

open FAssn

/-! ## Persistent assertions -/

/-- `P` owns no bytes and no ghost state: only knowledge, which is duplicable. -/
def Persistent (P : FAssn) : Prop := ∀ r, P r → r.heap = FHeap.empty ∧ r.gh = Ghost.unit

section Persistent

variable {P Q R : FAssn} {r : Res}

/-- **A persistent assertion is duplicable.** -/
theorem Persistent.dup (hP : Persistent P) (h : P r) : (P ⋆ P) r := by
  obtain ⟨e1, e2⟩ := hP r h
  refine ⟨r, r, fun _ => .inl (by rw [e1]; rfl), ?_, h, h⟩
  obtain ⟨rh, rk, rg⟩ := r
  simp only at e1 e2 ⊢
  subst e1 e2
  rw [FHeap.union_empty, Know.union_self, Ghost.add_unit]

theorem Persistent.sep (hP : Persistent P) (hQ : Persistent Q) : Persistent (P ⋆ Q) := by
  rintro _ ⟨r₁, r₂, -, rfl, h1, h2⟩
  obtain ⟨a1, b1⟩ := hP r₁ h1
  obtain ⟨a2, b2⟩ := hQ r₂ h2
  simp [a1, b1, a2, b2, Ghost.add_unit]

theorem Persistent.emp : Persistent FAssn.emp := fun _ h => ⟨h.1, h.2.2⟩

theorem Persistent.lift {φ : Prop} : Persistent ⟪φ⟫ := fun _ h => ⟨h.2.1, h.2.2.2⟩

theorem Persistent.ex {γ : Type} {P : γ → FAssn} (h : ∀ x, Persistent (P x)) :
    Persistent (FAssn.ex P) := fun r ⟨x, hx⟩ => h x r hx

theorem Persistent.known {b : BlockId} {A : Nat} : Persistent (Zig.Full.known b A) :=
  fun _ h => ⟨h.1, h.2.2⟩

/-- Knowledge can be forgotten (an update: `emp` has no knowledge, so not an entailment). -/
theorem Persistent.drop (hP : Persistent P) : EUpd (P ⋆ R) R := by
  rintro m _ rF hh ⟨r₁, r₂, -, rfl, hp, hr⟩ -
  obtain ⟨e1, e3⟩ := hP r₁ hp
  obtain ⟨hd, hm, hkn, hkF, hg⟩ := hh
  simp only [e1, e3, FHeap.empty_union, Ghost.unit_add] at hd hm hg
  exact ⟨r₂, ⟨hd, hm, Know.Sub.right hkn, hkF, hg⟩, hr⟩

end Persistent

/-! ## `const` bytes -/

/-- The facts of `cbytesAt`: block `b` at address `A`, and its bytes `bs` from offset `o`. -/
def cknow (b : BlockId) (A o : Nat) (bs : Array Byte) : Know := fun f =>
  f = .addr b A ∨ ∃ i, ∃ h : i < bs.size, f = .cbyte b (o + i) bs[i]

/-- **Persistent knowledge of `const` bytes**: the live `const` global at `p` (block address
`A`) holds `bs` from `p` on. Owns nothing (module doc). -/
def cbytesAt (p : Ptr) (A : Nat) (bs : Array Byte) : FAssn := fun r =>
  r.heap = FHeap.empty ∧ r.gh = Ghost.unit ∧
    ∃ b, p.block = some b ∧ 0 ≤ p.off ∧ r.know = cknow b A p.off.toNat bs

/-- **The read-only typed points-to**: `p` points to `v` in a live `const` global, readable with
alignment `a` (`ptsR` as persistent knowledge). -/
def cpts {T : Type} [Enc T] (p : Ptr) (a : Nat) (v : T) : FAssn := fun r =>
  ∃ A bs, (A + p.off.toNat) % a = 0 ∧ bs.size = Enc.size T ∧ Enc.decode bs = pure v ∧
    cbytesAt p A bs r

theorem Persistent.cbytesAt {p : Ptr} {A : Nat} {bs : Array Byte} :
    Persistent (Zig.Full.cbytesAt p A bs) := fun _ h => ⟨h.1, h.2.1⟩

theorem Persistent.cpts {T : Type} [Enc T] {p : Ptr} {a : Nat} {v : T} :
    Persistent (Zig.Full.cpts p a v) := fun _ ⟨_, _, _, _, _, h⟩ => ⟨h.1, h.2.1⟩

/-- A memory's facts about a live `const` global block: its address and each of its bytes. -/
theorem Mem.kn_const {m : Mem} {b : BlockId} {blk : Block} (hb : m.blocks[b]? = some blk)
    (hk : blk.kind = .constGlobal) (hl : blk.live = true) {o : Nat} {bs : Array Byte}
    (hbs : ∀ i (h : i < bs.size), blk.bytes[o + i]? = some bs[i]) :
    Know.Sub (cknow b blk.addr o bs) m.kn := by
  rintro f (rfl | ⟨i, hi, rfl⟩)
  · exact ⟨blk, hb, rfl⟩
  · exact ⟨blk, hb, hk, hl, hbs i hi⟩

/-- **The `const` globals of the memory at program start**: global `j`, if `const`, is a live
block whose facts the initial memory has, its whole initial bytes included. -/
theorem Mem.ofGlobals_kn (σ : Placement) (gs : List (Array Byte × Nat × BlockKind)) {j : Nat}
    (hj : j < gs.length) (hk : gs[j].2.2 = .constGlobal) :
    ∃ A, (0 < gs[j].2.1 → A % gs[j].2.1 = 0) ∧
      Know.Sub (cknow j A 0 gs[j].1) (Mem.ofGlobals σ gs).kn := by
  obtain ⟨A, hA, hb⟩ := Mem.ofGlobals_block σ gs j hj
  exact ⟨A, hA, Mem.kn_const hb hk rfl fun i hi => by simp [hi]⟩

/-- `cbytesAt` of knowledge that the memory has. -/
theorem cbytesAt_of_kn {m : Mem} {r rF : Res} {P : FAssn} {p : Ptr} {b : BlockId} {A : Nat}
    {bs : Array Byte} (hpb : p.block = some b) (h0 : 0 ≤ p.off)
    (hk : Know.Sub (cknow b A p.off.toNat bs) m.kn) (hh : Holds m r rF) (hp : P r) :
    ∃ r', Holds m r' rF ∧ (P ⋆ cbytesAt p A bs) r' :=
  ⟨_, Holds.addKnow hk hh, r, ⟨FHeap.empty, cknow b A p.off.toNat bs, Ghost.unit⟩,
    FHeap.disjoint_empty _, by rw [FHeap.union_empty, Ghost.add_unit], hp, rfl, rfl, b, hpb, h0, rfl⟩

theorem BlockKind.norm_eq_constGlobal {K : BlockKind} (h : K.norm = .constGlobal) :
    K = .constGlobal := by
  cases K <;> simp_all [BlockKind.norm]

/-- **Knowledge from ownership**: whoever owns the bytes `bs` of a `const` global at `p` may hand
out `cbytesAt p A bs` and keep the bytes (`up` of a legacy `bytesAt`, e.g. at program start). -/
theorem cbytesAt_intro {p : Ptr} {A S : Nat} {bs : Array Byte} (hpos : 0 < bs.size) :
    EUpd (up (bytesAt p A S .constGlobal bs))
      (up (bytesAt p A S .constGlobal bs) ⋆ cbytesAt p A bs) := by
  intro m r rF hh hp _
  obtain ⟨b, hpb, h0, hl⟩ := id hp.1
  -- each owned byte is a byte of a live `const` block at address `A`
  have cell : ∀ i (hi : i < bs.size), ∃ blk, m.blocks[b]? = some blk ∧ blk.kind = .constGlobal ∧
      blk.live = true ∧ blk.addr = A ∧ blk.bytes[p.off.toNat + i]? = some bs[i] := by
    intro i hi
    have e := hl (b, p.off.toNat + i)
    rw [if_pos ⟨rfl, by omega, by omega⟩] at e
    obtain ⟨fc, hfc, hfe⟩ := erase_cell e
    obtain ⟨c, hc, hn⟩ := hh.cellN hfc
    obtain ⟨blk, hblk, hlive, ho, rfl⟩ := Mem.heap_some hc
    rw [hfe] at hn
    simp only [Cell.norm, Cell.mk.injEq] at hn
    obtain ⟨hv, ha, -, hk⟩ := hn
    refine ⟨blk, hblk, BlockKind.norm_eq_constGlobal hk, hlive, ha, ?_⟩
    rw [Array.getElem?_eq_getElem ho, hv]; simp [getElem!_pos bs i hi]
  obtain ⟨blk, hblk, hk, hlive, ha, -⟩ := cell 0 hpos
  have hsub : Know.Sub (cknow b A p.off.toNat bs) m.kn := by
    rw [← ha]
    refine Mem.kn_const hblk hk hlive fun i hi => ?_
    obtain ⟨blk', hblk', -, -, -, hx⟩ := cell i hi
    rw [hblk] at hblk'; cases hblk'; exact hx
  exact cbytesAt_of_kn hpb h0 hsub hh hp

/-- **Absorbing knowledge one already has**: a persistent `X` whose facts `r` already has holds
next to anything `r` holds. -/
theorem Persistent.absorb {X P : FAssn} {k : Know} {r : Res}
    (hx : X ⟨FHeap.empty, k, Ghost.unit⟩) (hk : Know.Sub k r.know) (hp : P r) : (X ⋆ P) r := by
  refine ⟨⟨FHeap.empty, k, Ghost.unit⟩, r, fun _ => .inl rfl, ?_, hx, hp⟩
  obtain ⟨rh, rk, rg⟩ := r
  simp only at hk ⊢
  rw [FHeap.empty_union, Ghost.unit_add, Know.union_of_sub hk]

/-- **Part of known `const` bytes**: the bytes `[k, k + n)` of `bs`, at `p + k`, are known too
(the knowledge stays whole: it is persistent). -/
theorem cbytesAt_part {p : Ptr} {A k n : Nat} {bs : Array Byte} {r : Res} (hkn : k + n ≤ bs.size)
    (h : cbytesAt p A bs r) : (cbytesAt (p.add k) A (bs.extract k (k + n)) ⋆ cbytesAt p A bs) r := by
  obtain ⟨e1, e2, b, hpb, h0, hk⟩ := h
  have hoff : (p.add k).off.toNat = p.off.toNat + k := by simp [Ptr.add]; omega
  have hsub : Know.Sub (cknow b A (p.add k).off.toNat (bs.extract k (k + n))) r.know := by
    rw [hk, hoff]
    rintro f (rfl | ⟨i, hi, rfl⟩)
    · exact .inl rfl
    · simp only [Array.size_extract] at hi
      refine .inr ⟨k + i, by omega, ?_⟩
      simp [Array.getElem_extract, Nat.add_assoc]
  exact Persistent.absorb ⟨rfl, rfl, b, by simpa [Ptr.add] using hpb, by simp [Ptr.add]; omega, rfl⟩
    hsub ⟨e1, e2, b, hpb, h0, hk⟩

/-- `const` bytes that decode to `v` at an address aligned to `a` are a read-only typed value. -/
theorem cpts_of_cbytesAt {T : Type} [Enc T] {p : Ptr} {a A : Nat} {bs : Array Byte} {v : T}
    {r : Res} (ha : (A + p.off.toNat) % a = 0) (hs : bs.size = Enc.size T)
    (hv : Enc.decode bs = pure v) (h : cbytesAt p A bs r) : cpts p a v r :=
  ⟨A, bs, ha, hs, hv, h⟩

/-! ## Reading `const` bytes -/

/-- **Provider**: every memory that holds `P` has, at `p`, nonempty bytes `bs` of a live `const`
global whose address `A` and bytes meet `φ A bs`. -/
def ConstAt (p : Ptr) (φ : Nat → Array Byte → Prop) (P : FAssn) : Prop :=
  ∀ m r rF, Holds m r rF → P r → ∃ b blk bs, p.block = some b ∧ m.blocks[b]? = some blk ∧
    blk.kind = .constGlobal ∧ blk.live = true ∧ 0 ≤ p.off ∧ 0 < bs.size ∧ φ blk.addr bs ∧
    ∀ i (h : i < bs.size), blk.bytes[p.off.toNat + i]? = some bs[i]

section Providers

variable {p : Ptr} {φ ψ : Nat → Array Byte → Prop} {P R : FAssn}

theorem ConstAt.sepL (h : ConstAt p φ P) : ConstAt p φ (P ⋆ R) := fun m _ rF hh hp => by
  obtain ⟨r₁, r₂, hd, rfl, h1, -⟩ := hp
  exact h m r₁ _ (Holds.split hd hh) h1

theorem ConstAt.sepR (h : ConstAt p φ P) : ConstAt p φ (R ⋆ P) := fun m r rF hh hp =>
  h.sepL m r rF hh (sep_comm hp)

theorem ConstAt.of_imp {P' : FAssn} (h : ConstAt p φ P) (hp : ∀ r, P' r → P r) :
    ConstAt p φ P' := fun m r rF hh h' => h m r rF hh (hp r h')

theorem ConstAt.mono (h : ConstAt p φ P) (hφ : ∀ A bs, φ A bs → ψ A bs) : ConstAt p ψ P :=
  fun m r rF hh hp => by
    obtain ⟨b, blk, bs, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h m r rF hh hp
    exact ⟨b, blk, bs, h1, h2, h3, h4, h5, h6, hφ _ _ h7, h8⟩

/-- Nonempty `const` bytes are what they say. -/
theorem ConstAt.cbytesAt {A : Nat} {bs : Array Byte} (hpos : 0 < bs.size) :
    ConstAt p (fun A' bs' => A' = A ∧ bs' = bs) (cbytesAt p A bs) :=
  fun m r _ hh hp => by
    obtain ⟨-, -, b, hpb, h0, hk⟩ := hp
    have kn : ∀ f, cknow b A p.off.toNat bs f → m.kn f := fun f hf => hh.know f (by rw [hk]; exact hf)
    obtain ⟨blk, hblk, hA⟩ := kn (.addr b A) (.inl rfl)
    obtain ⟨blk', hb', hk', hl', -⟩ := kn _ (.inr ⟨0, hpos, rfl⟩)
    rw [hblk] at hb'; cases hb'
    refine ⟨b, blk, bs, hpb, hblk, hk', hl', h0, hpos, ⟨hA, rfl⟩, fun i hi => ?_⟩
    obtain ⟨blk', hb', -, -, hx⟩ := kn _ (.inr ⟨i, hi, rfl⟩)
    rw [hblk] at hb'; cases hb'; exact hx

/-- A read-only typed value is `const` bytes that decode to it. -/
theorem ConstAt.cpts {T : Type} [Enc T] {a : Nat} {v : T} (hn : 0 < Enc.size T) :
    ConstAt p (fun A bs => (A + p.off.toNat) % a = 0 ∧ bs.size = Enc.size T ∧
      Enc.decode bs = pure v) (cpts p a v) := fun m r rF hh hp => by
  obtain ⟨A, bs, ha, hs, hv, hc⟩ := hp
  obtain ⟨b, blk, bs', h1, h2, h3, h4, h5, h6, ⟨hA, rfl⟩, h8⟩ :=
    ConstAt.cbytesAt (by omega) m r rF hh hc
  exact ⟨b, blk, bs', h1, h2, h3, h4, h5, h6, ⟨hA ▸ ha, hs, hv⟩, h8⟩

/-- The bytes of a live `const` global give its address. -/
theorem ConstAt.addrOf {b : BlockId} {A : Nat} (hpb : p.block = some b)
    (h : ConstAt p φ P) (hφ : ∀ A' bs, φ A' bs → A' = A) : AddrOf b A P := fun m r rF hh hp => by
  obtain ⟨b', blk, bs, hpb', hblk, -, -, -, -, h7, -⟩ := h m r rF hh hp
  rw [hpb] at hpb'; cases hpb'
  exact ⟨blk, hblk, hφ _ _ h7⟩

/-- The bytes of a live `const` global: its block reaches their end. -/
theorem ConstAt.reaches {b : BlockId} {n : Nat} (hpb : p.block = some b) (h : ConstAt p φ P)
    (hφ : ∀ A bs, φ A bs → bs.size = n) : Reaches b (p.off.toNat + n) P := fun m r rF hh hp => by
  obtain ⟨b', blk, bs, hpb', hblk, -, -, -, hpos, h7, hx⟩ := h m r rF hh hp
  rw [hpb] at hpb'; cases hpb'
  obtain ⟨hlt, -⟩ := Array.getElem?_eq_some_iff.mp (hx (bs.size - 1) (by omega))
  exact ⟨blk, hblk, by rw [← hφ _ _ h7]; omega⟩

end Providers

/-- The run of a load from `const` bytes that a provider gives: the value, and the same
resources in the memory after it (only the footprint and the clock change). -/
theorem load_const_step {T : Type} [Enc T] {p : Ptr} {a : Nat} {v : T} {φ : Nat → Array Byte → Prop}
    {P : FAssn} (h : ConstAt p φ P)
    (hφ : ∀ A bs, φ A bs → (A + p.off.toNat) % a = 0 ∧ bs.size = Enc.size T ∧ Enc.decode bs = pure v)
    {m : Mem} {r rF : Res} (hh : Holds m r rF) (hp : P r) (hst : m.FSeq) :
    ∃ m', (Zig.load T a p).run m = pure (v, m') ∧ Holds m' r rF ∧ m'.FSeq := by
  obtain ⟨b, blk, bs, hpb, hblk, hk, hl, h0, hpos, h7, hx⟩ := h m r rF hh hp
  obtain ⟨ha, hs, hv⟩ := hφ _ _ h7
  obtain ⟨hlt, -⟩ := Array.getElem?_eq_some_iff.mp (hx (bs.size - 1) (by omega))
  have hacc : m.access p (Enc.size T) a = pure (b, blk, p.off.toNat) :=
    access_of hpb hblk hl h0 (by omega) ha (by rw [hk]; simp)
  have hext : blk.bytes.extract p.off.toNat (p.off.toNat + Enc.size T) = bs := by
    apply Array.ext
    · simp only [Array.size_extract]; omega
    · intro i h1 h2
      obtain ⟨_, he⟩ := Array.getElem?_eq_some_iff.mp (hx i h2)
      simp only [Array.getElem_extract]; exact he
  exact ⟨_, load_run hacc (by rw [hext]; exact hv) (noRace_of_singleThread hst.1.single _ _ _ _),
    ⟨hh.1, hh.2, hh.3, hh.4, hh.5⟩, ⟨hst.1.recordAt _ _ _ _, hst.2.1, hst.2.2⟩⟩

/-- **Load from a `const` global** (provider form): the bytes come from the knowledge, nothing is
owned or consumed. -/
theorem FTotalTriple.load_const {T : Type} [Enc T] {p : Ptr} {a : Nat} {v : T}
    {φ : Nat → Array Byte → Prop} {P : FAssn} (h : ConstAt p φ P)
    (hφ : ∀ A bs, φ A bs → (A + p.off.toNat) % a = 0 ∧ bs.size = Enc.size T ∧ Enc.decode bs = pure v) :
    FTotalTriple P (Zig.load T a p) (fun x => ⟪x = v⟫ ⋆ P) :=
  FTotalTriple.of_run fun _ r _ hh hp hst => by
    obtain ⟨m', hr, hh', hst'⟩ := load_const_step h hφ hh hp hst
    exact ⟨v, m', r, hr, hh', sep_lift.mpr ⟨rfl, hp⟩, hst'⟩

/-- **Load of a read-only typed value** (`@[fsym]`): the knowledge stays. -/
@[fsym] theorem FTotalTriple.cload {T : Type} [Enc T] {p : Ptr} {a : Nat} {v : T}
    (hn : 0 < Enc.size T) :
    FTotalTriple (cpts p a v) (Zig.load T a p) (fun x => ⟪x = v⟫ ⋆ cpts p a v) :=
  FTotalTriple.load_const (ConstAt.cpts hn) fun _ _ h => h

/-! ## Providers for `fsym` -/

/-- `fsym` provider: nonempty `const` bytes give their block's address. -/
@[fsym_provider] theorem AddrOf.cbytesAt {p : Ptr} {b : BlockId} {A : Nat} {bs : Array Byte}
    (hpb : p.block = some b) (hpos : 0 < bs.size) : AddrOf b A (Zig.Full.cbytesAt p A bs) :=
  (ConstAt.cbytesAt hpos).addrOf hpb fun _ _ h => h.1

/-- `fsym` provider: nonempty `const` bytes: their block reaches their end. -/
@[fsym_provider] theorem Reaches.cbytesAt {p : Ptr} {b : BlockId} {A : Nat} {bs : Array Byte}
    (hpb : p.block = some b) (hpos : 0 < bs.size) :
    Reaches b (p.off.toNat + bs.size) (Zig.Full.cbytesAt p A bs) :=
  (ConstAt.cbytesAt hpos).reaches hpb fun _ _ h => by rw [h.2]

/-- `fsym` provider: a read-only typed value: its block reaches one past it. -/
@[fsym_provider] theorem Reaches.cpts {T : Type} [Enc T] {p : Ptr} {a : Nat} {v : T}
    {b : BlockId} (hpb : p.block = some b) (hn : 0 < Enc.size T) :
    Reaches b (p.off.toNat + Enc.size T) (Zig.Full.cpts p a v) :=
  (ConstAt.cpts hn).reaches hpb fun _ _ h => h.2.1

end Full
end Zig
