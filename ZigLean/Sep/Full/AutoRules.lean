import ZigLean.Sep.Full.AutoAttr
import ZigLean.Sep.Full.AutoArith
import ZigLean.Sep.Full.Ops
import ZigLean.Sep.Full.AllocSpec
import ZigLean.Sep.Full.Reclaim
import ZigLean.Sep.AllocSpec.Ops
import ZigLean.Sep.AllocSpec.Norm
import ZigLean.Range

/-!
# The rule library of the full-state symbolic executor (`fsym`, `docs/proof-automation.md`)

General lemmas that `fsym` (`ZigLean/Sep/Full/Auto.lean`) applies; nothing here is about one std
module.

* **Structural steps** over any `FLogic` (`FLogic.total`: `FTotalTriple`, `FLogic.partial`:
  `FTriple`): a step by a total rule on a framed part (`step`) or on the whole precondition
  (`stepAll`), a return through a frame-preserving update (`ret`), existentials and facts of the
  precondition (`ex_sep`, `lift_sep`).
* **Step rules** (`@[fsym]`): pointer operations from the providers of `Ops.lean`, loads and
  stores of `pts`, the overflow-checked arithmetic of generated code.
* **Fields** of typed values (`EncField`, with `EncField.comp` for a field of a field): what the
  field rules of `Typed.lean` read and write; `fsym` derives them for generated structs.
* **Providers** (`AddrOf`, `Reaches`, `Live`, `Active`): from one of the precondition's atoms
  (`known`, an untagged `bshare`, an owned `pts` or region, an allocator's own state), or from the
  whole precondition (a share whose tag is active, a ledger at its epoch), lifted by `K.of_within`.
  Pointer `==` across two live blocks (`ptrEqAddr_live`).
* **`Junk`** (the library's, `Full/AllocSpec.lean`): bytes an allocator gave up (padding, leaked
  frees); an `up` part is absorbed.
* **`fsym_norm`** and **`fsym_arith`**: the simp sets for programs and side goals.
-/

namespace Zig.Full.Auto

open FAssn

/-! ## Structural steps over any `FLogic` -/

section Steps

variable (L : FLogic) {α β γ : Type} {P P' P₀ R : FAssn} {Q : β → FAssn} {c : MemM β}

theorem pre (h : ∀ r, P r → P' r) (t : L.T P' c Q) : L.T P c Q := L.pre t h

theorem pre_eq (h : P = P') (t : L.T P' c Q) : L.T P c Q := h ▸ t

theorem bind_pure (t : L.T P (c >>= pure) Q) : L.T P c Q := by
  simpa only [_root_.bind_pure] using t

/-- A command proved by a total rule on the part `P₀`, framed by `R`. -/
theorem step {c : MemM α} {f : α → MemM β} {Q₀ : α → FAssn} (r : FTotalTriple P₀ c Q₀)
    (k : ∀ v, L.T (Q₀ v ⋆ R) (f v) Q) : L.T (P₀ ⋆ R) (c >>= f) Q :=
  L.bind (L.frame (L.ofTotal r)) k

/-- A command proved by a total rule on the whole precondition. -/
theorem stepAll {c : MemM α} {f : α → MemM β} {Q₀ : α → FAssn} (r : FTotalTriple P c Q₀)
    (k : ∀ v, L.T (Q₀ v) (f v) Q) : L.T P (c >>= f) Q :=
  L.bind (L.ofTotal r) k

/-- **A return**, after a frame-preserving update into the postcondition. -/
theorem ret {v : β} (h : EUpd P (Q v)) : L.T P (pure v) Q :=
  L.ofTotal (FTotalTriple.eupd h (FTotalTriple.ret v))

theorem ex_sep {F : γ → FAssn} (t : ∀ x, L.T (F x ⋆ R) c Q) : L.T (FAssn.ex F ⋆ R) c Q :=
  L.pre (L.ex (P := fun x => F x ⋆ R) t) fun _ h => sep_ex.mp h

theorem lift_sep {φ : Prop} (t : φ → L.T R c Q) : L.T (⟪φ⟫ ⋆ R) c Q := L.lift t

theorem of_false (h : False) : L.T P c Q := h.elim

/-- The join of two branches' posts (a walk whose post it infers, `joinPosts`): the left one. -/
theorem join_l {Q₁ Q₂ : β → FAssn} (t : L.T P c Q₁) :
    L.T P c (fun v => FAssn.ex fun b : Bool => if b = true then Q₁ v else Q₂ v) :=
  L.post t fun _ _ h => ⟨true, h⟩

/-- The join of two branches' posts: the right one. -/
theorem join_r {Q₁ Q₂ : β → FAssn} (t : L.T P c Q₂) :
    L.T P c (fun v => FAssn.ex fun b : Bool => if b = true then Q₁ v else Q₂ v) :=
  L.post t fun _ _ h => ⟨false, h⟩

end Steps

/-! ## Facts of atoms -/

/-- The assertion `X` implies the fact `φ` (a facts lemma, `@[fsym_facts]`). -/
def AtomFacts (X : FAssn) (φ : Prop) : Prop := ∀ r, X r → φ

theorem AtomFacts.sepL {X R : FAssn} {φ : Prop} (h : AtomFacts X φ) {r : Res} (hr : (X ⋆ R) r) : φ := by
  obtain ⟨r₁, -, -, -, h1, -⟩ := hr; exact h r₁ h1

/-- A fact of a part `X` of the precondition, in the context. -/
theorem pre_fact (L : FLogic) {β : Type} {R : FAssn} {Q : β → FAssn} {c : MemM β} {X : FAssn} {φ : Prop}
    (hX : AtomFacts X φ) (t : φ → L.T (X ⋆ R) c Q) : L.T (X ⋆ R) c Q :=
  L.pre (L.lift t) fun _ h => sep_lift.mpr ⟨hX.sepL h, h⟩

/-- The assertion `X`, held in a memory, implies the fact `φ` (a facts lemma, `@[fsym_facts]`):
facts that need the memory or the whole ghost state, such as a token's grant in its authority's
map (`gauthP γ e M t ⋆ gfrag γ e i g`, `gfrag_mem`) or two owned regions apart. `X` is one atom
or a pair `X₁ ⋆ X₂` of atoms. Library lemmas: `facts_gfrag` (AutoConc), `MemFacts.regions_apart`
(Full/Region). -/
def _root_.Zig.Full.MemFacts (X : FAssn) (φ : Prop) : Prop :=
  ∀ m r rF, Holds m r rF → X r → m.FSeq → φ

theorem _root_.Zig.Full.MemFacts.sepL {X R : FAssn} {φ : Prop} (h : MemFacts X φ) :
    MemFacts (X ⋆ R) φ := fun m _ _ hh hp hs => by
  obtain ⟨r₁, r₂, hd, rfl, h1, -⟩ := hp
  exact h m r₁ _ (Holds.split hd hh) h1 hs

/-- A fact of a part, of the whole state (`stateFacts`). -/
theorem AtomFacts.mem {X R : FAssn} {φ : Prop} (h : AtomFacts X φ) : MemFacts (X ⋆ R) φ :=
  fun _ _ _ _ hp _ => h.sepL hp

theorem MemFacts.of_eq {P P' : FAssn} {φ : Prop} (e : P = P') (h : MemFacts P' φ) : MemFacts P φ :=
  e ▸ h

theorem MemFacts.and {P : FAssn} {φ ψ : Prop} (h₁ : MemFacts P φ) (h₂ : MemFacts P ψ) :
    MemFacts P (φ ∧ ψ) :=
  fun m r rF hh hp hs => ⟨h₁ m r rF hh hp hs, h₂ m r rF hh hp hs⟩

/-- The facts of the precondition, as an update that keeps it. -/
theorem _root_.Zig.Full.MemFacts.eupd {P : FAssn} {φ : Prop} (h : MemFacts P φ) : EUpd P (⟪φ⟫ ⋆ P) :=
  fun m r rF hh hp hs => ⟨r, hh, sep_lift.mpr ⟨h m r rF hh hp hs, hp⟩⟩

/-- An update of the precondition, in any logic (a return of `()` bound to the program). -/
theorem pre_eupd (L : FLogic) {β : Type} {P P' : FAssn} {Q : β → FAssn} {c : MemM β}
    (h : EUpd P P') (t : L.T P' c Q) : L.T P c Q :=
  L.congr (fun _ _ => rfl) (L.bind (ret L (Q := fun _ => P') (v := ()) h) fun _ => t)

/-- A memory fact of the precondition, in the context (any logic). -/
theorem _root_.Zig.Full.MemFacts.pre (L : FLogic) {β : Type} {P : FAssn} {c : MemM β} {Q : β → FAssn}
    {φ : Prop} (hX : MemFacts P φ) (t : φ → L.T P c Q) : L.T P c Q :=
  pre_eupd L hX.eupd (L.lift t)

/-- A fact of a part `X` of the precondition that needs the memory, in the context. -/
theorem pre_mfact (L : FLogic) {β : Type} {R : FAssn} {Q : β → FAssn} {c : MemM β} {X : FAssn} {φ : Prop}
    (hX : MemFacts X φ) (t : φ → L.T (X ⋆ R) c Q) : L.T (X ⋆ R) c Q :=
  MemFacts.pre L hX.sepL t

section Facts

variable {p : Ptr} {A S a : Nat} {K : BlockKind} {bs : Array Byte}

/-- An owned region: the block of its pointer, a nonnegative offset, its alignment. -/
@[fsym_facts] theorem facts_region :
    AtomFacts (up (regionIn p A S K a bs)) ((∃ b, p.block = some b) ∧ 0 ≤ p.off ∧ (A + p.off.toNat) % a = 0) := by
  rintro r ⟨⟨ha, -, b, hb, h0, -⟩, -⟩; exact ⟨⟨b, hb⟩, h0, ha⟩

/-- Owned bytes: the block of their pointer, a nonnegative offset. -/
@[fsym_facts] theorem facts_bytes :
    AtomFacts (up (bytesAt p A S K bs)) ((∃ b, p.block = some b) ∧ 0 ≤ p.off) := by
  rintro r ⟨⟨b, hb, h0, -⟩, -⟩; exact ⟨⟨b, hb⟩, h0⟩

/-- A typed value: the block of its pointer, a nonnegative offset. -/
@[fsym_facts] theorem facts_pts {T : Type} [Enc T] {v : T} :
    AtomFacts (up (pts p a v)) ((∃ b, p.block = some b) ∧ 0 ≤ p.off) := by
  rintro r ⟨⟨-, -, -, -, -, -, -, ⟨b, hb, h0, -⟩, -⟩, -⟩; exact ⟨⟨b, hb⟩, h0⟩

/-- An atomic word: the block of its pointer, a nonnegative offset. -/
@[fsym_facts] theorem facts_apts {v : BitVec 64} :
    AtomFacts (apts p v) ((∃ b, p.block = some b) ∧ 0 ≤ p.off) := by
  rintro r ⟨-, -, -, -, -, -, -, -, -, -, b, hb, h0, -⟩; exact ⟨⟨b, hb⟩, h0⟩

/-- Two separately owned nonempty regions of one block do not overlap (by offsets;
`MemFacts.regions_apart` compares addresses, also across blocks). The premises come from the
context (blocks) and the arithmetic solver (sizes). -/
@[fsym_facts] theorem facts_regions_block {q : Ptr} {b : BlockId} {A' S' a' : Nat} {K' : BlockKind}
    {cs : Array Byte} (hp : p.block = some b) (hq : q.block = some b) (hn : 0 < bs.size)
    (hn' : 0 < cs.size) :
    AtomFacts (up (regionIn p A S K a bs) ⋆ up (regionIn q A' S' K' a' cs))
      (p.off.toNat + bs.size ≤ q.off.toNat ∨ q.off.toNat + cs.size ≤ p.off.toNat) := by
  rintro r ⟨r₁, r₂, hd, rfl, h1, h2⟩
  refine Classical.byContradiction fun hc => ?_
  -- the later start lies in both
  obtain ⟨x, hx1, hx2⟩ : ∃ x, (p.off.toNat ≤ x ∧ x < p.off.toNat + bs.size) ∧
      (q.off.toNat ≤ x ∧ x < q.off.toNat + cs.size) := by
    rcases Nat.le_total p.off.toNat q.off.toNat with h | h
    · exact ⟨q.off.toNat, by omega, by omega⟩
    · exact ⟨p.off.toNat, by omega, by omega⟩
  obtain ⟨f1, e1, -⟩ := Owns.region (a := a) (S := S) hp (i := x - p.off.toNat) (by omega) r₁ h1
  obtain ⟨f2, e2, -⟩ := Owns.region (a := a') (S := S') hq (i := x - q.off.toNat) (by omega) r₂ h2
  rw [show p.off.toNat + (x - p.off.toNat) = x by omega] at e1
  rw [show q.off.toNat + (x - q.off.toNat) = x by omega] at e2
  rcases hd (b, x) with e | e <;> simp_all

/-- Two owned nonempty regions of one block carry the block's labels: the same address and the
same kind up to `BlockKind.norm` (`Owns.block`). -/
@[fsym_facts] theorem facts_regions_labels {q : Ptr} {b : BlockId} {A' S' a' : Nat} {K' : BlockKind}
    {cs : Array Byte} (hp : p.block = some b) (hq : q.block = some b) (hn : 0 < bs.size)
    (hn' : 0 < cs.size) :
    MemFacts (up (regionIn p A S K a bs) ⋆ up (regionIn q A' S' K' a' cs)) (A = A' ∧ K.norm = K'.norm) := by
  intro m r rF hh hr _
  obtain ⟨b1, e1, -, -, -, a1, k1⟩ :=
    (Owns.within (Owns.region (a := a) (S := S) hp hn) (Within.sepL (Within.refl _))).block hh hr
  obtain ⟨b2, e2, -, -, -, a2, k2⟩ :=
    (Owns.within (Owns.region (a := a') (S := S') hq hn') (Within.sepR (Within.refl _))).block hh hr
  rw [e1] at e2; cases e2
  exact ⟨a1.symm.trans a2, k1.symm.trans k2⟩

end Facts

/-! ## Providers from atoms -/

section Providers

variable {b : BlockId} {A k : Nat}

/-- A nonempty owned byte range at `p` (in block `b`): the block's address. -/
theorem AddrOf.bytes {Y : Assn} {p : Ptr} (hpb : p.block = some b)
    (hy : ∀ h, Y h → ∃ S K bs, 0 < bs.size ∧ bytesAt p A S K bs h) : AddrOf b A (up Y) :=
  AddrOf.owned fun r hr => by
    obtain ⟨S, K, bs, hpos, hb⟩ := hy _ hr.1
    obtain ⟨b', hb', h0, hl⟩ := id hb
    rw [hpb] at hb'; cases hb'
    have hc : r.heap.erase (b, p.off.toNat + (bs.size - 1)) = some ⟨bs[bs.size - 1]!, A, S, K⟩ := by
      rw [hl]; simp only [true_and]; rw [if_pos ⟨by omega, by omega⟩]; congr 3; omega
    obtain ⟨fc, hfc, he⟩ := erase_cell hc
    exact ⟨_, fc, hfc, by rw [he]⟩

/-- A nonempty region: its block's address. -/
theorem AddrOf.region {p : Ptr} {A S : Nat} {K : BlockKind} {a : Nat} {bs : Array Byte}
    (hpb : p.block = some b) (hpos : 0 < bs.size) : AddrOf b A (up (regionIn p A S K a bs)) :=
  AddrOf.bytes hpb fun _ hr => ⟨S, K, bs, hpos, hr.2.2⟩

end Providers

attribute [fsym_provider] AddrOf.known AddrOf.region Reaches.share

/-! ## Providers over the whole precondition

A provider kind `K … P` (`AddrOf`, `Reaches`, `Live`, `Active`) has a lemma `K.of_within`: what
an atom `X` of the precondition provides, the precondition provides (`Within X P`). `fsym` proves
a provider goal by an atom lemma (`@[fsym_provider]` with the conclusion `K … X` of an atom `X`)
on one of the precondition's parts, or by a lemma about the whole precondition (the conclusion
`K … P` of a variable `P`), whose hypotheses (`Within X P`, providers, blocks, arithmetic) are
solved in turn. -/

/-- Every resource of `P` has the tag `t` active (`Act`): the root, or a ledger at its epoch whose
authority is a part of `P` under an active parent. A share tagged `t` gives its block while `t`
is active (`Holds.bshare`). -/
def _root_.Zig.Full.Active (t : STag) (P : FAssn) : Prop := ∀ r, P r → Act r.gh.ls t

/-- Every memory that holds `P` has block `b` live with at least `k` bytes, live from offset `l`
on (at or above its first live offset, `BlockKind.mappedLo`): owned bytes from `l` to below `k`.
Two live blocks share no live byte (pointer `==` across blocks, `ptrEqAddr_live`); a share gives
no such bound (the bytes below an OS mapping's first live offset may be a thread's stack, MM-19). -/
def _root_.Zig.Full.Live (b : BlockId) (l k : Nat) (P : FAssn) : Prop :=
  ∀ m r rF, Holds m r rF → P r → ∃ blk, m.blocks[b]? = some blk ∧ blk.live = true ∧
    blk.kind.mappedLo ≤ l ∧ k ≤ blk.bytes.size

section Whole

variable {b : BlockId} {A l k : Nat} {t : STag} {P X : FAssn}

theorem _root_.Zig.Full.AddrOf.of_within (h : AddrOf b A X) (hw : Within X P) : AddrOf b A P :=
  fun m r rF hh hp => by obtain ⟨_, h'⟩ := hw r hp; exact h.sepL m r rF hh h'

theorem _root_.Zig.Full.Reaches.of_within (h : Reaches b k X) (hw : Within X P) : Reaches b k P :=
  fun m r rF hh hp => by obtain ⟨_, h'⟩ := hw r hp; exact h.sepL m r rF hh h'

theorem _root_.Zig.Full.Active.of_within (h : Active t X) (hw : Within X P) : Active t P :=
  fun r hp => by
    obtain ⟨_, r₁, r₂, -, rfl, h1, -⟩ := hw r hp
    exact (h r₁ h1).mono (Ghost.ls_add _ _)

theorem _root_.Zig.Full.Live.of_within (h : Live b l k X) (hw : Within X P) : Live b l k P :=
  fun m r rF hh hp => by
    obtain ⟨_, r₁, r₂, hd, rfl, h1, -⟩ := hw r hp
    exact h m r₁ _ (Holds.split hd hh) h1

/-- The root tag is always active. -/
theorem _root_.Zig.Full.Active.root : Active none P := fun _ _ => Act.root

/-- An allocator's own state keeps its tag active (`FAllocInv.act`). -/
theorem _root_.Zig.Full.Active.allocOwn (I : FAllocInv) : Active I.tag I.own := I.act

/-- A ledger at its epoch under an active parent: its tag is active (`act_gauthP`). -/
theorem _root_.Zig.Full.Active.gauthP {γ e : Nat} {M : GMap} {p : STag}
    (hw : Within (gauthP γ e M p) P) (hp : Active p P) : Active (some (γ, e)) P :=
  fun r hr => act_gauthP hw hr (hp r hr)

/-- A share whose tag is active: its block reaches the share's bound. -/
theorem _root_.Zig.Full.Reaches.shareW {q : Frac} (hw : Within (bshare b q k t) P) (ha : Active t P) :
    Reaches b k P := fun m r rF hh hp => by
  obtain ⟨blk, hb, -, hk, -⟩ := hh.bshareW hw hp (ha r hp)
  exact ⟨blk, hb, hk⟩

/-- Owned byte `i` of a `bytesAt`. -/
theorem _root_.Zig.Full.bytesAt_ownsAt_at {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte}
    {h : Heap} (hb : bytesAt p A S K bs h) {i : Nat} (hi : i < bs.size) :
    ∃ b, p.block = some b ∧ 0 ≤ p.off ∧ ∃ c, h (b, p.off.toNat + i) = some c := by
  obtain ⟨b, hpb, h0, hl⟩ := hb
  refine ⟨b, hpb, h0, ⟨bs[i]!, A, S, K⟩, ?_⟩
  rw [hl]; simp only [true_and]; rw [if_pos ⟨by omega, by omega⟩]; congr 3; omega

/-- A nonempty owned byte range at `p` (in block `b`): the block is live from `p` on and reaches
the range's end. -/
theorem _root_.Zig.Full.Live.bytes {Y : Assn} {p : Ptr} {n : Nat} (hpb : p.block = some b)
    (hy : ∀ h, Y h → ∃ A S K bs, 0 < bs.size ∧ n ≤ bs.size ∧ bytesAt p A S K bs h) :
    Live b p.off.toNat (p.off.toNat + n) (up Y) := fun m r rF hh hr => by
  obtain ⟨A, S, K, bs, hpos, hn, hb⟩ := hy _ hr.1
  have cell : ∀ i, i < bs.size → ∃ blk, m.blocks[b]? = some blk ∧ blk.live = true ∧
      p.off.toNat + i < blk.bytes.size ∧ blk.kind.mappedLo ≤ p.off.toNat + i := fun i hi => by
    obtain ⟨b', hb', -, c, hc⟩ := bytesAt_ownsAt_at hb hi
    rw [hpb] at hb'; cases hb'
    obtain ⟨fc, hfc, -⟩ := erase_cell hc
    obtain ⟨blk, hblk, hl, hj, hlo, -⟩ := hh.block hfc
    exact ⟨blk, hblk, hl, hj, hlo⟩
  obtain ⟨blk, hblk, hl, hj, -⟩ := cell (bs.size - 1) (by omega)
  obtain ⟨blk', hblk', -, -, hlo⟩ := cell 0 hpos
  rw [hblk] at hblk'; cases hblk'
  exact ⟨blk, hblk, hl, by omega, by omega⟩

/-- A nonempty region: its block is live from the region on and reaches its end. -/
theorem _root_.Zig.Full.Live.region {p : Ptr} {A S : Nat} {K : BlockKind} {a : Nat} {bs : Array Byte}
    (hpb : p.block = some b) (hpos : 0 < bs.size) :
    Live b p.off.toNat (p.off.toNat + bs.size) (up (regionIn p A S K a bs)) :=
  Live.bytes hpb fun _ hr => ⟨A, S, K, bs, hpos, Nat.le_refl _, hr.2.2⟩

/-- A typed value at `p`: its block is live from `p` on and reaches one past it. -/
theorem _root_.Zig.Full.Live.pts {T : Type} [Enc T] {p : Ptr} {a : Nat} {v : T} (hpb : p.block = some b)
    (hn : 0 < Enc.size T) : Live b p.off.toNat (p.off.toNat + Enc.size T) (up (Zig.pts p a v)) :=
  Live.bytes hpb fun _ hp => by
    obtain ⟨A, S, K, bs, -, hs, -, hb, -⟩ := hp
    exact ⟨A, S, K, bs, by omega, by omega, hb⟩

/-- A live block reaches its bound (owned bytes, `Live.region`/`Live.pts`). -/
theorem _root_.Zig.Full.Reaches.of_live (h : Live b l k P) : Reaches b k P := fun m r rF hh hp => by
  obtain ⟨blk, hb, -, -, hk⟩ := h m r rF hh hp
  exact ⟨blk, hb, hk⟩

/-- A live block's extent from any bound it reaches: liveness and the first live offset `l` from
owned bytes (`hl`), the bound `k` from another part (a share's bound, `Reaches.shareW`, or owned
bytes further up). Not a provider (with `Reaches.of_live` it would cycle): rules take the two
apart (`ptrEqAddr_live`). -/
theorem _root_.Zig.Full.Live.reach {k₀ : Nat} (hl : Live b l k₀ P) (hr : Reaches b k P) : Live b l k P :=
  fun m r rF hh hp => by
    obtain ⟨blk, hb, hlv, hlo, -⟩ := hl m r rF hh hp
    obtain ⟨blk', hb', hk⟩ := hr m r rF hh hp
    rw [hb] at hb'; cases hb'
    exact ⟨blk, hb, hlv, hlo, hk⟩

end Whole

attribute [fsym_provider] Active.root Active.allocOwn Active.gauthP Live.region Live.pts
  Reaches.shareW Reaches.of_live

/-- `ptrEqAddr p q` of pointers into blocks `b` and `b'` at the blocks' addresses. -/
theorem ptrEqAddr_blocks_run {m : Mem} {p q : Ptr} {b b' : BlockId} {blk blk' : Block}
    (hp : p.block = some b) (hb : m.blocks[b]? = some blk) (hq : q.block = some b')
    (hb' : m.blocks[b']? = some blk') :
    (ptrEqAddr p q).run m = pure (decide ((blk.addr : Int) + p.off = (blk'.addr : Int) + q.off), m) := by
  obtain ⟨pb, po⟩ := p
  obtain ⟨qb, qo⟩ := q
  simp only at hp hq; subst hp hq
  unfold ptrEqAddr
  simp only [StateT.run_bind, ptrAddr_run hb, pure_bind, ptrAddr_run hb', StateT.run_pure]

/-- **Pointer `==` of pointers into two live blocks** (possibly the same one): equal when the
blocks and the offsets are. Both pointers are at live bytes (from `l`, `l'` on, `Live`) in bounds,
or both are past a live byte (up to one past the end): two live blocks share no live byte
(`Mem.LiveDisjoint.addr_ne`), but one block's end may be the next one's start, and a byte below an
OS mapping's first live offset may be another block's (MM-19). Each block's first live offset
comes from owned bytes (`Live`) and its bound from any part that reaches it (`Reaches`: a share's
bound, or owned bytes further up; `Live.reach`): a pointer one past a full node lies past the
node's header and within its share. -/
@[fsym] theorem FTotalTriple.ptrEqAddr_live {p q : Ptr} {b b' : BlockId} {l l' k₀ k₀' k k' : Nat}
    {P : FAssn} (hpb : p.block = some b) (hqb : q.block = some b') (hp : Live b l k₀ P)
    (hpk : Reaches b k P) (hq : Live b' l' k₀' P) (hqk : Reaches b' k' P)
    (hk : ((l : Int) ≤ p.off ∧ p.off < k ∧ (l' : Int) ≤ q.off ∧ q.off < k') ∨
      ((l : Int) < p.off ∧ p.off ≤ k ∧ (l' : Int) < q.off ∧ q.off ≤ k')) :
    FTotalTriple P (ptrEqAddr p q) (fun r => ⟪r = decide (b = b' ∧ p.off = q.off)⟫ ⋆ P) :=
  FTotalTriple.of_read fun m r rF hh hr hs => by
    obtain ⟨blk, hb, hl, hlo, hsz⟩ := Live.reach hp hpk m r rF hh hr
    obtain ⟨blk', hb', hl', hlo', hsz'⟩ := Live.reach hq hqk m r rF hh hr
    rw [ptrEqAddr_blocks_run hpb hb hqb hb']
    congr 2
    by_cases hbb : b = b'
    · subst hbb
      rw [hb] at hb'; cases hb'
      exact decide_eq_decide.mpr ⟨fun h => ⟨rfl, by omega⟩, fun h => by omega⟩
    · have hne : ∀ x x', l ≤ x → x < blk.bytes.size → l' ≤ x' → x' < blk'.bytes.size →
          blk.addr + x ≠ blk'.addr + x' :=
        fun x x' h0 hx h0' hx' => hs.2.2.1.addr_ne hbb hb hb' hl hl' hx hx' (by omega) (by omega)
      refine decide_eq_decide.mpr ⟨fun h => ?_, fun h => absurd h.1 hbb⟩
      rcases hk with ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩
      · exact absurd h (by
          have := hne p.off.toNat q.off.toNat (by omega) (by omega) (by omega) (by omega); omega)
      · exact absurd h (by
          have := hne (p.off.toNat - 1) (q.off.toNat - 1) (by omega) (by omega) (by omega) (by omega)
          omega)

/-! ## Fields of typed values (`EncField`) -/

theorem result_pure_inj {α : Type} {a b : α} (h : (pure a : Result α) = pure b) : a = b := by
  have := congrArg (fun r : Result α => r.run) h
  simpa [pure, ExceptT.pure, ExceptT.mk, ExceptT.run] using this

theorem result_bind_of_pure {α β : Type} {x : Result α} {f : α → Result β} {a : α} {b : β}
    (hx : x = pure a) (hf : f a = pure b) : x >>= f = pure b := by
  rw [hx]; exact hf

theorem writeBytes_nested (bs cs : Array Byte) (o₁ o₂ n : Nat) (h₁ : o₁ + n ≤ bs.size)
    (h₂ : o₂ + cs.size ≤ n) :
    writeBytes bs (o₁ + o₂) cs = writeBytes bs o₁ (writeBytes (bs.extract o₁ (o₁ + n)) o₂ cs) := by
  apply Array.ext
  · simp [writeBytes]; omega
  · intro i h1 h2
    simp only [writeBytes, Array.size_append, Array.size_extract] at h1 h2
    simp only [writeBytes, Array.getElem_append, Array.getElem_extract, Array.size_append,
      Array.size_extract]
    have e1 : Min.min (o₁ + o₂) bs.size = o₁ + o₂ := by omega
    have e2 : Min.min o₁ bs.size = o₁ := by omega
    have e3 : Min.min (o₁ + n) bs.size = o₁ + n := by omega
    simp only [e1, e2, e3, Nat.min_self, Nat.sub_zero, Nat.add_sub_cancel_left] at h1 h2 ⊢
    repeat' split
    all_goals first | rfl | omega | (congr 1; omega)

end Zig.Full.Auto

namespace Zig.Full

/-- **The field at byte `o`** of a typed value (`T`), a `U`: every encoding of `s` holds
`get s` there, and bytes that decode to `v` written there make an encoding of `set s v`. The
field rules (`FTotalTriple.encField_load`/`_store`, `Typed.lean`) read and write the fields of a
stored value through it. `fsym` derives it for any struct the translator generates (and for
`Slice`), a field of a field by `EncField.comp` (`Auto.lean` `encFieldOf?`). -/
structure EncField (T U : Type) [Enc T] [Enc U] (o : Nat) (get : T → U) (set : T → U → T) :
    Prop where
  fit : o + Enc.size U ≤ Enc.size T
  get_dec : ∀ {bs : Array Byte} {s : T}, bs.size = Enc.size T → Enc.decode bs = pure s →
    Enc.decode (bs.extract o (o + Enc.size U)) = pure (get s)
  set_dec : ∀ {bs cs : Array Byte} {s : T} {v : U}, bs.size = Enc.size T →
    Enc.decode bs = pure s → cs.size = Enc.size U → Enc.decode cs = pure v →
    Enc.decode (writeBytes bs o cs) = pure (set s v)

/-- A field of a field. -/
theorem EncField.comp {T V U : Type} [Enc T] [Enc V] [Enc U] {o₁ o₂ : Nat} {g₁ : T → V}
    {s₁ : T → V → T} {g₂ : V → U} {s₂ : V → U → V} (h₁ : EncField T V o₁ g₁ s₁)
    (h₂ : EncField V U o₂ g₂ s₂) :
    EncField T U (o₁ + o₂) (fun s => g₂ (g₁ s)) (fun s v => s₁ s (s₂ (g₁ s) v)) where
  fit := by have := h₁.fit; have := h₂.fit; omega
  get_dec {bs s} hs hd := by
    have hx : (bs.extract o₁ (o₁ + Enc.size V)).size = Enc.size V := by
      have := h₁.fit; simp; omega
    have := h₂.get_dec hx (h₁.get_dec hs hd)
    rwa [Array.extract_extract, Nat.min_eq_left (by have := h₂.fit; omega), ← Nat.add_assoc]
      at this
  set_dec {bs cs s v} hs hd hc hv := by
    have hx : (bs.extract o₁ (o₁ + Enc.size V)).size = Enc.size V := by
      have := h₁.fit; simp; omega
    have hw := h₂.set_dec hx (h₁.get_dec hs hd) hc hv
    rw [Auto.writeBytes_nested bs cs o₁ o₂ (Enc.size V) (by have := h₁.fit; omega)
      (by have := h₂.fit; omega)]
    exact h₁.set_dec hs hd (by rw [writeBytes_size _ _ _ (by have := h₂.fit; omega), hx]) hw

end Zig.Full

namespace Zig.Full.Auto

open FAssn

/-! Steps of a derived field (`Auto.lean` `encFieldOf?`): a generated struct decodes its fields
one after the other (`do pure { f := ← Enc.decodeAt bs o, … }`); after `result_bind_eq_pure`
splits the decoding, these give a field (`get`) and a write into one (`set`). -/

/-- A field that is all of the bytes (a struct of one field). -/
theorem decode_extract_full {U : Type} [Enc U] {bs : Array Byte} {N : Nat} {v : U}
    (hs : bs.size = N) (hN : N = 0 + Enc.size U) (h : Enc.decode bs = pure v) :
    Enc.decode (bs.extract 0 (0 + Enc.size U)) = pure v := by
  rwa [Array.extract_eq_self_of_le (by omega)]

/-- A field (bytes `[lo, hi)`) that the write does not touch. -/
theorem decode_write_other {U : Type} [Enc U] {bs cs : Array Byte} {N n o lo hi : Nat} {a : U}
    (hs : bs.size = N) (hc : cs.size = n) (hfit : o + n ≤ N ∧ lo ≤ hi ∧ hi ≤ N)
    (hd : o + n ≤ lo ∨ hi ≤ o) (h : Enc.decode (bs.extract lo hi) = pure a) :
    Enc.decode ((writeBytes bs o cs).extract lo hi) = pure a := by
  have := extract_writeBytes_disjoint bs o cs lo (hi - lo) (by omega) (by omega) (by omega)
  rw [Nat.add_sub_cancel' hfit.2.1] at this
  rwa [this]

/-- The written field (bytes `[o, hi)`). -/
theorem decode_write_same {U : Type} [Enc U] {bs cs : Array Byte} {N o hi : Nat} {v : U}
    (hs : bs.size = N) (hc : cs.size = Enc.size U) (hfit : hi = o + Enc.size U ∧ hi ≤ N)
    (hv : Enc.decode cs = pure v) :
    Enc.decode ((writeBytes bs o cs).extract o hi) = pure v := by
  have := extract_writeBytes bs o cs (by omega)
  rw [hc, ← hfit.1] at this; rwa [this]

/-- The written field that is all of the bytes. -/
theorem decode_write_full {U : Type} [Enc U] {bs cs : Array Byte} {N : Nat} {v : U}
    (hs : bs.size = N) (hc : cs.size = Enc.size U) (hN : N = Enc.size U)
    (hv : Enc.decode cs = pure v) : Enc.decode (writeBytes bs 0 cs) = pure v := by
  rwa [writeBytes_all (by omega)]

/-! ## Memory and pointer rules -/

-- Rules registered later are tried first: `ptrProject_elem_of` before `ptrProject_of`, which
-- also matches `(·.elem size i)` by unfolding and would leave the item pointer as `p.add k`
-- (no longer the `p.elem size i` of the array rules, `Full/Arr`).
attribute [fsym] FTotalTriple.load FTotalTriple.store FTotalTriple.ptrAddr_of
  FTotalTriple.checkAlign_of FTotalTriple.ptrEqAddr_of FTotalTriple.ptrProject_of
  FTotalTriple.ptrProject_elem_of

/-- The size of written bytes, for the arithmetic solver (a region written after its
allocation, or twice). -/
@[fsym_arith] theorem _root_.Zig.Full.size_writeBytes (a : Array Byte) (o : Nat) (bs : Array Byte) :
    (writeBytes a o bs).size = Min.min o a.size + bs.size + (a.size - (o + bs.size)) := by
  simp [writeBytes]; omega

attribute [fsym_arith] Array.size_replicate

/-! ## Overflow-checked arithmetic -/

section Arith

variable {w : Nat} {P : FAssn}

/-- A word result with its value: the step rules below leave `r` opaque with the fact
`r.toNat = …` (a symbolic execution in SSA form), so later terms mention `r` and not the
growing expression that computed it. -/
theorem read_val {v : BitVec w} {n : Nat} (h : v.toNat = n) :
    FTotalTriple P (pure v : MemM (BitVec w)) (fun r => ⟪r.toNat = n⟫ ⋆ P) :=
  (FTotalTriple.ret (Q := fun r => ⟪r.toNat = n⟫ ⋆ P) v).pre fun _ hp => sep_lift.mpr ⟨h, hp⟩

/-- An unsigned `+` that does not overflow is its wrapped sum (the step rules of every
backend: `add_step`, `WP.liftMem_add`, the literal simproc's `add_lit`). `safe` (`add_safe` or
plain `add`) decides only the error of an overflow, so every rule holds for both. -/
theorem add_ok {a b : BitVec w} {safe : Bool} (h : a.toNat + b.toNat < 2 ^ w) :
    Zig.add false a b safe = pure (a + b) := by
  simp only [Zig.add, BitVec.uaddOverflow, Bool.false_eq_true, ↓reduceIte]
  rw [if_neg (by simp; omega)]

/-- An unsigned `-` that does not overflow is its wrapped difference. -/
theorem sub_ok {a b : BitVec w} {safe : Bool} (h : b.toNat ≤ a.toNat) :
    Zig.sub false a b safe = pure (a - b) := by
  simp only [Zig.sub, BitVec.usubOverflow, Bool.false_eq_true, ↓reduceIte]
  rw [if_neg (by simp; omega)]

/-- The value of `sub_ok`'s difference, stated without truncated subtraction (which `omega`
would case-split on). -/
theorem sub_val {a b : BitVec w} (h : b.toNat ≤ a.toNat) : (a - b).toNat + b.toNat = a.toNat := by
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr h)]; omega

/-- An unsigned `+` that does not overflow. -/
@[fsym] theorem add_step {a b : BitVec w} {safe : Bool} (h : a.toNat + b.toNat < 2 ^ w) :
    FTotalTriple P (StateT.lift (Zig.add false a b safe) : MemM (BitVec w))
      (fun r => ⟪r.toNat = a.toNat + b.toNat⟫ ⋆ P) := by
  rw [add_ok h]; exact read_val (BitVec.toNat_add_of_lt h)

/-- An unsigned `-` that does not overflow (its value as `sub_val`). -/
@[fsym] theorem sub_step {a b : BitVec w} {safe : Bool} (h : b.toNat ≤ a.toNat) :
    FTotalTriple P (StateT.lift (Zig.sub false a b safe) : MemM (BitVec w))
      (fun r => ⟪r.toNat + b.toNat = a.toNat⟫ ⋆ P) := by
  rw [sub_ok h]
  exact (FTotalTriple.ret (Q := fun r => ⟪r.toNat + b.toNat = a.toNat⟫ ⋆ P) (a - b)).pre
    fun _ hp => sep_lift.mpr ⟨sub_val h, hp⟩

/-- The payload of an optional that is not null (`.?`, `orelse unreachable`): some `v` with
`o = some v`. -/
@[fsym] theorem optPayload_step {α : Type} {o : Option α} (h : o.isSome = true) :
    FTotalTriple P (StateT.lift (optPayload o) : MemM α) (fun v => ⟪o = some v⟫ ⋆ P) := by
  obtain ⟨v, rfl⟩ := Option.isSome_iff_exists.mp h
  exact (FTotalTriple.ret (Q := fun r => ⟪some v = some r⟫ ⋆ P) v).pre fun _ hp => sep_lift.mpr ⟨rfl, hp⟩

/-! Tests of an optional as constructor equations (facts of `if o != null`, `orelse`), so a
`match o` of the precondition reduces (`destruct`, `substCtor`). -/

theorem opt_isSome_true {α : Type _} {o : Option α} (h : o.isSome = true) : ∃ a, o = some a :=
  Option.isSome_iff_exists.mp h

theorem opt_not_isSome {α : Type _} {o : Option α} (h : ¬o.isSome = true) : o = none :=
  Option.not_isSome_iff_eq_none.mp h

theorem opt_isSome_false {α : Type _} {o : Option α} (h : o.isSome = false) : o = none :=
  Option.not_isSome_iff_eq_none.mp (by simp [h])

theorem opt_isNone_true {α : Type _} {o : Option α} (h : o.isNone = true) : o = none :=
  Option.isNone_iff_eq_none.mp h

theorem opt_not_isNone {α : Type _} {o : Option α} (h : ¬o.isNone = true) : ∃ a, o = some a :=
  Option.isSome_iff_exists.mp (by cases o <;> simp_all)

theorem opt_isNone_false {α : Type _} {o : Option α} (h : o.isNone = false) : ∃ a, o = some a :=
  Option.isSome_iff_exists.mp (by cases o <;> simp_all)

/-- A slice's end check (`s[start..][0..len]`) within the source's length. -/
@[fsym] theorem checkSliceEnd_of {srcLen start len : BitVec 64} {extra : Nat}
    (h : start.toNat + len.toNat + extra ≤ srcLen.toNat) :
    FTotalTriple P (checkSliceEnd srcLen start len extra) (fun _ => P) := by
  unfold checkSliceEnd; rw [if_pos h]; exact FTotalTriple.ret (Q := fun _ => P) ()

/-- An item index (`s[i]`, `&s[i]`) within the operand's length. -/
@[fsym] theorem checkIndex_of {n : Nat} {len i : BitVec n} (h : i.toNat < len.toNat) :
    FTotalTriple P (checkIndex len i) (fun _ => P) := by
  unfold checkIndex; rw [if_pos h]; exact FTotalTriple.ret (Q := fun _ => P) ()

/-- A checked unsigned `%` by a nonzero divisor. -/
@[fsym] theorem rem_step {a b : BitVec w} (h : b ≠ 0) :
    FTotalTriple P (StateT.lift (Zig.rem false a b) : MemM (BitVec w))
      (fun r => ⟪r.toNat = a.toNat % b.toNat⟫ ⋆ P) := by
  have e : Zig.rem false a b = pure (a % b) := by
    simp only [Zig.rem, h, Bool.false_eq_true, ↓reduceIte]; rfl
  rw [e]; exact read_val BitVec.toNat_umod

/-- A checked unsigned `/` by a nonzero divisor. -/
@[fsym] theorem divTrunc_step {a b : BitVec w} (h : b ≠ 0) :
    FTotalTriple P (StateT.lift (Zig.divTrunc false a b) : MemM (BitVec w))
      (fun r => ⟪r.toNat = a.toNat / b.toNat⟫ ⋆ P) := by
  have e : Zig.divTrunc false a b = pure (a / b) := by
    simp only [Zig.divTrunc, h, Bool.false_eq_true, ↓reduceIte]; rfl
  rw [e]; exact read_val BitVec.toNat_udiv

/-- An `@intCast` (either signedness on either side) whose value fits in the target type. The
result is stated by its value (the arithmetic solver reads a signed one, `r.toInt`, from it). -/
@[fsym] theorem intCast_step {s₁ s₂ safe : Bool} {m : Nat} {a : BitVec w}
    (h : Zig.intLo s₂ m ≤ Zig.val s₁ a ∧ Zig.val s₁ a ≤ Zig.intHi s₂ m) :
    FTotalTriple P (StateT.lift (Zig.intCast s₁ s₂ m a safe) : MemM (BitVec m))
      (fun r : BitVec m => ⟪r.toNat = (BitVec.ofInt m (Zig.val s₁ a)).toNat⟫ ⋆ P) := by
  have e : Zig.intCast s₁ s₂ m a safe = pure (BitVec.ofInt m (Zig.val s₁ a)) := by
    simp only [Zig.intCast, h, and_self, ↓reduceIte]
  rw [e]; exact read_val rfl

end Arith

/-! ## Junk -/

-- The library's `Junk` (`Full/AllocSpec.lean`) stays opaque: `fsym` absorbs `up` parts into it.
attribute [fsym_atom] Junk

/-! ## Entailment combinators (the proofs `fsym` builds for returns) -/

section Imp

variable {P X Y A B A' B' : FAssn}

theorem imp_refl : ∀ r, P r → P r := fun _ h => h

theorem imp_sep (ha : ∀ r, A' r → A r) (hb : ∀ r, B' r → B r) : ∀ r, (A' ⋆ B') r → (A ⋆ B) r :=
  fun _ h => sep_mono ha hb h

theorem imp_ex {γ : Type} {F : γ → FAssn} (w : γ) (h : ∀ r, X r → F w r) : ∀ r, X r → FAssn.ex F r :=
  fun r hx => ⟨w, h r hx⟩

theorem imp_trans (h₁ : ∀ r, X r → Y r) (h₂ : ∀ r, Y r → P r) : ∀ r, X r → P r :=
  fun r h => h₂ r (h₁ r h)

theorem imp_eq (e : X = Y) : ∀ r, X r → Y r := fun _ h => e ▸ h

/-- An existential assertion of a resource (a hypothesis of a `WP` walk: a segment's post). -/
theorem ex_apply {γ : Type} {F : γ → FAssn} {r : Res} : FAssn.ex F r ↔ ∃ x, F x r := Iff.rfl

/-- A branch of an assertion-level `if`, with its condition as a fact. -/
theorem imp_ite_pos {c : Prop} [Decidable c] : ∀ r, (⟪c⟫ ⋆ X) r → (if c then X else Y) r :=
  fun _ h => by obtain ⟨hc, hx⟩ := sep_lift.mp h; rw [if_pos hc]; exact hx

theorem imp_ite_neg {c : Prop} [Decidable c] : ∀ r, (⟪¬c⟫ ⋆ Y) r → (if c then X else Y) r :=
  fun _ h => by obtain ⟨hc, hy⟩ := sep_lift.mp h; rw [if_neg hc]; exact hy

theorem imp_lift {φ : Prop} (hφ : φ) (h : ∀ r, X r → Y r) : ∀ r, X r → (⟪φ⟫ ⋆ Y) r :=
  fun r hx => sep_lift.mpr ⟨hφ, h r hx⟩

theorem imp_junk_emp : ∀ r, emp r → Junk r := fun _ h => junk_emp h

theorem imp_junk_up {Z : Assn} (h : ∀ r, X r → Junk r) : ∀ r, (up Z ⋆ X) r → Junk r :=
  fun _ hx => junk_absorb (sep_mono_right h hx)

theorem imp_junk_one {Z : Assn} : ∀ r, up Z r → Junk r :=
  fun _ hx => junk_absorb (sep_emp.mpr hx |> sep_mono_right fun _ h => junk_emp h)

theorem imp_junk_junk (h : ∀ r, X r → Junk r) : ∀ r, (Junk ⋆ X) r → Junk r := by
  intro r hx
  obtain ⟨r₁, r₂, hd, rfl, ⟨j1, h1⟩, h2⟩ := hx
  obtain ⟨j2, h2⟩ := h _ h2
  exact junk_absorb ⟨r₁, r₂, hd, rfl, h1, ⟨j2, h2⟩⟩

/-- A local update, reordered: the planner's step. -/
theorem eupd_frame_ac {R P' : FAssn} (h : EUpd X Y) (e1 : P = (X ⋆ R)) (e2 : (Y ⋆ R) = P') :
    EUpd P P' := e1 ▸ e2 ▸ h.frame

theorem eupd_ac {P' : FAssn} (h : EUpd X Y) (e1 : P = X) (e2 : Y = P') : EUpd P P' := e1 ▸ e2 ▸ h

end Imp

/-! ## Regions and shares (the planner's local steps) -/

section Plan

variable {p : Ptr} {A S : Nat} {K : BlockKind} {a a' : Nat} {bs bs' : Array Byte}

theorem up_region_split {k : Nat} (hk : k ≤ bs.size) (ha : (A + p.off.toNat + k) % a' = 0) :
    EUpd (up (regionIn p A S K a bs))
      (up (regionIn p A S K a (bs.extract 0 k)) ⋆ up (regionIn (p.add k) A S K a' (bs.extract k bs.size))) :=
  EUpd.of_imp fun _ h => Full.up_sep ⟨Region.regionIn_split h.1 hk ha, h.2⟩

theorem up_region_join :
    EUpd (up (regionIn p A S K a bs) ⋆ up (regionIn (p.add bs.size) A S K a' bs'))
      (up (regionIn p A S K a (bs ++ bs'))) :=
  EUpd.of_imp fun _ h => by
    have h' := Full.sep_up h
    exact ⟨Region.regionIn_join h'.1, h'.2⟩

theorem up_region_weaken (hd : a' ∣ a) :
    EUpd (up (regionIn p A S K a bs)) (up (regionIn p A S K a' bs)) :=
  EUpd.of_imp fun _ h => ⟨Region.regionIn_weaken h.1 hd, h.2⟩

/-- **A region as owned bytes** with its alignment and kind (`@[fsym_view]`: a rule about the
bytes, `Ops.lean`'s `…_bytesAt`). -/
@[fsym_view] theorem regionIn_view :
    EUpd (up (regionIn p A S K a bs))
      (⟪(A + p.off.toNat) % a = 0 ∧ K ≠ .constGlobal⟫ ⋆ up (bytesAt p A S K bs)) :=
  EUpd.of_imp fun _ h => sep_lift.mpr ⟨⟨h.1.1, h.1.2.1⟩, h.1.2.2, h.2⟩

/-- **Owned bytes as a region** again (`@[fsym_view]`: the view a postcondition names). -/
@[fsym_view] theorem regionIn_fold (ha : (A + p.off.toNat) % a = 0) (hK : K ≠ .constGlobal) :
    EUpd (up (bytesAt p A S K bs)) (up (regionIn p A S K a bs)) :=
  EUpd.of_imp fun _ h => ⟨⟨ha, hK, h.1⟩, h.2⟩

variable {b : BlockId} {q : Frac} {k k' : Nat} {t : STag}

theorem share_halves : EUpd (bshare b q k t) (bshare b q.half k t ⋆ bshare b q.half k t) :=
  EUpd.of_imp fun _ h => (bshare_split (Frac.half_pos h.1) (Frac.half_pos h.1)).mp
    (by rw [Frac.half_add_half]; exact h)

theorem share_weaken (h : k' ≤ k) : EUpd (bshare b q k t) (bshare b q k' t) := EUpd.weaken h

theorem share_join {q₂ : Frac} {k₂ : Nat} :
    EUpd (bshare b q k t ⋆ bshare b q₂ k₂ t) (bshare b (q.add q₂) (Max.max k k₂) t) := EUpd.join

/-- **Raise a share's bound** with another share of the block: both at the higher bound, the
fractions unchanged (join, then split back). A grant that grows in place takes its new bound
from the allocator's share of the block. -/
theorem share_raise {q₂ : Frac} {k₂ : Nat} :
    EUpd (bshare b q k t ⋆ bshare b q₂ k₂ t)
      (bshare b q (Max.max k k₂) t ⋆ bshare b q₂ (Max.max k k₂) t) := fun m r rF hh hp hs => by
  obtain ⟨r₁, r₂, -, -, h1, h2⟩ := id hp
  obtain ⟨r', hh', hp'⟩ := EUpd.join m r rF hh hp hs
  exact ⟨r', hh', (bshare_split h1.1 h2.1).mp hp'⟩

/-! The authority over a block's extent (`bauth`; `bext` is the fraction `Frac.one`): untagged
shares go back into it (`EUpd.unlend`) and come out of it (`EUpd.lend`); a share's bound rises up
to the block's size. -/

theorem auth_unlend {S : Nat} {K : BlockKind} {q₁ q₂ : Frac} :
    EUpd (bauth b S K q₁ ⋆ bshare b q₂ k) (bauth b S K (q₁.add q₂)) := EUpd.unlend

theorem auth_lend {S : Nat} {K : BlockKind} {q₁ q₂ : Frac} (hk : k ≤ S) (hq : 0 < q₂.val) :
    EUpd (bauth b S K (q₁.add q₂)) (bauth b S K q₁ ⋆ bshare b q₂ k) := EUpd.lend hk hq

/-- **Raise a share's bound** with the authority of its block: up to the block's size. -/
theorem auth_raise {S : Nat} {K : BlockKind} {q₁ q₂ : Frac} (hk : k' ≤ S) :
    EUpd (bauth b S K q₁ ⋆ bshare b q₂ k) (bauth b S K q₁ ⋆ bshare b q₂ k') := fun m r rF hh hp hs => by
  have hq : 0 < q₂.val := by obtain ⟨_, _, _, _, _, h2⟩ := hp; exact h2.1
  exact (EUpd.unlend.trans (EUpd.lend hk hq)) m r rF hh hp hs

/-- An authority whose fraction is known otherwise. -/
theorem auth_eq {S : Nat} {K : BlockKind} {q₁ q₂ : Frac} (h : q₁ = q₂) :
    bauth b S K q₁ = bauth b S K q₂ := h ▸ rfl

theorem one_half_pos : 0 < Frac.one.half.val := Frac.half_pos (by decide)

theorem frac_pos_of_eq {a c : Frac} (h : a = c) (ha : 0 < a.val) : 0 < c.val := h ▸ ha

/-- **Knowledge from ownership**, as an update: a nonempty region of block `b` whose cells have
the address `A` gives `known b A`. -/
theorem known_of_region {p : Ptr} {A S a : Nat} {K : BlockKind} {bs : Array Byte}
    (hpb : p.block = some b) (hpos : 0 < bs.size) :
    EUpd (up (regionIn p A S K a bs)) (up (regionIn p A S K a bs) ⋆ known b A) := by
  intro m r rF hh hp _
  obtain ⟨hr, hk, hg⟩ := id hp
  obtain ⟨-, -, b', hb', -, hl⟩ := id hr
  rw [hpb] at hb'; cases hb'
  have e := hl (b, p.off.toNat)
  rw [if_pos ⟨rfl, Nat.le_refl _, by omega⟩] at e
  simp only [FHeap.erase, Option.map_eq_some_iff] at e
  obtain ⟨fc, hfc, hfe⟩ := e
  have hkn : m.kn (.addr b A) := by
    obtain ⟨blk, hblk, -, -, -, ha, -⟩ := hh.block hfc
    exact ⟨blk, hblk, by rw [← ha, hfe]⟩
  exact ⟨⟨r.heap, r.know.union (Know.single (.addr b A)), r.gh⟩,
    ⟨hh.disj, hh.heap, hh.know.union (Know.sub_single hkn),
      hh.knowF, hh.ghost⟩,
    ⟨r, ⟨FHeap.empty, Know.single (.addr b A), Ghost.unit⟩, FHeap.disjoint_empty _,
      by rw [FHeap.union_empty, Ghost.add_unit], hp, rfl, rfl, rfl⟩⟩

/-- Knowledge can be forgotten. -/
@[fsym_drop] theorem known_drop {A : Nat} {R : FAssn} : EUpd (known b A ⋆ R) R := by
  rintro m _ rF hh ⟨r₁, r₂, -, rfl, ⟨e1, -, e3⟩, hp⟩ -
  obtain ⟨hd, hm, hkn, hkF, hg⟩ := hh
  simp only [e1, e3, FHeap.empty_union, Ghost.unit_add] at hd hm hg
  exact ⟨r₂, ⟨hd, hm, Know.Sub.right hkn, hkF, hg⟩, hp⟩

theorem ite_pos_eq {c : Prop} [Decidable c] (h : c) (X Y : FAssn) : (if c then X else Y) = X := if_pos h
theorem ite_neg_eq {c : Prop} [Decidable c] (h : ¬c) (X Y : FAssn) : (if c then X else Y) = Y := if_neg h

end Plan

theorem sep_emp_eq' (P : FAssn) : (P ⋆ emp) = P := funext fun _ => propext sep_emp
theorem emp_sep_eq' (P : FAssn) : (emp ⋆ P) = P := by rw [sep_comm_eq]; exact sep_emp_eq' P

theorem atom_eq {X Y : FAssn} (e : X = Y) : EUpd X Y := e ▸ EUpd.of_imp fun _ h => h

/-- A fact of the state of an update goes into the context. -/
theorem eupd_lift_pre {φ : Prop} {R Q : FAssn} (h : φ → EUpd R Q) : EUpd (⟪φ⟫ ⋆ R) Q :=
  fun m r rF hh hp hs => (h (sep_lift.mp hp).1) m r rF hh (sep_lift.mp hp).2 hs

/-- An existential of the state of an update is opened. -/
theorem eupd_ex_pre {β : Type} {F : β → FAssn} {R Q : FAssn} (h : ∀ x, EUpd (F x ⋆ R) Q) :
    EUpd (FAssn.ex F ⋆ R) Q := fun m r rF hh hp hs => by
  obtain ⟨x, hx⟩ := sep_ex.mp hp
  exact h x m r rF hh hx hs

theorem eupd_pre_eq {P P' Q : FAssn} (e : P = P') (h : EUpd P' Q) : EUpd P Q := e ▸ h

theorem ptr_ext' {p q : Ptr} (h1 : p.block = q.block) (h2 : p.off = q.off) : p = q := by
  cases p; cases q; simp_all

/-! ## Simp sets -/

theorem lift_bind {α β : Type} (x : Result α) (g : α → Result β) :
    (StateT.lift (x >>= g) : MemM β) = StateT.lift x >>= fun a => StateT.lift (g a) := by
  funext m
  show ((x >>= g) >>= fun a => pure (a, m)) =
    ((x >>= fun a => pure (a, m)) >>= fun p => (g p.1 >>= fun a => pure (a, p.2)))
  simp only [bind_assoc, pure_bind]

theorem lift_ite {α : Type} {c : Prop} [Decidable c] (x y : Result α) :
    (StateT.lift (if c then x else y) : MemM α) = if c then StateT.lift x else StateT.lift y := by
  split <;> rfl

theorem lift_optPayload_some {α : Type} (a : α) :
    (StateT.lift (optPayload (some a)) : MemM α) = pure a := rfl

theorem run_ite' {σ α : Type} {m : Type → Type} [Monad m] {c : Prop} [Decidable c]
    (x y : StateT σ m α) (s : σ) : (if c then x else y).run s = if c then x.run s else y.run s := by
  split <;> rfl

theorem run_throw' {σ α : Type} (e : Error) (s : σ) : (throw e : StateT σ Result α).run s = throw e := rfl

theorem result_throw_bind {α β : Type} (e : Error) (f : α → Result β) : (throw e : Result α) >>= f = throw e :=
  rfl

attribute [fsym_norm] run_ite' run_throw' result_throw_bind lift_bind lift_ite lift_optPayload_some Option.elim_none Option.elim_some
  Zig.call StateT.run_monadLift StateT.run_lift liftM monadLift MonadLift.monadLift StateT.run_get StateT.run_modify

/-- A store of `undefined` is the store of its undefined bytes (the byte rules execute it). -/
theorem storeUndef_eq {α : Type} [Enc α] (a : Nat) (p : Ptr) :
    Zig.storeUndef α a p = Zig.storeBytes p a (Array.replicate (Enc.size α) .undef) := rfl

attribute [fsym_norm] storeUndef_eq

/-- The payload and the error of an error union whose tag is known. -/
theorem unwrapPayload_ok {α : Type} (v : α) : Zig.unwrapPayload (.ok v : Except ErrName α) = pure v := rfl
theorem unwrapErr_error {α : Type} (e : ErrName) : Zig.unwrapErr (.error e : Except ErrName α) = pure e := rfl

attribute [fsym_norm] StateT.run'_eq StateT.run_bind StateT.run_pure Norm.run_callM Norm.run_callR
  Norm.run_liftM Norm.run_liftR Norm.run_ite Norm.ite_bind Norm.run_throw Norm.throw_bind
  Norm.lift_pure Norm.lift_throw Norm.sub_zero Norm.elem_zero Norm.run_get Norm.run_modify
  Norm.add_zero_ptr bind_assoc pure_bind map_pure bind_map_left map_bind Norm.beq_true_iff
  bind_pure_unit Zig.isNonErr Zig.isErr Bool.not_false Bool.not_true Bool.false_eq_true
  Norm.isSome_ite Norm.elim_bind unwrapPayload_ok unwrapErr_error

theorem add_lit {n : Nat} {a b : BitVec n} {safe : Bool} (h : decide (a.toNat + b.toNat < 2 ^ n) = true) :
    Zig.add false a b safe = pure (a + b) :=
  add_ok (of_decide_eq_true h)
theorem sub_lit {n : Nat} {a b : BitVec n} {safe : Bool} (h : decide (b.toNat ≤ a.toNat) = true) :
    Zig.sub false a b safe = pure (a - b) :=
  sub_ok (of_decide_eq_true h)
theorem mul_lit {n : Nat} {a b : BitVec n} {safe : Bool} (h : decide (a.toNat * b.toNat < 2 ^ n) = true) :
    Zig.mul false a b safe = pure (a * b) := by
  simp only [Zig.mul, BitVec.umulOverflow, Bool.false_eq_true, ↓reduceIte]
  rw [if_neg (by simp at h ⊢; omega)]

open Lean Meta Simp in
/-- Unsigned `+ - *` of two word literals that does not overflow: its value (`pure (a - b)`,
then evaluated by Lean's `BitVec` simprocs). Generated code computes constants such as
`alignment - 1` at run time. The side condition is decided on the literals. Either form (`safe`,
the last argument) reduces. -/
def reduceLitArithCore (op lem : Name) : Simproc := fun e => do
  unless e.isAppOfArity op 5 do return .continue
  let args := e.getAppArgs
  unless args[1]!.isConstOf ``Bool.false do return .continue
  let some ⟨w, a⟩ ← getBitVecValue? args[2]! | return .continue
  let some ⟨_, b⟩ ← getBitVecValue? args[3]! | return .continue
  let ok := if op == ``Zig.add then a.toNat + b.toNat < 2 ^ w
    else if op == ``Zig.sub then b.toNat ≤ a.toNat
    else a.toNat * b.toNat < 2 ^ w
  unless ok do return .continue
  let f ← mkAppOptM lem #[none, args[2]!, args[3]!, args[4]!]
  let hTy := (← whnfR (← inferType f)).bindingDomain!
  let pf := mkApp f (← mkExpectedTypeHint (← mkEqRefl (mkConst ``Bool.true)) hTy)
  let rhs := (← inferType pf).appArg!
  return .visit { expr := rhs, proof? := some pf }

simproc [fsym_norm] reduceLitAdd (Zig.add false _ _ _) := reduceLitArithCore ``Zig.add ``add_lit
simproc [fsym_norm] reduceLitSub (Zig.sub false _ _ _) := reduceLitArithCore ``Zig.sub ``sub_lit
simproc [fsym_norm] reduceLitMul (Zig.mul false _ _ _) := reduceLitArithCore ``Zig.mul ``mul_lit

open Lean Meta Simp in
/-- A field accessor of generated code applied to a structure value (`mem_Alignment.toBits ⟨x⟩`
is `x`): a user definition whose body is a projection of one of its parameters. -/
dsimproc [fsym_norm, fsym_arith] reduceAccessor (_) := fun e => do
  let .const c _ := e.getAppFn | return .continue
  if e.getAppNumArgs == 0 then return .continue
  let env ← getEnv
  if isLibraryConst env c then return .continue
  let some (.defnInfo info) := env.find? c | return .continue
  let isAccessor ← lambdaTelescope info.value fun xs body => do
    let body := body.consumeMData
    if xs.size != e.getAppNumArgs then return false
    match body with
    | .proj _ _ s => return s.isFVar && xs.contains s
    | _ =>
      let .const f _ := body.getAppFn | return false
      let some pi ← getProjectionFnInfo? f | return false
      let some s := body.getAppArgs[pi.numParams]? | return false
      return body.getAppNumArgs == pi.numParams + 1 && s.isFVar && xs.contains s
  unless isAccessor do return .continue
  let some e' ← withTransparency .default (unfoldDefinition? e) | return .continue
  let e' ← withTransparency .default (whnfCore e'.headBeta)
  if e' != e && (e.find? (· == e')).isSome then return .done e'
  return .continue

open Lean Meta Simp in
/-- **A field of a structure value that a user definition builds** (`(B A1 A0).cap` of
`def B … : FBuf := ⟨bufp, 16, …⟩`): the field's value, when the definition evaluates (`whnf`) to
the structure's constructor (ledger #48: `bnd (B A1 A0)` in an entailment's bounds). -/
dsimproc [fsym_norm, fsym_arith] reduceUserProj (_) := fun e => do
  let .const c _ := e.getAppFn | return .continue
  let some info ← getProjectionFnInfo? c | return .continue
  if info.fromClass then return .continue
  let some s := e.getAppArgs[info.numParams]? | return .continue
  let .const d _ := s.getAppFn | return .continue
  let env ← getEnv
  if isLibraryConst env d then return .continue
  let some (.defnInfo _) := env.find? d | return .continue
  let v ← whnfDCached s
  let .const vc _ := v.getAppFn | return .continue
  let some (.ctorInfo ci) := env.find? vc | return .continue
  let some f := v.getAppArgs[ci.numParams + info.i]? | return .continue
  return .visit (mkAppN f (e.getAppArgs.extract (info.numParams + 1) e.getAppNumArgs))

open Lean Meta Simp in
/-- **A generated function evaluated to a constructor** (ledger #37, #40): an application of a
user definition whose value is a constructor of an inductive type that is not a structure (an
enumeration, a union's tag, a loop's `again` test of an exit: `ResetMode.tag .free_all` is
`.free_all`, `again19 .rep19` is `true`). The definition is evaluated (`whnf`) and the result is
kept only if it is a constructor application, so a `match` on it reduces (in a program, in an
assertion's `if`). Definitional: no proof. -/
dsimproc [fsym_norm, fsym_arith] evalUserCtor (_) := fun e => do
  let .const c _ := e.getAppFn | return .continue
  if e.getAppNumArgs == 0 || e.hasLooseBVars then return .continue
  let env ← getEnv
  if isLibraryConst env c then return .continue
  let some (.defnInfo _) := env.find? c | return .continue
  if (← getProjectionFnInfo? c).isSome || isMatcherCore env c || isAuxRecursor env c then return .continue
  if (← isInstance c) then return .continue
  -- the result's type, as stated: an inductive type with several constructors, not a number
  -- (arithmetic, `unfoldUserValue`), not a structure (a record's fields stay folded) and not a
  -- definition over one (`Zig.Result`: a program's value stays `pure v`)
  let ty ← instantiateMVars (← inferType e)
  let .const tn _ := ty.getAppFn | return .continue
  if tn == ``Nat || tn == ``Int then return .continue
  let some (.inductInfo ii) := env.find? tn | return .continue
  if ii.ctors.length < 2 || isStructure env tn then return .continue
  if ← isProp ty then return .continue
  let v ← whnfDCached e
  let .const vc _ := v.getAppFn | return .continue
  let some (.ctorInfo _) := env.find? vc | return .continue
  return .done v

/-! ## Facts about byte arrays (`keepsPrefix` of `resizePost`/`remapPost`) -/

theorem kp_refl (bs : Array Byte) : keepsPrefix bs bs := rfl

theorem kp_extract (bs : Array Byte) (n : Nat) : keepsPrefix bs (bs.extract 0 n) := by
  unfold keepsPrefix; simp only [Array.extract_extract, Nat.zero_add, Array.size_extract]
  congr 1; omega

theorem kp_append (bs t : Array Byte) : keepsPrefix bs (bs ++ t) := by
  unfold keepsPrefix
  rw [Array.extract_append_left]
  simp only [Array.size_append, Array.extract_size]
  exact (Array.extract_eq_self_of_le (by omega)).symm

theorem kp_extract_append (bs t : Array Byte) (n : Nat) : keepsPrefix bs ((bs ++ t).extract 0 n) := by
  unfold keepsPrefix
  apply Array.ext
  · simp only [Array.size_extract, Array.size_append]; omega
  · intro i h1 h2
    simp only [Array.size_extract, Array.size_append] at h1 h2
    simp only [Array.getElem_extract, Nat.zero_add]
    rw [Array.getElem_append_left (by omega)]

theorem kp_extract_append_append (bs t u : Array Byte) (n : Nat) :
    keepsPrefix bs ((bs ++ t ++ u).extract 0 n) := by
  rw [Array.append_assoc]; exact kp_extract_append bs (t ++ u) n

/-- A prefix of a prefix of `bs ++ t` keeps `bs`'s prefix. -/
theorem kp_extract_extract_append (bs t : Array Byte) (m n : Nat) :
    keepsPrefix bs (((bs ++ t).extract 0 m).extract 0 n) := by
  rw [Array.extract_extract]; simp only [Nat.zero_add]
  exact kp_extract_append bs t (Nat.min n m)

end Zig.Full.Auto

/-- Library facts that are not arithmetic; extend with `macro_rules`. -/
syntax "fsym_fact" : tactic
macro_rules
  | `(tactic| fsym_fact) => `(tactic| first
      | with_reducible exact Zig.Full.Auto.kp_refl _
      | with_reducible exact Zig.Full.Auto.kp_extract _ _
      | with_reducible exact Zig.Full.Auto.kp_append _ _
      | with_reducible exact Zig.Full.Auto.kp_extract_append _ _ _
      | with_reducible exact Zig.Full.Auto.kp_extract_extract_append _ _ _ _
      | with_reducible exact Zig.Full.Auto.kp_extract_append_append _ _ _ _
      | with_reducible exact Zig.Full.Frac.half_add_half _
      | with_reducible exact Zig.Full.Auto.one_half_pos
      | with_reducible assumption
      | (apply Eq.symm; with_reducible assumption))
