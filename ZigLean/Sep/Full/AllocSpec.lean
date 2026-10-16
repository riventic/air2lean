import ZigLean.Sep.Full.Logic
import ZigLean.Sep.Full.Extent
import ZigLean.Sep.Full.Claims
import ZigLean.Sep.AllocSpec.Region
import ZigLean.Sep.Base.Alloc

/-!
# The allocator specification over full-state resources (migration stage 2)

`FAllocSpec L vt ctx I` is `AllocSpec` (`ZigLean/Sep/AllocSpec.lean`, `docs/alloc-spec.md`) with
full-state assertions (`ZigLean/Sep/Full/Res.lean`) and a full-state logic (`FLogic`): the same
four vtable entries, the same pre- and postconditions, and the same side conditions. Only the
assertion language changes. `I.own` and `I.tok` are `FAssn`s, so an allocator invariant can own
the atomic layout of its words (`apts`) and keep persistent knowledge of the blocks it handed out
(`known`). The page allocator needs both (`docs/alloc-page.md`, O1 and O3). Regions stay legacy
assertions under `up`, so the region library carries over.

**The extent share of a grant** (`docs/sep-full-state.md` §Block extents). A grant of `n` bytes at
`p` also carries a share `pshare p q (p.off + n)` of the extent of `p`'s block: while the client
holds the grant, the block is live with at least `p.off + n` bytes, whatever happens to the
block's other parts. A client uses it for pointers up to the end of the grant that it does not
own bytes to; an allocator that grants out of a block of its own (a fixed buffer, an arena node, a
mapping) lends it off its own claim on that block (`EUpd.lend`, `EUpd.weaken`) and takes it back
in `free` and `resize` (`EUpd.unlend`, `EUpd.join`). An allocator that revokes its grants (an
arena's `reset`) hands out shares tagged with its ledger's epoch (`FAllocInv.tag`, `EUpd.lendT`).
The token sees the fraction `q`
(`FAllocInv.tok`'s last argument), so an allocator that must get its whole extent back (the page
allocator's `munmap`) knows that `free` returns exactly what it lent.

**The fee of a grant** (`docs/sep-full-state.md` §The fee of a grant). `alloc` takes a fee
`I.fee φ` next to `own`, for a fraction `φ` the client picks; the token records `φ`
(`FAllocInv.tok`'s last argument), and `free` gives `I.fee φ` back, as does a failed `alloc`.
The default fee is `emp`: for an allocator that charges none (the page allocator) the contract is
the one without a fee. The fee is for an allocator that revokes its grants: an arena or a fixed
buffer charges a fraction of its epoch token, so that the client's whole epoch token, which
`reset` takes, shows that no grant is outstanding (`epFee`, `ResetLedger` in
`ZigLean/Sep/Full/ResetLedger.lean`; the arena of `tests/roadmap/alloc-arena` and the
`FixedBufferAllocator` of `tests/roadmap/alloc-fba` are instances).

A legacy specification does not lift wholesale (§No embedding of the legacy logic below): the
cells of an `up` assertion no longer pin their block's size.
-/

namespace Zig
namespace Full

open FAssn

/-- A share `q` of the extent of `p`'s block, at the lower bound `k`, with the epoch tag `t`. -/
def pshare (p : Ptr) (q : Frac) (k : Nat) (t : Option (Nat × Nat) := none) : FAssn :=
  FAssn.ex fun b => ⟪p.block = some b⟫ ⋆ bshare b q k t

/-- An allocator invariant over full-state assertions (`AllocInv`). The token
`tok p n k A S K q φ` of a grant of `n` bytes at `p` with alignment `2 ^ k` in a block with
address `A`, size `S` and kind `K` (as the region's cells record them) sees the fraction `q` of
the grant's extent share (`granted`) and the fraction `φ` of the fee paid for it. `fee φ` is
what `alloc` takes for a grant and `free` gives back (`emp` by default: no fee); the token
records `φ` so that the allocator refunds exactly what it was paid. `tag` is the epoch tag of
the grant's share
(`docs/sep-full-state.md` §Epoch-tagged shares): `none` for an allocator that never revokes its
grants, `some (γ, e)` for one whose grants die with epoch `e` of its ledger `γ` (an arena).

`act` is the allocator's obligation that **its state witnesses the tag of its shares as active**
(§Nested tags): whoever holds `own` holds the ledgers of the tag's whole chain. It is automatic
for an untagged allocator (`Act.root`). An allocator that holds another one's grants (an arena's
nodes) reads the bound of their shares from it (`Holds.bshare`), so the obligation composes: an
arena over a child proves `act` from its own ledger and the child's `act`.

`fee_add` is the allocator's obligation that **its fees are fractional**: two nonzero fees are
the fee of their sum (coordinator decision 2026-10-13). An allocator of allocators (an arena)
pays its child's fee for each node out of a reservoir it keeps (all of it, or half of it with
`FAllocInv.fee_half`) and joins refunds back into it (`fee_join`). It is automatic for the default fee
`emp`. -/
structure FAllocInv where
  own : FAssn
  tok : Ptr → Nat → Nat → Nat → Nat → BlockKind → Frac → Frac → FAssn
  fee : Frac → FAssn := fun _ => FAssn.emp
  fits : Nat → Nat → Prop := fun _ _ => True
  tag : Option (Nat × Nat) := none
  act : ∀ r, own r → Act r.gh.ls tag := by intro _ _; exact Act.root
  fee_add : ∀ a b : Frac, 0 < a.val → 0 < b.val → fee (a.add b) = (fee a ⋆ fee b) := by
    intro _ _ _ _; funext _; exact propext Zig.Full.sep_emp.symm
  freed : Ptr → FAssn := fun _ => FAssn.emp
  freed_pers : ∀ p r, freed p r → r.heap = FHeap.empty ∧ r.gh = Ghost.unit := by
    intro _ _ h; exact ⟨h.1, h.2.2⟩

namespace FAllocInv

/-- **What `free` tells about the freed pointer** (`freed`, knowledge only: `freed_pers`).
`emp` by default; an allocator whose `free` ends the grant's block says so (the page allocator:
the block is dead, `dead`, `docs/sep-full-state.md` §Why knowledge). A client of the contract
alone learns nothing from it and forgets it (`freed_drop`, `FAllocSpec.free'`,
`CAllocSpec.free'`); a client that knows the allocator reads it. -/
theorem freed_drop (I : FAllocInv) (p : Ptr) {P : FAssn} : EUpd (P ⋆ I.freed p) P := by
  rintro m _ rF hh ⟨r₁, r₂, -, rfl, hp, hr⟩ -
  obtain ⟨e1, e3⟩ := I.freed_pers p r₂ hr
  obtain ⟨hd, hm, hkn, hkF, hg⟩ := hh
  simp only [e1, e3, FHeap.union_empty, Ghost.add_unit] at hd hm hg
  exact ⟨r₁, ⟨hd, hm, Know.Sub.left hkn, hkF, hg⟩, hp⟩

/-- **Halve a fee** (`fee_add`): an allocator of allocators keeps a reservoir of its child's fee
and pays a node's fee out of it. -/
theorem fee_half (I : FAllocInv) {φ : Frac} (h : 0 < φ.val) :
    I.fee φ = (I.fee φ.half ⋆ I.fee φ.half) := by
  rw [← I.fee_add _ _ (Frac.half_pos h) (Frac.half_pos h), Frac.half_add_half]

/-- **Join a refund back** into a reservoir (`fee_add`): the result is again a nonzero fee. -/
theorem fee_join (I : FAllocInv) {φ ψ : Frac} (hφ : 0 < φ.val) (hψ : 0 < ψ.val) {r : Res}
    (h : (I.fee φ ⋆ I.fee ψ) r) : I.fee (φ.add ψ) r ∧ 0 < (φ.add ψ).val := by
  rw [I.fee_add _ _ hφ hψ]
  exact ⟨h, by simp only [Frac.add]; grind⟩

/-- **`I` takes every request up to `n` bytes** at alignment `2 ^ k` (`fits`): a property of a
child allocator that an allocator of allocators asks for (the arena's `reset` reallocates a node
of any size up to the sum of its lists' sizes, at most `2 ^ 63` bytes; `docs/alloc-arena.md`).
It is a hypothesis on the child parameter, not an environment premise: the page allocator has it
for every `n` with `n + 2 ^ k + P ≤ 2 ^ 64` (`PageTok.pinv_fitsUpTo`), a fixed buffer for every
`n` with `cap + 2 ^ k + n ≤ 2 ^ 64` (`AllocFba.FBA.finv_fitsUpTo`). -/
def FitsUpTo (I : FAllocInv) (n k : Nat) : Prop := ∀ m, m ≤ n → I.fits m k

theorem FitsUpTo.fits {I : FAllocInv} {n k m : Nat} (h : I.FitsUpTo n k) (hm : m ≤ n) :
    I.fits m k :=
  h m hm

variable (I : FAllocInv)

/-- A region that `I`'s allocator granted for the fee `φ` (`Zig.granted`): its bytes, the token,
and a share of its block's extent up to the region's end. -/
def granted (p : Ptr) (k : Nat) (φ : Frac) (bs : Array Byte) : FAssn :=
  FAssn.ex fun A => FAssn.ex fun S => FAssn.ex fun K => FAssn.ex fun q =>
    up (regionIn p A S K (2 ^ k) bs) ⋆ (I.tok p bs.size k A S K q φ ⋆
      (pshare p q (p.off.toNat + bs.size) I.tag ⋆ pclaim p p.off.toNat (p.off.toNat + bs.size) I.tag))

/-- After `alloc` of `len` bytes for the fee `φ` (`Zig.allocPost`): a failure gives the fee back. -/
def allocPost (len k : Nat) (φ : Frac) : Option Ptr → FAssn
  | none => I.own ⋆ I.fee φ
  | some p => I.own ⋆ FAssn.ex fun bs => ⟪bs.size = len⟫ ⋆ I.granted p k φ bs

/-- After `resize` of the region `bs` at `p` to `n` bytes (`Zig.resizePost`). -/
def resizePost (p : Ptr) (k : Nat) (φ : Frac) (bs : Array Byte) (n : Nat) : Bool → FAssn
  | true => I.own ⋆ FAssn.ex fun bs' => ⟪bs'.size = n ∧ keepsPrefix bs bs'⟫ ⋆ I.granted p k φ bs'
  | false => I.own ⋆ I.granted p k φ bs

/-- What `resize` needs of a grant of `len` bytes besides its bytes: the token and a share `q'`
of the grant's extent share at the grant's end (any part of it: the holder may have lent the rest
on, as an arena does with its nodes). The grant's claim follows its bytes: the client keeps the
claim on the bytes it keeps (`relBytes`, `newBytes`). -/
def held (p : Ptr) (len k A S : Nat) (K : BlockKind) (q q' φ : Frac) : FAssn :=
  I.tok p len k A S K q φ ⋆ pshare p q' (p.off.toNat + len) I.tag

/-- The bytes `tl` that a shrink of a grant of `len` bytes at `p` to `n` bytes releases: the
bytes `[n, len)`, with the cell labels `A S K`, and the claim on them; nothing for a growth. -/
def relBytes (p : Ptr) (A S : Nat) (K : BlockKind) (n len : Nat) (tl : Array Byte) : FAssn :=
  if n < len then ⟪tl.size = len - n⟫ ⋆
    (up (regionIn (p.add n) A S K 1 tl) ⋆ pclaim p (p.off.toNat + n) (p.off.toNat + len) I.tag)
  else emp

/-- The bytes `[len, n)` that a growth of a grant at `p` from `len` to `n` bytes adds, any values,
with the cell labels `A S K`, and the claim on them; nothing for a shrink. -/
def newBytes (p : Ptr) (A S : Nat) (K : BlockKind) (len n : Nat) : FAssn :=
  if len < n then FAssn.ex fun t : Array Byte => ⟪t.size = n - len⟫ ⋆
    (up (regionIn (p.add len) A S K 1 t) ⋆ pclaim p (p.off.toNat + len) (p.off.toNat + n) I.tag)
  else emp

/-- **The refined `resize`** (`docs/sep-full-state.md` §`FAllocSpec` refined): from a grant of
`len` bytes to `n` bytes. On success the token is at `n` (same address; the size and kind labels
may change within the kind's normal form), the share is at the new end, and a growth hands over
the new bytes `[len, n)`. On failure the precondition comes back: the token, the share and the
released bytes `tl` of a shrink. -/
def rresizePost (p : Ptr) (k len n A S : Nat) (K : BlockKind) (q q' φ : Frac) (tl : Array Byte) :
    Bool → FAssn
  | true => I.own ⋆ FAssn.ex fun S' : Nat => FAssn.ex fun K' : BlockKind => ⟪K'.norm = K.norm⟫ ⋆
      (I.held p n k A S' K' q q' φ ⋆ I.newBytes p A S' K' len n)
  | false => I.own ⋆ (I.held p len k A S K q q' φ ⋆ I.relBytes p A S K n len tl)

/-- After `remap` of the region `bs` at `p` to `n` bytes (`Zig.remapPost`). -/
def remapPost (p : Ptr) (k : Nat) (φ : Frac) (bs : Array Byte) (n : Nat) : Option Ptr → FAssn
  | none => I.own ⋆ I.granted p k φ bs
  | some q => I.own ⋆ FAssn.ex fun bs' => ⟪bs'.size = n ∧ keepsPrefix bs bs'⟫ ⋆ I.granted q k φ bs'

/-- `act` of a resource that holds `own` among its parts. -/
theorem act_within {P : FAssn} {r : Res} (hw : Within I.own P) (hp : P r) : Act r.gh.ls I.tag := by
  obtain ⟨R, r₁, r₂, -, rfl, h1, -⟩ := hw r hp
  exact (I.act r₁ h1).mono (Ghost.ls_add _ _)

end FAllocInv

/-- The resources an allocator's creation must establish: its state and an available, positive
fee, together with a nonempty accepted request domain. Requiring the fee and a request as well
as `own` excludes an invariant whose operations are vacuous because the fee or `fits` is
impossible (soundness audit F2). A creation obligation
is an ordinary `FTotalTriple P c (fun _ => … creationPost …)` with the existing `FAdmit P`
companion; this assertion introduces no program judgment. The post may existentially bind the
instance's fresh ghost parameters, including a ledger allocated by creation; visible program
parameters remain fixed at the actual application. -/
def FAllocInv.creationPost (I : FAllocInv) : FAssn :=
  FAssn.ex fun φ : Frac =>
    ⟪0 < φ.val ∧ ∃ len : BitVec 64, ∃ k, 0 < len.toNat ∧ k < 64 ∧ I.fits len.toNat k⟫ ⋆
      (I.own ⋆ I.fee φ)

/-- Hand-stated specification data for the contract theorem's binder positions. Creation keeps
every visible instance parameter fixed and may choose fresh ghost parameters existentially.
The two lists must partition the telescope; the assurance extractor checks this and compares
the existing creation triple's post. This records no program judgment or proof rule. -/
structure FAllocCreationParameters where
  visible : List Nat
  fresh : List Nat

/-- Any available positive fee and accepted positive request establish the generic creation
post. A contract need not make the whole fee available if its own state retains a fraction. -/
theorem FAllocInv.creationPost_intro (I : FAllocInv) (φ : Frac) (hφ : 0 < φ.val)
    (hf : ∃ len : BitVec 64, ∃ k, 0 < len.toNat ∧ k < 64 ∧ I.fits len.toNat k) :
    EUpd (I.own ⋆ I.fee φ) I.creationPost :=
  EUpd.of_imp fun _ h => ⟨φ, sep_lift.mpr ⟨⟨hφ, hf⟩, h⟩⟩

/-- `AllocSpec` over full-state assertions: the allocator `vt` with context `ctx` satisfies the
`std.mem.Allocator` contract in the logic `L`, with invariant `I`. -/
structure FAllocSpec (L : FLogic) (vt : RawVTable) (ctx : Ptr) (I : FAllocInv) : Prop where
  /-- `alloc` for the fee `φ` (`FAllocInv.fee`): a grant whose token records `φ`, or the fee back. -/
  alloc : ∀ (len : BitVec 64) (k : Nat) (ra : BitVec 64) (φ : Frac), 0 < len.toNat → k < 64 →
    I.fits len.toNat k → L.T (I.own ⋆ I.fee φ) (vt.alloc ctx len k ra) (I.allocPost len.toNat k φ)
  /-- The refined `resize` (`FAllocInv.rresizePost`): the token, a part `q' ≤ q` of the grant's
  extent share and only the released bytes; the client keeps the bytes it keeps. A growth takes
  any part of the share (every other part stays true when the block grows); a shrink takes the
  whole share `q' = q` (an allocator may shrink the block itself, `munmap` of a tail: no other
  share may then claim the old end). The whole-region form is the corollary
  `FAllocSpec.resize_granted`. -/
  resize : ∀ (s : Slice) (k : Nat) (n ra : BitVec 64) (A S : Nat) (K : BlockKind) (q q' φ : Frac)
    (tl : Array Byte), k < 64 → 0 < n.toNat → I.fits n.toNat k → 0 < s.len.toNat →
    q'.val ≤ q.val → (n.toNat < s.len.toNat → q' = q) →
    L.T (I.own ⋆ (I.held s.ptr s.len.toNat k A S K q q' φ ⋆
      I.relBytes s.ptr A S K n.toNat s.len.toNat tl))
      (vt.resize ctx s k n ra) (I.rresizePost s.ptr k s.len.toNat n.toNat A S K q q' φ tl)
  remap : ∀ (s : Slice) (k : Nat) (n ra : BitVec 64) (φ : Frac) (bs : Array Byte), k < 64 →
    0 < n.toNat → I.fits n.toNat k → s.len.toNat = bs.size → 0 < bs.size →
    L.T (I.own ⋆ I.granted s.ptr k φ bs) (vt.remap ctx s k n ra) (I.remapPost s.ptr k φ bs n.toNat)
  /-- `free` gives the grant's fee back, and what the allocator tells about the freed pointer
  (`FAllocInv.freed`, `emp` by default). -/
  free : ∀ (s : Slice) (k : Nat) (ra : BitVec 64) (φ : Frac) (bs : Array Byte), k < 64 →
    s.len.toNat = bs.size → 0 < bs.size →
    L.T (I.own ⋆ I.granted s.ptr k φ bs) (vt.free ctx s k ra)
      (fun _ => (I.own ⋆ I.fee φ) ⋆ I.freed s.ptr)

/-- `free` for a client of the contract alone: the fee back (`FAllocInv.freed_drop`). -/
theorem FAllocSpec.free' {L : FLogic} {vt : RawVTable} {ctx : Ptr} {I : FAllocInv}
    (h : FAllocSpec L vt ctx I) (s : Slice) (k : Nat) (ra : BitVec 64) (φ : Frac) (bs : Array Byte)
    (h1 : k < 64) (h2 : s.len.toNat = bs.size) (h3 : 0 < bs.size) :
    L.T (I.own ⋆ I.granted s.ptr k φ bs) (vt.free ctx s k ra) (fun _ => I.own ⋆ I.fee φ) :=
  L.eupdPost (h.free s k ra φ bs h1 h2 h3) fun _ => I.freed_drop s.ptr

/-- An allocator whose `free` tells nothing (`freed` is `emp`) gives `free`'s field from the fee
alone. -/
theorem FAllocInv.free_of_emp {L : FLogic} {I : FAllocInv} (he : ∀ p, I.freed p = FAssn.emp)
    {P : FAssn} {c : MemM Unit} {p : Ptr} {φ : Frac} (h : L.T P c (fun _ => I.own ⋆ I.fee φ)) :
    L.T P c (fun _ => (I.own ⋆ I.fee φ) ⋆ I.freed p) :=
  L.conseq h (fun _ x => x) fun _ _ x => by rw [he]; exact Zig.Full.sep_emp.mpr x

/-- A total allocator is a partial one. -/
theorem FAllocSpec.toPartial {L : FLogic} {vt : RawVTable} {ctx : Ptr} {I : FAllocInv}
    (h : FAllocSpec L vt ctx I) : FAllocSpec FLogic.partial vt ctx I where
  alloc len k ra φ h1 h2 h3 := L.toPartial (h.alloc len k ra φ h1 h2 h3)
  resize s k n ra A S K q q' φ tl h1 h2 h3 h4 h5 h6 :=
    L.toPartial (h.resize s k n ra A S K q q' φ tl h1 h2 h3 h4 h5 h6)
  remap s k n ra φ bs h1 h2 h3 h4 h5 := L.toPartial (h.remap s k n ra φ bs h1 h2 h3 h4 h5)
  free s k ra φ bs h1 h2 h3 := L.toPartial (h.free s k ra φ bs h1 h2 h3)

/-- The spec only depends on the runs of the entries from full-state sequential memories. -/
theorem FAllocSpec.congr {L : FLogic} {vt vt' : RawVTable} {ctx : Ptr} {I : FAllocInv}
    (h : FAllocSpec L vt ctx I)
    (ha : ∀ len k ra m, m.FSeq → (vt'.alloc ctx len k ra).run m = (vt.alloc ctx len k ra).run m)
    (hr : ∀ s k n ra m, m.FSeq → (vt'.resize ctx s k n ra).run m = (vt.resize ctx s k n ra).run m)
    (hm : ∀ s k n ra m, m.FSeq → (vt'.remap ctx s k n ra).run m = (vt.remap ctx s k n ra).run m)
    (hf : ∀ s k ra m, m.FSeq → (vt'.free ctx s k ra).run m = (vt.free ctx s k ra).run m) :
    FAllocSpec L vt' ctx I where
  alloc len k ra φ h1 h2 h3 := L.congr (ha len k ra) (h.alloc len k ra φ h1 h2 h3)
  resize s k n ra A S K q q' φ tl h1 h2 h3 h4 h5 h6 :=
    L.congr (hr s k n ra) (h.resize s k n ra A S K q q' φ tl h1 h2 h3 h4 h5 h6)
  remap s k n ra φ bs h1 h2 h3 h4 h5 :=
    L.congr (hm s k n ra) (h.remap s k n ra φ bs h1 h2 h3 h4 h5)
  free s k ra φ bs h1 h2 h3 := L.congr (hf s k ra) (h.free s k ra φ bs h1 h2 h3)

/-- The four entries keep the atomic layout and every block's address. -/
structure VTame (vt : RawVTable) (ctx : Ptr) : Prop where
  alloc : ∀ len k ra, Tame (vt.alloc ctx len k ra)
  resize : ∀ s k n ra, Tame (vt.resize ctx s k n ra)
  remap : ∀ s k n ra, Tame (vt.remap ctx s k n ra)
  free : ∀ s k ra, Tame (vt.free ctx s k ra)

/-! ## Building blocks of allocator invariants -/

/-- `pshare` of a pointer into block `b` is `b`'s share. -/
theorem pshare_iff {p : Ptr} {b : BlockId} {q : Frac} {k : Nat} {t : STag} {r : Res}
    (hb : p.block = some b) : pshare p q k t r ↔ bshare b q k t r := by
  constructor
  · intro h
    obtain ⟨b', h⟩ := h
    obtain ⟨hb', h⟩ := sep_lift.mp h
    rw [hb] at hb'; cases hb'; exact h
  · exact fun h => ⟨b, sep_lift.mpr ⟨hb, h⟩⟩

/-- **Weaken a grant share's bound** (`EUpd.weaken` for a pointer). -/
theorem EUpd.pweaken {p : Ptr} {q : Frac} {k k' : Nat} {t : STag} (h : k' ≤ k) :
    EUpd (pshare p q k t) (pshare p q k' t) :=
  EUpd.exAll fun b => EUpd.lift fun hb =>
    EUpd.trans (EUpd.weaken h) (EUpd.of_imp fun _ h => ⟨b, sep_lift.mpr ⟨hb, h⟩⟩)

theorem sep_exR {γ : Type} {P : FAssn} {Q : γ → FAssn} {r : Res} (h : (P ⋆ FAssn.ex Q) r) :
    ∃ x, (P ⋆ Q x) r := by
  obtain ⟨x, h⟩ := sep_ex.mp (sep_comm h); exact ⟨x, sep_comm h⟩

/-- **A ledger at its epoch under an active parent is active**: the tag `(γ, e)` of a resource
that holds ledger `γ`'s authority with parent `p` among its parts, when `p` is active. -/
theorem act_gauthP {γ e : Nat} {M : GMap} {p : STag} {P : FAssn} {r : Res}
    (hw : Within (gauthP γ e M p) P) (hr : P r) (hp : Act r.gh.ls p) : Act r.gh.ls (some (γ, e)) := by
  refine .tag ?_ hp
  obtain ⟨R, r₁, r₂, -, rfl, ⟨-, -, g1⟩, -⟩ := hw r hr
  exact Ghost.ls_add r₁.gh r₂.gh γ e p (by rw [g1]; exact Ghost.at_auth1_ls)

/-- **A held grant share gives a live block** (`Holds.bshare`), for a share among the parts of
the resource whose tag is active. -/
theorem Holds.pshareW {p : Ptr} {b : BlockId} {q : Frac} {k : Nat} {t : STag} {m : Mem} {r rF : Res}
    {P : FAssn} (hh : Holds m r rF) (hw : Within (pshare p q k t) P) (hr : P r) (hb : p.block = some b)
    (ha : Act r.gh.ls t := by exact Act.root) :
    ∃ blk, m.blocks[b]? = some blk ∧ blk.live = true ∧ k ≤ blk.bytes.size ∧
      blk.kind.mappedLo < blk.bytes.size :=
  hh.bshareW (Within.trans (fun r h => ⟨emp, sep_emp.mpr ((pshare_iff hb).mp h)⟩) hw) hr ha

/-- Bytes an allocator has given up (padding, frees that were not the last allocation): any
bytes, which it never reads again before a reset. -/
def Junk : FAssn := FAssn.ex fun h : Heap => up (fun h' => h' = h)

theorem junk_absorb {X : Assn} {r : Res} (h : (up X ⋆ Junk) r) : Junk r := by
  obtain ⟨r₁, r₂, hd, rfl, h1, ⟨hj, h2⟩⟩ := h
  refine ⟨r₁.heap.erase ∪ hj, ?_⟩
  obtain ⟨-, k1, g1⟩ := h1
  obtain ⟨e2, k2, g2⟩ := h2
  refine ⟨?_, by simp [k1, k2, Know.union_none], by simp [g1, g2]⟩
  show (FHeap.union r₁.heap r₂.heap).erase = _
  rw [← e2]; exact FHeap.erase_union _ _

theorem junk_emp {r : Res} (h : emp r) : Junk r := ⟨Heap.empty, up_emp.mpr h⟩

/-- The separating conjunction of `f 0, …, f (n - 1)`. -/
def sepN : Nat → (Nat → FAssn) → FAssn
  | 0, _ => emp
  | n + 1, f => f n ⋆ sepN n f

theorem sep_emp_eq (P : FAssn) : (P ⋆ emp) = P := funext fun _ => propext sep_emp

theorem emp_sep_eq (P : FAssn) : (emp ⋆ P) = P := by rw [sep_comm_eq]; exact sep_emp_eq P

theorem sepN_congr {n : Nat} {f g : Nat → FAssn} (h : ∀ j, j < n → f j = g j) : sepN n f = sepN n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sepN]; rw [h n (by omega), ih fun j hj => h j (by omega)]

/-- Trailing empty conjuncts. -/
theorem sepN_extend {n n' : Nat} {f : Nat → FAssn} (hle : n ≤ n')
    (h : ∀ j, n ≤ j → j < n' → f j = emp) : sepN n' f = sepN n f := by
  induction n' with
  | zero => rw [Nat.le_zero.mp hle]
  | succ n' ih =>
    by_cases hn : n = n' + 1
    · subst hn; rfl
    · simp only [sepN]
      rw [h n' (by omega) (by omega), emp_sep_eq, ih (by omega) fun j h1 h2 => h j h1 (by omega)]

/-- `esum` only reads the summands below its bound. -/
theorem esum_congr {f g : Nat → Rat} : ∀ {N : Nat}, (∀ j, j < N → f j = g j) → esum f N = esum g N
  | 0, _ => rfl
  | N + 1, h => by simp only [esum]; rw [esum_congr fun j hj => h j (by omega), h N (by omega)]

/-- **Change one summand** of `esum`: the sum moves by the difference. -/
theorem esum_update {f g : Nat → Rat} {i : Nat} (hfg : ∀ j, j ≠ i → g j = f j) :
    ∀ {N : Nat}, i < N → esum g N + f i = esum f N + g i
  | 0, h => absurd h (Nat.not_lt_zero _)
  | N + 1, h => by
    simp only [esum]
    by_cases hi : i = N
    · subst hi; rw [esum_congr fun j hj => hfg j (by omega)]; grind
    · have := esum_update hfg (N := N) (by omega); rw [hfg N (Ne.symm hi)]; grind

/-- **Pick one conjunct** of `sepN`: `f i` and the others. -/
theorem sepN_pick {n i : Nat} {f : Nat → FAssn} (hi : i < n) :
    sepN n f = (f i ⋆ sepN n (fun j => if j = i then emp else f j)) := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [sepN]
    by_cases hin : i = n
    · subst hin
      rw [sepN_congr (g := f) (fun j hj => if_neg (by omega)), if_pos rfl, emp_sep_eq]
    · rw [ih (by omega), if_neg (Ne.symm hin)]; ac_rfl

/-- **Relabel the cells of a region**: a full-state cell's size is a label and its kind counts
up to `BlockKind.norm` (`FMatch` compares `Cell.norm`), so a region's bytes are also a region
with any size label and any kind of the same normal form. -/
theorem EUpd.relabel {p : Ptr} {A S S' : Nat} {K K' : BlockKind} {a : Nat} {bs : Array Byte}
    (hK : K'.norm = K.norm) : EUpd (up (regionIn p A S K a bs)) (up (regionIn p A S' K' a bs)) := by
  intro m r rF hh hp _
  obtain ⟨⟨hal, hc, b, hb, h0, hl⟩, hk, hg⟩ := hp
  let f : FCell → FCell := fun fc => { fc with cell := { fc.cell with size := S', kind := K' } }
  let r' : Res := ⟨fun l => (r.heap l).map f, r.know, r.gh⟩
  have hcell : ∀ l fc, r.heap l = some fc → fc.cell.addr = A ∧ fc.cell.size = S ∧ fc.cell.kind = K := by
    intro l fc e
    have := hl l
    simp only [FHeap.erase, e, Option.map_some] at this
    split at this
    · rw [Option.some.injEq] at this; rw [this]; exact ⟨rfl, rfl, rfl⟩
    · cases this
  have hsim : FHeap.Sim r'.heap r.heap := by
    intro l
    cases e : r.heap l with
    | none => simp [r', e]
    | some fc =>
      obtain ⟨-, -, hk'⟩ := hcell l fc e
      simp only [r', e, Option.map_some, f, Option.some.injEq, Prod.mk.injEq, and_true]
      simp only [Cell.norm, hK, hk']
  refine ⟨r', (Holds.congrF hh.swap hsim rfl rfl).swap, ⟨⟨hal, ?_, b, hb, h0, fun l => ?_⟩, hk, hg⟩⟩
  · intro hK'
    subst hK'
    cases K <;> simp_all [BlockKind.norm]
  · have := hl l
    simp only [FHeap.erase, r', Option.map_map] at this ⊢
    by_cases hin : l.1 = b ∧ p.off.toNat ≤ l.2 ∧ l.2 < p.off.toNat + bs.size
    · rw [if_pos hin] at this ⊢
      cases e : r.heap l with
      | none => rw [e] at this; cases this
      | some fc =>
        rw [e, Option.map_some, Option.some.injEq] at this
        rw [Option.map_some, Function.comp_apply]
        simp only [f, this]
    · rw [if_neg hin] at this ⊢
      cases e : r.heap l with
      | none => rfl
      | some fc => rw [e] at this; cases this

/-! ## The whole-region `resize` -/

theorem up_imp {P P' : Assn} {r : Res} (h : ∀ x, P x → P' x) (hp : up P r) : up P' r :=
  ⟨h _ hp.1, hp.2⟩

/-- Rearrange a separating conjunction (`ac_rfl` proves the equation). -/
theorem ac_cast {P Q : FAssn} {r : Res} (h : P r) (e : P = Q) : Q r := e ▸ h

theorem FAllocInv.granted_intro (I : FAllocInv) {p : Ptr} {k A S : Nat} {K : BlockKind} {q φ : Frac}
    {bs : Array Byte} {r : Res}
    (h : (up (regionIn p A S K (2 ^ k) bs) ⋆ (I.held p bs.size k A S K q q φ ⋆
      pclaim p p.off.toNat (p.off.toNat + bs.size) I.tag)) r) : I.granted p k φ bs r :=
  ⟨A, S, K, q, ac_cast h (by simp only [FAllocInv.held]; ac_rfl)⟩

/-- Two adjacent parts of a region and of its claim are one. -/
theorem region_claim_join {p : Ptr} {A S : Nat} {K : BlockKind} {a : Nat} {bs bs' : Array Byte}
    {t : STag} {r : Res} :
    ((up (regionIn p A S K a bs) ⋆ pclaim p p.off.toNat (p.off.toNat + bs.size) t) ⋆
      (up (regionIn (p.add bs.size) A S K 1 bs') ⋆
        pclaim p (p.off.toNat + bs.size) (p.off.toNat + (bs.size + bs'.size)) t)) r →
    (up (regionIn p A S K a (bs ++ bs')) ⋆
      pclaim p p.off.toNat (p.off.toNat + (bs ++ bs').size) t) r := fun h => by
  have h := ac_cast h (Q := (up (regionIn p A S K a bs) ⋆ up (regionIn (p.add bs.size) A S K 1 bs')) ⋆
    (pclaim p p.off.toNat (p.off.toNat + bs.size) t ⋆
      pclaim p (p.off.toNat + bs.size) (p.off.toNat + (bs.size + bs'.size)) t)) (by ac_rfl)
  rw [pclaim_split (by omega) (by omega), Array.size_append] at *
  exact sep_mono_left (fun _ x => up_imp (fun y hy => Region.regionIn_join hy) (sep_up x)) h

/-- **The whole-region `resize` is a corollary of the refined one**: a client that holds the whole
grant splits off the bytes a shrink releases and their claim, keeps the rest (relabelled to the
new token's labels: `EUpd.relabel`) and joins the new bytes of a growth and their claim to it.
It needs of the triple `T` only the structural rules `pre`, `frame`, `ex` and `eupdPost`, so it
holds in every logic of a program `c` (`resize_granted_of`: an `FLogic`; `CTriple` for a
concurrent entry, `CAllocSpec.resize_granted`). -/
theorem FAllocInv.resize_granted_gen (I : FAllocInv) {Prog : Type}
    {T : FAssn → Prog → (Bool → FAssn) → Prop} {c : Prog}
    (pre : ∀ {P P' : FAssn} {Q : Bool → FAssn}, T P c Q → (∀ r, P' r → P r) → T P' c Q)
    (frame : ∀ {P R : FAssn} {Q : Bool → FAssn}, T P c Q → T (P ⋆ R) c (fun v => Q v ⋆ R))
    (ex : ∀ {γ : Type} {P : γ → FAssn} {Q : Bool → FAssn}, (∀ x, T (P x) c Q) →
      T (FAssn.ex P) c Q)
    (eupdPost : ∀ {P : FAssn} {Q Q' : Bool → FAssn}, T P c Q → (∀ v, EUpd (Q v) (Q' v)) →
      T P c Q')
    {s : Slice} {k : Nat} {n : BitVec 64} {φ : Frac} {bs : Array Byte}
    (hr : ∀ (A S : Nat) (K : BlockKind) (q q' : Frac) (tl : Array Byte), q'.val ≤ q.val →
      (n.toNat < s.len.toNat → q' = q) →
      T (I.own ⋆ (I.held s.ptr s.len.toNat k A S K q q' φ ⋆
        I.relBytes s.ptr A S K n.toNat s.len.toNat tl)) c
        (I.rresizePost s.ptr k s.len.toNat n.toNat A S K q q' φ tl))
    (hs : s.len.toNat = bs.size) :
    T (I.own ⋆ I.granted s.ptr k φ bs) c (I.resizePost s.ptr k φ bs n.toNat) := by
  refine pre (P := FAssn.ex fun A : Nat => FAssn.ex fun S : Nat => FAssn.ex fun K : BlockKind =>
      FAssn.ex fun q : Frac =>
        (up (regionIn s.ptr A S K (2 ^ k) bs) ⋆ pclaim s.ptr s.ptr.off.toNat (s.ptr.off.toNat + bs.size) I.tag) ⋆
          (I.own ⋆ I.held s.ptr bs.size k A S K q q φ)) ?_ ?_
  rotate_left
  · intro r hr
    obtain ⟨A, hr⟩ := sep_exR hr; obtain ⟨S, hr⟩ := sep_exR hr
    obtain ⟨K, hr⟩ := sep_exR hr; obtain ⟨q, hr⟩ := sep_exR hr
    exact ⟨A, S, K, q, ac_cast hr (by simp only [FAllocInv.held]; ac_rfl)⟩
  refine ex fun A => ex fun S => ex fun K => ex fun q => ?_
  have hq : q.val ≤ q.val := Rat.le_refl
  by_cases hcut : n.toNat < bs.size
  · -- a shrink: split off the released bytes and their claim
    have hks : (bs.extract 0 n.toNat).size = n.toNat := by simp; omega
    have hts : (bs.extract n.toNat bs.size).size = bs.size - n.toNat := by simp
    have ht := hr A S K q q (bs.extract n.toNat bs.size) hq (fun _ => rfl)
    rw [hs] at ht
    refine eupdPost (pre (frame (R := up (regionIn s.ptr A S K (2 ^ k) (bs.extract 0 n.toNat)) ⋆
      pclaim s.ptr s.ptr.off.toNat (s.ptr.off.toNat + n.toNat) I.tag) ht) fun r hr => ?_) fun v => ?_
    · rw [← pclaim_split (m := s.ptr.off.toNat + n.toNat) (by omega) (by omega)] at hr
      have h1 := sep_mono_left (Q := (up (regionIn s.ptr A S K (2 ^ k) (bs.extract 0 n.toNat)) ⋆
          up (regionIn (s.ptr.add n.toNat) A S K 1 (bs.extract n.toNat bs.size))) ⋆
          (pclaim s.ptr s.ptr.off.toNat (s.ptr.off.toNat + n.toNat) I.tag ⋆
            pclaim s.ptr (s.ptr.off.toNat + n.toNat) (s.ptr.off.toNat + bs.size) I.tag))
        (fun r' hr' => sep_mono_left (fun _ x => up_sep (up_imp (fun x hx =>
        Region.regionIn_split hx (k := n.toNat) (a' := 1) (Nat.le_of_lt hcut) (Nat.mod_one _)) x)) hr') hr
      simp only [FAllocInv.relBytes, if_pos hcut]
      refine ac_cast (P := (I.own ⋆ (I.held s.ptr bs.size k A S K q q φ ⋆ (⟪(bs.extract n.toNat bs.size).size =
        bs.size - n.toNat⟫ ⋆ (up (regionIn (s.ptr.add n.toNat) A S K 1 (bs.extract n.toNat bs.size)) ⋆
          pclaim s.ptr (s.ptr.off.toNat + n.toNat) (s.ptr.off.toNat + bs.size) I.tag)))) ⋆
        (up (regionIn s.ptr A S K (2 ^ k) (bs.extract 0 n.toNat)) ⋆ pclaim s.ptr s.ptr.off.toNat (s.ptr.off.toNat + n.toNat) I.tag))
        ?_ rfl
      refine sep_mono_left (fun _ x => sep_mono_right (fun _ y => sep_mono_right
        (fun _ z => sep_lift.mpr ⟨hts, z⟩) y) x) (ac_cast h1 (by ac_rfl))
    cases v with
    | true =>
      simp only [FAllocInv.rresizePost, FAllocInv.newBytes, if_neg (show ¬ bs.size < n.toNat by omega),
        sep_emp_eq]
      refine EUpd.trans (P' := FAssn.ex fun S' : Nat => FAssn.ex fun K' : BlockKind =>
          ⟪K'.norm = K.norm⟫ ⋆ (up (regionIn s.ptr A S K (2 ^ k) (bs.extract 0 n.toNat)) ⋆
            (I.own ⋆ (I.held s.ptr n.toNat k A S' K' q q φ ⋆ pclaim s.ptr s.ptr.off.toNat (s.ptr.off.toNat + n.toNat) I.tag))))
        (EUpd.of_imp fun r hr => ?_) (EUpd.exAll fun S' => EUpd.exAll fun K' =>
        EUpd.lift fun hK => EUpd.trans (EUpd.frame (EUpd.relabel (p := s.ptr) (A := A) (S := S) (S' := S')
          (K := K) (K' := K') (a := 2 ^ k) (bs := bs.extract 0 n.toNat) hK)) (EUpd.of_imp fun r hr => ?_))
      · -- open the token's labels
        have e : ∀ (a b c d : FAssn), ((a ⋆ b) ⋆ (c ⋆ d)) = (b ⋆ (a ⋆ (c ⋆ d))) := by intros; ac_rfl
        rw [e] at hr
        obtain ⟨S', hr⟩ := sep_ex.mp hr; obtain ⟨K', hr⟩ := sep_ex.mp hr
        obtain ⟨hK, hr⟩ := sep_lift.mp (sep_assoc hr)
        exact ⟨S', K', sep_lift.mpr ⟨hK, ac_cast hr (by ac_rfl)⟩⟩
      · rw [sep_left_comm_eq] at hr
        refine sep_mono_right (fun _ x => ⟨bs.extract 0 n.toNat, sep_lift.mpr ⟨⟨hks, ?_⟩, ?_⟩⟩) hr
        · show (bs.extract 0 n.toNat).extract 0 bs.size = bs.extract 0 (bs.extract 0 n.toNat).size
          rw [hks]; apply Array.ext <;> simp <;> omega
        · exact FAllocInv.granted_intro I (by rw [hks]; exact x)
    | false =>
      simp only [FAllocInv.rresizePost, FAllocInv.relBytes, if_pos hcut]
      refine EUpd.of_imp fun r hr => ?_
      obtain ⟨-, hr⟩ := sep_lift.mp (ac_cast hr (Q := ⟪(bs.extract n.toNat bs.size).size = bs.size - n.toNat⟫ ⋆
        (I.own ⋆ (I.held s.ptr bs.size k A S K q q φ ⋆
          ((up (regionIn s.ptr A S K (2 ^ k) (bs.extract 0 n.toNat)) ⋆
            pclaim s.ptr s.ptr.off.toNat (s.ptr.off.toNat + n.toNat) I.tag) ⋆
          (up (regionIn (s.ptr.add n.toNat) A S K 1 (bs.extract n.toNat bs.size)) ⋆
            pclaim s.ptr (s.ptr.off.toNat + n.toNat) (s.ptr.off.toNat + bs.size) I.tag))))) (by ac_rfl))
      have hj := fun r => region_claim_join (p := s.ptr) (A := A) (S := S) (K := K) (a := 2 ^ k)
        (bs := bs.extract 0 n.toNat) (bs' := bs.extract n.toNat bs.size) (t := I.tag) (r := r)
      rw [hks, show n.toNat + (bs.extract n.toNat bs.size).size = bs.size by simp; omega,
        Array.extract_append_extract, Nat.min_def, if_pos (Nat.zero_le _), Nat.max_def,
        if_pos (Nat.le_of_lt hcut), Array.extract_size] at hj
      exact sep_mono_right (fun _ x => FAllocInv.granted_intro I (A := A) (S := S) (K := K) (q := q)
        (ac_cast (sep_mono_right (R := up (regionIn s.ptr A S K (2 ^ k) bs) ⋆
          pclaim s.ptr s.ptr.off.toNat (s.ptr.off.toNat + bs.size) I.tag) (fun _ y => hj _ y) x)
          (by ac_rfl))) hr
  · -- a growth (or the same length): the whole region and its claim stay with the client
    have hle : bs.size ≤ n.toNat := Nat.le_of_not_lt hcut
    have ht := hr A S K q q #[] hq (fun h' => absurd (hs ▸ h') hcut)
    rw [hs] at ht
    simp only [FAllocInv.relBytes, if_neg hcut, sep_emp_eq] at ht
    refine eupdPost (pre (frame (R := up (regionIn s.ptr A S K (2 ^ k) bs) ⋆
      pclaim s.ptr s.ptr.off.toNat (s.ptr.off.toNat + bs.size) I.tag) ht) fun r hr => sep_comm hr) fun v => ?_
    cases v with
    | true =>
      simp only [FAllocInv.rresizePost]
      refine EUpd.trans (P' := FAssn.ex fun S' : Nat => FAssn.ex fun K' : BlockKind =>
          ⟪K'.norm = K.norm⟫ ⋆ (up (regionIn s.ptr A S K (2 ^ k) bs) ⋆
            (I.own ⋆ (I.held s.ptr n.toNat k A S' K' q q φ ⋆ (pclaim s.ptr s.ptr.off.toNat (s.ptr.off.toNat + bs.size) I.tag ⋆
              I.newBytes s.ptr A S' K' bs.size n.toNat)))))
        (EUpd.of_imp fun r hr => ?_) (EUpd.exAll fun S' => EUpd.exAll fun K' =>
        EUpd.lift fun hK => EUpd.trans (EUpd.frame (EUpd.relabel (p := s.ptr) (A := A) (S := S) (S' := S')
          (K := K) (K' := K') (a := 2 ^ k) (bs := bs) hK)) (EUpd.of_imp fun r hr => ?_))
      · have e : ∀ (a b c d : FAssn), ((a ⋆ b) ⋆ (c ⋆ d)) = (b ⋆ (a ⋆ (c ⋆ d))) := by intros; ac_rfl
        rw [e] at hr
        obtain ⟨S', hr⟩ := sep_ex.mp hr; obtain ⟨K', hr⟩ := sep_ex.mp hr
        obtain ⟨hK, hr⟩ := sep_lift.mp (sep_assoc hr)
        exact ⟨S', K', sep_lift.mpr ⟨hK, ac_cast hr (by ac_rfl)⟩⟩
      · rw [sep_left_comm_eq] at hr
        refine sep_mono_right (fun r' hr' => ?_) hr
        by_cases hgrow : bs.size < n.toNat
        · simp only [FAllocInv.newBytes, if_pos hgrow] at hr'
          obtain ⟨t, h4⟩ := sep_exR (ac_cast hr' (Q := (up (regionIn s.ptr A S' K' (2 ^ k) bs) ⋆
            (I.held s.ptr n.toNat k A S' K' q q φ ⋆ pclaim s.ptr s.ptr.off.toNat (s.ptr.off.toNat + bs.size) I.tag)) ⋆ _) (by ac_rfl))
          obtain ⟨htz, h4⟩ := sep_lift.mp (ac_cast h4 (Q := ⟪t.size = n.toNat - bs.size⟫ ⋆
            (((up (regionIn s.ptr A S' K' (2 ^ k) bs) ⋆ pclaim s.ptr s.ptr.off.toNat (s.ptr.off.toNat + bs.size) I.tag) ⋆
              (up (regionIn (s.ptr.add bs.size) A S' K' 1 t) ⋆
                pclaim s.ptr (s.ptr.off.toNat + bs.size) (s.ptr.off.toNat + n.toNat) I.tag)) ⋆
              I.held s.ptr n.toNat k A S' K' q q φ)) (by ac_rfl))
          have h5 := h4
          rw [show s.ptr.off.toNat + n.toNat = s.ptr.off.toNat + (bs.size + t.size) by omega] at h5
          have hsz : (bs ++ t).size = n.toNat := by simp [htz]; omega
          refine ⟨bs ++ t, sep_lift.mpr ⟨⟨hsz, ?_⟩, FAllocInv.granted_intro I (A := A) (S := S') (K := K') (q := q) ?_⟩⟩
          · show (bs ++ t).extract 0 bs.size = bs.extract 0 (bs ++ t).size
            simp only [Array.size_append]
            rw [Array.extract_append_left, Array.extract_size]
            apply Array.ext <;> simp
          · have h6 := sep_mono_left (Q := up (regionIn s.ptr A S' K' (2 ^ k) (bs ++ t)) ⋆
              pclaim s.ptr s.ptr.off.toNat (s.ptr.off.toNat + (bs ++ t).size) I.tag)
              (fun _ x => region_claim_join x) h5
            rw [hsz] at h6 ⊢
            exact ac_cast h6 (by ac_rfl)
        · have hnb : n.toNat = bs.size := by omega
          simp only [FAllocInv.newBytes, if_neg hgrow, sep_emp_eq] at hr'
          refine ⟨bs, sep_lift.mpr ⟨⟨hnb.symm, rfl⟩, FAllocInv.granted_intro I (A := A) (S := S') (K := K') (q := q) ?_⟩⟩
          rw [← hnb]; exact ac_cast hr' (by rw [hnb])
    | false =>
      simp only [FAllocInv.rresizePost, FAllocInv.relBytes, if_neg hcut, sep_emp_eq]
      refine EUpd.of_imp fun r hr => ?_
      rw [sep_assoc_eq] at hr
      refine sep_mono_right (fun _ x => FAllocInv.granted_intro I (ac_cast x (by ac_rfl))) hr

/-- `resize_granted_gen` in an `FLogic`. -/
theorem FAllocInv.resize_granted_of (I : FAllocInv) {L : FLogic} {c : MemM Bool} {s : Slice}
    {k : Nat} {n : BitVec 64} {φ : Frac} {bs : Array Byte}
    (hr : ∀ (A S : Nat) (K : BlockKind) (q q' : Frac) (tl : Array Byte), q'.val ≤ q.val →
      (n.toNat < s.len.toNat → q' = q) →
      L.T (I.own ⋆ (I.held s.ptr s.len.toNat k A S K q q' φ ⋆
        I.relBytes s.ptr A S K n.toNat s.len.toNat tl)) c
        (I.rresizePost s.ptr k s.len.toNat n.toNat A S K q q' φ tl))
    (hs : s.len.toNat = bs.size) :
    L.T (I.own ⋆ I.granted s.ptr k φ bs) c (I.resizePost s.ptr k φ bs n.toNat) :=
  I.resize_granted_gen (T := fun P c Q => L.T P c Q) (fun h hp => L.pre h hp) (fun h => L.frame h)
    (fun h => L.ex h) (fun h hu => L.eupdPost h hu) hr hs

/-! ### Claims follow bytes: no client loses

In the refined `resize` the grant's claim follows its bytes: `held` carries no claim, the bytes a
shrink releases come with their claim (`relBytes`) and the new bytes of a growth with theirs
(`newBytes`). A client that holds the claim on the whole grant next to the token loses nothing:
it keeps the claim on the bytes it keeps and gets the claim on the whole new grant back
(`FAllocInv.resize_whole_of`). Nothing else changes, so the refined form asks less of a client
than a form whose `held` carries the whole claim, and gives the same claims back. -/

/-- The bytes `[n, len)` a shrink releases, without their claim. -/
def FAllocInv.relRegion (p : Ptr) (A S : Nat) (K : BlockKind) (n len : Nat) (tl : Array Byte) : FAssn :=
  if n < len then ⟪tl.size = len - n⟫ ⋆ up (regionIn (p.add n) A S K 1 tl) else emp

/-- The bytes `[len, n)` a growth adds, without their claim. -/
def FAllocInv.newRegion (p : Ptr) (A S : Nat) (K : BlockKind) (len n : Nat) : FAssn :=
  if len < n then FAssn.ex fun t : Array Byte => ⟪t.size = n - len⟫ ⋆ up (regionIn (p.add len) A S K 1 t)
  else emp

/-- `held` with the claim on the whole grant. -/
def FAllocInv.heldW (I : FAllocInv) (p : Ptr) (len k A S : Nat) (K : BlockKind) (q q' φ : Frac) :
    FAssn :=
  I.held p len k A S K q q' φ ⋆ pclaim p p.off.toNat (p.off.toNat + len) I.tag

/-- `rresizePost` with the claim on the whole grant in `held`. -/
def FAllocInv.rresizePostW (I : FAllocInv) (p : Ptr) (k len n A S : Nat) (K : BlockKind)
    (q q' φ : Frac) (tl : Array Byte) : Bool → FAssn
  | true => I.own ⋆ FAssn.ex fun S' : Nat => FAssn.ex fun K' : BlockKind => ⟪K'.norm = K.norm⟫ ⋆
      (I.heldW p n k A S' K' q q' φ ⋆ FAllocInv.newRegion p A S' K' len n)
  | false => I.own ⋆ (I.heldW p len k A S K q q' φ ⋆ FAllocInv.relRegion p A S K n len tl)

/-- **No client loses by claims following bytes**: the refined `resize` (claims in `relBytes` and
`newBytes`) gives the form in which `held` carries the claim on the whole grant, before and after. -/
theorem FAllocInv.resize_whole_of (I : FAllocInv) {L : FLogic} {c : MemM Bool} {p : Ptr}
    {k len n A S : Nat} {K : BlockKind} {q q' φ : Frac} {tl : Array Byte}
    (hr : L.T (I.own ⋆ (I.held p len k A S K q q' φ ⋆ I.relBytes p A S K n len tl)) c
      (I.rresizePost p k len n A S K q q' φ tl)) :
    L.T (I.own ⋆ (I.heldW p len k A S K q q' φ ⋆ FAllocInv.relRegion p A S K n len tl)) c
      (I.rresizePostW p k len n A S K q q' φ tl) := by
  by_cases hcut : n < len
  · refine L.eupdPost (L.pre (L.frame (R := pclaim p p.off.toNat (p.off.toNat + n) I.tag) hr)
      fun r hr => ?_) fun v => EUpd.of_imp fun r hr => ?_
    · simp only [FAllocInv.heldW, FAllocInv.relRegion, FAllocInv.relBytes, if_pos hcut] at hr ⊢
      rw [← pclaim_split (m := p.off.toNat + n) (by omega) (by omega)] at hr
      exact ac_cast hr (by ac_rfl)
    cases v with
    | true =>
      simp only [FAllocInv.rresizePost, FAllocInv.rresizePostW, FAllocInv.newBytes, FAllocInv.newRegion,
        if_neg (show ¬ len < n by omega), sep_emp_eq] at hr ⊢
      refine sep_mono_right (fun _ x => ?_) (sep_assoc hr)
      obtain ⟨S', x⟩ := sep_ex.mp x; obtain ⟨K', x⟩ := sep_ex.mp x
      obtain ⟨hK, x⟩ := sep_lift.mp (sep_assoc x)
      exact ⟨S', K', sep_lift.mpr ⟨hK, x⟩⟩
    | false =>
      simp only [FAllocInv.rresizePost, FAllocInv.rresizePostW, FAllocInv.heldW, FAllocInv.relRegion,
        FAllocInv.relBytes, if_pos hcut] at hr ⊢
      rw [← pclaim_split (m := p.off.toNat + n) (by omega) (by omega)]
      exact ac_cast hr (by ac_rfl)
  · refine L.eupdPost (L.pre (L.frame (R := pclaim p p.off.toNat (p.off.toNat + len) I.tag) hr)
      fun r hr => ?_) fun v => EUpd.of_imp fun r hr => ?_
    · simp only [FAllocInv.heldW, FAllocInv.relRegion, FAllocInv.relBytes, if_neg hcut] at hr ⊢
      exact ac_cast hr (by ac_rfl)
    cases v with
    | true =>
      simp only [FAllocInv.rresizePost, FAllocInv.rresizePostW] at hr ⊢
      refine sep_mono_right (fun _ x => ?_) (sep_assoc hr)
      obtain ⟨S', x⟩ := sep_ex.mp x; obtain ⟨K', x⟩ := sep_ex.mp x
      obtain ⟨hK, x⟩ := sep_lift.mp (sep_assoc x)
      refine ⟨S', K', sep_lift.mpr ⟨hK, ?_⟩⟩
      simp only [FAllocInv.heldW]
      by_cases hgrow : len < n
      · simp only [FAllocInv.newBytes, FAllocInv.newRegion, if_pos hgrow] at x ⊢
        obtain ⟨t, x⟩ := sep_ex.mp (ac_cast x (Q := (FAssn.ex fun t : Array Byte => ⟪t.size = n - len⟫ ⋆
          (up (regionIn (p.add len) A S' K' 1 t) ⋆ pclaim p (p.off.toNat + len) (p.off.toNat + n) I.tag)) ⋆
          (I.held p n k A S' K' q q' φ ⋆ pclaim p p.off.toNat (p.off.toNat + len) I.tag)) (by ac_rfl))
        rw [← pclaim_split (m := p.off.toNat + len) (by omega) (by omega)]
        refine sep_mono_right (fun _ y => ⟨t, y⟩) (ac_cast x (Q := (I.held p n k A S' K' q q' φ ⋆
          (pclaim p p.off.toNat (p.off.toNat + len) I.tag ⋆
            pclaim p (p.off.toNat + len) (p.off.toNat + n) I.tag)) ⋆
          (⟪t.size = n - len⟫ ⋆ up (regionIn (p.add len) A S' K' 1 t))) (by ac_rfl))
      · have hn : n = len := by omega
        subst hn
        simp only [FAllocInv.newBytes, FAllocInv.newRegion, if_neg hgrow, sep_emp_eq] at x ⊢
        exact x
    | false =>
      simp only [FAllocInv.rresizePost, FAllocInv.rresizePostW, FAllocInv.heldW, FAllocInv.relRegion,
        FAllocInv.relBytes, if_neg hcut] at hr ⊢
      exact ac_cast hr (by ac_rfl)

/-- **The whole-region `resize` of an allocator** (`FAllocInv.resize_granted_of`). -/
theorem FAllocSpec.resize_granted {L : FLogic} {vt : RawVTable} {ctx : Ptr} {I : FAllocInv}
    (h : FAllocSpec L vt ctx I) (s : Slice) (k : Nat) (n ra : BitVec 64) (φ : Frac) (bs : Array Byte)
    (hk : k < 64) (hn : 0 < n.toNat) (hf : I.fits n.toNat k) (hs : s.len.toNat = bs.size)
    (hb : 0 < bs.size) :
    L.T (I.own ⋆ I.granted s.ptr k φ bs) (vt.resize ctx s k n ra) (I.resizePost s.ptr k φ bs n.toNat) :=
  I.resize_granted_of (fun A S K q q' tl h1 h2 =>
    h.resize s k n ra A S K q q' φ tl hk hn hf (by omega) h1 h2) hs

/-! ## No embedding of the legacy logic

The block-extent model (`docs/sep-full-state.md` §Block extents) has no `FAllocSpec.ofTotal` and
no `FLogic.legacy` (with `LegacyTokens`, `FAllocSpec.toLegacy` and the full-state wrapper
contracts that used them). Both read an arbitrary legacy assertion as `up P`, whose cells no
longer pin their block's size: `tests/roadmap/sep-full/BlockExtentsCX.lean`
(`no_cell_size_triple`) is a `Tame` step with a total legacy triple that has no full-state
triple, so `FLogic.legacy` would not satisfy `Logic.ofTotal`. No legacy triple is lifted;
allocator specifications are proved against `FAllocSpec` directly. -/

end Full
end Zig
