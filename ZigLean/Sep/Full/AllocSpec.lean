import ZigLean.Sep.Full.Logic
import ZigLean.Sep.Full.Extent
import ZigLean.Sep.AllocSpec

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
`tok p n k A S K q` of a grant of `n` bytes at `p` with alignment `2 ^ k` in a block with
address `A`, size `S` and kind `K` (as the region's cells record them) sees the fraction `q` of
the grant's extent share (`granted`). `tag` is the epoch tag of that share
(`docs/sep-full-state.md` §Epoch-tagged shares): `none` for an allocator that never revokes its
grants, `some (γ, e)` for one whose grants die with epoch `e` of its ledger `γ` (an arena).

`act` is the allocator's obligation that **its state witnesses the tag of its shares as active**
(§Nested tags): whoever holds `own` holds the ledgers of the tag's whole chain. It is automatic
for an untagged allocator (`Act.root`). An allocator that holds another one's grants (an arena's
nodes) reads the bound of their shares from it (`Holds.bshare`), so the obligation composes: an
arena over a child proves `act` from its own ledger and the child's `act`. -/
structure FAllocInv where
  own : FAssn
  tok : Ptr → Nat → Nat → Nat → Nat → BlockKind → Frac → FAssn
  fits : Nat → Nat → Prop := fun _ _ => True
  tag : Option (Nat × Nat) := none
  act : ∀ r, own r → Act r.gh.ls tag := by intro _ _; exact Act.root

namespace FAllocInv

variable (I : FAllocInv)

/-- A region that `I`'s allocator granted (`Zig.granted`): its bytes, the token, and a share of
its block's extent up to the region's end. -/
def granted (p : Ptr) (k : Nat) (bs : Array Byte) : FAssn :=
  FAssn.ex fun A => FAssn.ex fun S => FAssn.ex fun K => FAssn.ex fun q =>
    up (regionIn p A S K (2 ^ k) bs) ⋆ (I.tok p bs.size k A S K q ⋆ pshare p q (p.off.toNat + bs.size) I.tag)

/-- After `alloc` of `len` bytes (`Zig.allocPost`). -/
def allocPost (len k : Nat) : Option Ptr → FAssn
  | none => I.own
  | some p => I.own ⋆ FAssn.ex fun bs => ⟪bs.size = len⟫ ⋆ I.granted p k bs

/-- After `resize` of the region `bs` at `p` to `n` bytes (`Zig.resizePost`). -/
def resizePost (p : Ptr) (k : Nat) (bs : Array Byte) (n : Nat) : Bool → FAssn
  | true => I.own ⋆ FAssn.ex fun bs' => ⟪bs'.size = n ∧ keepsPrefix bs bs'⟫ ⋆ I.granted p k bs'
  | false => I.own ⋆ I.granted p k bs

/-- What `resize` needs of a grant of `len` bytes besides its bytes: the token and a share `q'`
of the grant's extent share at the grant's end (any part of it: the holder may have lent the rest
on, as an arena does with its nodes). -/
def held (p : Ptr) (len k A S : Nat) (K : BlockKind) (q q' : Frac) : FAssn :=
  I.tok p len k A S K q ⋆ pshare p q' (p.off.toNat + len) I.tag

/-- The bytes `tl` that a shrink of a grant of `len` bytes at `p` to `n` bytes releases: the
bytes `[n, len)`, with the cell labels `A S K`; nothing for a growth. -/
def relBytes (p : Ptr) (A S : Nat) (K : BlockKind) (n len : Nat) (tl : Array Byte) : FAssn :=
  if n < len then ⟪tl.size = len - n⟫ ⋆ up (regionIn (p.add n) A S K 1 tl) else emp

/-- The bytes `[len, n)` that a growth of a grant at `p` from `len` to `n` bytes adds, any values,
with the cell labels `A S K`; nothing for a shrink. -/
def newBytes (p : Ptr) (A S : Nat) (K : BlockKind) (len n : Nat) : FAssn :=
  if len < n then FAssn.ex fun t : Array Byte => ⟪t.size = n - len⟫ ⋆ up (regionIn (p.add len) A S K 1 t)
  else emp

/-- **The refined `resize`** (`docs/sep-full-state.md` §`FAllocSpec` refined): from a grant of
`len` bytes to `n` bytes. On success the token is at `n` (same address; the size and kind labels
may change within the kind's normal form), the share is at the new end, and a growth hands over
the new bytes `[len, n)`. On failure the precondition comes back: the token, the share and the
released bytes `tl` of a shrink. -/
def rresizePost (p : Ptr) (k len n A S : Nat) (K : BlockKind) (q q' : Frac) (tl : Array Byte) :
    Bool → FAssn
  | true => I.own ⋆ FAssn.ex fun S' : Nat => FAssn.ex fun K' : BlockKind => ⟪K'.norm = K.norm⟫ ⋆
      (I.held p n k A S' K' q q' ⋆ newBytes p A S' K' len n)
  | false => I.own ⋆ (I.held p len k A S K q q' ⋆ relBytes p A S K n len tl)

/-- After `remap` of the region `bs` at `p` to `n` bytes (`Zig.remapPost`). -/
def remapPost (p : Ptr) (k : Nat) (bs : Array Byte) (n : Nat) : Option Ptr → FAssn
  | none => I.own ⋆ I.granted p k bs
  | some q => I.own ⋆ FAssn.ex fun bs' => ⟪bs'.size = n ∧ keepsPrefix bs bs'⟫ ⋆ I.granted q k bs'

/-- `act` of a resource that holds `own` among its parts. -/
theorem act_within {P : FAssn} {r : Res} (hw : Within I.own P) (hp : P r) : Act r.gh.ls I.tag := by
  obtain ⟨R, r₁, r₂, -, rfl, h1, -⟩ := hw r hp
  exact (I.act r₁ h1).mono (Ghost.ls_add _ _)

end FAllocInv

/-- `AllocSpec` over full-state assertions: the allocator `vt` with context `ctx` satisfies the
`std.mem.Allocator` contract in the logic `L`, with invariant `I`. -/
structure FAllocSpec (L : FLogic) (vt : RawVTable) (ctx : Ptr) (I : FAllocInv) : Prop where
  alloc : ∀ (len : BitVec 64) (k : Nat) (ra : BitVec 64), 0 < len.toNat → k < 64 →
    I.fits len.toNat k → L.T I.own (vt.alloc ctx len k ra) (I.allocPost len.toNat k)
  /-- The refined `resize` (`FAllocInv.rresizePost`): the token, a part `q' ≤ q` of the grant's
  extent share and only the released bytes; the client keeps the bytes it keeps. A growth takes
  any part of the share (every other part stays true when the block grows); a shrink takes the
  whole share `q' = q` (an allocator may shrink the block itself, `munmap` of a tail: no other
  share may then claim the old end). The whole-region form is the corollary
  `FAllocSpec.resize_granted`. -/
  resize : ∀ (s : Slice) (k : Nat) (n ra : BitVec 64) (A S : Nat) (K : BlockKind) (q q' : Frac)
    (tl : Array Byte), k < 64 → 0 < n.toNat → I.fits n.toNat k → 0 < s.len.toNat →
    q'.val ≤ q.val → (n.toNat < s.len.toNat → q' = q) →
    L.T (I.own ⋆ (I.held s.ptr s.len.toNat k A S K q q' ⋆
      FAllocInv.relBytes s.ptr A S K n.toNat s.len.toNat tl))
      (vt.resize ctx s k n ra) (I.rresizePost s.ptr k s.len.toNat n.toNat A S K q q' tl)
  remap : ∀ (s : Slice) (k : Nat) (n ra : BitVec 64) (bs : Array Byte), k < 64 →
    0 < n.toNat → I.fits n.toNat k → s.len.toNat = bs.size → 0 < bs.size →
    L.T (I.own ⋆ I.granted s.ptr k bs) (vt.remap ctx s k n ra) (I.remapPost s.ptr k bs n.toNat)
  free : ∀ (s : Slice) (k : Nat) (ra : BitVec 64) (bs : Array Byte), k < 64 →
    s.len.toNat = bs.size → 0 < bs.size →
    L.T (I.own ⋆ I.granted s.ptr k bs) (vt.free ctx s k ra) (fun _ => I.own)

/-- A total allocator is a partial one. -/
theorem FAllocSpec.toPartial {L : FLogic} {vt : RawVTable} {ctx : Ptr} {I : FAllocInv}
    (h : FAllocSpec L vt ctx I) : FAllocSpec FLogic.partial vt ctx I where
  alloc len k ra h1 h2 h3 := L.toPartial (h.alloc len k ra h1 h2 h3)
  resize s k n ra A S K q q' tl h1 h2 h3 h4 h5 h6 :=
    L.toPartial (h.resize s k n ra A S K q q' tl h1 h2 h3 h4 h5 h6)
  remap s k n ra bs h1 h2 h3 h4 h5 := L.toPartial (h.remap s k n ra bs h1 h2 h3 h4 h5)
  free s k ra bs h1 h2 h3 := L.toPartial (h.free s k ra bs h1 h2 h3)

/-- The spec only depends on the runs of the entries from full-state sequential memories. -/
theorem FAllocSpec.congr {L : FLogic} {vt vt' : RawVTable} {ctx : Ptr} {I : FAllocInv}
    (h : FAllocSpec L vt ctx I)
    (ha : ∀ len k ra m, m.FSeq → (vt'.alloc ctx len k ra).run m = (vt.alloc ctx len k ra).run m)
    (hr : ∀ s k n ra m, m.FSeq → (vt'.resize ctx s k n ra).run m = (vt.resize ctx s k n ra).run m)
    (hm : ∀ s k n ra m, m.FSeq → (vt'.remap ctx s k n ra).run m = (vt.remap ctx s k n ra).run m)
    (hf : ∀ s k ra m, m.FSeq → (vt'.free ctx s k ra).run m = (vt.free ctx s k ra).run m) :
    FAllocSpec L vt' ctx I where
  alloc len k ra h1 h2 h3 := L.congr (ha len k ra) (h.alloc len k ra h1 h2 h3)
  resize s k n ra A S K q q' tl h1 h2 h3 h4 h5 h6 :=
    L.congr (hr s k n ra) (h.resize s k n ra A S K q q' tl h1 h2 h3 h4 h5 h6)
  remap s k n ra bs h1 h2 h3 h4 h5 := L.congr (hm s k n ra) (h.remap s k n ra bs h1 h2 h3 h4 h5)
  free s k ra bs h1 h2 h3 := L.congr (hf s k ra) (h.free s k ra bs h1 h2 h3)

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

theorem FAllocInv.granted_intro (I : FAllocInv) {p : Ptr} {k A S : Nat} {K : BlockKind} {q : Frac}
    {bs : Array Byte} {r : Res}
    (h : (up (regionIn p A S K (2 ^ k) bs) ⋆ I.held p bs.size k A S K q q) r) : I.granted p k bs r :=
  ⟨A, S, K, q, h⟩

/-- **The whole-region `resize` is a corollary of the refined one**: a client that holds the whole
grant splits off the bytes a shrink releases, keeps the rest (relabelled to the new token's labels:
`EUpd.relabel`) and joins the new bytes of a growth to it. -/
theorem FAllocSpec.resize_granted {L : FLogic} {vt : RawVTable} {ctx : Ptr} {I : FAllocInv}
    (h : FAllocSpec L vt ctx I) (s : Slice) (k : Nat) (n ra : BitVec 64) (bs : Array Byte)
    (hk : k < 64) (hn : 0 < n.toNat) (hf : I.fits n.toNat k) (hs : s.len.toNat = bs.size)
    (hb : 0 < bs.size) :
    L.T (I.own ⋆ I.granted s.ptr k bs) (vt.resize ctx s k n ra) (I.resizePost s.ptr k bs n.toNat) := by
  refine L.pre (P := FAssn.ex fun A : Nat => FAssn.ex fun S : Nat => FAssn.ex fun K : BlockKind =>
      FAssn.ex fun q : Frac =>
        up (regionIn s.ptr A S K (2 ^ k) bs) ⋆ (I.own ⋆ I.held s.ptr bs.size k A S K q q)) ?_ ?_
  rotate_left
  · intro r hr
    obtain ⟨A, hr⟩ := sep_exR hr; obtain ⟨S, hr⟩ := sep_exR hr
    obtain ⟨K, hr⟩ := sep_exR hr; obtain ⟨q, hr⟩ := sep_exR hr
    rw [sep_left_comm_eq] at hr
    exact ⟨A, S, K, q, hr⟩
  refine L.ex fun A => L.ex fun S => L.ex fun K => L.ex fun q => ?_
  have hq : q.val ≤ q.val := Rat.le_refl
  by_cases hcut : n.toNat < bs.size
  · -- a shrink: split off the released bytes
    have hks : (bs.extract 0 n.toNat).size = n.toNat := by simp; omega
    have hts : (bs.extract n.toNat bs.size).size = bs.size - n.toNat := by simp
    have ht := h.resize s k n ra A S K q q (bs.extract n.toNat bs.size) hk hn hf (by omega) hq
      (fun _ => rfl)
    rw [hs] at ht
    refine L.eupdPost (L.pre (L.frame (R := up (regionIn s.ptr A S K (2 ^ k) (bs.extract 0 n.toNat))) ht)
      fun r hr => ?_) fun v => ?_
    · have h1 := sep_mono_left (fun r' hr' => up_sep (up_imp (fun x hx =>
        Region.regionIn_split hx (k := n.toNat) (a' := 1) (Nat.le_of_lt hcut) (Nat.mod_one _)) hr')) hr
      have h2 := sep_mono_left (fun r' hr' => sep_mono_right (fun _ x =>
        (sep_lift.mpr ⟨hts, x⟩ : (⟪(bs.extract n.toNat bs.size).size = bs.size - n.toNat⟫ ⋆ _) _)) hr') h1
      simp only [FAllocInv.relBytes, if_pos hcut]
      have e : ∀ (a b c : FAssn), ((a ⋆ b) ⋆ c) = ((c ⋆ b) ⋆ a) := by intros; ac_rfl
      rw [e] at h2
      exact sep_mono_left (fun _ x => sep_assoc x) h2
    cases v with
    | true =>
      simp only [FAllocInv.rresizePost, FAllocInv.newBytes, if_neg (show ¬ bs.size < n.toNat by omega),
        sep_emp_eq]
      refine EUpd.trans (P' := FAssn.ex fun S' : Nat => FAssn.ex fun K' : BlockKind =>
          ⟪K'.norm = K.norm⟫ ⋆ (up (regionIn s.ptr A S K (2 ^ k) (bs.extract 0 n.toNat)) ⋆
            (I.own ⋆ I.held s.ptr n.toNat k A S' K' q q)))
        (EUpd.of_imp fun r hr => ?_) (EUpd.exAll fun S' => EUpd.exAll fun K' =>
        EUpd.lift fun hK => EUpd.trans (EUpd.frame (EUpd.relabel (p := s.ptr) (A := A) (S := S) (S' := S')
          (K := K) (K' := K') (a := 2 ^ k) (bs := bs.extract 0 n.toNat) hK)) (EUpd.of_imp fun r hr => ?_))
      · -- open the token's labels
        have e : ∀ (a b c : FAssn), ((a ⋆ b) ⋆ c) = (b ⋆ (c ⋆ a)) := by intros; ac_rfl
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
      have e : ∀ (a b c d f : FAssn), ((a ⋆ (b ⋆ (c ⋆ d))) ⋆ f) = (a ⋆ (c ⋆ ((f ⋆ d) ⋆ b))) := by
        intros; ac_rfl
      rw [e] at hr
      refine sep_mono_right (fun r' hr' => ?_) hr
      obtain ⟨-, hr'⟩ := sep_lift.mp hr'
      refine FAllocInv.granted_intro I (sep_mono_left (fun _ x => up_imp (fun y hy => ?_) (sep_up x)) hr')
      have := Region.regionIn_join (p := s.ptr) (A := A) (S := S) (K := K) (a := 2 ^ k) (a' := 1)
        (bs := bs.extract 0 n.toNat) (bs' := bs.extract n.toNat bs.size) (by rw [hks]; exact hy)
      rwa [Array.extract_append_extract, Nat.min_def, if_pos (Nat.zero_le _), Nat.max_def,
        if_pos (Nat.le_of_lt hcut), Array.extract_size] at this
  · -- a growth (or the same length): the whole region stays with the client
    have hle : bs.size ≤ n.toNat := Nat.le_of_not_lt hcut
    have ht := h.resize s k n ra A S K q q #[] hk hn hf (by omega) hq (fun h' => absurd (hs ▸ h') hcut)
    rw [hs] at ht
    simp only [FAllocInv.relBytes, if_neg hcut, sep_emp_eq] at ht
    refine L.eupdPost (L.pre (L.frame (R := up (regionIn s.ptr A S K (2 ^ k) bs)) ht)
      fun r hr => sep_comm hr) fun v => ?_
    cases v with
    | true =>
      simp only [FAllocInv.rresizePost]
      refine EUpd.trans (P' := FAssn.ex fun S' : Nat => FAssn.ex fun K' : BlockKind =>
          ⟪K'.norm = K.norm⟫ ⋆ (up (regionIn s.ptr A S K (2 ^ k) bs) ⋆
            (I.own ⋆ (I.held s.ptr n.toNat k A S' K' q q ⋆ FAllocInv.newBytes s.ptr A S' K' bs.size n.toNat))))
        (EUpd.of_imp fun r hr => ?_) (EUpd.exAll fun S' => EUpd.exAll fun K' =>
        EUpd.lift fun hK => EUpd.trans (EUpd.frame (EUpd.relabel (p := s.ptr) (A := A) (S := S) (S' := S')
          (K := K) (K' := K') (a := 2 ^ k) (bs := bs) hK)) (EUpd.of_imp fun r hr => ?_))
      · have e : ∀ (a b c : FAssn), ((a ⋆ b) ⋆ c) = (b ⋆ (c ⋆ a)) := by intros; ac_rfl
        rw [e] at hr
        obtain ⟨S', hr⟩ := sep_ex.mp hr; obtain ⟨K', hr⟩ := sep_ex.mp hr
        obtain ⟨hK, hr⟩ := sep_lift.mp (sep_assoc hr)
        exact ⟨S', K', sep_lift.mpr ⟨hK, ac_cast hr (by ac_rfl)⟩⟩
      · rw [sep_left_comm_eq] at hr
        refine sep_mono_right (fun r' hr' => ?_) hr
        by_cases hgrow : bs.size < n.toNat
        · simp only [FAllocInv.newBytes, if_pos hgrow] at hr'
          obtain ⟨t, h4⟩ := sep_exR (sep_assoc' hr')
          obtain ⟨htz, h5⟩ := sep_lift.mp (ac_cast h4 (Q := ⟪t.size = n.toNat - bs.size⟫ ⋆
            ((up (regionIn s.ptr A S' K' (2 ^ k) bs) ⋆ up (regionIn (s.ptr.add bs.size) A S' K' 1 t)) ⋆
              I.held s.ptr n.toNat k A S' K' q q)) (by ac_rfl))
          have hsz : (bs ++ t).size = n.toNat := by simp [htz]; omega
          refine ⟨bs ++ t, sep_lift.mpr ⟨⟨hsz, ?_⟩, FAllocInv.granted_intro I (A := A) (S := S') (K := K') (q := q) ?_⟩⟩
          · show (bs ++ t).extract 0 bs.size = bs.extract 0 (bs ++ t).size
            simp only [Array.size_append]
            rw [Array.extract_append_left, Array.extract_size]
            apply Array.ext <;> simp
          · rw [hsz]
            exact sep_mono_left (fun _ x => up_imp (fun y hy => Region.regionIn_join hy) (sep_up x)) h5
        · have hnb : n.toNat = bs.size := by omega
          simp only [FAllocInv.newBytes, if_neg hgrow, sep_emp_eq] at hr'
          refine ⟨bs, sep_lift.mpr ⟨⟨hnb.symm, rfl⟩, FAllocInv.granted_intro I (A := A) (S := S') (K := K') (q := q) ?_⟩⟩
          rw [← hnb]; exact hr'
    | false =>
      simp only [FAllocInv.rresizePost, FAllocInv.relBytes, if_neg hcut, sep_emp_eq]
      refine EUpd.of_imp fun r hr => ?_
      rw [sep_assoc_eq] at hr
      refine sep_mono_right (fun _ x => FAllocInv.granted_intro I (sep_comm x)) hr

/-! ## No embedding of the legacy logic

The block-extent model (`docs/sep-full-state.md` §Block extents) has no `FAllocSpec.ofTotal` and
no `FLogic.legacy` (with `LegacyTokens`, `FAllocSpec.toLegacy` and the full-state wrapper
contracts that used them). Both read an arbitrary legacy assertion as `up P`, whose cells no
longer pin their block's size: `tests/roadmap/sep-full/BlockExtentsCX.lean`
(`no_cell_size_triple`) is a `Tame` step with a total legacy triple that has no full-state
triple, so `FLogic.legacy` would not satisfy `Logic.ofTotal`. A legacy triple lifts with its
side conditions (`FTriple.ofTriple`: size-free outside owned extents, extent-keeping); allocator
specifications are proved against `FAllocSpec` directly. -/

end Full
end Zig
