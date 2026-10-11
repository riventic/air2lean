import ZigLean.Sep.Full.Logic
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
grants, `some (γ, e)` for one whose grants die with epoch `e` of its ledger `γ` (an arena). -/
structure FAllocInv where
  own : FAssn
  tok : Ptr → Nat → Nat → Nat → Nat → BlockKind → Frac → FAssn
  fits : Nat → Nat → Prop := fun _ _ => True
  tag : Option (Nat × Nat) := none

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

/-- After `remap` of the region `bs` at `p` to `n` bytes (`Zig.remapPost`). -/
def remapPost (p : Ptr) (k : Nat) (bs : Array Byte) (n : Nat) : Option Ptr → FAssn
  | none => I.own ⋆ I.granted p k bs
  | some q => I.own ⋆ FAssn.ex fun bs' => ⟪bs'.size = n ∧ keepsPrefix bs bs'⟫ ⋆ I.granted q k bs'

end FAllocInv

/-- `AllocSpec` over full-state assertions: the allocator `vt` with context `ctx` satisfies the
`std.mem.Allocator` contract in the logic `L`, with invariant `I`. -/
structure FAllocSpec (L : FLogic) (vt : RawVTable) (ctx : Ptr) (I : FAllocInv) : Prop where
  alloc : ∀ (len : BitVec 64) (k : Nat) (ra : BitVec 64), 0 < len.toNat → k < 64 →
    I.fits len.toNat k → L.T I.own (vt.alloc ctx len k ra) (I.allocPost len.toNat k)
  resize : ∀ (s : Slice) (k : Nat) (n ra : BitVec 64) (bs : Array Byte), k < 64 →
    0 < n.toNat → I.fits n.toNat k → s.len.toNat = bs.size → 0 < bs.size →
    L.T (I.own ⋆ I.granted s.ptr k bs) (vt.resize ctx s k n ra) (I.resizePost s.ptr k bs n.toNat)
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
  resize s k n ra bs h1 h2 h3 h4 h5 := L.toPartial (h.resize s k n ra bs h1 h2 h3 h4 h5)
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
  resize s k n ra bs h1 h2 h3 h4 h5 := L.congr (hr s k n ra) (h.resize s k n ra bs h1 h2 h3 h4 h5)
  remap s k n ra bs h1 h2 h3 h4 h5 := L.congr (hm s k n ra) (h.remap s k n ra bs h1 h2 h3 h4 h5)
  free s k ra bs h1 h2 h3 := L.congr (hf s k ra) (h.free s k ra bs h1 h2 h3)

/-- The four entries keep the atomic layout and every block's address. -/
structure VTame (vt : RawVTable) (ctx : Ptr) : Prop where
  alloc : ∀ len k ra, Tame (vt.alloc ctx len k ra)
  resize : ∀ s k n ra, Tame (vt.resize ctx s k n ra)
  remap : ∀ s k n ra, Tame (vt.remap ctx s k n ra)
  free : ∀ s k ra, Tame (vt.free ctx s k ra)

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
