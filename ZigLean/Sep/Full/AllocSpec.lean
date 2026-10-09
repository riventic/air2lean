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

`FAllocSpec.ofTotal` turns a legacy total specification into a full one, given that the four
entries are `Tame` (they keep the atomic layout and the block addresses). The translated
`FixedBufferAllocator` gets its full specification this way (`tests/roadmap/alloc-fba`).
-/

namespace Zig
namespace Full

open FAssn

/-- An allocator invariant over full-state assertions (`AllocInv`). -/
structure FAllocInv where
  own : FAssn
  tok : Ptr → Nat → Nat → Nat → Nat → BlockKind → FAssn
  fits : Nat → Nat → Prop := fun _ _ => True

namespace FAllocInv

variable (I : FAllocInv)

/-- A region that `I`'s allocator granted (`Zig.granted`). -/
def granted (p : Ptr) (k : Nat) (bs : Array Byte) : FAssn :=
  FAssn.ex fun A => FAssn.ex fun S => FAssn.ex fun K =>
    up (regionIn p A S K (2 ^ k) bs) ⋆ I.tok p bs.size k A S K

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

/-! ## Legacy specifications, lifted -/

/-- A legacy invariant as a full-state one: its assertions under `up` (any atomic layout, no
knowledge). -/
def _root_.Zig.AllocInv.toFull (I : AllocInv) : FAllocInv where
  own := FAssn.up I.own
  tok p n k A S K := FAssn.up (I.tok p n k A S K)
  fits := I.fits

/-- The four entries keep the atomic layout and every block's address. -/
structure VTame (vt : RawVTable) (ctx : Ptr) : Prop where
  alloc : ∀ len k ra, Tame (vt.alloc ctx len k ra)
  resize : ∀ s k n ra, Tame (vt.resize ctx s k n ra)
  remap : ∀ s k n ra, Tame (vt.remap ctx s k n ra)
  free : ∀ s k ra, Tame (vt.free ctx s k ra)

section Lift

variable {I : AllocInv} {r : Res}

theorem up_granted {p : Ptr} {k : Nat} {bs : Array Byte} :
    I.toFull.granted p k bs r ↔ up (granted I p k bs) r := by
  constructor
  · rintro ⟨A, S, K, h⟩
    exact up_ex.mpr ⟨A, up_ex.mpr ⟨S, up_ex.mpr ⟨K, sep_up h⟩⟩⟩
  · intro h
    obtain ⟨A, h⟩ := up_ex.mp h
    obtain ⟨S, h⟩ := up_ex.mp h
    obtain ⟨K, h⟩ := up_ex.mp h
    exact ⟨A, S, K, up_sep h⟩

theorem up_own_granted {p : Ptr} {k : Nat} {bs : Array Byte}
    (h : (I.toFull.own ⋆ I.toFull.granted p k bs) r) : up (I.own ∗ granted I p k bs) r :=
  sep_up (sep_mono_right (fun _ h => up_granted.mp h) h)

/-- `up (⌜φ⌝ ∗ granted)`, as a full `⟪φ⟫ ⋆ granted`. -/
theorem up_lift_granted {φ : Prop} {p : Ptr} {k : Nat} {bs : Array Byte}
    (h : up (⌜φ⌝ ∗ granted I p k bs) r) : (⟪φ⟫ ⋆ I.toFull.granted p k bs) r := by
  obtain ⟨hφ, h⟩ := up_lift.mp h
  exact sep_lift.mpr ⟨hφ, up_granted.mpr h⟩

theorem up_allocPost {n k : Nat} {v : Option Ptr} (h : up (allocPost I n k v) r) :
    I.toFull.allocPost n k v r := by
  cases v with
  | none => exact h
  | some p =>
    refine sep_mono_right (fun r h => ?_) (up_sep h)
    obtain ⟨bs, h⟩ := up_ex.mp h
    exact ⟨bs, up_lift_granted h⟩

theorem up_own_granted' {p : Ptr} {k : Nat} {bs : Array Byte}
    (h : up (I.own ∗ granted I p k bs) r) : (I.toFull.own ⋆ I.toFull.granted p k bs) r :=
  sep_mono_right (fun _ h => up_granted.mpr h) (up_sep h)

theorem up_resizePost {p : Ptr} {k : Nat} {bs : Array Byte} {n : Nat} {v : Bool}
    (h : up (resizePost I p k bs n v) r) : I.toFull.resizePost p k bs n v r := by
  cases v with
  | false => exact up_own_granted' h
  | true =>
    refine sep_mono_right (fun r h => ?_) (up_sep h)
    obtain ⟨bs', h⟩ := up_ex.mp h
    exact ⟨bs', up_lift_granted h⟩

theorem up_remapPost {p : Ptr} {k : Nat} {bs : Array Byte} {n : Nat} {v : Option Ptr}
    (h : up (remapPost I p k bs n v) r) : I.toFull.remapPost p k bs n v r := by
  cases v with
  | none => exact up_own_granted' h
  | some q =>
    refine sep_mono_right (fun r h => ?_) (up_sep h)
    obtain ⟨bs', h⟩ := up_ex.mp h
    exact ⟨bs', up_lift_granted h⟩

end Lift

/-- **A legacy total specification of a tame allocator is a full one**, with the invariant
under `up`. -/
theorem FAllocSpec.ofTotal {vt : RawVTable} {ctx : Ptr} {I : AllocInv}
    (h : AllocSpec Logic.total vt ctx I) (ht : VTame vt ctx) :
    FAllocSpec FLogic.total vt ctx I.toFull where
  alloc len k ra h1 h2 h3 :=
    (FTotalTriple.ofTotal (h.alloc len k ra h1 h2 h3) (ht.alloc len k ra)).post
      fun _ _ h => up_allocPost h
  resize s k n ra bs h1 h2 h3 h4 h5 :=
    (FTotalTriple.ofTotal (h.resize s k n ra bs h1 h2 h3 h4 h5) (ht.resize s k n ra)).conseq
      (fun _ h => up_own_granted h) fun _ _ h => up_resizePost h
  remap s k n ra bs h1 h2 h3 h4 h5 :=
    (FTotalTriple.ofTotal (h.remap s k n ra bs h1 h2 h3 h4 h5) (ht.remap s k n ra)).conseq
      (fun _ h => up_own_granted h) fun _ _ h => up_remapPost h
  free s k ra bs h1 h2 h3 :=
    (FTotalTriple.ofTotal (h.free s k ra bs h1 h2 h3) (ht.free s k ra)).pre
      fun _ h => up_own_granted h

end Full
end Zig
