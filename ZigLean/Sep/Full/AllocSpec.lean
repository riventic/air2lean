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

/-! ## The legacy contracts in the full-state logic

`FLogic.legacy FL O` reads a legacy assertion `P` as `O ⋆ up P` in the full-state logic `FL`, for
a fixed full-state frame `O` (the allocator state an `FAllocInv` owns beyond its legacy part). It
is a `Logic`: legacy total triples of `Tame` programs lift (`FTotalTriple.ofTotal`), and the
structural rules carry over. `FAllocSpec.toLegacy` turns a full-state allocator specification
whose tokens are legacy (`up`) into a legacy `AllocSpec` in that logic. So every contract proved
for an arbitrary `Logic` (`Wrap.*_spec`, `ZigLean/Sep/AllocSpec/Wrappers.lean`) holds in the
full-state logic, with the allocator state framed: for the FixedBufferAllocator
(`FBA.fallocSpec`) and the page allocator (`PageSpec.inv`).
-/

theorem up_mono {P P' : Assn} {r : Res} (h : ∀ x, P x → P' x) (hp : up P r) : up P' r :=
  ⟨h _ hp.1, hp.2⟩

/-- The full-state logic `FL` with the frame `O` around every legacy assertion. -/
def FLogic.legacy (FL : FLogic) (O : FAssn) : Logic where
  T P c Q := FL.T (O ⋆ up P) c (fun v => O ⋆ up (Q v))
  ofTotal ht hc := FL.ofTotal (FLogic.total.frameL (FTotalTriple.ofTotal ht hc))
  conseq ht hp hq := FL.conseq ht (fun _ h => sep_mono_right (fun _ x => up_mono hp x) h)
    (fun v _ h => sep_mono_right (fun _ x => up_mono (hq v) x) h)
  frame ht := FL.conseq (FL.frame (R := up _) ht)
    (fun _ h => sep_assoc' (sep_mono_right (fun _ x => up_sep x) h))
    (fun _ _ h => sep_mono_right (fun _ x => sep_up x) (sep_assoc h))
  bind hc hf := FL.bind hc hf
  ex h := FL.pre (FL.ex h) fun _ hp => by
    obtain ⟨x, hx⟩ := sep_ex.mp (sep_comm (sep_mono_right (fun _ y => up_ex.mp y) hp))
    exact ⟨x, sep_comm hx⟩
  lift h := FL.pre (FL.lift h) fun _ hp => by
    obtain ⟨r₁, r₂, hd, rfl, ho, hq⟩ := hp
    obtain ⟨hφ, hq⟩ := up_lift.mp hq
    exact sep_lift.mpr ⟨hφ, ⟨r₁, r₂, hd, rfl, ho, hq⟩⟩
  congr he ht := FL.congr (fun m hm => he m hm.1) ht

/-- `J` is the legacy invariant `I` with the full-state allocator state `O` added: its tokens are
`I`'s under `up`, it owns `O ⋆ up I.own`, and it accepts the same requests. -/
structure LegacyTokens (J : FAllocInv) (I : AllocInv) (O : FAssn) : Prop where
  tok : ∀ p n k A S K, J.tok p n k A S K = up (I.tok p n k A S K)
  own : ∀ r, J.own r ↔ (O ⋆ up I.own) r
  fits : ∀ n k, J.fits n k ↔ I.fits n k

/-- A lifted legacy invariant (`FBA.fallocSpec`) has no full-state allocator state. -/
theorem AllocInv.toFull_legacy (I : AllocInv) : LegacyTokens I.toFull I emp :=
  ⟨fun _ _ _ _ _ _ => rfl, fun _ => ⟨fun h => sep_comm (sep_emp.mpr h),
    fun h => sep_emp.mp (sep_comm h)⟩, fun _ _ => Iff.rfl⟩

section ToLegacy

variable {J : FAllocInv} {I : AllocInv} {O : FAssn} {r : Res}

theorem granted_up (htok : ∀ p n k A S K, J.tok p n k A S K = up (I.tok p n k A S K))
    {p : Ptr} {k : Nat} {bs : Array Byte} : J.granted p k bs r ↔ up (granted I p k bs) r := by
  have e : J.granted p k bs = I.toFull.granted p k bs := by
    unfold FAllocInv.granted; simp only [htok]; rfl
  rw [e]; exact up_granted

theorem lift_granted_up (htok : ∀ p n k A S K, J.tok p n k A S K = up (I.tok p n k A S K))
    {φ : Array Byte → Prop} {p : Ptr} {k : Nat} :
    (FAssn.ex fun bs => ⟪φ bs⟫ ⋆ J.granted p k bs) r ↔
      up (Assn.ex fun bs => ⌜φ bs⌝ ∗ granted I p k bs) r := by
  constructor
  · rintro ⟨bs, h⟩
    obtain ⟨hφ, hg⟩ := sep_lift.mp h
    exact up_ex.mpr ⟨bs, up_lift.mpr ⟨hφ, (granted_up htok).mp hg⟩⟩
  · intro h
    obtain ⟨bs, h⟩ := up_ex.mp h
    obtain ⟨hφ, hg⟩ := up_lift.mp h
    exact ⟨bs, sep_lift.mpr ⟨hφ, (granted_up htok).mpr hg⟩⟩

/-- `J.own ⋆ X'` as `O ⋆ up (I.own ∗ X)`, for parts `X'` and `X` that agree. -/
theorem own_to {X' : FAssn} {X : Assn} (hown : ∀ r, J.own r ↔ (O ⋆ up I.own) r)
    (hx : ∀ r, X' r → up X r) (h : (J.own ⋆ X') r) : (O ⋆ up (I.own ∗ X)) r :=
  sep_mono_right (fun _ y => sep_up y)
    (sep_assoc (sep_mono (fun _ y => (hown _).mp y) hx h))

theorem own_from {X' : FAssn} {X : Assn} (hown : ∀ r, J.own r ↔ (O ⋆ up I.own) r)
    (hx : ∀ r, up X r → X' r) (h : (O ⋆ up (I.own ∗ X)) r) : (J.own ⋆ X') r :=
  sep_mono (fun _ y => (hown _).mpr y) hx (sep_assoc' (sep_mono_right (fun _ y => up_sep y) h))

theorem FAllocSpec.toLegacy' {FL : FLogic} {vt : RawVTable} {ctx : Ptr}
    (h : FAllocSpec FL vt ctx J)
    (htok : ∀ p n k A S K, J.tok p n k A S K = up (I.tok p n k A S K))
    (hown : ∀ r, J.own r ↔ (O ⋆ up I.own) r) (hfits : ∀ n k, J.fits n k ↔ I.fits n k) :
    AllocSpec (FL.legacy O) vt ctx I where
  alloc len k ra h1 h2 h3 := FL.conseq (h.alloc len k ra h1 h2 ((hfits _ _).mpr h3))
    (fun _ hp => (hown _).mpr hp)
    (fun v _ hq => by
      cases v with
      | none => exact (hown _).mp hq
      | some p => exact own_to hown (fun _ y => (lift_granted_up htok).mp y) hq)
  resize s k n ra bs h1 h2 h3 h4 h5 :=
    FL.conseq (h.resize s k n ra bs h1 h2 ((hfits _ _).mpr h3) h4 h5)
      (fun _ hp => own_from hown (fun _ y => (granted_up htok).mpr y) hp)
      (fun v _ hq => by
        cases v with
        | false => exact own_to hown (fun _ y => (granted_up htok).mp y) hq
        | true => exact own_to hown (fun _ y => (lift_granted_up htok).mp y) hq)
  remap s k n ra bs h1 h2 h3 h4 h5 :=
    FL.conseq (h.remap s k n ra bs h1 h2 ((hfits _ _).mpr h3) h4 h5)
      (fun _ hp => own_from hown (fun _ y => (granted_up htok).mpr y) hp)
      (fun v _ hq => by
        cases v with
        | none => exact own_to hown (fun _ y => (granted_up htok).mp y) hq
        | some q => exact own_to hown (fun _ y => (lift_granted_up htok).mp y) hq)
  free s k ra bs h1 h2 h3 := FL.conseq (h.free s k ra bs h1 h2 h3)
    (fun _ hp => own_from hown (fun _ y => (granted_up htok).mpr y) hp)
    (fun _ _ hq => (hown _).mp hq)

/-- **A full-state allocator specification with legacy tokens is a legacy one** in the
full-state logic seen through the allocator state `O`. -/
theorem FAllocSpec.toLegacy {FL : FLogic} {vt : RawVTable} {ctx : Ptr}
    (h : FAllocSpec FL vt ctx J) (hJ : LegacyTokens J I O) : AllocSpec (FL.legacy O) vt ctx I :=
  h.toLegacy' hJ.tok hJ.own hJ.fits

end ToLegacy

end Full
end Zig
