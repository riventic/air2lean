import ZigLean.Sep.Full.WordRules

open Zig Zig.Conc Zig.Conc.Proto Zig.Full Zig.Full.FAssn Zig.Full.FLock

namespace SepAuto.WordWidths

variable {γ Tgt : Type} {L : FLock γ} {K : FPrim γ} {P : Proto Tgt γ}
  {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}
  {t : ThreadId} {g : γ} {G : ThreadId → γ} {m : Mem} {n : Nat}

section Generic
variable {bits bytes : Nat} {W : Word bits bytes}

theorem load_keeps_rest {ord : AtomicOrder}
    (hP : L.Fits K P U ok) (hW : W.InRest U) (hap : W.ApartL L.toLockWord)
    (hgone : L.ph g ≠ .gone) (hi : P.inv (upd G t g) m) (hcost : P.cost = none) :
    P.WP t ((atomicLoadC (n := bits) ord bytes W.ptr : CM Tgt Unit (BitVec bits)).run ())
    (fun _ G' m' _ => W.Ok m' ∧ ∃ rY, L.Inv G' (rsum (W.cellsR m') rY) m') G m n := by
  apply wp_wordLoad hP hW hap hgone hi (hcost := hcost)
  intro k hk G₁ rY m₁ m' v j hg₁ hc₁ hU hY hj hv hfloor hacq hhist hw' hw ht hrun hframe hfresh hseen hInv
  exact ⟨hw', rY, hInv⟩

theorem loadAs_keeps_rest {α : Type} [Packed α bits] {ord : AtomicOrder}
    (hP : L.Fits K P U ok) (hW : W.InRest U) (hap : W.ApartL L.toLockWord)
    (hgone : L.ph g ≠ .gone) (hi : P.inv (upd G t g) m) (hcost : P.cost = none)
    (hdec : ∀ G₁ rY m₁, G₁ t = g → m₁.current = t →
      U G₁ (rsum (W.cellsR m₁) rY) m₁ → ∀ j < (W.hist m₁).size, ∀ b,
      (W.hist m₁)[j]!.Val b → ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r)) :
    P.WP t ((atomicLoadAsC α ord bytes W.ptr : CM Tgt Unit α).run ())
    (fun _ G' m' _ => W.Ok m' ∧ ∃ rY, L.Inv G' (rsum (W.cellsR m') rY) m') G m n := by
  apply wp_wordLoadAs hP hW hap hgone hi hdec (hcost := hcost)
  intro k hk G₁ rY m₁ m' b r j hg₁ hc₁ hU hY hd hj hv hfloor hacq hhist hw' hw ht hrun hframe hfresh hseen hInv
  exact ⟨hw', rY, hInv⟩

theorem rmw_keeps_rest {op : RmwOp} {signed : Bool} {ord : AtomicOrder} {v : BitVec bits}
    (hP : L.Fits K P U ok) (hW : W.InRest U) (hap : W.ApartL L.toLockWord)
    (hgone : L.ph g ≠ .gone) (hi : P.inv (upd G t g) m) (hcost : P.cost = none) :
    P.WP t ((atomicRmwC op signed ord bytes W.ptr v : CM Tgt Unit (BitVec bits)).run ())
    (fun r G' m' _ => W.Ok m' ∧ W.Holds m' (op.apply signed r.1 v) ∧
      ∃ rY, L.Inv G' (rsum (W.cellsR m') rY) m') G m n := by
  apply wp_wordRmw hP hW hap hgone hi (hcost := hcost)
  intro k hk G₁ rY m₁ m' old hg₁ hc₁ hU hY hv hH hhist hacq hw' hw ht hrun hframe hfresh hseen hInv
  exact ⟨hw', hH, rY, hInv⟩

theorem rmwAs_keeps_rest {α : Type} [Packed α bits] {op : RmwOp} {ord : AtomicOrder} {v : α}
    (hP : L.Fits K P U ok) (hW : W.InRest U) (hap : W.ApartL L.toLockWord)
    (hgone : L.ph g ≠ .gone) (hi : P.inv (upd G t g) m) (hcost : P.cost = none)
    (hdec : ∀ G₁ rY m₁, G₁ t = g → m₁.current = t →
      U G₁ (rsum (W.cellsR m₁) rY) m₁ → ∀ b,
      (W.hist m₁)[(W.hist m₁).size - 1]!.Val b →
      ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r)) :
    P.WP t ((atomicRmwAsC op ord bytes W.ptr v : CM Tgt Unit α).run ())
    (fun _ G' m' _ => W.Ok m' ∧ ∃ rY, L.Inv G' (rsum (W.cellsR m') rY) m') G m n := by
  apply wp_wordRmwAs hP hW hap hgone hi hdec (hcost := hcost)
  intro k hk G₁ rY m₁ m' old r hg₁ hc₁ hU hY hd hv hH hhist hacq hw' hw ht hrun hframe hfresh hseen hInv
  exact ⟨hw', rY, hInv⟩

theorem cas_keeps_rest {succ fail : AtomicOrder} {exp new : BitVec bits}
    (hP : L.Fits K P U ok) (hW : W.InRest U) (hap : W.ApartL L.toLockWord)
    (hgone : L.ph g ≠ .gone) (hi : P.inv (upd G t g) m) (hcost : P.cost = none) :
    P.WP t ((cmpxchgC (n := bits) succ fail bytes W.ptr exp new : CM Tgt Unit (Option (BitVec bits))).run ())
    (fun r G' m' _ => (r.1 = none → W.Holds m' new) ∧
      W.Ok m' ∧ ∃ rY, L.Inv G' (rsum (W.cellsR m') rY) m') G m n := by
  apply wp_wordCas hP hW hap hgone hi (hcost := hcost)
  intro k hk G₁ rY m₁ m' hg₁ hc₁ hU hY hw' hw ht hrun hframe hfresh hInv
  constructor
  · intro hv hH hhist hacq hseen
    exact ⟨fun _ => hH, hw', rY, hInv⟩
  · intro j b hne hj hv hfloor hacq hhist hseen
    exact ⟨by intro h; cases h, hw', rY, hInv⟩

theorem casAs_keeps_rest {α : Type} [Packed α bits] {succ fail : AtomicOrder} {exp new : α}
    (hP : L.Fits K P U ok) (hW : W.InRest U) (hap : W.ApartL L.toLockWord)
    (hgone : L.ph g ≠ .gone) (hi : P.inv (upd G t g) m) (hcost : P.cost = none)
    (hdec : ∀ G₁ rY m₁, G₁ t = g → m₁.current = t →
      U G₁ (rsum (W.cellsR m₁) rY) m₁ → ∀ j < (W.hist m₁).size, ∀ b,
      (W.hist m₁)[j]!.Val b → ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r)) :
    P.WP t ((cmpxchgAsC succ fail bytes W.ptr exp new : CM Tgt Unit (Option α)).run ())
    (fun r G' m' _ => (r.1 = none → W.Holds m' (Packed.toBits new)) ∧
      W.Ok m' ∧ ∃ rY, L.Inv G' (rsum (W.cellsR m') rY) m') G m n := by
  apply wp_wordCasAs hP hW hap hgone hi hdec (hcost := hcost)
  intro k hk G₁ rY m₁ m' hg₁ hc₁ hU hY hw' hw ht hrun hframe hfresh hInv
  constructor
  · intro hv hH hhist hacq hseen
    exact ⟨fun _ => hH, hw', rY, hInv⟩
  · intro j b r hne hd hj hv hfloor hacq hhist hseen
    exact ⟨by intro h; cases h, hw', rY, hInv⟩

theorem weakCas_keeps_rest {succ fail : AtomicOrder} {exp new : BitVec bits}
    (hP : L.Fits K P U ok) (hW : W.InRest U) (hap : W.ApartL L.toLockWord)
    (hgone : L.ph g ≠ .gone) (hi : P.inv (upd G t g) m) (hcost : P.cost = none) :
    P.WP t ((cmpxchgWeakC (n := bits) succ fail bytes W.ptr exp new : CM Tgt Unit (Option (BitVec bits))).run ())
    (fun r G' m' _ => (r.1 = none → W.Holds m' new) ∧
      W.Ok m' ∧ ∃ rY, L.Inv G' (rsum (W.cellsR m') rY) m') G m n := by
  apply wp_wordWeakCas hP hW hap hgone hi (hcost := hcost)
  intro k hk G₁ rY m₁ m' hg₁ hc₁ hU hY hw' hw ht hrun hframe hfresh hInv
  constructor
  · intro hv hH hhist hacq hseen
    exact ⟨fun _ => hH, hw', rY, hInv⟩
  · intro j b hj hv hfloor hacq hhist hseen
    exact ⟨by intro h; cases h, hw', rY, hInv⟩

theorem weakCasAs_keeps_rest {α : Type} [Packed α bits] {succ fail : AtomicOrder} {exp new : α}
    (hP : L.Fits K P U ok) (hW : W.InRest U) (hap : W.ApartL L.toLockWord)
    (hgone : L.ph g ≠ .gone) (hi : P.inv (upd G t g) m) (hcost : P.cost = none)
    (hdec : ∀ G₁ rY m₁, G₁ t = g → m₁.current = t →
      U G₁ (rsum (W.cellsR m₁) rY) m₁ → ∀ j < (W.hist m₁).size, ∀ b,
      (W.hist m₁)[j]!.Val b → ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r)) :
    P.WP t ((cmpxchgWeakAsC succ fail bytes W.ptr exp new : CM Tgt Unit (Option α)).run ())
    (fun r G' m' _ => (r.1 = none → W.Holds m' (Packed.toBits new)) ∧
      W.Ok m' ∧ ∃ rY, L.Inv G' (rsum (W.cellsR m') rY) m') G m n := by
  apply wp_wordWeakCasAs hP hW hap hgone hi hdec (hcost := hcost)
  intro k hk G₁ rY m₁ m' hg₁ hc₁ hU hY hw' hw ht hrun hframe hfresh hInv
  constructor
  · intro hv hH hhist hacq hseen
    exact ⟨fun _ => hH, hw', rY, hInv⟩
  · intro j b r hd hj hv hfloor hacq hhist hseen
    exact ⟨by intro h; cases h, hw', rY, hInv⟩

end Generic

section Width32
variable {W : Word 32 4}

theorem load32_keeps_rest {ord : AtomicOrder}
    (hP : L.Fits K P U ok) (hW : W.InRest U) (hap : W.ApartL L.toLockWord)
    (hgone : L.ph g ≠ .gone) (hi : P.inv (upd G t g) m) (hcost : P.cost = none) :
    P.WP t ((atomicLoadC (n := 32) ord 4 W.ptr : CM Tgt Unit (BitVec 32)).run ())
    (fun _ G' m' _ => W.Ok m' ∧ ∃ rY, L.Inv G' (rsum (W.cellsR m') rY) m') G m n := by
  exact load_keeps_rest hP hW hap hgone hi hcost

theorem loadAs32_keeps_rest {α : Type} [Packed α 32] {ord : AtomicOrder}
    (hP : L.Fits K P U ok) (hW : W.InRest U) (hap : W.ApartL L.toLockWord)
    (hgone : L.ph g ≠ .gone) (hi : P.inv (upd G t g) m) (hcost : P.cost = none)
    (hdec : ∀ G₁ rY m₁, G₁ t = g → m₁.current = t →
      U G₁ (rsum (W.cellsR m₁) rY) m₁ → ∀ j < (W.hist m₁).size, ∀ b,
      (W.hist m₁)[j]!.Val b → ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r)) :
    P.WP t ((atomicLoadAsC α ord 4 W.ptr : CM Tgt Unit α).run ())
    (fun _ G' m' _ => W.Ok m' ∧ ∃ rY, L.Inv G' (rsum (W.cellsR m') rY) m') G m n := by
  exact loadAs_keeps_rest hP hW hap hgone hi hcost hdec

theorem rmw32_keeps_rest {op : RmwOp} {signed : Bool} {ord : AtomicOrder} {v : BitVec 32}
    (hP : L.Fits K P U ok) (hW : W.InRest U) (hap : W.ApartL L.toLockWord)
    (hgone : L.ph g ≠ .gone) (hi : P.inv (upd G t g) m) (hcost : P.cost = none) :
    P.WP t ((atomicRmwC op signed ord 4 W.ptr v : CM Tgt Unit (BitVec 32)).run ())
    (fun r G' m' _ => W.Ok m' ∧ W.Holds m' (op.apply signed r.1 v) ∧
      ∃ rY, L.Inv G' (rsum (W.cellsR m') rY) m') G m n := by
  exact rmw_keeps_rest hP hW hap hgone hi hcost

theorem rmwAs32_keeps_rest {α : Type} [Packed α 32] {op : RmwOp} {ord : AtomicOrder} {v : α}
    (hP : L.Fits K P U ok) (hW : W.InRest U) (hap : W.ApartL L.toLockWord)
    (hgone : L.ph g ≠ .gone) (hi : P.inv (upd G t g) m) (hcost : P.cost = none)
    (hdec : ∀ G₁ rY m₁, G₁ t = g → m₁.current = t →
      U G₁ (rsum (W.cellsR m₁) rY) m₁ → ∀ b,
      (W.hist m₁)[(W.hist m₁).size - 1]!.Val b →
      ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r)) :
    P.WP t ((atomicRmwAsC op ord 4 W.ptr v : CM Tgt Unit α).run ())
    (fun _ G' m' _ => W.Ok m' ∧ ∃ rY, L.Inv G' (rsum (W.cellsR m') rY) m') G m n := by
  exact rmwAs_keeps_rest hP hW hap hgone hi hcost hdec

theorem cas32_keeps_rest {succ fail : AtomicOrder} {exp new : BitVec 32}
    (hP : L.Fits K P U ok) (hW : W.InRest U) (hap : W.ApartL L.toLockWord)
    (hgone : L.ph g ≠ .gone) (hi : P.inv (upd G t g) m) (hcost : P.cost = none) :
    P.WP t ((cmpxchgC (n := 32) succ fail 4 W.ptr exp new : CM Tgt Unit (Option (BitVec 32))).run ())
    (fun r G' m' _ => (r.1 = none → W.Holds m' new) ∧
      W.Ok m' ∧ ∃ rY, L.Inv G' (rsum (W.cellsR m') rY) m') G m n := by
  exact cas_keeps_rest hP hW hap hgone hi hcost

theorem casAs32_keeps_rest {α : Type} [Packed α 32] {succ fail : AtomicOrder} {exp new : α}
    (hP : L.Fits K P U ok) (hW : W.InRest U) (hap : W.ApartL L.toLockWord)
    (hgone : L.ph g ≠ .gone) (hi : P.inv (upd G t g) m) (hcost : P.cost = none)
    (hdec : ∀ G₁ rY m₁, G₁ t = g → m₁.current = t →
      U G₁ (rsum (W.cellsR m₁) rY) m₁ → ∀ j < (W.hist m₁).size, ∀ b,
      (W.hist m₁)[j]!.Val b → ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r)) :
    P.WP t ((cmpxchgAsC succ fail 4 W.ptr exp new : CM Tgt Unit (Option α)).run ())
    (fun r G' m' _ => (r.1 = none → W.Holds m' (Packed.toBits new)) ∧
      W.Ok m' ∧ ∃ rY, L.Inv G' (rsum (W.cellsR m') rY) m') G m n := by
  exact casAs_keeps_rest hP hW hap hgone hi hcost hdec

theorem weakCas32_keeps_rest {succ fail : AtomicOrder} {exp new : BitVec 32}
    (hP : L.Fits K P U ok) (hW : W.InRest U) (hap : W.ApartL L.toLockWord)
    (hgone : L.ph g ≠ .gone) (hi : P.inv (upd G t g) m) (hcost : P.cost = none) :
    P.WP t ((cmpxchgWeakC (n := 32) succ fail 4 W.ptr exp new : CM Tgt Unit (Option (BitVec 32))).run ())
    (fun r G' m' _ => (r.1 = none → W.Holds m' new) ∧
      W.Ok m' ∧ ∃ rY, L.Inv G' (rsum (W.cellsR m') rY) m') G m n := by
  exact weakCas_keeps_rest hP hW hap hgone hi hcost

theorem weakCasAs32_keeps_rest {α : Type} [Packed α 32] {succ fail : AtomicOrder} {exp new : α}
    (hP : L.Fits K P U ok) (hW : W.InRest U) (hap : W.ApartL L.toLockWord)
    (hgone : L.ph g ≠ .gone) (hi : P.inv (upd G t g) m) (hcost : P.cost = none)
    (hdec : ∀ G₁ rY m₁, G₁ t = g → m₁.current = t →
      U G₁ (rsum (W.cellsR m₁) rY) m₁ → ∀ j < (W.hist m₁).size, ∀ b,
      (W.hist m₁)[j]!.Val b → ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r)) :
    P.WP t ((cmpxchgWeakAsC succ fail 4 W.ptr exp new : CM Tgt Unit (Option α)).run ())
    (fun r G' m' _ => (r.1 = none → W.Holds m' (Packed.toBits new)) ∧
      W.Ok m' ∧ ∃ rY, L.Inv G' (rsum (W.cellsR m') rY) m') G m n := by
  exact weakCasAs_keeps_rest hP hW hap hgone hi hcost hdec

end Width32

section Width64
variable {W : Word 64 8}

theorem load64_keeps_rest {ord : AtomicOrder}
    (hP : L.Fits K P U ok) (hW : W.InRest U) (hap : W.ApartL L.toLockWord)
    (hgone : L.ph g ≠ .gone) (hi : P.inv (upd G t g) m) (hcost : P.cost = none) :
    P.WP t ((atomicLoadC (n := 64) ord 8 W.ptr : CM Tgt Unit (BitVec 64)).run ())
    (fun _ G' m' _ => W.Ok m' ∧ ∃ rY, L.Inv G' (rsum (W.cellsR m') rY) m') G m n := by
  exact load_keeps_rest hP hW hap hgone hi hcost

theorem loadAs64_keeps_rest {α : Type} [Packed α 64] {ord : AtomicOrder}
    (hP : L.Fits K P U ok) (hW : W.InRest U) (hap : W.ApartL L.toLockWord)
    (hgone : L.ph g ≠ .gone) (hi : P.inv (upd G t g) m) (hcost : P.cost = none)
    (hdec : ∀ G₁ rY m₁, G₁ t = g → m₁.current = t →
      U G₁ (rsum (W.cellsR m₁) rY) m₁ → ∀ j < (W.hist m₁).size, ∀ b,
      (W.hist m₁)[j]!.Val b → ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r)) :
    P.WP t ((atomicLoadAsC α ord 8 W.ptr : CM Tgt Unit α).run ())
    (fun _ G' m' _ => W.Ok m' ∧ ∃ rY, L.Inv G' (rsum (W.cellsR m') rY) m') G m n := by
  exact loadAs_keeps_rest hP hW hap hgone hi hcost hdec

theorem rmw64_keeps_rest {op : RmwOp} {signed : Bool} {ord : AtomicOrder} {v : BitVec 64}
    (hP : L.Fits K P U ok) (hW : W.InRest U) (hap : W.ApartL L.toLockWord)
    (hgone : L.ph g ≠ .gone) (hi : P.inv (upd G t g) m) (hcost : P.cost = none) :
    P.WP t ((atomicRmwC op signed ord 8 W.ptr v : CM Tgt Unit (BitVec 64)).run ())
    (fun r G' m' _ => W.Ok m' ∧ W.Holds m' (op.apply signed r.1 v) ∧
      ∃ rY, L.Inv G' (rsum (W.cellsR m') rY) m') G m n := by
  exact rmw_keeps_rest hP hW hap hgone hi hcost

theorem rmwAs64_keeps_rest {α : Type} [Packed α 64] {op : RmwOp} {ord : AtomicOrder} {v : α}
    (hP : L.Fits K P U ok) (hW : W.InRest U) (hap : W.ApartL L.toLockWord)
    (hgone : L.ph g ≠ .gone) (hi : P.inv (upd G t g) m) (hcost : P.cost = none)
    (hdec : ∀ G₁ rY m₁, G₁ t = g → m₁.current = t →
      U G₁ (rsum (W.cellsR m₁) rY) m₁ → ∀ b,
      (W.hist m₁)[(W.hist m₁).size - 1]!.Val b →
      ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r)) :
    P.WP t ((atomicRmwAsC op ord 8 W.ptr v : CM Tgt Unit α).run ())
    (fun _ G' m' _ => W.Ok m' ∧ ∃ rY, L.Inv G' (rsum (W.cellsR m') rY) m') G m n := by
  exact rmwAs_keeps_rest hP hW hap hgone hi hcost hdec

theorem cas64_keeps_rest {succ fail : AtomicOrder} {exp new : BitVec 64}
    (hP : L.Fits K P U ok) (hW : W.InRest U) (hap : W.ApartL L.toLockWord)
    (hgone : L.ph g ≠ .gone) (hi : P.inv (upd G t g) m) (hcost : P.cost = none) :
    P.WP t ((cmpxchgC (n := 64) succ fail 8 W.ptr exp new : CM Tgt Unit (Option (BitVec 64))).run ())
    (fun r G' m' _ => (r.1 = none → W.Holds m' new) ∧
      W.Ok m' ∧ ∃ rY, L.Inv G' (rsum (W.cellsR m') rY) m') G m n := by
  exact cas_keeps_rest hP hW hap hgone hi hcost

theorem casAs64_keeps_rest {α : Type} [Packed α 64] {succ fail : AtomicOrder} {exp new : α}
    (hP : L.Fits K P U ok) (hW : W.InRest U) (hap : W.ApartL L.toLockWord)
    (hgone : L.ph g ≠ .gone) (hi : P.inv (upd G t g) m) (hcost : P.cost = none)
    (hdec : ∀ G₁ rY m₁, G₁ t = g → m₁.current = t →
      U G₁ (rsum (W.cellsR m₁) rY) m₁ → ∀ j < (W.hist m₁).size, ∀ b,
      (W.hist m₁)[j]!.Val b → ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r)) :
    P.WP t ((cmpxchgAsC succ fail 8 W.ptr exp new : CM Tgt Unit (Option α)).run ())
    (fun r G' m' _ => (r.1 = none → W.Holds m' (Packed.toBits new)) ∧
      W.Ok m' ∧ ∃ rY, L.Inv G' (rsum (W.cellsR m') rY) m') G m n := by
  exact casAs_keeps_rest hP hW hap hgone hi hcost hdec

theorem weakCas64_keeps_rest {succ fail : AtomicOrder} {exp new : BitVec 64}
    (hP : L.Fits K P U ok) (hW : W.InRest U) (hap : W.ApartL L.toLockWord)
    (hgone : L.ph g ≠ .gone) (hi : P.inv (upd G t g) m) (hcost : P.cost = none) :
    P.WP t ((cmpxchgWeakC (n := 64) succ fail 8 W.ptr exp new : CM Tgt Unit (Option (BitVec 64))).run ())
    (fun r G' m' _ => (r.1 = none → W.Holds m' new) ∧
      W.Ok m' ∧ ∃ rY, L.Inv G' (rsum (W.cellsR m') rY) m') G m n := by
  exact weakCas_keeps_rest hP hW hap hgone hi hcost

theorem weakCasAs64_keeps_rest {α : Type} [Packed α 64] {succ fail : AtomicOrder} {exp new : α}
    (hP : L.Fits K P U ok) (hW : W.InRest U) (hap : W.ApartL L.toLockWord)
    (hgone : L.ph g ≠ .gone) (hi : P.inv (upd G t g) m) (hcost : P.cost = none)
    (hdec : ∀ G₁ rY m₁, G₁ t = g → m₁.current = t →
      U G₁ (rsum (W.cellsR m₁) rY) m₁ → ∀ j < (W.hist m₁).size, ∀ b,
      (W.hist m₁)[j]!.Val b → ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r)) :
    P.WP t ((cmpxchgWeakAsC succ fail 8 W.ptr exp new : CM Tgt Unit (Option α)).run ())
    (fun r G' m' _ => (r.1 = none → W.Holds m' (Packed.toBits new)) ∧
      W.Ok m' ∧ ∃ rY, L.Inv G' (rsum (W.cellsR m') rY) m') G m n := by
  exact weakCasAs_keeps_rest hP hW hap hgone hi hcost hdec

end Width64

/-- Descriptor rejection, not a claim that raw 16-bit atomic operations are illegal. -/
theorem unsupported_descriptor : ¬ Nonempty (Word 16 2) := by
  rintro ⟨W⟩
  rcases W.n_ok with ⟨h, _⟩ | ⟨h, _⟩ <;> omega

theorem wrong_byte_count : ¬ Nonempty (Word 64 4) := by
  rintro ⟨W⟩
  rcases W.n_ok with ⟨h, _⟩ | ⟨_, h⟩ <;> omega

/-- A 64-bit word four bytes from an eight-byte-aligned block cannot satisfy native Ok. -/
theorem misaligned64_not_ok {m : Mem} {blk : Block}
    (hb : m.blocks[0]? = some blk) (ha : blk.addr = 4096) :
    ¬ ({ b := 0, o := 4 } : Word 64 8).Ok m := by
  intro hw
  obtain ⟨blk', hb', _, _, halign, _⟩ := hw.blk
  have he : blk = blk' := Option.some.inj (hb.symm.trans hb')
  subst blk'
  have hbad : (4096 + 4) % 8 ≠ (0 : Nat) := by decide
  exact hbad (by simpa only [ha] using halign)

end SepAuto.WordWidths
