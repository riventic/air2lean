import ZigLean.Conc.Lemmas
import ZigLean.Mem.AtomicPtr

/-!
# Rules for pointer atomics

The `*_ok` and `*_noErr` lemmas of `ZigLean/Conc/Lemmas.lean` for the pointer load and store of
`ZigLean/Mem/AtomicPtr.lean`: the same preparation, the same options and clocks, and a message
that holds the pointer's own bytes (`Enc.encode`), so a load decodes the pointer that a store
wrote, with its block (`atomicLoadPtrAt_ok`, `storePtrMsg`).
-/

namespace Zig
namespace Conc
namespace Proto

variable {α : Type} [Enc α]

/-- The message that a pointer store of `v` writes (`atomicStorePtrAt`). -/
def storePtrMsg (m : Mem) (ord : AtomicOrder) (v : α) : Msg :=
  let cl := m.clocks[m.current]!
  { id := m.nextMsg, bytes := Enc.encode v, clock := cl, relClock := if ord.isRel then cl else #[] }

/-- `atomicStorePtrAt` at place `slot` of location `li` on `m` (after `storePrep`). -/
def storePtrM (m : Mem) (li slot : Nat) (ord : AtomicOrder) (v : α) : Mem :=
  observeM (insertM m li slot (storePtrMsg m ord v)) li m.nextMsg

/-- A pointer store that took place `slot` of location `li`. -/
theorem atomicStorePtrAt_ok {c : Nat} {ord : AtomicOrder} {align : Nat} {p : Ptr} {v : α}
    {m m' : Mem} {x : Unit}
    (h : ((atomicStorePtrAt c ord align p v).run m).run = some (.ok (x, m'))) :
    ∃ b blk o li m₁ slot, m.accessW p (intSize 64) align = pure (b, blk, o) ∧
      NoRace m b o (intSize 64) .atomicWrite ∧
      ((locIdx b o (intSize 64)).run (m.recordAt b o (intSize 64) .atomicWrite)).run =
        some (.ok (li, m₁)) ∧
      (writeSlots m₁ li)[c]? = some slot ∧ m' = storePtrM m₁ li slot ord v := by
  unfold atomicStorePtrAt at h
  obtain ⟨⟨li, slots⟩, m₁, hp, h₁⟩ := MemM.bind_ok h
  obtain ⟨b, blk, o, ha, hnr, hl, rfl⟩ := storePrep_ok hp
  refine ⟨b, blk, o, li, m₁, ?_⟩
  dsimp only at h₁
  split at h₁
  · rename_i slot hslot
    refine ⟨slot, ha, hnr, hl, hslot, ?_⟩
    obtain ⟨a₂, m₂, hg, h₂⟩ := MemM.bind_ok h₁
    obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
    obtain ⟨_, m₃, hi, h₃⟩ := MemM.bind_ok h₂
    have := modify_ok hi
    subst this
    exact modify_ok h₃
  · exact (MemM.throw_ok h₁).elim

theorem atomicStorePtrAt_noErr {c : Nat} {ord : AtomicOrder} {align : Nat} {p : Ptr} {v : α}
    {m : Mem} (hprep : ∀ e, ((storePrep 64 ord align p).run m).run ≠ some (.error e))
    (hslot : ∀ li slots m₁, ((storePrep 64 ord align p).run m).run = some (.ok ((li, slots), m₁)) →
      c < slots.size)
    (e : Error) : ((atomicStorePtrAt c ord align p v).run m).run ≠ some (.error e) := by
  intro h
  unfold atomicStorePtrAt at h
  rcases MemM.bind_err h with he1 | ⟨⟨li, slots⟩, m₁, hp, h1⟩
  · exact hprep e he1
  have hc := hslot li slots m₁ hp
  dsimp only at h1
  rw [Array.getElem?_eq_getElem hc] at h1
  rcases MemM.bind_err h1 with he2 | ⟨a₂, m₂, hg, h2⟩
  · exact MemM.get_err he2
  obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
  rcases MemM.bind_err h2 with he3 | ⟨_, m₃, hi, h3⟩
  · exact MemM.modify_err he3
  · exact MemM.modify_err h3

/-- A pointer load that read message `pos` of location `li`: the pointer that the message's
bytes encode. -/
theorem atomicLoadPtrAt_ok {c : Nat} {ord : AtomicOrder} {align : Nat} {p : Ptr} {v : α}
    {m m' : Mem} (h : ((atomicLoadPtrAt α c ord align p).run m).run = some (.ok (v, m'))) :
    ∃ b blk o li m₁ pos, m.access p (intSize 64) align = pure (b, blk, o) ∧
      NoRace m b o (intSize 64) .atomicRead ∧
      ((locIdx b o (intSize 64)).run (m.recordAt b o (intSize 64) .atomicRead)).run =
        some (.ok (li, m₁)) ∧
      (readOpts m₁ li false)[c]? = some pos ∧
      (Enc.decode ((m₁.atomics[li]!).msgs[pos]!).bytes : Result α).run = some (.ok v) ∧
      m' = loadM m₁ li ord ((m₁.atomics[li]!).msgs[pos]!) := by
  unfold atomicLoadPtrAt at h
  obtain ⟨⟨li, opts⟩, m₁, hp, h₁⟩ := MemM.bind_ok h
  obtain ⟨b, blk, o, ha, hnr, hl, rfl⟩ := loadPrep_ok hp
  simp only [Bool.false_eq_true, ↓reduceIte] at ha hnr hl
  refine ⟨b, blk, o, li, m₁, ?_⟩
  dsimp only at h₁
  split at h₁
  · rename_i pos hpos
    refine ⟨pos, ha, hnr, hl, hpos, ?_⟩
    obtain ⟨a₂, m₂, hg, h₂⟩ := MemM.bind_ok h₁
    obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
    obtain ⟨_, m₃, ho, h₃⟩ := MemM.bind_ok h₂
    have := modify_ok ho
    subst this
    unfold loadM
    cases hq : ord.isAcq <;> simp only [hq, Bool.false_eq_true, ↓reduceIte] at h₃ ⊢
    · obtain ⟨hd, rfl⟩ := MemM.lift_ok h₃
      exact ⟨hd, rfl⟩
    · obtain ⟨_, m₄, hc, h₄⟩ := MemM.bind_ok h₃
      have := modify_ok hc
      subst this
      obtain ⟨hd, rfl⟩ := MemM.lift_ok h₄
      exact ⟨hd, rfl⟩
  · exact (MemM.throw_ok h₁).elim

theorem atomicLoadPtrAt_noErr {c : Nat} {ord : AtomicOrder} {align : Nat} {p : Ptr} {m : Mem}
    (hprep : ∀ e, ((loadPrep 64 ord align p false).run m).run ≠ some (.error e))
    (hpos : ∀ li opts m₁, ((loadPrep 64 ord align p false).run m).run =
        some (.ok ((li, opts), m₁)) →
      ∃ pos, opts[c]? = some pos ∧
        ∃ w : α, (Enc.decode ((m₁.atomics[li]!).msgs[pos]!).bytes : Result α).run = some (.ok w))
    (e : Error) : ((atomicLoadPtrAt α c ord align p).run m).run ≠ some (.error e) := by
  intro h
  unfold atomicLoadPtrAt at h
  rcases MemM.bind_err h with he1 | ⟨⟨li, opts⟩, m₁, hp, h1⟩
  · exact hprep e he1
  obtain ⟨pos, hpos, w, hw⟩ := hpos li opts m₁ hp
  simp only [hpos] at h1
  rcases MemM.bind_err h1 with he2 | ⟨a₂, m₂, hg, h2⟩
  · exact MemM.get_err he2
  obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
  rcases MemM.bind_err h2 with he3 | ⟨_, m₃, ho, h3⟩
  · exact MemM.modify_err he3
  have := modify_ok ho; subst this
  have hw' : (Enc.decode ((m₂.atomics[li]!).msgs[pos]!).bytes : Result α).run = some (.ok w) := hw
  cases hq : ord.isAcq <;> simp only [hq, Bool.false_eq_true, ↓reduceIte] at h3
  · have := MemM.lift_err h3
    rw [hw'] at this; cases this
  · rcases MemM.bind_err h3 with he4 | ⟨_, m₄, hc, h4⟩
    · exact MemM.modify_err he4
    have := modify_ok hc; subst this
    have := MemM.lift_err h4
    rw [hw'] at this; cases this

end Proto
end Conc
end Zig
