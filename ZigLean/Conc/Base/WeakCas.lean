import ZigLean.Conc.WeakCas

namespace Zig
namespace Conc
namespace Proto

/-- Every weak choice selects a readable message, whether or not success is permitted. -/
theorem weakCasOpts_read {n li c pos : Nat} {m : Mem} {expected : BitVec n}
    {spurious : Bool}
    (h : (weakCasOpts m li expected (casOpts m li expected))[c]? = some (pos, spurious)) :
    ∃ j : Nat, (readOpts m li false)[j]? = some pos := by
  have hm := Array.mem_of_getElem? h
  simp only [weakCasOpts_eq, Array.mem_append, Array.mem_map] at hm
  rcases hm with ⟨p, hp, he⟩ | ⟨p, hp, he⟩
  · simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    unfold casOpts at hp
    exact Array.mem_iff_getElem?.mp (Array.mem_filter.mp hp).1
  · simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact Array.mem_iff_getElem?.mp (Array.mem_filter.mp hp).1

/-- A success-capable weak choice is one of the original strong choices. -/
theorem weakCasOpts_strong {n li c pos : Nat} {m : Mem} {expected : BitVec n}
    (h : (weakCasOpts m li expected (casOpts m li expected))[c]? = some (pos, false)) :
    ∃ j : Nat, (casOpts m li expected)[j]? = some pos := by
  have hm := Array.mem_of_getElem? h
  simp only [weakCasOpts_eq, Array.mem_append, Array.mem_map] at hm
  rcases hm with ⟨p, hp, he⟩ | ⟨p, hp, he⟩
  · simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, -⟩ := he
    exact Array.mem_iff_getElem?.mp hp
  · simp at he

theorem weakCasPrep_noErr {n align : Nat} {p : Ptr} {expected : BitVec n} {m : Mem}
    (hp : ∀ e, ((casPrep n align p expected).run m).run ≠ some (.error e)) (e : Error) :
    ((weakCasPrep n align p expected).run m).run ≠ some (.error e) := by
  intro h
  unfold weakCasPrep at h
  rcases MemM.bind_err h with he | ⟨⟨li, readable⟩, m₁, hprep, h₁⟩
  · have he' : casReadPrep n align p m = some (.error e) := he
    have hc : ((casPrep n align p expected).run m).run = some (.error e) := by
      simp [casPrep, zig_unfold, he', ExceptT.run]
    exact hp e hc
  rcases MemM.bind_err h₁ with he | ⟨a, m₂, hg, h₂⟩
  · exact MemM.get_err he
  exact MemM.pure_err h₂

theorem weakCasPrep_of {n align li : Nat} {p : Ptr} {expected : BitVec n} {m m₁ : Mem}
    {opts : Array Nat} (h : ((casPrep n align p expected).run m).run = some (.ok ((li, opts), m₁))) :
    ((weakCasPrep n align p expected).run m).run =
      some (.ok ((li, weakCasOpts m₁ li expected opts), m₁)) := by
  unfold casPrep at h
  obtain ⟨⟨li₁, readable⟩, m₂, hp, h₁⟩ := MemM.bind_ok h
  obtain ⟨b, blk, o, ha, hnr, hl, rfl⟩ := casReadPrep_ok hp
  obtain ⟨a, m₃, hg, h₂⟩ := MemM.bind_ok h₁
  obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
  obtain ⟨he, rfl⟩ := MemM.pure_ok h₂
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  change casReadPrep n align p m = some (.ok ((li, readOpts m₁ li false), m₁)) at hp
  simp [weakCasPrep, weakCasOpts, zig_unfold, hp, ExceptT.run]

theorem weakOptCount_eq {n align li : Nat} {p : Ptr} {expected : BitVec n} {succ : AtomicOrder}
    {m m₁ : Mem} {opts : Array (Nat × Bool)}
    (h : ((weakCasPrep n align p expected).run m).run = some (.ok ((li, opts), m₁))) :
    weakCasCount n succ align p expected m = opts.size := by
  unfold weakCasCount
  exact optCount_eq h

theorem cmpxchgWeakAs_ok {α : Type} {n : Nat} [Packed α n] {c : Nat} {succ fail : AtomicOrder}
    {align : Nat} {p : Ptr} {expected new : α} {r : Option α} {m m' : Mem}
    (h : ((cmpxchgWeakAs c succ fail align p expected new).run m).run = some (.ok (r, m'))) :
    (r = none ∧ ((cmpxchgWeakAt c succ fail align p (Packed.toBits expected) (Packed.toBits new)).run
      m).run = some (.ok (none, m'))) ∨
    ∃ b v, r = some v ∧ ((cmpxchgWeakAt c succ fail align p (Packed.toBits expected)
      (Packed.toBits new)).run m).run = some (.ok (some b, m')) ∧
      (Packed.ofBits? (α := α) b).run = some (.ok v) := by
  unfold cmpxchgWeakAs at h
  obtain ⟨o, m₁, ho, h₁⟩ := MemM.bind_ok h
  cases o with
  | none =>
    obtain ⟨rfl, rfl⟩ := MemM.pure_ok h₁
    exact .inl ⟨rfl, ho⟩
  | some b =>
    obtain ⟨v, h₂, rfl⟩ := MemM.map_ok h₁
    obtain ⟨hd, rfl⟩ := MemM.lift_ok h₂
    exact .inr ⟨b, v, rfl, ho, hd⟩


theorem cmpxchgWeakAt_noErr {n c : Nat} {succ fail : AtomicOrder} {align : Nat} {p : Ptr}
    {expected new : BitVec n} {m : Mem}
    (hprep : ∀ e, ((weakCasPrep n align p expected).run m).run ≠ some (.error e))
    (hpos : ∀ li opts m₁, ((weakCasPrep n align p expected).run m).run =
        some (.ok ((li, opts), m₁)) →
      ∃ pos spurious, opts[c]? = some (pos, spurious) ∧
        ∃ w, (intOfBytes n ((m₁.atomics[li]!).msgs[pos]!).bytes).run = some (.ok w))
    (hwrite : ∀ li opts m₁, ((weakCasPrep n align p expected).run m).run =
        some (.ok ((li, opts), m₁)) →
      ∀ e, ((casMarkWrite n align p).run m₁).run ≠ some (.error e))
    (e : Error) : ((cmpxchgWeakAt c succ fail align p expected new).run m).run ≠ some (.error e) := by
  intro h
  unfold cmpxchgWeakAt at h
  rcases MemM.bind_err h with he1 | ⟨⟨li, opts⟩, m₁, hp, h1⟩
  · exact hprep e he1
  obtain ⟨pos, spurious, hpos, w, hw⟩ := hpos li opts m₁ hp
  simp only [hpos] at h1
  rcases MemM.bind_err h1 with he2 | ⟨a₂, m₂, hg, h2⟩
  · exact MemM.get_err he2
  obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
  rcases MemM.bind_err h2 with he3 | ⟨old, m₃, hd, h3⟩
  · have := MemM.lift_err he3
    change ExceptT.run (intOfBytes n _) = _ at this
    rw [hw] at this; cases this
  obtain ⟨-, rfl⟩ := MemM.lift_ok hd
  split at h3
  · rcases MemM.bind_err h3 with he4 | ⟨_, m₄, hm, h4⟩
    · exact hwrite li opts _ hp e he4
    · rcases MemM.bind_err h4 with he5 | ⟨_, m₅, hr, h5⟩
      · exact rmwWrite_noErr e he5
      · exact MemM.pure_err h5
  · rcases MemM.bind_err h3 with he4 | ⟨_, m₄, ho, h4⟩
    · exact MemM.modify_err he4
    cases hq : fail.isAcq <;> simp only [hq, Bool.false_eq_true, ↓reduceIte] at h4
    · exact MemM.pure_err h4
    · rcases MemM.bind_err h4 with he5 | ⟨_, m₅, hc, h5⟩
      · exact MemM.modify_err he5
      · exact MemM.pure_err h5


theorem cmpxchgWeakAs_noErr {α : Type} {n : Nat} [Packed α n] {c : Nat} {succ fail : AtomicOrder}
    {align : Nat} {p : Ptr} {expected new : α} {m : Mem}
    (hcas : ∀ e, ((cmpxchgWeakAt c succ fail align p (Packed.toBits expected)
      (Packed.toBits new)).run m).run ≠ some (.error e))
    (hdec : ∀ b m', ((cmpxchgWeakAt c succ fail align p (Packed.toBits expected)
      (Packed.toBits new)).run m).run = some (.ok (some b, m')) →
      ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r))
    (e : Error) : ((cmpxchgWeakAs c succ fail align p expected new).run m).run ≠ some (.error e) := by
  intro h
  unfold cmpxchgWeakAs at h
  rcases MemM.bind_err h with he1 | ⟨o, m₁, ho, h1⟩
  · exact hcas e he1
  cases o with
  | none => exact MemM.pure_err h1
  | some b =>
    obtain ⟨r, hr⟩ := hdec b m₁ ho
    dsimp only at h1
    rw [map_eq_pure_bind] at h1
    rcases MemM.bind_err h1 with he2 | ⟨_, m₂, hl, h2⟩
    · have := MemM.lift_err he2; rw [hr] at this; cases this
    · exact MemM.pure_err h2

end Proto
end Conc
end Zig
