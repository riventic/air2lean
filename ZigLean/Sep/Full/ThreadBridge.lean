import ZigLean.Sep.Full.Thread
import ZigLean.Sep.Full.Tame
import ZigLean.Conc.Own

/-!
# The transitional bridge from legacy thread triples (`docs/sep-threads.md` §Transitional bridge)

A legacy thread triple (`TTriple`, `ZigLean/Conc/Own.lean`) of a `Tame` program lifts to a
full-state thread triple (`FTTriple`, `ZigLean/Sep/Full/Thread.lean`) with the side conditions of
`FTriple.ofTriple` (`FTTriple.ofTTriple`, `ofTTriple_up`). The step is read from `m.noFp` as a
sequential program (`soloAt`), so the legacy bridge does the full-state part, and the legacy
thread triple on the exact cells gives ownership and `StepIn`.

The primitive rules of a thread (`FTTriple.alloc'`, `free'`, `storeAt`, `loadAt`, `ptrProjectAt`)
are lifted here until their native versions exist; a block's bytes come with its full extent
(`bext`), which pins its size and kind. This module is the only full-state module that imports the
legacy layer; it goes when the native rules replace it.
-/

namespace Zig
namespace Full

open FAssn Conc

open Classical in
/-- The run of `c` in `m`, as a program of `m.noFp` (with the final memory's accesses forgotten);
no result in any other memory. -/
noncomputable def soloAt {α : Type} (c : MemM α) (m : Mem) : MemM α := fun m₀ =>
  ExceptT.mk (if m₀ = m.noFp then (c.run m).run.map (Except.map fun p => (p.1, p.2.noFp)) else none)

section SoloAt

variable {α : Type} {c : MemM α} {m : Mem}

theorem soloAt_run_self :
    ((soloAt c m).run m.noFp).run = (c.run m).run.map (Except.map fun p => (p.1, p.2.noFp)) := by
  simp [soloAt, StateT.run, ExceptT.run, ExceptT.mk]

theorem soloAt_run_ne {m₀ : Mem} (h : m₀ ≠ m.noFp) : ((soloAt c m).run m₀).run = none := by
  simp [soloAt, StateT.run, ExceptT.run, ExceptT.mk, h]

/-- A successful run of `soloAt c m` is a run of `c` from `m`. -/
theorem soloAt_ok {m₀ m₁ : Mem} {v : α} (h : ((soloAt c m).run m₀).run = some (.ok (v, m₁))) :
    m₀ = m.noFp ∧ ∃ m', (c.run m).run = some (.ok (v, m')) ∧ m₁ = m'.noFp := by
  by_cases e : m₀ = m.noFp
  · subst e
    rw [soloAt_run_self] at h
    refine ⟨rfl, ?_⟩
    cases hr : (c.run m).run with
    | none => rw [hr] at h; cases h
    | some x =>
      rw [hr] at h
      cases x with
      | error => cases h
      | ok p =>
        simp only [Option.map_some, Except.map, Option.some.injEq, Except.ok.injEq] at h
        obtain ⟨v', m'⟩ := p
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        exact ⟨m', rfl, rfl⟩
  · rw [soloAt_run_ne e] at h; cases h

theorem Tame.soloAt (hc : Tame c) (m : Mem) : Tame (soloAt c m) := fun m₀ v m₁ h => by
  obtain ⟨rfl, m', hr, rfl⟩ := soloAt_ok h
  exact hc m v m' hr

theorem Keeps.soloAt {D : BlockId → Prop} (hc : Keeps D c) (m : Mem) : Keeps D (soloAt c m) :=
  fun m₀ v m₁ h => by
    obtain ⟨rfl, m', hr, rfl⟩ := soloAt_ok h
    exact hc m v m' hr

/-- A legacy thread triple of `c` gives a legacy triple of `soloAt c m` for the heaps that the
current thread of `m` owns. -/
theorem soloAt_triple {P : Assn} {Q : α → Assn} (ht : TTriple P c Q)
    (hc : m.current < m.clocks.size) :
    Triple (fun h => P h ∧ m.Owns m.current h) (soloAt c m) Q := by
  intro m₀ hP hF hd hm ⟨hp, ho⟩ _
  by_cases e : m₀ = m.noFp
  · subst e
    rw [soloAt_run_self]
    have := ht m hP hF hd hm hp hc ho
    revert this
    cases (c.run m).run with
    | none => intro; trivial
    | some x =>
      cases x with
      | error e => intro h; exact h
      | ok p =>
        obtain ⟨v, m'⟩ := p
        rintro ⟨hQ, hdQ, hmQ, hq, -, hst⟩
        have hc' : m'.current < m'.clocks.size := by rw [hst.current, hst.size]; exact hc
        exact ⟨hQ, hdQ, hmQ, hq, ⟨singleThread_empty rfl hc'⟩⟩
  · rw [soloAt_run_ne e]; trivial

end SoloAt

theorem SizeFree.owns {E : BlockId → Option (Nat × BlockKind)} {P : Assn} (hsf : SizeFree E P)
    (m : Mem) (t : ThreadId) : SizeFree E (fun h => P h ∧ m.Owns t h) :=
  fun h h' ⟨hp, ho⟩ hn h2 h3 => ⟨hsf h h' hp hn h2 h3, ho.sub fun l hl => by
    have := hn l
    cases e : h l <;> cases e' : h' l <;> simp_all⟩

namespace FTTriple

variable {α : Type} {P : Assn} {c : MemM α} {Q : α → Assn} {Pf : FAssn} {Qf : α → FAssn}

/-- **The bridge's core**: a legacy thread triple of `c` (for the precondition's exact cells) and,
in every memory, a full-state sequential triple of `soloAt c m` from the resources the thread owns,
give a thread triple. -/
theorem ofNoFp (ht : TTriple P c Q) (hP : ∀ m r rF, Holds m r rF → Pf r → P (r.fix m).heap.erase)
    (hF : ∀ m, m.current < m.clocks.size →
      FTriple (fun r => Pf r ∧ m.Owns m.current r.heap.erase) (soloAt c m) Qf) :
    FTTriple Pf c Qf := by
  intro m r rF hh hp hc ho
  have hs := hF m hc.1 m.noFp r rF hh.toNoFp ⟨hp, ho⟩ hc.noFp
  rw [soloAt_run_self] at hs
  have hFs : ∀ l, (rF.fix m).heap.erase l ≠ none → rF.heap.erase l ≠ none :=
    fun l h => FHeap.erase_fix_ne.mp h
  have hT := ht m _ _ (FHeap.erase_disjoint (FHeap.fix_disjoint hh.disj))
    (hh.fix.heap_exact hh.fix_exact hh.fix_exactF) (hP m r rF hh hp) hc.1
    (ho.sub fun l h => FHeap.erase_fix_ne.mp h)
  revert hs hT
  cases (c.run m).run with
  | none => intros; trivial
  | some x =>
    cases x with
    | error e => intro _ hT; exact hT
    | ok p =>
      obtain ⟨v, m'⟩ := p
      rintro ⟨r', hh', hq, hs'⟩ ⟨hQ, -, hmQ, -, hoQ, hst⟩
      refine ⟨r', hh'.ofNoFp, hq, ⟨by rw [hst.current, hst.size]; exact hc.1, hs'.2⟩, ?_,
        hst.weaken fun l h => FHeap.erase_fix_ne.mpr h⟩
      exact hoQ.sub (hh'.ofNoFp.erase_sub hmQ fun l h => by simpa [FHeap.erase] using hFs l h)

/-- **Lifting a legacy thread triple** with the side conditions of `FTriple.ofTriple`. -/
theorem ofTTriple {E : BlockId → Option (Nat × BlockKind)} {B : BlockId → Prop}
    (ht : TTriple P c Q) (hc : Tame c)
    (hB : ∀ h, P h → ∀ l c, h l = some c → B l.1)
    (hpin : ∀ h, P h → ∀ l c S K, h l = some c → E l.1 = some (S, K) → c.size = S ∧ c.kind = K)
    (hsf : SizeFree E P)
    (hk : (∀ b, B b → (E b).isSome) ∨ Keeps (fun b => (E b).isSome) c) :
    FTTriple (upE P E) c (fun v => upPost (Q v) B E) :=
  ofNoFp ht (fun _ _ _ hh hp => upE_fix hsf hpin hh hp) fun m hm =>
    (FTriple.ofTriple (soloAt_triple ht hm) (hc.soloAt m) (fun h hp => hB h hp.1)
      (fun h hp => hpin h hp.1) (hsf.owns m m.current) (hk.imp id (·.soloAt m))).pre
      fun _ ⟨hp, ho⟩ => ⟨⟨hp.1, ho⟩, hp.2⟩

/-- **Lifting a size-free legacy thread triple** of a program that keeps every live block. -/
theorem ofTTriple_up (ht : TTriple P c Q) (hc : Tame c) (hsf : SizeFree (fun _ => none) P)
    (hk : Keeps (fun _ => False) c) : FTTriple (up P) c (fun v => up (Q v)) :=
  ofNoFp ht (fun _ _ _ hh hp => upE_fix hsf (fun _ _ _ _ _ _ _ h => by cases h) hh (upE_none.mpr hp))
    fun m hm => (FTriple.ofTriple_up (soloAt_triple ht hm) (hc.soloAt m) (hsf.owns m m.current)
      (hk.soloAt m)).pre fun _ ⟨⟨hp, hk, hg⟩, ho⟩ => ⟨⟨hp, ho⟩, hk, hg⟩

end FTTriple

/-! ## Primitive rules of a thread

The rules of `FTriple.alloc'` and `FTriple.free'` (`Full/Toy.lean`) for a thread, lifted from the
legacy thread triples (`TTriple.alloc`, `TTriple.free`, `TTriple.storeAt`, `TTriple.loadAt`,
`TTriple.ptrProjectAt`) by the bridge; a block's bytes come with its full extent (`bext`), which
pins its size and kind. -/

namespace FTTriple

/-- `alloc` of `size > 0` bytes in a thread: the bytes and the new block's full extent. -/
theorem alloc' (kind : BlockKind) (size align : Nat) (ha : 0 < align) (hpos : 0 < size)
    (hk : kind.mappedLo = 0 := by first | rfl | simp_all [BlockKind.mappedLo]) :
    FTTriple emp (alloc kind size align) (fun p => FAssn.ex fun A : Nat => FAssn.ex fun b : BlockId =>
      ⟪p.block = some b ∧ p.off = 0 ∧ A % align = 0⟫ ⋆
        (up (bytesAt p A size kind (Array.replicate size .undef)) ⋆ bext b size kind)) := by
  refine FTTriple.drop (K := fun _ r => r.heap = FHeap.empty ∧ r.know = Know.none) ?_ (fun _ _ h => h.1)
  refine ((FTTriple.ofTTriple (E := fun _ => none) (B := fun _ => False)
    (TTriple.alloc kind size align ha hk) (Tame.alloc kind size align)
    (fun h hp l c hl => by rw [hp] at hl; cases hl) (fun _ _ _ _ _ _ _ h => by cases h)
    (SizeFree.of_pinned fun h hp l c hl => by rw [hp] at hl; cases hl) (.inl fun _ h => h.elim)).pre
    fun _ h => upE_none.mpr (up_emp.mpr h)).post fun p r h => ?_
  obtain ⟨E', ⟨hq, hk', hg⟩, hcov⟩ := id h
  obtain ⟨A, hq⟩ := hq
  obtain ⟨⟨h0, hA⟩, hb⟩ := Zig.sep_lift.mp hq
  obtain ⟨b, hpb, -, hl⟩ := id hb
  have hc := hl (b, p.off.toNat)
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨rfl, Nat.le_refl _, by simp; omega⟩)] at hc
  simp only [FHeap.erase, Option.map_eq_some_iff] at hc
  obtain ⟨fc, hfc, he⟩ := hc
  have hx := upPost_bext (b := b) (S := size) (K := kind) h ⟨_, fc, hfc, by rw [he], by rw [he], fun h => h.elim⟩
  obtain ⟨r₁, r₂, hd, rfl, ⟨r₃, r₄, hd', e, x, hbx⟩, h2⟩ := hx
  obtain ⟨A', x⟩ := up_ex.mp x
  obtain ⟨⟨h0', hA'⟩, x⟩ := up_lift.mp x
  exact ⟨_, r₂, hd, rfl, ⟨A', b, sep_lift.mpr ⟨⟨hpb, h0', hA'⟩, ⟨r₃, r₄, hd', e, x, hbx⟩⟩⟩, h2⟩

theorem bytesAt_cells {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte} {b : BlockId}
    (hpb : p.block = some b) :
    ∀ h, bytesAt p A S K bs h → ∀ l c, h l = some c → l.1 = b ∧ c.size = S ∧ c.kind = K := by
  intro h hb l c hc
  obtain ⟨b', hb', -, hl⟩ := hb
  rw [hpb] at hb'; cases hb'
  rw [hl l] at hc
  split at hc
  · rename_i hin; cases hc; exact ⟨hin.1, rfl, rfl⟩
  · cases hc

/-- A non-empty `bytesAt` of block `b` has a cell of `b` with the block's size and kind. -/
theorem bytesAt_cell {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte} {b : BlockId}
    (hpb : p.block = some b) (hpos : 0 < bs.size) {h : FHeap} (hb : bytesAt p A S K bs h.erase) :
    ∃ x fc, h (b, x) = some fc ∧ fc.cell.size = S ∧ fc.cell.kind = K := by
  obtain ⟨b', hb', -, hl⟩ := hb
  rw [hpb] at hb'; cases hb'
  have hc := hl (b, p.off.toNat)
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨rfl, Nat.le_refl _, by omega⟩)] at hc
  simp only [FHeap.erase, Option.map_eq_some_iff] at hc
  obtain ⟨fc, hfc, he⟩ := hc
  exact ⟨_, fc, hfc, by rw [he], by rw [he]⟩

/-- The extent map that pins block `b` to size `S` and kind `K`. -/
abbrev pin (b : BlockId) (S : Nat) (K : BlockKind) : BlockId → Option (Nat × BlockKind) :=
  fun x => if x = b then some (S, K) else none

/-- **A legacy thread rule on one block** whose full extent the thread owns (`bext`). -/
theorem ofBlock {α : Type} {c : MemM α} {Q : α → Assn} {p : Ptr} {A S : Nat} {K : BlockKind}
    {bs : Array Byte} {b : BlockId} (hpb : p.block = some b) (ht : TTriple (bytesAt p A S K bs) c Q)
    (hc : Tame c) :
    FTTriple (up (bytesAt p A S K bs) ⋆ bext b S K) c (fun v => upPost (Q v) (· = b) (pin b S K)) :=
  (FTTriple.ofTTriple (E := pin b S K) (B := (· = b)) ht hc
    (fun h hp l c hc => (bytesAt_cells hpb h hp l c hc).1)
    (fun h hp l c S' K' hc hE => by
      obtain ⟨e, hs, hk⟩ := bytesAt_cells hpb h hp l c hc
      simp only [pin, e, ↓reduceIte] at hE; cases hE; exact ⟨hs, hk⟩)
    (SizeFree.of_pinned fun h hp l c hc => by simp [(bytesAt_cells hpb h hp l c hc).1])
    (.inl fun x hx => by simp [hx])).pre fun _ h => up_sep_bext h

/-- The post of `ofBlock` for a rule that keeps a non-empty `bytesAt` of `b`: the bytes and the
extent again, and extents that own no byte (dropped by `FTTriple.drop`). -/
theorem ofBlock_post {Q : Assn} {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte}
    {b : BlockId} {r : Res} (hpb : p.block = some b) (hpos : 0 < bs.size)
    (hQ : ∀ h, Q h → bytesAt p A S K bs h) (h : upPost Q (· = b) (pin b S K) r) :
    ((up Q ⋆ bext b S K) ⋆ fun r => r.heap = FHeap.empty ∧ r.know = Know.none) r := by
  obtain ⟨E', ⟨hq', -, -⟩, -⟩ := id h
  obtain ⟨x, fc, hfc, hs, hk⟩ := bytesAt_cell hpb hpos (hQ _ hq')
  exact upPost_bext h ⟨x, fc, hfc, hs, hk, fun _ => by simp⟩

theorem up_lift_sep {φ : Prop} {P : Assn} {R : FAssn} {r : Res} (h : (up (⌜φ⌝ ∗ P) ⋆ R) r) :
    (⟪φ⟫ ⋆ (up P ⋆ R)) r := by
  obtain ⟨r₁, r₂, hd, e, h1, h2⟩ := h
  obtain ⟨hφ, h1⟩ := up_lift.mp h1
  exact sep_lift.mpr ⟨hφ, r₁, r₂, hd, e, h1, h2⟩

/-- `free` of a whole block in a thread, not a `const` global: its bytes and its full extent go. -/
theorem free' {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte} {b : BlockId}
    (hpb : p.block = some b) (hS : bs.size = S) (h0 : p.off = 0) (hpos : 0 < S)
    (hK : K ≠ .constGlobal := by decide) :
    FTTriple (up (bytesAt p A S K bs) ⋆ bext b S K) (free p) (fun _ => emp) :=
  (ofBlock hpb (TTriple.free hS h0 hpos hK) (Tame.free p)).forgetExt.post fun _ _ h => up_emp.mp h

/-- A store of `w` at byte `k` of a thread's block, whose full extent it owns. -/
theorem storeAt {T : Type} [Enc T] [LawfulEnc T] {p q : Ptr} {A S : Nat} {K : BlockKind}
    {bs : Array Byte} {b : BlockId} {k a : Nat} (w : T) (hpb : p.block = some b) (hq : q = p.add k)
    (hn : 0 < Enc.size T) (hk : k + Enc.size T ≤ bs.size) (ha : (A + p.off.toNat + k) % a = 0)
    (hK : K ≠ .constGlobal) :
    FTTriple (up (bytesAt p A S K bs) ⋆ bext b S K) (Zig.store a q w)
      (fun _ => up (bytesAt p A S K (writeBytes bs k (Enc.encode w))) ⋆ bext b S K) := by
  have hpos : 0 < (writeBytes bs k (Enc.encode w)).size := by
    rw [writeBytes_size _ _ _ (by rw [LawfulEnc.size_encode]; omega)]; omega
  exact FTTriple.drop ((ofBlock hpb (TTriple.storeAt w hq hn hk ha hK) (Tame.store a q w)).post
    fun _ _ h => ofBlock_post hpb hpos (fun _ h => h) h) fun _ _ h => h.1

/-- A load of `v` at byte `k` of a thread's block. -/
theorem loadAt {T : Type} [Enc T] {p q : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte}
    {b : BlockId} {k a : Nat} {v : T} (hpb : p.block = some b) (hq : q = p.add k)
    (hn : 0 < Enc.size T) (hk : k + Enc.size T ≤ bs.size) (ha : (A + p.off.toNat + k) % a = 0)
    (hv : Enc.decode (bs.extract k (k + Enc.size T)) = pure v) :
    FTTriple (up (bytesAt p A S K bs) ⋆ bext b S K) (Zig.load T a q)
      (fun x => ⟪x = v⟫ ⋆ (up (bytesAt p A S K bs) ⋆ bext b S K)) :=
  FTTriple.drop ((ofBlock hpb (TTriple.loadAt hq hn hk ha hv) (Tame.load T a q)).post
    fun _ _ h => sep_mono_left (fun _ h => up_lift_sep h)
      (ofBlock_post hpb (by omega) (fun _ h => (Zig.sep_lift.mp h).2) h)) fun _ _ h => h.1

/-- The pointer `k` bytes into a thread's block. -/
theorem ptrProjectAt {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte} {b : BlockId}
    {k : Nat} (hpb : p.block = some b) (hk : k ≤ bs.size) (hpos : 0 < bs.size) :
    FTTriple (up (bytesAt p A S K bs) ⋆ bext b S K) (ptrProject p (·.add k))
      (fun x => ⟪x = p.add k⟫ ⋆ (up (bytesAt p A S K bs) ⋆ bext b S K)) :=
  FTTriple.drop ((ofBlock hpb (TTriple.ptrProjectAt hk hpos) (Tame.ptrProject p _)).post
    fun _ _ h => sep_mono_left (fun _ h => up_lift_sep h)
      (ofBlock_post hpb hpos (fun _ h => (Zig.sep_lift.mp h).2) h)) fun _ _ h => h.1

end FTTriple

end Full
end Zig
