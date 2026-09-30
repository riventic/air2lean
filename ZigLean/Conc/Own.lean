import ZigLean.Conc.Lemmas
import ZigLean.Sep.Block

/-!
# Ownership in threads

The separation logic of `ZigLean/Sep/` for a thread of a concurrent run.

- **Ownership** (`Mem.OwnsC`, `Mem.Owns`). The clock `c` owns the heap `h` if every recorded
  access to a byte of `h` happened before `c`. Thread `t` owns `h` if its clock does. Then a
  plain access by `t` to the bytes of `h` does not race (`Mem.Owns.noRace`): no recorded access
  to them is concurrent with `t`. Ownership moves with the clocks: a clock that is later owns
  what an earlier one owns (`Mem.OwnsC.mono`). So a release write gives ownership to the thread that
  reads it with acquire, a spawn gives it to the child, and a join gives it back.
- **A step of the owner** (`StepIn hF`). A step of the current thread that changes only the
  bytes it owns: the frame `hF` (the rest of the heap) and the other threads' clocks stay
  unchanged, and each new footprint entry is the current thread's and touches no byte of `hF`.
  So the ownership of every part of `hF`, by any clock, stays (`Mem.OwnsC.frame`).
- **Thread triples** (`TTriple`). `Triple` with ownership in place of `SingleThread`: if the
  current thread owns the part `P` holds of, `c` does not throw, `Q` holds of the part after it,
  the thread owns that part, and the step is a `StepIn` of the frame. The rules are those of
  `Triple`: `conseq`, `frame`, `ret`, `bind`, `ex`, `lift`, `load`, `store`, `alloc`, `free`.
- **In a thread** (`WP.liftM_triple`). A `MemM` step of generated code with a thread triple is a
  `WP` step: the proof gets the post and the `StepIn` of the rest of the memory, and with it
  keeps its invariant for the other threads' parts.

A zero-length access counts as its first byte (`FootprintEntry.Touches`): the race check sees it
at that byte too.
-/

namespace Zig

open Assn

/-- The footprint entry `e` accesses a byte that `h` has (a zero-length entry: its first byte). -/
def FootprintEntry.Touches (e : FootprintEntry) (h : Heap) : Prop :=
  ∃ x, e.off ≤ x ∧ (x < e.off + e.len ∨ x = e.off) ∧ h (e.block, x) ≠ none

/-- The clock `c` owns `h`: every recorded access to a byte of `h`, and every access to a block
that does not exist yet, happened before `c`. -/
def Mem.OwnsC (m : Mem) (c : VClock) (h : Heap) : Prop :=
  ∀ e ∈ m.footprint, (e.Touches h ∨ m.blocks.size ≤ e.block) → VClock.le e.clock c = true

/-- Thread `t` owns `h`. -/
def Mem.Owns (m : Mem) (t : ThreadId) (h : Heap) : Prop := m.OwnsC (m.clocks[t]!) h

/-- A step of the current thread that changes only the bytes it owns (module doc). -/
structure StepIn (hF : Heap) (m m' : Mem) : Prop where
  current : m'.current = m.current
  threads : m'.threads = m.threads
  atomics : m'.atomics = m.atomics
  seen : m'.seen = m.seen
  nextMsg : m'.nextMsg = m.nextMsg
  waiters : m'.waiters = m.waiters
  woken : m'.woken = m.woken
  groups : m'.groups = m.groups
  size : m'.clocks.size = m.clocks.size
  others : ∀ u, u ≠ m.current → m'.clocks[u]! = m.clocks[u]!
  mine : VClock.le (m.clocks[m.current]!) (m'.clocks[m.current]!) = true
  blocks : m.blocks.size ≤ m'.blocks.size
  fp : ∀ e ∈ m'.footprint, e ∈ m.footprint ∨
    (e.tid = m.current ∧ ¬ e.Touches hF ∧ e.block < m'.blocks.size)

section Owns

variable {m m' : Mem} {c c' : VClock} {h h₁ h₂ hF : Heap}

theorem Mem.OwnsC.mono (ho : m.OwnsC c h) (hc : VClock.le c c' = true) : m.OwnsC c' h :=
  fun e he ht => VClock.le_trans (ho e he ht) hc

/-- A part of an owned heap is owned. -/
theorem Mem.OwnsC.sub (ho : m.OwnsC c h) (hs : ∀ l, h₁ l ≠ none → h l ≠ none) : m.OwnsC c h₁ :=
  fun e he ht => ho e he (ht.imp (fun ⟨x, h1, h2, h3⟩ => ⟨x, h1, h2, hs _ h3⟩) id)

theorem Mem.OwnsC.union (h1 : m.OwnsC c h₁) (h2 : m.OwnsC c h₂) : m.OwnsC c (h₁ ∪ h₂) := by
  intro e he ht
  rcases ht with ⟨x, hx1, hx2, hx3⟩ | hb
  · by_cases hn : h₁ (e.block, x) = none
    · exact h2 e he (.inl ⟨x, hx1, hx2, by simpa [hn] using hx3⟩)
    · exact h1 e he (.inl ⟨x, hx1, hx2, hn⟩)
  · exact h1 e he (.inr hb)

theorem Mem.OwnsC.left (ho : m.OwnsC c (h₁ ∪ h₂)) : m.OwnsC c h₁ :=
  ho.sub fun l hl => by simp only [Heap.union_apply]; cases e : h₁ l <;> simp_all

theorem Mem.OwnsC.right (ho : m.OwnsC c (h₁ ∪ h₂)) : m.OwnsC c h₂ :=
  ho.sub fun l hl => by simp only [Heap.union_apply]; cases e : h₁ l <;> simp_all

/-- A `StepIn hF` keeps the ownership of each part of `hF`, by any clock. -/
theorem Mem.OwnsC.frame (hs : StepIn hF m m') (ho : m.OwnsC c h) (hsub : ∀ l, h l ≠ none → hF l ≠ none) :
    m'.OwnsC c h := by
  intro e he ht
  rcases hs.fp e he with he | ⟨-, hnt, hb⟩
  · exact ho e he (ht.imp id fun hb => Nat.le_trans hs.blocks hb)
  · rcases ht with ⟨x, hx1, hx2, hx3⟩ | hb'
    · exact absurd ⟨x, hx1, hx2, hsub _ hx3⟩ hnt
    · exact absurd hb' (Nat.not_le.mpr hb)

/-- Another thread keeps what it owns over a `StepIn hF` when that is a part of `hF`. -/
theorem Mem.Owns.frame {u : ThreadId} (hs : StepIn hF m m') (hu : u ≠ m.current) (ho : m.Owns u h)
    (hsub : ∀ l, h l ≠ none → hF l ≠ none) : m'.Owns u h := by
  unfold Mem.Owns; rw [hs.others u hu]; exact Mem.OwnsC.frame hs ho hsub

/-- The current thread keeps what it owns in `hF` over a `StepIn hF`. -/
theorem Mem.Owns.frameSelf (hs : StepIn hF m m') (ho : m.Owns m.current h)
    (hsub : ∀ l, h l ≠ none → hF l ≠ none) : m'.Owns m'.current h := by
  unfold Mem.Owns; rw [hs.current]; exact (Mem.OwnsC.frame hs ho hsub).mono hs.mine

/-- A plain access by the current thread to bytes it owns does not race. -/
theorem Mem.Owns.noRace {b : BlockId} {off len : Nat} {kind : AccessKind} (ho : m.Owns m.current h)
    (hlen : 0 < len) (hin : ∀ x, off ≤ x → x < off + len → h (b, x) ≠ none) :
    NoRace m b off len kind := by
  unfold NoRace raceAt
  rw [Array.findSome?_eq_none_iff]
  intro e he
  split
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨hb, h1⟩, h2⟩, hcon⟩ := hc
    subst hb
    have ht : e.Touches h := by
      by_cases ho' : e.off ≤ off
      · exact ⟨off, ho', by omega, hin off (Nat.le_refl _) (by omega)⟩
      · exact ⟨e.off, Nat.le_refl _, by omega, hin e.off (by omega) h2⟩
    have hle := VClock.le_trans (ho e he (.inl ht)) (VClock.le_bump (m.clocks[m.current]!) m.current)
    simp [VClock.concurrent, hle] at hcon
  · rfl

end Owns

namespace StepIn

variable {m m' m'' : Mem} {hF hF' : Heap}

theorem refl (m : Mem) (hF : Heap) : StepIn hF m m :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, VClock.le_refl _, Nat.le_refl _,
    fun _ he => .inl he⟩

theorem trans (h₁ : StepIn hF m m') (h₂ : StepIn hF m' m'') : StepIn hF m m'' := by
  refine ⟨h₂.current.trans h₁.current, h₂.threads.trans h₁.threads, h₂.atomics.trans h₁.atomics,
    h₂.seen.trans h₁.seen, h₂.nextMsg.trans h₁.nextMsg, h₂.waiters.trans h₁.waiters,
    h₂.woken.trans h₁.woken, h₂.groups.trans h₁.groups, h₂.size.trans h₁.size,
    fun u hu => (h₂.others u (h₁.current ▸ hu)).trans (h₁.others u hu), ?_,
    Nat.le_trans h₁.blocks h₂.blocks, fun e he => ?_⟩
  · have := h₂.mine; rw [h₁.current] at this; exact VClock.le_trans h₁.mine this
  · rcases h₂.fp e he with he' | ⟨ht, hnt, hb⟩
    · rcases h₁.fp e he' with he'' | ⟨ht, hnt, hb⟩
      · exact .inl he''
      · exact .inr ⟨ht, hnt, Nat.lt_of_lt_of_le hb h₂.blocks⟩
    · exact .inr ⟨ht.trans h₁.current, hnt, hb⟩

/-- A step in a larger frame is a step in a part of it. -/
theorem weaken (hs : StepIn hF m m') (hsub : ∀ l, hF' l ≠ none → hF l ≠ none) : StepIn hF' m m' :=
  { hs with
    fp := fun e he => (hs.fp e he).imp id fun ⟨ht, hnt, hb⟩ =>
      ⟨ht, fun ⟨x, h1, h2, h3⟩ => hnt ⟨x, h1, h2, hsub _ h3⟩, hb⟩ }

/-- `Mem.write` changes only the bytes of a block. -/
theorem write (m : Mem) (hF : Heap) (b : BlockId) (blk : Block) (o : Nat) (bs : Array Byte) :
    StepIn hF m (m.write b blk o bs) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, VClock.le_refl _,
    by simp [Mem.write], fun _ he => .inl he⟩

end StepIn

section Record

variable {m : Mem} {h hF : Heap} {b : BlockId} {off len : Nat} {kind : AccessKind}

theorem recordAt_clock (hc : m.current < m.clocks.size) :
    (m.recordAt b off len kind).clocks[m.current]! = VClock.bump (m.clocks[m.current]!) m.current :=
  Array.getElem!_set!_self m.clocks m.current _ hc

/-- A recorded access by the current thread to bytes it owns (in `h`, not in `hF`). -/
theorem StepIn.recordAt (hc : m.current < m.clocks.size) (hd : Heap.Disjoint h hF)
    (hlen : 0 < len) (hin : ∀ x, off ≤ x → x < off + len → h (b, x) ≠ none)
    (hb : b < m.blocks.size) : StepIn hF m (m.recordAt b off len kind) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp [Mem.recordAt], fun u hu => ?_, ?_,
    Nat.le_refl _, fun e he => ?_⟩
  · show (m.clocks.set! m.current _)[u]! = _
    rw [Conc.Proto.getElem!_set!_ite]; simp [hu]
  · rw [recordAt_clock hc]; exact VClock.le_bump _ _
  · simp only [Mem.recordAt, Array.mem_push] at he
    rcases he with he | rfl
    · exact .inl he
    · refine .inr ⟨rfl, fun ⟨x, h1, h2, h3⟩ => ?_, hb⟩
      simp only at h1 h2 h3
      have := hin x h1 (by omega)
      rcases hd (b, x) with e | e
      · exact this e
      · exact h3 e

/-- The current thread keeps what it owns over one of its recorded accesses. -/
theorem Mem.Owns.recordAt (hc : m.current < m.clocks.size) (ho : m.Owns m.current h) :
    (m.recordAt b off len kind).Owns (m.recordAt b off len kind).current h := by
  show (m.recordAt b off len kind).OwnsC ((m.recordAt b off len kind).clocks[m.current]!) h
  rw [recordAt_clock hc]
  intro e he ht
  simp only [Mem.recordAt, Array.mem_push] at he
  rcases he with he | rfl
  · exact VClock.le_trans (ho e he ht) (VClock.le_bump _ _)
  · exact VClock.le_refl _

theorem Mem.Owns.write (ho : m.Owns m.current h) {b : BlockId} {blk : Block} {o : Nat}
    {bs : Array Byte} : (m.write b blk o bs).Owns (m.write b blk o bs).current h := by
  intro e he ht
  exact ho e he (ht.imp id fun h' => by simpa [Mem.write] using h')

end Record

/-! ## Thread triples -/

/-- `Triple` for a thread (module doc). -/
def TTriple {α : Type} (P : Assn) (c : MemM α) (Q : α → Assn) : Prop :=
  ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF → P hP → m.current < m.clocks.size →
    m.Owns m.current hP →
    match (c.run m).run with
    | none => True
    | some (.error _) => False
    | some (.ok (v, m')) =>
      ∃ hQ, Heap.Disjoint hQ hF ∧ m'.heap = hQ ∪ hF ∧ Q v hQ ∧ m'.Owns m'.current hQ ∧
        StepIn hF m m'

namespace TTriple

variable {α β : Type} {P P' R : Assn} {Q Q' : α → Assn} {c : MemM α}

theorem of_run
    (h : ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF → P hP → m.current < m.clocks.size →
      m.Owns m.current hP →
      ∃ v m' hQ, c.run m = pure (v, m') ∧ Heap.Disjoint hQ hF ∧ m'.heap = hQ ∪ hF ∧ Q v hQ ∧
        m'.Owns m'.current hQ ∧ StepIn hF m m') :
    TTriple P c Q := by
  intro m hP hF hd hm hp hc ho
  obtain ⟨v, m', hQ, hr, hd', hm', hq, ho', hs⟩ := h m hP hF hd hm hp hc ho
  rw [hr]; exact ⟨hQ, hd', hm', hq, ho', hs⟩

theorem conseq (ht : TTriple P c Q) (hp : ∀ h, P' h → P h) (hq : ∀ v h, Q v h → Q' v h) :
    TTriple P' c Q' := by
  intro m hP hF hd hm hp' hc ho
  have := ht m hP hF hd hm (hp _ hp') hc ho
  split at this
  · trivial
  · exact this
  · obtain ⟨hQ, a, b, c, d, e⟩ := this; exact ⟨hQ, a, b, hq _ _ c, d, e⟩

/-- The frame rule: a part of the memory that `c` does not own stays unchanged, and the thread
keeps it. -/
theorem frame (ht : TTriple P c Q) : TTriple (P ∗ R) c (fun v => Q v ∗ R) := by
  intro m hPR hF hd hm ⟨hP, hR, hPd, hPR', hp, hr⟩ hc ho
  subst hPR'
  obtain ⟨hPF, hRF⟩ := Heap.disjoint_union_left.mp hd
  have hd' : Heap.Disjoint hP (hR ∪ hF) := Heap.disjoint_union_right.mpr ⟨hPd, hPF⟩
  have hm' : m.heap = hP ∪ (hR ∪ hF) := by rw [hm, Heap.union_assoc]
  have := ht m hP (hR ∪ hF) hd' hm' hp hc (Mem.OwnsC.left ho)
  split at this
  · trivial
  · exact this
  · obtain ⟨hQ, hQd, hmQ, hq, ho', hs⟩ := this
    obtain ⟨hQR, hQF⟩ := Heap.disjoint_union_right.mp hQd
    have hsubR : ∀ l, hR l ≠ none → (hR ∪ hF) l ≠ none := fun l hl => by
      rw [Heap.union_apply]; cases e : hR l <;> simp_all
    refine ⟨hQ ∪ hR, Heap.disjoint_union_left.mpr ⟨hQF, hRF⟩, by rw [hmQ, Heap.union_assoc],
      ⟨hQ, hR, hQR, rfl, hq, hr⟩, Mem.OwnsC.union ho' (Mem.Owns.frameSelf hs (Mem.OwnsC.right ho) hsubR),
      hs.weaken fun l hl => ?_⟩
    simp only [Heap.union_apply]; cases e : hR l <;> simp_all

theorem ret (v : α) : TTriple (Q v) (pure v : MemM α) Q :=
  of_run fun m hP _ hd hm hq _ ho => ⟨v, m, hP, rfl, hd, hm, hq, ho, StepIn.refl m _⟩

theorem bind {R : β → Assn} {f : α → MemM β} (hc : TTriple P c Q) (hf : ∀ v, TTriple (Q v) (f v) R) :
    TTriple P (c >>= f) R := by
  intro m hP hF hd hm hp hcl ho
  have h1 := hc m hP hF hd hm hp hcl ho
  simp only [StateT.run_bind, ExceptT.run_bind]
  revert h1
  cases (c.run m).run with
  | none => intro; trivial
  | some r =>
    cases r with
    | error e => intro h1; exact h1.elim
    | ok r =>
      obtain ⟨v, m'⟩ := r
      rintro ⟨hQ, hd', hm', hq, ho', hs⟩
      have hcl' : m'.current < m'.clocks.size := by rw [hs.current, hs.size]; exact hcl
      have h2 := hf v m' hQ hF hd' hm' hq hcl' ho'
      dsimp only [Bind.bind, Option.bind]
      split at h2
      · trivial
      · exact h2
      · obtain ⟨hR, a, b, c, d, hs'⟩ := h2
        exact ⟨hR, a, b, c, d, hs.trans hs'⟩

theorem ex {γ : Type} {P : γ → Assn} (h : ∀ x, TTriple (P x) c Q) : TTriple (Assn.ex P) c Q := by
  intro m hP hF hd hm ⟨x, hp⟩ hc ho
  exact h x m hP hF hd hm hp hc ho

theorem lift {φ : Prop} (h : φ → TTriple P c Q) : TTriple (⌜φ⌝ ∗ P) c Q := by
  intro m hP hF hd hm hp hc ho
  obtain ⟨hφ, hp⟩ := sep_lift.mp hp
  exact h hφ m hP hF hd hm hp hc ho

end TTriple

section Rules

variable {T : Type} [Enc T] {m : Mem} {h hF : Heap}

/-- The bytes of `bytesAt` are in the heap. -/
theorem bytesAt_in {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte}
    (hb : bytesAt p A S K bs h) {b : BlockId} (hpb : p.block = some b) {x : Nat}
    (h1 : p.off.toNat ≤ x) (h2 : x < p.off.toNat + bs.size) : h (b, x) ≠ none := by
  obtain ⟨b', hb', -, hl⟩ := hb
  rw [hpb] at hb'; cases hb'
  rw [hl]; simp [h1, h2]

theorem TTriple.load {p : Ptr} {a : Nat} {v : T} (hn : 0 < Enc.size T) :
    TTriple (pts p a v) (Zig.load T a p) (fun r => ⌜r = v⌝ ∗ pts p a v) :=
  TTriple.of_run fun m hP hF hd hm hp hc ho => by
    have hp' := hp
    obtain ⟨A, S, K, bs, ha, hs, hv, hb, -⟩ := hp
    obtain ⟨b, blk, hacc, hblk, -, -, hx⟩ :=
      bytesAt_access (q := p) (k := 0) (n := Enc.size T) (a := a) hb hm (by simp [Ptr.add])
        hn (by omega) (by simpa using ha)
    obtain ⟨hpb, -⟩ := access_eq hacc
    simp only [Nat.add_zero] at hx hacc
    have hv' : Enc.decode (blk.bytes.extract p.off.toNat (p.off.toNat + Enc.size T)) = pure v := by
      rw [hx, show bs.extract 0 (0 + Enc.size T) = bs by rw [← hs]; simp]; exact hv
    have hin : ∀ x, p.off.toNat ≤ x → x < p.off.toNat + Enc.size T → hP (b, x) ≠ none :=
      fun x h1 h2 => bytesAt_in hb hpb h1 (by omega)
    have hbs : b < m.blocks.size := (Array.getElem?_eq_some_iff.mp hblk).1
    refine ⟨v, _, hP, load_run (by simpa using hacc) hv' (ho.noRace hn hin), hd, ?_,
      sep_lift.mpr ⟨rfl, hp'⟩, Mem.Owns.recordAt hc ho, StepIn.recordAt hc hd hn hin hbs⟩
    funext l; rw [Mem.heap_recordAt]; exact congrFun hm l

theorem TTriple.store [LawfulEnc T] {p : Ptr} {a : Nat} {v : T} (hn : 0 < Enc.size T) (w : T) :
    TTriple (pts p a v) (Zig.store a p w) (fun _ => pts p a w) :=
  TTriple.of_run fun m hP hF hd hm hp hc ho => by
    obtain ⟨A, S, K, bs, ha, hs, -, hb, hK⟩ := hp
    have hw := LawfulEnc.size_encode w
    have hin : ∀ b, p.block = some b →
        ∀ x, p.off.toNat + 0 ≤ x → x < p.off.toNat + 0 + (Enc.encode w).size → hP (b, x) ≠ none :=
      fun b hpb x h1 h2 => bytesAt_in hb hpb (by omega) (by omega)
    obtain ⟨b, blk, hpb, hr, h', hd', hm', hb'⟩ :=
      bytesAt_store_core (q := p) (k := 0) (a := a) (bs' := Enc.encode w) hb hm hd
        (by simp [Ptr.add]) (by omega) (by omega) (by simpa using ha)
        (fun b hpb => ho.noRace (by omega) (hin b hpb)) hK
    have hbs : b < m.blocks.size := by
      have c0 := bytesAt_cell (j := 0) hb hm hpb (by omega)
      obtain ⟨blk', hblk', -⟩ := Mem.heap_some c0
      exact (Array.getElem?_eq_some_iff.mp hblk').1
    have hs1 := StepIn.recordAt (kind := .write) hc hd (by omega) (hin b hpb) hbs
    refine ⟨(), _, h', hr, hd', hm', ⟨A, S, K, _, ha, ?_, ?_, hb', hK⟩,
      Mem.Owns.write ?_,
      hs1.trans (StepIn.write _ _ _ _ _ _)⟩
    · rw [writeBytes_all (by omega)]; exact hw
    · rw [writeBytes_all (by omega)]; exact LawfulEnc.decode_encode w
    · -- The written bytes are the owned bytes of `h'`: the same locations as those of `hP`.
      have ho1 := Mem.Owns.recordAt (b := b) (off := p.off.toNat + 0) (len := (Enc.encode w).size)
        (kind := .write) hc ho
      intro e he ht
      apply ho1 e he
      rcases ht with ⟨x, h1, h2, h3⟩ | hb2
      · refine .inl ⟨x, h1, h2, ?_⟩
        obtain ⟨b'', hpb'', -, hl'⟩ := id hb'
        rw [hpb] at hpb''; cases hpb''
        rw [hl', writeBytes_size _ _ _ (by omega)] at h3
        split at h3
        · rename_i hc'
          obtain ⟨hbe, hx1, hx2⟩ := hc'
          simp only at hbe hx1 hx2
          rw [hbe]; exact bytesAt_in hb hpb hx1 hx2
        · exact absurd rfl h3
      · exact .inr (by simpa [Mem.write] using hb2)

end Rules

section Blocks

variable {m : Mem} {h hF : Heap}

/-- A byte of `bytesAt p …` is in the block of `p`. -/
theorem bytesAt_block {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte}
    (hb : bytesAt p A S K bs h) {b : BlockId} (hpb : p.block = some b) {l : Loc}
    (hl : h l ≠ none) : l.1 = b := by
  obtain ⟨b', hb', -, hown⟩ := hb
  rw [hpb] at hb'; cases hb'
  rw [hown] at hl
  split at hl
  · rename_i hc; exact hc.1
  · exact absurd rfl hl

/-- A step that changes only the blocks. -/
theorem StepIn.sameThreads {m' : Mem} (hs : m.SameThreads m') (hb : m.blocks.size ≤ m'.blocks.size) :
    StepIn hF m m' where
  current := hs.current
  threads := hs.threads
  atomics := hs.atomics
  seen := hs.seen
  nextMsg := hs.nextMsg
  waiters := hs.waiters
  woken := hs.woken
  groups := hs.groups
  size := by rw [hs.clocks]
  others u _ := by rw [hs.clocks]
  mine := by rw [hs.clocks]; exact VClock.le_refl _
  blocks := hb
  fp e he := .inl (hs.footprint ▸ he)

theorem TTriple.alloc (kind : BlockKind) (size align : Nat) (ha : 0 < align) :
    TTriple emp (Zig.alloc kind size align) (fun p => Assn.ex fun A =>
      ⌜p.off = 0 ∧ A % align = 0⌝ ∗ bytesAt p A size kind (Array.replicate size .undef)) :=
  TTriple.of_run fun m hP hF hd hm hp _ ho => by
    have hP0 : hP = Heap.empty := hp
    subst hP0
    obtain ⟨p, m', h', hr, h0, hpb, hsz, hd', hm', -, hs, A, hA, hb⟩ :=
      alloc_run_core hd hm kind size align ha
    simp only [Heap.empty_union] at hd' hm'
    refine ⟨p, m', h', hr, hd', hm', ⟨A, sep_lift.mpr ⟨⟨h0, hA⟩, hb⟩⟩, ?_,
      StepIn.sameThreads hs (by omega)⟩
    intro e he ht
    rw [hs.footprint] at he
    unfold Mem.Owns at ho
    rw [hs.current, hs.clocks]
    apply ho e he (.inr ?_)
    rcases ht with ⟨x, -, -, hx⟩ | hb'
    · have := bytesAt_block hb hpb hx; simp only at this; rw [this]; exact Nat.le_refl _
    · omega

theorem TTriple.free {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte} (hS : bs.size = S)
    (h0 : p.off = 0) (hpos : 0 < S) : TTriple (bytesAt p A S K bs) (Zig.free p) (fun _ => emp) :=
  TTriple.of_run fun m _ hF hd hm hb _ ho => by
    obtain ⟨m', hr, hm', hsz, hs⟩ := free_run_core hb hm hd hS h0 hpos
    refine ⟨(), m', Heap.empty, hr, (Heap.disjoint_empty hF).symm, hm', rfl, ?_,
      StepIn.sameThreads hs (by omega)⟩
    intro e he ht
    rw [hs.footprint] at he
    unfold Mem.Owns at ho
    rw [hs.current, hs.clocks]
    apply ho e he (.inr ?_)
    rcases ht with ⟨x, -, -, hx⟩ | hb'
    · exact absurd rfl hx
    · omega

end Blocks

/-! ## In a thread -/

namespace Conc
namespace Proto

variable {Tgt γ σ α : Type} {P : Proto Tgt γ} {t : ThreadId} {G : ThreadId → γ} {m : Mem}
  {n : Nat}

/-- A `MemM` step of generated code with a thread triple (module doc): the current thread owns
`hP`, the rest of the heap is `hF`. -/
theorem WP.liftM_triple {x : MemM α} {s : σ} {Pa : Assn} {Qa : α → Assn}
    {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop} {hP hF : Heap} (ht : TTriple Pa x Qa)
    (hd : Heap.Disjoint hP hF) (hm : m.heap = hP ∪ hF) (hp : Pa hP)
    (hc : m.current < m.clocks.size) (ho : m.Owns m.current hP)
    (h : ∀ a m' hQ, Heap.Disjoint hQ hF → m'.heap = hQ ∪ hF → Qa a hQ →
      m'.Owns m'.current hQ → StepIn hF m m' → Q (a, s) G m' n) :
    P.WP t ((_root_.liftM x : CM Tgt σ α).run s) Q G m n := by
  have hx := ht m hP hF hd hm hp hc ho
  refine WP.liftM (fun e he => ?_) fun a m' hr => ?_
  · rw [he] at hx; exact hx.elim
  · rw [hr] at hx
    obtain ⟨hQ, hd', hm', hq, ho', hs⟩ := hx
    exact ⟨by rw [hs.threads], h a m' hQ hd' hm' hq ho' hs⟩

end Proto
end Conc

end Zig
