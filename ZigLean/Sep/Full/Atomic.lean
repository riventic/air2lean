import ZigLean.Sep.Full.ThreadStep

/-!
# Atomic points-to (`docs/sep-full-state.md`, `docs/sep-threads.md` S1)

Rules for `atomic_load` and `atomic_store` of a 64-bit word that the precondition owns
(`ZigLean/Sep/Full/Res.lean`), at choice `0` (the newest message, a write at the end):

* the op puts a location only over the owned bytes (`locIdx_post`), and a retired location
  leaves its other bytes without one, so every frame constraint stays true (`holds_after`;
  atomic tags are constraints, `docs/sep-full-state.md` §Atomic tags are constraints);
* choice `0` reads and writes the owned bytes like a plain access: the newest message has the
  block's bytes (`locIdx` adds a message when they differ, a new location starts with them);
* the op does not race (the thread owns the word, `Mem.Owns.noRace`) and is a step of the thread
  outside every frame (`FStepIn.locIdx`, `loadM`, `storeM`, `rmwM`, `ZigLean/Conc/Clock.lean`);
* the op does not throw at `locIdx` (`locIdx_noErr_word`) when **either** the word is an `apts`
  (its tag constraint: no location of another offset or size overlaps it, `abytesAt_layout`),
  **or** the run is sequential (`locIdx_noErr_single`: a location over the bytes of another
  offset or size is retired, since every access to it happened before; `retireAt`).

So each op has **one** analysis of its run (`atomicLoad_run`, `atomicStore_run`, …), with that
disjunction as its premise. It gives the **thread rule** of an `apts` word (`FTTriple.atomicLoad`,
…, by `FTTriple.of_step`), whose sequential reading is the `apts` rule (`.toFTriple`), and the
**sequential rule of any owned word** (`wpts`, whatever its constraint: `FTriple.atomicLoadW`, …,
by `FTriple.of_step`). A `wpts` word has no thread rule: concurrently, a mixed-size access whose
overlapping location has a concurrent access throws `.unspecified`
(`tests/roadmap/sep-full/AtomicRetireCX.lean`). `FTriple.untag` and `wpts_of_up` apply the `wpts`
rules to bytes owned as plain (`up`) bytes.
-/

namespace Zig
namespace Full

open FAssn Conc Conc.Proto

/-! ## The layout after `locIdx` -/

theorem shape_mem {m : Mem} {i : Nat} (hi : i < m.atomics.size) :
    ALoc.shape m.atomics[i] ∈ shapes m := by
  unfold shapes
  exact List.mem_map.mpr ⟨m.atomics[i], Array.mem_toList_iff.mpr (Array.getElem_mem hi), rfl⟩

theorem shapes_set {a : Array ALoc} {i : Nat} {l : ALoc} (hi : i < a.size)
    (hs : ALoc.shape l = ALoc.shape a[i]) :
    (a.set! i l).toList.map ALoc.shape = a.toList.map ALoc.shape := by
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    simp only [List.getElem_map, Array.getElem_toList, Array.set!_eq_setIfInBounds]
    rw [Array.getElem_setIfInBounds (by simpa using h2)]
    split
    · subst_vars; exact hs
    · rfl

theorem pos_of_back {M : Array Msg} {c : Array Byte} (h : (M.back?.map (·.bytes)).getD #[] = c)
    (hc : 0 < c.size) : 0 < M.size := by
  rcases hm : M.size with _ | n
  · have : M.back? = none := by rw [Array.back?_eq_none_iff]; exact Array.size_eq_zero_iff.mp hm
    rw [this] at h; rw [← h] at hc; simp at hc
  · omega

/-- `locIdx` at an existing location `i`: it keeps the shape, and its newest message has the
block's bytes. -/
theorem locIdx_found' {m m₁ : Mem} {b o len li i : Nat}
    (hi : m.atomics.findIdx? (fun l => l.block == b && l.off == o) = some i)
    (hlen : (m.atomics[i]!).len = len) (hcur : 0 < (curBytes m b o len).size)
    (h : ((locIdx b o len).run m).run = some (.ok (li, m₁))) :
    li = i ∧ ∃ (M : Array Msg) (next : Nat), 0 < M.size ∧
      (M.back?.map (·.bytes)).getD #[] = curBytes m b o len ∧
      m₁ = { m with atomics := m.atomics.set! i { m.atomics[i]! with msgs := M }, nextMsg := next } := by
  unfold locIdx at h
  obtain ⟨a₁, m', hg, h₁⟩ := MemM.bind_ok h
  obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
  simp only [hi] at h₁
  split at h₁
  · rename_i hne; simp [hlen] at hne
  · split at h₁
    · rename_i hc
      obtain ⟨_, m₂, hs, h₂⟩ := MemM.bind_ok h₁
      have := MemM.set_ok hs
      subst this
      obtain ⟨rfl, rfl⟩ := MemM.pure_ok h₂
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact ⟨rfl, _, _, pos_of_back hc.1 hcur, hc.1, rfl⟩
    · obtain ⟨_, m₂, hs, h₂⟩ := MemM.bind_ok h₁
      have := MemM.set_ok hs
      subst this
      obtain ⟨rfl, rfl⟩ := MemM.pure_ok h₂
      exact ⟨rfl, _, _, by simp, by simp [curBytes], rfl⟩

theorem List.map_getElem!_zipIdx_filter {α : Type} [Inhabited α] (f : α → Bool) :
    ∀ (pre L : List α), (((L.zipIdx pre.length).filter fun p => f p.1).map (·.2)).map
      (fun i => (pre ++ L)[i]!) = L.filter f
  | _, [] => rfl
  | pre, a :: L => by
    have ih := List.map_getElem!_zipIdx_filter f (pre ++ [a]) L
    simp only [List.length_append, List.length_singleton, List.append_assoc,
      List.singleton_append] at ih
    have ha : (pre ++ a :: L)[pre.length]! = a := by simp
    simp only [List.zipIdx_cons, List.filter_cons]
    split <;> simp_all

/-- The elements of `xs` at the indices that `zipIdx` keeps: a filter of `xs` (`retireAt`'s
`kept`). -/
theorem Array.map_getElem!_zipIdx_filter {α : Type} [Inhabited α] (xs : Array α) (f : α → Bool) :
    (((xs.zipIdx.filter fun p => f p.1).map (·.2)).map (xs[·]!)) = xs.filter f := by
  apply Array.toList_inj.mp
  have := List.map_getElem!_zipIdx_filter f [] xs.toList
  simp only [List.length_nil, List.nil_append] at this
  simp only [Array.toList_map, Array.toList_filter, Array.toList_zipIdx]
  rw [← this]
  congr 1
  funext i
  simp [getElem!_def]

/-- The location `s` overlaps the bytes `o..o+len` of block `b` (`ALoc.hits` of its shape). -/
def Hits (b o len : Nat) (s : Shape) : Bool :=
  s.1 == b && 0 < len && 0 < s.2.2 && o < s.2.1 + s.2.2 && s.2.1 < o + len

theorem shapes_filter_hits (a : Array ALoc) (b o len : Nat) :
    (a.filter fun l => !l.hits b o len).toList.map ALoc.shape =
      (a.toList.map ALoc.shape).filter fun s => !Hits b o len s := by
  rw [Array.toList_filter, List.filter_map]
  rfl

theorem tagOf_some_mem {sh : List Shape} {b x : Nat} {t : Nat × Nat} (h : tagOf sh b x = some t) :
    ∃ s ∈ sh, Covers b x s ∧ t = (s.2.1, s.2.2) := by
  unfold tagOf at h
  obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨s, List.mem_of_find?_eq_some hs, by simpa using List.find?_some hs, rfl⟩

/-! ## Retired locations (`Mem.retire`) -/

/-- The layout after `Mem.retire`: the locations over the bytes are gone. -/
theorem shapes_retire (m : Mem) (b o len : Nat) :
    shapes (m.retire b o len) = (shapes m).filter fun s => !Hits b o len s := by
  simp only [shapes, Mem.retire, Mem.retireIdx]
  rw [Array.map_getElem!_zipIdx_filter _ (fun l => !ALoc.hits b o len l), shapes_filter_hits]

/-- In a well-formed layout, a location of a filtered layout is the one there, or none. -/
theorem tagOf_filter {sh : List Shape} (hw : ShapesWF sh) (p : Shape → Bool) (b x : Nat) :
    tagOf (sh.filter p) b x = none ∨ tagOf (sh.filter p) b x = tagOf sh b x := by
  cases e : tagOf (sh.filter p) b x with
  | none => exact .inl rfl
  | some t =>
    right
    obtain ⟨s, hs, hcs, rfl⟩ := tagOf_some_mem e
    exact (tagOf_of_mem hw (List.mem_filter.mp hs).1 hcs).symm

theorem ShapesWF.filter {sh : List Shape} (hw : ShapesWF sh) (p : Shape → Bool) :
    ShapesWF (sh.filter p) :=
  ⟨fun s hs => hw.1 s (List.mem_filter.mp hs).1, hw.2.sublist List.filter_sublist⟩

/-- The layout after an access at `(b, o)` of `len` bytes that retires the locations over the
bytes and adds `(b, o, len)`: well formed, the bytes carry the new location, and every other
byte keeps its location or (a retired one) has none. -/
theorem layout_push {sh : List Shape} (hw : ShapesWF sh) {b o len : Nat} (hlen : 0 < len) :
    ShapesWF (sh.filter (fun s => !Hits b o len s) ++ [(b, o, len)]) ∧
    ∀ b' x, if Covers b' x (b, o, len)
      then tagOf (sh.filter (fun s => !Hits b o len s) ++ [(b, o, len)]) b' x = some (o, len)
      else tagOf (sh.filter (fun s => !Hits b o len s) ++ [(b, o, len)]) b' x = none ∨
        tagOf (sh.filter (fun s => !Hits b o len s) ++ [(b, o, len)]) b' x = tagOf sh b' x := by
  have hmem : ∀ s ∈ sh.filter (fun s => !Hits b o len s), s ∈ sh ∧ ¬ (s.1 = b ∧
      o < s.2.1 + s.2.2 ∧ s.2.1 < o + len) := by
    intro s hs
    obtain ⟨h1, h2⟩ := List.mem_filter.mp hs
    refine ⟨h1, fun ⟨e1, e2, e3⟩ => ?_⟩
    simp [Hits, e1, e2, e3, hlen, hw.1 s h1] at h2
  refine ⟨⟨fun s hs => ?_, ?_⟩, fun b' x => ?_⟩
  · rcases List.mem_append.mp hs with h | h
    · exact hw.1 s (hmem s h).1
    · simp at h; subst h; exact hlen
  · rw [List.pairwise_append]
    refine ⟨hw.2.sublist List.filter_sublist, List.pairwise_singleton _ _, fun s hs t ht hst => ?_⟩
    simp at ht; subst ht
    have := (hmem s hs).2
    simp only at hst ⊢
    by_cases h1 : o < s.2.1 + s.2.2
    · by_cases h2 : s.2.1 < o + len
      · exact (this ⟨hst, h1, h2⟩).elim
      · right; omega
    · left; omega
  · rw [tagOf_append_single]
    split
    · rename_i hc
      have : tagOf (sh.filter (fun s => !Hits b o len s)) b' x = none := tagOf_none.mpr
        fun s hs hcs => by
          obtain ⟨e1, e2, e3⟩ := hc
          obtain ⟨f1, f2, f3⟩ := hcs
          simp only at e1 e2 e3
          exact (hmem s hs).2 ⟨f1.trans e1.symm, by omega, by omega⟩
      rw [this]; rfl
    · rename_i hc
      simp only [hc, ↓reduceIte, Option.or_none]
      cases e : tagOf (sh.filter (fun s => !Hits b o len s)) b' x with
      | none => exact .inl rfl
      | some t =>
        right
        obtain ⟨s, hs, hcs, rfl⟩ := tagOf_some_mem e
        exact (tagOf_of_mem hw (hmem s hs).1 hcs).symm

/-- `retireAt` in its result: the locations over the bytes are gone, the new one is last. -/
theorem retireAt_eq {m m₁ : Mem} {b o len li : Nat}
    (h : ((retireAt b o len).run m).run = some (.ok (li, m₁))) :
    li = (m.atomics.filter fun l => !l.hits b o len).size ∧ ∃ sn, m₁ = { m with
      atomics := (m.atomics.filter fun l => !l.hits b o len).push (firstLoc m b o len),
      seen := sn, nextMsg := m.nextMsg + 1 } := by
  unfold retireAt at h
  obtain ⟨_, _, hg, h1⟩ := MemM.bind_ok h
  obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
  dsimp only at h1
  split at h1
  · exact (MemM.throw_ok h1).elim
  · obtain ⟨_, _, hs, h2⟩ := MemM.bind_ok h1
    have := MemM.set_ok hs
    subst this
    obtain ⟨rfl, rfl⟩ := MemM.pure_ok h2
    simp only [Mem.retire, Mem.retireIdx]
    rw [Array.map_getElem!_zipIdx_filter _ (fun l => !ALoc.hits b o len l)]
    exact ⟨rfl, _, rfl⟩

/-- What `locIdx` does in a well-formed layout, **whatever the layout over the bytes**: only the
atomics, the threads' views and the message counter change (no byte of any block); location
`li` is `(b, o)`, its newest message has the block's bytes; the layout stays well formed, the
bytes `o..o+len` carry the location `(o, len)`, and every other byte keeps its location or has
none (a location over the bytes and other bytes that a mixed-size access retires: `retireAt`). -/
theorem locIdx_post {m m₁ : Mem} {b o len li : Nat} (hw : ShapesWF (shapes m)) (hlen : 0 < len)
    (hcur : (curBytes m b o len).size = len)
    (h : ((locIdx b o len).run m).run = some (.ok (li, m₁))) :
    (∃ a sn next, m₁ = { m with atomics := a, seen := sn, nextMsg := next }) ∧
    li < m₁.atomics.size ∧ (m₁.atomics[li]!).block = b ∧ (m₁.atomics[li]!).off = o ∧
    0 < (m₁.atomics[li]!).msgs.size ∧ ALoc.lastBytes (m₁.atomics[li]!) = curBytes m b o len ∧
    ShapesWF (shapes m₁) ∧
    ∀ b' x, if Covers b' x (b, o, len) then tagOf (shapes m₁) b' x = some (o, len)
      else tagOf (shapes m₁) b' x = none ∨ tagOf (shapes m₁) b' x = tagOf (shapes m) b' x := by
  -- A retire or a first access: the new location is pushed after the kept ones.
  have hpush : ∀ sn, m₁ = { m with
      atomics := (m.atomics.filter fun l => !l.hits b o len).push (firstLoc m b o len),
      seen := sn, nextMsg := m.nextMsg + 1 } →
      li = (m.atomics.filter fun l => !l.hits b o len).size →
      (∃ a sn next, m₁ = { m with atomics := a, seen := sn, nextMsg := next }) ∧
      li < m₁.atomics.size ∧ (m₁.atomics[li]!).block = b ∧ (m₁.atomics[li]!).off = o ∧
      0 < (m₁.atomics[li]!).msgs.size ∧ ALoc.lastBytes (m₁.atomics[li]!) = curBytes m b o len ∧
      ShapesWF (shapes m₁) ∧
      ∀ b' x, if Covers b' x (b, o, len) then tagOf (shapes m₁) b' x = some (o, len)
        else tagOf (shapes m₁) b' x = none ∨ tagOf (shapes m₁) b' x = tagOf (shapes m) b' x := by
    intro sn hm₁ hli
    have hsh : shapes m₁ = (shapes m).filter (fun s => !Hits b o len s) ++ [(b, o, len)] := by
      rw [hm₁]; simp only [shapes, Array.toList_push, List.map_append]
      rw [shapes_filter_hits]; rfl
    have hat : m₁.atomics[li]! = firstLoc m b o len := by
      rw [hm₁, hli]; simp
    obtain ⟨hwf, htag⟩ := layout_push hw hlen (sh := shapes m) (b := b) (o := o)
    refine ⟨⟨_, _, _, hm₁⟩, by rw [hm₁, hli]; simp, by rw [hat]; rfl, by rw [hat]; rfl,
      by rw [hat]; simp [firstLoc], by rw [hat]; simp [ALoc.lastBytes, firstLoc, firstMsg],
      by rw [hsh]; exact hwf, fun b' x => by rw [hsh]; exact htag b' x⟩
  cases hi : m.atomics.findIdx? (fun l => l.block == b && l.off == o) with
  | some i =>
    obtain ⟨hlt, hp, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp hi
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    have hget : m.atomics[i]! = m.atomics[i] := getElem!_pos m.atomics i hlt
    by_cases hl : m.atomics[i].len = len
    · -- the location `(b, o, len)` is there: only its messages change
      have hmem := shape_mem hlt
      obtain ⟨rfl, M, next, hpos, hback, hm₁⟩ :=
        locIdx_found' hi (by rw [hget]; exact hl) (by omega) h
      have hsz : m₁.atomics.size = m.atomics.size := by rw [hm₁]; simp
      have hat : m₁.atomics[li]! = { m.atomics[li]! with msgs := M } := by
        rw [hm₁]
        show (m.atomics.set! li _)[li]! = _
        rw [Array.set!_eq_setIfInBounds, getElem!_pos _ li (by simpa using hlt)]
        simp
      have hsh : shapes m₁ = shapes m := by
        rw [hm₁]; exact shapes_set hlt (by simp [ALoc.shape, hget])
      refine ⟨⟨_, _, _, by rw [hm₁]⟩, by simp only [hsz]; exact hlt,
        by rw [hat, hget]; exact hp.1, by rw [hat, hget]; exact hp.2, by rw [hat]; exact hpos,
        by rw [hat]; exact hback, by rw [hsh]; exact hw, fun b' x => ?_⟩
      rw [hsh]
      split
      · rename_i hc
        have := tagOf_of_mem hw hmem (b := b') (x := x) (by
          simp only [ALoc.shape, hp.1, hp.2, hl]; exact hc)
        simpa [ALoc.shape, hp.2, hl] using this
      · exact .inr rfl
    · -- a location at `(b, o)` of another length: retired
      unfold locIdx at h
      obtain ⟨a0, m0, hg, h1⟩ := MemM.bind_ok h
      obtain ⟨ha0, hm0⟩ := MemM.get_ok hg
      subst a0 m0
      simp only [hi, hget] at h1
      rw [if_pos (by simpa using hl)] at h1
      obtain ⟨hli, sn, hm₁⟩ := retireAt_eq h1
      exact hpush sn hm₁ hli
  | none =>
    unfold locIdx at h
    obtain ⟨a0, m0, hg, h1⟩ := MemM.bind_ok h
    obtain ⟨ha0, hm0⟩ := MemM.get_ok hg
    subst a0 m0
    simp only [hi] at h1
    split at h1
    · -- a location over the bytes at another offset: retired
      obtain ⟨hli, sn, hm₁⟩ := retireAt_eq h1
      exact hpush sn hm₁ hli
    · -- no location over the bytes: a new one
      rename_i hno
      obtain ⟨_, m₂, hs, h₂⟩ := MemM.bind_ok h1
      have hm₂ := MemM.set_ok hs
      obtain ⟨hli, hm₁⟩ := MemM.pure_ok h₂
      subst hm₂
      have hf : (m.atomics.filter fun l => !l.hits b o len) = m.atomics := by
        apply Array.filter_eq_self.mpr
        intro l hl
        have := Array.any_eq_false.mp (Bool.eq_false_iff.mpr hno)
        obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp hl
        have := Bool.eq_false_iff.mpr (this j hj)
        show (!(m.atomics[j]).hits b o len) = true
        cases hh : (m.atomics[j]).hits b o len
        · rfl
        · simp only [ALoc.hits, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hh
          simp only [hh.1.1.1.1, beq_self_eq_true, Bool.true_and, Bool.and_eq_false_iff,
            decide_eq_false_iff_not] at this
          omega
      exact hpush m.seen (by rw [hm₁, hf]; rfl) (by rw [hli, hf])

/-- In one thread `locIdx` never throws: a mixed-size access retires the old locations, whose
accesses all happened before it. -/
theorem locIdx_noErr_single {m : Mem} (hst : m.SingleThread) (b o len : Nat) (e : Error) :
    ((locIdx b o len).run m).run ≠ some (.error e) := by
  have hret : ((retireAt b o len).run m).run ≠ some (.error e) := by
    intro h
    unfold retireAt at h
    rcases MemM.bind_err h with h₀ | ⟨a₁, m₁, hg, h₁⟩
    · exact MemM.get_err h₀
    obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
    dsimp only at h₁
    rw [if_neg] at h₁
    · rcases MemM.bind_err h₁ with h₂ | ⟨_, m₂, hs, h₂⟩
      · exact MemM.set_err h₂
      · exact MemM.pure_err h₂
    · simp only [Bool.not_eq_true', Bool.not_eq_false, Array.all_eq_true]
      intro j hj
      simp only [Bool.or_eq_true, Bool.not_eq_true']
      right
      unfold ALoc.over
      rw [Array.all_eq_true]
      intro k hk
      simp only [Bool.or_eq_true, Bool.not_eq_true']
      right
      exact (hst.2 _ (Array.getElem_mem hk)).2
  intro h
  unfold locIdx at h
  rcases MemM.bind_err h with h₀ | ⟨a₁, m₁, hg, h₁⟩
  · exact MemM.get_err h₀
  obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
  split at h₁
  · dsimp only at h₁
    split at h₁
    · exact hret h₁
    · rcases MemM.bind_err h₁ with h₂ | ⟨_, m₂, hs, h₂⟩
      · exact MemM.set_err h₂
      · exact MemM.pure_err h₂
  · split at h₁
    · exact hret h₁
    · rcases MemM.bind_err h₁ with h₂ | ⟨_, m₂, hs, h₂⟩
      · exact MemM.set_err h₂
      · exact MemM.pure_err h₂

/-! ## Sequential choices: the newest message, a write at the end -/

theorem readOpts_zero {m : Mem} {li : Nat} (h : 0 < (m.atomics[li]!).msgs.size) :
    (readOpts m li false)[0]? = some ((m.atomics[li]!).msgs.size - 1) := by
  have hf := floorPos_lt h
  obtain ⟨k, hk⟩ : ∃ k, (m.atomics[li]!).msgs.size - floorPos m li = k + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
  unfold readOpts
  rw [← Array.getElem?_toList]
  simp [hk, List.range_succ_eq_map, List.filter_cons]

theorem writeSlots_zero {m : Mem} {li : Nat} (h : 0 < (m.atomics[li]!).msgs.size) :
    (writeSlots m li)[0]? = some (m.atomics[li]!).msgs.size := by
  have hf := floorPos_lt h
  obtain ⟨k, hk⟩ : ∃ k, (m.atomics[li]!).msgs.size - floorPos m li = k + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
  unfold writeSlots
  rw [← Array.getElem?_toList]
  simp [hk, List.range_succ_eq_map, List.filter_cons]

theorem lastBytes_eq {l : ALoc} (h : 0 < l.msgs.size) :
    (l.msgs[l.msgs.size - 1]!).bytes = ALoc.lastBytes l := by
  unfold ALoc.lastBytes
  rw [Array.back?_eq_getElem?, getElem!_pos _ _ (by omega)]
  simp [Array.getElem?_eq_getElem (show l.msgs.size - 1 < l.msgs.size by omega)]

/-! ## Helpers: the owned word, the frame, the thread -/

theorem fheap_tag {m : Mem} {l : Loc} {fc : FCell} (h : m.fheap l = some fc) :
    fc.atom = tagOf (shapes m) l.1 l.2 ∧ m.heap l = some fc.cell := by
  simp only [Mem.fheap, Option.map_eq_some_iff] at h
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨rfl, hc⟩

/-- A constraint stays true when every location keeps its place or goes. -/
theorem TagSat.mono {sh sh' : List Shape} {b x : Nat} {t : Option (Nat × Nat)}
    (h : tagOf sh' b x = none ∨ tagOf sh' b x = tagOf sh b x) (ht : TagSat sh b x t) :
    TagSat sh' b x t := by
  cases t with
  | none => trivial
  | some s =>
    unfold TagSat at ht ⊢
    rcases h with h | h
    · exact .inl h
    · rw [h]; exact ht

/-- **Retiring locations keeps every resource**: a byte keeps its location or has none, and a
tag constraint allows none (`TagSat`). -/
theorem Holds.retire {m : Mem} {r rF : Res} (hw : ShapesWF (shapes m)) (hh : Holds m r rF)
    (b o len : Nat) : Holds (m.retire b o len) r rF := by
  have e1 : (m.retire b o len).heap = m.heap := rfl
  have e3 : (m.retire b o len).kn = m.kn := rfl
  obtain ⟨hd, ⟨hm1, hm2⟩, hk, hkF, hg⟩ := hh
  refine ⟨hd, ⟨by rw [e1]; exact hm1, fun l fc hl => ?_⟩, e3 ▸ hk, e3 ▸ hkF, hg⟩
  rw [shapes_retire]
  exact TagSat.mono (tagOf_filter hw _ _ _) (hm2 l fc hl)

theorem _root_.Zig.Mem.FSeq.retire {m : Mem} (hs : m.FSeq) (b o len : Nat) :
    (m.retire b o len).FSeq :=
  ⟨⟨hs.1.1⟩, by rw [shapes_retire]; exact hs.2.1.filter _, hs.2.2⟩

/-- A byte of an owned `abytesAt`. -/
theorem abytesAt_cell {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte}
    {tg : Option (Nat × Nat)} {r : Res} (hab : abytesAt p A S K bs tg r) {b : BlockId}
    (hpb : p.block = some b) {l : Loc} (hin : l.1 = b ∧ p.off.toNat ≤ l.2 ∧ l.2 < p.off.toNat + bs.size) :
    r.heap l = some ⟨⟨bs[l.2 - p.off.toNat]!, A, S, K⟩, tg⟩ := by
  obtain ⟨-, -, b0, hb0, -, hl⟩ := hab
  rw [hpb] at hb0; cases hb0
  rw [hl l, if_pos hin]

/-- **After an atomic op on an owned word**: the memory has new bytes `bs'` there (the same for a
load) and its layout puts the location `(p.off, 8)` over them; every other byte keeps its cell,
and its location or none (`locIdx_post`). Then the memory holds the word with the new bytes and
the constraint of that location, and the frame: its cells are unchanged and its constraints stay
true (`TagSat.mono`), whatever constraint the word had before. -/
theorem holds_after {m m' : Mem} {r rF : Res} (hh : Holds m r rF) {p : Ptr} {A S : Nat}
    {K : BlockKind} {bs bs' : Array Byte} {tg : Option (Nat × Nat)} (hab : abytesAt p A S K bs tg r)
    (hsz : bs'.size = bs.size) {b : BlockId} (hpb : p.block = some b)
    (hheap : ∀ l, m'.heap l = if l.1 = b ∧ p.off.toNat ≤ l.2 ∧ l.2 < p.off.toNat + bs.size
      then some ⟨bs'[l.2 - p.off.toNat]!, A, S, K⟩ else m.heap l)
    (htag : ∀ b' x, if Covers b' x (b, p.off.toNat, bs.size)
      then tagOf (shapes m') b' x = some (p.off.toNat, bs.size)
      else tagOf (shapes m') b' x = none ∨ tagOf (shapes m') b' x = tagOf (shapes m) b' x)
    (hkn : KMono m m' ∧ KeepsExt m m') :
    ∃ r', Holds m' r' rF ∧ abytesAt p A S K bs' (some (p.off.toNat, bs.size)) r' := by
  obtain ⟨-, -, b0, hb0, h0, hl⟩ := id hab
  rw [hpb] at hb0; cases hb0
  let h' : FHeap := fun l =>
    if l.1 = b ∧ p.off.toNat ≤ l.2 ∧ l.2 < p.off.toNat + bs'.size
    then some ⟨⟨bs'[l.2 - p.off.toNat]!, A, S, K⟩, some (p.off.toNat, bs.size)⟩ else none
  -- outside the word, the resource has nothing: the union is the frame
  have hout : ∀ l, ¬ (l.1 = b ∧ p.off.toNat ≤ l.2 ∧ l.2 < p.off.toNat + bs.size) →
      r.heap l = none := fun l hc => by rw [hl l, if_neg hc]
  refine ⟨⟨h', Know.none, Ghost.unit⟩, ⟨fun l => ?_, ⟨fun l => ?_, fun l fc hfc => ?_⟩,
    Know.sub_none _, hh.knowF.trans hkn.1, by rw [← hab.2.1]; exact hh.ghost.keep hkn.2 hkn.1.size_le⟩,
    rfl, rfl, b, hpb, h0, fun l => rfl⟩
  · by_cases hc : l.1 = b ∧ p.off.toNat ≤ l.2 ∧ l.2 < p.off.toNat + bs'.size
    · right
      have : r.heap l ≠ none := by rw [hl l, if_pos (by rw [← hsz]; exact hc)]; simp
      exact (hh.disj l).resolve_left this
    · left; simp only [h']; rw [if_neg hc]
  · rw [hheap]
    by_cases hc : l.1 = b ∧ p.off.toNat ≤ l.2 ∧ l.2 < p.off.toNat + bs.size
    · have hc' : l.1 = b ∧ p.off.toNat ≤ l.2 ∧ l.2 < p.off.toNat + bs'.size := by rw [hsz]; exact hc
      rw [if_pos hc]
      simp only [FHeap.union_apply, h']
      rw [if_pos hc']; rfl
    · have hc' : ¬ (l.1 = b ∧ p.off.toNat ≤ l.2 ∧ l.2 < p.off.toNat + bs'.size) := by
        rw [hsz]; exact hc
      rw [if_neg hc, hh.heap.1 l]
      simp only [FHeap.union_apply, h', hc', ↓reduceIte, hout l hc, Option.none_or]
  · obtain ⟨x, y⟩ := l
    by_cases hc : x = b ∧ p.off.toNat ≤ y ∧ y < p.off.toNat + bs.size
    · have hc' : x = b ∧ p.off.toNat ≤ y ∧ y < p.off.toNat + bs'.size := by rw [hsz]; exact hc
      simp only [FHeap.union_apply, h'] at hfc
      rw [if_pos hc'] at hfc
      simp only [Option.some_or, Option.some.injEq] at hfc
      subst hfc
      have hcov : Covers x y (b, p.off.toNat, bs.size) := ⟨hc.1.symm, hc.2.1, hc.2.2⟩
      have := htag x y
      rw [if_pos hcov] at this
      exact .inr this
    · have hc' : ¬ (x = b ∧ p.off.toNat ≤ y ∧ y < p.off.toNat + bs'.size) := by rw [hsz]; exact hc
      have hcov : ¬ Covers x y (b, p.off.toNat, bs.size) := fun h => hc ⟨h.1.symm, h.2.1, h.2.2⟩
      simp only [FHeap.union_apply, h'] at hfc
      rw [if_neg hc', Option.none_or] at hfc
      have := htag x y
      rw [if_neg hcov] at this
      exact TagSat.mono this (hh.tagF hfc)

/-- An owned 8-aligned 64-bit word that holds `v`, with any tag constraint: what an atomic op
needs in one thread. A location over the word, of another offset or size, is retired by the op
(its accesses all happened before it); afterwards the word is an `apts`. -/
def wpts (p : Ptr) (v : BitVec 64) : FAssn := fun r => ∃ A S K bs tg,
  (A + p.off.toNat) % 8 = 0 ∧ K ≠ .constGlobal ∧ bs.size = 8 ∧ intOfBytes 64 bs = pure v ∧
  abytesAt p A S K bs tg r

theorem apts_wpts {p : Ptr} {v : BitVec 64} {r : Res} (h : apts p v r) : wpts p v r := by
  obtain ⟨A, S, K, bs, hal, hK, hsz, hv, hab⟩ := h
  exact ⟨A, S, K, bs, _, hal, hK, hsz, hv, hab⟩

/-- `abytesAt` with the constraint of the word's location is `apts`. -/
theorem apts_of {p : Ptr} {v : BitVec 64} {A S : Nat} {K : BlockKind} {bs : Array Byte} {r : Res}
    (hal : (A + p.off.toNat) % 8 = 0) (hK : K ≠ .constGlobal) (hsz : bs.size = 8)
    (hv : intOfBytes 64 bs = pure v) (hab : abytesAt p A S K bs (some (p.off.toNat, bs.size)) r) :
    apts p v r :=
  ⟨A, S, K, bs, hal, hK, hsz, hv, by rw [hsz] at hab; exact hab⟩

/-! ### Plain bytes: dropping their constraints

A resource's tag constraints can be dropped (`untag`): the memory still holds it, with the same
frame. So the atomic rules apply to bytes owned as plain (legacy, `up`) bytes, whatever their
layout (`FTriple.untag`, `wpts_of_up`). -/

/-- `r` with every byte unconstrained. -/
def Res.untag (r : Res) : Res :=
  ⟨fun l => (r.heap l).map fun fc => ⟨fc.cell, none⟩, r.know, r.gh⟩

theorem Holds.untag {m : Mem} {r rF : Res} (hh : Holds m r rF) : Holds m r.untag rF := by
  refine ⟨fun l => ?_, ⟨?_, fun l fc hl => ?_⟩, hh.know, hh.knowF, hh.ghost⟩
  · rcases hh.disj l with e | e
    · left; simp [Res.untag, e]
    · right; exact e
  · intro l; rw [hh.heap.1 l]
    simp only [FHeap.union_apply, Res.untag]
    cases r.heap l <;> rfl
  · simp only [FHeap.union_apply, Res.untag] at hl
    cases e : r.heap l with
    | some fc0 =>
      rw [e] at hl; simp only [Option.map_some, Option.some_or, Option.some.injEq] at hl
      subst hl; trivial
    | none =>
      rw [e] at hl; simp only [Option.map_none, Option.none_or] at hl
      exact hh.tagF hl

/-- **Dropping tag constraints**: a triple from the unconstrained resource is one from the
resource. -/
theorem FTriple.untag {α : Type} {P P' : FAssn} {c : MemM α} {Q : α → FAssn}
    (hp : ∀ r, P r → P' r.untag) (ht : FTriple P' c Q) : FTriple P c Q :=
  fun m r rF hh h hs => ht m r.untag rF hh.untag (hp r h) hs

/-- Plain owned bytes, unconstrained, are `abytesAt` without a constraint. -/
theorem abytesAt_untag {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte} {r : Res}
    (h : up (bytesAt p A S K bs) r) : abytesAt p A S K bs none r.untag := by
  obtain ⟨⟨b, hb, h0, hl⟩, hk, hg⟩ := h
  refine ⟨hk, hg, b, hb, h0, fun l => ?_⟩
  have := hl l
  simp only [FHeap.erase, Res.untag] at this ⊢
  split
  · rename_i hc
    rw [if_pos hc] at this
    cases e : r.heap l with
    | none => rw [e] at this; cases this
    | some fc => rw [e] at this; simp only [Option.map_some, Option.some.injEq] at this ⊢; rw [this]
  · rename_i hc
    rw [if_neg hc] at this
    cases e : r.heap l with
    | none => rfl
    | some fc => rw [e] at this; cases this

/-- **A plain owned word is a word for an atomic op** once its constraints are dropped. -/
theorem wpts_of_up {p : Ptr} {v : BitVec 64} {A S : Nat} {K : BlockKind} {bs : Array Byte} {r : Res}
    (hal : (A + p.off.toNat) % 8 = 0) (hK : K ≠ .constGlobal) (hsz : bs.size = 8)
    (hv : intOfBytes 64 bs = pure v) (h : up (bytesAt p A S K bs) r) : wpts p v r.untag :=
  ⟨A, S, K, bs, none, hal, hK, hsz, hv, abytesAt_untag h⟩

theorem singleThread_acqM {m : Mem} (h : m.SingleThread) (c : VClock) : (acqM m c).SingleThread := by
  refine ⟨by simpa [acqM] using h.1, fun e he => ?_⟩
  obtain ⟨h1, h2⟩ := h.2 e he
  refine ⟨h1, ?_⟩
  show VClock.le e.clock ((m.clocks.set! m.current
    (VClock.merge (m.clocks[m.current]!) c))[m.current]!) = true
  rw [Array.getElem!_set!_self _ _ _ h.1]
  exact VClock.le_trans h2 (VClock.le_merge_left _ _)

theorem singleThread_loadM {m : Mem} (h : m.SingleThread) (li : Nat) (ord : AtomicOrder) (msg : Msg) :
    (loadM m li ord msg).SingleThread := by
  unfold loadM
  split
  · exact singleThread_acqM h _
  · exact h

theorem singleThread_insertM {m : Mem} (h : m.SingleThread) (li p : Nat) (msg : Msg) :
    (insertM m li p msg).SingleThread := by
  unfold insertM
  dsimp only
  split
  · split <;> exact h
  · exact h

/-- A write inside a block keeps live blocks apart. -/
theorem ld_write {m m' : Mem} {b : BlockId} {blk : Block} {o : Nat} {bs : Array Byte}
    (hb : m.blocks[b]? = some blk) (hn : o + bs.size ≤ blk.bytes.size)
    (h : m'.blocks = m.blocks.set! b { blk with bytes := writeBytes blk.bytes o bs })
    (hd : m.LiveLayout) : m'.LiveLayout :=
  (LDMono.set (nb := { blk with bytes := writeBytes blk.bytes o bs }) hb id rfl
    (by simp only; rw [writeBytes_size _ _ _ hn]; exact Nat.le_refl _) h) hd

theorem kmono_of_blocks {m m' : Mem} (h : m'.blocks = m.blocks) : KMono m m' ∧ KeepsExt m m' :=
  ⟨KMono.of_blocks h, KeepsExt.of_blocks h⟩

/-- A write inside a block that is not a `const` global keeps every address, every `const`
global and every extent. -/
theorem kmono_write {m m' : Mem} {b : BlockId} {blk : Block} {o : Nat} {bs : Array Byte}
    (hb : m.blocks[b]? = some blk)
    (h : m'.blocks = m.blocks.set! b { blk with bytes := writeBytes blk.bytes o bs })
    (hn : o + bs.size ≤ blk.bytes.size) (hc : blk.kind ≠ .constGlobal) :
    KMono m m' ∧ KeepsExt m m' :=
  ⟨KMono.set (blk' := { blk with bytes := writeBytes blk.bytes o bs }) hb rfl hc h,
    KeepsExt.set (nb := { blk with bytes := writeBytes blk.bytes o bs }) hb rfl
      (by simp only; rw [writeBytes_size _ _ _ hn]) rfl h⟩

/-! ### Reading the actual extent (`FTriple.of_fix`) -/

/-- Owned bytes with their block's actual size and kind. -/
theorem abytesAt_fix {m : Mem} {r rF : Res} (hh : Holds m r rF) {p : Ptr} {A S : Nat} {K : BlockKind}
    {bs : Array Byte} {tg : Option (Nat × Nat)} (hab : abytesAt p A S K bs tg r) (hpos : 0 < bs.size) :
    ∃ S' K', K'.norm = K.norm ∧ abytesAt p A S' K' bs tg (r.fix m) := by
  obtain ⟨hk, hg, b, hb, h0, hl⟩ := hab
  have hin : (b, p.off.toNat).1 = b ∧ p.off.toNat ≤ (b, p.off.toNat).2 ∧
      (b, p.off.toNat).2 < p.off.toNat + bs.size := ⟨rfl, Nat.le_refl _, by simp; omega⟩
  have hc := hl (b, p.off.toNat)
  rw [if_pos hin] at hc
  obtain ⟨blk, hblk, -, -, -, -, hkn⟩ := hh.block hc
  refine ⟨blk.bytes.size, blk.kind, hkn.symm, hk, hg, b, hb, h0, fun l => ?_⟩
  simp only [Res.fix, FHeap.fix, hl l]
  by_cases hc' : l.1 = b ∧ p.off.toNat ≤ l.2 ∧ l.2 < p.off.toNat + bs.size
  · rw [if_pos hc', if_pos hc']; simp [hc'.1, hblk]
  · rw [if_neg hc', if_neg hc']; rfl

theorem norm_ne_constGlobal {K K' : BlockKind} (h : K'.norm = K.norm) (hK : K ≠ .constGlobal) :
    K' ≠ .constGlobal := by
  rintro rfl; cases K <;> simp_all [BlockKind.norm]

theorem wpts_fix {m : Mem} {r rF : Res} (hh : Holds m r rF) {p : Ptr} {v : BitVec 64}
    (h : wpts p v r) : wpts p v (r.fix m) := by
  obtain ⟨A, S, K, bs, tg, hal, hK, hsz, hv, hab⟩ := h
  obtain ⟨S', K', hn, hab'⟩ := abytesAt_fix hh hab (by omega)
  exact ⟨A, S', K', bs, tg, hal, norm_ne_constGlobal hn hK, hsz, hv, hab'⟩

theorem apts_fix {m : Mem} {r rF : Res} (hh : Holds m r rF) {p : Ptr} {v : BitVec 64}
    (h : apts p v r) : apts p v (r.fix m) := by
  obtain ⟨A, S, K, bs, hal, hK, hsz, hv, hab⟩ := h
  obtain ⟨S', K', hn, hab'⟩ := abytesAt_fix hh hab (by omega)
  exact ⟨A, S', K', bs, hal, norm_ne_constGlobal hn hK, hsz, hv, hab'⟩

theorem heap_of_blocks {m m' : Mem} (h : m'.blocks = m.blocks) : m'.heap = m.heap := by
  funext l; simp [Mem.heap, h]

theorem _root_.Zig.Mem.NoRevive.of_blocks {m m' : Mem} (h : m'.blocks = m.blocks) : m.NoRevive m' :=
  fun _ _ _ hl => by rwa [heap_of_blocks h] at hl

/-- A write inside block `b` revives no byte. -/
theorem _root_.Zig.Mem.NoRevive.write {m m' : Mem} {b : BlockId} {blk : Block} {o : Nat}
    {bs : Array Byte} (hb : m.blocks[b]? = some blk) (hn : o + bs.size ≤ blk.bytes.size)
    (h : m'.blocks = m.blocks.set! b { blk with bytes := writeBytes blk.bytes o bs }) :
    m.NoRevive m' :=
  Mem.NoRevive.setBlock hb h id (by simp only; rw [writeBytes_size _ _ _ hn]; exact Nat.le_refl _)
    (Nat.le_refl _)

/-! ## The step of an atomic op in a thread -/

/-- **`locIdx` over bytes that are not the frame's** is a step of the thread, whichever branch
it takes: new messages of the word's location, a new location, or a mixed-size retirement and a
new location. -/
theorem _root_.Zig.FStepIn.locIdx {hF : Heap} {m m₁ : Mem} {b o len li : Nat} (hlen : 0 < len)
    (hoff : ∀ x, o ≤ x → x < o + len → hF (b, x) = none)
    (h : ((Zig.locIdx b o len).run m).run = some (.ok (li, m₁))) : FStepIn hF m m₁ := by
  have hret : ∀ {li : Nat} {m₁ : Mem}, ((retireAt b o len).run m).run = some (.ok (li, m₁)) →
      FStepIn hF m m₁ := by
    intro li m₁ h
    unfold retireAt at h
    obtain ⟨_, _, hg, h1⟩ := MemM.bind_ok h
    obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
    dsimp only at h1
    split at h1
    · exact (MemM.throw_ok h1).elim
    · obtain ⟨_, _, hs, h2⟩ := MemM.bind_ok h1
      have := MemM.set_ok hs
      subst this
      obtain ⟨rfl, rfl⟩ := MemM.pure_ok h2
      exact (FStepIn.retire hoff).trans (FStepIn.pushLoc hlen hoff)
  -- the word's location (at `(b, o)`, of `len` bytes) is not in the frame
  have hnot : ∀ i, m.atomics.findIdx? (fun l => l.block == b && l.off == o) = some i →
      (m.atomics[i]!).len = len → ¬ (m.atomics[i]!).In hF := by
    intro i hi hl hin
    obtain ⟨hlt, hp, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp hi
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    rw [getElem!_pos m.atomics i hlt] at hl hin
    have := hin o (by rw [hp.2]; exact Nat.le_refl _) (by rw [hp.2, hl]; omega)
    have h' : hF (b, o) ≠ none := by simpa [hp.1] using this
    exact h' (hoff o (Nat.le_refl _) (by omega))
  unfold Zig.locIdx at h
  obtain ⟨a₀, m₀, hg, h1⟩ := MemM.bind_ok h
  obtain ⟨ha, hm₀⟩ := MemM.get_ok hg
  subst a₀; subst m₀
  dsimp only at h1
  split at h1
  · rename_i i hi
    split at h1
    · exact hret h1
    · rename_i hne
      have hl : (m.atomics[i]!).len = len := by simpa using hne
      split at h1
      · obtain ⟨_, _, hs, h2⟩ := MemM.bind_ok h1
        have := MemM.set_ok hs
        subst this
        obtain ⟨rfl, rfl⟩ := MemM.pure_ok h2
        exact FStepIn.setLoc (Nat.le_refl _) (hnot _ hi hl)
      · obtain ⟨_, _, hs, h2⟩ := MemM.bind_ok h1
        have := MemM.set_ok hs
        subst this
        obtain ⟨rfl, rfl⟩ := MemM.pure_ok h2
        exact FStepIn.setLoc (Nat.le_succ _) (hnot _ hi hl)
  · split at h1
    · exact hret h1
    · obtain ⟨_, _, hs, h2⟩ := MemM.bind_ok h1
      have := MemM.set_ok hs
      subst this
      obtain ⟨rfl, rfl⟩ := MemM.pure_ok h2
      exact FStepIn.pushLoc hlen hoff

/-- The bytes of an owned word are the resource's. -/
theorem abytesAt_mine {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte}
    {tg : Option (Nat × Nat)} {r : Res} (hab : abytesAt p A S K bs tg r) {b : BlockId}
    (hpb : p.block = some b) :
    ∀ x, p.off.toNat ≤ x → x < p.off.toNat + bs.size → r.heap.erase (b, x) ≠ none := by
  intro x h1 h2
  simp [FHeap.erase, abytesAt_cell hab hpb (l := (b, x)) ⟨rfl, h1, h2⟩]

/-- The bytes of an owned word are not the frame's. -/
theorem abytesAt_frame {m : Mem} {r rF : Res} (hh : Holds m r rF) {p : Ptr} {A S : Nat}
    {K : BlockKind} {bs : Array Byte} {tg : Option (Nat × Nat)} (hab : abytesAt p A S K bs tg r)
    {b : BlockId} (hpb : p.block = some b) :
    ∀ x, p.off.toNat ≤ x → x < p.off.toNat + bs.size → rF.heap.erase (b, x) = none := fun x h1 h2 =>
  (FHeap.erase_disjoint hh.disj (b, x)).resolve_left (abytesAt_mine hab hpb x h1 h2)

/-- **O3.** In a memory that holds an owned word whose tag constraint is its own location
`(p.off, 8)`, no atomic location of another offset or size overlaps it. -/
theorem abytesAt_layout {m : Mem} {r rF : Res} (hh : Holds m r rF) (hw : ShapesWF (shapes m))
    {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte} (hsz : bs.size = 8)
    (hab : abytesAt p A S K bs (some (p.off.toNat, 8)) r) {b : BlockId} (hpb : p.block = some b)
    {l : ALoc} (hl : l ∈ m.atomics) (hb : l.block = b) (h1 : p.off.toNat < l.off + l.len)
    (h2 : l.off < p.off.toNat + 8) : l.off = p.off.toNat ∧ l.len = 8 := by
  have hmem : ALoc.shape l ∈ shapes m :=
    List.mem_map.mpr ⟨l, Array.mem_toList_iff.mpr hl, rfl⟩
  -- a byte of the word under `l`: its location is `l`, which its constraint names
  obtain ⟨x, hx1, hx2, hcov⟩ : ∃ x, p.off.toNat ≤ x ∧ x < p.off.toNat + 8 ∧ Covers b x (ALoc.shape l) := by
    by_cases ho : p.off.toNat ≤ l.off
    · exact ⟨l.off, ho, h2, hb, Nat.le_refl _, by have := hw.1 _ hmem; simp only [ALoc.shape] at this ⊢; omega⟩
    · exact ⟨p.off.toNat, Nat.le_refl _, by omega, hb, by simp only [ALoc.shape]; omega, h1⟩
  have hc := abytesAt_cell hab hpb (l := (b, x)) ⟨rfl, hx1, by rw [hsz]; exact hx2⟩
  have hsat := hh.heap.2 (b, x) _ (by rw [FHeap.union_apply, hc]; rfl)
  have ht := tagOf_of_mem hw hmem hcov
  simp only [TagSat, ht, reduceCtorEq, false_or, Option.some.injEq, Prod.mk.injEq] at hsat
  simpa [ALoc.shape] using hsat

/-- `locIdx` does not throw when every location over the bytes is the one at `(b, o)` of `len`
bytes: it takes no mixed-size branch. -/
theorem locIdx_noErr_layout {m : Mem} {b o len : Nat} (hlen : 0 < len)
    (hpos : ∀ l ∈ m.atomics, 0 < l.len)
    (hlay : ∀ l ∈ m.atomics, l.block = b → o < l.off + l.len → l.off < o + len →
      l.off = o ∧ l.len = len)
    (e : Error) : ((locIdx b o len).run m).run ≠ some (.error e) := by
  intro h
  unfold locIdx at h
  rcases MemM.bind_err h with h₀ | ⟨a₁, m₁, hg, h₁⟩
  · exact MemM.get_err h₀
  obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
  split at h₁
  · rename_i i hi
    obtain ⟨hlt, hp, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp hi
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    have hmem := Array.getElem_mem hlt
    have hl := (hlay _ hmem hp.1 (by rw [hp.2]; have := hpos _ hmem; omega)
      (by rw [hp.2]; omega)).2
    dsimp only at h₁
    split at h₁
    · rename_i hne
      rw [getElem!_pos _ i hlt, hl] at hne
      simp at hne
    · rcases MemM.bind_err h₁ with h₂ | ⟨_, m₂, hs, h₂⟩
      · exact MemM.set_err h₂
      · exact MemM.pure_err h₂
  · rename_i hi
    split at h₁
    · rename_i hany
      obtain ⟨j, hj, hpj⟩ := Array.any_eq_true.mp hany
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hpj
      have hjo := (hlay _ (Array.getElem_mem hj) hpj.1.1 hpj.1.2 hpj.2).1
      have := Array.findIdx?_eq_none_iff.mp hi _ (Array.getElem_mem hj)
      simp [hpj.1.1, hjo] at this
    · rcases MemM.bind_err h₁ with h₂ | ⟨_, m₂, hs, h₂⟩
      · exact MemM.set_err h₂
      · exact MemM.pure_err h₂

/-- **`locIdx` at an owned word does not throw** after the op records its access, if the run is
sequential (a mixed-size access retires) or the word's tag constraint is its own location (no
mixed-size access). Concurrently, a word of another constraint can throw
(`tests/roadmap/sep-full/AtomicRetireCX.lean`). -/
theorem locIdx_noErr_word {m : Mem} {r rF : Res} (hh : Holds m r rF) (hw : ShapesWF (shapes m))
    {p : Ptr} {b : BlockId} (hpb : p.block = some b)
    (hmix : m.SingleThread ∨ ∃ A S K bs, bs.size = 8 ∧ abytesAt p A S K bs (some (p.off.toNat, 8)) r)
    (k : AccessKind) (e : Error) :
    ((locIdx b p.off.toNat 8).run (m.recordAt b p.off.toNat 8 k)).run ≠ some (.error e) := by
  rcases hmix with hst | ⟨A, S, K, bs, hsz, hab⟩
  · exact locIdx_noErr_single (singleThread_recordAt hst _ _ _ _) _ _ _ e
  · exact locIdx_noErr_layout (m := m.recordAt b p.off.toNat 8 k) (by decide)
      (fun l hl => hw.1 _ (List.mem_map.mpr ⟨l, Array.mem_toList_iff.mpr hl, rfl⟩))
      (fun l hl hb h1 h2 => abytesAt_layout hh hw hsz hab hpb hl hb h1 h2) e

/-- The run of a step of the current thread on an owned word, read sequentially: from the
analysis of the run (premise `h`, for a memory that runs one thread), the sequential triple. -/
theorem FTriple.of_step {α : Type} {P : FAssn} {c : MemM α} {Q : α → FAssn}
    (hP : ∀ m r rF, Holds m r rF → P r → P (r.fix m))
    (h : ∀ m r rF, Holds m r rF → Exact m r → Exact m rF → P r → m.current < m.clocks.size →
      m.Owns m.current r.heap.erase → ShapesWF (shapes m) → m.LiveLayout → m.SingleThread →
      (∀ e, (c.run m).run ≠ some (.error e)) ∧
      ∀ v m', (c.run m).run = some (.ok (v, m')) → ∃ r', Holds m' r' rF ∧ Q v r' ∧
        ShapesWF (shapes m') ∧ m'.LiveLayout ∧ FStepIn rF.heap.erase m m' ∧ m.NoRevive m') :
    FTriple P c Q := by
  refine FTriple.of_fix hP fun m r rF hh hxr hxF hp hs => ?_
  obtain ⟨hne, hok⟩ := h m r rF hh hxr hxF hp hs.1.single.1 (hs.1.single.owns _) hs.2.1 hs.2.2
    hs.1.single
  match e : (c.run m).run with
  | none => trivial
  | some (.error er) => exact (hne er e).elim
  | some (.ok (v, m')) =>
    obtain ⟨r', hh', hq, hw', hl', hst, -⟩ := hok v m' e
    exact ⟨r', hh', hq, ⟨hs.1.single.fstep hst⟩, hw', hl'⟩

/-- The run of a step of the current thread on an owned word, in a thread: from the analysis of
the run (premise `h`, for every memory where the thread owns the precondition), the thread
triple. -/
theorem FTTriple.of_step {α : Type} {P : FAssn} {c : MemM α} {Q : α → FAssn}
    (hP : ∀ m r rF, Holds m r rF → P r → P (r.fix m))
    (h : ∀ m r rF, Holds m r rF → Exact m r → Exact m rF → P r → m.current < m.clocks.size →
      m.Owns m.current r.heap.erase → ShapesWF (shapes m) → m.LiveLayout →
      (∀ e, (c.run m).run ≠ some (.error e)) ∧
      ∀ v m', (c.run m).run = some (.ok (v, m')) → ∃ r', Holds m' r' rF ∧ Q v r' ∧
        ShapesWF (shapes m') ∧ m'.LiveLayout ∧ FStepIn rF.heap.erase m m' ∧ m.NoRevive m') :
    FTTriple P c Q := by
  refine FTTriple.of_fix hP fun m r rF hh hxr hxF hp hc ho => ?_
  obtain ⟨hne, hok⟩ := h m r rF hh hxr hxF hp hc.1 ho hc.2.1 hc.2.2
  match e : (c.run m).run with
  | none => trivial
  | some (.error er) => exact (hne er e).elim
  | some (.ok (v, m')) =>
    obtain ⟨r', hh', hq, hw', hl', hst, hnr⟩ := hok v m' e
    exact ⟨r', hh', hq, ⟨hst.cur hc.1, hw', hl'⟩, owns_step hh ho hst hnr.revivesOwned hh', hst⟩

/-! ## The rules -/

theorem intSize_64 : intSize 64 = 8 := by decide

theorem access_inj {x y : BlockId × Block × Nat} (h : (pure x : Result _) = pure y) : x = y := by
  have := congrArg ExceptT.run h
  simpa [pure, ExceptT.pure, ExceptT.mk, ExceptT.run] using this

/-- An `apts` word: its bytes, with their own location as the tag constraint (`locIdx_noErr_word`). -/
theorem apts_own {p : Ptr} {v : BitVec 64} {r : Res} (h : apts p v r) :
    ∃ A S K bs, bs.size = 8 ∧ abytesAt p A S K bs (some (p.off.toNat, 8)) r :=
  let ⟨A, S, K, bs, _, _, hsz, _, hab⟩ := h; ⟨A, S, K, bs, hsz, hab⟩

/-- The step of an atomic op on an owned word: the access to it records the current thread's
access to its bytes, which are not the frame's. -/
theorem fstep_record {m : Mem} {r rF : Res} (hd : FHeap.Disjoint r.heap rF.heap)
    (hc : m.current < m.clocks.size)
    {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte} {tg : Option (Nat × Nat)}
    (hab : abytesAt p A S K bs tg r) (hsz : bs.size = 8) {b : BlockId} (hpb : p.block = some b)
    {blk : Block} (hblk : m.blocks[b]? = some blk) (hKb : blk.kind = K) (hK : K ≠ .constGlobal)
    (k : AccessKind) : FStepIn rF.heap.erase m (m.recordAt b p.off.toNat 8 k) :=
  FStepIn.recordAt hc (FHeap.erase_disjoint hd)
    (fun x h1 h2 => abytesAt_mine hab hpb x h1 (by rw [hsz]; exact h2))
    (Array.getElem?_eq_some_iff.mp hblk).1 fun _ ⟨blk', e1, e2⟩ => by
      rw [show (m.blocks[b]? : Option Block) = some blk from hblk] at e1
      cases e1; exact hK (hKb ▸ e2)

/-- The bytes of an owned word are not the frame's (`FStepIn.locIdx`). -/
theorem frame_off {m : Mem} {r rF : Res} (hh : Holds m r rF) {p : Ptr} {A S : Nat}
    {K : BlockKind} {bs : Array Byte} {tg : Option (Nat × Nat)} (hab : abytesAt p A S K bs tg r)
    (hsz : bs.size = 8) {b : BlockId} (hpb : p.block = some b) :
    ∀ x, p.off.toNat ≤ x → x < p.off.toNat + 8 → rF.heap.erase (b, x) = none :=
  fun x h1 h2 => abytesAt_frame hh hab hpb x h1 (by rw [hsz]; exact h2)

/-- The block's kind is the owned word's (its cells name it). -/
theorem abytesAt_kind {m : Mem} {r : Res} (hxr : Exact m r) {p : Ptr} {A S : Nat}
    {K : BlockKind} {bs : Array Byte} {tg : Option (Nat × Nat)} (hab : abytesAt p A S K bs tg r)
    (hsz : bs.size = 8) {b : BlockId} (hpb : p.block = some b) {blk : Block}
    (hblk : m.blocks[b]? = some blk) : blk.kind = K ∧ blk.kind.mappedLo ≤ p.off.toNat := by
  obtain ⟨-, -, b0, hb0, -, hl0⟩ := id hab
  rw [hpb] at hb0; cases hb0
  have hr := hl0 (b, p.off.toNat)
  rw [if_pos ⟨rfl, Nat.le_refl _, by omega⟩] at hr
  obtain ⟨blk', hblk', _, _, hc⟩ := Mem.heap_some (hxr _ _ hr)
  obtain ⟨blk'', hblk'', hlo⟩ := Mem.heap_some_lo (hxr _ _ hr)
  rw [hblk] at hblk' hblk''; cases hblk'; cases hblk''
  simp only [Cell.mk.injEq] at hc
  exact ⟨hc.2.2.2.symm, hlo⟩

/-- **The run of an atomic load** of an owned word (choice 0): it reads the word, and afterwards
the word is an `apts`; the step does not throw when the run is sequential or the word is an
`apts` (`locIdx_noErr_word`). -/
theorem atomicLoad_run (p : Ptr) (v : BitVec 64) (ord : AtomicOrder) {m : Mem} {r rF : Res}
    (hh : Holds m r rF) (hxr : Exact m r) (hxF : Exact m rF) (hp : wpts p v r)
    (hc : m.current < m.clocks.size) (ho : m.Owns m.current r.heap.erase)
    (hwf : ShapesWF (shapes m)) (hld : m.LiveLayout)
    (hmix : m.SingleThread ∨ ∃ A S K bs, bs.size = 8 ∧ abytesAt p A S K bs (some (p.off.toNat, 8)) r) :
    (∀ e, ((Zig.atomicLoadAt (n := 64) 0 ord 8 p).run m).run ≠ some (.error e)) ∧
    ∀ w m', ((Zig.atomicLoadAt (n := 64) 0 ord 8 p).run m).run = some (.ok (w, m')) →
      ∃ r', Holds m' r' rF ∧ (⟪w = v⟫ ⋆ apts p v) r' ∧
        ShapesWF (shapes m') ∧ m'.LiveLayout ∧ FStepIn rF.heap.erase m m' ∧ m.NoRevive m' := by
  obtain ⟨A, S, K, bs, tg, hal, hK, hsz, hv, hab⟩ := hp
  have hm := hh.heap_exact hxr hxF
  obtain ⟨b, blk, hacc, hblk, hA, hS, hx⟩ := bytesAt_access (q := p) (k := 0) (n := 8) (a := 8)
    (abytesAt_bytesAt hab) hm (by simp [Ptr.add]) (by decide) (by omega) (by simpa using hal)
  have hpb := (access_eq hacc).1
  have hKb := (abytesAt_kind hxr hab hsz hpb hblk).1
  have hacc8 : m.access p (intSize 64) 8 = pure (b, blk, p.off.toNat) := by
    rw [intSize_64]; simpa using hacc
  have hcur : ∀ m₀ : Mem, m₀.blocks = m.blocks → curBytes m₀ b p.off.toNat 8 = bs := by
    intro m₀ e
    simp only [curBytes, e, hblk, Option.map_some, Option.getD_some]
    have : bs.extract 0 8 = bs := by rw [← hsz]; simp
    simpa [this] using hx
  have hlocok := locIdx_noErr_word hh hwf hpb hmix .atomicRead
  have hnr : NoRace m b p.off.toNat (intSize 64) .atomicRead := ho.noRace fun x h1 h2 =>
    abytesAt_mine hab hpb x h1 (by rw [hsz]; rw [intSize_64] at h2; exact h2)
  -- A successful preparation reads the newest message, which has the owned bytes.
  have hnewest : ∀ li m₁, ((locIdx b p.off.toNat (intSize 64)).run
      (m.recordAt b p.off.toNat (intSize 64) .atomicRead)).run = some (.ok (li, m₁)) →
      (readOpts m₁ li false)[0]? = some ((m₁.atomics[li]!).msgs.size - 1) ∧
      ((m₁.atomics[li]!).msgs[(m₁.atomics[li]!).msgs.size - 1]!).bytes = bs ∧
      (∃ a sn next, m₁ = { m.recordAt b p.off.toNat 8 .atomicRead with atomics := a, seen := sn, nextMsg := next }) ∧
      ShapesWF (shapes m₁) ∧
      ∀ b' x, if Covers b' x (b, p.off.toNat, 8) then tagOf (shapes m₁) b' x = some (p.off.toNat, 8)
        else tagOf (shapes m₁) b' x = none ∨ tagOf (shapes m₁) b' x = tagOf (shapes m) b' x := by
    intro li m₁ hl
    rw [intSize_64] at hl
    have := locIdx_post (m := m.recordAt b p.off.toNat 8 .atomicRead) hwf (by decide) (by rw [hcur (m.recordAt b p.off.toNat 8 .atomicRead) rfl, hsz]) hl
    obtain ⟨hupd, -, -, -, hpos, hlast, hwf, htag⟩ := this
    refine ⟨readOpts_zero hpos, by rw [lastBytes_eq hpos, hlast, hcur (m.recordAt b p.off.toNat 8 .atomicRead) rfl], ?_⟩
    exact ⟨hupd, hwf, htag⟩
  refine ⟨fun e hrun => ?_, fun w m' hrun => ?_⟩
  · refine atomicLoadAt_noErr (fun e' => ?_) (fun li opts m₁ hp => ?_) e hrun
    · exact loadPrep_noErr (by simpa using hacc8) hnr
        (fun e'' => by rw [intSize_64]; exact hlocok e'') e'
    · obtain ⟨b', blk', o', ha', -, hl, rfl⟩ := loadPrep_ok hp
      simp only [Bool.false_eq_true, ↓reduceIte] at ha'
      obtain ⟨rfl, rfl, rfl⟩ := access_inj (hacc8.symm.trans ha')
      obtain ⟨hz, hbytes, -⟩ := hnewest li m₁ hl
      exact ⟨_, hz, v, by rw [hbytes, hv]; rfl⟩
  ·
      obtain ⟨b', blk', o', li, m₁, pos, ha', -, hl, hpos, hw, hm'⟩ := atomicLoadAt_ok hrun
      obtain ⟨rfl, rfl, rfl⟩ := access_inj (hacc8.symm.trans ha')
      obtain ⟨hz, hbytes, ⟨a, sn, next, hm₁⟩, hwf, htag⟩ := hnewest li m₁ hl
      rw [hz] at hpos; cases hpos
      have hwv : w = v := by
        rw [hbytes, hv] at hw
        simpa [pure, ExceptT.pure, ExceptT.mk, ExceptT.run] using hw.symm
      subst hm'
      have hblocks : (loadM m₁ li ord ((m₁.atomics[li]!).msgs[(m₁.atomics[li]!).msgs.size - 1]!)).blocks
          = m.blocks := by
        unfold loadM acqM observeM; split <;> simp [hm₁, Mem.recordAt]
      have hshapes : shapes (loadM m₁ li ord
          ((m₁.atomics[li]!).msgs[(m₁.atomics[li]!).msgs.size - 1]!)) = shapes m₁ := by
        unfold loadM acqM observeM; split <;> rfl
      obtain ⟨r', hh', hab'⟩ := holds_after hh hab (bs' := bs) rfl hpb
        (fun l => by
          rw [heap_of_blocks hblocks]
          split
          · rename_i hin
            exact hxr _ _ (abytesAt_cell hab hpb hin)
          · rfl)
        (fun b' x => by rw [hshapes, hsz]; exact htag b' x) (kmono_of_blocks hblocks)
      have hs0 := fstep_record hh.disj hc hab hsz hpb hblk hKb hK .atomicRead
      have hs1 := FStepIn.locIdx (by decide) (frame_off hh hab hsz hpb) (by rw [intSize_64] at hl; exact hl)
      refine ⟨r', hh', sep_lift.mpr ⟨hwv, apts_of hal hK hsz hv hab'⟩, by rw [hshapes]; exact hwf,
        LDMono.of_blocks hblocks hld,
        hs0.trans (hs1.trans (FStepIn.loadM ((hs0.trans hs1).cur hc) _ _ _)),
        Mem.NoRevive.of_blocks hblocks⟩

/-- **Atomic load** of an owned word, whatever its layout (sequential: choice 0); afterwards the
word is an `apts`. -/
theorem FTriple.atomicLoadW (p : Ptr) (v : BitVec 64) (ord : AtomicOrder) :
    FTriple (wpts p v) (Zig.atomicLoadAt (n := 64) 0 ord 8 p)
      (fun w => ⟪w = v⟫ ⋆ apts p v) :=
  FTriple.of_step (fun _ _ _ hh hp => wpts_fix hh hp) fun _ _ _ hh hxr hxF hp hc ho hw hl hst =>
    atomicLoad_run p v ord hh hxr hxF hp hc ho hw hl (.inl hst)

/-- **Atomic load** of an `apts` word in a thread (choice 0: the newest message, which the thread
reads since it owns the word). -/
theorem FTTriple.atomicLoad (p : Ptr) (v : BitVec 64) (ord : AtomicOrder) :
    FTTriple (apts p v) (Zig.atomicLoadAt (n := 64) 0 ord 8 p) (fun w => ⟪w = v⟫ ⋆ apts p v) :=
  FTTriple.of_step (fun _ _ _ hh hp => apts_fix hh hp) fun _ _ _ hh hxr hxF hp hc ho hw hl =>
    atomicLoad_run p v ord hh hxr hxF (apts_wpts hp) hc ho hw hl (.inr (apts_own hp))

/-- **Atomic load** of an `apts` word (sequential: choice 0). -/
theorem FTriple.atomicLoad (p : Ptr) (v : BitVec 64) (ord : AtomicOrder) :
    FTriple (apts p v) (Zig.atomicLoadAt (n := 64) 0 ord 8 p) (fun w => ⟪w = v⟫ ⋆ apts p v) :=
  (FTTriple.atomicLoad p v ord).toFTriple

theorem shapes_insertM_last {m : Mem} {li : Nat} {msg : Msg} {blk : Block}
    (hb : m.blocks[(m.atomics[li]!).block]? = some blk) (hli : li < m.atomics.size) :
    shapes (insertM m li (m.atomics[li]!).msgs.size msg) = shapes m := by
  rw [insertM_last hb]
  exact shapes_set hli (by rw [getElem!_pos m.atomics li hli]; rfl)

/-- The word's location after `locIdx` is not in a frame that has none of the word's bytes. -/
theorem loc_not_in {m₁ : Mem} {hF : Heap} {li b o : Nat} (hw : ShapesWF (shapes m₁))
    (hli : li < m₁.atomics.size) (hb : (m₁.atomics[li]!).block = b)
    (ho : (m₁.atomics[li]!).off = o) (hoff : hF (b, o) = none) : ¬ (m₁.atomics[li]!).In hF := by
  intro hin
  have hpos := hw.1 _ (shape_mem hli)
  rw [← getElem!_pos m₁.atomics li hli] at hpos
  simp only [ALoc.shape] at hpos
  have := hin (m₁.atomics[li]!).off (Nat.le_refl _) (by omega)
  rw [hb, ho] at this
  exact this hoff

/-- **A write of the newest message of an owned word** (a store, an RMW, a successful `cmpxchg`
after its location step `m₀`, and for an RMW an acquire: `M₂`): the memory holds the word with
the message's bytes, under its own location, and the frame as it was; the step is one of the
thread outside the frame and revives no byte. -/
theorem write_newest {m m₀ M₂ : Mem} {r rF : Res} (hh : Holds m r rF) {p : Ptr} {A S : Nat}
    {K : BlockKind} {bs : Array Byte} {tg : Option (Nat × Nat)} (hab : abytesAt p A S K bs tg r)
    (hsz : bs.size = 8) (hK : K ≠ .constGlobal) {b : BlockId} {blk : Block}
    (hpb : p.block = some b) (hblk : m.blocks[b]? = some blk) (hlive : blk.live = true)
    (hlo : blk.kind.mappedLo ≤ p.off.toNat) (hfit : p.off.toNat + 8 ≤ blk.bytes.size)
    (hA : blk.addr = A) (hS : blk.bytes.size = S) (hKb : blk.kind = K)
    {li : Nat} (hli : li < m₀.atomics.size) (hb : (m₀.atomics[li]!).block = b)
    (ho : (m₀.atomics[li]!).off = p.off.toNat) (hwf : ShapesWF (shapes m₀))
    (htag : ∀ b' x, if Covers b' x (b, p.off.toNat, 8) then tagOf (shapes m₀) b' x = some (p.off.toNat, 8)
      else tagOf (shapes m₀) b' x = none ∨ tagOf (shapes m₀) b' x = tagOf (shapes m) b' x)
    (hld : m.LiveLayout) (hat : M₂.atomics = m₀.atomics) (hbl : M₂.blocks = m.blocks)
    (hs₂ : FStepIn rF.heap.erase m M₂) (msg : Msg) (hmb : msg.bytes.size = 8) :
    ∃ r', Holds (observeM (insertM M₂ li (M₂.atomics[li]!).msgs.size msg) li M₂.nextMsg) r' rF ∧
      abytesAt p A S K msg.bytes (some (p.off.toNat, 8)) r' ∧
      ShapesWF (shapes (observeM (insertM M₂ li (M₂.atomics[li]!).msgs.size msg) li M₂.nextMsg)) ∧
      (observeM (insertM M₂ li (M₂.atomics[li]!).msgs.size msg) li M₂.nextMsg).LiveLayout ∧
      FStepIn rF.heap.erase m (observeM (insertM M₂ li (M₂.atomics[li]!).msgs.size msg) li M₂.nextMsg) ∧
      m.NoRevive (observeM (insertM M₂ li (M₂.atomics[li]!).msgs.size msg) li M₂.nextMsg) := by
  have hb₂ : M₂.blocks[(M₂.atomics[li]!).block]? = some blk := by rw [hat, hb, hbl]; exact hblk
  have hins := insertM_last (li := li) (msg := msg) hb₂
  have hblocks : (observeM (insertM M₂ li (M₂.atomics[li]!).msgs.size msg) li M₂.nextMsg).blocks =
      m.blocks.set! b { blk with bytes := writeBytes blk.bytes p.off.toNat msg.bytes } := by
    unfold observeM; rw [hins, hat, hb, ho, hbl]
  have hshapes : shapes (observeM (insertM M₂ li (M₂.atomics[li]!).msgs.size msg) li M₂.nextMsg) =
      shapes m₀ := by
    show shapes (insertM M₂ li (M₂.atomics[li]!).msgs.size msg) = _
    rw [shapes_insertM_last hb₂ (by rw [hat]; exact hli)]
    simp [shapes, hat]
  have hwr := Mem.heap_write (m := m) (o := p.off.toNat) hblk hlive (bs := msg.bytes)
    (by rw [hmb]; omega) hlo
  obtain ⟨r', hh', hab'⟩ := holds_after hh hab (bs' := msg.bytes) (by rw [hmb, hsz]) hpb
    (fun l => by
      rw [heap_of_blocks (m := m.write b blk p.off.toNat msg.bytes) hblocks, hwr, hmb, hsz, hA, hS,
        hKb])
    (fun b' x => by rw [hshapes, hsz]; exact htag b' x)
    (kmono_write hblk hblocks (by rw [hmb]; omega) (hKb ▸ hK))
  have hnot := loc_not_in (hF := rF.heap.erase) hwf hli hb ho
    (frame_off hh hab hsz hpb _ (Nat.le_refl _) (by omega))
  refine ⟨r', hh', by rw [hsz] at hab'; exact hab', by rw [hshapes]; exact hwf,
    ld_write hblk (by rw [hmb]; omega) hblocks hld,
    hs₂.trans ((FStepIn.insertLast hb₂ (by rw [hat]; exact hnot)).trans (FStepIn.observe _ _)),
    Mem.NoRevive.write hblk (by rw [hmb]; omega) hblocks⟩

/-- **The run of an atomic store** to an owned word (choice 0: the write goes at the end);
afterwards the word is an `apts` of the new value. -/
theorem atomicStore_run (p : Ptr) (v w : BitVec 64) (ord : AtomicOrder) {m : Mem} {r rF : Res}
    (hh : Holds m r rF) (hxr : Exact m r) (hxF : Exact m rF) (hp : wpts p v r)
    (hc : m.current < m.clocks.size) (ho : m.Owns m.current r.heap.erase)
    (hwf : ShapesWF (shapes m)) (hld : m.LiveLayout)
    (hmix : m.SingleThread ∨ ∃ A S K bs, bs.size = 8 ∧ abytesAt p A S K bs (some (p.off.toNat, 8)) r) :
    (∀ e, ((Zig.atomicStoreAt 0 ord 8 p w).run m).run ≠ some (.error e)) ∧
    ∀ u m', ((Zig.atomicStoreAt 0 ord 8 p w).run m).run = some (.ok (u, m')) →
      ∃ r', Holds m' r' rF ∧ apts p w r' ∧
        ShapesWF (shapes m') ∧ m'.LiveLayout ∧ FStepIn rF.heap.erase m m' ∧ m.NoRevive m' := by
  obtain ⟨A, S, K, bs, tg, hal, hK, hsz, -, hab⟩ := hp
  have hm := hh.heap_exact hxr hxF
  obtain ⟨b, blk, hacc, hblk, hA, hS, -⟩ := bytesAt_access (q := p) (k := 0) (n := 8) (a := 8)
    (abytesAt_bytesAt hab) hm (by simp [Ptr.add]) (by decide) (by omega) (by simpa using hal)
  obtain ⟨hpb, -, hlive, h0, hfit, -, -⟩ := access_eq hacc
  obtain ⟨hKb, hlo⟩ := abytesAt_kind hxr hab hsz hpb hblk
  have haccW8 : m.accessW p (intSize 64) 8 = pure (b, blk, p.off.toNat) := by
    rw [intSize_64]; unfold Mem.accessW; rw [hacc]
    simp [hKb, hK, pure_bind]
  have hcur : (curBytes (m.recordAt b p.off.toNat 8 .atomicWrite) b p.off.toNat 8).size = 8 := by
    simp only [curBytes, Mem.recordAt, hblk, Option.map_some, Option.getD_some, Array.size_extract]
    omega
  have hlocok := locIdx_noErr_word hh hwf hpb hmix .atomicWrite
  have hnr : NoRace m b p.off.toNat (intSize 64) .atomicWrite := ho.noRace fun x h1 h2 =>
    abytesAt_mine hab hpb x h1 (by rw [hsz]; rw [intSize_64] at h2; exact h2)
  have hpost : ∀ li m₁, ((locIdx b p.off.toNat (intSize 64)).run
      (m.recordAt b p.off.toNat (intSize 64) .atomicWrite)).run = some (.ok (li, m₁)) →
      (writeSlots m₁ li)[0]? = some (m₁.atomics[li]!).msgs.size ∧
      li < m₁.atomics.size ∧ (m₁.atomics[li]!).block = b ∧ (m₁.atomics[li]!).off = p.off.toNat ∧
      (∃ a sn next, m₁ = { m.recordAt b p.off.toNat 8 .atomicWrite with atomics := a, seen := sn, nextMsg := next }) ∧
      ShapesWF (shapes m₁) ∧
      ∀ b' x, if Covers b' x (b, p.off.toNat, 8) then tagOf (shapes m₁) b' x = some (p.off.toNat, 8)
        else tagOf (shapes m₁) b' x = none ∨ tagOf (shapes m₁) b' x = tagOf (shapes m) b' x := by
    intro li m₁ hl
    rw [intSize_64] at hl
    obtain ⟨hupd, hli, hb, ho, hpos, -, hwf, htag⟩ :=
      locIdx_post (m := m.recordAt b p.off.toNat 8 .atomicWrite) hwf (by decide) hcur hl
    exact ⟨writeSlots_zero hpos, hli, hb, ho, hupd, hwf, htag⟩
  refine ⟨fun e hrun => ?_, fun u m' hrun => ?_⟩
  · refine atomicStoreAt_noErr (fun e' => ?_) (fun li slots m₁ hp => ?_) e hrun
    · exact storePrep_noErr haccW8 hnr (fun e'' => by rw [intSize_64]; exact hlocok e'') e'
    · obtain ⟨b', blk', o', ha', -, hl, rfl⟩ := storePrep_ok hp
      obtain ⟨rfl, rfl, rfl⟩ := access_inj (haccW8.symm.trans ha')
      obtain ⟨hz, -⟩ := hpost li m₁ hl
      exact (Array.getElem?_eq_some_iff.mp hz).1
  ·
      obtain ⟨b', blk', o', li, m₁, slot, ha', -, hl, hslot, hm'⟩ := atomicStoreAt_ok hrun
      obtain ⟨rfl, rfl, rfl⟩ := access_inj (haccW8.symm.trans ha')
      obtain ⟨hz, hli, hb, ho, ⟨a, sn, next, hm₁⟩, hwf, htag⟩ := hpost li m₁ hl
      rw [hz] at hslot; cases hslot
      have hb₁ : m₁.blocks[(m₁.atomics[li]!).block]? = some blk := by
        rw [hb, hm₁]; exact hblk
      subst hm'
      have hs0 := fstep_record hh.disj hc hab hsz hpb hblk hKb hK .atomicWrite
      have hs1 := FStepIn.locIdx (by decide) (frame_off hh hab hsz hpb)
        (by rw [intSize_64] at hl; exact hl)
      obtain ⟨r', hh', hab', hw', hl', hst, hnv⟩ := write_newest (M₂ := m₁) hh hab hsz hK hpb hblk
        hlive hlo (by omega) hA hS hKb hli hb ho hwf htag hld rfl (by rw [hm₁]; rfl) (hs0.trans hs1)
        (storeMsg m₁ ord w) (LawfulEnc.size_encode w)
      exact ⟨r', hh', apts_of hal hK (LawfulEnc.size_encode w) (LawfulEnc.decode_encode w)
        (by rw [LawfulEnc.size_encode w]; exact hab'), hw', hl', hst, hnv⟩

/-- **Atomic store** to an owned word, whatever its layout (sequential: the write goes at the
end). -/
theorem FTriple.atomicStoreW (p : Ptr) (v w : BitVec 64) (ord : AtomicOrder) :
    FTriple (wpts p v) (Zig.atomicStoreAt 0 ord 8 p w) (fun _ => apts p w) :=
  FTriple.of_step (fun _ _ _ hh hp => wpts_fix hh hp) fun _ _ _ hh hxr hxF hp hc ho hw hl hst =>
    atomicStore_run p v w ord hh hxr hxF hp hc ho hw hl (.inl hst)

/-- **Atomic store** to an `apts` word in a thread (choice 0: the write goes at the end). -/
theorem FTTriple.atomicStore (p : Ptr) (v w : BitVec 64) (ord : AtomicOrder) :
    FTTriple (apts p v) (Zig.atomicStoreAt 0 ord 8 p w) (fun _ => apts p w) :=
  FTTriple.of_step (fun _ _ _ hh hp => apts_fix hh hp) fun _ _ _ hh hxr hxF hp hc ho hw hl =>
    atomicStore_run p v w ord hh hxr hxF (apts_wpts hp) hc ho hw hl (.inr (apts_own hp))

/-- **Atomic store** to an `apts` word. -/
theorem FTriple.atomicStore (p : Ptr) (v w : BitVec 64) (ord : AtomicOrder) :
    FTriple (apts p v) (Zig.atomicStoreAt 0 ord 8 p w) (fun _ => apts p w) :=
  (FTTriple.atomicStore p v w ord).toFTriple

/-- **O3.** A memory that holds a word as `apts` has no atomic location of another offset or size
over it (`docs/alloc-page.md`'s `odd` memory, with a 4-byte location at the page allocator's
hint, holds no `apts` of the hint, though its heap is that of the program start). -/
theorem apts_layout {m : Mem} {r rF : Res} (hh : Holds m r rF) (hs : m.FSeq) {p : Ptr}
    {v : BitVec 64} (hp : apts p v r) {b : BlockId} (hpb : p.block = some b) {l : ALoc}
    (hl : l ∈ m.atomics) (hb : l.block = b) (h1 : p.off.toNat < l.off + l.len)
    (h2 : l.off < p.off.toNat + 8) : l.off = p.off.toNat ∧ l.len = 8 :=
  let ⟨_, _, _, _, hsz, hab⟩ := apts_own hp
  abytesAt_layout hh hs.2.1 hsz hab hpb hl hb h1 h2

end Full
end Zig
