import ZigLean.Sep.Full.Triple

/-!
# Atomic points-to (prototype, `docs/sep-full-state.md`)

Rules for `atomic_load` and `atomic_store` of a 64-bit word that the precondition owns
(`ZigLean/Sep/Full/Res.lean`), in a sequential run (choice `0`, the only option of one thread:
the newest message, a write at the end):

* in one thread the op never throws (`locIdx_noErr_single`): a location over the bytes of
  another offset or size is retired, since every access to it happened before
  (`ZigLean/Mem/Thread.lean`, `retireAt`);
* the op puts a location only over the owned bytes (`locIdx_post`), and a retired location
  leaves its other bytes without one, so every frame constraint stays true (`holds_after`;
  atomic tags are constraints, `docs/sep-full-state.md` §Atomic tags are constraints);
* in a sequential run the newest message has the block's bytes (`locIdx` adds a message when they
  differ, a new location starts with them), so the op reads and writes the owned bytes like a
  plain access.

The rules take any owned word (`wpts`, whatever its constraint) and leave an `apts`; the `apts`
versions are corollaries. `FTriple.untag` and `wpts_of_up` apply them to bytes owned as plain
(`up`) bytes.
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
def Hits (b o len : Nat) (s : Shape) : Bool := s.1 == b && o < s.2.1 + s.2.2 && s.2.1 < o + len

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
    simp [Hits, e1, e2, e3] at h2
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
        unfold ALoc.hits; rw [this]; rfl
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
    Know.sub_none _, hh.knowF.trans hkn.1, by rw [← hab.2.1]; exact hh.ghost.keep hkn.2⟩,
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
  LDMono.set (nb := { blk with bytes := writeBytes blk.bytes o bs }) hb id rfl
    (by simp only; rw [writeBytes_size _ _ _ hn]; exact Nat.le_refl _) h hd

theorem kmono_of_blocks {m m' : Mem} (h : m'.blocks = m.blocks) : KMono m m' ∧ KeepsExt m m' :=
  ⟨KMono.of_blocks h, KeepsExt.of_blocks h⟩

/-- A write inside a block keeps every address and every extent. -/
theorem kmono_write {m m' : Mem} {b : BlockId} {blk : Block} {o : Nat} {bs : Array Byte}
    (hb : m.blocks[b]? = some blk)
    (h : m'.blocks = m.blocks.set! b { blk with bytes := writeBytes blk.bytes o bs })
    (hn : o + bs.size ≤ blk.bytes.size) : KMono m m' ∧ KeepsExt m m' :=
  ⟨KMono.set (blk' := { blk with bytes := writeBytes blk.bytes o bs }) hb rfl h,
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

/-! ## The rules -/

theorem intSize_64 : intSize 64 = 8 := by decide

theorem access_inj {x y : BlockId × Block × Nat} (h : (pure x : Result _) = pure y) : x = y := by
  have := congrArg ExceptT.run h
  simpa [pure, ExceptT.pure, ExceptT.mk, ExceptT.run] using this

/-- **Atomic load** of an owned word, whatever its layout (sequential: choice 0); afterwards the
word is an `apts`. -/
theorem FTriple.atomicLoadW (p : Ptr) (v : BitVec 64) (ord : AtomicOrder) :
    FTriple (wpts p v) (Zig.atomicLoadAt (n := 64) 0 ord 8 p)
      (fun w => ⟪w = v⟫ ⋆ apts p v) := by
  refine FTriple.of_fix (fun _ _ _ hh hp => wpts_fix hh hp) fun m r rF hh hxr hxF hp hs => ?_
  obtain ⟨A, S, K, bs, tg, hal, hK, hsz, hv, hab⟩ := hp
  have hm := hh.heap_exact hxr hxF
  obtain ⟨b, blk, hacc, hblk, hA, hS, hx⟩ := bytesAt_access (q := p) (k := 0) (n := 8) (a := 8)
    (abytesAt_bytesAt hab) hm (by simp [Ptr.add]) (by decide) (by omega) (by simpa using hal)
  have hpb := (access_eq hacc).1
  have hacc8 : m.access p (intSize 64) 8 = pure (b, blk, p.off.toNat) := by
    rw [intSize_64]; simpa using hacc
  have hcur : ∀ m₀ : Mem, m₀.blocks = m.blocks → curBytes m₀ b p.off.toNat 8 = bs := by
    intro m₀ e
    simp only [curBytes, e, hblk, Option.map_some, Option.getD_some]
    have : bs.extract 0 8 = bs := by rw [← hsz]; simp
    simpa [this] using hx
  have hlocok := fun e => locIdx_noErr_single (m := m.recordAt b p.off.toNat 8 .atomicRead)
    (singleThread_recordAt hs.1.single _ _ _ _) b p.off.toNat 8 e
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
    have := locIdx_post (m := m.recordAt b p.off.toNat 8 .atomicRead) hs.2.1 (by decide) (by rw [hcur (m.recordAt b p.off.toNat 8 .atomicRead) rfl, hsz]) hl
    obtain ⟨hupd, -, -, -, hpos, hlast, hwf, htag⟩ := this
    refine ⟨readOpts_zero hpos, by rw [lastBytes_eq hpos, hlast, hcur (m.recordAt b p.off.toNat 8 .atomicRead) rfl], ?_⟩
    exact ⟨hupd, hwf, htag⟩
  cases hrun : ((Zig.atomicLoadAt (n := 64) 0 ord 8 p).run m).run with
  | none => trivial
  | some x =>
    cases x with
    | error e =>
      refine (atomicLoadAt_noErr (fun e' => ?_) (fun li opts m₁ hp => ?_) e hrun).elim
      · exact loadPrep_noErr (by simpa using hacc8) (noRace_of_singleThread hs.1.single _ _ _ _)
          (fun e'' => by rw [intSize_64]; exact hlocok e'') e'
      · obtain ⟨b', blk', o', ha', -, hl, rfl⟩ := loadPrep_ok hp
        simp only [Bool.false_eq_true, ↓reduceIte] at ha'
        obtain ⟨rfl, rfl, rfl⟩ := access_inj (hacc8.symm.trans ha')
        obtain ⟨hz, hbytes, -⟩ := hnewest li m₁ hl
        exact ⟨_, hz, v, by rw [hbytes, hv]; rfl⟩
    | ok x =>
      obtain ⟨w, m'⟩ := x
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
      refine ⟨r', hh', sep_lift.mpr ⟨hwv, apts_of hal hK hsz hv hab'⟩,
        ⟨⟨singleThread_loadM (by rw [hm₁]; exact singleThread_recordAt hs.1.single _ _ _ _) _ _ _⟩, by rw [hshapes]; exact hwf,
          LDMono.of_blocks hblocks hs.2.2⟩⟩

/-- **Atomic load** of an `apts` word (sequential: choice 0). -/
theorem FTriple.atomicLoad (p : Ptr) (v : BitVec 64) (ord : AtomicOrder) :
    FTriple (apts p v) (Zig.atomicLoadAt (n := 64) 0 ord 8 p) (fun w => ⟪w = v⟫ ⋆ apts p v) :=
  (FTriple.atomicLoadW p v ord).pre fun _ => apts_wpts

theorem shapes_insertM_last {m : Mem} {li : Nat} {msg : Msg} {blk : Block}
    (hb : m.blocks[(m.atomics[li]!).block]? = some blk) (hli : li < m.atomics.size) :
    shapes (insertM m li (m.atomics[li]!).msgs.size msg) = shapes m := by
  rw [insertM_last hb]
  exact shapes_set hli (by rw [getElem!_pos m.atomics li hli]; rfl)

/-- **Atomic store** to an owned word, whatever its layout (sequential: the write goes at the
end). -/
theorem FTriple.atomicStoreW (p : Ptr) (v w : BitVec 64) (ord : AtomicOrder) :
    FTriple (wpts p v) (Zig.atomicStoreAt 0 ord 8 p w) (fun _ => apts p w) := by
  refine FTriple.of_fix (fun _ _ _ hh hp => wpts_fix hh hp) fun m r rF hh hxr hxF hp hs => ?_
  obtain ⟨A, S, K, bs, tg, hal, hK, hsz, -, hab⟩ := hp
  have hm := hh.heap_exact hxr hxF
  obtain ⟨b, blk, hacc, hblk, hA, hS, -⟩ := bytesAt_access (q := p) (k := 0) (n := 8) (a := 8)
    (abytesAt_bytesAt hab) hm (by simp [Ptr.add]) (by decide) (by omega) (by simpa using hal)
  obtain ⟨hpb, -, hlive, h0, hfit, -, -⟩ := access_eq hacc
  have hcast : (p.off.toNat : Int) = p.off := Int.toNat_of_nonneg h0
  have hKb : blk.kind = K ∧ blk.kind.mappedLo ≤ p.off.toNat := by
    obtain ⟨-, -, b0, hb0, -, hl0⟩ := id hab
    rw [hpb] at hb0; cases hb0
    have hr := hl0 (b, p.off.toNat)
    rw [if_pos ⟨rfl, Nat.le_refl _, by omega⟩] at hr
    obtain ⟨blk', hblk', _, _, hc⟩ := Mem.heap_some (hxr _ _ hr)
    obtain ⟨blk'', hblk'', hlo⟩ := Mem.heap_some_lo (hxr _ _ hr)
    rw [hblk] at hblk' hblk''; cases hblk'; cases hblk''
    simp only [Cell.mk.injEq] at hc
    exact ⟨hc.2.2.2.symm, hlo⟩
  obtain ⟨hKb, hlo⟩ := hKb
  have haccW8 : m.accessW p (intSize 64) 8 = pure (b, blk, p.off.toNat) := by
    rw [intSize_64]; unfold Mem.accessW; rw [hacc]
    simp [hKb, hK, pure_bind]
  have hcur : (curBytes (m.recordAt b p.off.toNat 8 .atomicWrite) b p.off.toNat 8).size = 8 := by
    simp only [curBytes, Mem.recordAt, hblk, Option.map_some, Option.getD_some, Array.size_extract]
    omega
  have hlocok := fun e => locIdx_noErr_single (m := m.recordAt b p.off.toNat 8 .atomicWrite)
    (singleThread_recordAt hs.1.single _ _ _ _) b p.off.toNat 8 e
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
      locIdx_post (m := m.recordAt b p.off.toNat 8 .atomicWrite) hs.2.1 (by decide) hcur hl
    exact ⟨writeSlots_zero hpos, hli, hb, ho, hupd, hwf, htag⟩
  cases hrun : ((Zig.atomicStoreAt 0 ord 8 p w).run m).run with
  | none => trivial
  | some x =>
    cases x with
    | error e =>
      refine (atomicStoreAt_noErr (fun e' => ?_) (fun li slots m₁ hp => ?_) e hrun).elim
      · exact storePrep_noErr haccW8 (noRace_of_singleThread hs.1.single _ _ _ _)
          (fun e'' => by rw [intSize_64]; exact hlocok e'') e'
      · obtain ⟨b', blk', o', ha', -, hl, rfl⟩ := storePrep_ok hp
        obtain ⟨rfl, rfl, rfl⟩ := access_inj (haccW8.symm.trans ha')
        obtain ⟨hz, -⟩ := hpost li m₁ hl
        exact (Array.getElem?_eq_some_iff.mp hz).1
    | ok x =>
      obtain ⟨u, m'⟩ := x
      obtain ⟨b', blk', o', li, m₁, slot, ha', -, hl, hslot, hm'⟩ := atomicStoreAt_ok hrun
      obtain ⟨rfl, rfl, rfl⟩ := access_inj (haccW8.symm.trans ha')
      obtain ⟨hz, hli, hb, ho, ⟨a, sn, next, hm₁⟩, hwf, htag⟩ := hpost li m₁ hl
      rw [hz] at hslot; cases hslot
      have hb₁ : m₁.blocks[(m₁.atomics[li]!).block]? = some blk := by
        rw [hb, hm₁]; exact hblk
      subst hm'
      have hins := insertM_last (li := li) (msg := storeMsg m₁ ord w) hb₁
      have hblocks : (storeM m₁ li (m₁.atomics[li]!).msgs.size ord w).blocks =
          m.blocks.set! b { blk with bytes := writeBytes blk.bytes p.off.toNat (Enc.encode w) } := by
        unfold storeM observeM
        rw [hins, hb, ho, hm₁]; rfl
      have hshapes : shapes (storeM m₁ li (m₁.atomics[li]!).msgs.size ord w) = shapes m₁ := by
        unfold storeM observeM
        exact shapes_insertM_last hb₁ hli
      have henc : (Enc.encode w).size = 8 := LawfulEnc.size_encode w
      have hwr := Mem.heap_write (m := m) (o := p.off.toNat) hblk hlive (bs := Enc.encode w)
        (by rw [henc]; omega) hlo
      obtain ⟨r', hh', hab'⟩ := holds_after hh hab (bs' := Enc.encode w) (by rw [henc, hsz]) hpb
        (fun l => by
          rw [heap_of_blocks (m := m.write b blk p.off.toNat (Enc.encode w)) hblocks, hwr, henc,
            hsz, hA, hS, hKb])
        (fun b' x => by rw [hshapes, hsz]; exact htag b' x)
        (kmono_write hblk hblocks (by rw [henc]; omega))
      refine ⟨r', hh', apts_of hal hK henc (LawfulEnc.decode_encode w) (by rw [henc, ← hsz]; exact hab'), ⟨⟨?_⟩, by rw [hshapes]; exact hwf,
          ld_write hblk (by rw [henc]; omega) hblocks hs.2.2⟩⟩
      unfold storeM observeM
      exact singleThread_insertM (by rw [hm₁]; exact singleThread_recordAt hs.1.single _ _ _ _) _ _ _

/-- **Atomic store** to an `apts` word. -/
theorem FTriple.atomicStore (p : Ptr) (v w : BitVec 64) (ord : AtomicOrder) :
    FTriple (apts p v) (Zig.atomicStoreAt 0 ord 8 p w) (fun _ => apts p w) :=
  (FTriple.atomicStoreW p v w ord).pre fun _ => apts_wpts

end Full
end Zig
