import ZigLean.Sep.Full.Triple

/-!
# Atomic points-to (prototype, `docs/sep-full-state.md`)

Rules for `atomic_load` and `atomic_store` of a 64-bit word that the precondition owns as `apts`
(`ZigLean/Sep/Full/Res.lean`), in a sequential run (choice `0`, the only option of one thread:
the newest message, a write at the end). The atomic layout is part of the owned bytes, so:

* the op cannot hit the mixed-size policy (`locIdx` cannot throw `.unspecified`): the bytes carry
  no location, or exactly the location `(p.off, 8)` (obstruction O3);
* the op changes the layout only of the owned bytes (a new location over them), so the frame's
  tags stay;
* in a sequential run the newest message has the block's bytes (`locIdx` adds a message when they
  differ), so the op reads and writes the owned bytes like a plain access.
-/

namespace Zig
namespace Full

open FAssn Conc Conc.Proto

/-! ## The layout after `locIdx` -/

/-- The bytes `o..o+len` of block `b` carry no location, or all the location `(o, len)`. -/
def TagOk (sh : List Shape) (b o len : Nat) : Prop :=
  (∀ x, o ≤ x → x < o + len → tagOf sh b x = none) ∨
  (∀ x, o ≤ x → x < o + len → tagOf sh b x = some (o, len))

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

/-- A location overlapping the bytes `o..o+len` of block `b` (with `TagOk`) is `(b, o, len)`. -/
theorem overlap_eq {sh : List Shape} (hw : ShapesWF sh) {b o len : Nat} (hlen : 0 < len)
    (ht : TagOk sh b o len)
    {s : Shape} (hs : s ∈ sh) (hb : s.1 = b) (h1 : o < s.2.1 + s.2.2) (h2 : s.2.1 < o + len) :
    s.2.1 = o ∧ s.2.2 = len := by
  have hpos := hw.1 s hs
  obtain ⟨x, hx1, hx2, hc⟩ : ∃ x, o ≤ x ∧ x < o + len ∧ Covers b x s := by
    by_cases ho : o ≤ s.2.1
    · exact ⟨s.2.1, ho, h2, hb, Nat.le_refl _, by omega⟩
    · exact ⟨o, Nat.le_refl _, by omega, hb, by omega, h1⟩
  have e := tagOf_of_mem hw hs hc
  rcases ht with h | h
  · rw [h _ hx1 hx2] at e; cases e
  · rw [h _ hx1 hx2] at e
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    exact ⟨e.1.symm, e.2.symm⟩

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

/-- What `locIdx` does at bytes with `TagOk` in a well-formed layout: only the atomics change;
location `li` is at `(b, o)`, its newest message has the block's bytes; the layout gets the
location `(b, o, len)` if it was not there and stays well formed. -/
theorem locIdx_post {m m₁ : Mem} {b o len li : Nat} (hw : ShapesWF (shapes m)) (hlen : 0 < len)
    (ht : TagOk (shapes m) b o len) (hcur : (curBytes m b o len).size = len)
    (h : ((locIdx b o len).run m).run = some (.ok (li, m₁))) :
    (∃ a next, m₁ = { m with atomics := a, nextMsg := next }) ∧
    li < m₁.atomics.size ∧ (m₁.atomics[li]!).block = b ∧ (m₁.atomics[li]!).off = o ∧
    0 < (m₁.atomics[li]!).msgs.size ∧ ALoc.lastBytes (m₁.atomics[li]!) = curBytes m b o len ∧
    ShapesWF (shapes m₁) ∧
    ∀ b' x, tagOf (shapes m₁) b' x =
      if Covers b' x (b, o, len) then some (o, len) else tagOf (shapes m) b' x := by
  have hupd := locIdx_updates h
  cases hi : m.atomics.findIdx? (fun l => l.block == b && l.off == o) with
  | some i =>
    obtain ⟨hlt, hp, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp hi
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    have hmem := shape_mem hlt
    obtain ⟨-, hl⟩ := overlap_eq hw hlen ht hmem hp.1 (by
        have := hw.1 _ hmem; simp only [ALoc.shape] at this ⊢; omega)
      (by simp only [ALoc.shape]; omega)
    simp only [ALoc.shape] at hl
    have hget : m.atomics[i]! = m.atomics[i] := getElem!_pos m.atomics i hlt
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
    refine ⟨hupd, by simp only [hsz]; exact hlt, by rw [hat, hget]; exact hp.1,
      by rw [hat, hget]; exact hp.2, by rw [hat]; exact hpos, by rw [hat]; exact hback,
      by rw [hsh]; exact hw, fun b' x => ?_⟩
    rw [hsh]
    split
    · rename_i hc
      have := tagOf_of_mem hw hmem (b := b') (x := x) (by
        simp only [ALoc.shape, hp.1, hp.2, hl]; exact hc)
      simpa [ALoc.shape, hp.2, hl] using this
    · rfl
  | none =>
    obtain ⟨rfl, hm₁⟩ := locIdx_new hi h
    -- No location overlaps the bytes: one would be `(b, o, len)`, found by `findIdx?`.
    have hno : ∀ s ∈ shapes m, s.1 = b → o < s.2.1 + s.2.2 → s.2.1 < o + len → False := by
      intro s hs hb h1 h2
      obtain ⟨ho, -⟩ := overlap_eq hw hlen ht hs hb h1 h2
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hs
      obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hl)
      have := Array.findIdx?_eq_none_iff.mp hi m.atomics[j] (Array.getElem_mem hj)
      simp only [ALoc.shape] at hb ho
      simp [hb, ho] at this
    have hsh : shapes m₁ = shapes m ++ [(b, o, len)] := by
      rw [hm₁]; simp [shapes, ALoc.shape]
    have hat : m₁.atomics[m.atomics.size]! = firstLoc m b o len := by
      rw [hm₁]; simp [firstLoc, firstMsg]
    refine ⟨hupd, by rw [hm₁]; simp, by rw [hat]; rfl, by rw [hat]; rfl,
      by rw [hat]; simp [firstLoc], by rw [hat]; simp [ALoc.lastBytes, firstLoc, firstMsg], ?_,
      fun b' x => ?_⟩
    · rw [hsh]
      refine ⟨fun s hs => ?_, ?_⟩
      · rcases List.mem_append.mp hs with h | h
        · exact hw.1 s h
        · simp at h; subst h; exact hlen
      · rw [List.pairwise_append]
        refine ⟨hw.2, List.pairwise_singleton _ _, fun s hs t ht' hst => ?_⟩
        simp at ht'; subst ht'
        by_cases h1 : o < s.2.1 + s.2.2
        · by_cases h2 : s.2.1 < o + len
          · exact (hno s hs hst h1 h2).elim
          · right; simp only; omega
        · left; simp only; omega
    · rw [hsh, tagOf_append_single]
      split
      · rename_i hc
        have : tagOf (shapes m) b' x = none := tagOf_none.mpr fun s hs hcs => by
          obtain ⟨e1, e2, e3⟩ := hc
          obtain ⟨f1, f2, f3⟩ := hcs
          simp only at e1 e2 e3
          exact hno s hs (f1.trans e1.symm) (by omega) (by omega)
        rw [this]; rfl
      · simp

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

theorem locIdx_noErr_tag {m : Mem} {b o len : Nat} (hw : ShapesWF (shapes m)) (hlen : 0 < len)
    (ht : TagOk (shapes m) b o len) (e : Error) :
    ((locIdx b o len).run m).run ≠ some (.error e) := by
  apply locIdx_noErr_of _ _ e
  · intro i hi
    obtain ⟨hlt, hp, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp hi
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    have hmem := shape_mem hlt
    have hpos := hw.1 _ hmem
    simp only [ALoc.shape] at hpos
    obtain ⟨-, hl⟩ := overlap_eq hw hlen ht hmem hp.1 (by simp only [ALoc.shape]; omega)
      (by simp only [ALoc.shape]; omega)
    rw [getElem!_pos m.atomics i hlt]; exact hl
  · intro hi l hl hb h1 h2
    obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp hl
    obtain ⟨ho, -⟩ := overlap_eq hw hlen ht (shape_mem hj) hb h1 h2
    have := Array.findIdx?_eq_none_iff.mp hi m.atomics[j] (Array.getElem_mem hj)
    simp only [ALoc.shape] at hb ho
    simp [hb, ho] at this

theorem Holds.own {m : Mem} {r rF : Res} (hh : Holds m r rF) {l : Loc} {fc : FCell}
    (h : r.heap l = some fc) : m.fheap l = some fc := by
  rw [hh.heap, FHeap.union_apply, h]; rfl

theorem fheap_tag {m : Mem} {l : Loc} {fc : FCell} (h : m.fheap l = some fc) :
    fc.atom = tagOf (shapes m) l.1 l.2 ∧ m.heap l = some fc.cell := by
  simp only [Mem.fheap, Option.map_eq_some_iff] at h
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨rfl, hc⟩

/-- The owned word of `apts` has a uniform tag: `TagOk` for `(p.off, 8)`. -/
theorem tagOk_of_own {m : Mem} {r rF : Res} (hh : Holds m r rF) {p : Ptr} {A S : Nat}
    {K : BlockKind} {bs : Array Byte} {tg : Option (Nat × Nat)} (hab : abytesAt p A S K bs tg r)
    (hsz : bs.size = 8) (htg : tg = none ∨ tg = some (p.off.toNat, 8)) {b : BlockId}
    (hpb : p.block = some b) : TagOk (shapes m) b p.off.toNat 8 := by
  obtain ⟨-, b0, hb0, -, hl⟩ := hab
  rw [hpb] at hb0; cases hb0
  have key : ∀ x, p.off.toNat ≤ x → x < p.off.toNat + 8 → tagOf (shapes m) b x = tg := by
    intro x h1 h2
    have hr := hl (b, x)
    rw [if_pos ⟨rfl, h1, by omega⟩] at hr
    exact ((fheap_tag (hh.own hr)).1).symm
  rcases htg with rfl | rfl
  · exact .inl key
  · exact .inr key

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

/-- After an atomic op on the owned word: the memory has new bytes `bs'` there (the same for a
load), the layout gets the location `(p.off, 8)`, the rest is unchanged. Then the memory holds the
word with the new bytes and the tag of that location, and the frame. -/
theorem holds_after {m m' : Mem} {r rF : Res} (hh : Holds m r rF) {p : Ptr} {A S : Nat}
    {K : BlockKind} {bs bs' : Array Byte} {tg : Option (Nat × Nat)} (hab : abytesAt p A S K bs tg r)
    (hsz : bs'.size = bs.size) {b : BlockId} (hpb : p.block = some b)
    (hheap : ∀ l, m'.heap l = if l.1 = b ∧ p.off.toNat ≤ l.2 ∧ l.2 < p.off.toNat + bs.size
      then some ⟨bs'[l.2 - p.off.toNat]!, A, S, K⟩ else m.heap l)
    (htag : ∀ b' x, tagOf (shapes m') b' x = if Covers b' x (b, p.off.toNat, bs.size)
      then some (p.off.toNat, bs.size) else tagOf (shapes m) b' x)
    (hkn : KMono m m') (hA : m.AddrBelow) (hn : m'.nextAddr = m.nextAddr) :
    m'.AddrBelow ∧
      ∃ r', Holds m' r' rF ∧ abytesAt p A S K bs' (some (p.off.toNat, bs.size)) r' := by
  obtain ⟨-, b0, hb0, h0, hl⟩ := id hab
  rw [hpb] at hb0; cases hb0
  refine ⟨hA.of_heap hn fun l c hc => ?_, ?_⟩
  · rw [hheap] at hc
    split at hc
    · rename_i hin
      cases hc
      have hr := hl l
      rw [if_pos hin] at hr
      exact ⟨l, _, (fheap_tag (hh.own hr)).2, rfl, rfl⟩
    · exact ⟨l, c, hc, rfl, rfl⟩
  let h' : FHeap := fun l =>
    if l.1 = b ∧ p.off.toNat ≤ l.2 ∧ l.2 < p.off.toNat + bs'.size
    then some ⟨⟨bs'[l.2 - p.off.toNat]!, A, S, K⟩, some (p.off.toNat, bs.size)⟩ else none
  refine ⟨⟨h', Know.none⟩, ⟨fun l => ?_, funext fun l => ?_, Know.sub_none _,
    hh.knowF.trans hkn⟩, rfl, b, hpb, h0, fun l => rfl⟩
  · by_cases hc : l.1 = b ∧ p.off.toNat ≤ l.2 ∧ l.2 < p.off.toNat + bs'.size
    · right
      have : r.heap l ≠ none := by rw [hl l, if_pos (by rw [← hsz]; exact hc)]; simp
      exact (hh.disj l).resolve_left this
    · left; simp only [h']; rw [if_neg hc]
  · obtain ⟨x, y⟩ := l
    simp only [Mem.fheap, hheap, FHeap.union_apply, htag]
    by_cases hc : x = b ∧ p.off.toNat ≤ y ∧ y < p.off.toNat + bs.size
    · obtain ⟨rfl, h1, h2⟩ := hc
      have hcov : Covers x y (x, p.off.toNat, bs.size) := ⟨rfl, h1, h2⟩
      have hc : x = x ∧ p.off.toNat ≤ y ∧ y < p.off.toNat + bs.size := ⟨rfl, h1, h2⟩
      simp only [hc, hcov, and_self, ↓reduceIte, h', hsz, Option.map_some, Option.some_or]
    · have hcov : ¬ Covers x y (b, p.off.toNat, bs.size) := fun h => hc ⟨h.1.symm, h.2.1, h.2.2⟩
      have hr : r.heap (x, y) = none := by rw [hl]; simp only; rw [if_neg hc]
      have e := congrFun hh.heap (x, y)
      rw [FHeap.union_apply, hr, Option.none_or] at e
      have hc' : ¬ (x = b ∧ p.off.toNat ≤ y ∧ y < p.off.toNat + bs'.size) := by rw [hsz]; exact hc
      simp only [hc, hcov, ↓reduceIte, h', hc', Option.none_or]
      exact e

theorem kmono_of_blocks {m m' : Mem} (h : m'.blocks = m.blocks) : KMono m m' := KMono.of_blocks h

theorem heap_of_blocks {m m' : Mem} (h : m'.blocks = m.blocks) : m'.heap = m.heap := by
  funext l; simp [Mem.heap, h]

/-! ## The rules -/

theorem intSize_64 : intSize 64 = 8 := by decide

theorem access_inj {x y : BlockId × Block × Nat} (h : (pure x : Result _) = pure y) : x = y := by
  have := congrArg ExceptT.run h
  simpa [pure, ExceptT.pure, ExceptT.mk, ExceptT.run] using this

/-- **Atomic load** of an owned word (sequential: choice 0). -/
theorem FTriple.atomicLoad (p : Ptr) (v : BitVec 64) (ord : AtomicOrder) :
    FTriple (apts p v) (Zig.atomicLoadAt (n := 64) 0 ord 8 p)
      (fun w => ⟪w = v⟫ ⋆ apts p v) := by
  intro m r rF hh hp hs
  obtain ⟨A, S, K, bs, tg, hal, hK, hsz, hv, htg, hab⟩ := hp
  have hm : m.heap = r.heap.erase ∪ rF.heap.erase := by
    rw [← fheap_erase, hh.heap, FHeap.erase_union]
  obtain ⟨b, blk, hacc, hblk, hA, hS, hx⟩ := bytesAt_access (q := p) (k := 0) (n := 8) (a := 8)
    (abytesAt_bytesAt hab) hm (by simp [Ptr.add]) (by decide) (by omega) (by simpa using hal)
  have hpb := (access_eq hacc).1
  have hacc8 : m.access p (intSize 64) 8 = pure (b, blk, p.off.toNat) := by
    rw [intSize_64]; simpa using hacc
  have htok := tagOk_of_own hh hab hsz htg hpb
  have hcur : ∀ m₀ : Mem, m₀.blocks = m.blocks → curBytes m₀ b p.off.toNat 8 = bs := by
    intro m₀ e
    simp only [curBytes, e, hblk, Option.map_some, Option.getD_some]
    have : bs.extract 0 8 = bs := by rw [← hsz]; simp
    simpa [this] using hx
  have hlocok := fun e => locIdx_noErr_tag (m := m.recordAt b p.off.toNat 8 .atomicRead) hs.2
    (by decide) htok e
  -- A successful preparation reads the newest message, which has the owned bytes.
  have hnewest : ∀ li m₁, ((locIdx b p.off.toNat (intSize 64)).run
      (m.recordAt b p.off.toNat (intSize 64) .atomicRead)).run = some (.ok (li, m₁)) →
      (readOpts m₁ li false)[0]? = some ((m₁.atomics[li]!).msgs.size - 1) ∧
      ((m₁.atomics[li]!).msgs[(m₁.atomics[li]!).msgs.size - 1]!).bytes = bs ∧
      (∃ a next, m₁ = { m.recordAt b p.off.toNat 8 .atomicRead with atomics := a, nextMsg := next }) ∧
      ShapesWF (shapes m₁) ∧
      ∀ b' x, tagOf (shapes m₁) b' x =
        if Covers b' x (b, p.off.toNat, 8) then some (p.off.toNat, 8) else tagOf (shapes m) b' x := by
    intro li m₁ hl
    rw [intSize_64] at hl
    have := locIdx_post (m := m.recordAt b p.off.toNat 8 .atomicRead) hs.2 (by decide) htok
      (by rw [hcur (m.recordAt b p.off.toNat 8 .atomicRead) rfl, hsz]) hl
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
      obtain ⟨hz, hbytes, ⟨a, next, hm₁⟩, hwf, htag⟩ := hnewest li m₁ hl
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
      have hnext : (loadM m₁ li ord
          ((m₁.atomics[li]!).msgs[(m₁.atomics[li]!).msgs.size - 1]!)).nextAddr = m.nextAddr := by
        unfold loadM acqM observeM; split <;> simp [hm₁, Mem.recordAt]
      obtain ⟨hAB, r', hh', hab'⟩ := holds_after hh hab (bs' := bs) rfl hpb
        (fun l => by
          rw [heap_of_blocks hblocks]
          split
          · rename_i hin
            obtain ⟨-, b0, hb0, -, hl0⟩ := hab
            rw [hpb] at hb0; cases hb0
            have hr := hl0 l
            rw [if_pos hin] at hr
            exact (fheap_tag (hh.own hr)).2
          · rfl)
        (fun b' x => by rw [hshapes, htag, hsz]) (kmono_of_blocks hblocks) hs.1.addr hnext
      refine ⟨r', hh', sep_lift.mpr ⟨hwv, A, S, K, bs, _, hal, hK, hsz, hv, .inr (by rw [hsz]), hab'⟩,
        ⟨⟨singleThread_loadM (by rw [hm₁]; exact singleThread_recordAt hs.1.single _ _ _ _) _ _ _,
          hAB⟩, by rw [hshapes]; exact hwf⟩⟩

theorem shapes_insertM_last {m : Mem} {li : Nat} {msg : Msg} {blk : Block}
    (hb : m.blocks[(m.atomics[li]!).block]? = some blk) (hli : li < m.atomics.size) :
    shapes (insertM m li (m.atomics[li]!).msgs.size msg) = shapes m := by
  rw [insertM_last hb]
  exact shapes_set hli (by rw [getElem!_pos m.atomics li hli]; rfl)

/-- **Atomic store** to an owned word (sequential: the write goes at the end). -/
theorem FTriple.atomicStore (p : Ptr) (v w : BitVec 64) (ord : AtomicOrder) :
    FTriple (apts p v) (Zig.atomicStoreAt 0 ord 8 p w) (fun _ => apts p w) := by
  intro m r rF hh hp hs
  obtain ⟨A, S, K, bs, tg, hal, hK, hsz, -, htg, hab⟩ := hp
  have hm : m.heap = r.heap.erase ∪ rF.heap.erase := by
    rw [← fheap_erase, hh.heap, FHeap.erase_union]
  obtain ⟨b, blk, hacc, hblk, hA, hS, -⟩ := bytesAt_access (q := p) (k := 0) (n := 8) (a := 8)
    (abytesAt_bytesAt hab) hm (by simp [Ptr.add]) (by decide) (by omega) (by simpa using hal)
  obtain ⟨hpb, -, hlive, h0, hfit, -, -⟩ := access_eq hacc
  have hcast : (p.off.toNat : Int) = p.off := Int.toNat_of_nonneg h0
  have hKb : blk.kind = K ∧ blk.kind.mappedLo ≤ p.off.toNat := by
    obtain ⟨-, b0, hb0, -, hl0⟩ := id hab
    rw [hpb] at hb0; cases hb0
    have hr := hl0 (b, p.off.toNat)
    rw [if_pos ⟨rfl, Nat.le_refl _, by omega⟩] at hr
    obtain ⟨blk', hblk', _, _, hc⟩ := Mem.heap_some (fheap_tag (hh.own hr)).2
    obtain ⟨blk'', hblk'', hlo⟩ := Mem.heap_some_lo (fheap_tag (hh.own hr)).2
    rw [hblk] at hblk' hblk''; cases hblk'; cases hblk''
    simp only [Cell.mk.injEq] at hc
    exact ⟨hc.2.2.2.symm, hlo⟩
  obtain ⟨hKb, hlo⟩ := hKb
  have haccW8 : m.accessW p (intSize 64) 8 = pure (b, blk, p.off.toNat) := by
    rw [intSize_64]; unfold Mem.accessW; rw [hacc]
    simp [hKb, hK, pure_bind]
  have htok := tagOk_of_own hh hab hsz htg hpb
  have hcur : (curBytes (m.recordAt b p.off.toNat 8 .atomicWrite) b p.off.toNat 8).size = 8 := by
    simp only [curBytes, Mem.recordAt, hblk, Option.map_some, Option.getD_some, Array.size_extract]
    omega
  have hlocok := fun e => locIdx_noErr_tag (m := m.recordAt b p.off.toNat 8 .atomicWrite) hs.2
    (by decide) htok e
  have hpost : ∀ li m₁, ((locIdx b p.off.toNat (intSize 64)).run
      (m.recordAt b p.off.toNat (intSize 64) .atomicWrite)).run = some (.ok (li, m₁)) →
      (writeSlots m₁ li)[0]? = some (m₁.atomics[li]!).msgs.size ∧
      li < m₁.atomics.size ∧ (m₁.atomics[li]!).block = b ∧ (m₁.atomics[li]!).off = p.off.toNat ∧
      (∃ a next, m₁ = { m.recordAt b p.off.toNat 8 .atomicWrite with atomics := a, nextMsg := next }) ∧
      ShapesWF (shapes m₁) ∧
      ∀ b' x, tagOf (shapes m₁) b' x =
        if Covers b' x (b, p.off.toNat, 8) then some (p.off.toNat, 8) else tagOf (shapes m) b' x := by
    intro li m₁ hl
    rw [intSize_64] at hl
    obtain ⟨hupd, hli, hb, ho, hpos, -, hwf, htag⟩ :=
      locIdx_post (m := m.recordAt b p.off.toNat 8 .atomicWrite) hs.2 (by decide) htok hcur hl
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
      obtain ⟨hz, hli, hb, ho, ⟨a, next, hm₁⟩, hwf, htag⟩ := hpost li m₁ hl
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
      have hnext : (storeM m₁ li (m₁.atomics[li]!).msgs.size ord w).nextAddr = m.nextAddr := by
        unfold storeM observeM
        rw [hins, hm₁]; rfl
      have henc : (Enc.encode w).size = 8 := LawfulEnc.size_encode w
      have hwr := Mem.heap_write (m := m) (o := p.off.toNat) hblk hlive (bs := Enc.encode w)
        (by rw [henc]; omega) hlo
      obtain ⟨hAB, r', hh', hab'⟩ := holds_after hh hab (bs' := Enc.encode w) (by rw [henc, hsz]) hpb
        (fun l => by
          rw [heap_of_blocks (m := m.write b blk p.off.toNat (Enc.encode w)) hblocks, hwr, henc,
            hsz, hA, hS, hKb])
        (fun b' x => by rw [hshapes, htag, hsz])
        (KMono.set (blk' := { blk with bytes := writeBytes blk.bytes p.off.toNat (Enc.encode w) })
          hblk rfl hblocks) hs.1.addr hnext
      refine ⟨r', hh', ⟨A, S, K, Enc.encode w, _, hal, hK, henc, LawfulEnc.decode_encode w,
        .inr (by rw [hsz]), hab'⟩, ⟨⟨?_, hAB⟩, by rw [hshapes]; exact hwf⟩⟩
      unfold storeM observeM
      exact singleThread_insertM (by rw [hm₁]; exact singleThread_recordAt hs.1.single _ _ _ _) _ _ _

end Full
end Zig
