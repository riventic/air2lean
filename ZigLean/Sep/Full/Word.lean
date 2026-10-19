import ZigLean.Conc.Word
import ZigLean.Sep.Full.LockRules

/-!
# A shared atomic word, over full-state resources

A word of a sync object that no thread owns (the state and the epoch of a condition, the state
of an event; `ZigLean/Conc/Word.lean`) is a part of the protocol's rest: its bytes are in the rest
as the memory's cells (`Word.cellsR W m = cellsAt W.In m`, `ZigLean/Sep/Full/ThreadRest.lean`),
so no thread's part has them and no step of a thread on its own part touches them. The facts about
the word's values and clocks (`Word.Ok`, `Word.hist`, the ops `Ok.load`, `Ok.rmw`, `Ok.cas`) are
facts of the memory model and stay in `ZigLean/Conc/Word.lean`. This file connects them to the
full-state lock (`FLock`, `ZigLean/Sep/Full/Lock.lean`):

- **Actual primitive runs expose native state effects** (`RestStep`, `FStepIn`) and their
  validity, history and result facts. They preserve every part and the rest of the rest
  (`FOwned.restStep`), and the apart lock's invariant (`FLock.Inv.wordStep`).
- **A step of the lock's code preserves validity and history** (`Word.Ok.lockStep`).
- **A step on a thread's own part preserves a framed word** (`Word.Ok.fstep`, `hist_fstep`):
  its frame has the word's cells, which stay up to `Cell.norm` (`FLock.Inv.cellsN`).
- **A futex wait at the word** by a thread out of the lock's code (`away`) keeps the lock's
  invariant (`FLock.Inv.waitOff`, `FLock.Inv.spuriousOff`); so does a futex wake at it
  (`FLock.Inv.wakeOff`).

A rest that has the word's cells of an older memory, the same up to `Cell.norm`, is the rest with
the word's cells of the new memory (`FLock.Inv.congrX`).

The native producers feed WordRules and both Event/Cond step families directly. Old exported
`Op`/`Keep` helpers remain for their existing consumers; their types are visible retirement
debt in the `seen-floor-sync-retirement` engine-ledger row. Native paths do not construct
those packets or call their preservation wrappers.
-/

namespace Zig

namespace Conc


namespace Proto

/-- The complete memory equation of a newest-message RMW. The optional acquire
precedes the actual array replacement, byte write and observation. -/
theorem rmwM_last_eq {m : Mem} {li pos : Nat} {l : ALoc} {blk : Block} {n : Nat}
    (hl : m.atomics[li]! = l) (hpos : pos + 1 = l.msgs.size)
    (hb : m.blocks[l.block]? = some blk) (ord : AtomicOrder) (rd : Msg) (new : BitVec n) :
    let m₂ := if ord.isAcq then acqM m rd.relClock else m
    rmwM m li pos ord rd new = observeM { m₂ with
      atomics := m₂.atomics.set! li {l with msgs := l.msgs.push (rmwMsg m₂ ord rd new)},
      nextMsg := m₂.nextMsg + 1,
      blocks := m₂.blocks.set! l.block
        {blk with bytes := writeBytes blk.bytes l.off (rmwMsg m₂ ord rd new).bytes} }
      li m₂.nextMsg := by
  let m₂ := if ord.isAcq then acqM m rd.relClock else m
  have ha₂ : m₂.atomics = m.atomics := by
    simp only [m₂]
    split <;> rfl
  have hb₂ : m₂.blocks = m.blocks := by
    simp only [m₂]
    split <;> rfl
  have hl₂ : m₂.atomics[li]! = l := by rw [ha₂]; exact hl
  have hblk₂ : m₂.blocks[(m₂.atomics[li]!).block]? = some blk := by
    rw [hl₂, hb₂]
    exact hb
  have hp₂ : pos + 1 = (m₂.atomics[li]!).msgs.size := by
    rw [hl₂]
    exact hpos
  change observeM (insertM m₂ li (pos + 1) (rmwMsg m₂ ord rd new)) li m₂.nextMsg = _
  rw [hp₂, insertM_last hblk₂]
  simp only [hl₂]
  rfl

end Proto

namespace Word

open Full

variable {n nb : Nat} (W : Word n nb)

/-- The byte `l` is a byte of the word. -/
def In (l : Zig.Loc) : Prop := l.1 = W.b ∧ W.o ≤ l.2 ∧ l.2 < W.o + nb

instance (l : Zig.Loc) : Decidable (W.In l) := by unfold In; infer_instance

/-- The word's cells, as a resource of the protocol's rest. -/
abbrev cellsR (m : Mem) : Res := cellsAt W.In m

/-- The lock's word and `W` do not overlap. -/
def ApartL (L : LockWord) : Prop := L.b ≠ W.b ∨ L.o + 4 ≤ W.o ∨ W.o + nb ≤ L.o

variable {W}

/-- The word's cells depend only on the blocks. -/
theorem cellsR_congr {m m' : Mem} (h : m'.blocks = m.blocks) : W.cellsR m' = W.cellsR m := by
  have : m'.heap = m.heap := by funext ⟨b, x⟩; simp only [Mem.heap, h]
  simp only [cellsR, cellsAt, this]

/-- A word apart from the lock's is at another place. -/
theorem ApartL.ne {L : LockWord} (hap : W.ApartL L) : L.b ≠ W.b ∨ L.o ≠ W.o := by
  have := W.sz_pos
  rcases hap with h | h | h
  · exact .inl h
  · exact .inr (by omega)
  · exact .inr (by omega)

/-- A 32-bit word apart from the lock's has another pointer. -/
theorem ApartL.ptr_ne {W : Word 32 4} {L : LockWord} (hap : W.ApartL L) : W.ptr ≠ L.ptr := fun e => by
  simp only [Word.ptr, LockWord.ptr, Ptr.mk.injEq, Option.some.injEq, Int.natCast_inj] at e
  rcases hap.ne with h | h
  · exact h e.1.symm
  · exact h e.2.symm

theorem cellKey_norm (c : Cell) : cellKey c.norm = cellKey c := by
  obtain ⟨b, a, s, k⟩ := c
  cases k <;> rfl

/-- The blocks after an op at the word, from the block of the word. -/
theorem BlkStep.eq_set {m m' : Mem} (h : W.BlkStep m m') {blk : Block}
    (hb : m.blocks[W.b]? = some blk) : ∃ blk', m'.blocks[W.b]? = some blk' ∧
      blk'.addr = blk.addr ∧ blk'.live = blk.live ∧ blk'.kind = blk.kind ∧
      blk'.bytes.size = blk.bytes.size ∧ m'.blocks = m.blocks.set! W.b blk' := by
  obtain ⟨blk', hb', ha, hl, hk, hs, -⟩ := h.word blk hb
  refine ⟨blk', hb', ha, hl, hk, hs, ?_⟩
  have hlt : W.b < m.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  apply Array.ext_getElem? fun i => ?_
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases e : W.b = i
  · subst e; simp [hlt, hb']
  · simp only [e, ↓reduceIte]; exact h.other i (Ne.symm e)

theorem keys_toList (m : Mem) : (keys m).toList = shapes m := by
  simp [keys, shapes, ALoc.shape]

/-- The bytes of the word are live in a memory where it is `Ok`. -/
theorem Ok.cellIn {m : Mem} (hw : W.Ok m) {l : Zig.Loc} (hl : W.In l) : m.heap l ≠ none := by
  obtain ⟨b, x⟩ := l
  obtain ⟨h1, h2, h3⟩ := hl
  simp only at h1 h2 h3; subst h1
  exact hw.cell h2 h3

/-- **An op at the word is a step at its bytes** (`RestStep`). -/
theorem Op.rest {t : ThreadId} {m m' : Mem} (hop : W.Op t m m') (hw : W.Ok m) (hw' : W.Ok m') :
    RestStep W.In m m' := by
  have hsz0 := W.sz_pos
  obtain ⟨blk, hb, hl, hsz, -, hk, -⟩ := hw.blk
  obtain ⟨blk', hb', ha', hl', hk', hs', hset⟩ := hop.blocks.eq_set hb
  have hlt : W.b < m.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  refine ⟨hop.threads, hop.csize, hop.clocks, hop.bsize, fun l hl => hop.cells l hl,
    fun l hl => hw'.cellIn hl, KMono.set hb ha' hk hset,
    KeepsExt.set hb hl' hs' hk' hset,
    fun hd => LDMono.set hb (fun h => by rw [← hl']; exact h) ha' (Nat.le_of_eq hs') hset
      (Nat.le_of_eq (by rw [hk'])) hd,
    fun b x hx => ?_, fun hwf => ?_, fun e he => ?_,
    MemAuth.Keep.set (m' := { m' with current := m.current }) hb hset hl' ha' hs' hk' hop.aux.1
      (by rw [hop.aux.2.1]) hop.aux.2.2, hop.cov⟩
  · rcases hop.atoms with e | ⟨e, -⟩
    · rw [← keys_toList, e, keys_toList]
    · rw [← keys_toList, e, Array.toList_push, keys_toList, tagOf_append_single]
      have : ¬ Full.Covers b x (W.b, W.o, nb) := fun ⟨h1, h2, h3⟩ => hx ⟨h1.symm, h2, h3⟩
      simp [this]
  · rcases hop.atoms with e | ⟨e, hno⟩
    · rw [← keys_toList, e, keys_toList]; exact hwf
    · rw [← keys_toList, e, Array.toList_push, keys_toList]
      refine ⟨fun s hs => ?_, List.pairwise_append.mpr ⟨hwf.2, by simp, fun a ha b hb => ?_⟩⟩
      · rcases List.mem_append.mp hs with h | h
        · exact hwf.1 s h
        · simp at h; subst h; exact hsz0
      · simp at hb; subst hb
        obtain ⟨l, hlm, rfl⟩ : ∃ l ∈ m.atomics, ALoc.shape l = a := by
          simpa [shapes] using ha
        intro hlb
        simp only [ALoc.shape] at hlb ⊢
        by_cases h1 : l.off < W.o + nb
        · by_cases h2 : W.o < l.off + l.len
          · exact absurd ⟨hlb, hw.only l hlm hlb h1 h2⟩ (hno l hlm)
          · exact .inl (by omega)
        · exact .inr (by omega)
  · rcases hop.fp e he with h | ⟨h1, h2, h3, -, -⟩
    · exact .inl h
    · refine .inr ⟨fun x hx1 hx2 => ⟨h1, by omega, by omega⟩, by
        rw [h1]; exact hlt⟩

/-- **A step of the lock's code keeps a word apart from the lock's.** -/
theorem keep_lockWordStep {L : LockWord} {t : ThreadId} {m m' : Mem} (hs : L.Step t m m')
    (hap : W.ApartL L) : W.Keep m m' := by
  have hsz0 := W.sz_pos
  refine ⟨fun x h1 h2 => hs.heap ?_, fun i l => ?_, fun l hl => ?_, fun e he => ?_,
    fun _ h => hs.allLe h, fun _ h => hs.someLe h⟩
  · rintro ⟨hb, h3, h4⟩; simp only at hb h3 h4
    rcases hap with h | h | h
    · exact h hb.symm
    · omega
    · omega
  · exact hs.first_iff W.b W.o (hap.ne.imp Ne.symm Ne.symm) i l
  · rcases hs.atomic_mem hl with h | hshape
    · exact .inl h
    · obtain ⟨hb, ho, hlen⟩ : l.block = L.b ∧ l.off = L.o ∧ l.len = 4 := by
        simpa only [ALoc.shape, LockWord.shape, Prod.mk.injEq] using hshape
      rcases hap with h | h | h
      · exact .inr (.inl (by rw [hb]; exact h))
      · exact .inr (.inr (.inl (by omega)))
      · exact .inr (.inr (.inr (by omega)))
  · rcases hs.fp e he with h | ⟨hb, ho, hl, -⟩
    · exact .inl h
    · refine .inr fun ⟨hb', x, h1, h2, h3, h4⟩ => ?_
      rw [hb] at hb'
      rcases hap with h | h | h
      · exact h hb'
      · omega
      · omega

/-- The word's location stays under an atomic-location map whose frame has the word's bytes. -/
theorem loc_amap {m m' : Mem} {hF : Heap} {σ : Nat → Option Nat} (ha : AMap hF m m' σ)
    (hwF : ∀ l, W.In l → hF l ≠ none) (hok : ∀ i l, W.Loc m i l → l.len = nb) (l : ALoc) :
    (∃ i, W.Loc m' i l) ↔ (∃ i, W.Loc m i l) := by
  have := W.sz_pos
  refine (ha.first_iff (p := fun l => l.block == W.b && l.off == W.o)
    (fun l l' hb ho _ => by simp [hb, ho]) (fun i l hfi hl x h1 h2 => ?_)
    (fun l hp hpos => ⟨l.off, Nat.le_refl _, by omega, ?_⟩) l).symm
  · have hlen := hok i l ⟨hfi, hl⟩
    have hp : (l.block == W.b && l.off == W.o) = true := by
      have := Array.of_findIdx?_eq_some hfi; rw [hl] at this; exact this
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨hb, ho⟩ := hp
    rw [hb]; exact hwF _ ⟨rfl, by omega, by omega⟩
  · simp only [Bool.and_eq_true, beq_iff_eq] at hp
    rw [hp.1, hp.2]; exact hwF _ ⟨rfl, Nat.le_refl _, by omega⟩

/-- **The word's location stays** over a step whose frame `hF` has the word (`FStepIn`): the
word's location (if any) has the word's bytes (`hok`), so it is in the frame. -/
theorem loc_fstep {m m' : Mem} {hF : Heap} (hs : FStepIn hF m m')
    (hwF : ∀ l, W.In l → hF l ≠ none) (hok : ∀ i l, W.Loc m i l → l.len = nb) (l : ALoc) :
    (∃ i, W.Loc m' i l) ↔ (∃ i, W.Loc m i l) := by
  obtain ⟨σ, ha⟩ := hs.atomics
  exact loc_amap ha hwF hok l

/-- A native step whose frame contains the word preserves its validity when
the word's heap cells agree up to normalization. -/
theorem Ok.fstep {m m' : Mem} {hF : Heap} (hw : W.Ok m)
    (hs : FStepIn hF m m') (hwF : ∀ l, W.In l → hF l ≠ none)
    (hcells : ∀ l, W.In l →
      (m'.heap l).map Cell.norm = (m.heap l).map Cell.norm) : W.Ok m' := by
  have hsz0 := W.sz_pos
  have hkeys : ∀ x, W.o ≤ x → x < W.o + nb →
      (m'.heap (W.b, x)).map cellKey = (m.heap (W.b, x)).map cellKey := by
    intro x h1 h2
    have h := congrArg (Option.map cellKey) (hcells (W.b, x) ⟨rfl, h1, h2⟩)
    simpa [Option.map_map, Function.comp_def, cellKey_norm] using h
  obtain ⟨hb', hcur⟩ := Word.congr hkeys hw.blk
  have hloc := loc_fstep hs hwF (fun i l hl => (hw.loc i l hl).1)
  obtain ⟨σ, ha⟩ := hs.atomics
  refine ⟨hb', fun l hl hb h1 h2 => ?_, fun i l hl => ?_, fun e he hh => ?_, ?_,
    fun i l hl => ?_⟩
  · rcases ha.mem hl with ⟨l₀, hl₀, eb, eo, el⟩ | ⟨hpos, hoff⟩
    · have := hw.only l₀ hl₀ (eb.symm.trans hb) (by omega) (by omega)
      omega
    · exfalso
      have hx : ∃ x, l.off ≤ x ∧ x < l.off + l.len ∧ W.o ≤ x ∧ x < W.o + nb :=
        ⟨if W.o ≤ l.off then l.off else W.o, by split <;> omega,
          by split <;> omega, by split <;> omega, by split <;> omega⟩
      obtain ⟨x, hx1, hx2, hx3, hx4⟩ := hx
      have hf := hoff x hx1 hx2
      rw [hb] at hf
      exact hwF (W.b, x) ⟨rfl, hx3, hx4⟩ hf
  · obtain ⟨j, hj⟩ := (hloc l).mp ⟨i, hl⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := hw.loc j l hj
    exact ⟨h1, h2, h3, by rw [h4, hcur], h5⟩
  · rcases hs.fp e he with ⟨e₀, he₀, hn⟩ | ⟨-, hnt, -⟩
    · rcases hw.wfp e₀ he₀ (hits_narrows hn hh) with ⟨ha, u, hu, hle⟩ | ha
      · exact .inl ⟨by rw [hn.2.2.1]; exact ha, u, by rw [hs.threads]; exact hu,
          VClock.le_trans (VClock.le_trans hn.clock hle) (hs.clock u)⟩
      · exact .inr fun u hu =>
          VClock.le_trans (VClock.le_trans hn.clock (ha u (hs.threads ▸ hu))) (hs.clock u)
    · exact absurd (touches_of hh fun x h1 h2 => hwF (W.b, x) ⟨rfl, h1, h2⟩) hnt
  · obtain ⟨v, hv⟩ := hw.val
    exact ⟨v, by unfold Word.Holds; rw [hcur]; exact hv⟩
  · obtain ⟨j, hj⟩ := (hloc l).mp ⟨i, hl⟩
    exact (hw.plain j l hj).fstep hs fun x h1 h2 => hwF (W.b, x) ⟨rfl, h1, h2⟩

/-- An atomic-location map framed by a valid word preserves its complete history
when its normalized cells agree, including the initial plain singleton history. -/
theorem hist_amap {m m' : Mem} {hF : Heap} {σ : Nat → Option Nat} (hw : W.Ok m)
    (ha : AMap hF m m' σ) (hwF : ∀ l, W.In l → hF l ≠ none)
    (hcells : ∀ l, W.In l →
      (m'.heap l).map Cell.norm = (m.heap l).map Cell.norm) :
    W.hist m' = W.hist m := by
  have hloc := loc_amap ha hwF (fun i l hl => (hw.loc i l hl).1)
  cases hf : m.atomics.findIdx? (fun l => l.block == W.b && l.off == W.o) with
  | some i =>
    have hl := loc_of_find hf
    obtain ⟨j, hj⟩ := (hloc _).mpr ⟨i, hl⟩
    rw [hist_loc hl, hist_loc hj]
  | none =>
    have hn : ∀ i l, ¬ W.Loc m i l := fun i l hl => by rw [hl.1] at hf; cases hf
    have hn' : ∀ i l, ¬ W.Loc m' i l := fun i l hl => by
      obtain ⟨j, hj⟩ := (hloc l).mp ⟨i, hl⟩
      exact hn j l hj
    have hkeys : ∀ x, W.o ≤ x → x < W.o + nb →
        (m'.heap (W.b, x)).map cellKey = (m.heap (W.b, x)).map cellKey := by
      intro x h1 h2
      have h := congrArg (Option.map cellKey) (hcells (W.b, x) ⟨rfl, h1, h2⟩)
      simpa [Option.map_map, Function.comp_def, cellKey_norm] using h
    rw [hist_none hn, hist_none hn', (Word.congr hkeys hw.blk).2]


/-- A native framed step preserves the word's exact history, including the
plain singleton history before an atomic location exists. -/
theorem hist_fstep {m m' : Mem} {hF : Heap} (hw : W.Ok m)
    (hs : FStepIn hF m m') (hwF : ∀ l, W.In l → hF l ≠ none)
    (hcells : ∀ l, W.In l →
      (m'.heap l).map Cell.norm = (m.heap l).map Cell.norm) :
    W.hist m' = W.hist m := by
  obtain ⟨σ, ha⟩ := hs.atomics
  exact hist_amap hw ha hwF hcells

/-- **A step of a thread on its own part keeps the word** (`FStepIn`): its frame `hF` has the
word's bytes, the word's location has them (`hok`), and the word's cells stay up to `Cell.norm`
(`FLock.Inv.cellsN`). -/
theorem keepK_fstep {m m' : Mem} {hF : Heap}
    (hs : FStepIn hF m m') (hwF : ∀ l, W.In l → hF l ≠ none) (hok : ∀ i l, W.Loc m i l → l.len = nb)
    (hcells : ∀ l, W.In l → (m'.heap l).map Cell.norm = (m.heap l).map Cell.norm) :
    W.KeepK m m' := by
  have hcl : ∀ u : Nat, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true := hs.clock
  obtain ⟨σ, ha⟩ := hs.atomics
  refine ⟨fun x h1 h2 => ?_, loc_fstep hs hwF hok, fun l hl => ?_, fun e he => ?_,
    fun _ h u hu => VClock.le_trans (h u (hs.threads ▸ hu)) (hcl u),
    fun _ ⟨u, hu, hle⟩ => ⟨u, hs.threads ▸ hu, VClock.le_trans hle (hcl u)⟩⟩
  · have := congrArg (Option.map cellKey) (hcells (W.b, x) ⟨rfl, h1, h2⟩)
    simpa [Option.map_map, Function.comp_def, cellKey_norm] using this
  · rcases ha.mem hl with h | ⟨hpos, hoff⟩
    · exact .inl h
    · refine .inr (Classical.byContradiction fun hc => ?_)
      simp only [not_or, Nat.not_le, ne_eq, Classical.not_not] at hc
      obtain ⟨hb, h1, h2⟩ := hc
      have := W.sz_pos
      have hx := hoff (if W.o ≤ l.off then l.off else W.o) (by split <;> omega)
        (by split <;> omega)
      rw [hb] at hx
      exact hwF _ ⟨rfl, by split <;> omega, by split <;> omega⟩ hx
  · rcases hs.fp e he with h | ⟨-, hnt, -⟩
    · exact .inl h
    · exact .inr fun hh => hnt (touches_of hh fun x h1 h2 => hwF _ ⟨rfl, h1, h2⟩)

/-! ### The memory facts of an op, for the steps of a sync object's code

A step of a futex-based sync object's code (`FEvent.MStep`, `FCond.MStep`) is an op at one of
its words, a futex wait's sleep (an op that keeps the word's writes, then a new waiter), or a
change of the current thread, the futex queue or the woken threads only. The lemmas
`FEvent.MStep.*` and `FCond.MStep.*` give what such a step does to the memory, from these facts of
an op. -/

/-- The block `b` after an op at the word: as live, as large and of the same kind. -/
theorem Op.block {t : ThreadId} {m m' : Mem} (h : W.Op t m m') {b : BlockId} {blk : Block}
    (hb : m.blocks[b]? = some blk) : ∃ blk', m'.blocks[b]? = some blk' ∧ blk'.live = blk.live ∧
      blk'.bytes.size = blk.bytes.size ∧ blk'.kind = blk.kind := by
  by_cases e : b = W.b
  · subst e
    obtain ⟨blk', h1, -, h2, h3, h4, -⟩ := h.blocks.word blk hb
    exact ⟨blk', h1, h2, h4, h3⟩
  · exact ⟨blk, by rw [h.blocks.other b e]; exact hb, rfl, rfl, rfl⟩

/-- An op at the word keeps the atomic location of a lock's word apart from it. -/
theorem Op.lockLoc {t : ThreadId} {m m' : Mem} (h : W.Op t m m') {L : LockWord}
    (hap : W.ApartL L) {i : Nat} {l : ALoc} (hl : L.Loc m i l) : L.Loc m' i l :=
  (h.locs.same _ _ hap.ne i l).mpr hl

/-- An op at the word: a new access is at the word. -/
theorem Op.fpAt {t : ThreadId} {m m' : Mem} (h : W.Op t m m') :
    ∀ e ∈ m'.footprint, e ∈ m.footprint ∨ (e.block = W.b ∧ e.off = W.o) := fun e he =>
  (h.fp e he).imp id fun ⟨h1, h2, _⟩ => ⟨h1, h2⟩

/-- An op at the word keeps a word `W'` apart from it that is valid before: valid after it,
with the same writes. -/
theorem Op.word {n' nb' : Nat} {W' : Word n' nb'} {t : ThreadId} {m m' : Mem} (h : W.Op t m m')
    (hok : W'.Ok m) (hap : W.b ≠ W'.b ∨ W.o + nb ≤ W'.o ∨ W'.o + nb' ≤ W.o) :
    W'.Ok m' ∧ W'.hist m' = W'.hist m :=
  ⟨hok.keep (keep_op h hap), hist_keep hok (keep_op h hap)⟩

/-- A change of the futex queue keeps every word. -/
theorem keep_waiters (m : Mem) (ws : Array (ThreadId × Ptr)) : W.Keep m { m with waiters := ws } :=
  keep_of rfl rfl rfl rfl fun _ => VClock.le_refl _

end Word
end Conc

namespace Full

open FAssn Conc Proto

namespace FLock

variable {γ : Type} {L : FLock γ} {n nb : Nat} {W : Word n nb}

/-- A rest with the same bytes up to `Cell.norm` and the same knowledge and ghost state. -/
theorem Inv.congrX {G : ThreadId → γ} {rX rX' : Res} {m : Mem} (hi : L.Inv G rX m)
    (hs : FHeap.Sim rX'.heap rX.heap) (hk : rX'.know = rX.know) (hg : rX'.gh = rX.gh) :
    L.Inv G rX' m := by
  obtain ⟨rL, ho, hLoff, hLX, hF, hnF⟩ := hi.rest
  have hn : ∀ l, rX'.heap l = none ↔ rX.heap l = none := fun l => hs.none
  refine ⟨hi.w, ⟨rL, ho.congrRest (fun l => ?_) (by simp [hk]) (by simp [hg]), hLoff,
    fun l => (hLX l).imp id (fun h => (hn l).mpr h), hF, hnF⟩,
    LockWord.off_erase.mpr fun l hl => (hn l).mpr (LockWord.off_erase.mp hi.xoff l hl), hi.pdisj,
    hi.idle, hi.res⟩
  have := hs l
  simp only [FHeap.union_apply]
  cases (L.wordR m).heap l <;> cases rL.heap l <;> simp_all

/-- A byte of the rest is the memory's, up to `Cell.norm`. -/
theorem Inv.restCell {G : ThreadId → γ} {rX : Res} {m : Mem} (hi : L.Inv G rX m) {l : Zig.Loc}
    {fc : FCell} (hl : rX.heap l = some fc) : (m.heap l).map Cell.norm = some fc.cell.norm := by
  obtain ⟨rL, ho, -, hLX, -⟩ := hi.rest
  have hrL : rL.heap l = none := (hLX l).resolve_right (by simp [hl])
  have hwr : (L.wordR m).heap l = none := by
    by_cases hin : L.In l
    · have := LockWord.off_erase.mp hi.xoff l hin
      simp [hl] at this
    · exact cellsAt_none hin
  exact ho.rest_cell (by simp only [FHeap.union_apply, hl, hwr, hrL, Option.none_or])

/-- **Bytes of the rest are the memory's**: a part `r` of the rest with the bytes `bs` at `p`
(`0 < bs.size`): `p`'s block holds `bs` there. -/
theorem Inv.restBytes {G : ThreadId → γ} {rX r : Res} {m : Mem} (hi : L.Inv G rX m) {p : Ptr}
    {A S : Nat} {K : BlockKind} {bs : Array Byte} {b : BlockId} (hp : up (bytesAt p A S K bs) r)
    (hpb : p.block = some b) (hsub : ∀ l fc, r.heap l = some fc → rX.heap l = some fc)
    (hpos : 0 < bs.size) :
    ∃ blk, m.blocks[b]? = some blk ∧ blk.bytes.extract p.off.toNat (p.off.toNat + bs.size) = bs := by
  have cell : ∀ j (hj : j < bs.size), ∃ blk, m.blocks[b]? = some blk ∧
      blk.bytes[p.off.toNat + j]? = some bs[j] := by
    intro j hj
    obtain ⟨fc, hfc, hc⟩ := up_bytesAt_cell hp hpb hj
    have hn := hi.restCell (hsub _ _ hfc)
    cases e : m.heap (b, p.off.toNat + j) with
    | none => rw [e] at hn; cases hn
    | some c =>
      rw [e] at hn
      obtain ⟨blk, hb, -, hx, rfl⟩ := Mem.heap_some e
      have hbyte := congrArg Cell.byte (Option.some.inj hn)
      simp only [Cell.norm, hc] at hbyte
      exact ⟨blk, hb, by rw [Array.getElem?_eq_getElem hx, hbyte, getElem!_pos bs j hj]⟩
  obtain ⟨blk, hb, -⟩ := cell 0 hpos
  obtain ⟨blk', hb', hlast⟩ := cell (bs.size - 1) (by omega)
  rw [hb] at hb'; cases hb'
  have hlt := (Array.getElem?_eq_some_iff.mp hlast).1
  refine ⟨blk, hb, Array.ext (by simp only [Array.size_extract]; omega) fun j h1 h2 => ?_⟩
  obtain ⟨blk', hb', hx⟩ := cell j h2
  rw [hb] at hb'; cases hb'
  simp only [Array.getElem_extract]
  exact (Array.getElem?_eq_some_iff.mp hx).2

/-- The word's cells of the rest are the memory's, up to `Cell.norm`. -/
theorem Inv.cellsN {G : ThreadId → γ} {rY : Res} {m₀ m : Mem}
    (hi : L.Inv G (rsum (W.cellsR m₀) rY) m) {l : Zig.Loc} (hl : W.In l)
    (h0 : m₀.heap l ≠ none) : (m.heap l).map Cell.norm = (m₀.heap l).map Cell.norm := by
  cases e : m₀.heap l with
  | none => exact absurd e h0
  | some c =>
    rw [hi.restCell (fc := ⟨c, none⟩) (by simp [FHeap.union_apply, cellsAt_of hl, e])]; rfl

/-- **An op at a shared word apart from the lock's keeps the lock's invariant**, whose rest has
the word's cells: the rest gets the word's new cells. -/
theorem Inv.wordOp {G : ThreadId → γ} {rY : Res} {t : ThreadId} {m m' : Mem}
    (hi : L.Inv G (rsum (W.cellsR m) rY) m) (hWY : ∀ l, W.In l → rY.heap l = none) (hw : W.Ok m)
    (hw' : W.Ok m') (hop : W.Op t m m') (hap : W.ApartL L.toLockWord) :
    L.Inv G (rsum (W.cellsR m') rY) m' := by
  have hsz0 := W.sz_pos
  have hjb : joinedB m' = joinedB m := LockWord.joinedB_congr hop.threads
  have hown : L.own G m' = L.own G m := by funext u; unfold FLock.own; rw [hjb]
  have hnw : ∀ l, L.In l → ¬ W.In l := by
    rintro ⟨b, x⟩ ⟨h1, h2, h3⟩ ⟨h4, h5, h6⟩; simp only at h1 h2 h3 h4 h5 h6
    rcases hap with h | h | h
    · exact h (h1.symm.trans h4)
    · omega
    · omega
  have hLcells : ∀ x, L.o ≤ x → x < L.o + 4 → m'.heap (L.b, x) = m.heap (L.b, x) :=
    fun x h1 h2 => hop.cells _ (hnw _ ⟨rfl, h1, h2⟩)
  obtain ⟨hblk', hcur⟩ := LockWord.word_congr hLcells hi.w.blk
  have hU32 : ∀ v, L.U32 m' v ↔ L.U32 m v := fun v => by unfold LockWord.U32; rw [hcur]
  have hloc : ∀ i l, L.Loc m' i l ↔ L.Loc m i l := fun i l => hop.locs.same L.b L.o hap.ne i l
  have hWb : W.b < m.blocks.size := by
    obtain ⟨blk, hb, -⟩ := hw.blk; exact (Array.getElem?_eq_some_iff.mp hb).1
  have hcl : ∀ u < m.threads.size, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true :=
    fun u _ => hop.clocks u
  -- a new access is at the word, so it does not touch the lock's word
  have hnL : ∀ e ∈ m'.footprint, e ∉ m.footprint → ¬ L.Hits e := by
    intro e he hn ⟨hb, x, h1, h2, h3, h4⟩
    rcases hop.fp e he with h' | ⟨hb', ho, hl, -⟩
    · exact hn h'
    · rw [hb'] at hb; rw [ho] at h1; rw [ho, hl] at h2
      rcases hap with h | h | h
      · exact h hb.symm
      · omega
      · omega
  have hwi : L.WInv (L.pl G) m' := by
    refine ⟨by rw [hop.csize, hop.threads]; exact hi.w.csize, fun u hu => ?_, hblk', ?_, hi.w.one,
      ⟨fun l hl hb h1 h2 => ?_, fun i l hl => ?_, fun i l hl => ?_⟩, fun e he hh => ?_,
      fun i l hl => ?_, by rw [hop.waiters]; exact hi.w.fq, fun hp => ?_,
      fun u hu => let ⟨i, l, hl, hw⟩ := hi.w.owner u hu; ⟨i, l, (hloc i l).mpr hl, hw⟩⟩
    · rw [hop.threads, hjb]; exact hi.w.live u hu
    · obtain ⟨w, hw', hu, hz⟩ := hi.w.word; exact ⟨w, hw', (hU32 _).mpr hu, hz⟩
    · rcases hop.locs.new l hl with h | ⟨hb', ho, hlen⟩
      · exact hi.w.loc.only l h hb h1 h2
      · rw [ho] at h1; rw [ho, hlen] at h2; rw [hb'] at hb
        rcases hap with h | h | h
        · exact absurd hb.symm h
        · omega
        · omega
    · obtain ⟨h1, h2, h3, h4, h5⟩ := hi.w.loc.ok i l ((hloc i l).mp hl)
      exact ⟨h1, h2, h3, h4, by rw [h5, hcur]⟩
    · exact (hi.w.loc.plain i l ((hloc i l).mp hl)).of_fp fun e he =>
        (hop.fp e he).imp id fun h => plainHit_atomic h.2.2.2.1
    · by_cases hm : e ∈ m.footprint
      · rcases hi.w.wfp e hm hh with ⟨ha, hs⟩ | ha
        · exact .inl ⟨ha, LockWord.someLe_mono hop.threads hcl hs⟩
        · exact .inr (LockWord.LiveLe.mono hop.threads hcl ha)
      · exact absurd hh (hnL e he hm)
    · obtain ⟨h1, h2⟩ := hi.w.rel i l ((hloc i l).mp hl)
      exact ⟨LockWord.someLe_mono hop.threads hcl h1,
        fun u hu => VClock.le_trans (h2 u hu) (hop.clocks u)⟩
    · obtain ⟨v, hv, hq, h1, h2⟩ := hi.w.wit (hop.waiters ▸ hp)
      exact ⟨v, hop.threads ▸ hv, hop.waiters ▸ hq, h1, fun hh => (hU32 _).mpr (h2 hh)⟩
  obtain ⟨rL, ho, hLoff, hLX, hF, hnF⟩ := hi.rest
  -- the rest as `cells W ⋆ (word ⋆ (rL ⋆ rY))`
  have hWw : FHeap.Disjoint (W.cellsR m).heap (L.wordR m).heap := fun l => by
    by_cases hl : W.In l
    · exact .inr (cellsAt_none fun h => hnw l h hl)
    · exact .inl (cellsAt_none hl)
  have hXY := FHeap.disjoint_union_right.mp hLX
  -- `rL` has no byte of the word
  have hLW : ∀ l, W.In l → rL.heap l = none := fun l hl =>
    (hXY.1 l).resolve_right (cellsAt_some hl (hw.cellIn hl))
  have hLW' : FHeap.Disjoint rL.heap (W.cellsR m').heap := fun l => by
    by_cases hl : W.In l
    · exact .inl (hLW l hl)
    · exact .inr (cellsAt_none hl)
  have hWw' : FHeap.Disjoint (W.cellsR m').heap (L.wordR m).heap := fun l => by
    by_cases hl : W.In l
    · exact .inr (cellsAt_none fun h => hnw l h hl)
    · exact .inl (cellsAt_none hl)
  -- regroup `word ⋆ (rL ⋆ (C ⋆ rY))` as `C ⋆ (word ⋆ (rL ⋆ rY))`
  have regroup : ∀ C : Res, FHeap.Disjoint C.heap (L.wordR m).heap → FHeap.Disjoint rL.heap C.heap →
      rsum (L.wordR m) (rsum rL (rsum C rY)) = rsum C (rsum (L.wordR m) (rsum rL rY)) := by
    intro C h1 h2
    rw [← rsum_assoc (a := rL), rsum_comm h2, rsum_assoc, ← rsum_assoc (a := L.wordR m),
      rsum_comm h1.symm, rsum_assoc]
  have hwR : L.wordR m' = L.wordR m := by
    simp only [LockWord.wordR, cellsAt]
    congr 1; funext ⟨b, x⟩
    split
    · rename_i hl; obtain ⟨h1, h2, h3⟩ := hl; simp only at h1 h2 h3; subst h1
      rw [hLcells x h2 h3]
    · rfl
  rw [regroup _ hWw hXY.1] at ho
  have ho' := ho.restStep (hop.rest hw hw') (fun l hl => hw.cellIn hl) (fun l hl => by
    simp only [FHeap.union_apply, cellsAt_none (fun h => hnw l h hl), hLW l hl, hWY l hl]; rfl)
  rw [← regroup _ hWw' hLW', ← hwR, ← hown] at ho'
  refine ⟨hwi, ⟨rL, ho', hLoff, FHeap.disjoint_union_right.mpr ⟨hLW', hXY.2⟩, fun hF' => ?_, hnF⟩,
    LockWord.off_erase.mpr fun l hl => ?_, hi.pdisj, hi.idle, hi.res⟩
  · obtain ⟨hR, hO⟩ := hF hF'
    refine ⟨hR, fun e he htc => ?_⟩
    by_cases hm : e ∈ m.footprint
    · rcases hO e hm (htc.imp id fun h => by rw [← hop.bsize]; exact h) with h | ⟨i, l, hl, hle⟩
      · exact .inl (LockWord.LiveLe.mono hop.threads hcl h)
      · exact .inr ⟨i, l, (hloc i l).mpr hl, hle⟩
    · rcases hop.fp e he with h | ⟨hb, heo, hlen, -⟩
      · exact absurd h hm
      · rcases htc with ⟨x, h1, h2, h3⟩ | hbe
        · rw [hb] at h3; rw [heo] at h1; rw [heo, hlen] at h2
          exact absurd (by simp [FHeap.erase, hLW (W.b, x) ⟨rfl, h1, by omega⟩]) h3
        · rw [hb, hop.bsize] at hbe; exact absurd hWb (Nat.not_lt.mpr hbe)
  · have := LockWord.off_erase.mp hi.xoff l hl
    simp only [FHeap.union_apply, Option.or_eq_none_iff]
      at this ⊢
    exact ⟨cellsAt_none fun h => hnw l hl h, this.2⟩

/-- An actual native step at a shared word preserves an apart lock and the rest of its
resources. The lock's framed location may move to its mapped index. -/
theorem Inv.wordStep {G : ThreadId → γ} {rY : Res} {m m' : Mem}
    (hi : L.Inv G (rsum (W.cellsR m) rY) m) (hWY : ∀ l, W.In l → rY.heap l = none)
    (hw : W.Ok m) (hr : RestStep W.In m m')
    (hs : ∀ hF, (∀ x, W.o ≤ x → x < W.o + nb → hF (W.b, x) = none) → FStepIn hF m m')
    (hap : W.ApartL L.toLockWord) : L.Inv G (rsum (W.cellsR m') rY) m' := by
  have hjb : joinedB m' = joinedB m := LockWord.joinedB_congr hr.threads
  have hown : L.own G m' = L.own G m := by funext u; unfold FLock.own; rw [hjb]
  have hnw : ∀ l, L.In l → ¬ W.In l := by
    rintro ⟨b, x⟩ ⟨h1, h2, h3⟩ ⟨h4, h5, h6⟩
    simp only at h1 h2 h3 h4 h5 h6
    rcases hap with h | h | h
    · exact h (h1.symm.trans h4)
    · omega
    · omega
  have hLcells : ∀ x, L.o ≤ x → x < L.o + 4 → m'.heap (L.b, x) = m.heap (L.b, x) :=
    fun x h1 h2 => hr.heap _ (hnw _ ⟨rfl, h1, h2⟩)
  obtain ⟨rL, ho, hLoff, hLX, hF, hnF⟩ := hi.rest
  have hXY := FHeap.disjoint_union_right.mp hLX
  have hLW : ∀ l, W.In l → rL.heap l = none := fun l hl =>
    (hXY.1 l).resolve_right (cellsAt_some hl (hw.cellIn hl))
  have hframe := hs (rsum (L.wordR m) rL).heap.erase (fun x h1 h2 => by
    simp only [FHeap.erase, FHeap.union_apply,
      cellsAt_none (fun h => hnw (W.b, x) h ⟨rfl, h1, h2⟩), hLW (W.b, x) ⟨rfl, h1, h2⟩]
    rfl)
  have hframeL : ∀ x, L.o ≤ x → x < L.o + 4 →
      (rsum (L.wordR m) rL).heap.erase (L.b, x) ≠ none := by
    intro x h1 h2
    have hcell := cellsAt_some (m := m) (W := L.In) ⟨rfl, h1, h2⟩ (hi.w.blk.cell h1 h2)
    simp only [FHeap.erase, FHeap.union_apply]
    cases he : (L.wordR m).heap (L.b, x) with
    | none => exact (hcell he).elim
    | some fc => simp
  have hwi := hi.w.stepIn hframe hframeL (fun x h1 h2 => by rw [hLcells x h1 h2])
  have hWw : FHeap.Disjoint (W.cellsR m).heap (L.wordR m).heap := fun l => by
    by_cases hl : W.In l
    · exact .inr (cellsAt_none fun h => hnw l h hl)
    · exact .inl (cellsAt_none hl)
  have hLW' : FHeap.Disjoint rL.heap (W.cellsR m').heap := fun l => by
    by_cases hl : W.In l
    · exact .inl (hLW l hl)
    · exact .inr (cellsAt_none hl)
  have hWw' : FHeap.Disjoint (W.cellsR m').heap (L.wordR m).heap := fun l => by
    by_cases hl : W.In l
    · exact .inr (cellsAt_none fun h => hnw l h hl)
    · exact .inl (cellsAt_none hl)
  have regroup : ∀ C : Res, FHeap.Disjoint C.heap (L.wordR m).heap →
      FHeap.Disjoint rL.heap C.heap →
      rsum (L.wordR m) (rsum rL (rsum C rY)) = rsum C (rsum (L.wordR m) (rsum rL rY)) := by
    intro C h1 h2
    rw [← rsum_assoc (a := rL), rsum_comm h2, rsum_assoc, ← rsum_assoc (a := L.wordR m),
      rsum_comm h1.symm, rsum_assoc]
  have hwR : L.wordR m' = L.wordR m := by
    simp only [LockWord.wordR, cellsAt]
    congr 1; funext ⟨b, x⟩
    split
    · rename_i hl
      obtain ⟨h1, h2, h3⟩ := hl
      simp only at h1 h2 h3; subst h1
      rw [hLcells x h2 h3]
    · rfl
  rw [regroup _ hWw hXY.1] at ho
  have ho' := ho.restStep hr (fun l hl => hw.cellIn hl) (fun l hl => by
    simp only [FHeap.union_apply, cellsAt_none (fun h => hnw l h hl), hLW l hl, hWY l hl]
    rfl)
  rw [← regroup _ hWw' hLW', ← hwR, ← hown] at ho'
  refine ⟨hwi, ⟨rL, ho', hLoff, FHeap.disjoint_union_right.mpr ⟨hLW', hXY.2⟩,
    fun hfree => ?_, hnF⟩, LockWord.off_erase.mpr fun l hl => ?_, hi.pdisj, hi.idle, hi.res⟩
  · obtain ⟨hR, hO⟩ := hF hfree
    refine ⟨hR, hO.stepIn hframe (fun l hl => ?_) hframeL
      (fun i l hl => (hi.w.loc.ok i l hl).1)⟩
    simp only [FHeap.erase, FHeap.union_apply] at hl ⊢
    cases (L.wordR m).heap l <;> simp_all
  · have hoff := LockWord.off_erase.mp hi.xoff l hl
    simp only [FHeap.union_apply, Option.or_eq_none_iff] at hoff ⊢
    exact ⟨cellsAt_none fun h => hnw l hl h, hoff.2⟩

/-! ## A futex wait and a futex wake at the word -/

/-- The same memory, but `current`, the futex queue and the woken threads, with ghost values `G'`
whose word invariant holds there and that have the same parts, resources and holders. -/
theorem Inv.requeue {G G' : ThreadId → γ} {rX : Res} {m : Mem} (hi : L.Inv G rX m)
    (c : ThreadId) (ws : Array (ThreadId × Ptr)) (wk : Array ThreadId)
    (hw : L.WInv (L.pl G') { m with current := c, waiters := ws, woken := wk })
    (hpart : ∀ u, L.part (G' u) = L.part (G u)) (hheld : ∀ u, L.held (G' u) = L.held (G u))
    (hholds : ∀ u, L.ph (G' u) = .holds ↔ L.ph (G u) = .holds)
    (hg : ∀ u, L.ph (G' u) ≠ .gone → L.ph (G u) ≠ .gone) (hR : ∀ r, L.R G r ↔ L.R G' r) :
    L.Inv G' rX { m with current := c, waiters := ws, woken := wk } := by
  obtain ⟨rL, ho, hLoff, hLX, hF, hnF⟩ := hi.rest
  have hown : L.own G' { m with current := c, waiters := ws, woken := wk } = L.own G m := by
    funext u; unfold FLock.own; rw [hpart, hheld]; rfl
  have hfree := free_iff_of (L := L) hholds
  refine ⟨hw, ⟨rL, ?_, hLoff, hLX, fun hF' => ?_, fun h => hnF fun h' => h (hfree.mpr h')⟩,
    hi.xoff, fun u => by rw [hpart, hheld]; exact hi.pdisj u,
    fun u hu => by rw [hheld]; exact hi.idle u ((not_congr (hholds u)).mp hu),
    fun u hu => by rw [hheld]; exact (hR _).mp (hi.res u ((hholds u).mp hu))⟩
  · rw [hown]
    have : LockWord.wordR L.toLockWord { m with current := c, waiters := ws, woken := wk } =
        L.wordR m := rfl
    rw [this]; exact ho.keep rfl rfl rfl rfl rfl
  · obtain ⟨h1, h2⟩ := hF (hfree.mp hF')
    exact ⟨(hR _).mp h1, (h2.weaken hg).mono rfl rfl rfl (fun _ => VClock.le_refl _)
      fun e he => .inl he⟩

/-- Thread `t`, which does not hold the lock, goes to `out` at a stop (`current := t`) where the
word's invariant holds with `t` at `out`. -/
theorem Inv.toOut {G : ThreadId → γ} {rX : Res} {m : Mem} {t : ThreadId} (hi : L.Inv G rX m)
    (hc : m.current = t) (hnh : L.ph (G t) ≠ .holds) (hng : L.ph (G t) ≠ .gone)
    (hw : L.WInv (upd (L.pl G) t .out) m) :
    L.Inv (upd G t (L.set (G t) .out rnil)) rX m := by
  have hupd : ∀ u, L.ph (upd G t (L.set (G t) .out rnil) u) = if u = t then .out else L.ph (G u) :=
    fun u => by unfold upd; split <;> simp [L.ph_set]
  have := hi.requeue m.current m.waiters m.woken (G' := upd G t (L.set (G t) .out rnil))
    (by rw [pl_upd_set]; exact hw)
    (fun u => by
      unfold upd; split
      · rename_i e; subst e; rw [L.part_set]
      · rfl)
    (fun u => by
      unfold upd; split
      · rename_i e; subst e; rw [L.held_set, hi.idle _ hnh]
      · rfl)
    (fun u => by rw [hupd]; split <;> simp_all)
    (fun u hu => by rw [hupd] at hu; split at hu <;> simp_all)
    (fun r => by rw [L.R_set])
  exact this

/-- A futex wait of thread `t` (`away`, not in the queue) at a shared word `W` (its bytes in the
protocol's rest, apart from the lock's word). If it sleeps, the lock's invariant holds with `t` in
the queue; else `t` goes to `out`. -/
theorem Inv.waitOff {W : Word 32 4} {G : ThreadId → γ} {rX : Res} {m m' : Mem} {t : ThreadId}
    {e : BitVec 32} {b : Bool} (hi : L.Inv G rX m) (hph : L.ph (G t) = .away) (hW : W.Ok m)
    (hap : W.ApartL L.toLockWord) (hX : ∀ l, W.In l → rX.heap l ≠ none)
    (hq : m.waiters.any (·.1 == t) = false)
    (h : ((Thread.futexWait W.ptr e).run { m with current := t }).run = some (.ok (b, m'))) :
    if b then L.Inv G rX m' else
      (m'.current = t ∧ L.Inv (upd G t (L.set (G t) .out rnil)) rX m') := by
  have hng : L.ph (G t) ≠ .gone := by rw [hph]; decide
  have hnh : L.ph (G t) ≠ .holds := by rw [hph]; decide
  obtain ⟨ht, -⟩ := hi.ht hng
  obtain ⟨blk₀, hb₀, -, -, ha₀, -⟩ := hW.access
  have hWb : W.b < m.blocks.size := (Array.getElem?_eq_some_iff.mp hb₀).1
  have hoff : ∀ bid blk o, m.access W.ptr 4 4 = pure (bid, blk, o) →
      bid ≠ L.b ∨ o + 4 ≤ L.o ∨ L.o + 4 ≤ o := fun bid blk o ha => by
    rw [ha₀] at ha; cases ha
    rcases hap with h | h | h
    · exact .inl (Ne.symm h)
    · exact .inr (.inr h)
    · exact .inr (.inl h)
  have hw := hi.w.waitOff (t := t) (by exact hph) hap.ptr_ne hoff hq h
  -- the relabel of `t` from `away` to `out`, at a memory with the same parts
  have hrel : ∀ M : Mem, L.Inv G rX M → M.current = t →
      L.WInv (upd (L.pl G) t .out) M → L.Inv (upd G t (L.set (G t) .out rnil)) rX M :=
    fun _ hiM hc hwM => hiM.toOut hc hnh hng hwM
  rcases futexWait_eq h with ⟨-, rfl, rfl⟩ | ⟨-, bid, blk, o, v, ha, -, -, hc⟩
  · simp only [Bool.false_eq_true, ↓reduceIte] at hw ⊢
    exact ⟨by first | rfl | trivial, hrel _ (hi.requeue t m.waiters _ (hi.w.same t m.seen m.nextMsg _ |>.groups m.groups)
      (fun _ => rfl) (fun _ => rfl) (fun _ => Iff.rfl) (fun _ h => h) (fun _ => Iff.rfl)) rfl hw.2⟩
  have ha' : m.access W.ptr 4 4 = pure (bid, blk, o) := ha
  rw [ha₀] at ha'; cases ha'
  have hiR : L.Inv G rX (({ m with current := t } : Mem).recordAt W.b W.o 4 .atomicRead) :=
    (hi.cur t).recordX (by decide) rfl ht hWb (by decide)
      (fun x h1 h2 => hX _ ⟨rfl, h1, h2⟩)
  rcases hc with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
  · simp only [↓reduceIte] at hw ⊢
    exact hiR.requeue t _ _ hw (fun _ => rfl) (fun _ => rfl) (fun _ => Iff.rfl) (fun _ h => h)
      (fun _ => Iff.rfl)
  · simp only [Bool.false_eq_true, ↓reduceIte] at hw ⊢
    exact ⟨hw.1, hrel _ hiR rfl hw.2⟩

/-- A spurious return of a futex wait of thread `t` (`away`, not in the queue) at a shared word:
`t` goes to `out` with the memory before the wait. -/
theorem Inv.spuriousOff {G : ThreadId → γ} {rX : Res} {m : Mem} {t : ThreadId}
    (hi : L.Inv G rX m) (hph : L.ph (G t) = .away) (hq : m.waiters.any (·.1 == t) = false) :
    L.Inv (upd G t (L.set (G t) .out rnil)) rX { m with current := t } :=
  (hi.cur t).toOut rfl (by rw [hph]; decide) (by rw [hph]; decide) (hi.w.spuriousOff (t := t) (by exact hph) hq).2

/-- A futex wake by thread `t` at a shared word apart from the lock's: the lock's invariant
holds. -/
theorem Inv.wakeOff {W : Word 32 4} {G : ThreadId → γ} {rX : Res} {m m' : Mem} {t : ThreadId}
    {k : Nat} {cs : List Nat} (hi : L.Inv G rX m) (hap : W.ApartL L.toLockWord)
    (h : ((Thread.futexWake W.ptr k cs).run { m with current := t }).run = some (.ok ((), m'))) :
    L.Inv G rX m' := by
  have hw := hi.w.wakeOff hap.ptr_ne h
  have hm' := Proto.modify_ok h
  subst hm'
  exact hi.requeue t _ _ hw (fun _ => rfl) (fun _ => rfl) (fun _ => Iff.rfl) (fun _ h => h)
    (fun _ => Iff.rfl)

end FLock

end Full
end Zig

/-! ## Per-thread observed-message floors

The floor is a position in the word's history, derived from `Mem.seen` and distinct
message ids. Reads may advance it; steps disjoint from the framed word preserve it,
including when retiring another location reindexes the word. These are memory-model
facts for the full-state protocol library, not additional client assumptions. -/

namespace Zig
namespace Conc
namespace Word

open Proto Full

variable {n nb : Nat} {W : Word n nb}

variable (W) in
/-- Thread `u`'s floor at the word (module doc): the position of the message of the word's
location that `u` read or wrote last (`Mem.seenAt`); `0` without one. -/
def ownPos (m : Mem) (u : ThreadId) : Nat :=
  match m.atomics.findIdx? (fun l => l.block == W.b && l.off == W.o) with
  | some i => ((m.seenAt u i).bind (m.atomics[i]!).pos).getD 0
  | none => 0

variable (W) in
/-- The word's messages have distinct ids, each below the message counter. -/
def Fresh (m : Mem) : Prop :=
  ∀ i l, W.Loc m i l → ∀ j (hj : j < l.msgs.size),
    l.msgs[j].id < m.nextMsg ∧ l.pos l.msgs[j].id = some j

theorem ownPos_loc {m : Mem} {i : Nat} {l : ALoc} (hl : W.Loc m i l) (u : ThreadId) :
    W.ownPos m u = ((m.seenAt u i).bind l.pos).getD 0 := by
  unfold ownPos; rw [hl.1]; simp only; rw [(loc_get hl).2.2]

theorem ownPos_none {m : Mem} (h : ∀ i l, ¬ W.Loc m i l) (u : ThreadId) : W.ownPos m u = 0 := by
  unfold ownPos
  cases hf : m.atomics.findIdx? (fun l => l.block == W.b && l.off == W.o) with
  | none => rfl
  | some i => exact absurd (loc_of_find hf) (h _ _)

/-- The same locations and views: the same floors. -/
theorem ownPos_of_eq {m m' : Mem} (ha : m'.atomics = m.atomics) (hs : m'.seen = m.seen)
    (u : ThreadId) : W.ownPos m' u = W.ownPos m u := by
  unfold ownPos Mem.seenAt; rw [ha, hs]

theorem Fresh.of_eq {m m' : Mem} (hf : W.Fresh m) (ha : m'.atomics = m.atomics)
    (hn : m.nextMsg ≤ m'.nextMsg) : W.Fresh m' := fun i l hl j hj =>
  let ⟨h1, h2⟩ := hf i l (by unfold Loc at hl ⊢; rwa [ha] at hl) j hj
  ⟨Nat.lt_of_lt_of_le h1 hn, h2⟩

/-- **Thread `t`'s floor is at most where its next read may read** (`floorPos`). -/
theorem ownPos_le_floor {m : Mem} {i : Nat} {l : ALoc} (hl : W.Loc m i l) :
    W.ownPos m m.current ≤ floorPos m i := by
  rw [ownPos_loc hl]
  refine Nat.le_trans (Nat.le_of_eq ?_) (Nat.le_max_right _ _)
  rw [← (loc_get hl).2.2]
  split
  · rename_i id heq
    have hs : m.seenAt m.current i = some id := by
      unfold Mem.seenAt; exact (congrArg (Option.map (·.2.2)) heq : _)
    rw [hs]; rfl
  · rename_i heq
    have hs : m.seenAt m.current i = none := by
      unfold Mem.seenAt; exact (congrArg (Option.map (·.2.2)) heq : _)
    rw [hs]; rfl

/-! ## Steps that keep the word -/

/-- The word's location is found by its block and offset alone. -/
theorem pred_congr (l l' : ALoc) (hb : l.block = l'.block) (ho : l.off = l'.off)
    (_ : l.len = l'.len) :
    (l.block == W.b && l.off == W.o) = (l'.block == W.b && l'.off == W.o) := by
  simp [hb, ho]

/-- The word's location (of the word's size, `hok`) lies in a frame that has the word's bytes,
and every location at the word has a byte of it. -/
theorem frame_has {m : Mem} {hF : Heap}
    (hwF : ∀ x, W.o ≤ x → x < W.o + nb → hF (W.b, x) ≠ none)
    (hok : ∀ i l, W.Loc m i l → l.len = nb) :
    (∀ i l, m.atomics.findIdx? (fun l => l.block == W.b && l.off == W.o) = some i →
      m.atomics[i]? = some l → l.In hF) ∧
    (∀ l : ALoc, (l.block == W.b && l.off == W.o) = true → 0 < l.len →
      ∃ x, l.off ≤ x ∧ x < l.off + l.len ∧ hF (l.block, x) ≠ none) := by
  have := W.sz_pos
  refine ⟨fun i l hfi hl x h1 h2 => ?_, fun l hp hpos => ⟨l.off, Nat.le_refl _, by omega, ?_⟩⟩
  · have hL : W.Loc m i l := ⟨hfi, hl⟩
    obtain ⟨hb, ho⟩ := loc_at hL
    have hlen := hok i l hL
    rw [hb]; exact hwF x (by omega) (by omega)
  · simp only [Bool.and_eq_true, beq_iff_eq] at hp
    rw [hp.1, hp.2]; exact hwF W.o (Nat.le_refl _) (by omega)

/-- Atomic-location transport keeps every thread's floor at a fully framed word, independently
of changes to queues, the OS state or the selected current thread. -/
theorem ownPos_amap {m m' : Mem} {hF : Heap} {σ : Nat → Option Nat} (ha : AMap hF m m' σ)
    (hwF : ∀ x, W.o ≤ x → x < W.o + nb → hF (W.b, x) ≠ none)
    (hok : ∀ i l, W.Loc m i l → l.len = nb) (u : ThreadId) : W.ownPos m' u = W.ownPos m u := by
  obtain ⟨hin, hcov⟩ := frame_has hwF hok
  cases hf : m.atomics.findIdx? (fun l => l.block == W.b && l.off == W.o) with
  | some i =>
    have hl := loc_of_find hf
    obtain ⟨j, hij, hl'⟩ := ha.frame i _ hl.2 (hin i _ hf hl.2)
    have hL' : W.Loc m' j (m.atomics[i]!) := ⟨ha.first_eq pred_congr hin hcov hf hij, hl'⟩
    rw [ownPos_loc hl, ownPos_loc hL', ha.seenAt_frame hl.2 (hin i _ hf hl.2) hij u]
  | none =>
    have hn : ∀ i l, ¬ W.Loc m i l := fun i l hl => by rw [hl.1] at hf; cases hf
    refine (ownPos_none (fun j l hl => ?_) u).trans (ownPos_none hn u).symm
    obtain ⟨i, hi⟩ := (ha.first_iff pred_congr hin hcov l).mpr ⟨j, hl⟩
    exact hn i l hi

/-- **A step of a thread on its own part keeps every thread's floor** at a word whose bytes its
frame has (`FStepIn`; `hok`: the word's location has the word's size, as under `Word.Ok`). -/
theorem ownPos_fstep {m m' : Mem} {hF : Heap} (hs : FStepIn hF m m')
    (hwF : ∀ x, W.o ≤ x → x < W.o + nb → hF (W.b, x) ≠ none)
    (hok : ∀ i l, W.Loc m i l → l.len = nb) (u : ThreadId) : W.ownPos m' u = W.ownPos m u := by
  obtain ⟨σ, ha⟩ := hs.atomics
  exact ownPos_amap ha hwF hok u

/-- Atomic-location transport and a nondecreasing message counter preserve framed freshness. -/
theorem Fresh.amap {m m' : Mem} {hF : Heap} {σ : Nat → Option Nat} (hf : W.Fresh m)
    (ha : AMap hF m m' σ) (hn : m.nextMsg ≤ m'.nextMsg)
    (hwF : ∀ x, W.o ≤ x → x < W.o + nb → hF (W.b, x) ≠ none)
    (hok : ∀ i l, W.Loc m i l → l.len = nb) : W.Fresh m' := by
  intro j l hl k hk
  obtain ⟨i, hi⟩ := (loc_amap ha
    (fun ⟨b, x⟩ hx => by
      obtain ⟨hb, h1, h2⟩ := hx
      change b = W.b at hb
      change hF (b, x) ≠ none
      rw [hb]
      exact hwF x h1 h2) hok l).mp ⟨j, hl⟩
  obtain ⟨h1, h2⟩ := hf i l hi k hk
  exact ⟨Nat.lt_of_lt_of_le h1 hn, h2⟩

theorem Fresh.fstep {m m' : Mem} {hF : Heap} (hf : W.Fresh m) (hs : FStepIn hF m m')
    (hwF : ∀ x, W.o ≤ x → x < W.o + nb → hF (W.b, x) ≠ none)
    (hok : ∀ i l, W.Loc m i l → l.len = nb) : W.Fresh m' := by
  obtain ⟨σ, ha⟩ := hs.atomics
  exact hf.amap ha hs.nextMsg hwF hok

/-! ## The ops at the word -/

/-- A floor is a position of a nonempty location, including the default position zero. -/
theorem ownPos_lt {m : Mem} {i : Nat} {l : ALoc} (hl : W.Loc m i l)
    (h0 : 0 < l.msgs.size) (u : ThreadId) : W.ownPos m u < l.msgs.size := by
  rw [ownPos_loc hl]
  cases hs : m.seenAt u i with
  | none => exact h0
  | some id =>
    simp only [Option.bind_some]
    cases hp : l.pos id with
    | none => exact h0
    | some j =>
      exact ALoc.pos_lt hp

/-- Actual preparation at a valid word either keeps its location or creates its singleton
history. Its shape and floors do not require fresh ids; freshness, when present, is preserved. -/
theorem prepare {m m' : Mem} {li : Nat} {k : AccessKind} (hw : W.Ok m)
    (hk : k.isAtomic = true)
    (h : ((locIdx W.b W.o nb).run (m.recordAt W.b W.o nb k)).run = some (.ok (li, m'))) :
    ∃ l, W.Loc m' li l ∧ l.len = nb ∧ 0 < l.msgs.size ∧ l.Chain ∧ (W.Fresh m → W.Fresh m') ∧
      (∀ u, W.ownPos m' u = W.ownPos m u) ∧ m.nextMsg ≤ m'.nextMsg ∧ m'.current = m.current := by
  let mr := m.recordAt W.b W.o nb k
  have hfr (hf : W.Fresh m) : W.Fresh mr := hf.of_eq rfl (Nat.le_refl _)
  have hpos (u : ThreadId) : W.ownPos mr u = W.ownPos m u := ownPos_of_eq rfl rfl u
  cases he : mr.atomics.findIdx? (fun l => l.block == W.b && l.off == W.o) with
  | some i =>
    have hl := loc_of_find he
    have hl0 : W.Loc m i (mr.atomics[i]!) := hl
    obtain ⟨hlen, h0, hc, hlast, _⟩ := hw.loc i _ hl0
    have hpl : PlainLe mr W.b W.o nb (mr.atomics[i]!).lastClock :=
      (hw.plain i _ hl0).of_fp fun e he => by
        simp only [mr, Mem.recordAt, Array.mem_push] at he
        rcases he with he | rfl
        · exact .inl he
        · exact .inr (plainHit_atomic hk)
    obtain ⟨rfl, rfl⟩ := locIdx_found he hlen hlast hpl h
    exact ⟨_, hl, hlen, h0, hc, hfr, hpos, Nat.le_refl _, rfl⟩
  | none =>
    obtain ⟨rfl, rfl⟩ := locIdx_new he (noOverlap_of_only he hw.only) h
    let nl := firstLoc mr W.b W.o nb
    have hnl : W.Loc { mr with atomics := mr.atomics.push nl, nextMsg := mr.nextMsg + 1 }
        mr.atomics.size nl := by
      refine ⟨?_, by simp⟩
      show (mr.atomics.push nl).findIdx? _ = _
      rw [Array.findIdx?_push, he]; simp [nl, firstLoc]
    have h0 : 0 < nl.msgs.size := by simp [nl, firstLoc]
    refine ⟨nl, hnl, rfl, h0, ?_, ?_, ?_, Nat.le_succ _, rfl⟩
    · intro j hj; simp [nl, firstLoc] at hj
    · intro _ i l hl j hj
      obtain ⟨rfl, rfl⟩ := loc_unique hl hnl
      have : j = 0 := by simpa [nl, firstLoc] using hj
      subst j
      simp [nl, firstLoc, firstMsg, ALoc.pos]
    · intro u
      have hnew := ownPos_lt hnl h0 u
      have hold : W.ownPos mr u = 0 := ownPos_none (fun i l hl => by rw [hl.1] at he; cases he) u
      have : W.ownPos { mr with atomics := mr.atomics.push nl, nextMsg := mr.nextMsg + 1 } u = 0 := by
        simpa [nl, firstLoc] using hnew
      change W.ownPos { mr with atomics := mr.atomics.push nl, nextMsg := mr.nextMsg + 1 } u = _
      exact this.trans (hold.symm.trans (hpos u))

/-- Preparation preserves every floor and freshness without an operation-transport judgment. -/
theorem prepare_seen {m m' : Mem} {li : Nat} {k : AccessKind} (hw : W.Ok m)
    (hf : W.Fresh m) (hk : k.isAtomic = true)
    (h : ((locIdx W.b W.o nb).run (m.recordAt W.b W.o nb k)).run = some (.ok (li, m'))) :
    ∃ l, W.Loc m' li l ∧ l.len = nb ∧ 0 < l.msgs.size ∧ l.Chain ∧ W.Fresh m' ∧
      (∀ u, W.ownPos m' u = W.ownPos m u) ∧ m.nextMsg ≤ m'.nextMsg ∧ m'.current = m.current := by
  obtain ⟨l, hl, hlen, h0, hch, hfr, hpos, hn, hc⟩ := prepare hw hk h
  exact ⟨l, hl, hlen, h0, hch, hfr hf, hpos, hn, hc⟩

/-- The valid word cannot be contained in a frame disjoint from its bytes. -/
theorem loc_notIn {m : Mem} {i : Nat} {l : ALoc} {hF : Heap} (hl : W.Loc m i l)
    (hlen : l.len = nb) (hoff : ∀ x, W.o ≤ x → x < W.o + nb → hF (W.b, x) = none) :
    ¬ (m.atomics[i]!).In hF := by
  rw [(loc_get hl).2.2]
  intro hin
  obtain ⟨hb, ho⟩ := loc_at hl
  have hx := hin W.o (by omega) (by have := W.sz_pos; omega)
  rw [hb] at hx
  exact hx (hoff W.o (Nat.le_refl _) (by have := W.sz_pos; omega))

/-- The actual preparation carries the existing atomic-location map. Recording the access
does not change atomic locations or views, so it composes with the actual `locIdx` map. -/
theorem prepare_amap {m m' : Mem} {li : Nat} {k : AccessKind} {hF : Heap} (hw : W.Ok m)
    (hoff : ∀ x, W.o ≤ x → x < W.o + nb → hF (W.b, x) = none)
    (h : ((locIdx W.b W.o nb).run (m.recordAt W.b W.o nb k)).run = some (.ok (li, m'))) :
    m.nextMsg ≤ m'.nextMsg ∧ ∃ σ, AMap hF m m' σ := by
  obtain ⟨blk, hb, _, hsz, _⟩ := hw.blk
  have hs := FStepIn.locIdx (m := m.recordAt W.b W.o nb k) W.sz_pos hoff ⟨blk, hb, hsz⟩ h
  obtain ⟨σ, ha⟩ := hs.atomics
  have hr : AMap hF m (m.recordAt W.b W.o nb k) some := AMap.of_eq rfl rfl
  exact ⟨hs.nextMsg, _, hr.trans ha rfl⟩

/-- Recording an access at the valid word is a native full-state step of every disjoint frame.
Its existing non-constant block discharges the recorded access's constant-write condition. -/
theorem record_fstep {m : Mem} {k : AccessKind} {hF : Heap} (hw : W.Ok m)
    (hc : m.current < m.clocks.size)
    (hoff : ∀ x, W.o ≤ x → x < W.o + nb → hF (W.b, x) = none) :
    FStepIn hF m (m.recordAt W.b W.o nb k) := by
  obtain ⟨blk, hb, _, _, _, hk, _⟩ := hw.blk
  have hnot : ¬ m.IsConst W.b := by
    rintro ⟨blk', hb', hk'⟩
    rw [hb] at hb'
    cases hb'
    exact hk hk'
  exact FStepIn.recordAt_of hc hoff (Array.getElem?_eq_some_iff.mp hb).1 (fun _ => hnot)

/-- Actual preparation composes the native recorded-access and location-index steps. -/
theorem prepare_fstep {m m' : Mem} {li : Nat} {k : AccessKind} {hF : Heap} (hw : W.Ok m)
    (hc : m.current < m.clocks.size)
    (hoff : ∀ x, W.o ≤ x → x < W.o + nb → hF (W.b, x) = none)
    (h : ((locIdx W.b W.o nb).run (m.recordAt W.b W.o nb k)).run = some (.ok (li, m'))) :
    FStepIn hF m m' := by
  obtain ⟨blk, hb, _, hsz, _⟩ := hw.blk
  exact (record_fstep hw hc hoff).trans
    (FStepIn.locIdx (m := m.recordAt W.b W.o nb k) W.sz_pos hoff ⟨blk, hb, hsz⟩ h)

/-- A recorded access to live word bytes preserves every resource outside them. -/
theorem record_rest_of {m : Mem} {k : AccessKind} (hc : m.current < m.clocks.size)
    (hb : W.b < m.blocks.size) (hk : k.isWrite = true → ¬ m.IsConst W.b)
    (hlive : ∀ l, W.In l → m.heap l ≠ none) :
    RestStep W.In m (m.recordAt W.b W.o nb k) := by
  refine RestStep.of_blocks (FStepIn.recordAt_of (hF := fun _ => none)
    hc (fun _ _ _ => rfl) hb hk) rfl ⟨rfl, rfl, rfl⟩ hlive (fun _ _ _ => rfl) id ?_
  intro e he
  simp only [Mem.recordAt, Array.mem_push] at he
  rcases he with he | rfl
  · exact .inl he
  · exact .inr ⟨fun _ h1 h2 => ⟨rfl, h1, h2⟩, hb⟩

/-- The actual recorded access at a valid word preserves its resource rest. -/
theorem record_rest {m : Mem} {k : AccessKind} (hw : W.Ok m)
    (hc : m.current < m.clocks.size) : RestStep W.In m (m.recordAt W.b W.o nb k) := by
  obtain ⟨blk, hb, _, _, _, hk, _⟩ := hw.blk
  refine record_rest_of hc (Array.getElem?_eq_some_iff.mp hb).1 (fun _ => ?_)
    (fun l hl => hw.cellIn hl)
  rintro ⟨blk', hb', hk'⟩
  rw [hb] at hb'; cases hb'
  exact hk hk'

/-- Recording an atomic access preserves validity and history directly. No operation-summary
type occurs in the statement or proof. -/
theorem Ok.record_native {m : Mem} {t : ThreadId} {k : AccessKind} (hw : W.Ok m)
    (hc : m.current = t) (ht : t < m.threads.size) (hcs : m.clocks.size = m.threads.size)
    (hk : k.isAtomic = true) :
    W.Ok (m.recordAt W.b W.o nb k) ∧ W.hist (m.recordAt W.b W.o nb k) = W.hist m := by
  subst hc
  have hct : m.current < m.clocks.size := by rw [hcs]; exact ht
  let mr := m.recordAt W.b W.o nb k
  have hs : FStepIn (fun _ => none) m mr := record_fstep hw hct (fun _ _ _ => rfl)
  have hrt : mr.clocks[m.current]! = VClock.bump (m.clocks[m.current]!) m.current :=
    recordAt_clock hct
  have hcur : curBytes mr W.b W.o nb = curBytes m W.b W.o nb := curBytes_congr rfl _ _ _
  refine ⟨⟨hw.blk, hw.only, fun i l hl => ?_, fun e he hh => ?_, hw.val,
    fun i l hl => (hw.plain i l hl).of_fp fun e he => ?_⟩, hist_congr rfl rfl⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hw.loc i l hl
    exact ⟨h1, h2, h3, by rw [h4, hcur], h5⟩
  · simp only [mr, Mem.recordAt, Array.mem_push] at he
    rcases he with he | rfl
    · rcases hw.wfp e he hh with ⟨ha, hle⟩ | hle
      · exact .inl ⟨ha, LockWord.someLe_mono (m := m) (m' := mr) rfl
          (fun u _ => hs.clock u) hle⟩
      · exact .inr (LockWord.allLe_mono (m := m) (m' := mr) rfl
          (fun u _ => hs.clock u) hle)
    · refine .inl ⟨hk, m.current, ht, ?_⟩
      show VClock.le _ (mr.clocks[m.current]!) = true
      rw [hrt]; exact VClock.le_refl _
  · simp only [mr, Mem.recordAt, Array.mem_push] at he
    rcases he with he | rfl
    · exact .inl he
    · exact .inr (plainHit_atomic hk)

/-- Actual valid-word preparation preserves validity, history and the recorded access without
passing through the old operation summary. -/
theorem Ok.prep_native {m m₁ : Mem} {t li : Nat} {k : AccessKind} (hw : W.Ok m)
    (hc : m.current = t) (ht : t < m.threads.size) (hcs : m.clocks.size = m.threads.size)
    (hk : k.isAtomic = true)
    (h : ((locIdx W.b W.o nb).run (m.recordAt W.b W.o nb k)).run = some (.ok (li, m₁))) :
    ∃ l, W.Loc m₁ li l ∧ W.Ok m₁ ∧ W.hist m₁ = W.hist m ∧ m₁.blocks = m.blocks ∧
      m₁.seen = m.seen ∧ W.Rec m₁ t := by
  subst hc
  let mr := m.recordAt W.b W.o nb k
  have hcur : curBytes mr W.b W.o nb = curBytes m W.b W.o nb := curBytes_congr rfl _ _ _
  obtain ⟨hwr, _⟩ := hw.record_native rfl ht hcs hk
  have hrec : W.Rec mr m.current := rec_recordAt rfl (by rw [hcs]; exact ht)
  cases hf : mr.atomics.findIdx? (fun l => l.block == W.b && l.off == W.o) with
  | some i =>
    have hl := loc_of_find hf
    obtain ⟨hlen, _, _, hlast, _⟩ := hwr.loc i _ hl
    obtain ⟨rfl, rfl⟩ := locIdx_found hf hlen hlast (hwr.plain i _ hl) h
    exact ⟨_, hl, hwr, hist_congr rfl rfl, rfl, rfl, hrec⟩
  | none =>
    obtain ⟨rfl, rfl⟩ := locIdx_new hf (noOverlap_of_only hf hwr.only) h
    have hno : ∀ i l, ¬ W.Loc mr i l := fun i l hl => by rw [hl.1] at hf; cases hf
    let nl : ALoc := firstLoc mr W.b W.o nb
    have hnl : W.Loc { mr with atomics := mr.atomics.push nl, nextMsg := mr.nextMsg + 1 }
        mr.atomics.size nl := by
      refine ⟨?_, by simp⟩
      show (mr.atomics.push nl).findIdx? _ = _
      rw [Array.findIdx?_push, hf]; simp [nl, firstLoc]
    have honly : ∀ i l, W.Loc { mr with atomics := mr.atomics.push nl, nextMsg := mr.nextMsg + 1 }
        i l → i = mr.atomics.size ∧ l = nl := fun i l hl => loc_unique hl hnl
    refine ⟨nl, hnl, ⟨hw.blk, fun l hl hb h1 h2 => ?_, fun i l hl => ?_, hwr.wfp, hwr.val,
      fun i l hl e he hh => by
        obtain ⟨rfl, rfl⟩ := honly i l hl
        simpa [ALoc.lastClock, nl, firstLoc, firstMsg] using
          plainLe_plainClock mr W.b W.o nb e he hh⟩, ?_, rfl, rfl, hrec⟩
    · rcases Array.mem_push.mp hl with hl | rfl
      · exact hw.only l hl hb h1 h2
      · rfl
    · obtain ⟨rfl, rfl⟩ := honly i l hl
      refine ⟨rfl, by simp [nl, firstLoc], fun j hj => by simp [nl, firstLoc] at hj,
        by simp [ALoc.lastBytes, nl, firstLoc, firstMsg, curBytes], fun j hj => ?_⟩
      simp only [nl, firstLoc, List.size_toArray, List.length_cons, List.length_nil] at hj
      obtain rfl : j = 0 := by omega
      obtain ⟨v, hv⟩ := hwr.val
      exact ⟨v, hv⟩
    · have hn : ∀ i l, ¬ W.Loc m i l := fun i l hl => hno i l hl
      show W.hist { mr with atomics := mr.atomics.push nl, nextMsg := mr.nextMsg + 1 } = W.hist m
      rw [hist_loc hnl, hist_none hn, ← hcur]
      simp [nl, firstLoc, firstMsg, ent]

/-- Actual preparation keeps the resource rest. A fresh location is appended only at the
word; a previously existing location and its complete record stay unchanged. -/
theorem prepare_rest {m m₁ : Mem} {li : Nat} {k : AccessKind} (hw : W.Ok m)
    (hc : m.current < m.clocks.size) (hk : k.isAtomic = true)
    (h : ((locIdx W.b W.o nb).run (m.recordAt W.b W.o nb k)).run = some (.ok (li, m₁))) :
    RestStep W.In m m₁ := by
  let mr := m.recordAt W.b W.o nb k
  have hr := record_rest (k := k) hw hc
  cases hf : mr.atomics.findIdx? (fun l => l.block == W.b && l.off == W.o) with
  | some i =>
    have hl := loc_of_find hf
    have hl₀ : W.Loc m i (mr.atomics[i]!) := hl
    obtain ⟨hlen, _, _, hlast, _⟩ := hw.loc i _ hl₀
    have hpl : PlainLe mr W.b W.o nb (mr.atomics[i]!).lastClock :=
      (hw.plain i _ hl₀).of_fp fun e he => by
        simp only [mr, Mem.recordAt, Array.mem_push] at he
        rcases he with he | rfl
        · exact .inl he
        · exact .inr (plainHit_atomic hk)
    obtain ⟨rfl, rfl⟩ := locIdx_found hf hlen hlast hpl h
    exact hr
  | none =>
    have hs := FStepIn.locIdx (m := mr) (hF := fun _ => none) W.sz_pos
      (fun _ _ _ => rfl) (by obtain ⟨blk, hb, _, hsz, _⟩ := hw.blk; exact ⟨blk, hb, hsz⟩) h
    obtain ⟨rfl, rfl⟩ := locIdx_new hf (noOverlap_of_only hf hw.only) h
    refine hr.trans (RestStep.of_blocks hs rfl ⟨rfl, rfl, rfl⟩
      (fun l hl => hw.cellIn hl) (fun b x hx => ?_) (fun hwf => ?_)
      (fun _ he => .inl he))
    · simp only [shapes, Array.toList_push, List.map_append, List.map_cons, List.map_nil,
        firstLoc, ALoc.shape]
      rw [tagOf_append_single]
      have hn : ¬ Covers b x (W.b, W.o, nb) := fun ⟨h1, h2, h3⟩ => hx ⟨h1.symm, h2, h3⟩
      simp [hn]
      rfl
    · simp only [shapes, Array.toList_push, List.map_append, List.map_cons, List.map_nil,
        firstLoc, ALoc.shape]
      refine ⟨fun s hs => ?_, List.pairwise_append.mpr
        ⟨hwf.2, by simp, fun a ha b hb => ?_⟩⟩
      · rcases List.mem_append.mp hs with hs | hs
        · exact hwf.1 s hs
        · simp at hs; subst hs; exact W.sz_pos
      · simp at hb; subst hb
        obtain ⟨l, hlm, rfl⟩ : ∃ l ∈ mr.atomics, ALoc.shape l = a := by
          simpa [shapes] using ha
        intro hlb
        simp only [ALoc.shape] at hlb ⊢
        by_cases h1 : l.off < W.o + nb
        · by_cases h2 : W.o < l.off + l.len
          · have heq := hw.only l hlm hlb h1 h2
            have hn := Array.findIdx?_eq_none_iff.mp hf l hlm
            simp [hlb, heq] at hn
          · exact .inl (by omega)
        · exact .inr (by omega)

/-- Validity and history under unchanged memory-model data and growing clocks. This proves
the word's fields directly rather than constructing a legacy preservation summary. -/
theorem Ok.fields_native {m m' : Mem} (hw : W.Ok m) (hb : m'.blocks = m.blocks)
    (ha : m'.atomics = m.atomics) (hf : m'.footprint = m.footprint)
    (ht : m'.threads = m.threads)
    (hcl : ∀ u : Nat, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true) :
    W.Ok m' ∧ W.hist m' = W.hist m := by
  have hl : ∀ i l, W.Loc m' i l ↔ W.Loc m i l := by
    intro i l; unfold Loc; rw [ha]
  refine ⟨⟨by rw [hb]; exact hw.blk, fun l h hb' h1 h2 =>
    hw.only l (ha ▸ h) hb' h1 h2, fun i l h => ?_, fun e he hh => ?_, ?_,
    fun i l h => ?_⟩, hist_congr ha hb⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hw.loc i l ((hl i l).mp h)
    exact ⟨h1, h2, h3, by rw [h4, curBytes_congr hb], h5⟩
  · rw [hf] at he
    rcases hw.wfp e he hh with ⟨hk, hle⟩ | hle
    · exact .inl ⟨hk, LockWord.someLe_mono ht (fun u _ => hcl u) hle⟩
    · exact .inr (LockWord.allLe_mono ht (fun u _ => hcl u) hle)
  · obtain ⟨v, hv⟩ := hw.val
    refine ⟨v, ?_⟩
    unfold Holds at hv ⊢
    rw [curBytes_congr hb]
    exact hv
  · exact (hw.plain i l ((hl i l).mp h)).of_fp fun e he => .inl (hf ▸ he)

/-- A lock step preserves the validity and exact history of any apart word. The
proof uses its native array effect and frame facts, without a preservation packet. -/
theorem Ok.lockStep {L : LockWord} {t : ThreadId} {m m' : Mem} (hw : W.Ok m)
    (hs : L.Step t m m') (hap : W.ApartL L) : W.Ok m' ∧ W.hist m' = W.hist m := by
  have hnot : ∀ l, W.In l → ¬ L.In l := by
    rintro ⟨b, x⟩ ⟨hb, h1, h2⟩ ⟨hb', h3, h4⟩
    rcases hap with h | h | h
    · exact h (hb'.symm.trans hb)
    · omega
    · omega
  have hcells : ∀ l, W.In l → m'.heap l = m.heap l :=
    fun l hl => hs.heap (hnot l hl)
  obtain ⟨hb', hcur⟩ := Word.congr
    (fun x h1 h2 => congrArg (Option.map cellKey) (hcells (W.b, x) ⟨rfl, h1, h2⟩)) hw.blk
  have hloc : ∀ i l, W.Loc m' i l ↔ W.Loc m i l :=
    fun i l => hs.first_iff W.b W.o (hap.ne.imp Ne.symm Ne.symm) i l
  have hfp : ∀ e ∈ m'.footprint, e ∉ m.footprint → ¬ W.Hits e := by
    intro e he hn ⟨hb, x, h1, h2, h3, h4⟩
    rcases hs.fp e he with hold | ⟨hb', ho, hlen, -⟩
    · exact hn hold
    · rw [hb'] at hb
      rw [ho] at h1
      rw [ho, hlen] at h2
      rcases hap with h | h | h
      · exact h hb
      · omega
      · omega
  have hw' : W.Ok m' := by
    refine ⟨hb', fun l hl hb h1 h2 => ?_, fun i l hl => ?_, fun e he hh => ?_, ?_,
      fun i l hl => ?_⟩
    · rcases hs.atomic_mem hl with hold | hshape
      · exact hw.only l hold hb h1 h2
      · obtain ⟨hbl, ho, hlen⟩ : l.block = L.b ∧ l.off = L.o ∧ l.len = 4 := by
          simpa only [ALoc.shape, LockWord.shape, Prod.mk.injEq] using hshape
        rw [hbl] at hb
        rw [ho] at h1
        rw [ho, hlen] at h2
        rcases hap with h | h | h
        · exact absurd hb h
        · omega
        · omega
    · obtain ⟨h1, h2, h3, h4, h5⟩ := hw.loc i l ((hloc i l).mp hl)
      exact ⟨h1, h2, h3, by rw [h4, hcur], h5⟩
    · by_cases hold : e ∈ m.footprint
      · rcases hw.wfp e hold hh with ⟨hk, hle⟩ | hle
        · exact .inl ⟨hk, hs.someLe hle⟩
        · exact .inr (hs.allLe hle)
      · exact absurd hh (hfp e he hold)
    · obtain ⟨v, hv⟩ := hw.val
      exact ⟨v, by unfold Word.Holds; rw [hcur]; exact hv⟩
    · exact (hw.plain i l ((hloc i l).mp hl)).of_fp fun e he =>
        (hs.fp e he).imp id fun h => plainHit_atomic h.2.2.2.1
  have hoff : L.Off (W.cellsR m).heap.erase := by
    intro x h1 h2
    have hn : ¬ W.In (L.b, x) := by
      rintro ⟨hb, h3, h4⟩
      rcases hap with h | h | h
      · exact h hb
      · omega
      · omega
    simp [FHeap.erase, Word.cellsR, cellsAt_none hn]
  obtain ⟨σ, ha⟩ := hs.atomics (W.cellsR m).heap.erase hoff
  have hw₀ : W.Ok { m with current := t } :=
    (hw.fields_native (m' := { m with current := t }) rfl rfl rfl rfl
      (fun _ => VClock.le_refl _)).1
  have hh := hist_amap (m := { m with current := t }) (m' := { m' with current := t })
    hw₀ ha (fun l hl => by
      have hc := cellsAt_some (W := W.In) hl (hw.cellIn hl) (m := m)
      intro hn
      exact hc (Option.map_eq_none_iff.mp hn))
    (fun l hl => congrArg (Option.map Cell.norm) (hcells l hl))
  exact ⟨hw', hh⟩

/-- A permitted load of an actual message preserves validity and gives the original reader's
floor and acquire facts. The preparation is the existing native relation. -/
theorem Ok.read_native {m m₁ : Mem} {t li pos : Nat} {l : ALoc} {ord : AtomicOrder}
    (hw₁ : W.Ok m₁) (hl : W.Loc m₁ li l) (hc : m.current = t)
    (hs : FStepIn (fun _ => none) m m₁) (hct : t < m₁.clocks.size)
    (hlt : pos < l.msgs.size) (hfl : floorPos m₁ li ≤ pos) :
    Floor (W.hist m₁) (m.clocks[t]!) pos ∧
      (ord.isAcq = true → VClock.le (W.hist m₁)[pos]!.relClock
        ((loadM m₁ li ord (l.msgs[pos]!)).clocks[t]!) = true) ∧
      W.hist (loadM m₁ li ord (l.msgs[pos]!)) = W.hist m₁ ∧
      W.Ok (loadM m₁ li ord (l.msgs[pos]!)) := by
  have hl0 := (loc_get hl).2.2
  have hc₁ : m₁.current = t := hs.current.trans hc
  have hcs₁ : m₁.current < m₁.clocks.size := by rw [hc₁]; exact hct
  have hr := FStepIn.loadM (hF := fun _ => none) hcs₁ ord (l.msgs[pos]!)
    (loc_notIn hl (hw₁.loc li l hl).1 (fun _ _ _ => rfl))
  have hb : (loadM m₁ li ord (l.msgs[pos]!)).blocks = m₁.blocks := by
    unfold loadM; split <;> rfl
  have ha : (loadM m₁ li ord (l.msgs[pos]!)).atomics = m₁.atomics := by
    unfold loadM; split <;> rfl
  have hfp : (loadM m₁ li ord (l.msgs[pos]!)).footprint = m₁.footprint := by
    unfold loadM; split <;> rfl
  obtain ⟨hw', hh⟩ := hw₁.fields_native hb ha hfp hr.threads hr.clock
  refine ⟨fun k hk hle => ?_, fun hq => ?_, hh, hw'⟩
  · by_cases hk0 : k = 0
    · omega
    · rw [hist_size hl] at hk
      rw [hist_get hl hk] at hle
      simp only [ent, hk0, ↓reduceIte] at hle
      have hk' : k < (m₁.atomics[li]!).msgs.size := by rw [hl0]; exact hk
      have he : ((m₁.atomics[li]!).msgs[k]'hk').clock = l.msgs[k].clock := by simp [hl0]
      have : k ≤ floorPos m₁ li := le_floorPos hk'
        (by rw [he, hc₁]; exact VClock.le_trans hle (hs.clock t))
      omega
  · rw [hist_get hl hlt]
    simp only [ent]
    unfold loadM; simp only [hq, ↓reduceIte]
    rw [← hc₁]
    simp only [acqM, observeM]
    rw [Proto.getElem!_set!_ite]
    simp only [true_and, hcs₁, ↓reduceIte]
    rw [← getElem!_pos l.msgs _ hlt]
    exact VClock.le_merge_right _ _

/-- All completed loads expose their actual value, floor, acquire, history and validity facts
without a legacy operation premise or conclusion. -/
theorem Ok.load_native {m m' : Mem} {t c : Nat} {ord : AtomicOrder} {v : BitVec n}
    (hw : W.Ok m) (hc : m.current = t) (ht : t < m.threads.size)
    (hcs : m.clocks.size = m.threads.size)
    (h : ((atomicLoadAt c ord nb W.ptr : MemM (BitVec n)).run m).run = some (.ok (v, m'))) :
    ∃ j, j < (W.hist m).size ∧ (W.hist m)[j]!.Val v ∧ Floor (W.hist m) (m.clocks[t]!) j ∧
      (ord.isAcq = true → VClock.le (W.hist m)[j]!.relClock (m'.clocks[t]!) = true) ∧
      W.hist m' = W.hist m ∧ W.Ok m' := by
  obtain ⟨b, blk, o, li, m₁, pos, hacc, _, hp, hpos, hv, rfl⟩ := atomicLoadAt_ok h
  obtain ⟨blk₀, _, _, _, hacc₀, _⟩ := hw.access
  rw [W.sz_eq, hacc₀] at hacc
  rw [W.sz_eq] at hp
  cases hacc
  obtain ⟨l, hl, hw₁, hh₁, _, _⟩ := hw.prep_native hc ht hcs rfl hp
  have hs := prepare_fstep (hF := fun _ => none) hw (by rw [hc, hcs]; exact ht)
    (fun _ _ _ => rfl) hp
  have hl0 := (loc_get hl).2.2
  have hlt := readOpts_lt hpos
  rw [hl0] at hlt hv
  rw [hl0]
  have hct : t < m₁.clocks.size := by rw [hs.size, hcs]; exact ht
  obtain ⟨hfloor, hacq, hh, hw'⟩ := hw₁.read_native (ord := ord) hl hc hs hct hlt (floor_le hpos)
  exact ⟨pos, by rw [← hh₁, hist_size hl]; exact hlt,
    by rw [← hh₁]; exact val_of hl hlt hv,
    by rw [← hh₁]; exact hfloor, by rw [← hh₁]; exact hacq,
    by rw [hh, hh₁], hw'⟩

/-- The actual load of a selected message only changes the actor's view and clock. -/
theorem loadM_rest {m : Mem} {li : Nat} {l : ALoc}
    (hlive : ∀ l, W.In l → m.heap l ≠ none) (hl : W.Loc m li l) (hlen : l.len = nb)
    (hc : m.current < m.clocks.size) (ord : AtomicOrder) (msg : Msg) :
    RestStep W.In m (loadM m li ord msg) := by
  have hs := FStepIn.loadM (hF := fun _ => none) hc ord msg
    (loc_notIn hl hlen (fun _ _ _ => rfl))
  refine RestStep.of_blocks hs (by unfold loadM; split <;> rfl)
    (by unfold Mem.Aux loadM acqM observeM; split <;> simp)
    hlive (fun _ _ _ => ?_) (fun h => ?_) (fun _ he => ?_)
  · unfold loadM; split <;> rfl
  · unfold loadM; split <;> exact h
  · exact .inl (by unfold loadM at he; split at he <;> exact he)

/-- A native write of exactly the word's bytes preserves the resource rest. All block,
layout and authority obligations are discharged from the actual write equation. -/
theorem write_rest {m m' : Mem} {blk : Block} {bs : Array Byte} {hF : Heap}
    (hs : FStepIn hF m m') (hb : m.blocks[W.b]? = some blk) (hl : blk.live = true)
    (hsize : W.o + nb ≤ blk.bytes.size) (hk : blk.kind ≠ .constGlobal)
    (hlo : blk.kind.mappedLo ≤ W.o) (hbs : bs.size = nb)
    (hblocks : m'.blocks = (m.write W.b blk W.o bs).blocks)
    (hshape : shapes m' = shapes m) (hfp : m'.footprint = m.footprint)
    (ha : m.Aux m') : RestStep W.In m m' := by
  have hn : W.o + bs.size ≤ blk.bytes.size := by omega
  have hset : m'.blocks = m.blocks.set! W.b {blk with bytes := writeBytes blk.bytes W.o bs} :=
    hblocks
  have hheap := heap_of_blocks hblocks
  obtain ⟨hkn, hext, hauth⟩ := kmono_write hb hset hn hk ha hs.current
  refine ⟨hs.threads, hs.size, hs.clock, by rw [hset]; simp, fun l hl' => ?_,
    fun l hl' => ?_, hkn, hext,
    ld_write hb hn hset,
    fun b x _ => by rw [hshape], fun h => by rw [hshape]; exact h,
    fun e he => .inl (hfp ▸ he), ?_, hs.msgCov⟩
  · rw [hheap]
    exact Mem.heap_write_out hb hn l (by simpa only [hbs, In] using hl')
  · rw [hheap, Mem.heap_write hb hl hn hlo l, if_pos (by simpa only [hbs, In] using hl')]
    simp
  · have heq : {m' with current := m.current} = m' := by rw [← hs.current]
    rw [heq]
    exact hauth

/-- Every completed load preserves the full resource rest, for every order and selector. -/
theorem atomicLoad_rest {m m' : Mem} {c : Nat} {ord : AtomicOrder} {v : BitVec n}
    (hw : W.Ok m) (hc : m.current < m.clocks.size)
    (h : ((atomicLoadAt c ord nb W.ptr : MemM (BitVec n)).run m).run = some (.ok (v, m'))) :
    RestStep W.In m m' := by
  obtain ⟨b, blk, o, li, m₁, pos, hacc, _, hp, _, _, rfl⟩ := atomicLoadAt_ok h
  obtain ⟨blk₀, _, _, _, hacc₀, _⟩ := hw.access
  rw [W.sz_eq, hacc₀] at hacc
  rw [W.sz_eq] at hp
  cases hacc
  obtain ⟨l, hl, hlen, _⟩ := prepare hw rfl hp
  have hs := prepare_fstep (hF := fun _ => none) hw hc (fun _ _ _ => rfl) hp
  have hr := prepare_rest hw hc rfl hp
  rw [(loc_get hl).2.2]
  exact hr.trans (loadM_rest hr.live hl hlen (hs.cur hc) ord _)

/-- Native preparation supplies a nonempty message chain and every selected value decoder. -/
theorem Ok.opts_native {m m₁ : Mem} {li : Nat} {k : AccessKind} (hw : W.Ok m)
    (ht : m.current < m.threads.size) (hcs : m.clocks.size = m.threads.size)
    (hk : k.isAtomic = true)
    (hl : ((locIdx W.b W.o (intSize n)).run (m.recordAt W.b W.o (intSize n) k)).run =
      some (.ok (li, m₁))) :
    0 < (m₁.atomics[li]!).msgs.size ∧ (m₁.atomics[li]!).Chain ∧
      ∀ pos < (m₁.atomics[li]!).msgs.size,
        ∃ w, (intOfBytes n ((m₁.atomics[li]!).msgs[pos]!).bytes).run = some (.ok w) := by
  rw [W.sz_eq] at hl
  obtain ⟨l, hl', hw₁, _⟩ := hw.prep_native rfl ht hcs hk hl
  obtain ⟨_, h0, hchain, _, hval⟩ := hw₁.loc li l hl'
  rw [(loc_get hl').2.2]
  exact ⟨h0, hchain, fun pos hp => by
    rw [getElem!_pos l.msgs _ hp]; exact hval pos hp⟩

/-- All admitted load selectors are error-free, using native preparation validity. -/
theorem Ok.load_noErr_native {m : Mem} {c : Nat} {ord : AtomicOrder} (hw : W.Ok m)
    (ht : m.current < m.threads.size) (hcs : m.clocks.size = m.threads.size)
    (hcr : c < loadCount n ord nb W.ptr m ∨ loadCount n ord nb W.ptr m = 0 ∧ c = 0)
    (e : Error) : ((atomicLoadAt (n := n) c ord nb W.ptr).run m).run ≠ some (.error e) := by
  obtain ⟨blk, ha, _, hnr, hloc⟩ := hw.prep_ok ht (k := .atomicRead) rfl
  refine atomicLoadAt_noErr (loadPrep_noErr (by simpa using ha) (by simpa using hnr)
    (by simpa using hloc)) (fun li opts m₁ hp => ?_) e
  obtain ⟨b, blk', o, ha', _, hl, rfl⟩ := loadPrep_ok hp
  simp only [Bool.false_eq_true, ↓reduceIte] at ha' hl
  rw [ha] at ha'; cases ha'
  obtain ⟨h0, _, hval⟩ := hw.opts_native ht hcs rfl hl
  have hne := readOpts_ne (li := li) h0
  have hcnt : loadCount n ord nb W.ptr m = (readOpts m₁ li false).size := by
    unfold loadCount; rw [optCount_eq hp]
  have hc : c < (readOpts m₁ li false).size := by rw [hcnt] at hcr; omega
  exact ⟨_, Array.getElem?_eq_getElem hc,
    hval _ (readOpts_lt (Array.getElem?_eq_getElem hc))⟩

/-- All admitted RMW selectors and signed operations are error-free natively. -/
theorem Ok.rmw_noErr_native {m : Mem} {c : Nat} {op : RmwOp} {signed : Bool}
    {ord : AtomicOrder} {v : BitVec n} (hw : W.Ok m) (ht : m.current < m.threads.size)
    (hcs : m.clocks.size = m.threads.size)
    (hcr : c < rmwCount n ord nb W.ptr m ∨ rmwCount n ord nb W.ptr m = 0 ∧ c = 0)
    (e : Error) : ((atomicRmwAt c op signed ord nb W.ptr v).run m).run ≠ some (.error e) := by
  obtain ⟨blk, _, haw, hnr, hloc⟩ := hw.prep_ok ht (k := .atomicWrite) rfl
  refine atomicRmwAt_noErr (loadPrep_noErr (by simpa using haw) (by simpa using hnr)
    (by simpa using hloc)) (fun li opts m₁ hp => ?_) e
  obtain ⟨b, blk', o, ha', _, hl, rfl⟩ := loadPrep_ok hp
  simp only [↓reduceIte] at ha' hl
  rw [haw] at ha'; cases ha'
  obtain ⟨h0, hchain, hval⟩ := hw.opts_native ht hcs rfl hl
  have hro := readOpts_chain h0 hchain
  have hcnt : rmwCount n ord nb W.ptr m = 1 := by
    unfold rmwCount; rw [optCount_eq hp, hro]; rfl
  have hc0 : c = 0 := by rw [hcnt] at hcr; omega
  subst hc0
  exact ⟨(m₁.atomics[li]!).msgs.size - 1, by rw [hro]; rfl, hval _ (by omega)⟩

/-- All admitted strong-CAS selectors are error-free, including the write marking step. -/
theorem Ok.cas_noErr_native {m : Mem} {c : Nat} {succ fail : AtomicOrder}
    {exp new : BitVec n} (hw : W.Ok m) (ht : m.current < m.threads.size)
    (hcs : m.clocks.size = m.threads.size)
    (hcr : c < casCount n succ nb W.ptr exp m ∨ casCount n succ nb W.ptr exp m = 0 ∧ c = 0)
    (e : Error) : ((cmpxchgAt c succ fail nb W.ptr exp new).run m).run ≠ some (.error e) := by
  obtain ⟨blk, _, haw, hnr, hloc⟩ := hw.prep_ok ht (k := .atomicRead) rfl
  have hprep : ∀ e, ((casPrep n nb W.ptr exp).run m).run ≠ some (.error e) :=
    casPrep_noErr haw hnr hloc
  refine cmpxchgAt_noErr hprep (fun li opts m₁ hp => ?_)
    (fun li opts m₁ hp e he => ?_) e
  · obtain ⟨b, blk', o, ha, _, hl, rfl⟩ := casPrep_ok hp
    rw [haw] at ha; cases ha
    obtain ⟨h0, _, hval⟩ := hw.opts_native ht hcs rfl hl
    have hne := casOpts_ne (e := exp) (m := m₁) (li := li) h0
    have hcnt : casCount n succ nb W.ptr exp m = (casOpts m₁ li exp).size := by
      unfold casCount; rw [optCount_eq hp]
    have hc : c < (casOpts m₁ li exp).size := by rw [hcnt] at hcr; omega
    exact ⟨_, Array.getElem?_eq_getElem hc,
      hval _ (casOpts_pos (Array.getElem?_eq_getElem hc)).1⟩
  · obtain ⟨b, blk', o, ha, _, hl, _⟩ := casPrep_ok hp
    rw [haw] at ha; cases ha
    rw [W.sz_eq] at hl
    obtain ⟨l, hl', hw₁, _⟩ := hw.prep_native rfl ht hcs rfl hl
    have hs := prepare_fstep (hF := fun _ => none) hw (by rw [hcs]; exact ht)
      (fun _ _ _ => rfl) hl
    obtain ⟨blk₁, _, ha₁, hnr₁, _⟩ := hw₁.prep_ok
      (by rw [hs.current, hs.threads]; exact ht) (k := .atomicWrite) rfl
    rw [casMarkWrite_run ha₁ hnr₁] at he
    cases he

/-- Weak-CAS selectors, including all spurious failures, are error-free natively. -/
theorem Ok.weakCas_noErr_native {m : Mem} {c : Nat} {succ fail : AtomicOrder}
    {exp new : BitVec n} (hw : W.Ok m) (ht : m.current < m.threads.size)
    (hcs : m.clocks.size = m.threads.size)
    (hcr : c < weakCasCount n succ nb W.ptr exp m ∨
      weakCasCount n succ nb W.ptr exp m = 0 ∧ c = 0)
    (e : Error) : ((cmpxchgWeakAt c succ fail nb W.ptr exp new).run m).run ≠ some (.error e) := by
  obtain ⟨blk, _, haw, hnr, hloc⟩ := hw.prep_ok ht (k := .atomicRead) rfl
  have hprep : ∀ e, ((weakCasPrep n nb W.ptr exp).run m).run ≠ some (.error e) :=
    weakCasPrep_noErr (casPrep_noErr haw hnr hloc)
  refine cmpxchgWeakAt_noErr hprep (fun li opts m₁ hp => ?_)
    (fun li opts m₁ hp e he => ?_) e
  · obtain ⟨b, blk', o, ha, _, hl, rfl⟩ := weakCasPrep_ok hp
    rw [haw] at ha; cases ha
    obtain ⟨h0, _, hval⟩ := hw.opts_native ht hcs rfl hl
    have hne := casOpts_ne (e := exp) (m := m₁) (li := li) h0
    have hcnt := weakOptCount_eq (succ := succ) hp
    have hsz : 0 < (weakCasOpts m₁ li exp (casOpts m₁ li exp)).size := by
      simp only [weakCasOpts_eq, Array.size_append, Array.size_map]
      omega
    have hc : c < (weakCasOpts m₁ li exp (casOpts m₁ li exp)).size := by rw [hcnt] at hcr; omega
    let choice := (weakCasOpts m₁ li exp (casOpts m₁ li exp))[c]
    have hchoice : (weakCasOpts m₁ li exp (casOpts m₁ li exp))[c]? = some choice :=
      Array.getElem?_eq_getElem hc
    obtain ⟨j, hread⟩ := weakCasOpts_read hchoice
    exact ⟨choice.1, choice.2, hchoice, hval _ (readOpts_lt hread)⟩
  · obtain ⟨b, blk', o, ha, _, hl, _⟩ := weakCasPrep_ok hp
    rw [haw] at ha; cases ha
    rw [W.sz_eq] at hl
    obtain ⟨l, hl', hw₁, _⟩ := hw.prep_native rfl ht hcs rfl hl
    have hs := prepare_fstep (hF := fun _ => none) hw (by rw [hcs]; exact ht)
      (fun _ _ _ => rfl) hl
    obtain ⟨blk₁, _, ha₁, hnr₁, _⟩ := hw₁.prep_ok
      (by rw [hs.current, hs.threads]; exact ht) (k := .atomicWrite) rfl
    rw [casMarkWrite_run ha₁ hnr₁] at he
    cases he

/-- A completed load is a native full-state step of every disjoint frame, at every order.
Its actual preparation and read supply the whole relation, not only its map projection. -/
theorem atomicLoad_fstep {m m' : Mem} {c : Nat} {ord : AtomicOrder} {v : BitVec n} {hF : Heap}
    (hw : W.Ok m) (hc : m.current < m.clocks.size)
    (hoff : ∀ x, W.o ≤ x → x < W.o + nb → hF (W.b, x) = none)
    (h : ((atomicLoadAt c ord nb W.ptr).run m).run = some (.ok (v, m'))) :
    FStepIn hF m m' := by
  obtain ⟨b, blk, o, li, m₁, pos, hacc, _, hp, _, _, rfl⟩ := atomicLoadAt_ok h
  obtain ⟨blk₀, _, _, _, ha, _⟩ := hw.access
  rw [W.sz_eq, ha] at hacc
  rw [W.sz_eq] at hp
  cases hacc
  obtain ⟨l, hl, hlen, _, _, _, _, _, _⟩ := prepare hw rfl hp
  have hs := prepare_fstep hw hc hoff hp
  have hcs := hs.cur hc
  exact hs.trans
    (FStepIn.loadM hcs ord ((m₁.atomics[li]!).msgs[pos]!) (loc_notIn hl hlen hoff))

/-- A completed load carries the frame's atomic locations and views. This is obtained from
its actual preparation and read, for every memory order, without an `Op` transport premise. -/
theorem atomicLoad_amap {m m' : Mem} {c : Nat} {ord : AtomicOrder} {v : BitVec n} {hF : Heap}
    (hw : W.Ok m) (hc : m.current < m.clocks.size)
    (hoff : ∀ x, W.o ≤ x → x < W.o + nb → hF (W.b, x) = none)
    (h : ((atomicLoadAt c ord nb W.ptr).run m).run = some (.ok (v, m'))) :
    m.nextMsg ≤ m'.nextMsg ∧ ∃ σ, AMap hF m m' σ := by
  have hs := atomicLoad_fstep hw hc hoff h
  exact ⟨hs.nextMsg, hs.atomics⟩

/-- The recorded access remains at the current clock after actual preparation. -/
theorem prepare_rec {m m' : Mem} {li : Nat} {k : AccessKind}
    (hc : m.current < m.clocks.size)
    (h : ((locIdx W.b W.o nb).run (m.recordAt W.b W.o nb k)).run = some (.ok (li, m'))) :
    W.Rec m' m'.current ∧ m'.current < m'.clocks.size ∧ m'.blocks = m.blocks := by
  obtain ⟨a, sn, next, rfl⟩ := locIdx_updates h
  exact ⟨rec_recordAt rfl hc, by simpa [Mem.recordAt] using hc, rfl⟩

/-- The actual newest-message RMW is a native full-state step of a disjoint frame. -/
theorem rmwM_fstep {m : Mem} {li pos : Nat} {l : ALoc} {hF : Heap}
    (hl : W.Loc m li l) (hlen : l.len = nb) (hpos : pos + 1 = l.msgs.size)
    (hc : m.current < m.clocks.size) (hrec : W.Rec m m.current)
    (hb : ∃ blk, m.blocks[W.b]? = some blk)
    (hoff : ∀ x, W.o ≤ x → x < W.o + nb → hF (W.b, x) = none)
    (ord : AtomicOrder) (new : BitVec n) :
    FStepIn hF m (rmwM m li pos ord ((m.atomics[li]!).msgs[pos]!) new) := by
  obtain ⟨blk, hb⟩ := hb
  obtain ⟨e, he, heb, heo, hel, hec⟩ := hrec
  obtain ⟨hlb, hlo⟩ := loc_at hl
  have hl0 := (loc_get hl).2.2
  exact FStepIn.rmwM (hF := hF) (li := li) (pos := pos) (blk := blk) (e := e)
    ord ((m.atomics[li]!).msgs[pos]!) new hc
    (by rw [hl0]; exact hpos) (by rw [hl0, hlb]; exact hb) (loc_notIn hl hlen hoff)
    he (by rw [hl0, hlb]; exact heb) (by rw [hl0, hlo]; exact heo) hel hec
    (by rw [hl0, getElem!_pos l.msgs pos (by omega)]; exact Array.getElem_mem _)

/-- The actual newest-message RMW preserves the full resource rest. Its block write and
location replacement are obtained from `insertM_last`, at every width and order. -/
theorem rmwM_rest {m : Mem} {li pos : Nat} {l : ALoc} {blk : Block}
    (hl : W.Loc m li l) (hlen : l.len = nb) (hpos : pos + 1 = l.msgs.size)
    (hc : m.current < m.clocks.size) (hrec : W.Rec m m.current)
    (hb : m.blocks[W.b]? = some blk) (hlive : blk.live = true)
    (hsize : W.o + nb ≤ blk.bytes.size) (hk : blk.kind ≠ .constGlobal)
    (hlo : blk.kind.mappedLo ≤ W.o) (ord : AtomicOrder) (new : BitVec n) :
    RestStep W.In m (rmwM m li pos ord ((m.atomics[li]!).msgs[pos]!) new) := by
  have hl0 := (loc_get hl).2.2
  obtain ⟨hlb, hlo'⟩ := loc_at hl
  let rd := (m.atomics[li]!).msgs[pos]!
  let m₂ := if ord.isAcq then acqM m rd.relClock else m
  let msg := rmwMsg m₂ ord rd new
  let M := rmwM m li pos ord rd new
  have h2 : m₂.atomics = m.atomics ∧ m₂.blocks = m.blocks ∧
      m₂.footprint = m.footprint ∧ m.Aux m₂ := by
    simp only [m₂]; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨ha₂, hb₂, hf₂, hx₂⟩ := h2
  have hMe : M = observeM {m₂ with
      atomics := m₂.atomics.set! li {l with msgs := l.msgs.push msg}, nextMsg := m₂.nextMsg + 1,
      blocks := m₂.blocks.set! l.block {blk with bytes := writeBytes blk.bytes l.off msg.bytes}}
      li m₂.nextMsg := by
    exact rmwM_last_eq hl0 hpos (by rw [hlb]; exact hb) ord rd new
  have hMa : M.atomics = m.atomics.set! li {l with msgs := l.msgs.push msg} := by
    rw [hMe]; simp only [observeM, ha₂]
  have hMb : M.blocks = (m.write W.b blk W.o msg.bytes).blocks := by
    rw [hMe]; simp only [observeM, Mem.write, hb₂, hlb, hlo']
  have hMf : M.footprint = m.footprint := by rw [hMe]; exact hf₂
  have hMx : m.Aux M := by rw [hMe]; exact hx₂.trans ⟨rfl, rfl, rfl⟩
  have hsh : shapes M = shapes m := by
    rw [← keys_toList, keys_set (l' := {l with msgs := l.msgs.push msg}) hl.2 rfl hMa, keys_toList]
  exact write_rest (rmwM_fstep hl hlen hpos hc hrec ⟨blk, hb⟩
    (hF := fun _ => none) (fun _ _ _ => rfl) ord new)
    hb hlive hsize hk hlo (W.enc_size new) hMb hsh hMf hMx

/-- The location `i` with another location of the same place. -/
theorem loc_set {m : Mem} {i : Nat} {l l' : ALoc} (hl : W.Loc m i l) (hb : l'.block = l.block)
    (ho : l'.off = l.off) :
    (m.atomics.set! i l').findIdx? (fun l => l.block == W.b && l.off == W.o) = some i ∧
      (m.atomics.set! i l')[i]? = some l' := by
  obtain ⟨hi, -, -⟩ := loc_get hl
  refine ⟨(Conc.findIdx?_set_address hl.2 hb ho W.b W.o).trans hl.1, ?_⟩
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]; simp [hi]

/-- A newest-message RMW preserves validity and appends its actual result entry. The proof
uses the primitive's updates and native clock transport, without an operation summary. -/
theorem Ok.rmwAt_native {m₁ M : Mem} {t li : Nat} {l : ALoc} {ord : AtomicOrder} {new : BitVec n}
    (hw : W.Ok m₁) (hl : W.Loc m₁ li l) (hc : m₁.current = t) (ht : t < m₁.threads.size)
    (hcs : m₁.clocks.size = m₁.threads.size) (hrec : W.Rec m₁ t)
    (hM : M = rmwM m₁ li (l.msgs.size - 1) ord (l.msgs[l.msgs.size - 1]!) new) :
    W.Ok M ∧ W.Holds M new ∧
      W.hist M = (W.hist m₁).push (rmwEnt M t ord (W.hist m₁)[(W.hist m₁).size - 1]! new) ∧
      (ord.isAcq = true →
        VClock.le (W.hist m₁)[(W.hist m₁).size - 1]!.relClock (M.clocks[t]!) = true) := by
  subst hc
  obtain ⟨hlen, h0, hch, _, hval⟩ := hw.loc li l hl
  obtain ⟨hlb, hlo⟩ := loc_at hl
  obtain ⟨hli, _, hl0⟩ := loc_get hl
  obtain ⟨blk, hb, hlv, hsz, ha4, hk⟩ := hw.blk
  have hct : m₁.current < m₁.clocks.size := by rw [hcs]; exact ht
  have hs : FStepIn (fun _ => none) m₁ M := by
    rw [hM]
    simpa only [hl0] using
      (rmwM_fstep (pos := l.msgs.size - 1) hl hlen (by omega) hct hrec
        ⟨blk, hb⟩ (fun _ _ _ => rfl) ord new)
  let rd := l.msgs[l.msgs.size - 1]!
  let m₂ := if ord.isAcq then acqM m₁ rd.relClock else m₁
  have h2 : m₂.atomics = m₁.atomics ∧ m₂.blocks = m₁.blocks ∧
      m₂.footprint = m₁.footprint ∧ m₂.current = m₁.current := by
    simp only [m₂]; split <;> simp [acqM]
  obtain ⟨ha₂, hb₂, hf₂, hc₂⟩ := h2
  have hl₂ : m₂.atomics[li]! = l := by rw [ha₂]; exact hl0
  have hblk₂ : m₂.blocks[(m₂.atomics[li]!).block]? = some blk := by
    rw [hl₂, hlb, hb₂]; exact hb
  have hins := insertM_last (msg := rmwMsg m₂ ord rd new) hblk₂
  rw [hl₂] at hins
  have hp : l.msgs.size - 1 + 1 = l.msgs.size := by omega
  have hMe : M = observeM { m₂ with
      atomics := m₂.atomics.set! li { l with msgs := l.msgs.push (rmwMsg m₂ ord rd new) },
      nextMsg := m₂.nextMsg + 1,
      blocks := m₂.blocks.set! l.block
        { blk with bytes := writeBytes blk.bytes l.off (rmwMsg m₂ ord rd new).bytes } }
      li m₂.nextMsg := by
    rw [hM]; unfold rmwM; simp only; rw [hp, hins]
  have hMc : M.clocks = m₂.clocks := by rw [hMe]; rfl
  have hMa : M.atomics = m₁.atomics.set! li
      { l with msgs := l.msgs.push (rmwMsg m₂ ord rd new) } := by
    rw [hMe]; simp only [observeM, ha₂]
  have hMb : M.blocks[W.b]? = some
      { blk with bytes := writeBytes blk.bytes W.o (padTo (intSize n) (intBytes new)) } := by
    rw [hMe]; simp only [observeM, hb₂, hlb, hlo, rmwMsg]
    rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt
      (Array.getElem?_eq_some_iff.mp hb).1]
  have hbs : (padTo (intSize n) (intBytes new)).size = nb := W.enc_size new
  have hcur : curBytes M W.b W.o nb = padTo (intSize n) (intBytes new) := by
    unfold curBytes; rw [hMb]
    simp only [Option.map_some, Option.getD_some]
    have := extract_writeBytes blk.bytes W.o (padTo (intSize n) (intBytes new)) (by omega)
    rwa [hbs] at this
  have hholds : W.Holds M new := by
    unfold Word.Holds; rw [hcur]; exact W.enc_val new
  let l' : ALoc := { l with msgs := l.msgs.push (rmwMsg m₂ ord rd new) }
  have hl' : W.Loc M li l' := by
    unfold Loc
    rw [hMa]
    exact loc_set hl rfl rfl
  have hmr : (rmwMsg m₂ ord rd new).rmwOf = some (l.msgs[l.msgs.size - 1]!).id := rfl
  have hsz' : W.o + nb ≤
      (writeBytes blk.bytes W.o (padTo (intSize n) (intBytes new))).size := by
    rw [writeBytes_size _ _ _ (by omega)]; exact hsz
  have hMf : M.footprint = m₁.footprint := by rw [hMe]; exact hf₂
  refine ⟨⟨⟨_, hMb, hlv, hsz', ha4, hk⟩,
    fun l₀ hl₀ hb' h1 h2 => ?_, fun i l₀ hl₀ => ?_, fun e he hh => ?_,
    ⟨new, hholds⟩, fun i l₀ hl₀ => ?_⟩, hholds, ?_, fun hq => ?_⟩
  · rw [hMa, Array.set!_eq_setIfInBounds] at hl₀
    rcases Array.mem_or_eq_of_mem_set (w := hli)
      (by simpa [Array.setIfInBounds, hli] using hl₀) with h | rfl
    · exact hw.only l₀ h hb' h1 h2
    · exact hlo
  · obtain ⟨rfl, rfl⟩ := loc_unique hl₀ hl'
    refine ⟨hlen, by simp [l'], hch.push h0 hmr, ?_, fun j hj => ?_⟩
    · unfold ALoc.lastBytes; simp [l', hcur, rmwMsg]
    · simp only [l', Array.size_push] at hj
      simp only [l', Array.getElem_push]
      split
      · exact hval j (by assumption)
      · exact ⟨new, W.enc_val new⟩
  · have he' : e ∈ m₁.footprint := hMf ▸ he
    rcases hw.wfp e he' hh with ⟨ha', hle⟩ | hle
    · exact .inl ⟨ha', LockWord.someLe_mono hs.threads (fun u _ => hs.clock u) hle⟩
    · exact .inr (LockWord.allLe_mono hs.threads (fun u _ => hs.clock u) hle)
  · obtain ⟨rfl, rfl⟩ := loc_unique hl₀ hl'
    intro e he hh
    have he' : e ∈ m₁.footprint := hMf ▸ he
    have hlc : l'.lastClock = m₂.clocks[m₁.current]! := by
      simp [l', ALoc.lastClock, rmwMsg, hc₂]
    rw [hlc]
    rcases hw.wfp e he' (hits_of_plain hh) with ⟨ha', _⟩ | hle
    · rw [plainHit_atomic ha'] at hh; cases hh
    · have hle' := hs.clock m₁.current
      rw [hMc] at hle'
      exact VClock.le_trans (hle _ ht) hle'
  · rw [hist_loc hl', hist_loc hl, Array.mapIdx_push]
    congr 1
    have hk : (l.msgs.mapIdx ent).size - 1 = l.msgs.size - 1 := by simp
    have hrd : rd = l.msgs[l.msgs.size - 1] := getElem!_pos l.msgs _ (by omega)
    rw [hk, getElem!_pos _ _ (by simp; omega), Array.getElem_mapIdx]
    simp only [ent, rmwEnt, rmwMsg, hMc, hc₂, if_neg (by omega : l.msgs.size ≠ 0), ← hrd]
  · have : ord.isAcq = true := hq
    have hk : (l.msgs.mapIdx ent).size - 1 = l.msgs.size - 1 := by simp
    rw [hist_loc hl, hk, getElem!_pos _ _ (by simp; omega)]
    simp only [Array.getElem_mapIdx, ent]
    rw [hMc]; simp only [m₂, this, ↓reduceIte]
    rw [acqM_clock _ _ hct, ← getElem!_pos l.msgs _ (by omega)]
    exact VClock.le_merge_right _ _

/-- A completed RMW reads the newest value and appends the actual signed/unsigned result. -/
theorem Ok.rmw_native {m m' : Mem} {t c : Nat} {op : RmwOp} {signed : Bool} {ord : AtomicOrder}
    {v old : BitVec n} (hw : W.Ok m) (hc : m.current = t) (ht : t < m.threads.size)
    (hcs : m.clocks.size = m.threads.size)
    (h : ((atomicRmwAt c op signed ord nb W.ptr v).run m).run = some (.ok (old, m'))) :
    (W.hist m)[(W.hist m).size - 1]!.Val old ∧ W.Ok m' ∧
      W.Holds m' (op.apply signed old v) ∧
      W.hist m' = (W.hist m).push
        (rmwEnt m' t ord (W.hist m)[(W.hist m).size - 1]! (op.apply signed old v)) ∧
      (ord.isAcq = true →
        VClock.le (W.hist m)[(W.hist m).size - 1]!.relClock (m'.clocks[t]!) = true) := by
  obtain ⟨b, blk, o, li, m₁, pos, hacc, _, hp, hpos, hold, hm'⟩ := atomicRmwAt_ok h
  obtain ⟨blk₀, _, _, _, _, ha₀⟩ := hw.access
  rw [W.sz_eq, ha₀] at hacc
  rw [W.sz_eq] at hp
  cases hacc
  obtain ⟨l, hl, hw₁, hh₁, _, _, hrec⟩ := hw.prep_native hc ht hcs rfl hp
  have hs := prepare_fstep (hF := fun _ => none) hw (by rw [hc, hcs]; exact ht)
    (fun _ _ _ => rfl) hp
  obtain ⟨_, h0, hch, _, _⟩ := hw₁.loc li l hl
  have hl0 := (loc_get hl).2.2
  have hpl := rmw_chain_pos (m := m₁) (li := li)
    (by rw [hl0]; exact h0) (by rw [hl0]; exact hch) hpos
  rw [hl0] at hpl hold hm'
  rw [hpl] at hold hm'
  obtain ⟨hw', hU, hh, hacq⟩ := hw₁.rmwAt_native hl (hs.current.trans hc)
    (by rw [hs.threads]; exact ht) (by rw [hs.size, hs.threads]; exact hcs) hrec hm'
  have hsz := hist_size hl
  refine ⟨?_, hw', hU, by rw [hh, hh₁], by rw [← hh₁]; exact hacq⟩
  rw [← hh₁, hsz]; exact val_of hl (by omega) hold

/-- Strong CAS has the original newest-write success and mismatching-read failure facts. -/
theorem Ok.cas_native {m m' : Mem} {t c : Nat} {succ fail : AtomicOrder} {exp new : BitVec n}
    {r : Option (BitVec n)} (hw : W.Ok m) (hc : m.current = t) (ht : t < m.threads.size)
    (hcs : m.clocks.size = m.threads.size)
    (h : ((cmpxchgAt c succ fail nb W.ptr exp new).run m).run = some (.ok (r, m'))) :
    W.Ok m' ∧
    ((r = none ∧ (W.hist m)[(W.hist m).size - 1]!.Val exp ∧ W.Holds m' new ∧
      W.hist m' = (W.hist m).push (rmwEnt m' t succ (W.hist m)[(W.hist m).size - 1]! new) ∧
      (succ.isAcq = true →
        VClock.le (W.hist m)[(W.hist m).size - 1]!.relClock (m'.clocks[t]!) = true)) ∨
     (∃ j old, r = some old ∧ old ≠ exp ∧ j < (W.hist m).size ∧ (W.hist m)[j]!.Val old ∧
      Floor (W.hist m) (m.clocks[t]!) j ∧
      (fail.isAcq = true → VClock.le (W.hist m)[j]!.relClock (m'.clocks[t]!) = true) ∧
      W.hist m' = W.hist m)) := by
  obtain ⟨b, blk, o, li, m₁, pos, old, hacc, _, hp, hpos, hold, hcase⟩ := cmpxchgAt_ok h
  obtain ⟨blk₀, _, _, _, _, ha₀⟩ := hw.access
  rw [W.sz_eq, ha₀] at hacc
  rw [W.sz_eq] at hp
  cases hacc
  obtain ⟨l, hl, hw₁, hh₁, _, _, _⟩ := hw.prep_native hc ht hcs rfl hp
  have hs := prepare_fstep (hF := fun _ => none) hw (by rw [hc, hcs]; exact ht)
    (fun _ _ _ => rfl) hp
  have hc₁ : m₁.current = t := hs.current.trans hc
  have ht₁ : t < m₁.threads.size := by rw [hs.threads]; exact ht
  have hcs₁ : m₁.clocks.size = m₁.threads.size := by rw [hs.size, hs.threads]; exact hcs
  have hct : t < m₁.clocks.size := by rw [hs.size, hcs]; exact ht
  obtain ⟨_, h0, hch, _, _⟩ := hw₁.loc li l hl
  have hl0 := (loc_get hl).2.2
  have hsz := hist_size hl
  rcases hcase with ⟨rfl, rfl, _, hm'⟩ | ⟨hne, rfl, hm'⟩
  · have hpl := cas_chain_pos (m := m₁) (li := li) (by rw [hl0]; exact hch) hpos hold
    rw [hl0] at hpl hold hm'
    rw [hpl] at hold hm'
    rw [W.sz_eq] at hm'
    obtain ⟨hw₂, hh₂⟩ := hw₁.record_native hc₁ ht₁ hcs₁ (k := .atomicWrite) rfl
    have hl₂ : W.Loc (m₁.recordAt W.b W.o nb .atomicWrite) li l := hl
    obtain ⟨hw', hU, hh, hacq⟩ := hw₂.rmwAt_native (M := m') (ord := succ) (new := new)
      hl₂ hc₁ ht₁ (by simpa [Mem.recordAt] using hcs₁) (rec_recordAt hc₁ hct) hm'
    refine ⟨hw', .inl ⟨rfl, ?_, hU,
      by rw [hh, hh₂, hh₁], by rw [← hh₁]; exact hacq⟩⟩
    rw [← hh₁, hsz]; exact val_of hl (by omega) hold
  · have hlt := (casOpts_pos hpos).1
    have hfl := casOpts_floor hpos
    rw [hl0] at hlt hold hm'
    rw [hm']
    obtain ⟨hfl', hacq, hh, hw'⟩ := hw₁.read_native (ord := fail) hl hc hs hct hlt hfl
    refine ⟨hw', .inr ⟨pos, old, rfl, hne, by rw [← hh₁, hsz]; exact hlt,
      by rw [← hh₁]; exact val_of hl hlt hold, by rw [← hh₁]; exact hfl',
      by rw [← hh₁]; exact hacq, by rw [hh, hh₁]⟩⟩

/-- Weak CAS retains both successful newest writes and failures that may read the expected
value. The latter includes the matching-value spurious branch. -/
theorem Ok.weakCas_native {m m' : Mem} {t c : Nat} {succ fail : AtomicOrder} {exp new : BitVec n}
    {r : Option (BitVec n)} (hw : W.Ok m) (hc : m.current = t) (ht : t < m.threads.size)
    (hcs : m.clocks.size = m.threads.size)
    (h : ((cmpxchgWeakAt c succ fail nb W.ptr exp new).run m).run = some (.ok (r, m'))) :
    W.Ok m' ∧
    ((r = none ∧ (W.hist m)[(W.hist m).size - 1]!.Val exp ∧ W.Holds m' new ∧
      W.hist m' = (W.hist m).push (rmwEnt m' t succ (W.hist m)[(W.hist m).size - 1]! new) ∧
      (succ.isAcq = true →
        VClock.le (W.hist m)[(W.hist m).size - 1]!.relClock (m'.clocks[t]!) = true)) ∨
     (∃ j old, r = some old ∧ j < (W.hist m).size ∧ (W.hist m)[j]!.Val old ∧
      Floor (W.hist m) (m.clocks[t]!) j ∧
      (fail.isAcq = true → VClock.le (W.hist m)[j]!.relClock (m'.clocks[t]!) = true) ∧
      W.hist m' = W.hist m)) := by
  obtain ⟨b, blk, o, li, m₁, pos, spurious, old, hacc, _, hp, hpos, hold, hcase⟩ := cmpxchgWeakAt_ok h
  obtain ⟨blk₀, _, _, _, _, ha₀⟩ := hw.access
  rw [W.sz_eq, ha₀] at hacc
  rw [W.sz_eq] at hp
  cases hacc
  obtain ⟨l, hl, hw₁, hh₁, _, _, _⟩ := hw.prep_native hc ht hcs rfl hp
  have hs := prepare_fstep (hF := fun _ => none) hw (by rw [hc, hcs]; exact ht)
    (fun _ _ _ => rfl) hp
  have hc₁ : m₁.current = t := hs.current.trans hc
  have ht₁ : t < m₁.threads.size := by rw [hs.threads]; exact ht
  have hcs₁ : m₁.clocks.size = m₁.threads.size := by rw [hs.size, hs.threads]; exact hcs
  have hct : t < m₁.clocks.size := by rw [hs.size, hcs]; exact ht
  obtain ⟨_, h0, hch, _, _⟩ := hw₁.loc li l hl
  have hl0 := (loc_get hl).2.2
  have hsz := hist_size hl
  rcases hcase with ⟨rfl, hsp, rfl, _, hm'⟩ | ⟨_, rfl, hm'⟩
  · obtain ⟨j, hstrong⟩ := weakCasOpts_strong (by simpa [hsp] using hpos)
    have hpl := cas_chain_pos (m := m₁) (li := li) (by rw [hl0]; exact hch) hstrong hold
    rw [hl0] at hpl hold hm'
    rw [hpl] at hold hm'
    rw [W.sz_eq] at hm'
    obtain ⟨hw₂, hh₂⟩ := hw₁.record_native hc₁ ht₁ hcs₁ (k := .atomicWrite) rfl
    have hl₂ : W.Loc (m₁.recordAt W.b W.o nb .atomicWrite) li l := hl
    obtain ⟨hw', hU, hh, hacq⟩ := hw₂.rmwAt_native (M := m') (ord := succ) (new := new)
      hl₂ hc₁ ht₁ (by simpa [Mem.recordAt] using hcs₁) (rec_recordAt hc₁ hct) hm'
    refine ⟨hw', .inl ⟨rfl, ?_, hU,
      by rw [hh, hh₂, hh₁], by rw [← hh₁]; exact hacq⟩⟩
    rw [← hh₁, hsz]; exact val_of hl (by omega) hold
  · obtain ⟨j, hread⟩ := weakCasOpts_read hpos
    have hlt := readOpts_lt hread
    have hfl := floor_le hread
    rw [hl0] at hlt hold hm'
    rw [hm']
    obtain ⟨hfl', hacq, hh, hw'⟩ := hw₁.read_native (ord := fail) hl hc hs hct hlt hfl
    refine ⟨hw', .inr ⟨pos, old, rfl, by rw [← hh₁, hsz]; exact hlt,
      by rw [← hh₁]; exact val_of hl hlt hold, by rw [← hh₁]; exact hfl',
      by rw [← hh₁]; exact hacq, by rw [hh, hh₁]⟩⟩

/-- The actual newest-message RMW preserves a disjoint frame's atomic locations and views. -/
theorem rmwM_amap {m : Mem} {li pos : Nat} {l : ALoc} {hF : Heap}
    (hl : W.Loc m li l) (hlen : l.len = nb) (hpos : pos + 1 = l.msgs.size)
    (hc : m.current < m.clocks.size) (hrec : W.Rec m m.current)
    (hb : ∃ blk, m.blocks[W.b]? = some blk)
    (hoff : ∀ x, W.o ≤ x → x < W.o + nb → hF (W.b, x) = none)
    (ord : AtomicOrder) (new : BitVec n) :
    m.nextMsg ≤ (rmwM m li pos ord ((m.atomics[li]!).msgs[pos]!) new).nextMsg ∧
      ∃ σ, AMap hF m (rmwM m li pos ord ((m.atomics[li]!).msgs[pos]!) new) σ := by
  have hs := rmwM_fstep hl hlen hpos hc hrec hb hoff ord new
  exact ⟨hs.nextMsg, hs.atomics⟩

/-- Every completed RMW operation and signedness is a native full-state step, using actual
preparation and the newest-message write. -/
theorem atomicRmw_fstep {m m' : Mem} {c : Nat} {op : RmwOp} {signed : Bool} {ord : AtomicOrder}
    {v old : BitVec n} {hF : Heap} (hw : W.Ok m) (hc : m.current < m.clocks.size)
    (hoff : ∀ x, W.o ≤ x → x < W.o + nb → hF (W.b, x) = none)
    (h : ((atomicRmwAt c op signed ord nb W.ptr v).run m).run = some (.ok (old, m'))) :
    FStepIn hF m m' := by
  obtain ⟨b, blk, o, li, m₁, pos, hacc, _, hp, hr, _, rfl⟩ := atomicRmwAt_ok h
  obtain ⟨blk₀, hb, _, _, _, ha⟩ := hw.access
  rw [W.sz_eq, ha] at hacc
  rw [W.sz_eq] at hp
  cases hacc
  obtain ⟨l, hl, hlen, h0, hch, _, _, _, _⟩ := prepare hw rfl hp
  obtain ⟨hrec, hcs, hblocks⟩ := prepare_rec hc hp
  have hpos : pos + 1 = l.msgs.size := by
    have := rmw_chain_pos (by rwa [(loc_get hl).2.2]) (by rwa [(loc_get hl).2.2]) hr
    rw [(loc_get hl).2.2] at this
    omega
  exact (prepare_fstep hw hc hoff hp).trans
    (rmwM_fstep hl hlen hpos hcs hrec
      ⟨_, by rw [hblocks]; exact hb⟩ hoff ord (op.apply signed old v))

/-- Every completed signed or unsigned RMW preserves the resource rest. -/
theorem atomicRmw_rest {m m' : Mem} {c : Nat} {op : RmwOp} {signed : Bool} {ord : AtomicOrder}
    {v old : BitVec n} (hw : W.Ok m) (hc : m.current < m.clocks.size)
    (h : ((atomicRmwAt c op signed ord nb W.ptr v).run m).run = some (.ok (old, m'))) :
    RestStep W.In m m' := by
  obtain ⟨b, blk, o, li, m₁, pos, hacc, _, hp, hr, _, rfl⟩ := atomicRmwAt_ok h
  obtain ⟨blk₀, _, _, _, _, ha⟩ := hw.access
  rw [W.sz_eq, ha] at hacc
  rw [W.sz_eq] at hp
  cases hacc
  obtain ⟨blk₁, hb, hlive, hsize, _, hk, hlo⟩ := hw.blk
  obtain ⟨l, hl, hlen, h0, hch, _⟩ := prepare hw rfl hp
  obtain ⟨hrec, hcs, hblocks⟩ := prepare_rec hc hp
  have hpos : pos + 1 = l.msgs.size := by
    have := rmw_chain_pos (by rwa [(loc_get hl).2.2]) (by rwa [(loc_get hl).2.2]) hr
    rw [(loc_get hl).2.2] at this
    omega
  exact (prepare_rest hw hc rfl hp).trans
    (rmwM_rest hl hlen hpos hcs hrec (by rw [hblocks]; exact hb)
      hlive hsize hk hlo ord (op.apply signed old v))

/-- Every completed RMW operation uses actual preparation and the actual newest-message write. -/
theorem atomicRmw_amap {m m' : Mem} {c : Nat} {op : RmwOp} {signed : Bool} {ord : AtomicOrder}
    {v old : BitVec n} {hF : Heap} (hw : W.Ok m) (hc : m.current < m.clocks.size)
    (hoff : ∀ x, W.o ≤ x → x < W.o + nb → hF (W.b, x) = none)
    (h : ((atomicRmwAt c op signed ord nb W.ptr v).run m).run = some (.ok (old, m'))) :
    m.nextMsg ≤ m'.nextMsg ∧ ∃ σ, AMap hF m m' σ := by
  have hs := atomicRmw_fstep hw hc hoff h
  exact ⟨hs.nextMsg, hs.atomics⟩

/-- A successful CAS records its write, then performs the actual newest-message RMW. -/
theorem casRmw_amap {m : Mem} {li c pos : Nat} {l : ALoc} {hF : Heap}
    {expected new : BitVec n} (hl : W.Loc m li l) (hlen : l.len = nb) (hch : l.Chain)
    (hr : (casOpts m li expected)[c]? = some pos)
    (hv : (intOfBytes n ((m.atomics[li]!).msgs[pos]!).bytes).run = some (.ok expected))
    (hc : m.current < m.clocks.size) (hb : ∃ blk, m.blocks[W.b]? = some blk)
    (hoff : ∀ x, W.o ≤ x → x < W.o + nb → hF (W.b, x) = none) (ord : AtomicOrder) :
    m.nextMsg ≤ (rmwM (m.recordAt W.b W.o nb .atomicWrite) li pos ord
      ((m.atomics[li]!).msgs[pos]!) new).nextMsg ∧
      ∃ σ, AMap hF m (rmwM (m.recordAt W.b W.o nb .atomicWrite) li pos ord
        ((m.atomics[li]!).msgs[pos]!) new) σ := by
  have hpos := cas_chain_pos (by rwa [(loc_get hl).2.2]) hr hv
  have hj := (casOpts_pos hr).1
  rw [(loc_get hl).2.2] at hpos hj
  have hlr : W.Loc (m.recordAt W.b W.o nb .atomicWrite) li l := hl
  obtain ⟨hn, σ, ha⟩ := rmwM_amap (pos := pos) hlr hlen (by omega)
    (by simpa [Mem.recordAt] using hc) (rec_recordAt rfl hc) hb hoff ord new
  have hr : AMap hF m (m.recordAt W.b W.o nb .atomicWrite) some := AMap.of_eq rfl rfl
  exact ⟨hn, _, hr.trans ha rfl⟩

/-- A successful CAS records its actual write and performs a native newest-message RMW.
The non-constant block is supplied by the valid source word, not a client admission. -/
theorem casRmw_fstep {m : Mem} {li c pos : Nat} {l : ALoc} {hF : Heap}
    {expected new : BitVec n} (hl : W.Loc m li l) (hlen : l.len = nb) (hch : l.Chain)
    (hr : (casOpts m li expected)[c]? = some pos)
    (hv : (intOfBytes n ((m.atomics[li]!).msgs[pos]!).bytes).run = some (.ok expected))
    (hc : m.current < m.clocks.size)
    (hb : ∃ blk, m.blocks[W.b]? = some blk ∧ blk.kind ≠ .constGlobal)
    (hoff : ∀ x, W.o ≤ x → x < W.o + nb → hF (W.b, x) = none) (ord : AtomicOrder) :
    FStepIn hF m (rmwM (m.recordAt W.b W.o nb .atomicWrite) li pos ord
      ((m.atomics[li]!).msgs[pos]!) new) := by
  obtain ⟨blk, hb, hk⟩ := hb
  have hnot : ¬ m.IsConst W.b := by
    rintro ⟨blk', hb', hk'⟩
    rw [hb] at hb'
    cases hb'
    exact hk hk'
  have hp := cas_chain_pos (by rwa [(loc_get hl).2.2]) hr hv
  have hj := (casOpts_pos hr).1
  rw [(loc_get hl).2.2] at hp hj
  have hlr : W.Loc (m.recordAt W.b W.o nb .atomicWrite) li l := hl
  have hs : FStepIn hF m (m.recordAt W.b W.o nb .atomicWrite) :=
    FStepIn.recordAt_of hc hoff (Array.getElem?_eq_some_iff.mp hb).1 (fun _ => hnot)
  exact hs.trans (rmwM_fstep (pos := pos) hlr hlen (by omega)
    (hs.cur hc) (rec_recordAt rfl hc) ⟨blk, hb⟩ hoff ord new)

/-- A successful CAS preserves the resource rest through its actual write record and RMW. -/
theorem casRmw_rest {m : Mem} {li c pos : Nat} {l : ALoc} {blk : Block}
    {expected new : BitVec n} (hl : W.Loc m li l) (hlen : l.len = nb) (hch : l.Chain)
    (hr : (casOpts m li expected)[c]? = some pos)
    (hv : (intOfBytes n ((m.atomics[li]!).msgs[pos]!).bytes).run = some (.ok expected))
    (hc : m.current < m.clocks.size) (hb : m.blocks[W.b]? = some blk)
    (hlive : blk.live = true) (hsize : W.o + nb ≤ blk.bytes.size)
    (hk : blk.kind ≠ .constGlobal) (hlo : blk.kind.mappedLo ≤ W.o) (ord : AtomicOrder) :
    RestStep W.In m (rmwM (m.recordAt W.b W.o nb .atomicWrite) li pos ord
      ((m.atomics[li]!).msgs[pos]!) new) := by
  have hnot : ¬ m.IsConst W.b := by
    rintro ⟨blk', hb', hk'⟩
    rw [hb] at hb'; cases hb'
    exact hk hk'
  have hp := cas_chain_pos (by rwa [(loc_get hl).2.2]) hr hv
  have hj := (casOpts_pos hr).1
  rw [(loc_get hl).2.2] at hp hj
  have hrest := record_rest_of (W := W) hc (Array.getElem?_eq_some_iff.mp hb).1
    (fun _ => hnot) (k := .atomicWrite) (fun ⟨b, x⟩ ⟨heq, h1, h2⟩ => by
      simp only at heq h1 h2; subst b
      simp only [Mem.heap, hb]
      rw [dite_eq_left_of_eq_true (eq_true ⟨hlive, by omega, by omega⟩)]
      simp)
  have hlr : W.Loc (m.recordAt W.b W.o nb .atomicWrite) li l := hl
  exact hrest.trans (rmwM_rest (pos := pos) hlr hlen (by omega) (by simpa [Mem.recordAt] using hc)
    (rec_recordAt rfl hc) hb hlive hsize hk hlo ord new)

/-- Both branches of a completed strong CAS are native full-state steps of a disjoint frame. -/
theorem cmpxchg_fstep {m m' : Mem} {c : Nat} {succ fail : AtomicOrder}
    {expected new : BitVec n} {r : Option (BitVec n)} {hF : Heap}
    (hw : W.Ok m) (hc : m.current < m.clocks.size)
    (hoff : ∀ x, W.o ≤ x → x < W.o + nb → hF (W.b, x) = none)
    (h : ((cmpxchgAt c succ fail nb W.ptr expected new).run m).run = some (.ok (r, m'))) :
    FStepIn hF m m' := by
  obtain ⟨b, blk, o, li, m₁, pos, old, hacc, _, hp, hr, hv, hcase⟩ := cmpxchgAt_ok h
  obtain ⟨blk₀, hblk, _, _, _, ha⟩ := hw.access
  rw [W.sz_eq, ha] at hacc
  rw [W.sz_eq] at hp
  cases hacc
  obtain ⟨l, hl, hlen, _, hch, _, _, _, _⟩ := prepare hw rfl hp
  obtain ⟨_, hcs, hblocks⟩ := prepare_rec hc hp
  obtain ⟨wordBlk, hword, _, _, _, hkind, _⟩ := hw.blk
  have hs := prepare_fstep hw hc hoff hp
  rcases hcase with ⟨rfl, _, _, rfl⟩ | ⟨_, _, rfl⟩
  · rw [W.sz_eq]
    exact hs.trans (casRmw_fstep (new := new) hl hlen hch hr hv hcs
      ⟨wordBlk, by rw [hblocks]; exact hword, hkind⟩ hoff succ)
  · exact hs.trans
      (FStepIn.loadM hcs fail ((m₁.atomics[li]!).msgs[pos]!) (loc_notIn hl hlen hoff))

/-- Both strong-CAS branches preserve the resource rest. -/
theorem cmpxchg_rest {m m' : Mem} {c : Nat} {succ fail : AtomicOrder}
    {expected new : BitVec n} {r : Option (BitVec n)} (hw : W.Ok m)
    (hc : m.current < m.clocks.size)
    (h : ((cmpxchgAt c succ fail nb W.ptr expected new).run m).run = some (.ok (r, m'))) :
    RestStep W.In m m' := by
  obtain ⟨b, blk, o, li, m₁, pos, old, hacc, _, hp, hr, hv, hcase⟩ := cmpxchgAt_ok h
  obtain ⟨blk₀, _, _, _, _, ha⟩ := hw.access
  rw [W.sz_eq, ha] at hacc
  rw [W.sz_eq] at hp
  cases hacc
  obtain ⟨l, hl, hlen, _, hch, _⟩ := prepare hw rfl hp
  obtain ⟨_, hcs, hblocks⟩ := prepare_rec hc hp
  obtain ⟨wordBlk, hb, hlive, hsize, _, hk, hlo⟩ := hw.blk
  have hs := prepare_rest hw hc rfl hp
  rcases hcase with ⟨rfl, _, _, rfl⟩ | ⟨_, _, rfl⟩
  · rw [W.sz_eq]
    exact hs.trans (casRmw_rest (new := new) hl hlen hch hr hv hcs
      (by rw [hblocks]; exact hb) hlive hsize hk hlo succ)
  · exact hs.trans (loadM_rest hs.live hl hlen hcs fail _)

/-- Both branches of a completed strong CAS carry the actual disjoint-frame map. -/
theorem cmpxchg_amap {m m' : Mem} {c : Nat} {succ fail : AtomicOrder}
    {expected new : BitVec n} {r : Option (BitVec n)} {hF : Heap}
    (hw : W.Ok m) (hc : m.current < m.clocks.size)
    (hoff : ∀ x, W.o ≤ x → x < W.o + nb → hF (W.b, x) = none)
    (h : ((cmpxchgAt c succ fail nb W.ptr expected new).run m).run = some (.ok (r, m'))) :
    m.nextMsg ≤ m'.nextMsg ∧ ∃ σ, AMap hF m m' σ := by
  have hs := cmpxchg_fstep hw hc hoff h
  exact ⟨hs.nextMsg, hs.atomics⟩

/-- Success, mismatch and matching-value spurious failure of weak CAS are native full-state
steps. The success branch uses the same newest-message write as strong CAS. -/
theorem cmpxchgWeak_fstep {m m' : Mem} {c : Nat} {succ fail : AtomicOrder}
    {expected new : BitVec n} {r : Option (BitVec n)} {hF : Heap}
    (hw : W.Ok m) (hc : m.current < m.clocks.size)
    (hoff : ∀ x, W.o ≤ x → x < W.o + nb → hF (W.b, x) = none)
    (h : ((cmpxchgWeakAt c succ fail nb W.ptr expected new).run m).run = some (.ok (r, m'))) :
    FStepIn hF m m' := by
  obtain ⟨b, blk, o, li, m₁, pos, spurious, old, hacc, _, hp, hr, hv, hb⟩ := cmpxchgWeakAt_ok h
  obtain ⟨blk₀, hblk, _, _, _, ha⟩ := hw.access
  rw [W.sz_eq, ha] at hacc
  rw [W.sz_eq] at hp
  cases hacc
  obtain ⟨l, hl, hlen, _, hch, _, _, _, _⟩ := prepare hw rfl hp
  obtain ⟨_, hcs, hblocks⟩ := prepare_rec hc hp
  obtain ⟨wordBlk, hword, _, _, _, hkind, _⟩ := hw.blk
  have hs := prepare_fstep hw hc hoff hp
  rcases hb with ⟨rfl, rfl, _, _, rfl⟩ | ⟨_, _, rfl⟩
  · obtain ⟨j, hj⟩ := weakCasOpts_strong hr
    rw [W.sz_eq]
    exact hs.trans (casRmw_fstep (new := new) hl hlen hch hj hv hcs
      ⟨wordBlk, by rw [hblocks]; exact hword, hkind⟩ hoff succ)
  · exact hs.trans
      (FStepIn.loadM hcs fail ((m₁.atomics[li]!).msgs[pos]!) (loc_notIn hl hlen hoff))

/-- Weak-CAS success, mismatch and matching-value spurious failure preserve the resource rest. -/
theorem cmpxchgWeak_rest {m m' : Mem} {c : Nat} {succ fail : AtomicOrder}
    {expected new : BitVec n} {r : Option (BitVec n)} (hw : W.Ok m)
    (hc : m.current < m.clocks.size)
    (h : ((cmpxchgWeakAt c succ fail nb W.ptr expected new).run m).run = some (.ok (r, m'))) :
    RestStep W.In m m' := by
  obtain ⟨b, blk, o, li, m₁, pos, spurious, old, hacc, _, hp, hr, hv, hcase⟩ := cmpxchgWeakAt_ok h
  obtain ⟨blk₀, _, _, _, _, ha⟩ := hw.access
  rw [W.sz_eq, ha] at hacc
  rw [W.sz_eq] at hp
  cases hacc
  obtain ⟨l, hl, hlen, _, hch, _⟩ := prepare hw rfl hp
  obtain ⟨_, hcs, hblocks⟩ := prepare_rec hc hp
  obtain ⟨wordBlk, hb, hlive, hsize, _, hk, hlo⟩ := hw.blk
  have hs := prepare_rest hw hc rfl hp
  rcases hcase with ⟨rfl, rfl, _, _, rfl⟩ | ⟨_, _, rfl⟩
  · obtain ⟨j, hj⟩ := weakCasOpts_strong hr
    rw [W.sz_eq]
    exact hs.trans (casRmw_rest (new := new) hl hlen hch hj hv hcs
      (by rw [hblocks]; exact hb) hlive hsize hk hlo succ)
  · exact hs.trans (loadM_rest hs.live hl hlen hcs fail _)

/-- Weak CAS carries the same map for success, mismatches and matching-value spurious failures. -/
theorem cmpxchgWeak_amap {m m' : Mem} {c : Nat} {succ fail : AtomicOrder}
    {expected new : BitVec n} {r : Option (BitVec n)} {hF : Heap}
    (hw : W.Ok m) (hc : m.current < m.clocks.size)
    (hoff : ∀ x, W.o ≤ x → x < W.o + nb → hF (W.b, x) = none)
    (h : ((cmpxchgWeakAt c succ fail nb W.ptr expected new).run m).run = some (.ok (r, m'))) :
    m.nextMsg ≤ m'.nextMsg ∧ ∃ σ, AMap hF m m' σ := by
  have hs := cmpxchgWeak_fstep hw hc hoff h
  exact ⟨hs.nextMsg, hs.atomics⟩

/-- Actual primitive runs at a valid word preserve every disjoint full-state frame.
The alternatives retain every width, order, signedness and strong/weak CAS result. -/
theorem actualRun_fstep {m m' : Mem} {hF : Heap} (hw : W.Ok m)
    (hc : m.current < m.clocks.size)
    (hoff : ∀ x, W.o ≤ x → x < W.o + nb → hF (W.b, x) = none)
    (hop :
      (∃ (c : Nat) (ord : AtomicOrder) (v : BitVec n),
        ((atomicLoadAt c ord nb W.ptr).run m).run = some (.ok (v, m'))) ∨
      (∃ (c : Nat) (op : RmwOp) (signed : Bool) (ord : AtomicOrder)
          (v old : BitVec n),
        ((atomicRmwAt c op signed ord nb W.ptr v).run m).run =
          some (.ok (old, m'))) ∨
      (∃ (c : Nat) (succ fail : AtomicOrder) (expected new : BitVec n)
          (r : Option (BitVec n)),
        ((cmpxchgAt c succ fail nb W.ptr expected new).run m).run =
          some (.ok (r, m'))) ∨
      (∃ (c : Nat) (succ fail : AtomicOrder) (expected new : BitVec n)
          (r : Option (BitVec n)),
        ((cmpxchgWeakAt c succ fail nb W.ptr expected new).run m).run =
          some (.ok (r, m'))) ∨
      m' = m.recordAt W.b W.o nb .atomicRead) :
    FStepIn hF m m' := by
  rcases hop with ⟨c, ord, v, hr⟩ | ⟨c, op, signed, ord, v, old, hr⟩ |
    ⟨c, succ, fail, expected, new, r, hr⟩ |
    ⟨c, succ, fail, expected, new, r, hr⟩ | hr
  · exact atomicLoad_fstep hw hc hoff hr
  · exact atomicRmw_fstep hw hc hoff hr
  · exact cmpxchg_fstep hw hc hoff hr
  · exact cmpxchgWeak_fstep hw hc hoff hr
  · rw [hr]
    exact record_fstep (k := .atomicRead) hw hc hoff

/-- Normalize a whole family of actual disjoint-frame maps to the explicitly named actor.
The counter fact follows at the empty frame; no destination `current` fact is needed. -/
theorem amap_for_actor {m m' : Mem} {t : ThreadId} (hc : m.current = t)
    (h : ∀ hF, (∀ x, W.o ≤ x → x < W.o + nb → hF (W.b, x) = none) →
      m.nextMsg ≤ m'.nextMsg ∧ ∃ σ, AMap hF m m' σ) :
    m.nextMsg ≤ m'.nextMsg ∧ ∀ hF,
      (∀ x, W.o ≤ x → x < W.o + nb → hF (W.b, x) = none) →
      ∃ σ, AMap hF { m with current := t } { m' with current := t } σ := by
  refine ⟨(h (fun _ => none) (fun _ _ _ => rfl)).1, fun hF hoff => ?_⟩
  obtain ⟨_, σ, ha⟩ := h hF hoff
  exact ⟨σ, ha.withCurrent hc⟩

/-- The scheduler's futex compare/sleep records an access and changes only its queue or woken
set. Unlike an atomic-load operation, it does not select an atomic-history message. -/
theorem futexWait_fields {m m' : Mem} {p : Ptr} {e : BitVec 32} {b : Bool}
    (h : ((Thread.futexWait p e).run m).run = some (.ok (b, m'))) :
    m'.atomics = m.atomics ∧ m'.seen = m.seen ∧ m'.nextMsg = m.nextMsg := by
  rcases futexWait_eq h with ⟨_, rfl, rfl⟩ | ⟨_, bid, blk, o, v, _, _, _, hcase⟩
  · exact ⟨rfl, rfl, rfl⟩
  rcases hcase with ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩ <;> exact ⟨rfl, rfl, rfl⟩

/-- The current thread observes message `id` of the word's location. -/
theorem ownPos_observe {m : Mem} {i : Nat} {l : ALoc} (hl : W.Loc m i l) (id u : Nat) :
    W.ownPos (observeM m i id) u = if u = m.current then (l.pos id).getD 0 else W.ownPos m u := by
  have hl' : W.Loc (observeM m i id) i l := hl
  rw [ownPos_loc hl', ownPos_loc hl, seenAt_observe]
  by_cases hu : u = m.current <;> simp [hu]

/-- A read of message `j` of the word's location (`loadM`): the reader's floor is `j`, the
other floors stay. -/
theorem loadM_seen {m : Mem} {i : Nat} {l : ALoc} (hl : W.Loc m i l) (hf : W.Fresh m) {j : Nat}
    (hj : j < l.msgs.size) (ord : AtomicOrder) :
    W.ownPos (loadM m i ord (l.msgs[j]!)) m.current = j ∧
      (∀ u, u ≠ m.current → W.ownPos (loadM m i ord (l.msgs[j]!)) u = W.ownPos m u) ∧
      W.Fresh (loadM m i ord (l.msgs[j]!)) := by
  have hobs : ∀ u, W.ownPos (loadM m i ord (l.msgs[j]!)) u =
      W.ownPos (observeM m i (l.msgs[j]!).id) u := by
    intro u; unfold loadM; dsimp only; split
    · exact ownPos_of_eq rfl rfl u
    · rfl
  refine ⟨?_, fun u hu => ?_, hf.of_eq (by unfold loadM; split <;> rfl)
    (by unfold loadM; split <;> exact Nat.le_refl _)⟩
  · rw [hobs, ownPos_observe hl, if_pos rfl, getElem!_pos l.msgs j hj, (hf i l hl j hj).2]; rfl
  · rw [hobs, ownPos_observe hl, ite_eq_right hu]

/-- Every admitted read choice, at every atomic order, preserves freshness and advances only
the reader's floor. An unconstrained `observeM` does not have this property. -/
theorem loadM_read_seen {m : Mem} {i c j : Nat} {l : ALoc} (hl : W.Loc m i l)
    (hf : W.Fresh m) (hr : (readOpts m i false)[c]? = some j) (ord : AtomicOrder) :
    W.Fresh (loadM m i ord (l.msgs[j]!)) ∧
      ∀ u, W.ownPos m u ≤ W.ownPos (loadM m i ord (l.msgs[j]!)) u := by
  have hj := readOpts_lt hr
  rw [(loc_get hl).2.2] at hj
  obtain ⟨ha, ho, hf'⟩ := loadM_seen hl hf hj ord
  refine ⟨hf', fun u => ?_⟩
  by_cases hu : u = m.current
  · subst u; rw [ha]; exact Nat.le_trans (ownPos_le_floor hl) (floor_le hr)
  · rw [ho u hu]; exact Nat.le_refl _

/-- The bytes returned by a read belong to the message at its resulting caller-local floor. -/
theorem loadM_seen_val {m : Mem} {i j : Nat} {l : ALoc} {v : BitVec n}
    (hl : W.Loc m i l) (hf : W.Fresh m) (hj : j < l.msgs.size)
    (hv : (intOfBytes n (l.msgs[j]!).bytes).run = some (.ok v)) (ord : AtomicOrder) :
    j < (W.hist (loadM m i ord (l.msgs[j]!))).size ∧
      (W.hist (loadM m i ord (l.msgs[j]!)))[j]!.Val v ∧
      W.ownPos (loadM m i ord (l.msgs[j]!)) m.current = j := by
  have ha : (loadM m i ord (l.msgs[j]!)).atomics = m.atomics := by
    unfold loadM; split <;> rfl
  have hL : W.Loc (loadM m i ord (l.msgs[j]!)) i l := by
    unfold Loc; rw [ha]; exact hl
  exact ⟨by rw [hist_size hL]; exact hj, val_of hL hj hv, (loadM_seen hl hf hj ord).1⟩

/-- A completed load at the word satisfies the floor property for its actual selected message. -/
theorem atomicLoad_seen {m m' : Mem} {c : Nat} {ord : AtomicOrder} {v : BitVec n}
    (hw : W.Ok m) (hf : W.Fresh m)
    (h : ((atomicLoadAt c ord nb W.ptr).run m).run = some (.ok (v, m'))) :
    W.Fresh m' ∧ (∀ u, W.ownPos m u ≤ W.ownPos m' u) ∧
      m.nextMsg ≤ m'.nextMsg ∧ m'.current = m.current := by
  obtain ⟨b, blk, o, li, m₁, pos, hacc, _, hp, hr, _, rfl⟩ := atomicLoadAt_ok h
  obtain ⟨blk₀, _, _, _, ha, _⟩ := hw.access
  rw [W.sz_eq, ha] at hacc
  rw [W.sz_eq] at hp
  cases hacc
  obtain ⟨l, hl, _, _, _, hf₁, he, hn, hc⟩ := prepare_seen hw hf rfl hp
  rw [(loc_get hl).2.2]
  obtain ⟨hf', hm⟩ := loadM_read_seen hl hf₁ hr ord
  refine ⟨hf', fun u => by rw [← he u]; exact hm u, ?_, (loadM_current _ _ _ _).trans hc⟩
  exact Nat.le_trans hn (by unfold loadM; split <;> exact Nat.le_refl _)

/-- The actual selected message of a load is the reader's new floor. The witness uses the
resulting history, so it composes with any existing rule that preserves that history. -/
theorem atomicLoad_read_seen {m m' : Mem} {c : Nat} {ord : AtomicOrder} {v : BitVec n}
    (hw : W.Ok m) (hf : W.Fresh m)
    (h : ((atomicLoadAt c ord nb W.ptr).run m).run = some (.ok (v, m'))) :
    W.Fresh m' ∧ (∀ u, W.ownPos m u ≤ W.ownPos m' u) ∧
      ∃ j < (W.hist m').size, (W.hist m')[j]!.Val v ∧ W.ownPos m' m.current = j := by
  obtain ⟨hf', hm, _, _⟩ := atomicLoad_seen hw hf h
  refine ⟨hf', hm, ?_⟩
  obtain ⟨b, blk, o, li, m₁, pos, hacc, _, hp, hr, hv, rfl⟩ := atomicLoadAt_ok h
  obtain ⟨blk₀, _, _, _, ha, _⟩ := hw.access
  rw [W.sz_eq, ha] at hacc
  rw [W.sz_eq] at hp
  cases hacc
  obtain ⟨l, hl, _, _, _, hf₁, _, _, hc⟩ := prepare_seen hw hf rfl hp
  have hj := readOpts_lt hr
  rw [(loc_get hl).2.2] at hj hv ⊢
  refine ⟨pos, ?_⟩
  rw [← hc]
  exact loadM_seen_val hl hf₁ hj hv ord

/-- A message with a fresh id at the end of the word's location keeps the ids fresh and no floor
smaller, and it is at the end. -/
theorem fresh_push {m M : Mem} {i : Nat} {l : ALoc} {x : Msg} (hl : W.Loc m i l)
    (hf : W.Fresh m) (hL : W.Loc M i { l with msgs := l.msgs.push x }) (hx : x.id = m.nextMsg)
    (hn : M.nextMsg = m.nextMsg + 1) (hs : M.seen = m.seen) :
    W.Fresh M ∧ (∀ u, W.ownPos m u ≤ W.ownPos M u) ∧
      ({ l with msgs := l.msgs.push x } : ALoc).pos x.id = some l.msgs.size := by
  have hold : ∀ id k, l.pos id = some k →
      ({ l with msgs := l.msgs.push x } : ALoc).pos id = some k := by
    intro id k h
    unfold ALoc.pos at h ⊢
    rw [Array.findIdx?_push, h]; rfl
  have hnew : ({ l with msgs := l.msgs.push x } : ALoc).pos x.id = some l.msgs.size := by
    have hnone : l.msgs.findIdx? (·.id == x.id) = none := by
      rw [Array.findIdx?_eq_none_iff]
      intro y hy
      obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem hy
      have := (hf i l hl k hk).1
      simpa using (by omega : l.msgs[k].id ≠ x.id)
    unfold ALoc.pos
    rw [Array.findIdx?_push, hnone]; simp
  refine ⟨fun i' l' hl' k hk => ?_, fun u => ?_, hnew⟩
  · obtain ⟨e1, e2⟩ := loc_unique hL hl'
    subst e1 e2
    rw [hn]
    simp only [Array.size_push] at hk
    by_cases hk' : k < l.msgs.size
    · simp only [Array.getElem_push, hk', ↓reduceDIte]
      obtain ⟨h1, h2⟩ := hf i l hl k hk'
      exact ⟨by omega, hold _ _ h2⟩
    · obtain rfl : k = l.msgs.size := by omega
      simp only [Array.getElem_push, Nat.lt_irrefl, ↓reduceDIte]
      exact ⟨by omega, hnew⟩
  · have hsa : M.seenAt u i = m.seenAt u i := by unfold Mem.seenAt; rw [hs]
    rw [ownPos_loc hl, ownPos_loc hL, hsa]
    cases m.seenAt u i with
    | none => exact Nat.le_refl _
    | some id =>
      show (l.pos id).getD 0 ≤ (({ l with msgs := l.msgs.push x } : ALoc).pos id).getD 0
      cases hp : l.pos id with
      | none => exact Nat.zero_le _
      | some k => rw [hold _ _ hp]; exact Nat.le_refl _

/-- Inserting immediately after the newest message keeps the word at the same location. -/
theorem loc_insert_last {m : Mem} {i pos : Nat} {l : ALoc} (hl : W.Loc m i l)
    (hp : pos + 1 = l.msgs.size) (msg : Msg) :
    W.Loc (insertM m i (pos + 1) msg) i { l with msgs := l.msgs.push msg } := by
  unfold Loc
  rw [insertM_atomics, (loc_get hl).2.2, hp, Conc.Proto.insertIdxIfInBounds_size_self]
  exact loc_set hl rfl rfl

/-- An RMW of the newest message of the word's location (`rmwM`): the writer's floor is the new
message, at the end; no other floor gets smaller. -/
theorem rmwM_seen {m : Mem} {i : Nat} {l : ALoc} (hl : W.Loc m i l) (hf : W.Fresh m) {pos : Nat}
    (hpos : pos + 1 = l.msgs.size) (ord : AtomicOrder) (rd : Msg) (new : BitVec n) :
    W.ownPos (rmwM m i pos ord rd new) m.current = l.msgs.size ∧
      (∀ u, u ≠ m.current → W.ownPos m u ≤ W.ownPos (rmwM m i pos ord rd new) u) ∧
      W.Fresh (rmwM m i pos ord rd new) := by
  obtain ⟨m₂, ha₂, hs₂, hn₂, hc₂, e⟩ : ∃ m₂ : Mem, m₂.atomics = m.atomics ∧ m₂.seen = m.seen ∧
      m₂.nextMsg = m.nextMsg ∧ m₂.current = m.current ∧
      rmwM m i pos ord rd new = observeM (insertM m₂ i (pos + 1) (rmwMsg m₂ ord rd new)) i
        m₂.nextMsg := by
    unfold rmwM; dsimp only; split
    · exact ⟨acqM m rd.relClock, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨m, rfl, rfl, rfl, rfl, rfl⟩
  rw [e]
  have hl₂ : W.Loc m₂ i l := by unfold Loc; rw [ha₂]; exact hl
  have hf₂ : W.Fresh m₂ := hf.of_eq ha₂ (Nat.le_of_eq hn₂.symm)
  have hl0 := (loc_get hl₂).2.2
  generalize hmsg : rmwMsg m₂ ord rd new = msg
  have hid : msg.id = m₂.nextMsg := by rw [← hmsg]; rfl
  have hMa : (insertM m₂ i (pos + 1) msg).atomics =
      m₂.atomics.set! i { l with msgs := l.msgs.push msg } := by
    rw [insertM_atomics, hl0, hpos, Conc.Proto.insertIdxIfInBounds_size_self]
  generalize hM : insertM m₂ i (pos + 1) msg = M at hMa
  have hL : W.Loc M i { l with msgs := l.msgs.push msg } := by
    unfold Loc; rw [hMa]; exact loc_set hl₂ rfl rfl
  have hMs : M.seen = m₂.seen := by rw [← hM]; exact insertM_seen
  have hMn : M.nextMsg = m₂.nextMsg + 1 := by rw [← hM]; exact insertM_nextMsg
  have hMc : M.current = m.current := by rw [← hM]; exact insertM_current.trans hc₂
  obtain ⟨hfM, hle, hend⟩ := fresh_push hl₂ hf₂ hL hid hMn hMs
  rw [← hid]
  refine ⟨?_, fun u hu => ?_, hfM.of_eq rfl (Nat.le_refl _)⟩
  · rw [ownPos_observe hL, ← hMc, ite_eq_left rfl, hend]; rfl
  · rw [ownPos_observe hL, ite_eq_right (by rw [hMc]; exact hu), ← ownPos_of_eq ha₂ hs₂ u]
    exact hle u

/-- Appending an RMW to the newest message preserves freshness and every thread's floor. -/
theorem rmwM_latest_seen {m : Mem} {i pos : Nat} {l : ALoc} (hl : W.Loc m i l)
    (hf : W.Fresh m) (hp : pos + 1 = l.msgs.size) (ord : AtomicOrder) (rd : Msg) (new : BitVec n) :
    W.Fresh (rmwM m i pos ord rd new) ∧
      ∀ u, W.ownPos m u ≤ W.ownPos (rmwM m i pos ord rd new) u := by
  obtain ⟨ha, ho, hf'⟩ := rmwM_seen hl hf hp ord rd new
  refine ⟨hf', fun u => ?_⟩
  by_cases hu : u = m.current
  · subst u; rw [ha]; exact Nat.le_of_lt (ownPos_lt hl (by omega) _)
  · exact ho u hu

/-- A successful newest-message RMW leaves its caller's floor at the new last write. -/
theorem rmwM_seen_last {m : Mem} {i pos : Nat} {l : ALoc} (hl : W.Loc m i l)
    (hf : W.Fresh m) (hp : pos + 1 = l.msgs.size) (ord : AtomicOrder) (rd : Msg) (new : BitVec n) :
    W.ownPos (rmwM m i pos ord rd new) m.current =
      (W.hist (rmwM m i pos ord rd new)).size - 1 := by
  have hs : (W.hist (rmwM m i pos ord rd new)).size = l.msgs.size + 1 := by
    unfold rmwM
    split
    · have hl' : W.Loc (acqM m rd.relClock) i l := hl
      change (W.hist (insertM (acqM m rd.relClock) i (pos + 1)
        (rmwMsg (acqM m rd.relClock) ord rd new))).size = l.msgs.size + 1
      rw [hist_size (loc_insert_last hl' hp _)]; simp
    · change (W.hist (insertM m i (pos + 1) (rmwMsg m ord rd new))).size = l.msgs.size + 1
      rw [hist_size (loc_insert_last hl hp _)]; simp
  rw [hs, Nat.add_sub_cancel]
  exact (rmwM_seen hl hf hp ord rd new).1

/-- An RMW's actual read choice in a chain selects its newest message. -/
theorem rmwM_read_seen {m : Mem} {i c pos : Nat} {l : ALoc} (hl : W.Loc m i l)
    (hf : W.Fresh m) (h0 : 0 < l.msgs.size) (hc : l.Chain)
    (hr : (readOpts m i true)[c]? = some pos) (ord : AtomicOrder) (new : BitVec n) :
    W.Fresh (rmwM m i pos ord (l.msgs[pos]!) new) ∧
      ∀ u, W.ownPos m u ≤ W.ownPos (rmwM m i pos ord (l.msgs[pos]!) new) u := by
  have hp : pos + 1 = l.msgs.size := by
    have := rmw_chain_pos (by rwa [(loc_get hl).2.2]) (by rwa [(loc_get hl).2.2]) hr
    rw [(loc_get hl).2.2] at this
    omega
  exact rmwM_latest_seen hl hf hp ord _ new

/-- Every completed RMW operation and signedness uses the same floor/freshness rule. -/
theorem atomicRmw_seen {m m' : Mem} {c : Nat} {op : RmwOp} {signed : Bool} {ord : AtomicOrder}
    {v old : BitVec n} (hw : W.Ok m) (hf : W.Fresh m)
    (h : ((atomicRmwAt c op signed ord nb W.ptr v).run m).run = some (.ok (old, m'))) :
    W.Fresh m' ∧ (∀ u, W.ownPos m u ≤ W.ownPos m' u) ∧
      m.nextMsg ≤ m'.nextMsg ∧ m'.current = m.current := by
  obtain ⟨b, blk, o, li, m₁, pos, hacc, _, hp, hr, _, rfl⟩ := atomicRmwAt_ok h
  obtain ⟨blk₀, _, _, _, _, ha⟩ := hw.access
  rw [W.sz_eq, ha] at hacc
  rw [W.sz_eq] at hp
  cases hacc
  obtain ⟨l, hl, _, h0, hchain, hf₁, he, hn, hc⟩ := prepare_seen hw hf rfl hp
  rw [(loc_get hl).2.2]
  obtain ⟨hf', hm⟩ := rmwM_read_seen hl hf₁ h0 hchain hr ord (op.apply signed old v)
  refine ⟨hf', fun u => by rw [← he u]; exact hm u, Nat.le_trans hn ?_, ?_⟩
  · unfold rmwM
    split <;> dsimp only [observeM] <;> rw [insertM_nextMsg] <;> exact Nat.le_succ _
  · unfold rmwM
    split <;> exact insertM_current.trans hc

/-- Every completed RMW leaves its caller at the new last write, for every operation, order
and signedness. -/
theorem atomicRmw_write_seen {m m' : Mem} {c : Nat} {op : RmwOp} {signed : Bool} {ord : AtomicOrder}
    {v old : BitVec n} (hw : W.Ok m) (hf : W.Fresh m)
    (h : ((atomicRmwAt c op signed ord nb W.ptr v).run m).run = some (.ok (old, m'))) :
    W.ownPos m' m.current = (W.hist m').size - 1 := by
  obtain ⟨b, blk, o, li, m₁, pos, hacc, _, hp, hr, _, rfl⟩ := atomicRmwAt_ok h
  obtain ⟨blk₀, _, _, _, _, ha⟩ := hw.access
  rw [W.sz_eq, ha] at hacc
  rw [W.sz_eq] at hp
  cases hacc
  obtain ⟨l, hl, _, h0, hchain, hf₁, _, _, hc⟩ := prepare_seen hw hf rfl hp
  have hp' := rmw_chain_pos (by rwa [(loc_get hl).2.2]) (by rwa [(loc_get hl).2.2]) hr
  rw [(loc_get hl).2.2] at hp' ⊢
  rw [← hc]
  exact rmwM_seen_last hl hf₁ (by omega) ord _ _

/-- Success of a CAS uses the newest message of a chain. Recording its write does not change
the floors or freshness before the RMW. -/
theorem casRmw_seen {m : Mem} {i c pos : Nat} {l : ALoc} {expected new : BitVec n}
    (hl : W.Loc m i l) (hf : W.Fresh m) (hc : l.Chain)
    (hr : (casOpts m i expected)[c]? = some pos)
    (hv : (intOfBytes n ((m.atomics[i]!).msgs[pos]!).bytes).run = some (.ok expected))
    (ord : AtomicOrder) :
    W.Fresh (rmwM (m.recordAt W.b W.o nb .atomicWrite) i pos ord (l.msgs[pos]!) new) ∧
      ∀ u, W.ownPos m u ≤
        W.ownPos (rmwM (m.recordAt W.b W.o nb .atomicWrite) i pos ord (l.msgs[pos]!) new) u := by
  have hp := cas_chain_pos (by rwa [(loc_get hl).2.2]) hr hv
  have hj := (casOpts_pos hr).1
  rw [(loc_get hl).2.2] at hp hj
  have hlr : W.Loc (m.recordAt W.b W.o nb .atomicWrite) i l := hl
  exact rmwM_latest_seen (pos := pos) hlr (hf.of_eq rfl (Nat.le_refl _)) (by omega) ord _ new

/-- Strong CAS preserves freshness and nondecreasing floors in both its successful RMW and
its failure-order read branch. -/
theorem cmpxchg_seen {m m' : Mem} {c : Nat} {succ fail : AtomicOrder}
    {expected new : BitVec n} {r : Option (BitVec n)} (hw : W.Ok m) (hf : W.Fresh m)
    (h : ((cmpxchgAt c succ fail nb W.ptr expected new).run m).run = some (.ok (r, m'))) :
    W.Fresh m' ∧ (∀ u, W.ownPos m u ≤ W.ownPos m' u) ∧
      m.nextMsg ≤ m'.nextMsg ∧ m'.current = m.current := by
  obtain ⟨b, blk, o, li, m₁, pos, old, hacc, _, hp, hr, hv, hb⟩ := cmpxchgAt_ok h
  obtain ⟨blk₀, _, _, _, _, ha⟩ := hw.access
  rw [W.sz_eq, ha] at hacc
  rw [W.sz_eq] at hp
  cases hacc
  obtain ⟨l, hl, _, _, hchain, hf₁, he, hn, hc⟩ := prepare_seen hw hf rfl hp
  rcases hb with ⟨rfl, _, _, rfl⟩ | ⟨_, _, rfl⟩
  · rw [W.sz_eq, (loc_get hl).2.2]
    obtain ⟨hf', hm⟩ := casRmw_seen hl hf₁ hchain hr hv succ
    refine ⟨hf', fun u => by rw [← he u]; exact hm u, Nat.le_trans hn ?_, ?_⟩
    · unfold rmwM
      split <;> dsimp only [observeM] <;> rw [insertM_nextMsg] <;> exact Nat.le_succ _
    · unfold rmwM
      split <;> exact insertM_current.trans hc
  · have hread : ∃ j : Nat, (readOpts m₁ li false)[j]? = some pos := by
      exact Array.mem_iff_getElem?.mp (Array.mem_filter.mp (Array.mem_of_getElem? hr)).1
    obtain ⟨j, hj⟩ := hread
    rw [(loc_get hl).2.2]
    obtain ⟨hf', hm⟩ := loadM_read_seen hl hf₁ hj fail
    refine ⟨hf', fun u => by rw [← he u]; exact hm u, Nat.le_trans hn ?_, (loadM_current _ _ _ _).trans hc⟩
    unfold loadM; split <;> exact Nat.le_refl _

/-- A failed strong CAS reads the message at its resulting floor, at its failure order. -/
theorem cmpxchg_read_seen {m m' : Mem} {c : Nat} {succ fail : AtomicOrder}
    {expected new old : BitVec n} (hw : W.Ok m) (hf : W.Fresh m)
    (h : ((cmpxchgAt c succ fail nb W.ptr expected new).run m).run =
      some (.ok (some old, m'))) :
    W.Fresh m' ∧ (∀ u, W.ownPos m u ≤ W.ownPos m' u) ∧
      ∃ j < (W.hist m').size, (W.hist m')[j]!.Val old ∧ W.ownPos m' m.current = j := by
  obtain ⟨hf', hm, _, _⟩ := cmpxchg_seen hw hf h
  refine ⟨hf', hm, ?_⟩
  obtain ⟨b, blk, o, li, m₁, pos, rd, hacc, _, hp, hr, hv, hb⟩ := cmpxchgAt_ok h
  obtain ⟨blk₀, _, _, _, _, ha⟩ := hw.access
  rw [W.sz_eq, ha] at hacc
  rw [W.sz_eq] at hp
  cases hacc
  obtain ⟨l, hl, _, _, _, hf₁, _, _, hc⟩ := prepare_seen hw hf rfl hp
  rcases hb with ⟨_, he, _, _⟩ | ⟨_, he, rfl⟩
  · cases he
  · cases he
    have hj := (casOpts_pos hr).1
    rw [(loc_get hl).2.2] at hj hv ⊢
    refine ⟨pos, ?_⟩
    rw [← hc]
    exact loadM_seen_val hl hf₁ hj hv fail

/-- A successful strong CAS leaves the caller at its new last message. -/
theorem cmpxchg_write_seen {m m' : Mem} {c : Nat} {succ fail : AtomicOrder}
    {expected new : BitVec n} (hw : W.Ok m) (hf : W.Fresh m)
    (h : ((cmpxchgAt c succ fail nb W.ptr expected new).run m).run =
      some (.ok (none, m'))) :
    W.ownPos m' m.current = (W.hist m').size - 1 := by
  obtain ⟨b, blk, o, li, m₁, pos, old, hacc, _, hp, hr, hv, hb⟩ := cmpxchgAt_ok h
  obtain ⟨blk₀, _, _, _, _, ha⟩ := hw.access
  rw [W.sz_eq, ha] at hacc
  rw [W.sz_eq] at hp
  cases hacc
  obtain ⟨l, hl, _, _, hchain, hf₁, _, _, hc⟩ := prepare_seen hw hf rfl hp
  rcases hb with ⟨rfl, _, _, rfl⟩ | ⟨_, he, _⟩
  · have hp' := cas_chain_pos (by rwa [(loc_get hl).2.2]) hr hv
    have hj := (casOpts_pos hr).1
    rw [(loc_get hl).2.2] at hp' hj
    have hlr : W.Loc (m₁.recordAt W.b W.o nb .atomicWrite) li l := hl
    rw [W.sz_eq, (loc_get hl).2.2, ← hc]
    exact rmwM_seen_last hlr (hf₁.of_eq rfl (Nat.le_refl _)) (by omega) succ _ new
  · cases he

/-- Weak CAS includes every matching-value spurious failure. Each permitted branch uses the
same preparation, read and RMW facts as strong CAS. -/
theorem cmpxchgWeak_seen {m m' : Mem} {c : Nat} {succ fail : AtomicOrder}
    {expected new : BitVec n} {r : Option (BitVec n)} (hw : W.Ok m) (hf : W.Fresh m)
    (h : ((cmpxchgWeakAt c succ fail nb W.ptr expected new).run m).run = some (.ok (r, m'))) :
    W.Fresh m' ∧ (∀ u, W.ownPos m u ≤ W.ownPos m' u) ∧
      m.nextMsg ≤ m'.nextMsg ∧ m'.current = m.current := by
  obtain ⟨b, blk, o, li, m₁, pos, spurious, old, hacc, _, hp, hr, hv, hb⟩ := cmpxchgWeakAt_ok h
  obtain ⟨blk₀, _, _, _, _, ha⟩ := hw.access
  rw [W.sz_eq, ha] at hacc
  rw [W.sz_eq] at hp
  cases hacc
  obtain ⟨l, hl, _, _, hchain, hf₁, he, hn, hc⟩ := prepare_seen hw hf rfl hp
  rcases hb with ⟨rfl, rfl, _, _, rfl⟩ | ⟨_, _, rfl⟩
  · obtain ⟨j, hj⟩ := weakCasOpts_strong hr
    rw [W.sz_eq, (loc_get hl).2.2]
    obtain ⟨hf', hm⟩ := casRmw_seen hl hf₁ hchain hj hv succ
    refine ⟨hf', fun u => by rw [← he u]; exact hm u, Nat.le_trans hn ?_, ?_⟩
    · unfold rmwM
      split <;> dsimp only [observeM] <;> rw [insertM_nextMsg] <;> exact Nat.le_succ _
    · unfold rmwM
      split <;> exact insertM_current.trans hc
  · obtain ⟨j, hj⟩ := weakCasOpts_read hr
    rw [(loc_get hl).2.2]
    obtain ⟨hf', hm⟩ := loadM_read_seen hl hf₁ hj fail
    refine ⟨hf', fun u => by rw [← he u]; exact hm u, Nat.le_trans hn ?_, (loadM_current _ _ _ _).trans hc⟩
    unfold loadM; split <;> exact Nat.le_refl _

/-- The same actual-message fact includes matching-value spurious weak-CAS failures. -/
theorem cmpxchgWeak_read_seen {m m' : Mem} {c : Nat} {succ fail : AtomicOrder}
    {expected new old : BitVec n} (hw : W.Ok m) (hf : W.Fresh m)
    (h : ((cmpxchgWeakAt c succ fail nb W.ptr expected new).run m).run =
      some (.ok (some old, m'))) :
    W.Fresh m' ∧ (∀ u, W.ownPos m u ≤ W.ownPos m' u) ∧
      ∃ j < (W.hist m').size, (W.hist m')[j]!.Val old ∧ W.ownPos m' m.current = j := by
  obtain ⟨hf', hm, _, _⟩ := cmpxchgWeak_seen hw hf h
  refine ⟨hf', hm, ?_⟩
  obtain ⟨b, blk, o, li, m₁, pos, spurious, rd, hacc, _, hp, hr, hv, hb⟩ := cmpxchgWeakAt_ok h
  obtain ⟨blk₀, _, _, _, _, ha⟩ := hw.access
  rw [W.sz_eq, ha] at hacc
  rw [W.sz_eq] at hp
  cases hacc
  obtain ⟨l, hl, _, _, _, hf₁, _, _, hc⟩ := prepare_seen hw hf rfl hp
  rcases hb with ⟨_, _, he, _, _⟩ | ⟨_, he, rfl⟩
  · cases he
  · cases he
    obtain ⟨j, hj⟩ := weakCasOpts_read hr
    have hpos := readOpts_lt hj
    rw [(loc_get hl).2.2] at hpos hv ⊢
    refine ⟨pos, ?_⟩
    rw [← hc]
    exact loadM_seen_val hl hf₁ hpos hv fail

/-- A successful weak CAS has the same newest-write floor as a successful strong CAS. -/
theorem cmpxchgWeak_write_seen {m m' : Mem} {c : Nat} {succ fail : AtomicOrder}
    {expected new : BitVec n} (hw : W.Ok m) (hf : W.Fresh m)
    (h : ((cmpxchgWeakAt c succ fail nb W.ptr expected new).run m).run =
      some (.ok (none, m'))) :
    W.ownPos m' m.current = (W.hist m').size - 1 := by
  obtain ⟨b, blk, o, li, m₁, pos, spurious, old, hacc, _, hp, hr, hv, hb⟩ := cmpxchgWeakAt_ok h
  obtain ⟨blk₀, _, _, _, _, ha⟩ := hw.access
  rw [W.sz_eq, ha] at hacc
  rw [W.sz_eq] at hp
  cases hacc
  obtain ⟨l, hl, _, _, hchain, hf₁, _, _, hc⟩ := prepare_seen hw hf rfl hp
  rcases hb with ⟨rfl, rfl, _, _, rfl⟩ | ⟨_, he, _⟩
  · obtain ⟨j, hj⟩ := weakCasOpts_strong hr
    have hp' := cas_chain_pos (by rwa [(loc_get hl).2.2]) hj hv
    have hpos := (casOpts_pos hj).1
    rw [(loc_get hl).2.2] at hp' hpos
    have hlr : W.Loc (m₁.recordAt W.b W.o nb .atomicWrite) li l := hl
    rw [W.sz_eq, (loc_get hl).2.2, ← hc]
    exact rmwM_seen_last hlr (hf₁.of_eq rfl (Nat.le_refl _)) (by omega) succ _ new
  · cases he

end Word
end Conc
end Zig




namespace Zig.Conc.Proto

/-- A selected atomic read changes neither the blocks nor the ordered atomic array. -/
theorem loadM_fields {m : Mem} {li : Nat} {ord : AtomicOrder} {msg : Msg} :
    (loadM m li ord msg).blocks = m.blocks ∧
      (loadM m li ord msg).atomics = m.atomics := by
  unfold loadM
  split <;> exact ⟨rfl, rfl⟩

end Zig.Conc.Proto

namespace Zig.Conc.Word

open Proto Full

variable {n nb : Nat} {W : Word n nb}

/-- The actual valid-word preparation is exactly the found case or the append
case, including its returned index and complete destination memory. -/
theorem prepare_run_eq {m m' : Mem} {li : Nat} {k : AccessKind} (hw : W.Ok m)
    (hk : k.isAtomic = true)
    (h : ((locIdx W.b W.o nb).run (m.recordAt W.b W.o nb k)).run = some (.ok (li, m'))) :
    (li, m') = match m.atomics.findIdx? (fun l => l.block == W.b && l.off == W.o) with
      | some i => (i, m.recordAt W.b W.o nb k)
      | none => (m.atomics.size, { m.recordAt W.b W.o nb k with
          atomics := m.atomics.push (firstLoc (m.recordAt W.b W.o nb k) W.b W.o nb),
          nextMsg := m.nextMsg + 1 }) := by
  let mr := m.recordAt W.b W.o nb k
  change (li, m') = match mr.atomics.findIdx? (fun l => l.block == W.b && l.off == W.o) with
    | some i => (i, mr)
    | none => (mr.atomics.size, { mr with
        atomics := mr.atomics.push (firstLoc mr W.b W.o nb), nextMsg := mr.nextMsg + 1 })
  cases hf : mr.atomics.findIdx? (fun l => l.block == W.b && l.off == W.o) with
  | some i =>
    have hl := loc_of_find hf
    have hl₀ : W.Loc m i (mr.atomics[i]!) := hl
    obtain ⟨hlen, _, _, hlast, _⟩ := hw.loc i _ hl₀
    have hpl : PlainLe mr W.b W.o nb (mr.atomics[i]!).lastClock :=
      (hw.plain i _ hl₀).of_fp fun e he => by
        simp only [mr, Mem.recordAt, Array.mem_push] at he
        rcases he with he | rfl
        · exact .inl he
        · exact .inr (plainHit_atomic hk)
    obtain ⟨rfl, rfl⟩ := locIdx_found hf hlen hlast hpl h
    rfl
  | none =>
    obtain ⟨rfl, rfl⟩ := locIdx_new hf (noOverlap_of_only hf hw.only) h
    rfl

end Zig.Conc.Word

namespace Zig.Mem

/-- The primitive fixed-size byte write preserves every old block's live flag,
byte-array size and kind, including blocks that were already dead. -/
theorem write_block_fields {m : Mem} {b o : Nat} {blk : Block} {bs : Array Byte}
    (hb : m.blocks[b]? = some blk) (hbound : o + bs.size ≤ blk.bytes.size)
    {q : BlockId} {old : Block} (hq : m.blocks[q]? = some old) :
    ∃ new, (m.write b blk o bs).blocks[q]? = some new ∧ new.live = old.live ∧
      new.bytes.size = old.bytes.size ∧ new.kind = old.kind := by
  have hlt : b < m.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  by_cases he : b = q
  · subst q
    rw [hb] at hq
    cases hq
    refine ⟨{blk with bytes := writeBytes blk.bytes o bs}, ?_, rfl,
      writeBytes_size _ _ _ hbound, rfl⟩
    simp only [Mem.write, Array.set!_eq_setIfInBounds]
    exact Array.getElem?_setIfInBounds_self_of_lt hlt
  · refine ⟨old, ?_, rfl, rfl, rfl⟩
    simp only [Mem.write, Array.set!_eq_setIfInBounds]
    rw [Array.getElem?_setIfInBounds_ne he]
    exact hq

end Zig.Mem


/-!
Private source corollaries of AtomicArray.native.lean and WordRunFields.native.lean.
Each conclusion is a concrete ordered-array query of the actual primitive memory.
-/

namespace Zig.Conc.Word

open Proto Full

variable {n nb : Nat} {W : Word n nb}

/-- Valid-word preparation retains every existing first-address match, at its
original index with its complete original atomic record. -/
theorem prepare_first {m m' : Mem} {li : Nat} {k : AccessKind} (hw : W.Ok m)
    (hk : k.isAtomic = true)
    (h : ((locIdx W.b W.o nb).run (m.recordAt W.b W.o nb k)).run = some (.ok (li, m')))
    {b o i : Nat} {l : ALoc}
    (hf : m.atomics.findIdx? (fun a => a.block == b && a.off == o) = some i)
    (hi : m.atomics[i]? = some l) :
    m'.atomics.findIdx? (fun a => a.block == b && a.off == o) = some i ∧
      m'.atomics[i]? = some l := by
  have he := prepare_run_eq hw hk h
  cases hfind : m.atomics.findIdx? (fun a => a.block == W.b && a.off == W.o) with
  | some j =>
    rw [hfind] at he
    obtain ⟨_, hm⟩ := Prod.mk.inj he
    rw [hm]
    exact ⟨hf, hi⟩
  | none =>
    rw [hfind] at he
    obtain ⟨_, hm⟩ := Prod.mk.inj he
    rw [hm]
    exact Zig.Conc.first_push hf hi (firstLoc (m.recordAt W.b W.o nb k) W.b W.o nb)

end Zig.Conc.Word

namespace Zig.Conc.Proto

/-- A selected read retains every complete first-address record at its old index. -/
theorem loadM_first {m : Mem} {li : Nat} {ord : AtomicOrder} {msg : Msg}
    {b o i : Nat} {l : ALoc}
    (hf : m.atomics.findIdx? (fun a => a.block == b && a.off == o) = some i)
    (hi : m.atomics[i]? = some l) :
    (loadM m li ord msg).atomics.findIdx? (fun a => a.block == b && a.off == o) = some i ∧
      (loadM m li ord msg).atomics[i]? = some l := by
  rw [(loadM_fields (m := m) (li := li) (ord := ord) (msg := msg)).2]
  exact ⟨hf, hi⟩

/-- A newest-message RMW retains another address's complete first record at the
same index, without any premise about the queried location's width or validity. -/
theorem rmwM_first_ne {m : Mem} {li pos : Nat} {active : ALoc} {blk : Block} {n : Nat}
    (hl : m.atomics[li]? = some active) (hpos : pos + 1 = active.msgs.size)
    (hb : m.blocks[active.block]? = some blk) (ord : AtomicOrder) (rd : Msg) (new : BitVec n)
    {b o i : Nat} {saved : ALoc} (hne : active.block ≠ b ∨ active.off ≠ o)
    (hf : m.atomics.findIdx? (fun a => a.block == b && a.off == o) = some i)
    (hi : m.atomics[i]? = some saved) :
    (rmwM m li pos ord rd new).atomics.findIdx? (fun a => a.block == b && a.off == o) = some i ∧
      (rmwM m li pos ord rd new).atomics[i]? = some saved := by
  have hlt : li < m.atomics.size := (Array.getElem?_eq_some_iff.mp hl).1
  have hl0 : m.atomics[li]! = active := by
    rw [getElem!_pos m.atomics li hlt, (Array.getElem?_eq_some_iff.mp hl).2]
  let m₂ := if ord.isAcq then acqM m rd.relClock else m
  have ha₂ : m₂.atomics = m.atomics := by
    simp only [m₂]
    split <;> rfl
  rw [rmwM_last_eq hl0 hpos hb ord rd new]
  change (m₂.atomics.set! li {active with msgs := active.msgs.push (rmwMsg m₂ ord rd new)}).findIdx?
      (fun a => a.block == b && a.off == o) = some i ∧
    (m₂.atomics.set! li {active with msgs := active.msgs.push (rmwMsg m₂ ord rd new)})[i]? = some saved
  rw [ha₂]
  exact Zig.Conc.first_set_address_ne hl rfl rfl hne hf hi

/-- A newest-message RMW's actual bounded write preserves the required fields
of every old block, even if the queried block is dead. -/
theorem rmwM_block_fields {m : Mem} {li pos : Nat} {active : ALoc} {blk : Block} {n : Nat}
    (hl : m.atomics[li]! = active) (hpos : pos + 1 = active.msgs.size)
    (hb : m.blocks[active.block]? = some blk)
    (ord : AtomicOrder) (rd : Msg) (new : BitVec n)
    (hbound : active.off + (padTo (intSize n) (intBytes new)).size ≤ blk.bytes.size)
    {b : BlockId} {old : Block} (hlookup : m.blocks[b]? = some old) :
    ∃ next, (rmwM m li pos ord rd new).blocks[b]? = some next ∧
      next.live = old.live ∧ next.bytes.size = old.bytes.size ∧ next.kind = old.kind := by
  let m₂ := if ord.isAcq then acqM m rd.relClock else m
  have hb₂ : m₂.blocks = m.blocks := by
    simp only [m₂]
    split <;> rfl
  rw [rmwM_last_eq hl hpos hb ord rd new]
  change ∃ next, (m₂.blocks.set! active.block
      {blk with bytes := writeBytes blk.bytes active.off (rmwMsg m₂ ord rd new).bytes})[b]? =
        some next ∧ next.live = old.live ∧ next.bytes.size = old.bytes.size ∧ next.kind = old.kind
  rw [hb₂]
  exact Mem.write_block_fields hb
    (by simpa only [rmwMsg] using hbound) hlookup

end Zig.Conc.Proto


/-!
Private operation wrappers for WordRunFields.native.lean, AtomicArray.native.lean
and WordQueries.native.lean. Conclusions are raw block fields and the exact
existing LockWord.Loc, derived from actual primitive runs. No import is added.
-/

namespace Zig.Conc.Word

open Proto Full

variable {n nb : Nat} {W : Word n nb}

/-- Actual preparation retains the complete block array. -/
theorem prepare_blocks {m m' : Mem} {li : Nat} {k : AccessKind}
    (h : ((locIdx W.b W.o nb).run (m.recordAt W.b W.o nb k)).run = some (.ok (li, m'))) :
    m'.blocks = m.blocks := by
  obtain ⟨a, s, next, rfl⟩ := locIdx_updates h
  rfl

/-- The actual newest-message RMW has the required block fields at every old
lookup. The query itself has no liveness premise. -/
theorem rmwM_block {m : Mem} {li pos : Nat} {active : ALoc} {wordBlk : Block}
    (hl : W.Loc m li active) (hpos : pos + 1 = active.msgs.size)
    (hw : m.blocks[W.b]? = some wordBlk) (hsize : W.o + nb ≤ wordBlk.bytes.size)
    (ord : AtomicOrder) (rd : Msg) (new : BitVec n)
    {b : BlockId} {blk : Block} (hb : m.blocks[b]? = some blk) :
    ∃ blk', (rmwM m li pos ord rd new).blocks[b]? = some blk' ∧ blk'.live = blk.live ∧
      blk'.bytes.size = blk.bytes.size ∧ blk'.kind = blk.kind := by
  obtain ⟨hblock, hoff⟩ := loc_at hl
  exact Proto.rmwM_block_fields (loc_get hl).2.2 hpos
    (by rw [hblock]; exact hw) ord rd new
    (by rw [hoff, W.enc_size new]; exact hsize) hb

/-- The actual newest-message replacement leaves an apart lock's first record
at the same index, including its entire history and metadata. -/
theorem rmwM_lockLoc {m : Mem} {li pos : Nat} {active : ALoc} {wordBlk : Block}
    (hl : W.Loc m li active) (hpos : pos + 1 = active.msgs.size)
    (hw : m.blocks[W.b]? = some wordBlk) (ord : AtomicOrder) (rd : Msg) (new : BitVec n)
    {L : LockWord} (hap : W.ApartL L) {i : Nat} {l : ALoc} (hL : L.Loc m i l) :
    L.Loc (rmwM m li pos ord rd new) i l := by
  obtain ⟨hblock, hoff⟩ := loc_at hl
  have hne : active.block ≠ L.b ∨ active.off ≠ L.o := by
    rw [hblock, hoff]
    rcases hap.ne with hb | ho
    · exact .inl (Ne.symm hb)
    · exact .inr (Ne.symm ho)
  exact Proto.rmwM_first_ne hl.2 hpos (by rw [hblock]; exact hw)
    ord rd new hne hL.1 hL.2

/-- Every actual load preserves every old block's required fields. -/
theorem atomicLoad_block {m m' : Mem} {c : Nat} {ord : AtomicOrder} {v : BitVec n}
    (hw : W.Ok m)
    (h : ((atomicLoadAt c ord nb W.ptr).run m).run = some (.ok (v, m')))
    {b : BlockId} {blk : Block} (hb : m.blocks[b]? = some blk) :
    ∃ blk', m'.blocks[b]? = some blk' ∧ blk'.live = blk.live ∧
      blk'.bytes.size = blk.bytes.size ∧ blk'.kind = blk.kind := by
  obtain ⟨b₀, blk₀, o, li, m₁, pos, hacc, _, hp, _, _, rfl⟩ := atomicLoadAt_ok h
  obtain ⟨wordBlk, _, _, _, ha, _⟩ := hw.access
  rw [W.sz_eq, ha] at hacc
  rw [W.sz_eq] at hp
  cases hacc
  rw [(Proto.loadM_fields (m := m₁) (li := li) (ord := ord)
    (msg := (m₁.atomics[li]!).msgs[pos]!)).1, prepare_blocks (W := W) hp]
  exact ⟨blk, hb, rfl, rfl, rfl⟩

/-- Loads retain every old first-address record, even without an apartness
premise on the queried lock. -/
theorem atomicLoad_lockLoc {m m' : Mem} {c : Nat} {ord : AtomicOrder} {v : BitVec n}
    (hw : W.Ok m)
    (h : ((atomicLoadAt c ord nb W.ptr).run m).run = some (.ok (v, m')))
    {L : LockWord} {i : Nat} {l : ALoc} (hL : L.Loc m i l) : L.Loc m' i l := by
  obtain ⟨b₀, blk₀, o, li, m₁, pos, hacc, _, hp, _, _, rfl⟩ := atomicLoadAt_ok h
  obtain ⟨wordBlk, _, _, _, ha, _⟩ := hw.access
  rw [W.sz_eq, ha] at hacc
  rw [W.sz_eq] at hp
  cases hacc
  obtain ⟨hf, hi⟩ := prepare_first hw rfl hp hL.1 hL.2
  exact Proto.loadM_first (li := li) (ord := ord)
    (msg := (m₁.atomics[li]!).msgs[pos]!) hf hi

/-- An actual signed or unsigned RMW supplies arbitrary block preservation and
exact apart-lock location preservation from one preparation and newest-message proof. -/
theorem atomicRmw_block_lockLoc {m m' : Mem} {c : Nat} {op : RmwOp} {signed : Bool}
    {ord : AtomicOrder} {v old : BitVec n} (hw : W.Ok m)
    (h : ((atomicRmwAt c op signed ord nb W.ptr v).run m).run = some (.ok (old, m'))) :
    (∀ {b : BlockId} {blk : Block}, m.blocks[b]? = some blk →
      ∃ blk', m'.blocks[b]? = some blk' ∧ blk'.live = blk.live ∧
        blk'.bytes.size = blk.bytes.size ∧ blk'.kind = blk.kind) ∧
    (∀ {L : LockWord}, W.ApartL L → ∀ {i : Nat} {l : ALoc},
      L.Loc m i l → L.Loc m' i l) := by
  obtain ⟨b₀, blk₀, o, li, m₁, pos, hacc, _, hp, hr, _, rfl⟩ := atomicRmwAt_ok h
  obtain ⟨wordBlk, hword, _, hsize, _, ha⟩ := hw.access
  rw [W.sz_eq, ha] at hacc
  rw [W.sz_eq] at hp
  cases hacc
  obtain ⟨active, hl, _, h0, hchain, _⟩ := prepare hw rfl hp
  have hl0 := (loc_get hl).2.2
  have hpos : pos + 1 = active.msgs.size := by
    have he := rmw_chain_pos (by rwa [hl0]) (by rwa [hl0]) hr
    rw [hl0] at he
    omega
  have hblocks := prepare_blocks (W := W) hp
  have hword₁ := hword
  rw [← hblocks] at hword₁
  constructor
  · intro b blk hb
    exact rmwM_block (W := W) hl hpos hword₁ hsize ord
      ((m₁.atomics[li]!).msgs[pos]!) (op.apply signed old v)
      (by rw [hblocks]; exact hb)
  · intro L hap i l hL
    have hL₁ : L.Loc m₁ i l := prepare_first hw rfl hp hL.1 hL.2
    exact rmwM_lockLoc (W := W) hl hpos hword₁ ord
      ((m₁.atomics[li]!).msgs[pos]!) (op.apply signed old v) hap hL₁

/-- Every actual signed or unsigned RMW preserves every old block's required
fields through its actual bounded word write. -/
theorem atomicRmw_block {m m' : Mem} {c : Nat} {op : RmwOp} {signed : Bool}
    {ord : AtomicOrder} {v old : BitVec n} (hw : W.Ok m)
    (h : ((atomicRmwAt c op signed ord nb W.ptr v).run m).run = some (.ok (old, m')))
    {b : BlockId} {blk : Block} (hb : m.blocks[b]? = some blk) :
    ∃ blk', m'.blocks[b]? = some blk' ∧ blk'.live = blk.live ∧
      blk'.bytes.size = blk.bytes.size ∧ blk'.kind = blk.kind := by
  exact (atomicRmw_block_lockLoc hw h).1 hb

/-- Every actual signed or unsigned RMW retains an apart lock's exact old
first-address record and its original index. -/
theorem atomicRmw_lockLoc {m m' : Mem} {c : Nat} {op : RmwOp} {signed : Bool}
    {ord : AtomicOrder} {v old : BitVec n} (hw : W.Ok m)
    (h : ((atomicRmwAt c op signed ord nb W.ptr v).run m).run = some (.ok (old, m')))
    {L : LockWord} (hap : W.ApartL L) {i : Nat} {l : ALoc} (hL : L.Loc m i l) :
    L.Loc m' i l := by
  exact (atomicRmw_block_lockLoc hw h).2 hap hL

/-- Both strong-CAS branches supply block fields and exact apart-lock locations
from a single actual preparation and newest-message proof. -/
theorem cmpxchg_block_lockLoc {m m' : Mem} {c : Nat} {succ fail : AtomicOrder}
    {expected new : BitVec n} {r : Option (BitVec n)} (hw : W.Ok m)
    (h : ((cmpxchgAt c succ fail nb W.ptr expected new).run m).run = some (.ok (r, m'))) :
    (∀ {b : BlockId} {blk : Block}, m.blocks[b]? = some blk →
      ∃ blk', m'.blocks[b]? = some blk' ∧ blk'.live = blk.live ∧
        blk'.bytes.size = blk.bytes.size ∧ blk'.kind = blk.kind) ∧
    (∀ {L : LockWord}, W.ApartL L → ∀ {i : Nat} {l : ALoc},
      L.Loc m i l → L.Loc m' i l) := by
  obtain ⟨b₀, blk₀, o, li, m₁, pos, old, hacc, _, hp, hr, hv, hcase⟩ := cmpxchgAt_ok h
  obtain ⟨wordBlk, hword, _, hsize, _, ha⟩ := hw.access
  rw [W.sz_eq, ha] at hacc
  rw [W.sz_eq] at hp
  cases hacc
  obtain ⟨active, hl, _, h0, hchain, _⟩ := prepare hw rfl hp
  have hblocks := prepare_blocks (W := W) hp
  have hword₁ := hword
  rw [← hblocks] at hword₁
  have hfirst {L : LockWord} {i : Nat} {l : ALoc} (hL : L.Loc m i l) :
      L.Loc m₁ i l := prepare_first hw rfl hp hL.1 hL.2
  rcases hcase with ⟨rfl, _, _, rfl⟩ | ⟨_, _, rfl⟩
  · have hl0 := (loc_get hl).2.2
    have hpos : pos + 1 = active.msgs.size := by
      have he := cas_chain_pos (by rwa [hl0]) hr hv
      rw [hl0] at he
      omega
    have hlr : W.Loc (m₁.recordAt W.b W.o nb .atomicWrite) li active := hl
    constructor
    · intro b blk hb
      rw [W.sz_eq]
      exact rmwM_block (W := W) hlr hpos hword₁ hsize succ
        ((m₁.atomics[li]!).msgs[pos]!) new
        (by change m₁.blocks[b]? = _; rw [hblocks]; exact hb)
    · intro L hap i l hL
      rw [W.sz_eq]
      exact rmwM_lockLoc (W := W) hlr hpos hword₁
        succ ((m₁.atomics[li]!).msgs[pos]!) new hap (hfirst hL)
  · constructor
    · intro b blk hb
      rw [(Proto.loadM_fields (m := m₁) (li := li) (ord := fail)
        (msg := (m₁.atomics[li]!).msgs[pos]!)).1, hblocks]
      exact ⟨blk, hb, rfl, rfl, rfl⟩
    · intro L hap i l hL
      exact Proto.loadM_first (li := li) (ord := fail)
        (msg := (m₁.atomics[li]!).msgs[pos]!) (hfirst hL).1 (hfirst hL).2

/-- Strong CAS preserves arbitrary old block fields in both its actual branches. -/
theorem cmpxchg_block {m m' : Mem} {c : Nat} {succ fail : AtomicOrder}
    {expected new : BitVec n} {r : Option (BitVec n)} (hw : W.Ok m)
    (h : ((cmpxchgAt c succ fail nb W.ptr expected new).run m).run = some (.ok (r, m')))
    {b : BlockId} {blk : Block} (hb : m.blocks[b]? = some blk) :
    ∃ blk', m'.blocks[b]? = some blk' ∧ blk'.live = blk.live ∧
      blk'.bytes.size = blk.bytes.size ∧ blk'.kind = blk.kind := by
  exact (cmpxchg_block_lockLoc hw h).1 hb

/-- Strong CAS retains an apart lock's exact old first-address record in its
newest-message success and failure-order read branches. -/
theorem cmpxchg_lockLoc {m m' : Mem} {c : Nat} {succ fail : AtomicOrder}
    {expected new : BitVec n} {r : Option (BitVec n)} (hw : W.Ok m)
    (h : ((cmpxchgAt c succ fail nb W.ptr expected new).run m).run = some (.ok (r, m')))
    {L : LockWord} (hap : W.ApartL L) {i : Nat} {l : ALoc} (hL : L.Loc m i l) :
    L.Loc m' i l := by
  exact (cmpxchg_block_lockLoc hw h).2 hap hL

/-- Weak-CAS success, mismatch and matching-value spurious failure share the
same preparation proof for block fields and exact apart-lock locations. -/
theorem cmpxchgWeak_block_lockLoc {m m' : Mem} {c : Nat} {succ fail : AtomicOrder}
    {expected new : BitVec n} {r : Option (BitVec n)} (hw : W.Ok m)
    (h : ((cmpxchgWeakAt c succ fail nb W.ptr expected new).run m).run = some (.ok (r, m'))) :
    (∀ {b : BlockId} {blk : Block}, m.blocks[b]? = some blk →
      ∃ blk', m'.blocks[b]? = some blk' ∧ blk'.live = blk.live ∧
        blk'.bytes.size = blk.bytes.size ∧ blk'.kind = blk.kind) ∧
    (∀ {L : LockWord}, W.ApartL L → ∀ {i : Nat} {l : ALoc},
      L.Loc m i l → L.Loc m' i l) := by
  obtain ⟨b₀, blk₀, o, li, m₁, pos, spurious, old, hacc, _, hp, hr, hv, hcase⟩ := cmpxchgWeakAt_ok h
  obtain ⟨wordBlk, hword, _, hsize, _, ha⟩ := hw.access
  rw [W.sz_eq, ha] at hacc
  rw [W.sz_eq] at hp
  cases hacc
  obtain ⟨active, hl, _, h0, hchain, _⟩ := prepare hw rfl hp
  have hblocks := prepare_blocks (W := W) hp
  have hword₁ := hword
  rw [← hblocks] at hword₁
  have hfirst {L : LockWord} {i : Nat} {l : ALoc} (hL : L.Loc m i l) :
      L.Loc m₁ i l := prepare_first hw rfl hp hL.1 hL.2
  rcases hcase with ⟨rfl, rfl, _, _, rfl⟩ | ⟨_, _, rfl⟩
  · obtain ⟨j, hj⟩ := weakCasOpts_strong hr
    have hl0 := (loc_get hl).2.2
    have hpos : pos + 1 = active.msgs.size := by
      have he := cas_chain_pos (by rwa [hl0]) hj hv
      rw [hl0] at he
      omega
    have hlr : W.Loc (m₁.recordAt W.b W.o nb .atomicWrite) li active := hl
    constructor
    · intro b blk hb
      rw [W.sz_eq]
      exact rmwM_block (W := W) hlr hpos hword₁ hsize succ
        ((m₁.atomics[li]!).msgs[pos]!) new
        (by change m₁.blocks[b]? = _; rw [hblocks]; exact hb)
    · intro L hap i l hL
      rw [W.sz_eq]
      exact rmwM_lockLoc (W := W) hlr hpos hword₁
        succ ((m₁.atomics[li]!).msgs[pos]!) new hap (hfirst hL)
  · constructor
    · intro b blk hb
      rw [(Proto.loadM_fields (m := m₁) (li := li) (ord := fail)
        (msg := (m₁.atomics[li]!).msgs[pos]!)).1, hblocks]
      exact ⟨blk, hb, rfl, rfl, rfl⟩
    · intro L hap i l hL
      exact Proto.loadM_first (li := li) (ord := fail)
        (msg := (m₁.atomics[li]!).msgs[pos]!) (hfirst hL).1 (hfirst hL).2

/-- Weak-CAS block preservation includes matching-value spurious failures. -/
theorem cmpxchgWeak_block {m m' : Mem} {c : Nat} {succ fail : AtomicOrder}
    {expected new : BitVec n} {r : Option (BitVec n)} (hw : W.Ok m)
    (h : ((cmpxchgWeakAt c succ fail nb W.ptr expected new).run m).run = some (.ok (r, m')))
    {b : BlockId} {blk : Block} (hb : m.blocks[b]? = some blk) :
    ∃ blk', m'.blocks[b]? = some blk' ∧ blk'.live = blk.live ∧
      blk'.bytes.size = blk.bytes.size ∧ blk'.kind = blk.kind := by
  exact (cmpxchgWeak_block_lockLoc hw h).1 hb

/-- Weak CAS retains the same complete apart record at the same index on
success, mismatch and matching-value spurious failure. -/
theorem cmpxchgWeak_lockLoc {m m' : Mem} {c : Nat} {succ fail : AtomicOrder}
    {expected new : BitVec n} {r : Option (BitVec n)} (hw : W.Ok m)
    (h : ((cmpxchgWeakAt c succ fail nb W.ptr expected new).run m).run = some (.ok (r, m')))
    {L : LockWord} (hap : W.ApartL L) {i : Nat} {l : ALoc} (hL : L.Loc m i l) :
    L.Loc m' i l := by
  exact (cmpxchgWeak_block_lockLoc hw h).2 hap hL

end Zig.Conc.Word


namespace Zig.Conc.Proto

theorem loadM_footprint (m : Mem) (li : Nat) (ord : AtomicOrder) (msg : Msg) :
    (loadM m li ord msg).footprint = m.footprint := by
  unfold loadM
  dsimp only
  split <;> rfl

theorem insertM_footprint (m : Mem) (li pos : Nat) (msg : Msg) :
    (insertM m li pos msg).footprint = m.footprint := by
  unfold insertM
  dsimp only
  split
  · split <;> rfl
  · rfl

theorem rmwM_footprint {n : Nat} (m : Mem) (li pos : Nat) (ord : AtomicOrder)
    (rd : Msg) (new : BitVec n) : (rmwM m li pos ord rd new).footprint = m.footprint := by
  cases hq : ord.isAcq
  · simpa only [rmwM, hq, Bool.false_eq_true, ↓reduceIte, observeM, acqM] using
      insertM_footprint m li (pos + 1) (rmwMsg m ord rd new)
  · simpa only [rmwM, hq, Bool.false_eq_true, ↓reduceIte, observeM, acqM] using
      insertM_footprint (acqM m rd.relClock) li (pos + 1)
        (rmwMsg (acqM m rd.relClock) ord rd new)

end Zig.Conc.Proto

namespace Zig.Conc.Word

open Proto

variable {n nb : Nat} {W : Word n nb}

/-- The actual recorded access has the exact word address, not just a subrange. -/
theorem record_fpAt {m : Mem} {k : AccessKind} {e : FootprintEntry}
    (he : e ∈ (m.recordAt W.b W.o nb k).footprint) :
    e ∈ m.footprint ∨ (e.block = W.b ∧ e.off = W.o) := by
  simp only [Mem.recordAt, Array.mem_push] at he
  rcases he with he | rfl
  · exact .inl he
  · exact .inr ⟨rfl, rfl⟩

/-- Location preparation changes no footprint entry after the recorded access. -/
theorem prepare_fpAt {m m' : Mem} {li : Nat} {k : AccessKind} {e : FootprintEntry}
    (h : ((locIdx W.b W.o nb).run (m.recordAt W.b W.o nb k)).run = some (.ok (li, m')))
    (he : e ∈ m'.footprint) : e ∈ m.footprint ∨ (e.block = W.b ∧ e.off = W.o) := by
  obtain ⟨a, s, next, rfl⟩ := locIdx_updates h
  exact record_fpAt he

theorem atomicLoad_fpAt {m m' : Mem} {c : Nat} {ord : AtomicOrder} {v : BitVec n}
    (hw : W.Ok m)
    (h : ((atomicLoadAt c ord nb W.ptr).run m).run = some (.ok (v, m')))
    {e : FootprintEntry} (he : e ∈ m'.footprint) :
    e ∈ m.footprint ∨ (e.block = W.b ∧ e.off = W.o) := by
  obtain ⟨b, blk, o, li, m₁, pos, hacc, _, hp, _, _, rfl⟩ := atomicLoadAt_ok h
  obtain ⟨blk₀, _, _, _, ha, _⟩ := hw.access
  rw [W.sz_eq, ha] at hacc
  rw [W.sz_eq] at hp
  cases hacc
  rw [loadM_footprint] at he
  exact prepare_fpAt hp he

theorem atomicRmw_fpAt {m m' : Mem} {c : Nat} {op : RmwOp} {signed : Bool}
    {ord : AtomicOrder} {v old : BitVec n} (hw : W.Ok m)
    (h : ((atomicRmwAt c op signed ord nb W.ptr v).run m).run = some (.ok (old, m')))
    {e : FootprintEntry} (he : e ∈ m'.footprint) :
    e ∈ m.footprint ∨ (e.block = W.b ∧ e.off = W.o) := by
  obtain ⟨b, blk, o, li, m₁, pos, hacc, _, hp, _, _, rfl⟩ := atomicRmwAt_ok h
  obtain ⟨blk₀, _, _, _, _, ha⟩ := hw.access
  rw [W.sz_eq, ha] at hacc
  rw [W.sz_eq] at hp
  cases hacc
  rw [rmwM_footprint] at he
  exact prepare_fpAt hp he

theorem cmpxchg_fpAt {m m' : Mem} {c : Nat} {succ fail : AtomicOrder}
    {expected new : BitVec n} {r : Option (BitVec n)} (hw : W.Ok m)
    (h : ((cmpxchgAt c succ fail nb W.ptr expected new).run m).run = some (.ok (r, m')))
    {e : FootprintEntry} (he : e ∈ m'.footprint) :
    e ∈ m.footprint ∨ (e.block = W.b ∧ e.off = W.o) := by
  obtain ⟨b, blk, o, li, m₁, pos, old, hacc, _, hp, _, _, hcase⟩ := cmpxchgAt_ok h
  obtain ⟨blk₀, _, _, _, _, ha⟩ := hw.access
  rw [W.sz_eq, ha] at hacc
  rw [W.sz_eq] at hp
  cases hacc
  rcases hcase with ⟨_, _, _, hm⟩ | ⟨_, _, hm⟩
  · rw [hm, rmwM_footprint, W.sz_eq] at he
    rcases record_fpAt (W := W) he with he | he
    · exact prepare_fpAt hp he
    · exact .inr he
  · rw [hm, loadM_footprint] at he
    exact prepare_fpAt hp he

/-- A matching-value spurious weak failure is still the actual failure-order read. -/
theorem cmpxchgWeak_fpAt {m m' : Mem} {c : Nat} {succ fail : AtomicOrder}
    {expected new : BitVec n} {r : Option (BitVec n)} (hw : W.Ok m)
    (h : ((cmpxchgWeakAt c succ fail nb W.ptr expected new).run m).run = some (.ok (r, m')))
    {e : FootprintEntry} (he : e ∈ m'.footprint) :
    e ∈ m.footprint ∨ (e.block = W.b ∧ e.off = W.o) := by
  obtain ⟨b, blk, o, li, m₁, pos, spurious, old, hacc, _, hp, _, _, hcase⟩ :=
    cmpxchgWeakAt_ok h
  obtain ⟨blk₀, _, _, _, _, ha⟩ := hw.access
  rw [W.sz_eq, ha] at hacc
  rw [W.sz_eq] at hp
  cases hacc
  rcases hcase with ⟨_, _, _, _, hm⟩ | ⟨_, _, hm⟩
  · rw [hm, rmwM_footprint, W.sz_eq] at he
    rcases record_fpAt (W := W) he with he | he
    · exact prepare_fpAt hp he
    · exact .inr he
  · rw [hm, loadM_footprint] at he
    exact prepare_fpAt hp he

/-- Every actual primitive run at a valid word preserves the resource rest.
The alternatives include all widths, orders, signedness and strong/weak CAS results. -/
theorem actualRun_rest {m m' : Mem} (hw : W.Ok m)
    (hc : m.current < m.clocks.size)
    (hop :
      (∃ (c : Nat) (ord : AtomicOrder) (v : BitVec n),
        ((atomicLoadAt c ord nb W.ptr).run m).run = some (.ok (v, m'))) ∨
      (∃ (c : Nat) (op : RmwOp) (signed : Bool) (ord : AtomicOrder)
          (v old : BitVec n),
        ((atomicRmwAt c op signed ord nb W.ptr v).run m).run =
          some (.ok (old, m'))) ∨
      (∃ (c : Nat) (succ fail : AtomicOrder) (expected new : BitVec n)
          (r : Option (BitVec n)),
        ((cmpxchgAt c succ fail nb W.ptr expected new).run m).run =
          some (.ok (r, m'))) ∨
      (∃ (c : Nat) (succ fail : AtomicOrder) (expected new : BitVec n)
          (r : Option (BitVec n)),
        ((cmpxchgWeakAt c succ fail nb W.ptr expected new).run m).run =
          some (.ok (r, m'))) ∨
      m' = m.recordAt W.b W.o nb .atomicRead) :
    Full.RestStep W.In m m' := by
  rcases hop with ⟨c, ord, v, hr⟩ | ⟨c, op, signed, ord, v, old, hr⟩ |
    ⟨c, succ, fail, expected, new, r, hr⟩ |
    ⟨c, succ, fail, expected, new, r, hr⟩ | hr
  · exact atomicLoad_rest hw hc hr
  · exact atomicRmw_rest hw hc hr
  · exact cmpxchg_rest hw hc hr
  · exact cmpxchgWeak_rest hw hc hr
  · rw [hr]
    exact record_rest (k := .atomicRead) hw hc

/-- A new footprint entry of any actual primitive run is at the exact word address. -/
theorem actualRun_fpAt {m m' : Mem} (hw : W.Ok m)
    (hop :
      (∃ (c : Nat) (ord : AtomicOrder) (v : BitVec n),
        ((atomicLoadAt c ord nb W.ptr).run m).run = some (.ok (v, m'))) ∨
      (∃ (c : Nat) (op : RmwOp) (signed : Bool) (ord : AtomicOrder)
          (v old : BitVec n),
        ((atomicRmwAt c op signed ord nb W.ptr v).run m).run =
          some (.ok (old, m'))) ∨
      (∃ (c : Nat) (succ fail : AtomicOrder) (expected new : BitVec n)
          (r : Option (BitVec n)),
        ((cmpxchgAt c succ fail nb W.ptr expected new).run m).run =
          some (.ok (r, m'))) ∨
      (∃ (c : Nat) (succ fail : AtomicOrder) (expected new : BitVec n)
          (r : Option (BitVec n)),
        ((cmpxchgWeakAt c succ fail nb W.ptr expected new).run m).run =
          some (.ok (r, m'))) ∨
      m' = m.recordAt W.b W.o nb .atomicRead)
    {e : FootprintEntry} (he : e ∈ m'.footprint) :
    e ∈ m.footprint ∨ (e.block = W.b ∧ e.off = W.o) := by
  rcases hop with ⟨c, ord, v, hr⟩ | ⟨c, op, signed, ord, v, old, hr⟩ |
    ⟨c, succ, fail, expected, new, r, hr⟩ |
    ⟨c, succ, fail, expected, new, r, hr⟩ | hr
  · exact atomicLoad_fpAt hw hr he
  · exact atomicRmw_fpAt hw hr he
  · exact cmpxchg_fpAt hw hr he
  · exact cmpxchgWeak_fpAt hw hr he
  · rw [hr] at he
    exact record_fpAt (W := W) he

/-- Every actual primitive run preserves each old block's live flag, byte-array
size and kind. The queried block need not be live. -/
theorem actualRun_block {m m' : Mem} (hw : W.Ok m)
    (hop :
      (∃ (c : Nat) (ord : AtomicOrder) (v : BitVec n),
        ((atomicLoadAt c ord nb W.ptr).run m).run = some (.ok (v, m'))) ∨
      (∃ (c : Nat) (op : RmwOp) (signed : Bool) (ord : AtomicOrder)
          (v old : BitVec n),
        ((atomicRmwAt c op signed ord nb W.ptr v).run m).run =
          some (.ok (old, m'))) ∨
      (∃ (c : Nat) (succ fail : AtomicOrder) (expected new : BitVec n)
          (r : Option (BitVec n)),
        ((cmpxchgAt c succ fail nb W.ptr expected new).run m).run =
          some (.ok (r, m'))) ∨
      (∃ (c : Nat) (succ fail : AtomicOrder) (expected new : BitVec n)
          (r : Option (BitVec n)),
        ((cmpxchgWeakAt c succ fail nb W.ptr expected new).run m).run =
          some (.ok (r, m'))) ∨
      m' = m.recordAt W.b W.o nb .atomicRead)
    {b : BlockId} {blk : Block} (hb : m.blocks[b]? = some blk) :
    ∃ blk', m'.blocks[b]? = some blk' ∧ blk'.live = blk.live ∧
      blk'.bytes.size = blk.bytes.size ∧ blk'.kind = blk.kind := by
  rcases hop with ⟨c, ord, v, hr⟩ | ⟨c, op, signed, ord, v, old, hr⟩ |
    ⟨c, succ, fail, expected, new, r, hr⟩ |
    ⟨c, succ, fail, expected, new, r, hr⟩ | hr
  · exact atomicLoad_block hw hr hb
  · exact atomicRmw_block hw hr hb
  · exact cmpxchg_block hw hr hb
  · exact cmpxchgWeak_block hw hr hb
  · rw [hr]
    exact ⟨blk, hb, rfl, rfl, rfl⟩

/-- Every actual primitive run retains an apart lock's complete first-address
record at the same index, including all history and metadata. -/
theorem actualRun_lockLoc {m m' : Mem} (hw : W.Ok m)
    (hop :
      (∃ (c : Nat) (ord : AtomicOrder) (v : BitVec n),
        ((atomicLoadAt c ord nb W.ptr).run m).run = some (.ok (v, m'))) ∨
      (∃ (c : Nat) (op : RmwOp) (signed : Bool) (ord : AtomicOrder)
          (v old : BitVec n),
        ((atomicRmwAt c op signed ord nb W.ptr v).run m).run =
          some (.ok (old, m'))) ∨
      (∃ (c : Nat) (succ fail : AtomicOrder) (expected new : BitVec n)
          (r : Option (BitVec n)),
        ((cmpxchgAt c succ fail nb W.ptr expected new).run m).run =
          some (.ok (r, m'))) ∨
      (∃ (c : Nat) (succ fail : AtomicOrder) (expected new : BitVec n)
          (r : Option (BitVec n)),
        ((cmpxchgWeakAt c succ fail nb W.ptr expected new).run m).run =
          some (.ok (r, m'))) ∨
      m' = m.recordAt W.b W.o nb .atomicRead)
    {L : Full.LockWord} (hap : W.ApartL L) {i : Nat} {l : ALoc} (hl : L.Loc m i l) :
    L.Loc m' i l := by
  rcases hop with ⟨c, ord, v, hr⟩ | ⟨c, op, signed, ord, v, old, hr⟩ |
    ⟨c, succ, fail, expected, new, r, hr⟩ |
    ⟨c, succ, fail, expected, new, r, hr⟩ | hr
  · exact atomicLoad_lockLoc hw hr hl
  · exact atomicRmw_lockLoc hw hr hap hl
  · exact cmpxchg_lockLoc hw hr hap hl
  · exact cmpxchgWeak_lockLoc hw hr hap hl
  · rw [hr]
    exact hl

end Zig.Conc.Word


namespace Zig.Conc.Word

open Full Proto

variable {n nb : Nat} {W : Word n nb}


/-- Native framing preserves every valid apart word and its exact history.
The caller supplies native steps for all frames disjoint from the active word,
and the actual resource step supplies unchanged cells outside that word. -/
theorem preserve_apart {n' nb' : Nat} {V : Word n' nb'} {m m' : Mem}
    (hv : V.Ok m)
    (hs : ∀ hF : Heap,
      (∀ x, W.o ≤ x → x < W.o + nb → hF (W.b, x) = none) → FStepIn hF m m')
    (hcells : ∀ l, ¬ W.In l → m'.heap l = m.heap l)
    (hap : W.b ≠ V.b ∨ W.o + nb ≤ V.o ∨ V.o + nb' ≤ W.o) :
    V.Ok m' ∧ V.hist m' = V.hist m := by
  have hd : ∀ l, V.In l → ¬ W.In l := by
    rintro ⟨b, x⟩ ⟨hbV, hV₁, hV₂⟩ ⟨hbW, hW₁, hW₂⟩
    change b = V.b at hbV
    change b = W.b at hbW
    rcases hap with h | h | h
    · exact h (hbW.symm.trans hbV)
    · omega
    · omega
  let hF : Heap := fun l => if V.In l then m.heap l else none
  have hoff : ∀ x, W.o ≤ x → x < W.o + nb → hF (W.b, x) = none := by
    intro x h₁ h₂
    have hn : ¬ V.In (W.b, x) := fun h => hd (W.b, x) h ⟨rfl, h₁, h₂⟩
    change (if V.In (W.b, x) then m.heap (W.b, x) else none) = none
    exact if_neg hn
  have hcover : ∀ l, V.In l → hF l ≠ none := by
    intro l hl
    change (if V.In l then m.heap l else none) ≠ none
    rw [if_pos hl]
    exact hv.cellIn hl
  have hnorm : ∀ l, V.In l →
      (m'.heap l).map Cell.norm = (m.heap l).map Cell.norm := by
    intro l hl
    rw [hcells l (hd l hl)]
  have hs₀ := hs hF hoff
  exact ⟨hv.fstep hs₀ hcover hnorm, hist_fstep hv hs₀ hcover hnorm⟩

end Zig.Conc.Word


namespace Zig
namespace Conc
namespace Word
open Proto

section futex_native

variable {W : Word 32 4}

/-- A completed scheduler futex wait either consumes a pending wake or performs the actual
recorded atomic read. Only a matching value sleeps; the read preserves validity and history. -/
theorem Ok.futexWait_native {m m' : Mem} {t : ThreadId} {e : BitVec 32} {b : Bool} (hw : W.Ok m)
    (hc : m.current = t) (ht : t < m.threads.size) (hcs : m.clocks.size = m.threads.size)
    (h : ((Thread.futexWait W.ptr e).run m).run = some (.ok (b, m'))) :
    (m.woken.contains m.current = true ∧ b = false ∧
      m' = { m with woken := m.woken.erase m.current }) ∨
    (m.woken.contains m.current = false ∧ ∃ M, W.Ok M ∧
      M = m.recordAt W.b W.o 4 .atomicRead ∧ W.hist M = W.hist m ∧
      M.blocks = m.blocks ∧
      ((W.Holds m e ∧ b = true ∧ m' = { M with waiters := M.waiters.push (t, W.ptr) }) ∨
       (b = false ∧ m' = M))) := by
  rcases futexWait_eq h with hwk | ⟨hwk, bid, blk, o, v, ha, _, hv, hcase⟩
  · exact .inl hwk
  obtain ⟨blk₀, hb₀, _, _, ha₀, _⟩ := hw.access
  rw [ha₀] at ha
  cases ha
  obtain ⟨hok, hh⟩ := hw.record_native (k := .atomicRead) hc ht hcs rfl
  refine .inr ⟨hwk, _, hok, rfl, hh, rfl, ?_⟩
  rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨_, rfl, rfl⟩
  · subst hc
    exact .inl ⟨(holds_bytes hb₀).mpr hv, rfl, rfl⟩
  · exact .inr ⟨rfl, rfl⟩

end futex_native

end Word
end Conc
end Zig
