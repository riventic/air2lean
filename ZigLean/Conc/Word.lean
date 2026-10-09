import ZigLean.Conc.LockRules

/-!
# A shared atomic word

A word of a sync object that no thread owns: the state and the epoch of an `Io.Condition`, the
state of an `Io.Event`. It is 4 or 8 bytes (`n` = 32 or 64 bits) at offset `o` of block `b`, and each thread accesses it
only with atomic ops (translated std code; the futex under it is the model). A lock's word owns a
resource (`ZigLean/Conc/Lock.lean`); a shared word owns nothing, so a proof keeps facts about its
values and clocks in the rest of its invariant.

- **The writes** (`Word.hist`): the messages of the word's atomic location, oldest first, without
  their ids; before the first atomic op, the block's bytes. The first entry has no clock: a
  thread can always read it or a newer one.
- **The invariant** (`Word.Ok`): the block is live and aligned, no other atomic location overlaps
  the word, the location is an RMW chain of messages of the word's size whose newest has the word's bytes,
  and each access to the word is atomic or happened before every thread. So an atomic op at the
  word does not race, and an RMW reads the newest message.
- **Steps that keep the word** (`Word.Keep`): the same cells and location, and no new access to
  the word. A step of the lock's code (`keep_lockStep`), a step of a thread on its own part
  (`keep_stepIn`), a spawn, a join, a plain read and an op at another word (`keep_op`) keep each
  word that the step does not touch, with the same writes (`hist_keep`).
- **The ops** (`Word.Op`): a load (`Ok.load`) reads write `j`, at least each write that happened
  before the thread (`Word.Floor`); an RMW (`Ok.rmw`) reads the newest write and adds one
  (`rmwEnt`); a `cmpxchg` (`Ok.cas`) is an RMW of the newest write or a read of write `j`. In
  strict mode no op throws (`Ok.load_noErr`, `Ok.rmw_noErr`, `Ok.cas_noErr`). An op at a word
  keeps a lock's invariant (`Lock.Inv.wordOp`).
-/

namespace Zig
namespace Conc

open Assn Proto

/-- A word of `n` bits and `nb` bytes (`32` and `4`, or `64` and `8`) at offset `o` of block `b`. -/
structure Word (n nb : Nat) where
  b : BlockId
  o : Nat
  n_ok : (n = 32 ∧ nb = 4) ∨ (n = 64 ∧ nb = 8) := by decide
  deriving DecidableEq

namespace Word

variable {n nb : Nat} (W : Word n nb)

/-- The address of the word. -/
def ptr : Ptr := ⟨some W.b, (W.o : Int)⟩

include W in
theorem sz_eq : intSize n = nb := by
  rcases W.n_ok with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

include W in
theorem sz_pos : 0 < nb := by rcases W.n_ok with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide

include W in
theorem n_cases : n = 32 ∨ n = 64 := by rcases W.n_ok with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]

theorem enc_ok32_64 : ∀ w, w = 32 ∨ w = 64 → ∀ v : BitVec w,
    (intOfBytes w (padTo (intSize w) (intBytes v))).run = some (.ok v) ∧
      (padTo (intSize w) (intBytes v)).size = intSize w := by
  rintro w (rfl | rfl) v
  · exact ⟨intOfBytes_rmw v, LawfulEnc.size_encode (α := BitVec 32) v⟩
  · exact ⟨intOfBytes_rmw v, LawfulEnc.size_encode (α := BitVec 64) v⟩

include W in
/-- The bytes that an RMW writes hold its value. -/
theorem enc_val (v : BitVec n) :
    (intOfBytes n (padTo (intSize n) (intBytes v))).run = some (.ok v) :=
  (enc_ok32_64 n W.n_cases v).1

include W in
theorem enc_size (v : BitVec n) : (padTo (intSize n) (intBytes v)).size = nb := by
  rw [(enc_ok32_64 n W.n_cases v).2, W.sz_eq]

/-- The word's atomic location is location `i`, `l`. -/
def Loc (m : Mem) (i : Nat) (l : ALoc) : Prop :=
  m.atomics.findIdx? (fun l => l.block == W.b && l.off == W.o) = some i ∧ m.atomics[i]? = some l

/-- The access `e` touches a byte of the word. -/
def Hits (e : FootprintEntry) : Prop :=
  e.block = W.b ∧ ∃ x, e.off ≤ x ∧ (x < e.off + e.len ∨ x = e.off) ∧ W.o ≤ x ∧ x < W.o + nb

/-- `h` has no byte of the word. -/
def Off (h : Heap) : Prop := ∀ x, W.o ≤ x → x < W.o + nb → h (W.b, x) = none

/-- A write of the word: its bytes, its clock, its release clock and its writer (`Msg.writer`). -/
structure Entry where
  bytes : Array Byte
  clock : VClock
  relClock : VClock
  writer : Option ThreadId
  deriving Inhabited

/-- Message `j` without its id; the first one without its clock. -/
def ent (j : Nat) (x : Msg) : Entry := ⟨x.bytes, if j = 0 then #[] else x.clock, x.relClock, x.writer⟩

/-- The writes of the word, oldest first (module doc). -/
def hist (m : Mem) : Array Entry :=
  match m.atomics.findIdx? (fun l => l.block == W.b && l.off == W.o) with
  | some i => (m.atomics[i]!).msgs.mapIdx ent
  | none => #[⟨curBytes m W.b W.o nb, #[], #[], none⟩]

/-- The value of a write. -/
def Entry.Val {n : Nat} (x : Entry) (v : BitVec n) : Prop := (intOfBytes n x.bytes).run = some (.ok v)

/-- The word holds `v`. -/
def Holds (m : Mem) (v : BitVec n) : Prop :=
  (intOfBytes n (curBytes m W.b W.o nb)).run = some (.ok v)

/-- The word is shared and atomic only (module doc). -/
structure Ok (m : Mem) : Prop where
  blk : ∃ blk, m.blocks[W.b]? = some blk ∧ blk.live = true ∧ W.o + nb ≤ blk.bytes.size ∧
    (blk.addr + W.o) % nb = 0 ∧ blk.kind ≠ .constGlobal
  only : ∀ l ∈ m.atomics, l.block = W.b → l.off < W.o + nb → W.o < l.off + l.len → l.off = W.o
  loc : ∀ i l, W.Loc m i l → l.len = nb ∧ 0 < l.msgs.size ∧ l.Chain ∧
    ALoc.lastBytes l = curBytes m W.b W.o nb ∧
    ∀ j (h : j < l.msgs.size), ∃ v, (intOfBytes n l.msgs[j].bytes).run = some (.ok v)
  wfp : ∀ e ∈ m.footprint, W.Hits e →
    (e.kind.isAtomic = true ∧ SomeLe m e.clock) ∨ AllLe m e.clock
  /-- The word holds a value. -/
  val : ∃ v, W.Holds m v
  /-- Every plain write to the word happened before its newest message. -/
  plain : ∀ i l, W.Loc m i l → PlainLe m W.b W.o nb l.lastClock

/-- A step that keeps the word (module doc): the clocks of the threads do not get smaller (a
new thread's clock is above another one's). -/
structure Keep (m m' : Mem) : Prop where
  cells : ∀ x, W.o ≤ x → x < W.o + nb → m'.heap (W.b, x) = m.heap (W.b, x)
  loc : ∀ i l, W.Loc m' i l ↔ W.Loc m i l
  only : ∀ l ∈ m'.atomics, l ∈ m.atomics ∨ l.block ≠ W.b ∨ l.off + l.len ≤ W.o ∨ W.o + nb ≤ l.off
  fp : ∀ e ∈ m'.footprint, e ∈ m.footprint ∨ ¬ W.Hits e
  all : ∀ c, AllLe m c → AllLe m' c
  some : ∀ c, SomeLe m c → SomeLe m' c

variable {W}

/-! ## Basic facts -/

/-- The same cells at the word: the same facts of its block, and the same bytes. -/
theorem congr {m m' : Mem}
    (hw : ∀ x, W.o ≤ x → x < W.o + nb → m'.heap (W.b, x) = m.heap (W.b, x))
    (hb : ∃ blk, m.blocks[W.b]? = some blk ∧ blk.live = true ∧ W.o + nb ≤ blk.bytes.size ∧
      (blk.addr + W.o) % nb = 0 ∧ blk.kind ≠ .constGlobal) :
    (∃ blk, m'.blocks[W.b]? = some blk ∧ blk.live = true ∧ W.o + nb ≤ blk.bytes.size ∧
      (blk.addr + W.o) % nb = 0 ∧ blk.kind ≠ .constGlobal) ∧
      curBytes m' W.b W.o nb = curBytes m W.b W.o nb := by
  have hsz0 := W.sz_pos
  obtain ⟨blk, hblk, hl, hs, ha, hk⟩ := hb
  have hc : m.heap (W.b, W.o) =
      some ⟨blk.bytes[W.o]'(by omega), blk.addr, blk.bytes.size, blk.kind⟩ := by
    simp only [Mem.heap, hblk]; rw [dite_eq_left_of_eq_true (eq_true ⟨hl, by omega⟩)]
  have hc' := hw W.o (Nat.le_refl _) (by omega)
  rw [hc] at hc'
  obtain ⟨blk', hblk', hl', ho', he⟩ := Mem.heap_some hc'
  simp only [Cell.mk.injEq] at he
  obtain ⟨-, hA, hS, hK⟩ := he
  refine ⟨⟨blk', hblk', hl', by omega, by rw [← hA]; exact ha, by rw [← hK]; exact hk⟩, ?_⟩
  unfold curBytes; rw [hblk, hblk']
  simp only [Option.map_some, Option.getD_some]
  apply Array.ext (by simp; omega)
  intro i h1 h2
  simp only [Array.size_extract] at h1 h2
  rw [Array.getElem_extract, Array.getElem_extract]
  have := hw (W.o + i) (by omega) (by omega)
  simp only [Mem.heap, hblk, hblk'] at this
  rw [dite_eq_left_of_eq_true (eq_true ⟨hl', by omega⟩),
    dite_eq_left_of_eq_true (eq_true ⟨hl, by omega⟩)] at this
  simp only [Option.some.injEq, Cell.mk.injEq] at this
  exact this.1

theorem loc_get {m : Mem} {i : Nat} {l : ALoc} (hl : W.Loc m i l) :
    ∃ h : i < m.atomics.size, m.atomics[i] = l ∧ m.atomics[i]! = l := by
  obtain ⟨h, e⟩ := Array.getElem?_eq_some_iff.mp hl.2
  exact ⟨h, e, by rw [getElem!_pos m.atomics i h, e]⟩

theorem loc_unique {m : Mem} {i j : Nat} {l l' : ALoc} (hl : W.Loc m i l) (hl' : W.Loc m j l') :
    i = j ∧ l = l' := by
  have e : i = j := by have := hl.1; rw [hl'.1] at this; cases this; rfl
  subst e
  have := hl.2; rw [hl'.2] at this; cases this; exact ⟨rfl, rfl⟩

theorem loc_at {m : Mem} {i : Nat} {l : ALoc} (hl : W.Loc m i l) : l.block = W.b ∧ l.off = W.o := by
  obtain ⟨hi', hp, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp hl.1
  obtain ⟨h, e, -⟩ := loc_get hl
  rw [e] at hp
  simpa using hp

/-- The location of the word, if the memory has one. -/
theorem loc_of_find {m : Mem} {i : Nat}
    (h : m.atomics.findIdx? (fun l => l.block == W.b && l.off == W.o) = some i) :
    W.Loc m i (m.atomics[i]!) := by
  have hi := (Array.findIdx?_eq_some_iff_getElem.mp h).1
  exact ⟨h, by rw [getElem!_pos m.atomics i hi, Array.getElem?_eq_getElem hi]⟩

/-- The writes, from the location. -/
theorem hist_loc {m : Mem} {i : Nat} {l : ALoc} (hl : W.Loc m i l) : W.hist m = l.msgs.mapIdx ent := by
  unfold hist; rw [hl.1]; simp only; rw [(loc_get hl).2.2]

/-- The same blocks and atomic locations: the same writes. -/
theorem hist_congr {m m' : Mem} (ha : m'.atomics = m.atomics) (hb : m'.blocks = m.blocks) :
    W.hist m' = W.hist m := by
  unfold hist; rw [ha, curBytes_congr hb]

/-- The writes, before the first atomic op. -/
theorem hist_none {m : Mem} (h : ∀ i l, ¬ W.Loc m i l) :
    W.hist m = #[⟨curBytes m W.b W.o nb, #[], #[], none⟩] := by
  unfold hist
  cases hf : m.atomics.findIdx? (fun l => l.block == W.b && l.off == W.o) with
  | none => rfl
  | some i => exact absurd (loc_of_find hf) (h _ _)

/-- An access that overlaps the word hits it. -/
theorem hits_of {e : FootprintEntry} (hb : e.block = W.b) (h1 : W.o < e.off + e.len)
    (h2 : e.off < W.o + nb) : W.Hits e := by
  have hsz0 := W.sz_pos
  by_cases ho : e.off ≤ W.o
  · exact ⟨hb, W.o, ho, .inl h1, Nat.le_refl _, by omega⟩
  · exact ⟨hb, e.off, Nat.le_refl _, .inr rfl, by omega, h2⟩

/-- A plain write to a byte of the word hits it. -/
theorem hits_of_plain {e : FootprintEntry} (h : plainHit W.b W.o nb e = true) : W.Hits e := by
  unfold plainHit at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact hits_of h.1.1.1 h.1.2 h.2

/-- An access that does not hit the word is not a plain write to it. -/
theorem plainHit_false {e : FootprintEntry} (h : ¬ W.Hits e) : plainHit W.b W.o nb e = false := by
  cases hp : plainHit W.b W.o nb e
  · rfl
  · exact absurd (hits_of_plain hp) h

/-- An access that hits the word touches a heap with the word's bytes. -/
theorem touches_of {e : FootprintEntry} {h : Heap} (he : W.Hits e)
    (hw : ∀ x, W.o ≤ x → x < W.o + nb → h (W.b, x) ≠ none) : e.Touches h := by
  obtain ⟨hb, x, h1, h2, h3, h4⟩ := he
  exact ⟨x, h1, h2, by rw [hb]; exact hw x h3 h4⟩

/-- Each byte of the word is in the heap. -/
theorem Ok.cell {m : Mem} (hw : W.Ok m) {x : Nat} (h1 : W.o ≤ x) (h2 : x < W.o + nb) :
    m.heap (W.b, x) ≠ none := by
  obtain ⟨blk, hb, hl, hs, -⟩ := hw.blk
  simp only [Mem.heap, hb]
  rw [dite_eq_left_of_eq_true (eq_true ⟨hl, by omega⟩)]
  simp

/-- The word as the block's bytes. -/
theorem holds_bytes {m : Mem} {blk : Block} {v : BitVec n} (hb : m.blocks[W.b]? = some blk) :
    W.Holds m v ↔ (intOfBytes n (blk.bytes.extract W.o (W.o + nb))).run = some (.ok v) := by
  unfold Word.Holds curBytes; rw [hb]; rfl

/-- The word holds the value of its newest write. -/
theorem Ok.holds_last {m : Mem} (hw : W.Ok m) {v : BitVec n} :
    W.Holds m v ↔ (W.hist m)[(W.hist m).size - 1]!.Val v := by
  unfold hist
  cases hf : m.atomics.findIdx? (fun l => l.block == W.b && l.off == W.o) with
  | none => simp [Entry.Val, Word.Holds]
  | some i =>
    have hl := loc_of_find hf
    obtain ⟨-, h0, -, hlast, -⟩ := hw.loc i _ hl
    simp only
    rw [getElem!_pos _ _ (by simp; omega), Array.getElem_mapIdx]
    unfold Entry.Val ent Word.Holds
    rw [← hlast]
    unfold ALoc.lastBytes
    rw [Array.back?_eq_getElem?, Array.getElem?_eq_getElem (by omega)]
    simp only [Array.size_mapIdx, Option.map_some, Option.getD_some]

/-! ## Steps that keep the word -/

theorem hist_keep {m m' : Mem} (hw : W.Ok m) (hk : W.Keep m m') : W.hist m' = W.hist m := by
  cases hf : m.atomics.findIdx? (fun l => l.block == W.b && l.off == W.o) with
  | some i =>
    have hl := loc_of_find hf
    rw [hist_loc hl, hist_loc ((hk.loc _ _).mpr hl)]
  | none =>
    have hn : ∀ i l, ¬ W.Loc m i l := fun i l hl => by rw [hl.1] at hf; cases hf
    have hn' : ∀ i l, ¬ W.Loc m' i l := fun i l hl => hn i l ((hk.loc i l).mp hl)
    rw [hist_none hn, hist_none hn', (congr hk.cells hw.blk).2]

/-- A step that keeps the word keeps its invariant. -/
theorem Ok.keep {m m' : Mem} (hw : W.Ok m) (hk : W.Keep m m') : W.Ok m' := by
  obtain ⟨hb', hcur⟩ := congr hk.cells hw.blk
  refine ⟨hb', fun l hl hb h1 h2 => ?_, fun i l hl => ?_, fun e he hh => ?_, ?_,
    fun i l hl => (hw.plain i l ((hk.loc i l).mp hl)).of_fp fun e he =>
      (hk.fp e he).imp id plainHit_false⟩
  · rcases hk.only l hl with h | h | h | h
    · exact hw.only l h hb h1 h2
    · exact absurd hb h
    · omega
    · omega
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hw.loc i l ((hk.loc i l).mp hl)
    exact ⟨h1, h2, h3, by rw [h4, hcur], h5⟩
  · rcases hk.fp e he with h | h
    · rcases hw.wfp e h hh with ⟨ha, hs⟩ | ha
      · exact .inl ⟨ha, hk.some _ hs⟩
      · exact .inr (hk.all _ ha)
    · exact absurd hh h
  · obtain ⟨v, hv⟩ := hw.val; exact ⟨v, by unfold Word.Holds; rw [hcur]; exact hv⟩

/-- The same blocks, atomic locations and footprint, and clocks that do not get smaller. -/
theorem keep_of {m m' : Mem} (hb : m'.blocks = m.blocks) (ha : m'.atomics = m.atomics)
    (hf : m'.footprint = m.footprint) (ht : m'.threads = m.threads)
    (hcl : ∀ u : Nat, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true) : W.Keep m m' :=
  ⟨fun x _ _ => by simp only [Mem.heap, hb], fun i l => by unfold Word.Loc; rw [ha],
    fun l hl => .inl (ha ▸ hl), fun e he => .inl (hf ▸ he),
    fun _ h u hu => VClock.le_trans (h u (ht ▸ hu)) (hcl u),
    fun _ ⟨u, hu, hle⟩ => ⟨u, ht ▸ hu, VClock.le_trans hle (hcl u)⟩⟩

/-- The same memory, but `current`, `seen`, `nextMsg`, the futex queue, the woken threads and
the groups. -/
theorem keep_same (m : Mem) (c : ThreadId) (s : Array (ThreadId × Nat × Nat)) (k : Nat)
    (ws : Array (ThreadId × Ptr)) (wk : Array ThreadId) (gs : Array (Ptr × ThreadId)) :
    W.Keep m { m with current := c, seen := s, nextMsg := k, waiters := ws, woken := wk, groups := gs } :=
  keep_of rfl rfl rfl rfl fun _ => VClock.le_refl _

/-- The lock's word and `W` do not overlap. -/
def Apart {γ : Type} (L : Lock γ) {n nb : Nat} (W : Word n nb) : Prop := L.b ≠ W.b ∨ L.o + 4 ≤ W.o ∨ W.o + nb ≤ L.o

/-- A step of the lock's code keeps a word apart from the lock's. -/
theorem keep_lockStep {γ : Type} {L : Lock γ} {t : ThreadId} {m m' : Mem} (hs : L.Step t m m')
    (hap : Apart L W) : W.Keep m m' := by
  have hsz0 := W.sz_pos
  refine ⟨fun x h1 h2 => hs.heap ?_, fun i l => ?_, fun l hl => ?_, fun e he => ?_,
    fun _ h => hs.allLe h, fun _ h => hs.someLe h⟩
  · rintro ⟨hb, h3, h4⟩; simp only at hb h3 h4
    rcases hap with h | h | h
    · exact h hb.symm
    · omega
    · omega
  · have hne : W.b ≠ L.b ∨ W.o ≠ L.o := by
      rcases hap with h | h | h
      · exact .inl (Ne.symm h)
      · exact .inr (by omega)
      · exact .inr (by omega)
    exact hs.locs.same W.b W.o hne i l
  · rcases hs.locs.new l hl with h | ⟨hb, ho, hlen⟩
    · exact .inl h
    · rcases hap with h | h | h
      · exact .inr (.inl (by rw [hb]; exact h))
      · exact .inr (.inr (.inl (by omega)))
      · exact .inr (.inr (.inr (by omega)))
  · rcases hs.fp e he with h | ⟨hb, ho, hl, -⟩
    · exact .inl h
    · refine .inr fun ⟨hb', x, h1, h2, h3, h4⟩ => ?_
      rw [hb] at hb'
      rcases hap with h | h | h
      · exact h hb'
      · rcases h2 with h2 | h2 <;> omega
      · rcases h2 with h2 | h2 <;> omega

/-- A step of thread `t` on its own part (`WP.liftMem_owned`), which has no byte of the word
(its cells are in the rest of the heap, `hF`). -/
theorem keep_stepIn_of {m m' : Mem} {own hQ : Heap}
    (hF : ∀ x, W.o ≤ x → x < W.o + nb → m.heap.diff own (W.b, x) ≠ none)
    (hs : StepIn (m.heap.diff own) m m') (hm' : m'.heap = hQ ∪ m.heap.diff own)
    (hd : Heap.Disjoint hQ (m.heap.diff own)) : W.Keep m m' := by
  have hcl : ∀ u : Nat, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true := fun u => by
    by_cases hu : u = m.current
    · subst hu; exact hs.mine
    · rw [hs.others u hu]; exact VClock.le_refl _
  refine ⟨fun x h1 h2 => ?_, fun i l => by unfold Word.Loc; rw [hs.atomics],
    fun l hl => .inl (hs.atomics ▸ hl), fun e he => ?_,
    fun _ h u hu => VClock.le_trans (h u (hs.threads ▸ hu)) (hcl u),
    fun _ ⟨u, hu, hle⟩ => ⟨u, hs.threads ▸ hu, VClock.le_trans hle (hcl u)⟩⟩
  · rw [hm', Heap.union_of_right ((hd (W.b, x)).resolve_right (hF x h1 h2))]
    have hF' := hF x h1 h2
    unfold Heap.diff at hF' ⊢; split at hF' <;> simp_all
  · rcases hs.fp e he with h | ⟨-, hnt, -⟩
    · exact .inl h
    · exact .inr fun hh => hnt (touches_of hh hF)

/-- A step of thread `t` on its own part (`WP.liftMem_owned`), which has no byte of the word. -/
theorem keep_stepIn {m m' : Mem} {own hQ : Heap} (hw : W.Ok m) (hoff : W.Off own)
    (hs : StepIn (m.heap.diff own) m m') (hm' : m'.heap = hQ ∪ m.heap.diff own)
    (hd : Heap.Disjoint hQ (m.heap.diff own)) : W.Keep m m' :=
  keep_stepIn_of (fun x h1 h2 => by
    simp only [Heap.diff, hoff x h1 h2, ↓reduceIte]; exact hw.cell h1 h2) hs hm' hd

/-- A spawn by `t`. -/
theorem keep_fork {m m' : Mem} {t c : ThreadId} (ht : t < m.threads.size)
    (hcs : m.clocks.size = m.threads.size)
    (hf : (Thread.fork.run { m with current := t }).run = some (.ok (c, m'))) : W.Keep m m' := by
  obtain ⟨rfl, rfl⟩ := Lock.fork_eq hf
  obtain ⟨hcl, hcn, -⟩ := Lock.fork_clocks (cs := m.clocks) (t := t) (by rw [hcs]; exact ht)
  refine ⟨fun x _ _ => rfl, fun i l => Iff.rfl, fun l hl => .inl hl, fun e he => .inl he,
    fun _ h u hu => ?_, fun _ ⟨u, hu, hle⟩ => ⟨u, by simp only [Array.size_push]; omega,
      VClock.le_trans hle (hcl u (by rw [hcs]; exact hu))⟩⟩
  simp only [Array.size_push] at hu
  by_cases hu' : u < m.threads.size
  · exact VClock.le_trans (h u hu') (hcl u (by rw [hcs]; exact hu'))
  · have : u = m.threads.size := by omega
    subst this; rw [← hcs]; exact VClock.le_trans (h t ht) hcn

/-- A join of `u` by `t`. -/
theorem keep_join {m m' : Mem} {t u : ThreadId}
    (hj : ((Thread.join u).run { m with current := t }).run = some (.ok ((), m'))) : W.Keep m m' := by
  obtain ⟨rec, -, -, rfl⟩ := Proto.join_eq hj
  have hcl : ∀ w : Nat, VClock.le (m.clocks[w]!) ((m.clocks.set! t (VClock.merge
      (VClock.bump (m.clocks[t]!) t) (m.clocks[u]!)))[w]!) = true := by
    intro w
    rw [Proto.getElem!_set!_ite]
    split
    · rename_i h; rw [h.1]
      exact VClock.le_trans (VClock.le_bump _ _) (VClock.le_merge_left _ _)
    · exact VClock.le_refl _
  have hsz : (m.threads.set! u { rec with joined := true }).size = m.threads.size := by simp
  exact ⟨fun x _ _ => rfl, fun i l => Iff.rfl, fun l hl => .inl hl, fun e he => .inl he,
    fun _ h w hw => VClock.le_trans (h w (hsz ▸ hw)) (hcl w),
    fun _ ⟨w, hw, hle⟩ => ⟨w, by rw [hsz]; exact hw, VClock.le_trans hle (hcl w)⟩⟩

/-- A plain read of `n` bytes at `o` of block `b` that do not hit the word. -/
theorem keep_read (m : Mem) {b o n : Nat} (hn : 0 < n) (hnw : b ≠ W.b ∨ o + n ≤ W.o ∨ W.o + nb ≤ o) :
    W.Keep m (m.recordAt b o n .read) := by
  refine ⟨fun x _ _ => rfl, fun i l => Iff.rfl, fun l hl => .inl hl, fun e he => ?_,
    fun _ h u hu => VClock.le_trans (h u hu) (Lock.recordAt_le m _ _ _ _ u),
    fun _ ⟨u, hu, hle⟩ => ⟨u, hu, VClock.le_trans hle (Lock.recordAt_le m _ _ _ _ u)⟩⟩
  simp only [Mem.recordAt, Array.mem_push] at he
  rcases he with he | rfl
  · exact .inl he
  · refine .inr fun ⟨hb', x, h1, h2, h3, h4⟩ => ?_
    dsimp only at hb' h1 h2
    rcases hnw with h | h | h
    · exact h hb'
    · rcases h2 with h2 | h2 <;> omega
    · rcases h2 with h2 | h2 <;> omega

/-! ## An atomic op at the word -/

/-- An atomic op at the word by thread `t`: the threads, the futex queue and the groups stay,
only `t`'s clock grows, only the word's cells change, each new access is an atomic access to the
word, and the atomic locations of other addresses stay. -/
structure Op (t : ThreadId) (m m' : Mem) : Prop where
  current : m'.current = t
  threads : m'.threads = m.threads
  waiters : m'.waiters = m.waiters
  woken : m'.woken = m.woken
  groups : m'.groups = m.groups
  csize : m'.clocks.size = m.clocks.size
  others : ∀ u, u ≠ t → m'.clocks[u]! = m.clocks[u]!
  mine : VClock.le (m.clocks[t]!) (m'.clocks[t]!) = true
  bsize : m'.blocks.size = m.blocks.size
  cells : ∀ l : Zig.Loc, ¬ (l.1 = W.b ∧ W.o ≤ l.2 ∧ l.2 < W.o + nb) → m'.heap l = m.heap l
  fp : ∀ e ∈ m'.footprint, e ∈ m.footprint ∨
    (e.block = W.b ∧ e.off = W.o ∧ e.len = nb ∧ e.kind.isAtomic = true ∧ SomeLe m' e.clock)
  locs : LocsKeep W.b W.o nb m m'
  /-- A new access is by thread `t`, below its new clock. -/
  fpt : ∀ e ∈ m'.footprint, e ∈ m.footprint ∨ (e.tid = t ∧ VClock.le e.clock (m'.clocks[t]!) = true)

theorem Op.clocks {t : ThreadId} {m m' : Mem} (h : W.Op t m m') (u : Nat) :
    VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true := by
  by_cases hu : u = t
  · subst hu; exact h.mine
  · rw [h.others u hu]; exact VClock.le_refl _

theorem Op.someLe {t : ThreadId} {m m' : Mem} (h : W.Op t m m') {c : VClock} (hc : SomeLe m c) :
    SomeLe m' c := by
  obtain ⟨u, hu, hle⟩ := hc
  exact ⟨u, h.threads ▸ hu, VClock.le_trans hle (h.clocks u)⟩

theorem Op.allLe {t : ThreadId} {m m' : Mem} (h : W.Op t m m') {c : VClock} (hc : AllLe m c) :
    AllLe m' c := fun u hu => VClock.le_trans (hc u (h.threads ▸ hu)) (h.clocks u)

theorem Op.trans {t : ThreadId} {m₁ m₂ m₃ : Mem} (h₁ : W.Op t m₁ m₂) (h₂ : W.Op t m₂ m₃) :
    W.Op t m₁ m₃ := by
  refine ⟨h₂.current, h₂.threads.trans h₁.threads, h₂.waiters.trans h₁.waiters,
    h₂.woken.trans h₁.woken, h₂.groups.trans h₁.groups, h₂.csize.trans h₁.csize,
    fun u hu => (h₂.others u hu).trans (h₁.others u hu), VClock.le_trans h₁.mine h₂.mine,
    h₂.bsize.trans h₁.bsize, fun l hl => (h₂.cells l hl).trans (h₁.cells l hl), fun e he => ?_,
    h₁.locs.trans h₂.locs, fun e he => ?_⟩
  · rcases h₂.fp e he with h | h
    · rcases h₁.fp e h with h' | ⟨a, b, c, d, f⟩
      · exact .inl h'
      · exact .inr ⟨a, b, c, d, h₂.someLe f⟩
    · exact .inr h
  · rcases h₂.fpt e he with h | h
    · rcases h₁.fpt e h with h' | ⟨ht, hle⟩
      · exact .inl h'
      · exact .inr ⟨ht, VClock.le_trans hle h₂.mine⟩
    · exact .inr h

/-- An op at the word keeps a word apart from it. -/
theorem keep_op {n' nb' : Nat} {W' : Word n' nb'} {t : ThreadId} {m m' : Mem} (h : W.Op t m m')
    (hap : W.b ≠ W'.b ∨ W.o + nb ≤ W'.o ∨ W'.o + nb' ≤ W.o) : W'.Keep m m' := by
  have hsz0 := W.sz_pos
  have hsz1 := W'.sz_pos
  refine ⟨fun x h1 h2 => h.cells _ ?_, fun i l => ?_, fun l hl => ?_, fun e he => ?_,
    fun _ hc => h.allLe hc, fun _ hc => h.someLe hc⟩
  · rintro ⟨hb, h3, h4⟩; simp only at hb h3 h4
    rcases hap with h | h | h
    · exact h hb.symm
    · omega
    · omega
  · have hne : W'.b ≠ W.b ∨ W'.o ≠ W.o := by
      rcases hap with h | h | h
      · exact .inl (Ne.symm h)
      · exact .inr (by omega)
      · exact .inr (by omega)
    exact h.locs.same W'.b W'.o hne i l
  · rcases h.locs.new l hl with h' | ⟨hb, ho, hlen⟩
    · exact .inl h'
    · rcases hap with h' | h' | h'
      · exact .inr (.inl (by rw [hb]; exact h'))
      · exact .inr (.inr (.inl (by omega)))
      · exact .inr (.inr (.inr (by omega)))
  · rcases h.fp e he with h' | ⟨hb, ho, hl, -⟩
    · exact .inl h'
    · refine .inr fun ⟨hb', x, h1, h2, h3, h4⟩ => ?_
      rw [hb] at hb'
      rcases hap with h' | h' | h'
      · exact h' hb'
      · rcases h2 with h2 | h2 <;> omega
      · rcases h2 with h2 | h2 <;> omega

/-- The word's access: no error. -/
theorem Ok.access {m : Mem} (hw : W.Ok m) :
    ∃ blk, m.blocks[W.b]? = some blk ∧ blk.live = true ∧ W.o + nb ≤ blk.bytes.size ∧
      m.access W.ptr nb nb = pure (W.b, blk, W.o) ∧ m.accessW W.ptr nb nb = pure (W.b, blk, W.o) := by
  obtain ⟨blk, hb, hl, hs, ha, hk⟩ := hw.blk
  have hacc : m.access W.ptr nb nb = pure (W.b, blk, W.o) := by
    have := access_of (p := W.ptr) (n := nb) (a := nb) (m := m) rfl hb hl (by simp [Word.ptr])
      (by simp only [Word.ptr]; omega) (by simpa [Word.ptr] using ha)
    simpa [Word.ptr] using this
  refine ⟨blk, hb, hl, hs, hacc, ?_⟩
  unfold Mem.accessW; rw [hacc]
  simp [hk, pure, bind, ExceptT.bind, ExceptT.mk, ExceptT.pure, ExceptT.bindCont]

/-- Recording an atomic access preserves the shared word and its history. -/
theorem Ok.record {m : Mem} {t : Nat} {k : AccessKind} (hw : W.Ok m) (hc : m.current = t)
    (ht : t < m.threads.size) (hcs : m.clocks.size = m.threads.size) (hk : k.isAtomic = true) :
    W.Ok (m.recordAt W.b W.o nb k) ∧ W.Op t m (m.recordAt W.b W.o nb k) ∧
      W.hist (m.recordAt W.b W.o nb k) = W.hist m := by
  subst hc
  have hct : m.current < m.clocks.size := by rw [hcs]; exact ht
  -- the record
  let mr := m.recordAt W.b W.o nb k
  have hrc : ∀ u : Nat, VClock.le (m.clocks[u]!) (mr.clocks[u]!) = true :=
    Lock.recordAt_le m _ _ _ _
  have hrt : mr.clocks[m.current]! = VClock.bump (m.clocks[m.current]!) m.current := by
    simp only [mr, Mem.recordAt]; rw [Proto.getElem!_set!_ite]; simp [hct]
  have hro : ∀ u, u ≠ m.current → mr.clocks[u]! = m.clocks[u]! := by
    intro u hu; simp only [mr, Mem.recordAt]; rw [Proto.getElem!_set!_ite, if_neg (fun h => hu h.1)]
  have hcur : curBytes mr W.b W.o nb = curBytes m W.b W.o nb := curBytes_congr rfl _ _ _
  have hwr : W.Ok mr := by
    refine ⟨hw.blk, hw.only, fun i l hl => ?_, fun e he hh => ?_, hw.val,
      fun i l hl => (hw.plain i l hl).of_fp fun e he => by
        simp only [mr, Mem.recordAt, Array.mem_push] at he
        rcases he with he | rfl
        · exact .inl he
        · exact .inr (plainHit_atomic hk)⟩
    · obtain ⟨h1, h2, h3, h4, h5⟩ := hw.loc i l hl
      exact ⟨h1, h2, h3, by rw [h4, hcur], h5⟩
    simp only [mr, Mem.recordAt, Array.mem_push] at he
    rcases he with he | rfl
    · rcases hw.wfp e he hh with ⟨ha, hs⟩ | ha
      · exact .inl ⟨ha, Lock.someLe_mono (m := m) (m' := mr) rfl (fun u _ => hrc u) hs⟩
      · exact .inr (Lock.allLe_mono (m := m) (m' := mr) rfl (fun u _ => hrc u) ha)
    · refine .inl ⟨hk, m.current, ht, ?_⟩
      show VClock.le _ (mr.clocks[m.current]!) = true
      rw [hrt]; exact VClock.le_refl _
  have hopr : W.Op m.current m mr := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, by simp [mr, Mem.recordAt], hro,
      by rw [hrt]; exact VClock.le_bump _ _, rfl, fun l _ => rfl, fun e he => ?_, .of_eq rfl,
      fun e he => ?_⟩
    · simp only [mr, Mem.recordAt, Array.mem_push] at he
      rcases he with he | rfl
      · exact .inl he
      · refine .inr ⟨rfl, rfl, rfl, hk, m.current, ht, ?_⟩
        show VClock.le _ (mr.clocks[m.current]!) = true
        rw [hrt]; exact VClock.le_refl _
    · simp only [mr, Mem.recordAt, Array.mem_push] at he
      rcases he with he | rfl
      · exact .inl he
      · refine .inr ⟨rfl, ?_⟩
        show VClock.le _ (mr.clocks[m.current]!) = true
        rw [hrt]; exact VClock.le_refl _
  exact ⟨hwr, hopr, hist_congr rfl rfl⟩

/-- The record of an atomic access to the word, and the word's location (`locIdx`): the
location exists after it, with the same writes. -/
theorem Ok.prep {m m₁ : Mem} {t li : Nat} {k : AccessKind} (hw : W.Ok m) (hc : m.current = t)
    (ht : t < m.threads.size) (hcs : m.clocks.size = m.threads.size) (hk : k.isAtomic = true)
    (h : ((locIdx W.b W.o nb).run (m.recordAt W.b W.o nb k)).run = some (.ok (li, m₁))) :
    ∃ l, W.Loc m₁ li l ∧ W.Ok m₁ ∧ W.Op t m m₁ ∧ W.hist m₁ = W.hist m ∧ m₁.blocks = m.blocks ∧
      m₁.seen = m.seen := by
  subst hc
  let mr := m.recordAt W.b W.o nb k
  have hcur : curBytes mr W.b W.o nb = curBytes m W.b W.o nb := curBytes_congr rfl _ _ _
  obtain ⟨hwr, hopr, -⟩ := hw.record rfl ht hcs hk
  -- the location
  cases hf : mr.atomics.findIdx? (fun l => l.block == W.b && l.off == W.o) with
  | some i =>
    have hl := loc_of_find hf
    obtain ⟨hlen, -, -, hlast, -⟩ := hwr.loc i _ hl
    obtain ⟨rfl, rfl⟩ := locIdx_found hf hlen hlast (hwr.plain i _ hl) h
    exact ⟨_, hl, hwr, hopr, hist_congr rfl rfl, rfl, rfl⟩
  | none =>
    obtain ⟨rfl, rfl⟩ := locIdx_new hf h
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
        simpa [ALoc.lastClock, nl, firstLoc, firstMsg] using plainLe_plainClock mr W.b W.o nb e he hh⟩,
      hopr.trans ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, VClock.le_refl _, rfl,
        fun _ _ => rfl, fun e he => .inl he, .push rfl rfl rfl rfl, fun e he => .inl he⟩, ?_, rfl, rfl⟩
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

/-! ## The ops at the word -/

/-- An atomic access to the word does not race. -/
theorem Ok.noRace {m : Mem} (hw : W.Ok m) {k : AccessKind} (hk : k.isAtomic = true)
    (ht : m.current < m.threads.size) : NoRace m W.b W.o nb k := by
  refine noRace_of fun e he hb h1 h2 => ?_
  rcases hw.wfp e he (hits_of hb h1 h2) with ⟨ha, -⟩ | h
  · refine .inr ?_; unfold racePair; simp [ha, hk]
  · exact .inl (h _ ht)

/-- Message `j` as write `j`. -/
theorem hist_get {m : Mem} {i : Nat} {l : ALoc} (hl : W.Loc m i l) {j : Nat} (hj : j < l.msgs.size) :
    (W.hist m)[j]! = ent j l.msgs[j] := by
  rw [hist_loc hl, getElem!_pos _ _ (by simpa using hj)]
  simp

/-- A position that a read can read is at least the floor. -/
theorem floor_le {m : Mem} {li c pos : Nat} {rmw : Bool} (h : (readOpts m li rmw)[c]? = some pos) :
    floorPos m li ≤ pos := by
  have hm := Array.mem_of_getElem? h
  unfold readOpts at hm
  simp only [Array.mem_filter, Array.mem_map, Array.mem_range] at hm
  obtain ⟨⟨k, hk, rfl⟩, -⟩ := hm
  omega

/-- The write of an RMW by `t` in the release sequence of `last`, with the value `new`; `M` is
the memory after it. -/
def rmwEnt (M : Mem) (t : ThreadId) (ord : AtomicOrder) (last : Entry) (new : BitVec n) : Entry :=
  ⟨padTo (intSize n) (intBytes new), M.clocks[t]!,
    if ord.isRel then VClock.merge last.relClock (M.clocks[t]!) else last.relClock, some t⟩

/-- An RMW at the word by thread `t` that read the newest message of `l` and wrote `new`. -/
theorem Ok.rmwAt {m₁ M : Mem} {t li : Nat} {l : ALoc} {ord : AtomicOrder} {new : BitVec n}
    (hw : W.Ok m₁) (hl : W.Loc m₁ li l) (hc : m₁.current = t) (ht : t < m₁.threads.size)
    (hcs : m₁.clocks.size = m₁.threads.size)
    (hM : M = rmwM m₁ li (l.msgs.size - 1) ord (l.msgs[l.msgs.size - 1]!) new) :
    W.Ok M ∧ W.Op t m₁ M ∧ W.Holds M new ∧
      W.hist M = (W.hist m₁).push (rmwEnt M t ord (W.hist m₁)[(W.hist m₁).size - 1]! new) ∧
      (ord.isAcq = true →
        VClock.le (W.hist m₁)[(W.hist m₁).size - 1]!.relClock (M.clocks[t]!) = true) := by
  subst hc
  obtain ⟨hlen, h0, hch, hlast, hval⟩ := hw.loc li l hl
  obtain ⟨hlb, hlo⟩ := loc_at hl
  obtain ⟨hli, -, hl0⟩ := loc_get hl
  obtain ⟨blk, hb, hlv, hsz, ha4, hk⟩ := hw.blk
  have hct : m₁.current < m₁.clocks.size := by rw [hcs]; exact ht
  let rd := l.msgs[l.msgs.size - 1]!
  let m₂ := if ord.isAcq then acqM m₁ rd.relClock else m₁
  have h2 : m₂.atomics = m₁.atomics ∧ m₂.blocks = m₁.blocks ∧ m₂.threads = m₁.threads ∧
      m₂.footprint = m₁.footprint ∧ m₂.waiters = m₁.waiters ∧ m₂.current = m₁.current ∧
      m₂.groups = m₁.groups ∧ m₂.woken = m₁.woken ∧ m₂.nextMsg = m₁.nextMsg ∧
      m₂.clocks.size = m₁.clocks.size := by
    simp only [m₂]; split <;> simp [acqM]
  obtain ⟨ha₂, hb₂, ht₂, hf₂, hw₂, hc₂, hg₂, hk₂, hn₂, hcs₂⟩ := h2
  have hl₂ : m₂.atomics[li]! = l := by rw [ha₂]; exact hl0
  have hblk₂ : m₂.blocks[(m₂.atomics[li]!).block]? = some blk := by rw [hl₂, hlb, hb₂]; exact hb
  have hins := insertM_last (msg := rmwMsg m₂ ord rd new) hblk₂
  rw [hl₂] at hins
  have hp : l.msgs.size - 1 + 1 = l.msgs.size := by omega
  have hMe : M = observeM { m₂ with
      atomics := m₂.atomics.set! li { l with msgs := l.msgs.push (rmwMsg m₂ ord rd new) },
      nextMsg := m₂.nextMsg + 1,
      blocks := m₂.blocks.set! l.block
        { blk with bytes := writeBytes blk.bytes l.off (rmwMsg m₂ ord rd new).bytes } } li m₂.nextMsg := by
    rw [hM]; unfold rmwM; simp only; rw [hp, hins]
  -- the clocks
  have hcl₂ : ∀ u, u ≠ m₁.current → m₂.clocks[u]! = m₁.clocks[u]! := by
    intro u hu; simp only [m₂]; split
    · simp only [acqM]; rw [Proto.getElem!_set!_ite, if_neg (fun h => hu h.1)]
    · rfl
  have hct₂ : VClock.le (m₁.clocks[m₁.current]!) (m₂.clocks[m₁.current]!) = true := by
    simp only [m₂]; split
    · rw [acqM_clock _ _ hct]; exact VClock.le_merge_left _ _
    · exact VClock.le_refl _
  have hMc : M.clocks = m₂.clocks := by rw [hMe]; rfl
  have hMa : M.atomics = m₁.atomics.set! li { l with msgs := l.msgs.push (rmwMsg m₂ ord rd new) } := by
    rw [hMe]; simp only [observeM, ha₂]
  have hMb : M.blocks[W.b]? = some { blk with bytes := writeBytes blk.bytes W.o (padTo (intSize n) (intBytes new)) } := by
    rw [hMe]; simp only [observeM, hb₂, hlb, hlo, rmwMsg]
    rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt
      (Array.getElem?_eq_some_iff.mp hb).1]
  have hMbs : M.blocks.size = m₁.blocks.size := by rw [hMe]; simp [observeM, hb₂]
  have hbs : (padTo (intSize n) (intBytes new)).size = nb := W.enc_size new
  have hcur : curBytes M W.b W.o nb = padTo (intSize n) (intBytes new) := by
    unfold curBytes; rw [hMb]
    simp only [Option.map_some, Option.getD_some]
    have := extract_writeBytes blk.bytes W.o (padTo (intSize n) (intBytes new)) (by omega)
    rwa [hbs] at this
  let l' : ALoc := { l with msgs := l.msgs.push (rmwMsg m₂ ord rd new) }
  have hl' : W.Loc M li l' := by
    obtain ⟨hi', hpr, hj⟩ := Array.findIdx?_eq_some_iff_getElem.mp hl.1
    have hs : (m₁.atomics.set! li l').size = m₁.atomics.size := by simp
    refine ⟨Array.findIdx?_eq_some_iff_getElem.mpr ⟨by rw [hMa, hs]; exact hi', ?_,
      fun j hji => ?_⟩, ?_⟩
    · simp only [hMa, Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds, ↓reduceIte]
      simp [l', hlb, hlo]
    · simp only [hMa, Array.set!_eq_setIfInBounds]
      rw [Array.getElem_setIfInBounds (by omega), if_neg (Nat.ne_of_gt hji)]
      exact hj j hji
    · rw [hMa, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]; simp [hli, l']
  have hmr : (rmwMsg m₂ ord rd new).rmwOf = some (l.msgs[l.msgs.size - 1]!).id := rfl
  have hhc : M.heap = (m₁.write W.b blk W.o (padTo (intSize n) (intBytes new))).heap := by
    funext x; obtain ⟨b', o'⟩ := x
    simp only [Mem.heap, Mem.write]
    by_cases hb' : b' = W.b
    · subst hb'; rw [hMb, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt
        (Array.getElem?_eq_some_iff.mp hb).1]
    · rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (Ne.symm hb')]
      rw [hMe]; simp only [observeM, hb₂, hlb]
      rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (Ne.symm hb')]
  have hrel : (rmwMsg m₂ ord rd new).relClock =
      if ord.isRel then VClock.merge rd.relClock (M.clocks[m₁.current]!) else rd.relClock := by
    simp only [rmwMsg, hMc, hc₂]
  have hsz' : W.o + nb ≤ (writeBytes blk.bytes W.o (padTo (intSize n) (intBytes new))).size := by
    rw [writeBytes_size _ _ _ (by omega)]; exact hsz
  refine ⟨⟨⟨_, hMb, hlv, hsz', ha4, hk⟩,
    fun l₀ hl₀ hb' h1 h2 => ?_, fun i l₀ hl₀ => ?_, fun e he hh => ?_,
    ⟨new, by unfold Word.Holds; rw [hcur]; exact W.enc_val new⟩, fun i l₀ hl₀ => ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_,
    fun u hu => by rw [hMc]; exact hcl₂ u hu, by rw [hMc]; exact hct₂, hMbs, fun x hx => ?_,
    fun e he => .inl (by rw [hMe] at he; simpa [observeM, hf₂] using he), ?_,
    fun e he => .inl (by rw [hMe] at he; simpa [observeM, hf₂] using he)⟩,
    by unfold Word.Holds; rw [hcur]; exact W.enc_val new, ?_, fun hq => ?_⟩
  · rw [hMa, Array.set!_eq_setIfInBounds] at hl₀
    rcases Array.mem_or_eq_of_mem_set (w := hli) (by simpa [Array.setIfInBounds, hli] using hl₀)
      with h | rfl
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
  · have he' : e ∈ m₁.footprint := by rw [hMe] at he; simpa [observeM, hf₂] using he
    rcases hw.wfp e he' hh with ⟨ha', hle⟩ | hle
    · refine .inl ⟨ha', ?_⟩
      obtain ⟨u, hu, hle'⟩ := hle
      refine ⟨u, by rw [hMe]; simpa [observeM, ht₂] using hu, VClock.le_trans hle' ?_⟩
      rw [hMc]; by_cases hu' : u = m₁.current
      · subst hu'; exact hct₂
      · rw [hcl₂ u hu']; exact VClock.le_refl _
    · refine .inr fun u hu => VClock.le_trans (hle u (by rw [hMe] at hu; simpa [observeM, ht₂] using hu)) ?_
      rw [hMc]; by_cases hu' : u = m₁.current
      · subst hu'; exact hct₂
      · rw [hcl₂ u hu']; exact VClock.le_refl _
  · obtain ⟨rfl, rfl⟩ := loc_unique hl₀ hl'
    intro e he hh
    have he' : e ∈ m₁.footprint := by rw [hMe] at he; simpa [observeM, hf₂] using he
    have hlc : l'.lastClock = m₂.clocks[m₁.current]! := by simp [l', ALoc.lastClock, rmwMsg, hc₂]
    rw [hlc]
    rcases hw.wfp e he' (hits_of_plain hh) with ⟨ha', -⟩ | hle
    · rw [plainHit_atomic ha'] at hh; cases hh
    · exact VClock.le_trans (hle _ ht) hct₂
  · rw [hMe]; simp [observeM, hc₂]
  · rw [hMe]; simp [observeM, ht₂]
  · rw [hMe]; simp [observeM, hw₂]
  · rw [hMe]; simp [observeM, hk₂]
  · rw [hMe]; simp [observeM, hg₂]
  · rw [hMc, hcs₂]
  · rw [hhc, Mem.heap_write hb hlv (by omega)]
    rw [hbs]; simp only [hx, ↓reduceIte]
  · exact LocsKeep.set hl.2 hlb hlo (by exact hlb) (by exact hlo) (by exact hlen) hMa
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

/-- Write `j` of the word, from the location. -/
theorem hist_size {m : Mem} {i : Nat} {l : ALoc} (hl : W.Loc m i l) : (W.hist m).size = l.msgs.size := by
  rw [hist_loc hl]; simp

/-- The holder of a mutex word from its writes (`ALoc.holder`). -/
def holder (h : Array Entry) : Option ThreadId :=
  holderRev (h.toList.reverse.map fun x => (x.bytes, x.writer))

/-- The holder from the writes is the holder of the location. -/
theorem holder_hist {m : Mem} {i : Nat} {l : ALoc} (hl : W.Loc m i l) :
    holder (W.hist m) = l.holder := by
  rw [hist_loc hl]
  unfold holder ALoc.holder
  have h : (l.msgs.mapIdx ent).map (fun x => (x.bytes, x.writer)) =
      l.msgs.map (fun x => (x.bytes, x.writer)) := by
    apply Array.ext
    · simp
    · intro j h1 h2; simp [ent]
  have h' := congrArg (fun a => a.toList.reverse) h
  simp only [Array.toList_map, ← List.map_reverse] at h'
  rw [h']

/-- A write that is not `0` over a newest write `0` (a successful acquire): its writer holds the
word. -/
theorem holder_push_acq {h : Array Entry} {e : Entry} (h0 : 0 < h.size)
    (he : word0 e.bytes = false) (hl : word0 h[h.size - 1]!.bytes = true) :
    holder (h.push e) = e.writer :=
  Lock.holderRev_push_acq _ h0 he hl

/-- A write that is not `0` over a newest write that is not `0`: the holder stays. -/
theorem holder_push_keep {h : Array Entry} {e : Entry} (h0 : 0 < h.size)
    (he : word0 e.bytes = false) (hl : word0 h[h.size - 1]!.bytes = false) :
    holder (h.push e) = holder h :=
  Lock.holderRev_push_keep _ h0 he hl

/-- `word0` of a write with a 32-bit value. -/
theorem word0_of_val {x : Entry} {v : BitVec 32} (h : x.Val v) : word0 x.bytes = (v == 0) := by
  unfold word0; unfold Entry.Val at h; rw [h]

/-- Before the first atomic op the word has no holder. -/
theorem holder_none {m : Mem} (h : ∀ i l, ¬ W.Loc m i l) : holder (W.hist m) = none := by
  rw [hist_none h]; simp [holder, holderRev]

/-- The owner check of an unlock (`Thread.mutexOwnerCheck`) at a 4-byte word that the current
thread holds: it passes and changes nothing. -/
theorem Ok.ownerCheck {W : Word 32 4} {m : Mem} (hw : W.Ok m)
    (hh : holder (W.hist m) = some m.current) :
    ((Thread.mutexOwnerCheck W.ptr).run m).run = some (.ok ((), m)) := by
  obtain ⟨blk, -, -, -, ha, -⟩ := hw.access
  cases hf : m.atomics.findIdx? (fun l => l.block == W.b && l.off == W.o) with
  | none => rw [holder_none fun i l hl => by rw [hl.1] at hf; cases hf] at hh; cases hh
  | some i =>
    have hl := loc_of_find hf
    exact Lock.mutexOwnerCheck_ok ha hl (by rw [← holder_hist hl]; exact hh)

/-- The value of message `j`, as the value of write `j`. -/
theorem val_of {m : Mem} {i : Nat} {l : ALoc} (hl : W.Loc m i l) {j : Nat} (hj : j < l.msgs.size)
    {v : BitVec n} (h : (intOfBytes n (l.msgs[j]!).bytes).run = some (.ok v)) :
    (W.hist m)[j]!.Val v := by
  rw [hist_get hl hj]; unfold Entry.Val ent; rw [← getElem!_pos l.msgs _ hj]; exact h

/-- An RMW at the word by thread `t`: it reads the newest write (`old`), and its write is the
newest. -/
theorem Ok.rmw {m m' : Mem} {t c : Nat} {op : RmwOp} {signed : Bool} {ord : AtomicOrder}
    {v old : BitVec n} (hw : W.Ok m) (hc : m.current = t) (ht : t < m.threads.size)
    (hcs : m.clocks.size = m.threads.size)
    (h : ((atomicRmwAt c op signed ord nb W.ptr v).run m).run = some (.ok (old, m'))) :
    (W.hist m)[(W.hist m).size - 1]!.Val old ∧ W.Ok m' ∧ W.Op t m m' ∧
      W.Holds m' (op.apply signed old v) ∧
      W.hist m' = (W.hist m).push
        (rmwEnt m' t ord (W.hist m)[(W.hist m).size - 1]! (op.apply signed old v)) ∧
      (ord.isAcq = true →
        VClock.le (W.hist m)[(W.hist m).size - 1]!.relClock (m'.clocks[t]!) = true) := by
  obtain ⟨b, blk, o, li, m₁, pos, hacc, -, hl, hpos, hold, hm'⟩ := atomicRmwAt_ok h
  obtain ⟨blk₀, -, -, -, -, ha₀⟩ := hw.access
  rw [W.sz_eq, ha₀] at hacc
  rw [W.sz_eq] at hl
  cases hacc
  obtain ⟨l, hl', hw₁, hop₁, hh₁, -, -⟩ := hw.prep hc ht hcs rfl hl
  obtain ⟨-, h0, hch, -, -⟩ := hw₁.loc li l hl'
  have hl0 := (loc_get hl').2.2
  have hpl := rmw_chain_pos (m := m₁) (li := li) (by rw [hl0]; exact h0) (by rw [hl0]; exact hch) hpos
  rw [hl0] at hpl hold hm'
  rw [hpl] at hold hm'
  obtain ⟨hw', hop₂, hU, hh, hacq⟩ := hw₁.rmwAt hl' hop₁.current (by rw [hop₁.threads]; exact ht)
    (by rw [hop₁.csize, hop₁.threads]; exact hcs) hm'
  have hsz := hist_size hl'
  refine ⟨?_, hw', hop₁.trans hop₂, hU, by rw [hh, hh₁], by rw [← hh₁]; exact hacq⟩
  rw [← hh₁, hsz]; exact val_of hl' (by omega) hold

theorem loadM_others (m : Mem) (li : Nat) (ord : AtomicOrder) (msg : Msg) {u : Nat}
    (hu : u ≠ m.current) : (loadM m li ord msg).clocks[u]! = m.clocks[u]! := by
  unfold loadM; split
  · simp only [acqM, observeM]; rw [Proto.getElem!_set!_ite, if_neg (fun h => hu h.1)]
  · rfl

/-- A read of message `pos ≥ floorPos` of the word by thread `t` (`loadM`). -/
theorem Ok.read {m m₁ : Mem} {t li pos : Nat} {l : ALoc} {ord : AtomicOrder} (hw₁ : W.Ok m₁)
    (hl : W.Loc m₁ li l) (hop : W.Op t m m₁) (hct : t < m₁.clocks.size) (hlt : pos < l.msgs.size)
    (hfl : floorPos m₁ li ≤ pos) :
    (∀ k < (W.hist m₁).size, VClock.le (W.hist m₁)[k]!.clock (m.clocks[t]!) = true → k ≤ pos) ∧
      (ord.isAcq = true → VClock.le (W.hist m₁)[pos]!.relClock
        ((loadM m₁ li ord (l.msgs[pos]!)).clocks[t]!) = true) ∧
      W.hist (loadM m₁ li ord (l.msgs[pos]!)) = W.hist m₁ ∧
      W.Ok (loadM m₁ li ord (l.msgs[pos]!)) ∧ W.Op t m₁ (loadM m₁ li ord (l.msgs[pos]!)) := by
  have hl0 := (loc_get hl).2.2
  have hg := grows_loadM m₁ li ord (l.msgs[pos]!)
  have hcu : (loadM m₁ li ord (l.msgs[pos]!)).current = t := by rw [loadM_current]; exact hop.current
  have hcs₁ : m₁.current < m₁.clocks.size := by rw [hop.current]; exact hct
  refine ⟨fun k hk hle => ?_, fun hq => ?_, hist_congr hg.atomics hg.blocks,
    hw₁.keep (keep_of hg.blocks hg.atomics hg.footprint hg.threads hg.cle),
    ⟨hcu, hg.threads, hg.waiters, by unfold loadM; split <;> rfl, by unfold loadM; split <;> rfl,
      hg.csize, fun u hu => loadM_others _ _ _ _ (by rw [hop.current]; exact hu),
      hg.cle t, by rw [hg.blocks], fun x _ => by simp only [Mem.heap, hg.blocks],
      fun e he => .inl (hg.footprint ▸ he), .of_eq hg.atomics,
      fun e he => .inl (hg.footprint ▸ he)⟩⟩
  · by_cases hk0 : k = 0
    · omega
    · rw [hist_size hl] at hk
      rw [hist_get hl hk] at hle
      simp only [ent, hk0, ↓reduceIte] at hle
      have hk' : k < (m₁.atomics[li]!).msgs.size := by rw [hl0]; exact hk
      have e : ((m₁.atomics[li]!).msgs[k]'hk').clock = l.msgs[k].clock := by simp [hl0]
      have : k ≤ floorPos m₁ li := le_floorPos hk'
        (by rw [e, hop.current]; exact VClock.le_trans hle hop.mine)
      omega
  · rw [hist_get hl hlt]
    simp only [ent]
    unfold loadM; simp only [hq, ↓reduceIte]
    rw [← hop.current]
    simp only [acqM, observeM]
    rw [Proto.getElem!_set!_ite]
    simp only [true_and, hcs₁, ↓reduceIte]
    rw [← getElem!_pos l.msgs _ hlt]; exact VClock.le_merge_right _ _

/-- The floor property of a read of write `j`: each write that happened before the reader is
`j` or older. -/
def Floor (h : Array Entry) (c : VClock) (j : Nat) : Prop :=
  ∀ k < h.size, VClock.le h[k]!.clock c = true → k ≤ j

/-- An atomic load at the word by thread `t`: it reads write `j`, at least each write that
happened before `t`. -/
theorem Ok.load {m m' : Mem} {t c : Nat} {ord : AtomicOrder} {v : BitVec n} (hw : W.Ok m)
    (hc : m.current = t) (ht : t < m.threads.size) (hcs : m.clocks.size = m.threads.size)
    (h : ((atomicLoadAt c ord nb W.ptr : MemM (BitVec n)).run m).run = some (.ok (v, m'))) :
    ∃ j, j < (W.hist m).size ∧ (W.hist m)[j]!.Val v ∧ Floor (W.hist m) (m.clocks[t]!) j ∧
      (ord.isAcq = true → VClock.le (W.hist m)[j]!.relClock (m'.clocks[t]!) = true) ∧
      W.hist m' = W.hist m ∧ W.Ok m' ∧ W.Op t m m' := by
  obtain ⟨b, blk, o, li, m₁, pos, hacc, -, hl, hpos, hv, rfl⟩ := atomicLoadAt_ok h
  obtain ⟨blk₀, -, -, -, ha₀, -⟩ := hw.access
  rw [W.sz_eq, ha₀] at hacc
  rw [W.sz_eq] at hl
  cases hacc
  obtain ⟨l, hl', hw₁, hop₁, hh₁, -, -⟩ := hw.prep hc ht hcs rfl hl
  have hl0 := (loc_get hl').2.2
  have hlt := readOpts_lt hpos
  rw [hl0] at hlt hv
  rw [hl0]
  have hct : t < m₁.clocks.size := by rw [hop₁.csize, hcs]; exact ht
  obtain ⟨hfl, hacq, hh, hw', hop₂⟩ := hw₁.read (ord := ord) hl' hop₁ hct hlt (floor_le hpos)
  refine ⟨pos, by rw [← hh₁, hist_size hl']; exact hlt, by rw [← hh₁]; exact val_of hl' hlt hv,
    by rw [← hh₁]; exact hfl, by rw [← hh₁]; exact hacq, by rw [hh, hh₁], hw', hop₁.trans hop₂⟩

/-- A `cmpxchg` option is at least the floor. -/
theorem casOpts_floor {m : Mem} {li c pos : Nat} {e : BitVec n} (h : (casOpts m li e)[c]? = some pos) :
    floorPos m li ≤ pos := by
  have hm := Array.mem_of_getElem? h
  unfold casOpts at hm
  obtain ⟨hr, -⟩ := Array.mem_filter.mp hm
  obtain ⟨i, hi⟩ := Array.mem_iff_getElem?.mp hr
  exact floor_le hi

/-- A `cmpxchg` at the word by thread `t`: on success (`none`) an RMW of the newest write, which
holds `exp`; on failure a read with the failure order of write `j`, which does not hold `exp`. -/
theorem Ok.cas {m m' : Mem} {t c : Nat} {succ fail : AtomicOrder} {exp new : BitVec n}
    {r : Option (BitVec n)} (hw : W.Ok m) (hc : m.current = t) (ht : t < m.threads.size)
    (hcs : m.clocks.size = m.threads.size)
    (h : ((cmpxchgAt c succ fail nb W.ptr exp new).run m).run = some (.ok (r, m'))) :
    W.Ok m' ∧ W.Op t m m' ∧
    ((r = none ∧ (W.hist m)[(W.hist m).size - 1]!.Val exp ∧ W.Holds m' new ∧
      W.hist m' = (W.hist m).push (rmwEnt m' t succ (W.hist m)[(W.hist m).size - 1]! new) ∧
      (succ.isAcq = true →
        VClock.le (W.hist m)[(W.hist m).size - 1]!.relClock (m'.clocks[t]!) = true)) ∨
     (∃ j old, r = some old ∧ old ≠ exp ∧ j < (W.hist m).size ∧ (W.hist m)[j]!.Val old ∧
      Floor (W.hist m) (m.clocks[t]!) j ∧
      (fail.isAcq = true → VClock.le (W.hist m)[j]!.relClock (m'.clocks[t]!) = true) ∧
      W.hist m' = W.hist m)) := by
  obtain ⟨b, blk, o, li, m₁, pos, old, hacc, -, hl, hpos, hold, hcase⟩ := cmpxchgAt_ok h
  obtain ⟨blk₀, -, -, -, -, ha₀⟩ := hw.access
  rw [W.sz_eq, ha₀] at hacc
  rw [W.sz_eq] at hl
  cases hacc
  obtain ⟨l, hl', hw₁, hop₁, hh₁, -, -⟩ := hw.prep hc ht hcs rfl hl
  obtain ⟨-, h0, hch, -, -⟩ := hw₁.loc li l hl'
  have hl0 := (loc_get hl').2.2
  have hct : t < m₁.clocks.size := by rw [hop₁.csize, hcs]; exact ht
  have hsz := hist_size hl'
  rcases hcase with ⟨rfl, rfl, -, hm'⟩ | ⟨hne, rfl, hm'⟩
  · have hpl := cas_chain_pos (m := m₁) (li := li) (by rw [hl0]; exact hch) hpos hold
    rw [hl0] at hpl hold hm'
    rw [hpl] at hold hm'
    rw [W.sz_eq] at hm'
    obtain ⟨hw₂, hop₂, hh₂⟩ := hw₁.record hop₁.current
      (by rw [hop₁.threads]; exact ht) (by rw [hop₁.csize, hop₁.threads]; exact hcs)
      (k := .atomicWrite) rfl
    have hl₂ : W.Loc (m₁.recordAt W.b W.o nb .atomicWrite) li l := hl'
    obtain ⟨hw', hop₃, hU, hh, hacq⟩ := hw₂.rmwAt (M := m') (ord := succ) (new := new) hl₂ hop₂.current
      (by rw [hop₂.threads, hop₁.threads]; exact ht)
      (by rw [hop₂.csize, hop₂.threads, hop₁.csize, hop₁.threads]; exact hcs) hm'
    refine ⟨hw', hop₁.trans (hop₂.trans hop₃), .inl ⟨rfl, ?_, hU,
      by rw [hh, hh₂, hh₁], by rw [← hh₁]; exact hacq⟩⟩
    rw [← hh₁, hsz]; exact val_of hl' (by omega) hold
  · have hlt := (casOpts_pos hpos).1
    have hfl := casOpts_floor hpos
    rw [hl0] at hlt hold hm'
    rw [hm']
    obtain ⟨hfl', hacq, hh, hw', hop₂⟩ := hw₁.read (ord := fail) hl' hop₁ hct hlt hfl
    refine ⟨hw', hop₁.trans hop₂, .inr ⟨pos, old, rfl, hne, by rw [← hh₁, hsz]; exact hlt,
      by rw [← hh₁]; exact val_of hl' hlt hold, by rw [← hh₁]; exact hfl',
      by rw [← hh₁]; exact hacq, by rw [hh, hh₁]⟩⟩

/-! ## No error at the word -/

/-- The access to the word, its race check and its location do not fail. -/
theorem Ok.prep_ok {m : Mem} (hw : W.Ok m) (ht : m.current < m.threads.size) {k : AccessKind}
    (hk : k.isAtomic = true) :
    ∃ blk, m.access W.ptr (intSize n) nb = pure (W.b, blk, W.o) ∧
      m.accessW W.ptr (intSize n) nb = pure (W.b, blk, W.o) ∧ NoRace m W.b W.o (intSize n) k ∧
      ∀ e, ((Zig.locIdx W.b W.o (intSize n)).run (m.recordAt W.b W.o (intSize n) k)).run ≠
        some (.error e) := by
  rw [W.sz_eq]
  obtain ⟨blk, -, -, -, ha, haw⟩ := hw.access
  refine ⟨blk, ha, haw, hw.noRace hk ht, fun e => locIdx_noErr_of (fun i hf => ?_)
    (fun hn l hl hb h1 h2 => ?_) e⟩
  · obtain ⟨hi', -, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp hf
    rw [getElem!_pos _ i hi']
    exact (hw.loc i _ ⟨hf, Array.getElem?_eq_getElem hi'⟩).1
  · have ho := hw.only l hl hb (by exact h2) h1
    have := Array.findIdx?_eq_none_iff.mp hn l hl
    simp [hb, ho] at this

/-- The options of an op at the word: a message with a value. -/
theorem Ok.opts {m m₁ : Mem} {li : Nat} {k : AccessKind} (hw : W.Ok m)
    (ht : m.current < m.threads.size) (hcs : m.clocks.size = m.threads.size) (hk : k.isAtomic = true)
    (hl : ((Zig.locIdx W.b W.o (intSize n)).run (m.recordAt W.b W.o (intSize n) k)).run =
      some (.ok (li, m₁))) :
    0 < (m₁.atomics[li]!).msgs.size ∧ (m₁.atomics[li]!).Chain ∧
      ∀ pos < (m₁.atomics[li]!).msgs.size,
        ∃ w, (intOfBytes n ((m₁.atomics[li]!).msgs[pos]!).bytes).run = some (.ok w) := by
  rw [W.sz_eq] at hl
  obtain ⟨l, hl', hw₁, -⟩ := hw.prep rfl ht hcs hk hl
  obtain ⟨-, h0, hch, -, hval⟩ := hw₁.loc li l hl'
  have hl0 := (loc_get hl').2.2
  rw [hl0]
  exact ⟨h0, hch, fun pos hp => by rw [getElem!_pos l.msgs _ hp]; exact hval pos hp⟩

/-- An atomic load at the word does not throw. -/
theorem Ok.load_noErr {m : Mem} {c : Nat} {ord : AtomicOrder} (hw : W.Ok m)
    (ht : m.current < m.threads.size) (hcs : m.clocks.size = m.threads.size)
    (hcr : c < loadCount n ord nb W.ptr m ∨ loadCount n ord nb W.ptr m = 0 ∧ c = 0) (e : Error) :
    ((atomicLoadAt (n := n) c ord nb W.ptr).run m).run ≠ some (.error e) := by
  obtain ⟨blk, ha, -, hnr, hloc⟩ := hw.prep_ok ht (k := .atomicRead) rfl
  refine atomicLoadAt_noErr (loadPrep_noErr (by simpa using ha) (by simpa using hnr)
    (by simpa using hloc)) (fun li opts m₁ hp => ?_) e
  obtain ⟨b, blk', o, ha', -, hl, rfl⟩ := loadPrep_ok hp
  simp only [Bool.false_eq_true, ↓reduceIte] at ha' hl
  rw [ha] at ha'; cases ha'
  obtain ⟨h0, -, hval⟩ := hw.opts ht hcs rfl hl
  have hne := readOpts_ne (li := li) h0
  have hcnt : loadCount n ord nb W.ptr m = (readOpts m₁ li false).size := by
    unfold loadCount; rw [optCount_eq hp]
  have hc : c < (readOpts m₁ li false).size := by rw [hcnt] at hcr; omega
  exact ⟨_, Array.getElem?_eq_getElem hc, hval _ (readOpts_lt (Array.getElem?_eq_getElem hc))⟩

/-- An RMW at the word does not throw. -/
theorem Ok.rmw_noErr {m : Mem} {c : Nat} {op : RmwOp} {signed : Bool} {ord : AtomicOrder}
    {v : BitVec n} (hw : W.Ok m) (ht : m.current < m.threads.size)
    (hcs : m.clocks.size = m.threads.size)
    (hcr : c < rmwCount n ord nb W.ptr m ∨ rmwCount n ord nb W.ptr m = 0 ∧ c = 0) (e : Error) :
    ((atomicRmwAt c op signed ord nb W.ptr v).run m).run ≠ some (.error e) := by
  obtain ⟨blk, -, haw, hnr, hloc⟩ := hw.prep_ok ht (k := .atomicWrite) rfl
  refine atomicRmwAt_noErr (loadPrep_noErr (by simpa using haw) (by simpa using hnr)
    (by simpa using hloc)) (fun li opts m₁ hp => ?_) e
  obtain ⟨b, blk', o, ha', -, hl, rfl⟩ := loadPrep_ok hp
  simp only [↓reduceIte] at ha' hl
  rw [haw] at ha'; cases ha'
  obtain ⟨h0, hch, hval⟩ := hw.opts ht hcs rfl hl
  have hro := readOpts_chain h0 hch
  have hcnt : rmwCount n ord nb W.ptr m = 1 := by
    unfold rmwCount; rw [optCount_eq hp, hro]; rfl
  have hc0 : c = 0 := by rw [hcnt] at hcr; omega
  subst hc0
  exact ⟨(m₁.atomics[li]!).msgs.size - 1, by rw [hro]; rfl, hval _ (by omega)⟩

/-- A `cmpxchg` at the word does not throw. -/
theorem Ok.cas_noErr {m : Mem} {c : Nat} {succ fail : AtomicOrder} {exp new : BitVec n}
    (hw : W.Ok m) (ht : m.current < m.threads.size) (hcs : m.clocks.size = m.threads.size)
    (hcr : c < casCount n succ nb W.ptr exp m ∨ casCount n succ nb W.ptr exp m = 0 ∧ c = 0)
    (e : Error) : ((cmpxchgAt c succ fail nb W.ptr exp new).run m).run ≠ some (.error e) := by
  obtain ⟨blk, -, haw, hnr, hloc⟩ := hw.prep_ok ht (k := .atomicRead) rfl
  have hprep : ∀ e, ((casPrep n nb W.ptr exp).run m).run ≠ some (.error e) :=
    casPrep_noErr haw hnr hloc
  refine cmpxchgAt_noErr hprep (fun li opts m₁ hp => ?_)
    (fun li opts m₁ hp e he => ?_) e
  · obtain ⟨b, blk', o, ha, -, hl, rfl⟩ := casPrep_ok hp
    rw [haw] at ha; cases ha
    obtain ⟨h0, -, hval⟩ := hw.opts ht hcs rfl hl
    have hne := casOpts_ne (e := exp) (m := m₁) (li := li) h0
    have hcnt : casCount n succ nb W.ptr exp m = (casOpts m₁ li exp).size := by
      unfold casCount; rw [optCount_eq hp]
    have hc : c < (casOpts m₁ li exp).size := by rw [hcnt] at hcr; omega
    exact ⟨_, Array.getElem?_eq_getElem hc, hval _ (casOpts_pos (Array.getElem?_eq_getElem hc)).1⟩

  · obtain ⟨b, blk', o, ha, -, hl, -⟩ := casPrep_ok hp
    rw [haw] at ha; cases ha
    rw [W.sz_eq] at hl
    obtain ⟨l, hl', hw₁, hop₁, -⟩ := hw.prep rfl ht hcs rfl hl
    obtain ⟨blk₁, -, ha₁, hnr₁, -⟩ := hw₁.prep_ok (by rw [hop₁.current, hop₁.threads]; exact ht)
      (k := .atomicWrite) rfl
    rw [casMarkWrite_run ha₁ hnr₁] at he
    cases he

/-! ## An op at the word keeps a lock's invariant -/

/-- An op at a word apart from the lock's, which no part and no resource has, keeps the lock's
invariant. -/
theorem _root_.Zig.Conc.Lock.Inv.wordOp {γ : Type} {L : Lock γ} {G : ThreadId → γ} {t : ThreadId}
    {m m' : Mem} (hi : L.Inv G m) (hw : W.Ok m) (hop : W.Op t m m') (hap : Apart L W)
    (hoff : ∀ u, W.Off (L.own G m u)) (hR : ∀ hL, L.R G hL → W.Off hL) : L.Inv G m' := by
  have hsz0 := W.sz_pos
  have hjb : joinedB m' = joinedB m := Lock.joinedB_congr hop.threads
  have hown : L.own G m' = L.own G m := by funext u; unfold Lock.own; rw [hjb]
  have hnw : ∀ x, L.o ≤ x → x < L.o + 4 → ¬ ((L.b, x).1 = W.b ∧ W.o ≤ (L.b, x).2 ∧ (L.b, x).2 < W.o + nb) := by
    rintro x h1 h2 ⟨hb, h3, h4⟩; simp only at hb h3 h4
    rcases hap with h | h | h
    · exact h hb
    · omega
    · omega
  obtain ⟨hblk', hcur⟩ := Lock.word_congr (L := L) (fun x h1 h2 => hop.cells _ (hnw x h1 h2)) hi.blk
  have hU32 : ∀ v, L.U32 m' v ↔ L.U32 m v := fun v => by unfold Lock.U32; rw [hcur]
  have hne : L.b ≠ W.b ∨ L.o ≠ W.o := by
    rcases hap with h | h | h
    · exact .inl h
    · exact .inr (by omega)
    · exact .inr (by omega)
  have hloc : ∀ i l, L.Loc m' i l ↔ L.Loc m i l := fun i l => hop.locs.same L.b L.o hne i l
  have hWb : W.b < m.blocks.size := by
    obtain ⟨blk, hb, -⟩ := hw.blk; exact (Array.getElem?_eq_some_iff.mp hb).1
  -- a new access is at the word, so it touches no heap without the word's bytes
  have hnt : ∀ {h : Heap}, W.Off h → ∀ e ∈ m'.footprint, e ∉ m.footprint → ¬ e.Touches h := by
    intro h ho e he hn ht
    rcases hop.fp e he with h' | ⟨hb, heo, hl, -⟩
    · exact hn h'
    · obtain ⟨x, h1, h2, h3⟩ := ht
      rw [hb] at h3
      rw [heo] at h1; rw [heo, hl] at h2
      rw [ho x h1 (by rcases h2 with h2 | h2 <;> omega)] at h3; exact h3 rfl
  have hsub : ∀ {h : Heap}, W.Off h → h.Sub m.heap → h.Sub m'.heap := fun ho hs l c hc => by
    have hw' : ¬ (l.1 = W.b ∧ W.o ≤ l.2 ∧ l.2 < W.o + nb) := by
      rintro ⟨h1, h2, h3⟩
      obtain ⟨b, x⟩ := l; simp only at h1 h2 h3; subst h1
      rw [ho x h2 h3] at hc; cases hc
    rw [hop.cells l hw']; exact hs l c hc
  refine ⟨?_, hi.pdisj, hi.idle, fun u hu => ?_, hblk', ?_, hi.one,
    ⟨fun l hl hb h1 h2 => ?_, fun i l hl => ?_,
      fun i l hl => (hi.loc.plain i l ((hloc i l).mp hl)).of_fp fun e he =>
        (hop.fp e he).imp id fun h => plainHit_atomic h.2.2.2.1⟩, fun u => hown ▸ hi.off u,
    fun e he hh => ?_, fun i l hl => ?_, fun hF => ?_, hi.res, by rw [hop.waiters]; exact hi.fq,
    fun hp => ?_, fun u hu =>
      let ⟨i, l, hl, hw⟩ := hi.owner u hu; ⟨i, l, (hloc i l).mpr hl, hw⟩⟩
  · rw [hown]
    refine hi.own.keep (by rw [hop.threads]) hop.csize (fun u => hsub (hoff u) (hi.own.sub u))
      (Nat.le_of_eq hop.bsize.symm) (fun u _ => hop.clocks u) (fun e he => ?_)
    by_cases hm : e ∈ m.footprint
    · exact .inl hm
    · refine .inr ⟨?_, fun u => hnt (hoff u) e he hm⟩
      rcases hop.fp e he with h' | ⟨hb, -⟩
      · exact absurd h' hm
      · rw [hb, hop.bsize]; exact hWb
  · rw [hop.threads, hjb]; exact hi.live u hu
  · obtain ⟨w, hw', hu, hz⟩ := hi.word; exact ⟨w, hw', (hU32 _).mpr hu, hz⟩
  · rcases hop.locs.new l hl with h | ⟨hb', ho, hlen⟩
    · exact hi.loc.only l h hb h1 h2
    · rw [ho] at h1; rw [ho, hlen] at h2; rw [hb'] at hb
      rcases hap with h | h | h
      · exact absurd hb.symm h
      · omega
      · omega
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hi.loc.ok i l ((hloc i l).mp hl)
    exact ⟨h1, h2, h3, h4, by rw [h5, hcur]⟩
  · rcases hop.fp e he with h' | ⟨hb, heo, hl, -⟩
    · rcases hi.wfp e h' hh with ⟨ha, hs⟩ | ha
      · exact .inl ⟨ha, hop.someLe hs⟩
      · exact .inr (Lock.LiveLe.mono hop.threads (fun u _ => hop.clocks u) ha)
    · exfalso
      obtain ⟨hb', x, h1, h2, h3, h4⟩ := hh
      rw [hb] at hb'; rw [heo] at h1; rw [heo, hl] at h2
      rcases hap with h | h | h
      · exact h hb'.symm
      · rcases h2 with h2 | h2 <;> omega
      · rcases h2 with h2 | h2 <;> omega
  · obtain ⟨h1, h2⟩ := hi.rel i l ((hloc i l).mp hl)
    exact ⟨hop.someLe h1, fun u hu => VClock.le_trans (h2 u hu) (hop.clocks u)⟩
  · obtain ⟨hL, hRL, hsL, hdj, hoffL, how⟩ := hi.free hF
    refine ⟨hL, hRL, hsub (hR hL hRL) hsL, fun u => hown ▸ hdj u, hoffL, fun e he htc => ?_⟩
    by_cases hm : e ∈ m.footprint
    · rcases how e hm (htc.imp id fun h => by rw [← hop.bsize]; exact h) with h | ⟨i, l, hl, hle⟩
      · exact .inl (Lock.LiveLe.mono hop.threads (fun u _ => hop.clocks u) h)
      · exact .inr ⟨i, l, (hloc i l).mpr hl, hle⟩
    · rcases htc with htc | hbe
      · exact absurd htc (hnt (hR hL hRL) e he hm)
      · rcases hop.fp e he with h' | ⟨hb, -⟩
        · exact absurd h' hm
        · rw [hb, hop.bsize] at hbe; exact absurd hWb (Nat.not_lt.mpr hbe)
  · obtain ⟨v, hv, hq, h1, h2⟩ := hi.wit (hop.waiters ▸ hp)
    exact ⟨v, hop.threads ▸ hv, hop.waiters ▸ hq, h1, fun hh => (hU32 _).mpr (h2 hh)⟩

/-! ## A futex wait at the word

The kernel's compare of a futex wait is a recorded atomic read of the word (`Thread.futexWait`):
an `Op` that keeps the word's writes. -/

section futex

variable {W : Word 32 4}

/-- A futex wait at the word by the current thread `t`: a woken thread goes on; else the
kernel's read of the word is an op `M` that keeps the word's writes, and the thread sleeps (it
joins `waiters`) only if the word holds `e`. -/
theorem Ok.futexWait {m m' : Mem} {t : ThreadId} {e : BitVec 32} {b : Bool} (hw : W.Ok m)
    (hc : m.current = t) (ht : t < m.threads.size) (hcs : m.clocks.size = m.threads.size)
    (h : ((Thread.futexWait W.ptr e).run m).run = some (.ok (b, m'))) :
    (m.woken.contains m.current = true ∧ b = false ∧
      m' = { m with woken := m.woken.erase m.current }) ∨
    (m.woken.contains m.current = false ∧ ∃ M, W.Ok M ∧ W.Op t m M ∧ W.hist M = W.hist m ∧
      ((W.Holds m e ∧ b = true ∧ m' = { M with waiters := M.waiters.push (t, W.ptr) }) ∨
       (b = false ∧ m' = M))) := by
  rcases futexWait_eq h with hwk | ⟨hwk, bid, blk, o, v, ha, -, hv, hcase⟩
  · exact .inl hwk
  obtain ⟨blk₀, hb₀, -, -, ha₀, -⟩ := hw.access
  rw [ha₀] at ha
  cases ha
  obtain ⟨hok, hop, hh⟩ := hw.record (k := .atomicRead) hc ht hcs rfl
  refine .inr ⟨hwk, _, hok, hop, hh, ?_⟩
  rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
  · subst hc; exact .inl ⟨(holds_bytes hb₀).mpr hv, rfl, rfl⟩
  · exact .inr ⟨rfl, rfl⟩

/-- A futex wait at the word has no error. -/
theorem Ok.futexWait_run {m : Mem} {e : BitVec 32} (hw : W.Ok m)
    (ht : m.current < m.threads.size) :
    ∃ b m', ((Thread.futexWait W.ptr e).run m).run = some (.ok (b, m')) := by
  by_cases hwk : m.woken.contains m.current = true
  · exact ⟨_, _, futexWait_run_woken hwk⟩
  · obtain ⟨blk, hb, -, -, ha, -⟩ := hw.access
    obtain ⟨v, hv⟩ := hw.val
    rw [holds_bytes hb] at hv
    exact ⟨_, _, futexWait_run_go (by simpa using hwk) ha (hw.noRace rfl ht) hv⟩

/-- The word is off the lock's word, the threads' parts and the resources: a futex wait at it
keeps the lock's invariant (`Lock.Inv.waitOff`). -/
theorem offWord {γ : Type} {L : Lock γ} {G : ThreadId → γ} {m : Mem} (hw : W.Ok m)
    (hown : ∀ u, W.Off (L.own G m u)) (hR : ∀ hL, L.R G hL → W.Off hL) (hap : Apart L W) :
    L.OffWord G m W.ptr := by
  intro bid blk o ha
  obtain ⟨blk₀, -, -, -, ha₀, -⟩ := hw.access
  rw [ha₀] at ha
  cases ha
  refine ⟨fun u x h1 h2 => hown u x h1 h2, fun hL hRL x h1 h2 => hR hL hRL x h1 h2, ?_⟩
  rcases hap with h | h | h
  · exact .inl (Ne.symm h)
  · exact .inr (.inr h)
  · exact .inr (.inl h)

end futex

end Word

end Conc
end Zig
