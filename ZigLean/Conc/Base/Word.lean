import ZigLean.Conc.Base.Lock
import ZigLean.Conc.Base.Heap
import ZigLean.Conc.Clock

/-!
# A shared atomic word

A word of a sync object that no thread owns: the state and the epoch of an `Io.Condition`, the
state of an `Io.Event`. It is 4 or 8 bytes (`n` = 32 or 64 bits) at offset `o` of block `b`, and
each thread accesses it only with atomic ops (translated std code; the futex under it is the
model). A lock's word owns a resource (`ZigLean/Sep/Full/Lock.lean`); a shared word owns nothing,
so a proof keeps facts about its values and clocks in the rest of its invariant.

- **The writes** (`Word.hist`): the messages of the word's atomic location, oldest first, without
  their ids; before the first atomic op, the block's bytes. The first entry has no clock: a
  thread can always read it or a newer one.
- **The invariant** (`Word.Ok`): the block is live and aligned, no other atomic location overlaps
  the word, the location is an RMW chain of messages of the word's size whose newest has the
  word's bytes, and each access to the word is atomic or happened before every thread of the live
  set (the threads that may still access it; every thread by default). So an atomic op at the word
  by a live thread does not race, and an RMW reads the newest message. A smaller live set keeps
  the word (`Ok.anti`).
- **The writes only grow** (`Word.Prefix`, `Word.Extends`): a step keeps the writes or adds one.
- **The ops**: the record of an atomic access keeps the word (`Ok.record_native`) and finds or
  adds its location (`Ok.prep_native`); a read can read at least the floor (`floor_le`,
  `Word.Floor`); an RMW writes `rmwEnt`. In strict mode no op throws (`Ok.load_noErr`,
  `Ok.rmw_noErr`, `Ok.cas_noErr`), and a futex wait at the word runs (`Ok.futexWait_run`).

This is the permanent vocabulary of a shared word; the native steps over it are in
`ZigLean/Sep/Full/Word.lean`, the legacy part in `ZigLean/Conc/Word.lean`.
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

/-- The access `e` touches a byte of the word (`FootprintEntry.Touches`). -/
def Hits (e : FootprintEntry) : Prop :=
  e.block = W.b ∧ ∃ x, e.off ≤ x ∧ x < e.off + e.len ∧ W.o ≤ x ∧ x < W.o + nb

/-- `h` has no byte of the word. -/
def Off (h : Heap) : Prop := ∀ x, W.o ≤ x → x < W.o + nb → h (W.b, x) = none

/-- A write of the word: its bytes, its clock and its release clock. -/
structure Entry where
  bytes : Array Byte
  clock : VClock
  relClock : VClock
  deriving Inhabited

/-- Message `j` without its id; the first one without its clock. -/
def ent (j : Nat) (x : Msg) : Entry := ⟨x.bytes, if j = 0 then #[] else x.clock, x.relClock⟩

/-- The writes of the word, oldest first (module doc). -/
def hist (m : Mem) : Array Entry :=
  match m.atomics.findIdx? (fun l => l.block == W.b && l.off == W.o) with
  | some i => (m.atomics[i]!).msgs.mapIdx ent
  | none => #[⟨curBytes m W.b W.o nb, #[], #[]⟩]

/-- The value of a write. -/
def Entry.Val {n : Nat} (x : Entry) (v : BitVec n) : Prop := (intOfBytes n x.bytes).run = some (.ok v)

/-- The word holds `v`. -/
def Holds (m : Mem) (v : BitVec n) : Prop :=
  (intOfBytes n (curBytes m W.b W.o nb)).run = some (.ok v)

/-- The word is shared and atomic only (module doc), for the live set `A`: the threads that may
still access the word (a protocol chooses it; every thread by default). A plain access to the
word (a whole read of the struct it is in) happened before every thread of `A`, so each thread of
`A` accesses the word without a race, and a thread that never accesses it again need not be above
it: an op at the word by `t` takes `A t` (`Ok.noRace`). -/
structure Ok (m : Mem) (A : ThreadId → Prop := fun _ => True) : Prop where
  blk : ∃ blk, m.blocks[W.b]? = some blk ∧ blk.live = true ∧ W.o + nb ≤ blk.bytes.size ∧
    (blk.addr + W.o) % nb = 0 ∧ blk.kind ≠ .constGlobal ∧
    blk.kind.mappedLo ≤ W.o
  only : ∀ l ∈ m.atomics, l.block = W.b → l.off < W.o + nb → W.o < l.off + l.len → l.off = W.o
  loc : ∀ i l, W.Loc m i l → l.len = nb ∧ 0 < l.msgs.size ∧ l.Chain ∧
    ALoc.lastBytes l = curBytes m W.b W.o nb ∧
    ∀ j (h : j < l.msgs.size), ∃ v, (intOfBytes n l.msgs[j].bytes).run = some (.ok v)
  wfp : ∀ e ∈ m.footprint, W.Hits e →
    (e.kind.isAtomic = true ∧ SomeLe m e.clock) ∨ AllLeOn A m e.clock
  /-- The word holds a value. -/
  val : ∃ v, W.Holds m v
  /-- Every plain write to the word happened before its newest message. -/
  plain : ∀ i l, W.Loc m i l → PlainLe m W.b W.o nb l.lastClock

/-- What a step that keeps the word keeps of a cell of it: the byte, the block's address, and
whether the block is a `const` global. Not the block's size or mapping start: the owner of the
block's extent can resize it, or unmap pages below the word (`Cell.norm` of the full-state
logic keeps the same). -/
def cellKey (c : Cell) : Byte × Nat × Bool := (c.byte, c.addr, c.kind == .constGlobal)

/-- The shapes (block, offset, length) of the atomic locations. -/
def keys (m : Mem) : Array (BlockId × Nat × Nat) := m.atomics.map fun l => (l.block, l.off, l.len)

variable {W} {A : ThreadId → Prop}

/-! ## The atomic layout -/

theorem mem_keys {m : Mem} {k : BlockId × Nat × Nat} :
    k ∈ keys m ↔ ∃ l ∈ m.atomics, (l.block, l.off, l.len) = k := by
  unfold keys; exact Array.mem_map

/-- A location replaced by one of the same shape (an RMW's new message). -/
theorem keys_set {m m' : Mem} {i : Nat} {l l' : ALoc} (hl : m.atomics[i]? = some l)
    (hk : (l'.block, l'.off, l'.len) = (l.block, l.off, l.len))
    (h : m'.atomics = m.atomics.set! i l') : keys m' = keys m := by
  unfold keys; rw [h]
  apply Array.ext (by simp)
  intro j h1 h2
  simp only [Array.getElem_map, Array.set!_eq_setIfInBounds]
  rw [Array.getElem_setIfInBounds]
  split
  · rename_i e; subst e
    rw [(Array.getElem?_eq_some_iff.mp hl).2]; exact hk
  · rfl

/-! ## Basic facts -/

/-- The same cells at the word, up to `cellKey`: the same facts of its block, and the same
bytes. -/
theorem congr {m m' : Mem}
    (hw : ∀ x, W.o ≤ x → x < W.o + nb →
      (m'.heap (W.b, x)).map cellKey = (m.heap (W.b, x)).map cellKey)
    (hb : ∃ blk, m.blocks[W.b]? = some blk ∧ blk.live = true ∧ W.o + nb ≤ blk.bytes.size ∧
      (blk.addr + W.o) % nb = 0 ∧ blk.kind ≠ .constGlobal ∧ blk.kind.mappedLo ≤ W.o) :
    (∃ blk, m'.blocks[W.b]? = some blk ∧ blk.live = true ∧ W.o + nb ≤ blk.bytes.size ∧
      (blk.addr + W.o) % nb = 0 ∧ blk.kind ≠ .constGlobal ∧ blk.kind.mappedLo ≤ W.o) ∧
      curBytes m' W.b W.o nb = curBytes m W.b W.o nb := by
  have hsz0 := W.sz_pos
  obtain ⟨blk, hblk, hl, hs, ha, hk, hlo⟩ := hb
  -- each byte of the word: a live byte of the same block in `m'`, with the same key
  have hcell : ∀ x (_ : W.o ≤ x) (_ : x < W.o + nb), ∃ blk', m'.blocks[W.b]? = some blk' ∧
      blk'.live = true ∧ ∃ h' : x < blk'.bytes.size, blk'.kind.mappedLo ≤ x ∧
        cellKey ⟨blk'.bytes[x], blk'.addr, blk'.bytes.size, blk'.kind⟩ =
          cellKey ⟨blk.bytes[x]'(by omega), blk.addr, blk.bytes.size, blk.kind⟩ := by
    intro x h1 h2
    have hc : m.heap (W.b, x) =
        some ⟨blk.bytes[x]'(by omega), blk.addr, blk.bytes.size, blk.kind⟩ := by
      simp only [Mem.heap, hblk]; rw [dite_eq_left_of_eq_true (eq_true ⟨hl, by omega, by omega⟩)]
    have hc' := hw x h1 h2
    rw [hc] at hc'
    cases e : m'.heap (W.b, x) with
    | none => rw [e] at hc'; cases hc'
    | some c =>
      rw [e] at hc'
      obtain ⟨blk', hblk', hl', ho', rfl⟩ := Mem.heap_some e
      obtain ⟨blk'', hblk'', hlo'⟩ := Mem.heap_some_lo e
      rw [hblk'] at hblk''; cases hblk''
      exact ⟨blk', hblk', hl', ho', hlo', Option.some.inj hc'⟩
  obtain ⟨blk', hblk', hl', h0, hlo', hn0⟩ := hcell W.o (Nat.le_refl _) (by omega)
  have hA : blk'.addr = blk.addr := by
    have := congrArg (fun k => k.2.1) hn0; simpa [cellKey] using this
  have hK : (blk'.kind == .constGlobal) = (blk.kind == .constGlobal) := by
    have := congrArg (fun k => k.2.2) hn0; simpa [cellKey] using this
  have hsz : W.o + nb ≤ blk'.bytes.size := by
    obtain ⟨blk₃, h₃, -, h3, -⟩ := hcell (W.o + (nb - 1)) (by omega) (by omega)
    rw [hblk'] at h₃; cases h₃; omega
  refine ⟨⟨blk', hblk', hl', hsz, by rw [hA]; exact ha, fun e => hk ?_, hlo'⟩, ?_⟩
  · rw [e] at hK; simpa using hK.symm
  · unfold curBytes; rw [hblk, hblk']
    simp only [Option.map_some, Option.getD_some]
    apply Array.ext (by simp; omega)
    intro i h1 h2
    simp only [Array.size_extract] at h1 h2
    rw [Array.getElem_extract, Array.getElem_extract]
    obtain ⟨blk₃, h₃, -, h3, -, hn⟩ := hcell (W.o + i) (by omega) (by omega)
    rw [hblk'] at h₃; cases h₃
    have := congrArg (fun k => k.1) hn; simpa [cellKey] using this

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
    W.hist m = #[⟨curBytes m W.b W.o nb, #[], #[]⟩] := by
  unfold hist
  cases hf : m.atomics.findIdx? (fun l => l.block == W.b && l.off == W.o) with
  | none => rfl
  | some i => exact absurd (loc_of_find hf) (h _ _)

/-- An access that overlaps the word hits it. -/
theorem hits_of {e : FootprintEntry} (hb : e.block = W.b) (hel : 0 < e.len)
    (h1 : W.o < e.off + e.len) (h2 : e.off < W.o + nb) : W.Hits e := by
  have hsz0 := W.sz_pos
  by_cases ho : e.off ≤ W.o
  · exact ⟨hb, W.o, ho, h1, Nat.le_refl _, by omega⟩
  · exact ⟨hb, e.off, Nat.le_refl _, by omega, by omega, h2⟩

/-- A plain write to a byte of the word hits it. -/
theorem hits_of_plain {e : FootprintEntry} (h : plainHit W.b W.o nb e = true) : W.Hits e :=
  have ⟨_, hel, h1, h2⟩ := plainHit_range h
  hits_of (plainHit_block h) hel h1 h2

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
theorem Ok.cell {m : Mem} (hw : W.Ok m A) {x : Nat} (h1 : W.o ≤ x) (h2 : x < W.o + nb) :
    m.heap (W.b, x) ≠ none := by
  obtain ⟨blk, hb, hl, hs, -, -, hlo⟩ := hw.blk
  simp only [Mem.heap, hb]
  rw [dite_eq_left_of_eq_true (eq_true ⟨hl, by omega, by omega⟩)]
  simp

/-- The word as the block's bytes. -/
theorem holds_bytes {m : Mem} {blk : Block} {v : BitVec n} (hb : m.blocks[W.b]? = some blk) :
    W.Holds m v ↔ (intOfBytes n (blk.bytes.extract W.o (W.o + nb))).run = some (.ok v) := by
  unfold Word.Holds curBytes; rw [hb]; rfl

/-- The word holds the value of its newest write. -/
theorem Ok.holds_last {m : Mem} (hw : W.Ok m A) {v : BitVec n} :
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

/-- A narrowing of an access that hits the word is one that hits it. -/
theorem hits_narrows {e e₀ : FootprintEntry} (hn : e.Narrows e₀) (h : W.Hits e) : W.Hits e₀ := by
  obtain ⟨-, hb, -, ho, hl, -⟩ := hn
  obtain ⟨hb', x, h1, h2, h3, h4⟩ := h
  exact ⟨hb.symm.trans hb', x, by omega, by omega, h3, h4⟩

/-! ## The writes only grow

A protocol relates the memories at two stops of a thread only through one-state facts (`Proto.WP`
resumes a stop in every state its invariant allows). So a proof that compares the word's writes
at a call with those at a later stop keeps a snapshot `h` of the writes in its ghost value and
an invariant that `h` stays a prefix of the writes (`Prefix`). Every step keeps or extends the
writes (`Extends`): it keeps them (`Extends.of_eq`: a step that keeps the word, a lock step, a
framed step, a fork, a load, a failed `cmpxchg`, a futex op) or adds one (`Extends.of_push`: an
RMW, a successful `cmpxchg`), so a prefix stays one (`Prefix.extend`). The instances for the
native steps are in `ZigLean/Sep/Full/Word.lean`. -/

variable (W) in
/-- `h` is a prefix of the word's writes at `m`. -/
def Prefix (h : Array Entry) (m : Mem) : Prop := ∃ r, W.hist m = h ++ r

variable (W) in
/-- The word's writes at `m'` extend those at `m`. -/
def Extends (m m' : Mem) : Prop := W.Prefix (W.hist m) m'

theorem Prefix.self (m : Mem) : W.Prefix (W.hist m) m := ⟨#[], Array.append_empty.symm⟩

theorem Prefix.extend {h : Array Entry} {m m' : Mem} (hp : W.Prefix h m) (hg : W.Extends m m') :
    W.Prefix h m' := by
  obtain ⟨r, hr⟩ := hp
  obtain ⟨r', hr'⟩ := hg
  exact ⟨r ++ r', by rw [hr', hr, Array.append_assoc]⟩

theorem Prefix.size_le {h : Array Entry} {m : Mem} (hp : W.Prefix h m) :
    h.size ≤ (W.hist m).size := by
  obtain ⟨r, hr⟩ := hp
  rw [hr, Array.size_append]; omega

/-- A write of the snapshot is the word's write at the same index. -/
theorem Prefix.get {h : Array Entry} {m : Mem} (hp : W.Prefix h m) {j : Nat} (hj : j < h.size) :
    (W.hist m)[j]! = h[j]! := by
  obtain ⟨r, hr⟩ := hp
  rw [hr, getElem!_pos (h ++ r) j (by rw [Array.size_append]; omega), getElem!_pos h j hj,
    Array.getElem_append_left hj]

theorem Extends.refl (m : Mem) : W.Extends m m := Prefix.self m

theorem Extends.trans {m m' m'' : Mem} (h₁ : W.Extends m m') (h₂ : W.Extends m' m'') :
    W.Extends m m'' :=
  h₁.extend h₂

/-- A step that keeps the writes. -/
theorem Extends.of_eq {m m' : Mem} (he : W.hist m' = W.hist m) : W.Extends m m' :=
  ⟨#[], by rw [he, Array.append_empty]⟩

/-- A step that adds a write. -/
theorem Extends.of_push {m m' : Mem} {e : Entry} (he : W.hist m' = (W.hist m).push e) :
    W.Extends m m' :=
  ⟨#[e], by rw [he, Array.push_eq_append]⟩

/-- A step that keeps the atomic locations and the blocks (a futex wake, a change of the futex
queue or of the clocks). -/
theorem Extends.congr {m m' : Mem} (ha : m'.atomics = m.atomics) (hb : m'.blocks = m.blocks) :
    W.Extends m m' :=
  .of_eq (hist_congr ha hb)

/-- A step tick (`Zig.tick`, `Mem.ticked`) keeps the word: it changes only the step count. -/
theorem Ok.ticked {m : Mem} (hw : W.Ok m A) : W.Ok { m with ticks := m.ticks + 1 } A :=
  ⟨hw.blk, hw.only, hw.loc, hw.wfp, hw.val, hw.plain⟩

/-- **A smaller live set keeps the word**: a thread that will not access the word again leaves
the set (a `WaitGroup`'s task after its last op at the group's word). -/
theorem Ok.anti {m : Mem} {B : ThreadId → Prop} (hw : W.Ok m A) (hB : ∀ u, B u → A u) :
    W.Ok m B :=
  ⟨hw.blk, hw.only, hw.loc, fun e he hh => (hw.wfp e he hh).imp_right (·.anti hB), hw.val,
    hw.plain⟩

/-- A thread of the live set: the word for the live set of that thread alone (its op does not
race; `Ok.noRace`). -/
theorem Ok.single {m : Mem} {t : ThreadId} (hw : W.Ok m A) (ht : A t) : W.Ok m (· = t) :=
  hw.anti fun u hu => by subst hu; exact ht

/-- Two live sets of the word make their union one. -/
theorem Ok.union {m : Mem} {B : ThreadId → Prop} (hA : W.Ok m A) (hB : W.Ok m B) :
    W.Ok m (fun u => A u ∨ B u) := by
  refine ⟨hA.blk, hA.only, hA.loc, fun e he hh => ?_, hA.val, hA.plain⟩
  rcases hA.wfp e he hh with h | h
  · exact .inl h
  rcases hB.wfp e he hh with h' | h'
  · exact .inl h'
  exact .inr fun u hu hu' => hu'.elim (h u hu) (h' u hu)

/-- The word for every thread is the word for each live set. -/
theorem Ok.on {m : Mem} (hw : W.Ok m) (A : ThreadId → Prop) : W.Ok m A := hw.anti fun _ _ => trivial

/-! ## The access, the record and the location of an atomic op -/

/-- Thread `t`'s clock is the clock of a recorded access to the word (an RMW's message clock is
covered, `FStepIn.rmwM`). -/
def Rec (m : Mem) (t : ThreadId) : Prop :=
  ∃ e ∈ m.footprint, e.block = W.b ∧ e.off = W.o ∧ 0 < e.len ∧ e.clock = m.clocks[t]!

/-- A recorded access to the word by the current thread `t` is at its clock. -/
theorem rec_recordAt {m : Mem} {t : ThreadId} {k : AccessKind} (hc : m.current = t)
    (hcs : t < m.clocks.size) : W.Rec (m.recordAt W.b W.o nb k) t := by
  subst hc
  rw [Rec, recordAt_clock hcs]
  exact ⟨_, Array.mem_push_self, rfl, rfl, W.sz_pos, rfl⟩

/-- The word's access: no error. -/
theorem Ok.access {m : Mem} (hw : W.Ok m A) :
    ∃ blk, m.blocks[W.b]? = some blk ∧ blk.live = true ∧ W.o + nb ≤ blk.bytes.size ∧
      m.access W.ptr nb nb = pure (W.b, blk, W.o) ∧ m.accessW W.ptr nb nb = pure (W.b, blk, W.o) := by
  obtain ⟨blk, hb, hl, hs, ha, hk⟩ := hw.blk
  have hacc : m.access W.ptr nb nb = pure (W.b, blk, W.o) := by
    have := access_of (p := W.ptr) (n := nb) (a := nb) (m := m) rfl hb hl (by simp [Word.ptr])
      (by simp only [Word.ptr]; omega) (by simpa [Word.ptr] using ha) (by simpa [Word.ptr] using hk.2)
    simpa [Word.ptr] using this
  refine ⟨blk, hb, hl, hs, hacc, ?_⟩
  unfold Mem.accessW; rw [hacc]
  simp [hk, pure, bind, ExceptT.bind, ExceptT.mk, ExceptT.pure, ExceptT.bindCont]

/-- Recording an atomic access preserves validity and history directly. No operation-summary
type occurs in the statement or proof. -/
theorem Ok.record_native {m : Mem} {t : ThreadId} {k : AccessKind} (hw : W.Ok m A)
    (hc : m.current = t) (ht : t < m.threads.size) (hcs : m.clocks.size = m.threads.size)
    (hk : k.isAtomic = true) :
    W.Ok (m.recordAt W.b W.o nb k) A ∧ W.hist (m.recordAt W.b W.o nb k) = W.hist m := by
  subst hc
  have hct : m.current < m.clocks.size := by rw [hcs]; exact ht
  -- the record
  let mr := m.recordAt W.b W.o nb k
  have hrc : ∀ u : Nat, VClock.le (m.clocks[u]!) (mr.clocks[u]!) = true :=
    recordAt_le m _ _ _ _
  have hrt : mr.clocks[m.current]! = VClock.bump (m.clocks[m.current]!) m.current :=
    recordAt_clock hct
  have hcur : curBytes mr W.b W.o nb = curBytes m W.b W.o nb := curBytes_congr rfl _ _ _
  have hwr : W.Ok mr A := by
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
      · exact .inl ⟨ha, someLe_mono (m := m) (m' := mr) rfl (fun u _ => hrc u) hs⟩
      · exact .inr (allLeOn_mono (m := m) (m' := mr) rfl (fun u _ => hrc u) ha)
    · refine .inl ⟨hk, m.current, ht, ?_⟩
      show VClock.le _ (mr.clocks[m.current]!) = true
      rw [hrt]; exact VClock.le_refl _
  exact ⟨hwr, hist_congr rfl rfl⟩

/-- Actual valid-word preparation preserves validity, history and the recorded access without
passing through the old operation summary. -/
theorem Ok.prep_native {m m₁ : Mem} {t li : Nat} {k : AccessKind} (hw : W.Ok m A)
    (hc : m.current = t) (ht : t < m.threads.size) (hcs : m.clocks.size = m.threads.size)
    (hk : k.isAtomic = true)
    (h : ((locIdx W.b W.o nb).run (m.recordAt W.b W.o nb k)).run = some (.ok (li, m₁))) :
    ∃ l, W.Loc m₁ li l ∧ W.Ok m₁ A ∧ W.hist m₁ = W.hist m ∧ m₁.blocks = m.blocks ∧
      m₁.seen = m.seen ∧ W.Rec m₁ t := by
  subst hc
  let mr := m.recordAt W.b W.o nb k
  have hcur : curBytes mr W.b W.o nb = curBytes m W.b W.o nb := curBytes_congr rfl _ _ _
  obtain ⟨hwr, -⟩ := hw.record_native rfl ht hcs hk
  have hrec : W.Rec mr m.current := rec_recordAt rfl (by rw [hcs]; exact ht)
  -- the location
  cases hf : mr.atomics.findIdx? (fun l => l.block == W.b && l.off == W.o) with
  | some i =>
    have hl := loc_of_find hf
    obtain ⟨hlen, -, -, hlast, -⟩ := hwr.loc i _ hl
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
        simpa [ALoc.lastClock, nl, firstLoc, firstMsg] using plainLe_plainClock mr W.b W.o nb e he hh⟩,
      ?_, rfl, rfl, hrec⟩
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

/-- An atomic access to the word by a thread of the live set does not race. -/
theorem Ok.noRace {m : Mem} (hw : W.Ok m A) {k : AccessKind} (hk : k.isAtomic = true)
    (ht : m.current < m.threads.size) (hA : A m.current) : NoRace m W.b W.o nb k := by
  refine noRace_of_pos fun e he hb hel h1 h2 => ?_
  rcases hw.wfp e he (hits_of hb hel h1 h2) with ⟨ha, -⟩ | h
  · refine .inr ?_; unfold racePair; simp [ha, hk]
  · exact .inl (h _ ht hA)

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
    if ord.isRel then VClock.merge last.relClock (M.clocks[t]!) else last.relClock⟩

/-- Write `j` of the word, from the location. -/
theorem hist_size {m : Mem} {i : Nat} {l : ALoc} (hl : W.Loc m i l) : (W.hist m).size = l.msgs.size := by
  rw [hist_loc hl]; simp

/-- The value of message `j`, as the value of write `j`. -/
theorem val_of {m : Mem} {i : Nat} {l : ALoc} (hl : W.Loc m i l) {j : Nat} (hj : j < l.msgs.size)
    {v : BitVec n} (h : (intOfBytes n (l.msgs[j]!).bytes).run = some (.ok v)) :
    (W.hist m)[j]!.Val v := by
  rw [hist_get hl hj]; unfold Entry.Val ent; rw [← getElem!_pos l.msgs _ hj]; exact h

theorem loadM_others (m : Mem) (li : Nat) (ord : AtomicOrder) (msg : Msg) {u : Nat}
    (hu : u ≠ m.current) : (loadM m li ord msg).clocks[u]! = m.clocks[u]! := by
  unfold loadM; split
  · simp only [acqM, observeM]; rw [Proto.getElem!_set!_ite, if_neg (fun h => hu h.1)]
  · rfl

/-- The floor property of a read of write `j`: each write that happened before the reader is
`j` or older. -/
def Floor (h : Array Entry) (c : VClock) (j : Nat) : Prop :=
  ∀ k < h.size, VClock.le h[k]!.clock c = true → k ≤ j

/-- A `cmpxchg` option is at least the floor. -/
theorem casOpts_floor {m : Mem} {li c pos : Nat} {e : BitVec n} (h : (casOpts m li e)[c]? = some pos) :
    floorPos m li ≤ pos := by
  have hm := Array.mem_of_getElem? h
  unfold casOpts at hm
  obtain ⟨hr, -⟩ := Array.mem_filter.mp hm
  obtain ⟨i, hi⟩ := Array.mem_iff_getElem?.mp hr
  exact floor_le hi

/-! ## No error at the word -/

/-- The access to the word, its race check and its location do not fail. -/
theorem Ok.prep_ok {m : Mem} (hw : W.Ok m A) (ht : m.current < m.threads.size)
    (hA : A m.current) {k : AccessKind} (hk : k.isAtomic = true) :
    ∃ blk, m.access W.ptr (intSize n) nb = pure (W.b, blk, W.o) ∧
      m.accessW W.ptr (intSize n) nb = pure (W.b, blk, W.o) ∧ NoRace m W.b W.o (intSize n) k ∧
      ∀ e, ((Zig.locIdx W.b W.o (intSize n)).run (m.recordAt W.b W.o (intSize n) k)).run ≠
        some (.error e) := by
  rw [W.sz_eq]
  obtain ⟨blk, -, -, -, ha, haw⟩ := hw.access
  refine ⟨blk, ha, haw, hw.noRace hk ht hA, fun e => locIdx_noErr_of (fun i hf => ?_)
    (fun hn l hl hb h1 h2 => ?_) e⟩
  · obtain ⟨hi', -, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp hf
    rw [getElem!_pos _ i hi']
    exact (hw.loc i _ ⟨hf, Array.getElem?_eq_getElem hi'⟩).1
  · have ho := hw.only l hl hb (by exact h2) h1
    have := Array.findIdx?_eq_none_iff.mp hn l hl
    simp [hb, ho] at this

/-- The options of an op at the word: a message with a value. -/
theorem Ok.opts {m m₁ : Mem} {li : Nat} {k : AccessKind} (hw : W.Ok m A)
    (ht : m.current < m.threads.size) (hcs : m.clocks.size = m.threads.size) (hk : k.isAtomic = true)
    (hl : ((Zig.locIdx W.b W.o (intSize n)).run (m.recordAt W.b W.o (intSize n) k)).run =
      some (.ok (li, m₁))) :
    0 < (m₁.atomics[li]!).msgs.size ∧ (m₁.atomics[li]!).Chain ∧
      ∀ pos < (m₁.atomics[li]!).msgs.size,
        ∃ w, (intOfBytes n ((m₁.atomics[li]!).msgs[pos]!).bytes).run = some (.ok w) := by
  rw [W.sz_eq] at hl
  obtain ⟨l, hl', hw₁, -⟩ := hw.prep_native rfl ht hcs hk hl
  obtain ⟨-, h0, hch, -, hval⟩ := hw₁.loc li l hl'
  have hl0 := (loc_get hl').2.2
  rw [hl0]
  exact ⟨h0, hch, fun pos hp => by rw [getElem!_pos l.msgs _ hp]; exact hval pos hp⟩

/-- An atomic load at the word does not throw. -/
theorem Ok.load_noErr {m : Mem} {c : Nat} {ord : AtomicOrder} (hw : W.Ok m A)
    (ht : m.current < m.threads.size) (hA : A m.current) (hcs : m.clocks.size = m.threads.size)
    (hcr : c < loadCount n ord nb W.ptr m ∨ loadCount n ord nb W.ptr m = 0 ∧ c = 0) (e : Error) :
    ((atomicLoadAt (n := n) c ord nb W.ptr).run m).run ≠ some (.error e) := by
  obtain ⟨blk, ha, -, hnr, hloc⟩ := hw.prep_ok ht hA (k := .atomicRead) rfl
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
    {v : BitVec n} (hw : W.Ok m A) (ht : m.current < m.threads.size) (hA : A m.current)
    (hcs : m.clocks.size = m.threads.size)
    (hcr : c < rmwCount n ord nb W.ptr m ∨ rmwCount n ord nb W.ptr m = 0 ∧ c = 0) (e : Error) :
    ((atomicRmwAt c op signed ord nb W.ptr v).run m).run ≠ some (.error e) := by
  obtain ⟨blk, -, haw, hnr, hloc⟩ := hw.prep_ok ht hA (k := .atomicWrite) rfl
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
    (hw : W.Ok m A) (ht : m.current < m.threads.size) (hA : A m.current)
    (hcs : m.clocks.size = m.threads.size)
    (hcr : c < casCount n succ nb W.ptr exp m ∨ casCount n succ nb W.ptr exp m = 0 ∧ c = 0)
    (e : Error) : ((cmpxchgAt c succ fail nb W.ptr exp new).run m).run ≠ some (.error e) := by
  obtain ⟨blk, -, haw, hnr, hloc⟩ := hw.prep_ok ht hA (k := .atomicRead) rfl
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
    obtain ⟨l, hl', hw₁, -⟩ := hw.prep_native rfl ht hcs rfl hl
    have ht₁ : m₁.current < m₁.threads.size ∧ A m₁.current := by
      obtain ⟨_, _, _, rfl⟩ := locIdx_updates hl
      exact ⟨ht, hA⟩
    obtain ⟨blk₁, -, ha₁, hnr₁, -⟩ := hw₁.prep_ok ht₁.1 ht₁.2 (k := .atomicWrite) rfl
    rw [casMarkWrite_run ha₁ hnr₁] at he
    cases he

/-! ## A futex wait at the word

The kernel's compare of a futex wait is a recorded atomic read of the word (`Thread.futexWait`). -/

section futex

variable {W : Word 32 4}

/-- A futex wait at the word has no error. -/
theorem Ok.futexWait_run {m : Mem} {e : BitVec 32} (hw : W.Ok m A)
    (ht : m.current < m.threads.size) (hA : A m.current := by trivial) :
    ∃ b m', ((Thread.futexWait W.ptr e).run m).run = some (.ok (b, m')) := by
  by_cases hwk : m.woken.contains m.current = true
  · exact ⟨_, _, futexWait_run_woken hwk⟩
  · obtain ⟨blk, hb, -, -, ha, -⟩ := hw.access
    obtain ⟨v, hv⟩ := hw.val
    rw [holds_bytes hb] at hv
    exact ⟨_, _, futexWait_run_go (by simpa using hwk) ha (hw.noRace rfl ht hA) hv⟩

end futex

end Word

end Conc
end Zig
