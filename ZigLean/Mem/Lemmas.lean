import ZigLean.Mem.Enc
import ZigLean.Union
import ZigLean.Simp

/-!
# Lemmas about memory

The run of `loadBytes`/`storeBytes` when the access succeeds, what a store does to other
accesses, and that a store to a `const` global throws `.illegal`. The round trips
(`LawfulEnc`) of some integer widths and of error unions, and a field read of an `extern` union.
`M17` builds separation logic on these.
-/

namespace Zig

attribute [zig_unfold] callM callR

/-! ## Pointer bytes as integers (MM-11) -/

/-- A load's decode is the plain decode whenever that succeeds. -/
theorem decodeLoad_of_decode {α : Type} [Enc α] {blocks : Array Block} {bs : Array Byte} {v : α}
    (h : Enc.decode bs = pure v) : decodeLoad blocks bs = pure v := by
  unfold decodeLoad; rw [h]; rfl

/-- `decodeLoad_of_decode` in `ExceptT.run` form. -/
theorem decodeLoad_run_of_decode {α : Type} [Enc α] {blocks : Array Block} {bs : Array Byte}
    {v : α} (h : (Enc.decode bs : Result α).run = some (.ok v)) :
    (decodeLoad blocks bs : Result α).run = some (.ok v) :=
  decodeLoad_of_decode h

/-- A successful load decode: the plain decode, or (pointer bytes read as an integer) the decode
of the bytes with the pointer bytes exposed as addresses. -/
theorem decodeLoad_ok {α : Type} [Enc α] {blocks : Array Block} {bs : Array Byte} {v : α}
    (h : (decodeLoad blocks bs).run = some (.ok v)) :
    (Enc.decode bs : Result α).run = some (.ok v) ∨
      ((Enc.decode bs : Result α).run = some (.error .unspecified) ∧
        (Enc.decode (exposeBytes blocks bs) : Result α).run = some (.ok v)) := by
  unfold decodeLoad at h
  simp only [ExceptT.run_mk] at h
  split at h
  · rename_i heq
    split at h
    · exact .inr ⟨heq, h⟩
    · cases h
  · exact .inl h

/-! ## Stack budget (MM-5) -/

/-- Without a stack budget (`stackLimit = none`, every generated `mem0`), a frame is charged
and never overflows. A statement over such a memory carries premise STK-01. -/
theorem enterFrame_run_none {m : Mem} (h : m.stackLimit = none) (bytes : Nat) :
    (enterFrame bytes).run m = pure ((), { m with stackUsed := m.stackUsed + (frameBase + bytes) }) := by
  simp [enterFrame, h, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    set, StateT.set, MonadStateOf.set, pure, StateT.pure, ExceptT.pure, ExceptT.mk, ExceptT.bind,
    ExceptT.bindCont]

/-- A frame that fits in the budget is charged. -/
theorem enterFrame_run_fits {m : Mem} {limit bytes : Nat} (h : m.stackLimit = some limit)
    (hfit : m.stackUsed + (frameBase + bytes) ≤ limit) :
    (enterFrame bytes).run m = pure ((), { m with stackUsed := m.stackUsed + (frameBase + bytes) }) := by
  have : ¬ limit < m.stackUsed + (frameBase + bytes) := by omega
  simp [enterFrame, h, this, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get,
    StateT.get, set, StateT.set, MonadStateOf.set, pure, StateT.pure, ExceptT.pure, ExceptT.mk,
    ExceptT.bind, ExceptT.bindCont]

/-- A frame that does not fit in the budget overflows the stack. -/
theorem enterFrame_overflow {m : Mem} {limit bytes : Nat} (h : m.stackLimit = some limit)
    (hover : limit < m.stackUsed + (frameBase + bytes)) :
    ((enterFrame bytes).run m).run = some (.error .stackOverflow) := by
  simp [enterFrame, h, hover, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get,
    StateT.get, throw, throwThe, MonadExceptOf.throw, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
    pure, ExceptT.pure, StateT.lift, ExceptT.run]

/-- Releasing a frame restores the bytes that `enterFrame` charged. -/
theorem leaveFrame_run (m : Mem) (bytes : Nat) :
    (leaveFrame bytes).run m = pure ((), { m with stackUsed := m.stackUsed - (frameBase + bytes) }) := rfl

/-- An access that succeeds: its block is live, the bytes are in the block, and the address is
aligned. -/
theorem access_eq {m : Mem} {p : Ptr} {n a : Nat} {b : BlockId} {blk : Block} {o : Nat}
    (h : m.access p n a = pure (b, blk, o)) :
    p.block = some b ∧ m.blocks[b]? = some blk ∧ blk.live ∧ 0 ≤ p.off ∧
      p.off + n ≤ blk.bytes.size ∧ (blk.addr + p.off.toNat) % a = 0 ∧ o = p.off.toNat := by
  unfold Mem.access at h
  split at h
  · simp only [throw, throwThe, MonadExceptOf.throw, ExceptT.mk, pure, ExceptT.pure] at h; cases h
  · rename_i b' hb
    split at h
    · simp only [throw, throwThe, MonadExceptOf.throw, ExceptT.mk, pure, ExceptT.pure] at h; cases h
    · rename_i blk' hblk
      split at h
      · rename_i hc
        simp [pure, ExceptT.pure, ExceptT.mk] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨hb, hblk, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, rfl⟩
      · simp only [throw, throwThe, MonadExceptOf.throw, ExceptT.mk, pure, ExceptT.pure] at h
        cases h

theorem access_of {m : Mem} {p : Ptr} {n a : Nat} {b : BlockId} {blk : Block}
    (hb : p.block = some b) (hblk : m.blocks[b]? = some blk) (hl : blk.live) (h0 : 0 ≤ p.off)
    (hn : p.off + n ≤ blk.bytes.size) (ha : (blk.addr + p.off.toNat) % a = 0) :
    m.access p n a = pure (b, blk, p.off.toNat) := by
  simp [Mem.access, hb, hblk, hl, h0, hn, ha]

/-! ### Pointer formation (`ptrProject`, MM-3) -/

@[simp] theorem Ptr.add_zero (p : Ptr) : p.add 0 = p := by cases p; simp [Ptr.add]

@[simp] theorem Ptr.add_block (p : Ptr) (n : Int) : (p.add n).block = p.block := rfl

theorem Ptr.add_off (p : Ptr) (n : Int) : (p.add n).off = p.off + n := rfl

@[simp] theorem Ptr.elem_block (p : Ptr) (size : Nat) (i : BitVec 64) :
    (p.elem size i).block = p.block := rfl

@[simp] theorem Ptr.elemSub_block (p : Ptr) (size : Nat) (i : BitVec 64) :
    (p.elemSub size i).block = p.block := rfl

theorem Ptr.add_add (p : Ptr) (x y : Int) : (p.add x).add y = p.add (x + y) := by
  simp [Ptr.add, Int.add_assoc]

theorem inBounds_iff {m : Mem} {p : Ptr} : m.inBounds p = true ↔
    ∃ b blk, p.block = some b ∧ m.blocks[b]? = some blk ∧ 0 ≤ p.off ∧ p.off ≤ blk.bytes.size := by
  unfold Mem.inBounds
  split
  · rename_i h; simp [h]
  · rename_i b h
    split
    · rename_i hk; simp [h, hk]
    · rename_i blk hk; simp [h, hk]

theorem inBounds_of {m : Mem} {p : Ptr} {b : BlockId} {blk : Block} (hb : p.block = some b)
    (hblk : m.blocks[b]? = some blk) (h0 : 0 ≤ p.off) (hn : p.off ≤ blk.bytes.size) :
    m.inBounds p = true :=
  inBounds_iff.mpr ⟨b, blk, hb, hblk, h0, hn⟩

/-- A pointer that an access of `n` bytes succeeds at is in bounds (so is `n` bytes later). -/
theorem inBounds_of_access {m : Mem} {p : Ptr} {n a : Nat} {b : BlockId} {blk : Block} {o : Nat}
    (h : m.access p n a = pure (b, blk, o)) (k : Nat) (hk : k ≤ n) :
    m.inBounds (p.add k) = true := by
  obtain ⟨hb, hblk, -, h0, hn, -⟩ := access_eq h
  exact inBounds_of (b := b) (blk := blk) hb hblk (by simp [Ptr.add]; omega) (by simp [Ptr.add]; omega)

/-- A derived pointer equal to its base is the base, in every memory (no instruction natively). -/
theorem ptrProject_same {m : Mem} {p : Ptr} (project : Ptr → Ptr) (h : project p = p) :
    (ptrProject p project).run m = pure (p, m) := by
  simp [ptrProject, StateT.run, h]

/-- A derived pointer in bounds of its base's block (base included) is formed; memory is
unchanged. -/
theorem ptrProject_run {m : Mem} {p : Ptr} (project : Ptr → Ptr)
    (hb : (project p).block = p.block) (hp : m.inBounds p = true)
    (hq : m.inBounds (project p) = true) :
    (ptrProject p project).run m = pure (project p, m) := by
  simp [ptrProject, StateT.run, hb, hp, hq]

/-- The identity projection (a zero offset after simplification) is the base. -/
@[simp] theorem ptrProject_id (p : Ptr) (m : Mem) : ptrProject p (fun x => x) m = pure (p, m) := by
  simp [ptrProject]

/-- `ptrProject_run` for a byte offset. -/
theorem ptrProject_add_run {m : Mem} {p : Ptr} {off : Int} (hp : m.inBounds p = true)
    (hq : m.inBounds (p.add off) = true) :
    (ptrProject p (·.add off)).run m = pure (p.add off, m) :=
  ptrProject_run (·.add off) rfl hp hq

/-- A byte offset of a pointer into block `b` that stays within its bytes is formed. -/
theorem ptrProject_block_run {m : Mem} {b : BlockId} {blk : Block} (hb : m.blocks[b]? = some blk)
    {p : Ptr} {k : Nat} (hp : p.block = some b) (h0 : 0 ≤ p.off) (hk : p.off + k ≤ blk.bytes.size) :
    (ptrProject p (·.add k)).run m = pure (p.add k, m) :=
  ptrProject_add_run (inBounds_of hp hb h0 (by omega))
    (inBounds_of hp hb (by simp [Ptr.add]; omega) (by simp [Ptr.add]; omega))

/-- Any other derived pointer is illegal behaviour (`getelementptr inbounds` poison). -/
theorem ptrProject_illegal {m : Mem} {p : Ptr} (project : Ptr → Ptr) (h : project p ≠ p)
    (hout : ¬ ((project p).block = p.block ∧ m.inBounds p = true ∧ m.inBounds (project p) = true)) :
    (ptrProject p project).run m = throw .illegal := by
  simp only [ptrProject, StateT.run]
  rw [if_neg (by simp only [not_or]; exact ⟨h, hout⟩)]

/-- Pointer formation never changes memory and keeps the base's block. -/
theorem ptrProject_block {m m' : Mem} {p q : Ptr} {project : Ptr → Ptr}
    (h : (ptrProject p project).run m = pure (q, m')) : q.block = p.block ∧ m' = m := by
  by_cases hs : project p = p
  · rw [ptrProject_same project hs] at h
    simp [pure, StateT.pure, ExceptT.pure, ExceptT.mk] at h; obtain ⟨rfl, rfl⟩ := h; simp
  · by_cases hc : (project p).block = p.block ∧ m.inBounds p = true ∧ m.inBounds (project p) = true
    · rw [ptrProject_run project hc.1 hc.2.1 hc.2.2] at h
      simp [pure, StateT.pure, ExceptT.pure, ExceptT.mk] at h; obtain ⟨rfl, rfl⟩ := h
      exact ⟨hc.1, rfl⟩
    · rw [ptrProject_illegal project hs hc] at h; cases h

/-- Pointer formation either succeeds without a change to memory or is illegal behaviour. -/
theorem ptrProject_cases (p : Ptr) (project : Ptr → Ptr) (m : Mem) :
    (ptrProject p project).run m = pure (project p, m) ∨
      (ptrProject p project).run m = throw .illegal := by
  simp only [ptrProject, StateT.run]
  split
  · exact .inl rfl
  · exact .inr rfl

/-- A pointer that formation returned is the projection; memory is unchanged. -/
theorem ptrProject_ok {m m' : Mem} {p q : Ptr} {project : Ptr → Ptr}
    (h : (ptrProject p project).run m = pure (q, m')) : q = project p ∧ m' = m := by
  simp only [ptrProject, StateT.run] at h
  split at h
  · cases h; exact ⟨rfl, rfl⟩
  · cases h

theorem writeBytes_size (a : Array Byte) (o : Nat) (bs : Array Byte) (h : o + bs.size ≤ a.size) :
    (writeBytes a o bs).size = a.size := by
  simp [writeBytes]; omega

/-- A read of the written range gives the written bytes. -/
theorem extract_writeBytes (a : Array Byte) (o : Nat) (bs : Array Byte) (h : o + bs.size ≤ a.size) :
    (writeBytes a o bs).extract o (o + bs.size) = bs := by
  apply Array.ext
  · simp [writeBytes]; omega
  · intro i _ _
    have ho : Min.min o a.size = o := Nat.min_eq_left (by omega)
    simp [writeBytes, ho]

/-- A read of a range that does not overlap the written one is unchanged. -/
theorem extract_writeBytes_disjoint (a : Array Byte) (o : Nat) (bs : Array Byte) (o' n : Nat)
    (h : o + bs.size ≤ a.size) (h' : o' + n ≤ a.size) (hd : o + bs.size ≤ o' ∨ o' + n ≤ o) :
    (writeBytes a o bs).extract o' (o' + n) = a.extract o' (o' + n) := by
  apply Array.ext
  · simp [writeBytes]; omega
  · intro i h1 _
    have ho : Min.min o a.size = o := Nat.min_eq_left (by omega)
    simp only [Array.size_extract, writeBytes_size a o bs h] at h1
    simp only [writeBytes, Array.getElem_extract, Array.getElem_append, Array.size_append,
      Array.size_extract, ho]
    split
    · split
      · simp
      · omega
    · congr 1; omega

/-- `recordAccess` at `block`/`off`/`len`/`kind` succeeds (does not race) on `m`, and its effect:
bumps the current thread's clock and appends the footprint entry, leaving `blocks` untouched. A
`NoRace` hypothesis is a precondition on every lemma below that composes a load or a store, the
same way `Mem.access`'s own success is (`access_eq`/`access_of`) — it is not derived from an
invariant on `Mem` (an arbitrary `Mem` value has no such invariant), so a caller composing several
accesses in one thread (no concurrent access to the same bytes, the common case for the example
proofs) discharges it directly at each step. -/
def NoRace (m : Mem) (block : BlockId) (off len : Nat) (kind : AccessKind) : Prop :=
  raceCheck m (VClock.bump (m.clocks[m.current]!) m.current) block off len kind = none

/-- No footprint entry races with the access: `NoRace`, whether or not `m.solo` skips the scan. -/
theorem noRace_of_raceAt {m : Mem} {block : BlockId} {off len : Nat} {kind : AccessKind}
    (h : raceAt m.footprint (VClock.bump (m.clocks[m.current]!) m.current) block off len kind = none) :
    NoRace m block off len kind := by
  unfold NoRace raceCheck; split <;> simp_all

theorem recordAccess_run {m : Mem} {block : BlockId} {off len : Nat} {kind : AccessKind}
    (hnr : NoRace m block off len kind) :
    (recordAccess block off len kind).run m = pure ((), { m with
      clocks := m.clocks.set! m.current (VClock.bump (m.clocks[m.current]!) m.current),
      footprint := m.footprint.push
        { tid := m.current, clock := VClock.bump (m.clocks[m.current]!) m.current,
          block, off, len, kind } }) := by
  unfold recordAccess NoRace at *
  simp only [get, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind, set, StateT.set,
    MonadStateOf.set, pure, StateT.run, ExceptT.pure, ExceptT.mk, ExceptT.bind,
    ExceptT.bindCont, Option.bind_some, hnr]

/-- The memory after a race-free `recordAccess` at `block`/`off`/`len`/`kind` on `m`
(`recordAccess_run`). -/
def Mem.recordAt (m : Mem) (block : BlockId) (off len : Nat) (kind : AccessKind) : Mem :=
  { m with
    clocks := m.clocks.set! m.current (VClock.bump (m.clocks[m.current]!) m.current),
    footprint := m.footprint.push
      { tid := m.current, clock := VClock.bump (m.clocks[m.current]!) m.current,
        block, off, len, kind } }

/-! ## Single-thread executions

A per-call-site `NoRace` hypothesis is the general obligation (`NoRace`'s own doc comment), but a
program that never spawns a thread (all of `M17`'s example proofs) discharges it uniformly: no
other thread ever runs, so no footprint entry can be concurrent with the current access. -/

theorem VClock.le_iff {a b : VClock} : VClock.le a b = true ↔ ∀ i, a.get i ≤ b.get i := by
  unfold VClock.le
  constructor
  · intro h i
    by_cases hi : i < Nat.max a.size b.size
    · have h' := (Array.all_eq_true.mp h) i (by simpa using hi)
      rw [Array.getElem_range (by simpa using hi)] at h'
      exact Nat.ble_eq.mp h'
    · have hmax : Nat.max a.size b.size ≤ i := Nat.not_lt.mp hi
      have ha : a.size ≤ i := Nat.le_trans (Nat.le_max_left _ _) hmax
      have hb : b.size ≤ i := Nat.le_trans (Nat.le_max_right _ _) hmax
      simp [VClock.get, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none ha,
        Array.getElem?_eq_none hb]
  · intro h
    apply Array.all_eq_true.mpr
    intro i hi
    rw [Array.getElem_range (by simpa using hi)]
    exact Nat.ble_eq.mpr (h i)

theorem VClock.le_refl (c : VClock) : VClock.le c c = true := VClock.le_iff.mpr fun _ => Nat.le_refl _

theorem VClock.le_trans {a b c : VClock} (hab : VClock.le a b = true) (hbc : VClock.le b c = true) :
    VClock.le a c = true :=
  VClock.le_iff.mpr fun i => Nat.le_trans (VClock.le_iff.mp hab i) (VClock.le_iff.mp hbc i)

/-- The empty clock (`default`, a thread with no access yet) is below every clock. -/
theorem VClock.le_default (c : VClock) : VClock.le default c = true :=
  VClock.le_iff.mpr fun i => by
    show (#[] : Array Nat).getD i 0 ≤ _
    simp

/-- A clock with one component above `b`'s is not below `b`. -/
theorem VClock.le_eq_false {a b : VClock} {i : ThreadId} (h : b.get i < a.get i) :
    VClock.le a b = false := by
  cases hl : VClock.le a b
  · rfl
  · have := VClock.le_iff.mp hl i; omega

/-- `VClock.merge` is a genuine upper bound: `a`'s own component is never lost. -/
theorem VClock.get_merge (a b : VClock) (i : ThreadId) :
    (VClock.merge a b).get i = Nat.max (a.get i) (b.get i) := by
  unfold VClock.merge VClock.get
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range]
  by_cases hi : i < Nat.max a.size b.size
  · simp only [hi, ite_true, Option.map_some, Option.getD_some]
  · simp only [hi, ite_false, Option.map_none, Option.getD_none]
    have hmax : Nat.max a.size b.size ≤ i := Nat.not_lt.mp hi
    have ha : a.size ≤ i := Nat.le_trans (Nat.le_max_left _ _) hmax
    have hb : b.size ≤ i := Nat.le_trans (Nat.le_max_right _ _) hmax
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none ha, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_none hb]
    rfl

theorem VClock.le_merge_left (a b : VClock) : VClock.le a (VClock.merge a b) = true :=
  VClock.le_iff.mpr fun i => by rw [VClock.get_merge]; exact Nat.le_max_left _ _

theorem VClock.le_merge_right (a b : VClock) : VClock.le b (VClock.merge a b) = true :=
  VClock.le_iff.mpr fun i => by rw [VClock.get_merge]; exact Nat.le_max_right _ _

theorem VClock.merge_le {a b c : VClock} (ha : VClock.le a c = true) (hb : VClock.le b c = true) :
    VClock.le (VClock.merge a b) c = true :=
  VClock.le_iff.mpr fun i => by
    rw [VClock.get_merge]
    exact Nat.max_le.mpr ⟨VClock.le_iff.mp ha i, VClock.le_iff.mp hb i⟩

/-- The padding a bump to `t` may append does not change any component already in `c`, and (if it
extends the array) leaves every new component but `t` itself at `0`. -/
theorem VClock.get_pad (c : VClock) (t i : ThreadId) (_h : i ≠ t) :
    ((if t < c.size then c else c ++ Array.replicate (t + 1 - c.size) 0) : VClock).get i =
      c.get i := by
  unfold VClock.get
  by_cases ht : t < c.size
  · simp [ht]
  · simp only [ht, ↓reduceIte, Array.getD_eq_getD_getElem?, Array.getElem?_append]
    by_cases hi : i < c.size
    · simp [hi]
    · simp only [hi, ↓reduceIte, Array.getElem?_replicate]
      rw [Array.getElem?_eq_none (Nat.le_of_not_lt hi)]
      split <;> rfl

/-- Bumping `t`'s own component leaves every other component as-is. -/
theorem VClock.get_bump_ne (c : VClock) (t i : ThreadId) (h : i ≠ t) :
    (VClock.bump c t).get i = c.get i := by
  unfold VClock.bump VClock.get
  rw [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds_ne (Ne.symm h), ← Array.getD_eq_getD_getElem?]
  exact VClock.get_pad c t i h

/-- Bumping `t`'s own component increases it by one.

`t : Nat`, not `ThreadId`: mixing the `ThreadId` abbrev into arithmetic on `c.size` (a bare `Nat`)
makes Lean's binop elaborator pick inconsistent (though defeq) instance paths across the
expression, so `omega` fails to relate the hypotheses to the goal — see the sibling helper
`have`s below, which hit exactly this if stated over `ThreadId`. -/
theorem VClock.get_bump_self (c : VClock) (t : Nat) :
    (VClock.bump c t).get t = c.get t + 1 := by
  unfold VClock.bump VClock.get
  rw [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds]
  by_cases ht : t < c.size
  · simp only [ht, ↓reduceIte]
    rw [Array.getElem?_setIfInBounds_self_of_lt ht, Option.getD_some]
  · have hge : c.size ≤ t := Nat.le_of_not_lt ht
    have hpad : (c ++ Array.replicate (t + 1 - c.size) 0 : VClock).size = t + 1 := by
      simp only [Array.size_append, Array.size_replicate]; omega
    have hsize : t < (c ++ Array.replicate (t + 1 - c.size) 0 : VClock).size := by omega
    simp only [ht, ↓reduceIte]
    rw [Array.getElem?_setIfInBounds_self_of_lt hsize, Option.getD_some]
    congr 1
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_append]
    simp only [ht, ↓reduceIte, Array.getElem?_replicate]
    have hlt : t - c.size < t + 1 - c.size := by omega
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hge]
    simp [hlt]

/-- Bumping only ever increases (or leaves unchanged) every component. -/
theorem VClock.le_bump (c : VClock) (t : ThreadId) : VClock.le c (VClock.bump c t) = true := by
  apply VClock.le_iff.mpr
  intro i
  by_cases hi : i = t
  · subst hi; rw [VClock.get_bump_self]; omega
  · rw [VClock.get_bump_ne c t i hi]; exact Nat.le_refl _

/-- Every recorded access was made by `m`'s current thread, and its clock is dominated by the
current thread's own (present) clock. True of the initial memory (empty footprint), and preserved
by every race-free access on the same thread (`singleThread_recordAt`) — so a program that never
spawns another thread carries this as a standing invariant, discharging `NoRace` for free at every
step (`noRace_of_singleThread`) instead of a bespoke hypothesis per call site. The bound on
`current` is carried alongside so `recordAt`'s `set!` provably lands on a real slot. -/
def Mem.SingleThread (m : Mem) : Prop :=
  m.current < m.clocks.size ∧
    ∀ e ∈ m.footprint, e.tid = m.current ∧ VClock.le e.clock (m.clocks[m.current]!) = true

theorem singleThread_empty {m : Mem} (hf : m.footprint = #[]) (hc : m.current < m.clocks.size) :
    m.SingleThread := ⟨hc, by simp [hf]⟩

theorem noRace_of_singleThread {m : Mem} (h : m.SingleThread) (block off len : Nat)
    (kind : AccessKind) : NoRace m block off len kind := by
  apply noRace_of_raceAt
  unfold raceAt
  rw [Array.findSome?_eq_none_iff]
  intro e he
  have ⟨_, hle⟩ := h.2 e he
  have hle' := VClock.le_trans hle (VClock.le_bump m.clocks[m.current]! m.current)
  simp [VClock.concurrent, hle']

/-- MM-14: on a single-thread memory, `raceCheck`'s skip changes nothing — the scan it skips
finds no race either. -/
theorem raceCheck_eq_raceAt {m : Mem} (h : m.SingleThread) (block off len : Nat)
    (kind : AccessKind) :
    raceCheck m (VClock.bump (m.clocks[m.current]!) m.current) block off len kind =
      raceAt m.footprint (VClock.bump (m.clocks[m.current]!) m.current) block off len kind := by
  have hr : raceAt m.footprint (VClock.bump (m.clocks[m.current]!) m.current) block off len kind
      = none := by
    unfold raceAt
    rw [Array.findSome?_eq_none_iff]
    intro e he
    have ⟨_, hle⟩ := h.2 e he
    have hle' := VClock.le_trans hle (VClock.le_bump m.clocks[m.current]! m.current)
    simp [VClock.concurrent, hle']
  unfold raceCheck; split <;> simp [hr]

/-- The end of a block does not race if every thread's clock is below the current thread's
(each thread joined into it, or no other thread). -/
theorem freeRaces_of_le {m : Mem} {b n : Nat}
    (h : ∀ u < m.clocks.size, VClock.le (m.clocks[u]!) (m.clocks[m.current]!) = true) :
    m.freeRaces b n = false := by
  apply Bool.eq_false_iff.mpr
  intro hany
  obtain ⟨i, hi, he⟩ := Array.any_eq_true.mp hany
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at he
  have hle : VClock.le (m.clocks[m.footprint[i].tid]!)
      (VClock.bump (m.clocks[m.current]!) m.current) = true := by
    by_cases hu : m.footprint[i].tid < m.clocks.size
    · exact VClock.le_trans (h _ hu) (VClock.le_bump _ _)
    · rw [getElem!_neg m.clocks _ hu]; exact VClock.le_default _
  rw [he.1.2] at hle; cases hle

/-- The end of a block does not race if each access to its bytes happened before the current
thread. -/
theorem freeRaces_of_clock {m : Mem} {b n : Nat}
    (h : ∀ e ∈ m.footprint, e.block = b → e.off < n →
      VClock.le e.clock (m.clocks[m.current]!) = true) :
    m.freeRaces b n = false := by
  apply Bool.eq_false_iff.mpr
  intro hany
  obtain ⟨i, hi, he⟩ := Array.any_eq_true.mp hany
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, decide_eq_true_eq] at he
  obtain ⟨⟨⟨⟨⟨⟨hb, -⟩, ho⟩, -⟩, hcl⟩, -⟩, -⟩ := he
  have hle := VClock.le_trans (h _ (Array.getElem_mem hi) hb ho)
    (VClock.le_bump (m.clocks[m.current]!) m.current)
  rw [hcl] at hle; cases hle

/-- The end of a block does not race if each other thread is a child of the current thread that
it joined (and there are as many clocks as threads). -/
theorem freeRaces_of_joined {m : Mem} {b n : Nat} (hcs : m.clocks.size = m.threads.size)
    (h : ∀ u < m.threads.size, u = m.current ∨
      ∃ r, m.threads[u]? = some r ∧ r.spawner = m.current ∧ r.joined = true ∧ r.released = false) :
    m.freeRaces b n = false := by
  apply Bool.eq_false_iff.mpr
  intro hany
  obtain ⟨i, hi, he⟩ := Array.any_eq_true.mp hany
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at he
  obtain ⟨⟨⟨⟨-, htc⟩, -⟩, hcl⟩, hj⟩ := he
  by_cases hu : m.footprint[i].tid < m.threads.size
  · rcases h _ hu with h' | ⟨r, hr, hs, hjr, hrel⟩
    · exact htc h'
    · rw [hr] at hj; simp [hs, hjr, hrel] at hj
  · rw [getElem!_neg m.clocks m.footprint[i].tid (by rw [hcs]; exact hu)] at hcl
    rw [VClock.le_default] at hcl; cases hcl

/-- In a single thread, the end of a block does not race. -/
theorem freeRaces_of_singleThread {m : Mem} (h : m.SingleThread) (b n : Nat) :
    m.freeRaces b n = false := by
  apply Bool.eq_false_iff.mpr
  intro hany
  obtain ⟨i, hi, he⟩ := Array.any_eq_true.mp hany
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at he
  obtain ⟨⟨⟨⟨-, htc⟩, -⟩, -⟩, -⟩ := he
  exact htc (h.2 _ (Array.getElem_mem hi)).1

theorem singleThread_recordAt {m : Mem} (h : m.SingleThread) (block off len : Nat)
    (kind : AccessKind) : (m.recordAt block off len kind).SingleThread := by
  have hbump : (m.recordAt block off len kind).clocks[(m.recordAt block off len kind).current]! =
      VClock.bump (m.clocks[m.current]!) m.current := by
    show (m.clocks.set! m.current (VClock.bump (m.clocks[m.current]!) m.current))[m.current]! = _
    exact Array.getElem!_set!_self m.clocks m.current _ h.1
  refine ⟨?_, ?_⟩
  · show m.current < (m.clocks.set! m.current _).size
    rw [Array.size_set!]; exact h.1
  · intro e he
    unfold Mem.recordAt at he
    simp only [Array.mem_push] at he
    rcases he with he | rfl
    · have ⟨htid, hle⟩ := h.2 e he
      refine ⟨htid, ?_⟩
      rw [hbump]
      exact VClock.le_trans hle (VClock.le_bump m.clocks[m.current]! m.current)
    · refine ⟨rfl, ?_⟩
      rw [hbump]
      exact VClock.le_refl _

theorem loadBytes_run {m : Mem} {p : Ptr} {n a : Nat} {b : BlockId} {blk : Block} {o : Nat}
    {kind : AccessKind} (h : m.access p n a = pure (b, blk, o)) (hnr : NoRace m b o n kind) :
    (loadBytes p n a kind).run m =
      pure (blk.bytes.extract o (o + n), m.recordAt b o n kind) := by
  unfold loadBytes recordAccess NoRace at *
  simp only [h, get, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind, set, StateT.set,
    MonadStateOf.set, pure, StateT.pure, StateT.run, liftM, monadLift, MonadLift.monadLift,
    StateT.lift, ExceptT.pure, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, Option.bind_some, hnr,
    Mem.recordAt]

/-- Direct discarded access is equivalent for every state to the former full read and
unused result, including access errors, race errors, clock changes and read footprints. -/
theorem loadDiscardBytes_eq (n a : Nat) (p : Ptr) :
    loadDiscardBytes n a p = (do let _ ← loadBytes p n a; pure ()) := by
  simp only [loadDiscardBytes, loadBytes, bind_assoc, pure_bind]

/-- A discarded load validates and records the full raw read without extracting bytes. -/
theorem loadDiscardBytes_run {m : Mem} {p : Ptr} {n a : Nat} {b : BlockId} {blk : Block} {o : Nat}
    (h : m.access p n a = pure (b, blk, o)) (hnr : NoRace m b o n .read) :
    (loadDiscardBytes n a p).run m = pure ((), m.recordAt b o n .read) := by
  rw [loadDiscardBytes_eq]
  simp only [StateT.run_bind, loadBytes_run h hnr]
  simp [StateT.run, pure, StateT.pure, bind, ExceptT.pure, ExceptT.mk, ExceptT.bind,
    ExceptT.bindCont]

/-- The memory after writing `bs` at offset `o` of block `b` (`storeBytes`). -/
def Mem.write (m : Mem) (b : BlockId) (blk : Block) (o : Nat) (bs : Array Byte) : Mem :=
  { m with blocks := m.blocks.set! b { blk with bytes := writeBytes blk.bytes o bs } }

/-- `.write` only touches `blocks`, never `current`/`clocks`/`footprint`, so it preserves
`SingleThread`. -/
theorem singleThread_write {m : Mem} (h : m.SingleThread) (b : BlockId) (blk : Block) (o : Nat)
    (bs : Array Byte) : (m.write b blk o bs).SingleThread := h

/-- `.access` only looks at `blocks`, never at `current`/`clocks`/`threads`/`footprint`, so a
race-free `recordAccess` (`Mem.recordAt`) never changes what a further access sees. -/
theorem access_recordAt {m : Mem} {block off len : Nat} {kind : AccessKind} {q : Ptr}
    {n' a' : Nat} : (m.recordAt block off len kind).access q n' a' = m.access q n' a' := by
  simp [Mem.access, Mem.recordAt]

theorem storeBytes_run {m : Mem} {p : Ptr} {a : Nat} {bs : Array Byte} {b : BlockId}
    {blk : Block} {o : Nat} {kind : AccessKind} (h : m.access p bs.size a = pure (b, blk, o))
    (hK : blk.kind ≠ .constGlobal) (hnr : NoRace m b o bs.size kind) :
    (storeBytes p a bs kind).run m = pure ((), (m.recordAt b o bs.size kind).write b blk o bs) := by
  have hw : m.accessW p bs.size a = pure (b, blk, o) := by simp [Mem.accessW, h, hK]
  unfold storeBytes recordAccess NoRace at *
  simp only [hw, Mem.write, get, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind, set,
    StateT.set, MonadStateOf.set, pure, StateT.run, liftM, monadLift,
    MonadLift.monadLift, StateT.lift, ExceptT.pure, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
    Option.bind_some, hnr, Mem.recordAt]

/-- After a write to block `b`, an access to `b` sees the new bytes, at the same offset. -/
theorem access_write_same {m : Mem} {p q : Ptr} {a n' a' : Nat} {bs : Array Byte} {b : BlockId}
    {blk : Block} {o o' : Nat} (hw : m.access p bs.size a = pure (b, blk, o))
    (hq : m.access q n' a' = pure (b, blk, o')) :
    (m.write b blk o bs).access q n' a' =
      pure (b, { blk with bytes := writeBytes blk.bytes o bs }, o') := by
  obtain ⟨hpb, hblk, hl, h0, hn, _, rfl⟩ := access_eq hw
  obtain ⟨hqb, -, -, h0', hn', ha', rfl⟩ := access_eq hq
  have hlt : b < m.blocks.size := by
    rcases Array.getElem?_eq_some_iff.mp hblk with ⟨h, _⟩; exact h
  apply access_of hqb
  · simp [Mem.write, hlt]
  · exact hl
  · exact h0'
  · rw [writeBytes_size _ _ _ (by omega)]; exact hn'
  · exact ha'

/-- A write to block `b` does not change an access to another block. -/
theorem access_write_other {m : Mem} {q : Ptr} {n' a' : Nat} {bs : Array Byte}
    {b c : BlockId} {blk blk' : Block} {o o' : Nat}
    (hq : m.access q n' a' = pure (c, blk', o')) (hbc : b ≠ c) :
    (m.write b blk o bs).access q n' a' = pure (c, blk', o') := by
  obtain ⟨hqb, hblk', hl, h0, hn, ha, rfl⟩ := access_eq hq
  exact access_of hqb (by simp [Mem.write, Array.getElem?_setIfInBounds_ne hbc, hblk']) hl h0 hn ha

/-! ## Typed access -/

/-- An encoding that reads back what it writes. -/
class LawfulEnc (α : Type) [Enc α] : Prop where
  size_encode : ∀ v : α, (Enc.encode v).size = Enc.size α
  decode_encode : ∀ v : α, Enc.decode (Enc.encode v) = pure v

/-- `NoRace` only reads `footprint`/`clocks`/`current`, none of which `Mem.write` touches. -/
theorem noRace_write {m : Mem} {b' : BlockId} {blk' : Block} {o' : Nat} {bs : Array Byte}
    {block : BlockId} {off len : Nat} {kind : AccessKind} :
    NoRace (m.write b' blk' o' bs) block off len kind ↔ NoRace m block off len kind := Iff.rfl

theorem load_run {α : Type} [Enc α] {m : Mem} {p : Ptr} {a : Nat} {b : BlockId} {blk : Block}
    {o : Nat} {v : α} (h : m.access p (Enc.size α) a = pure (b, blk, o))
    (hv : Enc.decode (blk.bytes.extract o (o + Enc.size α)) = pure v)
    (hnr : NoRace m b o (Enc.size α) .read) :
    (load α a p).run m = pure (v, m.recordAt b o (Enc.size α) .read) := by
  simp only [load, StateT.run_bind, loadBytes_run h hnr]
  simp [decodeLoad_of_decode hv, pure, ExceptT.pure, ExceptT.mk, bind, ExceptT.bind,
    ExceptT.bindCont, StateT.run, liftM, monadLift, MonadLift.monadLift, StateT.lift, get, getThe,
    MonadStateOf.get, StateT.get]

theorem store_run {α : Type} [Enc α] [LawfulEnc α] {m : Mem} {p : Ptr} {a : Nat} {b : BlockId}
    {blk : Block} {o : Nat} (v : α) (h : m.access p (Enc.size α) a = pure (b, blk, o))
    (hK : blk.kind ≠ .constGlobal) (hnr : NoRace m b o (Enc.size α) .write) :
    (store a p v).run m = pure ((), (m.recordAt b o (Enc.size α) .write).write b blk o (Enc.encode v)) := by
  rw [show Enc.size α = (Enc.encode v).size from (LawfulEnc.size_encode v).symm] at h hnr ⊢
  exact storeBytes_run h hK hnr

/-- A store to a `const` global throws `.illegal` (`Mem.accessW`). -/
theorem store_constGlobal {α : Type} [Enc α] [LawfulEnc α] {m : Mem} {p : Ptr} {a : Nat}
    {b : BlockId} {blk : Block} {o : Nat} (v : α) (h : m.access p (Enc.size α) a = pure (b, blk, o))
    (hK : blk.kind = .constGlobal) : (store a p v).run m = throw .illegal := by
  rw [show Enc.size α = (Enc.encode v).size from (LawfulEnc.size_encode v).symm] at h
  simp [store, storeBytes, Mem.accessW, h, hK, StateT.run, bind, StateT.bind, get, getThe,
    MonadStateOf.get, StateT.get, liftM, monadLift, MonadLift.monadLift, StateT.lift, pure,
    ExceptT.pure, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, throw, throwThe,
    MonadExceptOf.throw]

/-- After `store_run`, an access to the same block sees the new bytes, at its own offset (which
may differ from the store's, e.g. two disjoint fields of one struct). Composes `access_recordAt`
(the `recordAt` layer is invisible to `.access`) with `access_write_same`, matching `store_run`'s
conclusion memory exactly. -/
theorem access_store_same {α : Type} [Enc α] [LawfulEnc α] {m : Mem} {p q : Ptr} {a n' a' : Nat}
    {b : BlockId} {blk : Block} {o o' : Nat} (v : α)
    (hp : m.access p (Enc.size α) a = pure (b, blk, o))
    (hq : m.access q n' a' = pure (b, blk, o')) :
    ((m.recordAt b o (Enc.size α) .write).write b blk o (Enc.encode v)).access q n' a' =
      pure (b, { blk with bytes := writeBytes blk.bytes o (Enc.encode v) }, o') := by
  have hp' := hp
  rw [show Enc.size α = (Enc.encode v).size from (LawfulEnc.size_encode v).symm] at hp'
  exact access_write_same (access_recordAt.trans hp') (access_recordAt.trans hq)

/-- After `store_run`, an access to another block is unaffected. -/
theorem access_store_other {α : Type} [Enc α] {m : Mem} {p q : Ptr} {a n' a' : Nat}
    {b c : BlockId} {blk blk' : Block} {o o' : Nat} (v : α)
    (_hp : m.access p (Enc.size α) a = pure (b, blk, o))
    (hq : m.access q n' a' = pure (c, blk', o')) (hbc : b ≠ c) :
    ((m.recordAt b o (Enc.size α) .write).write b blk o (Enc.encode v)).access q n' a' =
      pure (c, blk', o') :=
  access_write_other (access_recordAt.trans hq) hbc

/-- After a store at `p`, a load of the same type at `p` gives the stored value. `hnr`: the load,
on the memory after the store, does not race (a caller composing accesses in one thread discharges
it, `NoRace`; the store's own race-freedom, if any, is the caller's `store_run`). -/
theorem load_store_same {α : Type} [Enc α] [LawfulEnc α] {m : Mem} {p : Ptr} {a a' : Nat}
    {b : BlockId} {blk : Block} {o : Nat} (v : α)
    (h : m.access p (Enc.size α) a = pure (b, blk, o))
    (h' : m.access p (Enc.size α) a' = pure (b, blk, o))
    (hnr : NoRace (m.write b blk o (Enc.encode v)) b o (Enc.size α) .read) :
    (load α a' p).run (m.write b blk o (Enc.encode v)) =
      pure (v, (m.write b blk o (Enc.encode v)).recordAt b o (Enc.size α) .read) := by
  have hw := h
  rw [← LawfulEnc.size_encode v] at hw
  have h0 := (access_eq h).2.2.2.1
  have hn := (access_eq h).2.2.2.2.1
  have ho := (access_eq h).2.2.2.2.2.2
  have hx := extract_writeBytes blk.bytes o (Enc.encode v) (by rw [LawfulEnc.size_encode v]; omega)
  rw [LawfulEnc.size_encode v] at hx
  exact load_run (access_write_same hw h') (by simp only [hx, LawfulEnc.decode_encode]) hnr

/-- A store at `p` does not change a load at `q` in another block, or at a range of the same
block that does not overlap. `hnr`: the load does not race (as in `load_store_same`). -/
theorem load_store_other {α β : Type} [Enc α] [LawfulEnc α] [Enc β] {m : Mem} {p q : Ptr}
    {a a' : Nat} {b c : BlockId} {blk blk' : Block} {o o' : Nat} (v : α) {w : β}
    (hp : m.access p (Enc.size α) a = pure (b, blk, o))
    (hq : m.access q (Enc.size β) a' = pure (c, blk', o'))
    (hd : b ≠ c ∨ o + Enc.size α ≤ o' ∨ o' + Enc.size β ≤ o)
    (hw : Enc.decode (blk'.bytes.extract o' (o' + Enc.size β)) = pure w)
    (hnr : NoRace (m.write b blk o (Enc.encode v)) c o' (Enc.size β) .read) :
    (load β a' q).run (m.write b blk o (Enc.encode v)) =
      pure (w, (m.write b blk o (Enc.encode v)).recordAt c o' (Enc.size β) .read) := by
  by_cases hbc : b = c
  · subst hbc
    have hd' : o + Enc.size α ≤ o' ∨ o' + Enc.size β ≤ o := hd.resolve_left (· rfl)
    have hblk : blk' = blk := by
      have := (access_eq hp).2.1; have := (access_eq hq).2.1; simp_all
    subst hblk
    have hpw := hp
    rw [← LawfulEnc.size_encode v] at hpw
    apply load_run (access_write_same hpw hq) _ hnr
    have h0 := (access_eq hp).2.2.2.1
    have h0' := (access_eq hq).2.2.2.1
    have hn := (access_eq hp).2.2.2.2.1
    have hn' := (access_eq hq).2.2.2.2.1
    have ho := (access_eq hp).2.2.2.2.2.2
    have ho' := (access_eq hq).2.2.2.2.2.2
    rw [extract_writeBytes_disjoint _ _ _ _ _ (by rw [LawfulEnc.size_encode v]; omega) (by omega)
      (by rw [LawfulEnc.size_encode v]; omega)]
    exact hw
  · exact load_run (access_write_other hq hbc) hw hnr

/-! ## Pointer-level form -/

-- `Mem.writeAt`/`store_run'`/`load_writeAt_same`/`load_writeAt_other` (the "load unchanges
-- memory" idiom) were dropped with M22: a load now also records a footprint entry, so callers
-- (`Proofs/Pointers/Proofs.lean`) compose `load_run`/`store_run`/`load_store_same`/
-- `load_store_other` directly, threading each step's own `NoRace` hypothesis and output memory.

/-- Inverts a successful `load`: the access succeeds, the decode gives `v`, and the resulting
memory is the input with the read recorded (`Mem.recordAt`). -/
theorem load_inv {α : Type} [Enc α] {m m' : Mem} {p : Ptr} {a : Nat} {v : α}
    (h : (load α a p).run m = pure (v, m')) :
    ∃ b blk o, m.access p (Enc.size α) a = pure (b, blk, o) ∧
      decodeLoad m.blocks (blk.bytes.extract o (o + Enc.size α)) = pure v ∧
      m' = m.recordAt b o (Enc.size α) .read := by
  simp only [load, loadBytes, recordAccess, StateT.run, bind, StateT.bind, get, getThe,
    MonadStateOf.get, StateT.get, liftM, monadLift, MonadLift.monadLift, StateT.lift, ExceptT.bind,
    ExceptT.mk, pure, StateT.pure, ExceptT.pure, Option.bind_some, ExceptT.bindCont, set,
    MonadStateOf.set, throw, throwThe, MonadExceptOf.throw, Function.comp] at h
  generalize hacc : m.access p (Enc.size α) a = r at h
  match r, hacc, h with
  | none, _, h => simp at h
  | some (.error _), _, h =>
    simp only [ExceptT.bindCont, Option.bind_some] at h; cases h
  | some (.ok (b, blk, o)), hacc, h =>
    simp only [ExceptT.bindCont, Option.bind_some] at h
    generalize hr : raceCheck m (VClock.bump (m.clocks[m.current]!) m.current) b o
      (Enc.size α) .read = r at h
    match r, hr, h with
    | some _, _, h =>
      cases h
    | none, hr, h =>
      simp only [ExceptT.bindCont, Option.bind_some, StateT.set, pure, ExceptT.pure, ExceptT.mk] at h
      generalize hd2 : (decodeLoad m.blocks (blk.bytes.extract o (o + Enc.size α)) : Result α) = d at h
      match d, hd2, h with
      | none, _, h => simp at h
      | some (.error _), _, h =>
        simp only [ExceptT.bindCont, Option.bind_some] at h; cases h
      | some (.ok w), hd2, h =>
        simp only [ExceptT.bindCont, Option.bind_some] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨b, blk, o, rfl, hd2, rfl⟩

/-- A load of the bytes of a value of a lawful encoding decodes the value. -/
@[simp] theorem decodeLoad_encode {α : Type} [Enc α] [LawfulEnc α] (blocks : Array Block) (v : α) :
    decodeLoad blocks (Enc.encode v) = pure v :=
  decodeLoad_of_decode (LawfulEnc.decode_encode v)

instance : LawfulEnc Bool where
  size_encode _ := rfl
  decode_encode v := by cases v <;> rfl

instance : LawfulEnc (BitVec 32) where
  size_encode v := by simp [Enc.encode, Enc.size, padTo, intBytes, intSize, intAlign, alignUp]
  decode_encode v := by
    have hr : Array.range 4 = #[0, 1, 2, 3] := by decide
    simp [Enc.encode, Enc.decode, intSize, intAlign, alignUp, padTo, intBytes, intOfBytes, byteBits,
      hr, bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont]
    congr 2
    apply BitVec.eq_of_toNat_eq
    have := v.isLt
    simp only [Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
    omega

instance : LawfulEnc (BitVec 64) where
  size_encode v := by simp [Enc.encode, Enc.size, padTo, intBytes, intSize, intAlign, alignUp]
  decode_encode v := by
    have hr : Array.range 8 = #[0, 1, 2, 3, 4, 5, 6, 7] := by decide
    simp [Enc.encode, Enc.decode, intSize, intAlign, alignUp, padTo, intBytes, intOfBytes, byteBits,
      hr, bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont]
    congr 2
    apply BitVec.eq_of_toNat_eq
    have := v.isLt
    simp only [Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
    omega

instance : LawfulEnc (BitVec 8) where
  size_encode v := by simp [Enc.encode, Enc.size, padTo, intBytes, intSize, intAlign, alignUp]
  decode_encode v := by
    have hr : Array.range 1 = #[0] := by decide
    simp [Enc.encode, Enc.decode, intSize, intAlign, alignUp, padTo, intBytes, intOfBytes, byteBits,
      hr, bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont]
    congr 2
    apply BitVec.eq_of_toNat_eq
    have := v.isLt
    simp only [BitVec.toNat_ofNat]
    omega

instance : LawfulEnc (BitVec 16) where
  size_encode v := by simp [Enc.encode, Enc.size, padTo, intBytes, intSize, intAlign, alignUp]
  decode_encode v := by
    have hr : Array.range 2 = #[0, 1] := by decide
    simp [Enc.encode, Enc.decode, intSize, intAlign, alignUp, padTo, intBytes, intOfBytes, byteBits,
      hr, bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont]
    congr 2
    apply BitVec.eq_of_toNat_eq
    have := v.isLt
    simp only [Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
    omega

instance : LawfulEnc (BitVec 2) where
  size_encode v := by simp [Enc.encode, Enc.size, padTo, intBytes, intSize, intAlign, alignUp]
  decode_encode v := by
    have hr : Array.range 1 = #[0] := by decide
    have hl : v.toNat % 256 < 4 := by have := v.isLt; simp at this; omega
    simp [Enc.encode, Enc.decode, intSize, intAlign, alignUp, padTo, intBytes, intOfBytes, byteBits,
      hr, hl, bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont]
    congr 2
    apply BitVec.eq_of_toNat_eq
    have := v.isLt
    simp only [BitVec.toNat_ofNat]
    omega

instance : LawfulEnc (BitVec 1) where
  size_encode v := by simp [Enc.encode, Enc.size, padTo, intBytes, intSize, intAlign, alignUp]
  decode_encode v := by
    have hr : Array.range 1 = #[0] := by decide
    have hl : v.toNat % 256 < 2 := by have := v.isLt; simp at this; omega
    simp [Enc.encode, Enc.decode, intSize, intAlign, alignUp, padTo, intBytes, intOfBytes, byteBits,
      hr, hl, bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont]
    congr 2
    apply BitVec.eq_of_toNat_eq
    have := v.isLt
    simp only [BitVec.toNat_ofNat]
    omega

/-- `?*T`: `null` is 8 zero bytes, and pointer bytes are never zero bytes. -/
instance : LawfulEnc (Option Ptr) where
  size_encode v := by cases v <;> simp [Enc.encode, Enc.size]
  decode_encode v := by
    have hr : Array.finRange 8 = #[0, 1, 2, 3, 4, 5, 6, 7] := by decide
    cases v with
    | none => simp [Enc.encode, Enc.decode, pure, ExceptT.pure, ExceptT.mk]
    | some p =>
      simp [Enc.encode, Enc.decode, hr, pure, ExceptT.pure, ExceptT.mk, Functor.map, ExceptT.map]
      intro h
      have := congrArg (·[0]?) h
      simp at this

instance : LawfulEnc Ptr where
  size_encode p := by simp [Enc.encode, Enc.size]
  decode_encode p := by
    have hr : Array.finRange 8 = #[0, 1, 2, 3, 4, 5, 6, 7] := by decide
    simp [Enc.encode, Enc.decode, hr, pure, ExceptT.pure, ExceptT.mk]

/-! ## Finite error storage -/

@[simp] theorem errOfBytes_errBytes (e : Option ErrName) :
    errOfBytes (errBytes e) = pure e := by
  cases e <;> simp [errOfBytes, errBytes, pure, ExceptT.pure, ExceptT.mk]

theorem errorEnc_size_encode (d : ErrorDomain) (e : ErrName) :
    ((errorEnc d).encode e).size = 2 := by
  change (if d.names.contains e then errBytes (some e) else #[.undef, .undef]).size = 2
  split <;> rfl

/-- The string API is lawful only on the declared finite domain. -/
theorem errorEnc_roundtrip (d : ErrorDomain) (e : ErrName) (h : d.names.contains e = true) :
    (errorEnc d).decode ((errorEnc d).encode e) = pure e := by
  change (errOfBytes (if d.names.contains e then errBytes (some e) else #[.undef, .undef]) >>= fun code =>
    match code with
    | some name => if d.names.contains name then pure name else throw .unspecified
    | none => throw .unspecified) = pure e
  have hm : e ∈ d.names := Array.contains_iff_mem.mp h
  simp [h, hm, errOfBytes_errBytes, bind, pure, ExceptT.bind, ExceptT.pure,
    ExceptT.mk, ExceptT.bindCont]

theorem optionalErrorEnc_roundtrip (d : ErrorDomain) (e : Option ErrName)
    (h : ∀ x, e = some x → d.names.contains x = true) :
    (optionalErrorEnc d).decode ((optionalErrorEnc d).encode e) = pure e := by
  cases e with
  | none =>
    change (errOfBytes (errBytes none) >>= fun code =>
      match code with
      | none => pure none
      | some name => if d.names.contains name then pure (some name) else throw .unspecified) = pure none
    simp [errOfBytes_errBytes, bind, pure, ExceptT.bind, ExceptT.pure,
      ExceptT.mk, ExceptT.bindCont]
  | some x =>
    change (errOfBytes (if d.names.contains x then errBytes (some x) else #[.undef, .undef]) >>= fun code =>
      match code with
      | none => pure none
      | some name => if d.names.contains name then pure (some name) else throw .unspecified) = pure (some x)
    have hm : x ∈ d.names := Array.contains_iff_mem.mp (h x rfl)
    simp [h x rfl, hm, errOfBytes_errBytes, bind,
      pure, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont]

instance (d : ErrorDomain) : LawfulEnc (FiniteError d) where
  size_encode _ := rfl
  decode_encode e := by
    have hm : e.val ∈ d.names := Array.contains_iff_mem.mp e.property
    simp [Enc.encode, Enc.decode, errOfBytes_errBytes, e.property, hm, bind, pure,
      ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont]

instance (d : ErrorDomain) : LawfulEnc (Option (FiniteError d)) where
  size_encode e := by cases e <;> rfl
  decode_encode e := by
    cases e with
    | none => simp [Enc.encode, Enc.decode, errOfBytes_errBytes, bind, pure,
        ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont]
    | some x =>
      have hm : x.val ∈ d.names := Array.contains_iff_mem.mp x.property
      simp [Enc.encode, Enc.decode, errOfBytes_errBytes, x.property, hm,
        bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont]

theorem finiteError_encode_injective (d : ErrorDomain) :
    Function.Injective (Enc.encode : FiniteError d → Array Byte) := by
  intro x y h
  have := congrArg (Enc.decode : Array Byte → Result (FiniteError d)) h
  simp only [LawfulEnc.decode_encode] at this
  exact Except.ok.inj (Option.some.inj this)

theorem optionalFiniteError_encode_injective (d : ErrorDomain) :
    Function.Injective (Enc.encode : Option (FiniteError d) → Array Byte) := by
  intro x y h
  have := congrArg (Enc.decode : Array Byte → Result (Option (FiniteError d))) h
  simp only [LawfulEnc.decode_encode] at this
  exact Except.ok.inj (Option.some.inj this)

@[simp] theorem errorEnc_reject_zero (d : ErrorDomain) :
    (errorEnc d).decode #[.int 0, .int 0] = throw .unspecified := by
  change (errOfBytes #[.int 0, .int 0] >>= fun code =>
    match code with
    | some name => if d.names.contains name then pure name else throw .unspecified
    | none => throw .unspecified) = throw .unspecified
  simp [errOfBytes, bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.mk,
    ExceptT.bindCont, throw, throwThe, MonadExceptOf.throw]

theorem le_alignUp (n a : Nat) : n ≤ alignUp n a := by
  unfold alignUp
  split
  · omega
  · have h1 := Nat.div_add_mod (n + a - 1) a
    have h2 := Nat.mod_lt (n + a - 1) (by omega : a > 0)
    rw [Nat.mul_comm] at h1
    omega

/-! ## Block addresses (MM-1)

What holds for every placement (`Mem.place`): the address of a new block is a multiple of its
alignment (`Mem.newAddr_mod`), and the fallback `Mem.top` is past every block. The memory at
program start (`Mem.ofGlobals σ gs`) holds global `k` as block `k`, with its bytes, alignment and
kind, at an aligned address, and nothing else (`Mem.ofGlobals_block`, `Mem.ofGlobals_eq`). -/

theorem Mem.placed?_ok {m : Mem} {size align A : Nat} (h : m.placed? size align = some A) :
    0 < A ∧ A % align = 0 ∧ A + size ≤ 2 ^ 64 ∧ m.addrFree A size = true := by
  unfold Mem.placed? at h
  split at h
  · split at h
    · cases h; simpa [Mem.placeOk, and_assoc] using ‹m.placeOk _ size align = true›
    · cases h
  · cases h

private theorem foldl_top (l : List Block) (t : Nat) :
    t ≤ l.foldl (fun t blk => Nat.max t (blk.addr + blk.bytes.size + 1)) t ∧
      ∀ blk ∈ l, blk.addr + blk.bytes.size < l.foldl (fun t blk => Nat.max t (blk.addr + blk.bytes.size + 1)) t := by
  induction l generalizing t with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨h1, h2⟩ := ih (Nat.max t (x.addr + x.bytes.size + 1))
    simp only [List.foldl_cons, List.mem_cons]
    refine ⟨Nat.le_trans (Nat.le_max_left _ _) h1, fun blk hb => ?_⟩
    rcases hb with rfl | hb
    · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_trans (Nat.le_max_right _ _) h1)
    · exact h2 blk hb

/-- Every block, dead or live, ends below `Mem.top`. -/
theorem Mem.lt_top {m : Mem} {b : BlockId} {blk : Block} (h : m.blocks[b]? = some blk) :
    blk.addr + blk.bytes.size < m.top := by
  unfold Mem.top
  rw [← Array.foldl_toList]
  exact (foldl_top m.blocks.toList 4096).2 blk
    (Array.mem_toList_iff.mpr (Array.mem_of_getElem? h))

theorem Mem.newAddr_mod (m : Mem) (size align : Nat) (ha : 0 < align) :
    m.newAddr size align % align = 0 := by
  unfold Mem.newAddr
  split
  · exact (Mem.placed?_ok ‹_›).2.1
  · simp only [alignUp, Nat.ne_of_gt ha, ↓reduceIte, Nat.mul_mod_left]

theorem Mem.addGlobal_blocks (m : Mem) (bs : Array Byte) (a : Nat) (k : BlockKind) :
    (m.addGlobal bs a k).blocks =
      m.blocks.push { bytes := bs, align := a, kind := k, live := true, addr := m.newAddr bs.size a } :=
  rfl

private theorem foldl_addGlobal (gs : List (Array Byte × Nat × BlockKind)) (m : Mem) :
    let m' := gs.foldl (fun m (bs, a, k) => m.addGlobal bs a k) m
    m' = { m with blocks := m'.blocks } ∧ m'.blocks.size = m.blocks.size + gs.length ∧
      (∀ i < m.blocks.size, m'.blocks[i]? = m.blocks[i]?) ∧
      ∀ j (hj : j < gs.length), ∃ A, (0 < gs[j].2.1 → A % gs[j].2.1 = 0) ∧
        m'.blocks[m.blocks.size + j]? =
          some { bytes := gs[j].1, align := gs[j].2.1, kind := gs[j].2.2, live := true, addr := A } := by
  induction gs generalizing m with
  | nil => simp
  | cons g gs ih =>
    obtain ⟨bs, a, k⟩ := g
    obtain ⟨he, hs, hold, hnew⟩ := ih (m.addGlobal bs a k)
    simp only [List.foldl_cons] at he hs hold hnew ⊢
    have hsz : (m.addGlobal bs a k).blocks.size = m.blocks.size + 1 := by
      simp [Mem.addGlobal_blocks]
    refine ⟨?_, by rw [hs, hsz]; simp; omega, fun i hi => ?_, fun j hj => ?_⟩
    · rw [he]; rfl
    · rw [hold i (by omega)]; simp [Mem.addGlobal_blocks, Array.getElem?_push, Nat.ne_of_lt hi]
    · cases j with
      | zero =>
        refine ⟨m.newAddr bs.size a, fun ha => m.newAddr_mod bs.size a ha, ?_⟩
        rw [Nat.add_zero, hold m.blocks.size (by omega)]
        simp [Mem.addGlobal_blocks]
      | succ j =>
        obtain ⟨A, hA, hb⟩ := hnew j (by simp at hj; omega)
        refine ⟨A, hA, ?_⟩
        rw [hsz, show m.blocks.size + 1 + j = m.blocks.size + (j + 1) by omega] at hb
        simpa using hb

/-- The memory at program start is its blocks under the placement `σ`, every other field the
default. -/
theorem Mem.ofGlobals_eq (σ : Placement) (gs : List (Array Byte × Nat × BlockKind)) :
    Mem.ofGlobals σ gs = { blocks := (Mem.ofGlobals σ gs).blocks, place := σ } :=
  (foldl_addGlobal gs { place := σ }).1

/-! Every field of the memory at program start except `blocks` is the default. -/

@[simp] theorem Mem.ofGlobals_place (σ : Placement) (gs : List (Array Byte × Nat × BlockKind)) :
    (Mem.ofGlobals σ gs).place = σ := by
  rw [Mem.ofGlobals_eq]

@[simp] theorem Mem.ofGlobals_allocs (σ : Placement) (gs : List (Array Byte × Nat × BlockKind)) :
    (Mem.ofGlobals σ gs).allocs = 0 := by
  rw [Mem.ofGlobals_eq]

@[simp] theorem Mem.ofGlobals_failAt (σ : Placement) (gs : List (Array Byte × Nat × BlockKind)) :
    (Mem.ofGlobals σ gs).failAt = none := by
  rw [Mem.ofGlobals_eq]

@[simp] theorem Mem.ofGlobals_allocPolicy (σ : Placement) (gs : List (Array Byte × Nat × BlockKind)) :
    (Mem.ofGlobals σ gs).allocPolicy = {} := by
  rw [Mem.ofGlobals_eq]

@[simp] theorem Mem.ofGlobals_current (σ : Placement) (gs : List (Array Byte × Nat × BlockKind)) :
    (Mem.ofGlobals σ gs).current = 0 := by
  rw [Mem.ofGlobals_eq]

@[simp] theorem Mem.ofGlobals_clocks (σ : Placement) (gs : List (Array Byte × Nat × BlockKind)) :
    (Mem.ofGlobals σ gs).clocks = #[#[]] := by
  rw [Mem.ofGlobals_eq]

@[simp] theorem Mem.ofGlobals_threads (σ : Placement) (gs : List (Array Byte × Nat × BlockKind)) :
    (Mem.ofGlobals σ gs).threads = #[{ spawner := 0, joined := true }] := by
  rw [Mem.ofGlobals_eq]

@[simp] theorem Mem.ofGlobals_footprint (σ : Placement) (gs : List (Array Byte × Nat × BlockKind)) :
    (Mem.ofGlobals σ gs).footprint = #[] := by
  rw [Mem.ofGlobals_eq]

@[simp] theorem Mem.ofGlobals_atomics (σ : Placement) (gs : List (Array Byte × Nat × BlockKind)) :
    (Mem.ofGlobals σ gs).atomics = #[] := by
  rw [Mem.ofGlobals_eq]

@[simp] theorem Mem.ofGlobals_seen (σ : Placement) (gs : List (Array Byte × Nat × BlockKind)) :
    (Mem.ofGlobals σ gs).seen = #[] := by
  rw [Mem.ofGlobals_eq]

@[simp] theorem Mem.ofGlobals_nextMsg (σ : Placement) (gs : List (Array Byte × Nat × BlockKind)) :
    (Mem.ofGlobals σ gs).nextMsg = 0 := by
  rw [Mem.ofGlobals_eq]

@[simp] theorem Mem.ofGlobals_waiters (σ : Placement) (gs : List (Array Byte × Nat × BlockKind)) :
    (Mem.ofGlobals σ gs).waiters = #[] := by
  rw [Mem.ofGlobals_eq]

@[simp] theorem Mem.ofGlobals_woken (σ : Placement) (gs : List (Array Byte × Nat × BlockKind)) :
    (Mem.ofGlobals σ gs).woken = #[] := by
  rw [Mem.ofGlobals_eq]

@[simp] theorem Mem.ofGlobals_groups (σ : Placement) (gs : List (Array Byte × Nat × BlockKind)) :
    (Mem.ofGlobals σ gs).groups = #[] := by
  rw [Mem.ofGlobals_eq]

@[simp] theorem Mem.ofGlobals_allocators (σ : Placement) (gs : List (Array Byte × Nat × BlockKind)) :
    (Mem.ofGlobals σ gs).allocators = #[] := by
  rw [Mem.ofGlobals_eq]

theorem Mem.ofGlobals_size (σ : Placement) (gs : List (Array Byte × Nat × BlockKind)) :
    (Mem.ofGlobals σ gs).blocks.size = gs.length := by
  have := (foldl_addGlobal gs { place := σ }).2.1
  simpa [Mem.ofGlobals] using this

/-- Block `j` at program start is global `j`: its bytes, alignment and kind, live, at an address
that is a multiple of its alignment, under every placement. Nothing else is known about the
address. -/
theorem Mem.ofGlobals_block (σ : Placement) (gs : List (Array Byte × Nat × BlockKind)) (j : Nat)
    (hj : j < gs.length) :
    ∃ A, (0 < gs[j].2.1 → A % gs[j].2.1 = 0) ∧ (Mem.ofGlobals σ gs).blocks[j]? =
      some { bytes := gs[j].1, align := gs[j].2.1, kind := gs[j].2.2, live := true, addr := A } := by
  have := (foldl_addGlobal gs { place := σ }).2.2.2 j hj
  simpa [Mem.ofGlobals] using this

/-- The address of global `j` at program start under the placement `σ` (0 if there is no global
`j`). A theorem that holds for every `σ` can use only `Mem.globalAddr_mod` about it. -/
def Mem.globalAddr (σ : Placement) (gs : List (Array Byte × Nat × BlockKind)) (j : Nat) : Nat :=
  ((Mem.ofGlobals σ gs).blocks[j]?.map (·.addr)).getD 0

/-- Block `j` at program start, in a form for `simp`: global `j` at `Mem.globalAddr σ gs j`. -/
theorem Mem.ofGlobals_getElem? (σ : Placement) (gs : List (Array Byte × Nat × BlockKind))
    (j : Nat) : (Mem.ofGlobals σ gs).blocks[j]? = gs[j]?.map fun g =>
      { bytes := g.1, align := g.2.1, kind := g.2.2, live := true, addr := Mem.globalAddr σ gs j } := by
  by_cases hj : j < gs.length
  · obtain ⟨A, -, h⟩ := Mem.ofGlobals_block σ gs j hj
    simp [Mem.globalAddr, h, List.getElem?_eq_getElem hj]
  · have : (Mem.ofGlobals σ gs).blocks.size ≤ j := by rw [Mem.ofGlobals_size]; omega
    simp [Array.getElem?_eq_none this, List.getElem?_eq_none (Nat.le_of_not_lt hj)]

/-- A block at program start is aligned: its address is a multiple of its alignment, under every
placement. -/
theorem Mem.ofGlobals_addr_mod {σ : Placement} {gs : List (Array Byte × Nat × BlockKind)} {j : Nat}
    {blk : Block} (h : (Mem.ofGlobals σ gs).blocks[j]? = some blk) (ha : 0 < blk.align) :
    blk.addr % blk.align = 0 := by
  by_cases hj : j < gs.length
  · obtain ⟨A, hA, h'⟩ := Mem.ofGlobals_block σ gs j hj
    rw [h'] at h; cases h; exact hA ha
  · have : (Mem.ofGlobals σ gs).blocks.size ≤ j := by rw [Mem.ofGlobals_size]; omega
    rw [Array.getElem?_eq_none this] at h; cases h

/-! ## Error unions -/

/-- The error code and the payload of `E!T` do not overlap, and both are inside it. -/
theorem errUnion_bounds (s a : Nat) :
    (errUnionOffsets s a).1 + 2 ≤ errUnionSize s a ∧
      (errUnionOffsets s a).2 + s ≤ errUnionSize s a ∧
      ((errUnionOffsets s a).1 + 2 ≤ (errUnionOffsets s a).2 ∨
        (errUnionOffsets s a).2 + s ≤ (errUnionOffsets s a).1) := by
  have hd : (errUnionOffsets s a).1 + 2 ≤ (errUnionOffsets s a).2 ∨
      (errUnionOffsets s a).2 + s ≤ (errUnionOffsets s a).1 := by
    unfold errUnionOffsets
    split
    · right; simp_all
    · split
      · right; simpa using le_alignUp s 2
      · left; simpa using le_alignUp 2 a
  have hsz : errUnionSize s a =
      alignUp (Max.max ((errUnionOffsets s a).1 + 2) ((errUnionOffsets s a).2 + s)) (Nat.max a 2) := by
    unfold errUnionSize
    generalize errUnionOffsets s a = r
    obtain ⟨eo, po⟩ := r
    rfl
  rw [hsz]
  have hS := le_alignUp (Max.max ((errUnionOffsets s a).1 + 2) ((errUnionOffsets s a).2 + s))
    (Nat.max a 2)
  have := Nat.le_max_left ((errUnionOffsets s a).1 + 2) ((errUnionOffsets s a).2 + s)
  have := Nat.le_max_right ((errUnionOffsets s a).1 + 2) ((errUnionOffsets s a).2 + s)
  exact ⟨by omega, by omega, hd⟩

/-- `E!T` in memory: an error union reads back as itself. -/
instance {α : Type} [Enc α] [LawfulEnc α] : LawfulEnc (Except ErrName α) where
  size_encode v := by
    obtain ⟨h1, h2, -⟩ := errUnion_bounds (Enc.size α) (Enc.align α)
    have hx : ∀ x : α, (Enc.encode x).size = Enc.size α := LawfulEnc.size_encode
    simp only [Enc.encode, Enc.size]
    generalize errUnionSize (Enc.size α) (Enc.align α) = S at h1 h2 ⊢
    generalize errUnionOffsets (Enc.size α) (Enc.align α) = r at h1 h2 ⊢
    obtain ⟨eo, po⟩ := r
    have he : ∀ e, (errBytes e).size = 2 := by intro e; cases e <;> rfl
    cases v with
    | error e => simp only; rw [writeBytes_size _ _ _ (by simp [he]; omega)]; simp
    | ok x =>
      simp only
      rw [writeBytes_size _ _ _ (by rw [writeBytes_size _ _ _ (by simp [he]; omega), hx]; simp; omega),
        writeBytes_size _ _ _ (by simp [he]; omega)]
      simp
  decode_encode v := by
    obtain ⟨h1, h2, hd⟩ := errUnion_bounds (Enc.size α) (Enc.align α)
    have hxs : ∀ x : α, (Enc.encode x).size = Enc.size α := LawfulEnc.size_encode
    simp only [Enc.encode, Enc.decode]
    generalize errUnionSize (Enc.size α) (Enc.align α) = S at h1 h2 ⊢
    generalize errUnionOffsets (Enc.size α) (Enc.align α) = r at h1 h2 hd ⊢
    obtain ⟨eo, po⟩ := r
    simp only at h1 h2 hd ⊢
    have he : ∀ e, (errBytes e).size = 2 := by intro e; cases e <;> rfl
    cases v with
    | error e =>
      have hx := extract_writeBytes (Array.replicate S .undef) eo (errBytes (some e))
        (by simp [he]; omega)
      rw [he] at hx
      simp only [hx]
      simp [errOfBytes, errBytes, bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.mk,
        ExceptT.bindCont]
    | ok x =>
      have ha1 : (writeBytes (Array.replicate S Byte.undef) eo (errBytes none)).size = S := by
        rw [writeBytes_size _ _ _ (by simp [he]; omega)]; simp
      have hw := extract_writeBytes (writeBytes (Array.replicate S Byte.undef) eo (errBytes none))
        po (Enc.encode x) (by rw [ha1, hxs]; omega)
      rw [hxs] at hw
      have hc := extract_writeBytes_disjoint
        (writeBytes (Array.replicate S Byte.undef) eo (errBytes none)) po (Enc.encode x) eo 2
        (by rw [ha1, hxs]; omega) (by omega) (by rw [hxs]; omega)
      have hc' := extract_writeBytes (Array.replicate S Byte.undef) eo (errBytes none)
        (by simp [he]; omega)
      rw [he] at hc'
      simp only [hw, hc, hc', LawfulEnc.decode_encode x]
      simp [errOfBytes, errBytes, bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.mk,
        ExceptT.bindCont, Functor.map, ExceptT.map]

/-- The bytes of an error union that holds a payload: the error code is 0, and the payload
bytes decode to the payload. -/
theorem errUnion_decode_ok {α : Type} [Enc α] {bs : Array Byte} {x : α}
    (h : (Enc.decode bs : Result (Except ErrName α)) = pure (.ok x)) :
    errOfBytes (bs.extract (errUnionOffsets (Enc.size α) (Enc.align α)).1
        ((errUnionOffsets (Enc.size α) (Enc.align α)).1 + 2)) = pure none ∧
      (Enc.decode (bs.extract (errUnionOffsets (Enc.size α) (Enc.align α)).2
        ((errUnionOffsets (Enc.size α) (Enc.align α)).2 + Enc.size α)) : Result α) = pure x := by
  simp only [Enc.decode] at h
  generalize errUnionOffsets (Enc.size α) (Enc.align α) = r at h ⊢
  obtain ⟨eo, po⟩ := r
  simp only at h ⊢
  generalize errOfBytes (bs.extract eo (eo + 2)) = re at h ⊢
  generalize (Enc.decode (bs.extract po (po + Enc.size α)) : Result α) = rd at h ⊢
  match re, rd, h with
  | some (.ok none), some (.ok y), h =>
    simp [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, pure, ExceptT.pure, Functor.map,
      ExceptT.map] at h
    cases h; exact ⟨rfl, rfl⟩
  | some (.ok none), some (.error _), h =>
    simp [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, pure, ExceptT.pure, Functor.map,
      ExceptT.map] at h <;> cases h
  | some (.ok none), none, h =>
    simp [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, pure, ExceptT.pure, Functor.map,
      ExceptT.map] at h <;> cases h
  | some (.ok (some _)), _, h =>
    simp [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, pure, ExceptT.pure] at h <;> cases h
  | some (.error _), _, h =>
    simp [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, pure, ExceptT.pure] at h <;> cases h
  | none, _, h =>
    simp [bind, ExceptT.bind, ExceptT.mk, pure, ExceptT.pure] at h <;> cases h

/-- A payload write to an error union that holds a payload: it then holds the new payload. -/
theorem errUnion_decode_setPayload {α : Type} [Enc α] [LawfulEnc α] {bs : Array Byte} (y : α)
    (hs : bs.size = errUnionSize (Enc.size α) (Enc.align α))
    (h : errOfBytes (bs.extract (errUnionOffsets (Enc.size α) (Enc.align α)).1
        ((errUnionOffsets (Enc.size α) (Enc.align α)).1 + 2)) = pure none) :
    (Enc.decode (writeBytes bs (errUnionOffsets (Enc.size α) (Enc.align α)).2 (Enc.encode y)) :
      Result (Except ErrName α)) = pure (.ok y) := by
  obtain ⟨h1, h2, hd⟩ := errUnion_bounds (Enc.size α) (Enc.align α)
  have hy := LawfulEnc.size_encode y
  simp only [Enc.decode]
  generalize errUnionSize (Enc.size α) (Enc.align α) = S at hs h1 h2
  generalize errUnionOffsets (Enc.size α) (Enc.align α) = r at h h1 h2 hd ⊢
  obtain ⟨eo, po⟩ := r
  simp only at h h1 h2 hd ⊢
  have hw := extract_writeBytes bs po (Enc.encode y) (by omega)
  rw [hy] at hw
  rw [extract_writeBytes_disjoint _ _ _ _ _ (by omega) (by omega) (by omega), h, hw,
    LawfulEnc.decode_encode y]
  rfl

/-! ## `extern` unions (`ZigLean/Union.lean`) -/

/-- The first `k` bytes of `Raw.ofArray n bs` are the first `k` bytes of `bs`, if `bs` has them. -/
theorem Raw.extract_ofArray {n k : Nat} {bs : Array Byte} (hk : k ≤ n) (hb : k ≤ bs.size) :
    (Raw.ofArray n bs).toArray.extract 0 k = bs.extract 0 k := by
  apply Array.ext
  · simp; omega
  · intro i h1 h2
    simp only [Array.size_extract, Vector.size_toArray] at h1
    simp only [Array.getElem_extract, Raw.ofArray, Vector.toArray_ofFn, Array.getElem_ofFn,
      Nat.zero_add, Array.getD, dite_eq_left (show i < bs.size by omega)]
    rfl

/-- An `extern` union: a read of the field that `union_init` wrote gives its value. -/
theorem Raw.get_init {α : Type} [Enc α] [LawfulEnc α] (n : Nat) (v : α) (h : Enc.size α ≤ n) :
    Raw.get α (Raw.init n v) = pure v := by
  have hs := LawfulEnc.size_encode v
  simp only [Raw.get, Raw.init]
  rw [Raw.extract_ofArray h (by omega), ← hs, Array.extract_size]
  exact LawfulEnc.decode_encode v

/-- An `extern` union: a read of the field that a field write wrote gives its value. -/
theorem Raw.get_set {α : Type} [Enc α] [LawfulEnc α] {n : Nat} (u : Vector Byte n) (v : α)
    (h : Enc.size α ≤ n) : Raw.get α (Raw.set u v) = pure v := by
  have hs := LawfulEnc.size_encode v
  have hw : (writeBytes u.toArray 0 (Enc.encode v)).extract 0 (0 + (Enc.encode v).size) = Enc.encode v :=
    extract_writeBytes _ 0 _ (by simp; omega)
  simp only [Raw.get, Raw.set]
  rw [Raw.extract_ofArray h (by rw [writeBytes_size _ _ _ (by simp; omega)]; simp; omega), ← hs]
  simp only [Nat.zero_add] at hw
  rw [hw]
  exact LawfulEnc.decode_encode v

/-! ## Loops in a memory function

`Zig.loop` over `MM` (locals over `MemM`): the same rules as `loop_run`/`loop_spec`
(`ZigLean/Loop.lean`), with the memory as a second state. -/

/-- One unfolding of a loop over `MM`. -/
theorem loop_run_mm {σ ε : Type} (body : MM σ ε) (again : ε → Bool) (s : σ) (m : Mem) :
    ((loop body again).run s).run m =
      (do let ((e, s'), m') ← (body.run s).run m
          if again e then ((loop body again).run s').run m' else pure ((e, s'), m')) := by
  conv => lhs; rw [loop]
  simp only [StateT.run, bind, StateT.bind]
  congr 1
  funext p
  rcases p with ⟨⟨e, s'⟩, m'⟩
  cases again e <;> rfl

/-- `loop_spec` over `MM`: an invariant on the locals and the memory, a measure that each
repeating iteration makes smaller, and a post-condition on the exit that ends the loop. -/
theorem loop_spec_mm {σ ε : Type} (body : MM σ ε) (again : ε → Bool)
    (inv : σ → Mem → Prop) (meas : σ → Mem → Nat) (post : ε → σ → Mem → Prop)
    (step : ∀ s m, inv s m → ∃ e s' m', (body.run s).run m = pure ((e, s'), m') ∧
      (if again e then inv s' m' ∧ meas s' m' < meas s m else post e s' m')) :
    ∀ s m, inv s m → ∃ e s' m', ((loop body again).run s).run m = pure ((e, s'), m') ∧
      post e s' m' := by
  intro s m
  induction h : meas s m using Nat.strongRecOn generalizing s m with
  | _ n ih =>
    intro hs
    obtain ⟨e, s', m', hrun, hnext⟩ := step s m hs
    rw [loop_run_mm, hrun]
    cases ha : again e
    · simp only [ha, Bool.false_eq_true, ↓reduceIte] at hnext
      exact ⟨e, s', m', by simp [ha], hnext⟩
    · simp only [ha, ↓reduceIte] at hnext
      obtain ⟨hinv, hlt⟩ := hnext
      obtain ⟨e', s'', m'', hr, hpost⟩ := ih (meas s' m') (h ▸ hlt) s' m' rfl hinv
      exact ⟨e', s'', m'', by simp [ha, hr], hpost⟩

/-- Two atomic accesses never race: the scheduler orders them. -/
theorem racePair_atomic {a b : AccessKind} (ha : a.isAtomic = true) (hb : b.isAtomic = true) :
    racePair a b = none := by
  simp [racePair, ha, hb]

theorem size_encode_u32 (v : BitVec 32) : (Enc.encode v).size = 4 := LawfulEnc.size_encode v

theorem size_encode_ptr (p : Ptr) : (Enc.encode p).size = 8 := LawfulEnc.size_encode p

/-- `@memcpy` with equal counts between different blocks, or of no bytes, is `@memmove`: its
illegal-behaviour checks pass. -/
theorem memcpy_eq_memmove {size da sa : Nat} {dst src : Ptr} {n m : BitVec 64} (hm : n = m)
    (h : dst.block ≠ src.block ∨ n.toNat * size = 0) :
    memcpy size da sa dst src n m = memmove size da sa dst src n := by
  subst hm
  unfold memcpy Ptr.overlaps
  rcases h with h | h <;> simp [h]

/-- An index below the length passes `slice_elem_val`'s bounds check. -/
theorem checkIndex_bind_of_lt {α : Type} {s : Slice} {i : BitVec 64} (h : i.toNat < s.len.toNat)
    (x : MemM α) : (checkIndex s i >>= fun _ => x) = x := by
  simp [checkIndex, h]

end Zig
