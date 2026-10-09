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
  simp [hv, pure, ExceptT.pure, ExceptT.mk, bind, ExceptT.bind, ExceptT.bindCont, StateT.run,
    liftM, monadLift, MonadLift.monadLift, StateT.lift]

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
      Enc.decode (blk.bytes.extract o (o + Enc.size α)) = pure v ∧
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
      generalize hd2 : (Enc.decode (blk.bytes.extract o (o + Enc.size α)) : Result α) = d at h
      match d, hd2, h with
      | none, _, h => simp at h
      | some (.error _), _, h =>
        simp only [ExceptT.bindCont, Option.bind_some] at h; cases h
      | some (.ok w), hd2, h =>
        simp only [ExceptT.bindCont, Option.bind_some] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨b, blk, o, rfl, hd2, rfl⟩

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

/-! ## Error unions -/

theorem le_alignUp (n a : Nat) : n ≤ alignUp n a := by
  unfold alignUp
  split
  · omega
  · have h1 := Nat.div_add_mod (n + a - 1) a
    have h2 := Nat.mod_lt (n + a - 1) (by omega : a > 0)
    rw [Nat.mul_comm] at h1
    omega

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

end Zig
