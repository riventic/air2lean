import ZigLean.Sep.Full.Atomic
import ZigLean.Sep.Full.Word

/-!
# The newest choice of an atomic op at a word

Every atomic op at a valid word (`Word.Ok`) has a run for its first oracle choice (`c = 0`), and
that run uses the word's newest write: a load returns its value, an RMW updates it, and a weak
`cmpxchg` that expects it succeeds. A futex wait of a thread that is not woken compares the
newest value (`Thread.futexWait`), and a futex wake at an address where nothing waits changes
nothing. Each run is also a native full-state step of the empty frame (`FStepIn`), and it keeps
every word apart from it (`Ok.apart_run`).

These are the runs of a schedule that a proof exhibits, for a thread that reads the newest
write (`ZigLean/Sep/Full/CondEpoch.lean`). What every run does, whatever the choice, is the
native op lemmas' part (`Ok.load_native`, `Ok.rmw_native`, `Ok.weakCas_native`,
`Ok.futexWait_native`).
-/

namespace Zig

open Conc Proto Full

/-- An RMW write returns in every memory. -/
theorem rmwWrite_run_ne_none {n : Nat} (li pos : Nat) (ord : AtomicOrder) (rd : Msg)
    (new : BitVec n) : ∀ m, ((rmwWrite li pos ord rd new).run m).run ≠ none := by
  unfold rmwWrite
  have hrest : ∀ m, ((do
      let m ← get
      let cl := m.clocks[m.current]!
      let id := m.nextMsg
      let msg : Msg :=
        { id := id, bytes := padTo (intSize n) (intBytes new), clock := cl,
          relClock := (if ord.isRel then VClock.merge rd.relClock cl else rd.relClock),
          rmwOf := some rd.id, writer := some m.current }
      insertMsg li (pos + 1) msg
      observe li id : MemM Unit).run m).run ≠ none :=
    M.bind_run_ne_none M.get_run_ne_none fun _ =>
      M.bind_run_ne_none (M.modify_run_ne_none _) fun _ => M.modify_run_ne_none _
  split
  · exact M.bind_run_ne_none (M.modify_run_ne_none _) fun _ => hrest
  · exact hrest

/-- An atomic RMW returns a value or an error, for every pointer, oracle choice and memory. -/
theorem atomicRmwAt_run_ne_none {n : Nat} (c : Nat) (op : RmwOp) (signed : Bool)
    (ord : AtomicOrder) (align : Nat) (p : Ptr) (v : BitVec n) :
    ∀ m, ((atomicRmwAt c op signed ord align p v).run m).run ≠ none := by
  unfold atomicRmwAt
  refine M.bind_run_ne_none (loadPrep_run_ne_none _ _ _ _ _) fun r => ?_
  obtain ⟨li, opts⟩ := r
  dsimp only
  split
  · exact M.bind_run_ne_none M.get_run_ne_none fun _ =>
      M.bind_run_ne_none (M.lift_run_ne_none (intOfBytes_run_ne_none _ _ _)) fun _ =>
        M.bind_run_ne_none (rmwWrite_run_ne_none _ _ _ _ _) fun _ => M.pure_run_ne_none _
  · exact M.throw_run_ne_none _

/-- The shared CAS preparation returns in every memory. -/
theorem casReadPrep_run_ne_none (n align : Nat) (p : Ptr) :
    ∀ m, ((casReadPrep n align p).run m).run ≠ none := by
  unfold casReadPrep
  refine M.bind_run_ne_none M.get_run_ne_none fun m => ?_
  refine M.bind_run_ne_none (M.lift_run_ne_none (m.accessW_run_ne_none _ _ _)) fun r => ?_
  obtain ⟨b, _, o⟩ := r
  refine M.bind_run_ne_none (recordAccess_run_ne_none _ _ _ _) fun _ =>
    M.bind_run_ne_none (locIdx_run_ne_none _ _ _) fun _ => ?_
  exact M.bind_run_ne_none M.get_run_ne_none fun _ => M.pure_run_ne_none _

/-- A weak `cmpxchg` returns a result or an error, for every pointer, oracle choice and memory. -/
theorem cmpxchgWeakAt_run_ne_none {n : Nat} (c : Nat) (succ fail : AtomicOrder) (align : Nat)
    (p : Ptr) (expected new : BitVec n) :
    ∀ m, ((cmpxchgWeakAt c succ fail align p expected new).run m).run ≠ none := by
  unfold cmpxchgWeakAt weakCasPrep
  refine M.bind_run_ne_none (M.bind_run_ne_none (casReadPrep_run_ne_none _ _ _) fun _ =>
    M.bind_run_ne_none M.get_run_ne_none fun _ => M.pure_run_ne_none _) fun r => ?_
  obtain ⟨li, opts⟩ := r
  dsimp only
  split
  · refine M.bind_run_ne_none M.get_run_ne_none fun _ =>
      M.bind_run_ne_none (M.lift_run_ne_none (intOfBytes_run_ne_none _ _ _)) fun _ => ?_
    split
    · unfold casMarkWrite
      refine M.bind_run_ne_none (M.bind_run_ne_none M.get_run_ne_none fun m =>
        M.bind_run_ne_none (M.lift_run_ne_none (m.accessW_run_ne_none _ _ _)) fun r => ?_)
        fun _ => M.bind_run_ne_none (rmwWrite_run_ne_none _ _ _ _ _) fun _ =>
          M.pure_run_ne_none _
      obtain ⟨b, _, o⟩ := r
      exact recordAccess_run_ne_none _ _ _ _
    · refine M.bind_run_ne_none (M.modify_run_ne_none _) fun _ => ?_
      split
      · exact M.bind_run_ne_none (M.modify_run_ne_none _) fun _ => M.pure_run_ne_none _
      · exact M.pure_run_ne_none _
  · exact M.throw_run_ne_none _

namespace Thread

/-- A futex wake at `p` where no thread waits wakes no thread: the memory stays as it is. -/
theorem futexWake_run_idle {m : Mem} {p : Ptr} {n : Nat} {cs : List Nat}
    (hq : ∀ w ∈ m.waiters, w.2 ≠ p) :
    ((futexWake p n cs).run m).run = some (.ok ((), m)) := by
  have hf : m.waiters.filter (·.2 == p) = #[] := by
    rw [Array.filter_eq_empty_iff]
    intro w hw
    simpa using hq w hw
  have hs : wakeSet m.waiters p n cs = #[] := by
    unfold wakeSet
    rw [hf]
    cases n <;> rfl
  show (some (.ok ((), { m with waiters := m.waiters.filter
      (fun w => !(wakeSet m.waiters p n cs).contains w.1),
    woken := m.woken ++ wakeSet m.waiters p n cs })) : Option (Except Error (Unit × Mem))) = _
  rw [hs]
  simp

end Thread

namespace Conc.Word

variable {n nb : Nat} {W : Word n nb}

/-- One write has one value. -/
theorem Entry.val_inj {x : Entry} {a b : BitVec n} (ha : x.Val a) (hb : x.Val b) : a = b := by
  unfold Entry.Val at ha hb
  rw [ha] at hb
  cases hb
  rfl

/-- The first choice of a count. -/
private theorem first_choice (k : Nat) : 0 < k ∨ k = 0 ∧ 0 = 0 := by omega

/-- The first readable message of a filter that keeps it. -/
private theorem filter_first {α : Type} {a : Array α} {x : α} {p : α → Bool} (h : a[0]? = some x)
    (hp : p x = true) : (a.filter p)[0]? = some x := by
  rcases a with ⟨l⟩
  cases l with
  | nil => simp at h
  | cons y l =>
    simp only [List.getElem?_toArray, List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp [List.filter_cons, hp]

/-- **A load of the newest write**: the first choice of a load at a valid word returns the
value the word holds, and keeps it. -/
theorem Ok.load_newest {m : Mem} {ord : AtomicOrder} {v : BitVec n} (hw : W.Ok m)
    (ht : m.current < m.threads.size) (hcs : m.clocks.size = m.threads.size)
    (hv : W.Holds m v) :
    ∃ m', ((atomicLoadAt (n := n) 0 ord nb W.ptr).run m).run = some (.ok (v, m')) ∧
      W.Ok m' ∧ W.Holds m' v ∧ FStepIn (fun _ => none) m m' := by
  obtain ⟨⟨v', m'⟩, h⟩ := Result.exists_ok_of_run_ne_none (atomicLoadAt_run_ne_none (n := n) 0 ord nb W.ptr m)
    (hw.load_noErr_native ht hcs (first_choice _))
  have hcc : m.current < m.clocks.size := by rw [hcs]; exact ht
  obtain ⟨_, _, _, _, _, hh, hw'⟩ := hw.load_native rfl ht hcs h
  have hs := atomicLoad_fstep (hF := fun _ => none) hw hcc (fun _ _ _ => rfl) h
  obtain ⟨b, blk, o, li, m₁, pos, hacc, _, hp, hpos, hval, -⟩ := atomicLoadAt_ok h
  obtain ⟨blk₀, _, _, _, hacc₀, _⟩ := hw.access
  rw [W.sz_eq, hacc₀] at hacc
  rw [W.sz_eq] at hp
  cases hacc
  obtain ⟨l, hl, hw₁, hh₁, _, _⟩ := hw.prep_native rfl ht hcs rfl hp
  obtain ⟨_, h0, _, _, _⟩ := hw₁.loc li l hl
  have hl0 := (loc_get hl).2.2
  rw [readOpts_zero (m := m₁) (li := li) (by rw [hl0]; exact h0), hl0] at hpos
  cases hpos
  rw [hl0] at hval
  have hlast := val_of hl (by omega) hval
  rw [← hist_size hl, hh₁] at hlast
  obtain rfl := Entry.val_inj hlast (hw.holds_last.mp hv)
  exact ⟨m', h, hw', hw'.holds_last.mpr (by rw [hh]; exact hlast), hs⟩

/-- **An RMW of the newest write**: the first choice of an RMW at a valid word reads the value
the word holds and leaves the word holding the op's result. -/
theorem Ok.rmw_newest {m : Mem} {op : RmwOp} {signed : Bool} {ord : AtomicOrder}
    {v₀ v : BitVec n} (hw : W.Ok m) (ht : m.current < m.threads.size)
    (hcs : m.clocks.size = m.threads.size) (hv : W.Holds m v₀) :
    ∃ m', ((atomicRmwAt 0 op signed ord nb W.ptr v).run m).run = some (.ok (v₀, m')) ∧
      W.Ok m' ∧ W.Holds m' (op.apply signed v₀ v) ∧ FStepIn (fun _ => none) m m' := by
  obtain ⟨⟨old, m'⟩, h⟩ := Result.exists_ok_of_run_ne_none
    (atomicRmwAt_run_ne_none 0 op signed ord nb W.ptr v m) (hw.rmw_noErr_native ht hcs (first_choice _))
  have hcc : m.current < m.clocks.size := by rw [hcs]; exact ht
  obtain ⟨hold, hw', hU, _, _⟩ := hw.rmw_native rfl ht hcs h
  obtain rfl := Entry.val_inj hold (hw.holds_last.mp hv)
  exact ⟨m', h, hw', hU, atomicRmw_fstep hw hcc (fun _ _ _ => rfl) h⟩

/-- **A weak `cmpxchg` of the newest write**: the first choice of a weak `cmpxchg` at a valid
word that expects the value the word holds succeeds (the first choices are the strong ones,
newest first) and leaves the word holding the new value. -/
theorem Ok.weakCas_newest {m : Mem} {succ fail : AtomicOrder} {exp new : BitVec n}
    (hw : W.Ok m) (ht : m.current < m.threads.size) (hcs : m.clocks.size = m.threads.size)
    (hv : W.Holds m exp) :
    ∃ m', ((cmpxchgWeakAt 0 succ fail nb W.ptr exp new).run m).run = some (.ok (none, m')) ∧
      W.Ok m' ∧ W.Holds m' new ∧ FStepIn (fun _ => none) m m' := by
  obtain ⟨⟨r, m'⟩, h⟩ := Result.exists_ok_of_run_ne_none
    (cmpxchgWeakAt_run_ne_none 0 succ fail nb W.ptr exp new m) (hw.weakCas_noErr_native ht hcs (first_choice _))
  have hcc : m.current < m.clocks.size := by rw [hcs]; exact ht
  have hs := cmpxchgWeak_fstep (hF := fun _ => none) hw hcc (fun _ _ _ => rfl) h
  have hr : r = none := by
    obtain ⟨b, blk, o, li, m₁, pos, spurious, old, hacc, _, hp, hpos, hold, hcase⟩ :=
      cmpxchgWeakAt_ok h
    obtain ⟨blk₀, _, _, _, _, haw₀⟩ := hw.access
    rw [W.sz_eq, haw₀] at hacc
    rw [W.sz_eq] at hp
    cases hacc
    obtain ⟨l, hl, hw₁, hh₁, _, _⟩ := hw.prep_native rfl ht hcs rfl hp
    obtain ⟨_, h0, _, _, _⟩ := hw₁.loc li l hl
    have hl0 := (loc_get hl).2.2
    have hz : (readOpts m₁ li false)[0]? = some (l.msgs.size - 1) := by
      rw [readOpts_zero (m := m₁) (li := li) (by rw [hl0]; exact h0), hl0]
    have hc : (casOpts m₁ li exp)[0]? = some (l.msgs.size - 1) := by
      unfold casOpts
      refine filter_first hz ?_
      rw [hl0]
      simp [ALoc.hasRmwAfter_last]
    have hsz : 0 < ((casOpts m₁ li exp).map fun pos => (pos, false)).size := by
      rw [Array.size_map]
      obtain ⟨h0', _⟩ := Array.getElem?_eq_some_iff.mp hc
      exact h0'
    rw [weakCasOpts_eq, Array.getElem?_append_left hsz, Array.getElem?_map, hc] at hpos
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hpos
    obtain ⟨rfl, rfl⟩ := hpos
    rw [hl0] at hold
    have hlast := val_of hl (by omega) hold
    rw [← hist_size hl, hh₁] at hlast
    obtain rfl := Entry.val_inj hlast (hw.holds_last.mp hv)
    rcases hcase with ⟨_, _, hr, _⟩ | ⟨hne, _⟩
    · exact hr
    · exact absurd ⟨rfl, rfl⟩ hne
  subst hr
  obtain ⟨hw', hcase⟩ := hw.weakCas_native rfl ht hcs h
  rcases hcase with ⟨_, _, hU, _⟩ | ⟨_, _, hr, _⟩
  · exact ⟨m', h, hw', hU, hs⟩
  · cases hr

/-- **An actual op at a word keeps every word apart from it**: its validity and its writes. -/
theorem Ok.apart_run {n' nb' : Nat} {V : Word n' nb'} {m m' : Mem} (hw : W.Ok m) (hv : V.Ok m)
    (hc : m.current < m.clocks.size) (hap : W.b ≠ V.b ∨ W.o + nb ≤ V.o ∨ V.o + nb' ≤ W.o)
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
    V.Ok m' ∧ V.hist m' = V.hist m :=
  preserve_apart hv (fun _ hoff => actualRun_fstep hw hc hoff hop)
    (fun l hl => (actualRun_rest hw hc hop).heap l hl) hap

/-- A word with the same writes holds the same value. -/
theorem Ok.holds_of_hist {m m' : Mem} {v : BitVec n} (hw : W.Ok m) (hw' : W.Ok m')
    (hh : W.hist m' = W.hist m) (hv : W.Holds m v) : W.Holds m' v :=
  hw'.holds_last.mpr (by rw [hh]; exact hw.holds_last.mp hv)

/-- A word is valid, with the same writes, in a memory with another current thread. -/
theorem Ok.withCurrent {m : Mem} (hw : W.Ok m) (t : ThreadId) :
    W.Ok { m with current := t } ∧ W.hist { m with current := t } = W.hist m :=
  hw.fields_native rfl rfl rfl rfl fun _ => VClock.le_refl _

section futex

variable {W : Word 32 4}

/-- **A futex wait at a valid word** of a thread that is not woken compares the word's newest
value `v` with `e`: it sleeps exactly if they are equal. -/
theorem Ok.futexWait_newest {m : Mem} {e v : BitVec 32} (hw : W.Ok m)
    (ht : m.current < m.threads.size) (hwk : m.woken.contains m.current = false)
    (hv : W.Holds m v) :
    ((Thread.futexWait W.ptr e).run m).run = some (.ok (decide (v = e),
      if v = e then
        { m.recordAt W.b W.o 4 .atomicRead with waiters := m.waiters.push (m.current, W.ptr) }
      else m.recordAt W.b W.o 4 .atomicRead)) := by
  obtain ⟨blk, hb, -, -, ha, -⟩ := hw.access
  rw [holds_bytes hb] at hv
  exact futexWait_run_go hwk ha (hw.noRace rfl ht) hv

end futex

end Conc.Word

end Zig
