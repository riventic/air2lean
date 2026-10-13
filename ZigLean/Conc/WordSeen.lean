import ZigLean.Conc.Word
import ZigLean.Conc.Clock

/-!
# A thread's read floor at a shared word

A thread that read or wrote a message of an atomic location does not read an older one later
(read-read coherence): the model keeps each thread's view of each location (`Mem.seen`,
`Mem.seenAt`: the id of the message it read or wrote last there), and an atomic read picks a
message at or after the position of that message (`floorPos`). This file gives that floor at a
shared word (`ZigLean/Conc/Word.lean`) as a position in the word's writes (`Word.ownPos`, the
position in `Word.hist`):

- **The ops** (`Ok.load_seen`, `Ok.cas_seen`, `Ok.rmw_seen`): an op of thread `t` reads at or
  after `t`'s floor, afterwards `t`'s floor is the write it read or wrote, and no other
  thread's floor gets smaller.
- **The steps that keep the word keep every floor**: a step of a thread on its own part whose
  frame has the word's bytes (`ownPos_fstep`: the frame keeps the views of its locations,
  `AMap.seenAt_frame`), and a step that keeps the word and the views of its location
  (`ownPos_keep`).
- The floor is a position because the word's messages have distinct ids (`Word.Fresh`): each op
  and each of these steps keeps that (`Fresh.fstep`, `Fresh.keep`, and the ops).

So a thread that read write `j` of a word reads write `j` or a later one at its next op there,
whatever the other threads do in between.
-/

namespace Zig
namespace Conc
namespace Word

open Proto

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

/-- **A step that keeps the word and every view of its location keeps every floor.** -/
theorem ownPos_keep {m m' : Mem} (hk : W.Keep m m')
    (hs : ∀ u i l, W.Loc m i l → m'.seenAt u i = m.seenAt u i) (u : ThreadId) :
    W.ownPos m' u = W.ownPos m u := by
  cases hf : m.atomics.findIdx? (fun l => l.block == W.b && l.off == W.o) with
  | some i =>
    have hl := loc_of_find hf
    rw [ownPos_loc hl, ownPos_loc ((hk.loc _ _).mpr hl), hs u i _ hl]
  | none =>
    have hn : ∀ i l, ¬ W.Loc m i l := fun i l hl => by rw [hl.1] at hf; cases hf
    rw [ownPos_none hn, ownPos_none fun i l hl => hn i l ((hk.loc i l).mp hl)]

theorem Fresh.keep {m m' : Mem} (hf : W.Fresh m) (hk : W.Keep m m')
    (hn : m.nextMsg ≤ m'.nextMsg) : W.Fresh m' := fun i l hl j hj =>
  let ⟨h1, h2⟩ := hf i l ((hk.loc i l).mp hl) j hj
  ⟨Nat.lt_of_lt_of_le h1 hn, h2⟩

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

/-- **A step of a thread on its own part keeps every thread's floor** at a word whose bytes its
frame has (`FStepIn`; `hok`: the word's location has the word's size, as under `Word.Ok`). -/
theorem ownPos_fstep {m m' : Mem} {hF : Heap} (hs : FStepIn hF m m')
    (hwF : ∀ x, W.o ≤ x → x < W.o + nb → hF (W.b, x) ≠ none)
    (hok : ∀ i l, W.Loc m i l → l.len = nb) (u : ThreadId) : W.ownPos m' u = W.ownPos m u := by
  obtain ⟨σ, ha⟩ := hs.atomics
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

theorem Fresh.fstep {m m' : Mem} {hF : Heap} (hf : W.Fresh m) (hs : FStepIn hF m m')
    (hwF : ∀ x, W.o ≤ x → x < W.o + nb → hF (W.b, x) ≠ none)
    (hok : ∀ i l, W.Loc m i l → l.len = nb) : W.Fresh m' := by
  obtain ⟨σ, ha⟩ := hs.atomics
  obtain ⟨hin, hcov⟩ := frame_has hwF hok
  intro j l hl k hk
  obtain ⟨i, hi⟩ := (ha.first_iff pred_congr hin hcov l).mpr ⟨j, hl⟩
  obtain ⟨h1, h2⟩ := hf i l hi k hk
  exact ⟨Nat.lt_of_lt_of_le h1 hs.nextMsg, h2⟩

/-! ## The ops at the word -/

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

/-- The location `i` with another location of the same place. -/
theorem loc_set {m : Mem} {i : Nat} {l l' : ALoc} (hl : W.Loc m i l) (hb : l'.block = l.block)
    (ho : l'.off = l.off) :
    (m.atomics.set! i l').findIdx? (fun l => l.block == W.b && l.off == W.o) = some i ∧
      (m.atomics.set! i l')[i]? = some l' := by
  obtain ⟨hi, -, -⟩ := loc_get hl
  obtain ⟨hlb, hlo⟩ := loc_at hl
  obtain ⟨_, _, hj⟩ := Array.findIdx?_eq_some_iff_getElem.mp hl.1
  have hs : (m.atomics.set! i l').size = m.atomics.size := by simp
  refine ⟨Array.findIdx?_eq_some_iff_getElem.mpr ⟨by rw [hs]; exact hi, ?_, fun j hji => ?_⟩, ?_⟩
  · simp only [Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds, ↓reduceIte]
    simp [hb, ho, hlb, hlo]
  · simp only [Array.set!_eq_setIfInBounds]
    rw [Array.getElem_setIfInBounds (by omega), ite_eq_right (Nat.ne_of_gt hji)]
    exact hj j hji
  · rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]; simp [hi]

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

/-- The preparation of an op at the word (its access record and its location, `Ok.prep`) keeps
the ids fresh, the views and the current thread, and no floor gets smaller. -/
theorem Ok.prep_seen {m m₁ : Mem} {li : Nat} {k : AccessKind} (hw : W.Ok m) (hf : W.Fresh m)
    (ht : m.current < m.threads.size) (hcs : m.clocks.size = m.threads.size)
    (hk : k.isAtomic = true)
    (h : ((locIdx W.b W.o nb).run (m.recordAt W.b W.o nb k)).run = some (.ok (li, m₁))) :
    W.Fresh m₁ ∧ (∀ u, W.ownPos m u ≤ W.ownPos m₁ u) ∧ m₁.current = m.current := by
  let mr := m.recordAt W.b W.o nb k
  obtain ⟨hwr, -, -⟩ := hw.record rfl ht hcs hk
  have hfr : W.Fresh mr := hf.of_eq rfl (Nat.le_refl _)
  cases hfi : mr.atomics.findIdx? (fun l => l.block == W.b && l.off == W.o) with
  | some i =>
    have hl := loc_of_find hfi
    obtain ⟨hlen, -, -, hlast, -⟩ := hwr.loc i _ hl
    obtain ⟨rfl, rfl⟩ := locIdx_found hfi hlen hlast (hwr.plain i _ hl) h
    exact ⟨hfr, fun u => Nat.le_of_eq (ownPos_of_eq rfl rfl u).symm, rfl⟩
  | none =>
    obtain ⟨rfl, rfl⟩ := locIdx_new hfi (noOverlap_of_only hfi hwr.only) h
    have hno : ∀ i l, ¬ W.Loc m i l := fun i l hl => by
      have h1 := hl.1
      change mr.atomics.findIdx? _ = _ at h1
      rw [hfi] at h1; cases h1
    refine ⟨fun i l hl j hj => ?_, fun u => by rw [ownPos_none hno]; exact Nat.zero_le _, rfl⟩
    let nl : ALoc := firstLoc mr W.b W.o nb
    have hnl : W.Loc { mr with atomics := mr.atomics.push nl, nextMsg := mr.nextMsg + 1 }
        mr.atomics.size nl := by
      refine ⟨?_, by simp⟩
      show (mr.atomics.push nl).findIdx? _ = _
      rw [Array.findIdx?_push, hfi]; simp [nl, firstLoc]
    obtain ⟨rfl, rfl⟩ := loc_unique hl hnl
    simp only [nl, firstLoc, List.size_toArray, List.length_cons, List.length_nil] at hj
    obtain rfl : j = 0 := by omega
    exact ⟨by simp [nl, firstLoc, firstMsg, mr], by simp [nl, firstLoc, firstMsg, ALoc.pos]⟩

/-- **An atomic load at the word by thread `t`** reads write `j` (the `j` of `Ok.load`: its
value, the floor of the writes that happened before `t`, the acquire) at or after `t`'s floor;
afterwards `t`'s floor is `j`, and no other floor is smaller. -/
theorem Ok.load_seen {m m' : Mem} {t c : Nat} {ord : AtomicOrder} {v : BitVec n} (hw : W.Ok m)
    (hf : W.Fresh m) (hc : m.current = t) (ht : t < m.threads.size)
    (hcs : m.clocks.size = m.threads.size)
    (h : ((atomicLoadAt c ord nb W.ptr : MemM (BitVec n)).run m).run = some (.ok (v, m'))) :
    (∃ j, (j < (W.hist m).size ∧ (W.hist m)[j]!.Val v ∧ Floor (W.hist m) (m.clocks[t]!) j ∧
      (ord.isAcq = true → VClock.le (W.hist m)[j]!.relClock (m'.clocks[t]!) = true)) ∧
      W.ownPos m t ≤ j ∧ W.ownPos m' t = j) ∧
    (∀ u, u ≠ t → W.ownPos m u ≤ W.ownPos m' u) ∧ W.Fresh m' := by
  obtain ⟨b, blk, o, li, m₁, pos, hacc, -, hl, hpos, hv, rfl⟩ := atomicLoadAt_ok h
  obtain ⟨blk₀, -, -, -, ha₀, -⟩ := hw.access
  rw [W.sz_eq, ha₀] at hacc
  rw [W.sz_eq] at hl
  cases hacc
  obtain ⟨l, hl', hw₁, hop₁, hh₁, -, -⟩ := hw.prep hc ht hcs rfl hl
  obtain ⟨hf₁, hle₁, hc₁⟩ := hw.prep_seen hf (by rw [hc]; exact ht) hcs rfl hl
  have hl0 := (loc_get hl').2.2
  have hfl₀ := floor_le hpos
  have hlt := readOpts_lt hpos
  rw [hl0] at hlt hv
  rw [hl0]
  have hct : t < m₁.clocks.size := by rw [hop₁.csize, hcs]; exact ht
  obtain ⟨hfl, hacq, -, -, -⟩ := hw₁.read (ord := ord) hl' hop₁ hct hlt hfl₀
  obtain ⟨hown, hoth, hf'⟩ := loadM_seen hl' hf₁ hlt ord
  have hcur : m₁.current = t := hc₁.trans hc
  have hfloor := ownPos_le_floor hl'
  rw [hcur] at hown hoth hfloor
  exact ⟨⟨pos, ⟨by rw [← hh₁, hist_size hl']; exact hlt, by rw [← hh₁]; exact val_of hl' hlt hv,
    by rw [← hh₁]; exact hfl, by rw [← hh₁]; exact hacq⟩,
    Nat.le_trans (hle₁ t) (Nat.le_trans hfloor hfl₀), hown⟩,
    fun u hu => Nat.le_trans (hle₁ u) (Nat.le_of_eq (hoth u hu).symm), hf'⟩

/-- **An RMW at the word by thread `t`**: afterwards `t`'s floor is its write, the newest
(`Ok.rmw`), and no other floor is smaller. -/
theorem Ok.rmw_seen {m m' : Mem} {t c : Nat} {op : RmwOp} {signed : Bool} {ord : AtomicOrder}
    {v old : BitVec n} (hw : W.Ok m) (hf : W.Fresh m) (hc : m.current = t)
    (ht : t < m.threads.size) (hcs : m.clocks.size = m.threads.size)
    (h : ((atomicRmwAt c op signed ord nb W.ptr v).run m).run = some (.ok (old, m'))) :
    W.ownPos m' t = (W.hist m).size ∧ (∀ u, u ≠ t → W.ownPos m u ≤ W.ownPos m' u) ∧
      W.Fresh m' := by
  obtain ⟨b, blk, o, li, m₁, pos, hacc, -, hl, hpos, -, hm'⟩ := atomicRmwAt_ok h
  obtain ⟨blk₀, -, -, -, -, ha₀⟩ := hw.access
  rw [W.sz_eq, ha₀] at hacc
  rw [W.sz_eq] at hl
  cases hacc
  obtain ⟨l, hl', hw₁, -, hh₁, -, -⟩ := hw.prep hc ht hcs rfl hl
  obtain ⟨hf₁, hle₁, hc₁⟩ := hw.prep_seen hf (by rw [hc]; exact ht) hcs rfl hl
  obtain ⟨-, h0, hch, -, -⟩ := hw₁.loc li l hl'
  have hl0 := (loc_get hl').2.2
  have hpl := rmw_chain_pos (m := m₁) (li := li) (by rw [hl0]; exact h0) (by rw [hl0]; exact hch) hpos
  rw [hl0] at hpl hm'
  rw [hpl] at hm'
  subst hm'
  obtain ⟨hown, hoth, hf'⟩ := rmwM_seen hl' hf₁ (pos := l.msgs.size - 1) (by omega) ord
    (l.msgs[l.msgs.size - 1]!) _
  have hcur : m₁.current = t := hc₁.trans hc
  rw [hcur] at hown hoth
  exact ⟨by rw [hown, ← hh₁, hist_size hl'], fun u hu => Nat.le_trans (hle₁ u) (hoth u hu), hf'⟩

/-- **A `cmpxchg` at the word by thread `t`**: on success its write, the newest, is `t`'s floor;
on failure it reads write `j` (the `j` of `Ok.cas`) at or after `t`'s floor, and `t`'s floor is
`j`. No other floor gets smaller. -/
theorem Ok.cas_seen {m m' : Mem} {t c : Nat} {succ fail : AtomicOrder} {exp new : BitVec n}
    {r : Option (BitVec n)} (hw : W.Ok m) (hf : W.Fresh m) (hc : m.current = t)
    (ht : t < m.threads.size) (hcs : m.clocks.size = m.threads.size)
    (h : ((cmpxchgAt c succ fail nb W.ptr exp new).run m).run = some (.ok (r, m'))) :
    (r = none → W.ownPos m' t = (W.hist m).size) ∧
    (∀ old, r = some old → ∃ j, (j < (W.hist m).size ∧ (W.hist m)[j]!.Val old ∧
      Floor (W.hist m) (m.clocks[t]!) j ∧
      (fail.isAcq = true → VClock.le (W.hist m)[j]!.relClock (m'.clocks[t]!) = true)) ∧
      W.ownPos m t ≤ j ∧ W.ownPos m' t = j) ∧
    (∀ u, u ≠ t → W.ownPos m u ≤ W.ownPos m' u) ∧ W.Fresh m' := by
  obtain ⟨b, blk, o, li, m₁, pos, old, hacc, -, hl, hpos, hold, hcase⟩ := cmpxchgAt_ok h
  obtain ⟨blk₀, -, -, -, -, ha₀⟩ := hw.access
  rw [W.sz_eq, ha₀] at hacc
  rw [W.sz_eq] at hl
  cases hacc
  obtain ⟨l, hl', hw₁, hop₁, hh₁, -, -⟩ := hw.prep hc ht hcs rfl hl
  obtain ⟨hf₁, hle₁, hc₁⟩ := hw.prep_seen hf (by rw [hc]; exact ht) hcs rfl hl
  obtain ⟨-, h0, hch, -, -⟩ := hw₁.loc li l hl'
  have hl0 := (loc_get hl').2.2
  have hcur : m₁.current = t := hc₁.trans hc
  have hct : t < m₁.clocks.size := by rw [hop₁.csize, hcs]; exact ht
  rcases hcase with ⟨rfl, rfl, -, hm'⟩ | ⟨hne, rfl, hm'⟩
  · have hpl := cas_chain_pos (m := m₁) (li := li) (by rw [hl0]; exact hch) hpos hold
    rw [hl0] at hpl hm'
    rw [hpl] at hm'
    subst hm'
    have hlr : W.Loc (m₁.recordAt W.b W.o (intSize n) .atomicWrite) li l := hl'
    obtain ⟨hown, hoth, hf'⟩ := rmwM_seen hlr (hf₁.of_eq rfl (Nat.le_refl _))
      (pos := l.msgs.size - 1) (by omega) succ (l.msgs[l.msgs.size - 1]!) new
    have hpr : ∀ u, W.ownPos (m₁.recordAt W.b W.o (intSize n) .atomicWrite) u = W.ownPos m₁ u :=
      ownPos_of_eq rfl rfl
    have hcr : (m₁.recordAt W.b W.o (intSize n) .atomicWrite).current = t := hcur
    rw [hcr] at hown hoth
    refine ⟨fun _ => by rw [hown, ← hh₁, hist_size hl'], fun _ h => nomatch h,
      fun u hu => Nat.le_trans (hle₁ u) (by rw [← hpr u]; exact hoth u hu), hf'⟩
  · have hlt := (casOpts_pos hpos).1
    have hfl₀ := casOpts_floor hpos
    rw [hl0] at hlt hold hm'
    subst hm'
    obtain ⟨hfl, hacq, -, -, -⟩ := hw₁.read (ord := fail) hl' hop₁ hct hlt hfl₀
    obtain ⟨hown, hoth, hf'⟩ := loadM_seen hl' hf₁ hlt fail
    have hfloor := ownPos_le_floor hl'
    rw [hcur] at hown hoth hfloor
    refine ⟨fun h => nomatch h, fun o ho => ?_,
      fun u hu => Nat.le_trans (hle₁ u) (Nat.le_of_eq (hoth u hu).symm), hf'⟩
    cases ho
    exact ⟨pos, ⟨by rw [← hh₁, hist_size hl']; exact hlt, by rw [← hh₁]; exact val_of hl' hlt hold,
      by rw [← hh₁]; exact hfl, by rw [← hh₁]; exact hacq⟩,
      Nat.le_trans (hle₁ t) (Nat.le_trans hfloor hfl₀), hown⟩

end Word
end Conc
end Zig
