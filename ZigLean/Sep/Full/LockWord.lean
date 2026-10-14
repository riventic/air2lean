import ZigLean.Conc.LockBase
import ZigLean.Conc.WeakCasLemmas
import ZigLean.Sep.Full.Res

/-!
# The word of a lock

The part of a lock (`Io.Mutex` of Zig 0.16.0, `Thread.Mutex` of 0.15.2, translated from their std
code; the futex under it is the model) that reads no heap assertion: its mutex word, the places
of the threads in the lock's code, and the clocks of the accesses to the word. The lock over
full-state resources (`ZigLean/Sep/Full/Lock.lean`) adds the resource that the lock owns and the
threads' parts (`FOwned`); its rules (`ZigLean/Sep/Full/LockRules.lean`) are this file's rules
with the resource moved between a thread's part and the protocol's rest.

- **The word** (`LockWord`): 4 bytes at offset `o` of block `b`; its value while a thread can
  wait for the lock, `c` (`2` for `Io.Mutex`, `3` for `Thread.Mutex` on Linux, `1` for
  `Thread.Mutex` on macOS).
- **The places** (`P : ThreadId → LPh`): where each thread is in the lock's code.
- **The invariant** (`WInv P m`): the word is `0` if no thread holds the lock, else `1` or `c`; at
  most one thread holds it. The word's atomic location is an RMW chain, and no other location
  overlaps the word. An access to the word is atomic, or happened before every thread that has not
  ended. A thread in the futex queue waits at the word or at another futex (`away`); if a thread
  waits at the word, a thread that is not asleep is in the lock's code (`wit`), so there is no
  deadlock at the word. The holder made the newest acquire of the word (`owner`).
- **A step of the lock's code** (`Step t m m'`): the threads, the groups and the other threads'
  clocks stay, only the word's bytes change, each new access is an atomic access to the word, and
  the atomic layout changes at most by a new location at the word.
- **The free resource's clocks** (`Owns P m h`): each access to `h` happened before every thread
  that has not ended, or before the release clock of the word's newest message. An acquire gives
  them to the acquiring thread's clock (`Acq`), a release takes them from the releasing thread's
  clock (`Rel`).
-/

namespace Zig
namespace Full

open Conc Proto

/-- The mutex word of a lock (module doc). -/
structure LockWord where
  /-- The block of the word. -/
  b : BlockId
  /-- The offset of the word in its block. -/
  o : Nat
  /-- The word's value while a thread can wait for the lock: `2` (`Io.Mutex`), `3` (`Thread.Mutex`,
  Linux) or `1` (`Thread.Mutex`, macOS: the word is only `0` or `1`). -/
  c : Nat := 2
  c_ok : c = 1 ∨ c = 2 ∨ c = 3 := by decide

namespace LockWord

variable (L : LockWord)

/-- The address of the word. -/
def ptr : Ptr := ⟨some L.b, (L.o : Int)⟩

/-- The values of the word: `0`, `1`, `c`. -/
def Val (w : Nat) : Prop := w = 0 ∨ w = 1 ∨ w = L.c

theorem Val.lt {w : Nat} (h : L.Val w) : w < 4 := by
  rcases L.c_ok with hc | hc | hc <;> rcases h with rfl | rfl | rfl <;> omega

theorem c_ne0 : L.c ≠ 0 := by rcases L.c_ok with h | h | h <;> omega
theorem c_lt : L.c < 4 := by rcases L.c_ok with h | h | h <;> omega
theorem val0 : L.Val 0 := .inl rfl
theorem val1 : L.Val 1 := .inr (.inl rfl)
theorem valC : L.Val L.c := .inr (.inr rfl)

/-- The word holds `v`. -/
def U32 (m : Mem) (v : BitVec 32) : Prop :=
  (intOfBytes 32 (curBytes m L.b L.o 4)).run = some (.ok v)

/-- `h` has no byte of the word. -/
def Off (h : Heap) : Prop := ∀ x, L.o ≤ x → x < L.o + 4 → h (L.b, x) = none

/-- The byte `l` is a byte of the word. -/
def In (l : Loc) : Prop := l.1 = L.b ∧ L.o ≤ l.2 ∧ l.2 < L.o + 4

instance (l : Loc) : Decidable (L.In l) := by unfold In; infer_instance

/-- The word's location shape. -/
def shape : Shape := (L.b, L.o, 4)

/-- The word's atomic location is location `i`, `l`. -/
def Loc (m : Mem) (i : Nat) (l : ALoc) : Prop :=
  m.atomics.findIdx? (fun l => l.block == L.b && l.off == L.o) = some i ∧ m.atomics[i]? = some l

/-- The word's atomic location: no other location overlaps the word; the location is an RMW
chain of 4-byte messages that hold `0`, `1` or `c`, its newest message has the word's
bytes, and every plain write to the word happened before that message. -/
structure LocOk (m : Mem) : Prop where
  only : ∀ l ∈ m.atomics, l.block = L.b → l.off < L.o + 4 → L.o < l.off + l.len → l.off = L.o
  ok : ∀ i l, L.Loc m i l → l.len = 4 ∧ 0 < l.msgs.size ∧ l.Chain ∧
    (∀ j (h : j < l.msgs.size), ∃ w, L.Val w ∧
      (intOfBytes 32 l.msgs[j].bytes).run = some (.ok (BitVec.ofNat 32 w))) ∧
    ALoc.lastBytes l = curBytes m L.b L.o 4
  plain : ∀ i l, L.Loc m i l → PlainLe m L.b L.o 4 l.lastClock

/-- The clock `c` happened before every thread that has not ended (`gone`) at the places `P`: a
thread that ended does not access the word or the resource again. -/
def LiveLe (P : ThreadId → LPh) (m : Mem) (c : VClock) : Prop :=
  ∀ u < m.threads.size, P u ≠ .gone → VClock.le c (m.clocks[u]!) = true

/-- The clock `c` happened before the release clock of the newest message of the word. -/
def Before (m : Mem) (c : VClock) : Prop :=
  ∃ i l, L.Loc m i l ∧ VClock.le c (l.msgs.back!).relClock = true

/-- The free lock owns `h` at the places `P`: each access to it (or to a block that does not
exist yet) happened before every thread that has not ended, or before the release clock of the
newest message of the word. -/
def Owns (P : ThreadId → LPh) (m : Mem) (h : Heap) : Prop :=
  ∀ e ∈ m.footprint, (e.Touches h ∨ m.blocks.size ≤ e.block) → LiveLe P m e.clock ∨ L.Before m e.clock

/-- The access `e` touches a byte of the word (`FootprintEntry.Touches`). -/
def Hits (e : FootprintEntry) : Prop :=
  e.block = L.b ∧ ∃ x, e.off ≤ x ∧ x < e.off + e.len ∧ L.o ≤ x ∧ x < L.o + 4

/-- No thread holds the lock. -/
def Free (P : ThreadId → LPh) : Prop := ∀ u, P u ≠ .holds

/-- A thread waits at the word in the futex queue `ws`. -/
def Waits (ws : Array (ThreadId × Ptr)) : Prop := ws.any (·.2 == L.ptr) = true

/-- The futex queue `ws`: a thread at the word is at `lock`'s futex wait; a thread at another
futex is `away`. -/
def Queue (P : ThreadId → LPh) (ws : Array (ThreadId × Ptr)) : Prop :=
  ∀ w ∈ ws, (w.2 = L.ptr ∧ P w.1 = .wait) ∨ (w.2 ≠ L.ptr ∧ P w.1 = .away)

/-- The word's block: live, with the word inside, aligned, writable, mapped at the word. -/
def BlkOk (m : Mem) : Prop :=
  ∃ blk, m.blocks[L.b]? = some blk ∧ blk.live = true ∧ L.o + 4 ≤ blk.bytes.size ∧
    (blk.addr + L.o) % 4 = 0 ∧ blk.kind ≠ .constGlobal ∧ blk.kind.mappedLo ≤ L.o

/-- The invariant of the word at the places `P` (module doc). -/
structure WInv (P : ThreadId → LPh) (m : Mem) : Prop where
  csize : m.clocks.size = m.threads.size
  live : ∀ u, P u ≠ .gone → u < m.threads.size ∧ joinedB m u = false
  blk : L.BlkOk m
  word : ∃ w, L.Val w ∧ L.U32 m (BitVec.ofNat 32 w) ∧ (w = 0 ↔ Free P)
  one : ∀ u v, P u = .holds → P v = .holds → u = v
  loc : L.LocOk m
  /-- An access to the word is atomic, or happened before every thread that has not ended. -/
  wfp : ∀ e ∈ m.footprint, L.Hits e →
    (e.kind.isAtomic = true ∧ SomeLe m e.clock) ∨ LiveLe P m e.clock
  /-- The release clock of the newest message happened before a thread, and before the holder. -/
  rel : ∀ i l, L.Loc m i l → SomeLe m (l.msgs.back!).relClock ∧
    ∀ u, P u = .holds → VClock.le (l.msgs.back!).relClock (m.clocks[u]!) = true
  fq : L.Queue P m.waiters
  wit : L.Waits m.waiters → ∃ v, v < m.threads.size ∧ m.waiters.any (·.1 == v) = false ∧
    (P v).busy = true ∧ (P v = .holds → L.U32 m (BitVec.ofNat 32 L.c))
  /-- The holder made the most recent successful acquire of the word (`ALoc.holder`), for the
  owner check of the unlock (`Thread.mutexOwnerCheck`). -/
  owner : ∀ u, P u = .holds → ∃ i l, L.Loc m i l ∧ l.holder = some u

/-- The atomic layout after a step at the word: the same, or one new location at the word, apart
from every other one. -/
def ShapesStep (m m' : Mem) : Prop :=
  shapes m' = shapes m ∨ (shapes m' = shapes m ++ [L.shape] ∧ ∀ s ∈ shapes m, Apart s L.shape)

/-- A step of thread `t` in the lock's code: the threads, the groups and the other threads'
clocks stay, `t`'s clock does not get smaller, and only the word's bytes can change. -/
structure Step (t : ThreadId) (m m' : Mem) : Prop where
  threads : m'.threads = m.threads
  fp : ∀ e ∈ m'.footprint, e ∈ m.footprint ∨
    (e.block = L.b ∧ e.off = L.o ∧ e.len = 4 ∧ e.kind.isAtomic = true ∧ SomeLe m' e.clock)
  groups : m'.groups = m.groups
  csize : m'.clocks.size = m.clocks.size
  others : ∀ u, u ≠ t → m'.clocks[u]! = m.clocks[u]!
  mine : VClock.le (m.clocks[t]!) (m'.clocks[t]!) = true
  bsize : m'.blocks.size = m.blocks.size
  blocks : m'.blocks = m.blocks ∨ ∃ blk bs, m.blocks[L.b]? = some blk ∧ blk.live = true ∧
    bs.size = 4 ∧ L.o + 4 ≤ blk.bytes.size ∧ m'.blocks = (m.write L.b blk L.o bs).blocks
  /-- The threads at another futex stay in the queue. -/
  waiters : ∀ w, w.2 ≠ L.ptr → (w ∈ m'.waiters ↔ w ∈ m.waiters)
  /-- A clock that happened before the newest message of the word still does. -/
  before : ∀ c, L.Before m c → L.Before m' c
  /-- The atomic locations at other addresses stay. -/
  locs : LocsKeep L.b L.o 4 m m'
  /-- A new access is by thread `t`, and happened before its new clock. -/
  fpt : ∀ e ∈ m'.footprint, e ∈ m.footprint ∨ (e.tid = t ∧ VClock.le e.clock (m'.clocks[t]!) = true)
  /-- The atomic layout changes at most by a new location at the word. -/
  shapes : L.ShapesStep m m'
  /-- The messages stay covered (`Mem.MsgCov`). -/
  cov : m.MsgCov → m'.MsgCov

/-- An acquire of thread `t` from `m` to `m'`: each heap without the word's bytes that the free
lock owns in `m` at the places `P`, `t`'s clock owns in `m'`. -/
def Acq (P : ThreadId → LPh) (t : ThreadId) (m m' : Mem) : Prop :=
  ∀ h, L.Owns P m h → L.Off h → m'.OwnsC (m'.clocks[t]!) h

/-- A release of thread `t` from `m` to `m'`: each heap without the word's bytes that `t`'s clock
owns in `m`, the free lock owns in `m'` at the places `P'`. -/
def Rel (t : ThreadId) (P' : ThreadId → LPh) (m m' : Mem) : Prop :=
  ∀ h, m.OwnsC (m.clocks[t]!) h → L.Off h → L.Owns P' m' h

/-- Thread `t` recorded an access to the word at its clock (an RMW's recorded access before its
message, whose clock is the thread's: the message is covered, `Mem.MsgCov`). -/
def Rec (m : Mem) (t : ThreadId) : Prop :=
  ∃ e ∈ m.footprint, e.block = L.b ∧ e.off = L.o ∧ 0 < e.len ∧ e.clock = m.clocks[t]!

variable {L}

/-! ## Basic facts -/

theorem allLe_mono {m m' : Mem} {c : VClock} (ht : m'.threads = m.threads)
    (hcl : ∀ u < m.threads.size, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (h : AllLe m c) : AllLe m' c := fun u hu =>
  VClock.le_trans (h u (ht ▸ hu)) (hcl u (ht ▸ hu))

theorem someLe_mono {m m' : Mem} {c : VClock} (ht : m'.threads = m.threads)
    (hcl : ∀ u < m.threads.size, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (h : SomeLe m c) : SomeLe m' c := by
  obtain ⟨u, hu, hle⟩ := h
  exact ⟨u, ht ▸ hu, VClock.le_trans hle (hcl u hu)⟩

theorem LiveLe.mono {P : ThreadId → LPh} {m m' : Mem} {c : VClock} (ht : m'.threads = m.threads)
    (hcl : ∀ u < m.threads.size, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (h : LiveLe P m c) : LiveLe P m' c := fun u hu hg =>
  VClock.le_trans (h u (ht ▸ hu) hg) (hcl u (ht ▸ hu))

/-- Fewer threads that have not ended. -/
theorem LiveLe.weaken {P P' : ThreadId → LPh} {m : Mem} {c : VClock}
    (hg : ∀ u, P' u ≠ .gone → P u ≠ .gone) (h : LiveLe P m c) : LiveLe P' m c :=
  fun u hu hu' => h u hu (hg u hu')

theorem Owns.weaken {P P' : ThreadId → LPh} {m : Mem} {h : Heap}
    (hg : ∀ u, P' u ≠ .gone → P u ≠ .gone) (ho : L.Owns P m h) : L.Owns P' m h :=
  fun e he ht => (ho e he ht).imp (LiveLe.weaken hg) id

theorem Owns.sub {P : ThreadId → LPh} {m : Mem} {h h₁ : Heap} (ho : L.Owns P m h)
    (hs : ∀ l, h₁ l ≠ none → h l ≠ none) : L.Owns P m h₁ :=
  fun e he ht => ho e he (ht.imp (fun ⟨x, h1, h2, h3⟩ => ⟨x, h1, h2, hs _ h3⟩) id)

/-- `wfp` for other places with fewer threads that have not ended. -/
theorem WInv.wfpW {P P' : ThreadId → LPh} {m : Mem} (hi : L.WInv P m)
    (hg : ∀ u, P' u ≠ .gone → P u ≠ .gone) :
    ∀ e ∈ m.footprint, L.Hits e →
      (e.kind.isAtomic = true ∧ SomeLe m e.clock) ∨ LiveLe P' m e.clock :=
  fun e he hh => (hi.wfp e he hh).imp id (LiveLe.weaken hg)

theorem ShapesStep.refl (m : Mem) : L.ShapesStep m m := .inl rfl

theorem ShapesStep.of_atomics {m m' : Mem} (h : m'.atomics = m.atomics) : L.ShapesStep m m' :=
  .inl (by simp only [shapes, h])

theorem ShapesStep.trans {m₁ m₂ m₃ : Mem} (h₁ : L.ShapesStep m₁ m₂) (h₂ : L.ShapesStep m₂ m₃) :
    L.ShapesStep m₁ m₃ := by
  rcases h₁ with e₁ | ⟨e₁, ha₁⟩ <;> rcases h₂ with e₂ | ⟨e₂, ha₂⟩
  · exact .inl (e₂.trans e₁)
  · exact .inr ⟨by rw [e₂, e₁], by rw [← e₁]; exact ha₂⟩
  · exact .inr ⟨by rw [e₂, e₁], ha₁⟩
  · exfalso
    have := ha₂ L.shape (by rw [e₁]; simp)
    rcases this rfl with h | h <;> simp [LockWord.shape] at h <;> omega

/-- A step that keeps the threads, the groups, the blocks, the clocks, the footprint, the atomic
locations and the threads at another futex. -/
theorem Step.same {t : ThreadId} {m m' : Mem} (ht : m'.threads = m.threads)
    (hg : m'.groups = m.groups) (hb : m'.blocks = m.blocks) (hc : m'.clocks = m.clocks)
    (hf : m'.footprint = m.footprint) (ha : m'.atomics = m.atomics)
    (hw : ∀ w, w.2 ≠ L.ptr → (w ∈ m'.waiters ↔ w ∈ m.waiters)) : L.Step t m m' :=
  ⟨ht, fun e he => .inl (hf ▸ he), hg, by rw [hc], fun _ _ => by rw [hc],
    by rw [hc]; exact VClock.le_refl _, by rw [hb], .inl hb, hw,
    fun _ ⟨i, l, hl, hle⟩ => ⟨i, l, by unfold LockWord.Loc; rw [ha]; exact hl, hle⟩, .of_eq ha,
    fun e he => .inl (hf ▸ he), .of_atomics ha,
    fun h => h.keep (fun _ hl _ => ha ▸ hl) (fun _ _ _ hin => hin.of_blocks hb) fun _ he => hf ▸ he⟩

/-- The same memory, but `current`, `seen`, `nextMsg` and `woken`. -/
theorem WInv.same {P : ThreadId → LPh} {m : Mem} (hi : L.WInv P m) (c : ThreadId)
    (s : Array (ThreadId × Nat × Nat)) (k : Nat) (w : Array ThreadId) :
    L.WInv P { m with current := c, seen := s, nextMsg := k, woken := w } :=
  ⟨hi.csize, hi.live, hi.blk, hi.word, hi.one, ⟨hi.loc.only, hi.loc.ok, hi.loc.plain⟩, hi.wfp,
    hi.rel, hi.fq, hi.wit, hi.owner⟩

/-- The same memory, but the groups' tasks. -/
theorem WInv.groups {P : ThreadId → LPh} {m : Mem} (hi : L.WInv P m) (gs : Array (Ptr × ThreadId)) :
    L.WInv P { m with groups := gs } :=
  ⟨hi.csize, hi.live, hi.blk, hi.word, hi.one, ⟨hi.loc.only, hi.loc.ok, hi.loc.plain⟩, hi.wfp,
    hi.rel, hi.fq, hi.wit, hi.owner⟩

theorem WInv.current {P : ThreadId → LPh} {m : Mem} (hi : L.WInv P m) (t : ThreadId) :
    L.WInv P { m with current := t } :=
  hi.same t m.seen m.nextMsg m.woken

/-- The queue with fewer threads, whose places stay. -/
theorem Queue.mono {P P' : ThreadId → LPh} {ws ws' : Array (ThreadId × Ptr)} (hq : L.Queue P ws)
    (hsub : ∀ w ∈ ws', w ∈ ws) (hph : ∀ w ∈ ws', P' w.1 = P w.1) : L.Queue P' ws' := fun w hw => by
  rw [hph w hw]; exact hq w (hsub w hw)

theorem joinedB_congr {m m' : Mem} (h : m'.threads = m.threads) : joinedB m' = joinedB m := by
  funext u; unfold joinedB; rw [h]

/-- The place of `t` changed to `p`. -/
theorem upd_apply {P : ThreadId → LPh} {t u : ThreadId} {p : LPh} :
    upd P t p u = if u = t then p else P u := by
  unfold upd; split <;> rfl

/-! ## The word in the heap -/

theorem BlkOk.cell {m : Mem} (h : L.BlkOk m) {x : Nat} (h1 : L.o ≤ x) (h2 : x < L.o + 4) :
    m.heap (L.b, x) ≠ none := by
  obtain ⟨blk, hb, hl, hs, -, -, hk⟩ := h
  simp only [Mem.heap, hb]
  rw [dite_eq_left_of_eq_true (eq_true ⟨hl, by omega, by omega⟩)]
  simp

/-- Each byte of the word is in the heap. -/
theorem WInv.wordIn {P : ThreadId → LPh} {m : Mem} (hi : L.WInv P m) {x : Nat} (h1 : L.o ≤ x)
    (h2 : x < L.o + 4) : m.heap (L.b, x) ≠ none :=
  hi.blk.cell h1 h2

theorem BlkOk.access {m : Mem} (h : L.BlkOk m) :
    ∃ blk, m.blocks[L.b]? = some blk ∧ blk.live = true ∧ L.o + 4 ≤ blk.bytes.size ∧
      m.access L.ptr 4 4 = pure (L.b, blk, L.o) ∧ m.accessW L.ptr 4 4 = pure (L.b, blk, L.o) := by
  obtain ⟨blk, hb, hl, hs, ha, hk, hlo⟩ := h
  have hacc : m.access L.ptr 4 4 = pure (L.b, blk, L.o) := by
    have := access_of (p := L.ptr) (n := 4) (a := 4) (m := m) rfl hb hl (by simp [LockWord.ptr])
      (by simp only [LockWord.ptr]; omega) (by simpa [LockWord.ptr] using ha)
      (by simpa [LockWord.ptr] using hlo)
    simpa [LockWord.ptr] using this
  refine ⟨blk, hb, hl, hs, hacc, ?_⟩
  unfold Mem.accessW; rw [hacc]
  simp [hk, pure, bind, ExceptT.bind, ExceptT.mk, ExceptT.pure, ExceptT.bindCont]

/-- A heap disjoint from one with the word's bytes has none of them. -/
theorem off_of_disj {h hF : Heap} (hd : Heap.Disjoint h hF)
    (hw : ∀ x, L.o ≤ x → x < L.o + 4 → hF (L.b, x) ≠ none) : L.Off h :=
  fun x h1 h2 => (hd (L.b, x)).resolve_right (hw x h1 h2)

theorem off_sub {h h₁ : Heap} (ho : L.Off h) (hs : ∀ l, h₁ l ≠ none → h l ≠ none) : L.Off h₁ :=
  fun x h1 h2 => by
    cases e : h₁ (L.b, x) with
    | none => rfl
    | some c => exact absurd (ho x h1 h2) (hs _ (by rw [e]; simp))

theorem off_union {h₁ h₂ : Heap} (h1 : L.Off h₁) (h2 : L.Off h₂) : L.Off (h₁ ∪ h₂) :=
  fun x a b => by simp [h1 x a b, h2 x a b]

theorem off_empty : L.Off Heap.empty := fun _ _ _ => rfl

/-- An access that overlaps the word hits it. -/
theorem hits_of {e : FootprintEntry} (hb : e.block = L.b) (hel : 0 < e.len)
    (h1 : L.o < e.off + e.len) (h2 : e.off < L.o + 4) : L.Hits e := by
  by_cases ho : e.off ≤ L.o
  · exact ⟨hb, L.o, ho, h1, Nat.le_refl _, by omega⟩
  · exact ⟨hb, e.off, Nat.le_refl _, by omega, by omega, h2⟩

/-- A plain write to a byte of the word hits it. -/
theorem hits_of_plain {e : FootprintEntry} (h : plainHit L.b L.o 4 e = true) : L.Hits e :=
  have ⟨_, hel, h1, h2⟩ := plainHit_range h
  L.hits_of (plainHit_block h) hel h1 h2

/-- An access that does not hit the word is not a plain write to it. -/
theorem plainHit_false {e : FootprintEntry} (h : ¬ L.Hits e) : plainHit L.b L.o 4 e = false := by
  cases hp : plainHit L.b L.o 4 e
  · rfl
  · exact absurd (hits_of_plain hp) h

/-- An access that hits the word touches a heap with the word's bytes. -/
theorem touches_word {e : FootprintEntry} {h : Heap} (he : L.Hits e)
    (hw : ∀ x, L.o ≤ x → x < L.o + 4 → h (L.b, x) ≠ none) : e.Touches h := by
  obtain ⟨hb, x, h1, h2, h3, h4⟩ := he
  exact ⟨x, h1, h2, by rw [hb]; exact hw x h3 h4⟩

/-- An access that touches no part of a heap with the word's bytes is not a plain write to it. -/
theorem plainHit_false_of {e : FootprintEntry} {h : Heap}
    (hw : ∀ x, L.o ≤ x → x < L.o + 4 → h (L.b, x) ≠ none) (hnt : ¬ e.Touches h) :
    plainHit L.b L.o 4 e = false :=
  plainHit_false fun hh => hnt (touches_word hh hw)

/-- An access that touches a heap without the word's bytes, and whose bytes are the word's,
does not exist. -/
theorem not_touches_off {e : FootprintEntry} {h : Heap} (hoff : L.Off h) (hb : e.block = L.b)
    (ho : e.off = L.o) (hl : e.len = 4) : ¬ e.Touches h := by
  rintro ⟨x, h1, h2, h3⟩
  rw [hb] at h3; rw [ho] at h1 h2; rw [hl] at h2
  exact h3 (hoff x h1 (by omega))

/-- The cells at the word up to `Cell.norm` (the byte, the address and the kind's constructor):
the same facts of its block, and the same word. -/
theorem word_congrN {m m' : Mem}
    (hw : ∀ x, L.o ≤ x → x < L.o + 4 →
      (m'.heap (L.b, x)).map Cell.norm = (m.heap (L.b, x)).map Cell.norm)
    (hb : L.BlkOk m) : L.BlkOk m' ∧ curBytes m' L.b L.o 4 = curBytes m L.b L.o 4 := by
  obtain ⟨blk, hblk, hl, hs, ha, hk, hlo⟩ := hb
  have hcell : ∀ x (_ : L.o ≤ x) (_ : x < L.o + 4), ∃ blk', m'.blocks[L.b]? = some blk' ∧ blk'.live = true ∧
      ∃ h' : x < blk'.bytes.size, blk'.kind.mappedLo ≤ x ∧
        (Cell.mk blk'.bytes[x] blk'.addr blk'.bytes.size blk'.kind).norm =
          (Cell.mk (blk.bytes[x]'(by omega)) blk.addr blk.bytes.size blk.kind).norm := by
    intro x h1 h2
    have hc : m.heap (L.b, x) =
        some ⟨blk.bytes[x]'(by omega), blk.addr, blk.bytes.size, blk.kind⟩ := by
      simp only [Mem.heap, hblk]; rw [dite_eq_left_of_eq_true (eq_true ⟨hl, by omega, by omega⟩)]
    have hc' := hw x h1 h2
    rw [hc] at hc'
    cases e : m'.heap (L.b, x) with
    | none => rw [e] at hc'; cases hc'
    | some c =>
      rw [e] at hc'
      obtain ⟨blk', hblk', hl', ho', rfl⟩ := Mem.heap_some e
      obtain ⟨blk'', hblk'', hlo'⟩ := Mem.heap_some_lo e
      rw [hblk'] at hblk''; cases hblk''
      exact ⟨blk', hblk', hl', ho', hlo', Option.some.inj hc'⟩
  obtain ⟨blk', hblk', hl', h0, hlo', hn0⟩ := hcell L.o (Nat.le_refl _) (by omega)
  have hA : blk'.addr = blk.addr := by
    have := congrArg Cell.addr hn0; simpa [Cell.norm] using this
  have hK : blk'.kind.norm = blk.kind.norm := by
    have := congrArg Cell.kind hn0; simpa [Cell.norm] using this
  have hsz : L.o + 4 ≤ blk'.bytes.size := by
    obtain ⟨blk₃, h₃, -, h3, -⟩ := hcell (L.o + 3) (by omega) (by omega)
    rw [hblk'] at h₃; cases h₃; omega
  refine ⟨⟨blk', hblk', hl', hsz, by rw [hA]; exact ha, fun e => hk ?_, hlo'⟩, ?_⟩
  · rw [e] at hK; cases hk' : blk.kind <;> rw [hk'] at hK <;> simp_all [BlockKind.norm]
  · unfold curBytes; rw [hblk, hblk']
    simp only [Option.map_some, Option.getD_some]
    apply Array.ext (by simp; omega)
    intro i h1 h2
    simp only [Array.size_extract] at h1 h2
    rw [Array.getElem_extract, Array.getElem_extract]
    obtain ⟨blk₃, h₃, -, h3, -, hn⟩ := hcell (L.o + i) (by omega) (by omega)
    rw [hblk'] at h₃; cases h₃
    have := congrArg Cell.byte hn; simpa [Cell.norm] using this

/-- The same cells at the word. -/
theorem word_congr {m m' : Mem}
    (hw : ∀ x, L.o ≤ x → x < L.o + 4 → m'.heap (L.b, x) = m.heap (L.b, x))
    (hb : L.BlkOk m) : L.BlkOk m' ∧ curBytes m' L.b L.o 4 = curBytes m L.b L.o 4 :=
  word_congrN (fun x h1 h2 => by rw [hw x h1 h2]) hb

/-! ## A step of a thread on its own part -/

/-- A narrowing of an access that hits the word is one that hits it. -/
theorem hits_narrows {e e₀ : FootprintEntry} (hn : e.Narrows e₀) (h : L.Hits e) : L.Hits e₀ := by
  obtain ⟨-, hb, -, ho, hl, -⟩ := hn
  obtain ⟨hb', x, h1, h2, h3, h4⟩ := h
  exact ⟨hb ▸ hb', x, by omega, by omega, h3, h4⟩

theorem someLe_le {m : Mem} {c c' : VClock} (hc : VClock.le c c' = true) (h : SomeLe m c') :
    SomeLe m c :=
  let ⟨u, hu, hle⟩ := h; ⟨u, hu, VClock.le_trans hc hle⟩

theorem LiveLe.le {P : ThreadId → LPh} {m : Mem} {c c' : VClock} (hc : VClock.le c c' = true)
    (h : LiveLe P m c') : LiveLe P m c := fun u hu hg => VClock.le_trans hc (h u hu hg)

/-- **The word's location stays** over a step whose frame `hF` has the word (`FStepIn`): the
word's location (if any) has the word's 4 bytes (`hok`), so it is in the frame. -/
theorem loc_fstep {m m' : Mem} {hF : Heap} (hs : FStepIn hF m m')
    (hwF : ∀ x, L.o ≤ x → x < L.o + 4 → hF (L.b, x) ≠ none) (hok : ∀ i l, L.Loc m i l → l.len = 4)
    (l : ALoc) : (∃ i, L.Loc m' i l) ↔ (∃ i, L.Loc m i l) := by
  obtain ⟨σ, ha⟩ := hs.atomics
  refine (ha.first_iff (p := fun l => l.block == L.b && l.off == L.o)
    (fun l l' hb ho _ => by simp [hb, ho]) (fun i l hfi hl x h1 h2 => ?_)
    (fun l hp hpos => ⟨l.off, Nat.le_refl _, by omega, ?_⟩) l).symm
  · have hlen := hok i l ⟨hfi, hl⟩
    have hp : (l.block == L.b && l.off == L.o) = true := by
      have := Array.of_findIdx?_eq_some hfi; rw [hl] at this; exact this
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    rw [hp.1]; exact hwF x (by omega) (by omega)
  · simp only [Bool.and_eq_true, beq_iff_eq] at hp
    rw [hp.1, hp.2]; exact hwF L.o (Nat.le_refl _) (by omega)

/-- A step of a thread on its own part (`FStepIn hF`, with the word in its frame `hF`), after
which the word's cells are the same up to `Cell.norm`, keeps the invariant. -/
theorem WInv.stepIn {P : ThreadId → LPh} {m m' : Mem} {hF : Heap} (hi : L.WInv P m)
    (hs : FStepIn hF m m') (hwF : ∀ x, L.o ≤ x → x < L.o + 4 → hF (L.b, x) ≠ none)
    (hcells : ∀ x, L.o ≤ x → x < L.o + 4 →
      (m'.heap (L.b, x)).map Cell.norm = (m.heap (L.b, x)).map Cell.norm) :
    L.WInv P m' := by
  have hjb : joinedB m' = joinedB m := joinedB_congr hs.threads
  obtain ⟨hblk', hcur⟩ := word_congrN hcells hi.blk
  have hcl : ∀ u < m.threads.size, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true :=
    fun u _ => hs.clock u
  have hU32 : ∀ v, L.U32 m' v ↔ L.U32 m v := fun v => by unfold LockWord.U32; rw [hcur]
  have hloc := L.loc_fstep hs hwF fun i l hl => (hi.loc.ok i l hl).1
  obtain ⟨σ, ha⟩ := hs.atomics
  refine ⟨by rw [hs.size, hs.threads]; exact hi.csize, fun u hu => ?_, hblk', ?_, hi.one,
    ⟨fun l hl hb h1 h2 => ?_, fun i l hl => ?_, fun i l hl => ?_⟩,
    fun e he hh => ?_, fun i l hl => ?_, by rw [hs.waiters]; exact hi.fq, fun hp => ?_,
    fun u hu => ?_⟩
  · rw [hs.threads, hjb]; exact hi.live u hu
  · obtain ⟨w, hw, hu, hz⟩ := hi.word
    exact ⟨w, hw, (hU32 _).mpr hu, hz⟩
  · rcases ha.mem hl with ⟨l₀, hl₀, eb, eo, el⟩ | ⟨hpos, hoff⟩
    · rw [eo]; exact hi.loc.only l₀ hl₀ (eb ▸ hb) (by omega) (by omega)
    · exfalso
      have hx : ∃ x, l.off ≤ x ∧ x < l.off + l.len ∧ L.o ≤ x ∧ x < L.o + 4 :=
        ⟨if L.o ≤ l.off then l.off else L.o, by split <;> omega, by split <;> omega,
          by split <;> omega, by split <;> omega⟩
      obtain ⟨x, hx1, hx2, hx3, hx4⟩ := hx
      exact hwF x hx3 hx4 (hb ▸ hoff x hx1 hx2)
  · obtain ⟨i₀, hl₀⟩ := (hloc l).mp ⟨i, hl⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := hi.loc.ok i₀ l hl₀
    exact ⟨h1, h2, h3, h4, by rw [h5, hcur]⟩
  · obtain ⟨i₀, hl₀⟩ := (hloc l).mp ⟨i, hl⟩
    exact (hi.loc.plain i₀ l hl₀).fstep hs hwF
  · rcases hs.fp e he with ⟨e₀, he₀, hn⟩ | ⟨-, hnt, -⟩
    · rcases hi.wfp e₀ he₀ (L.hits_narrows hn hh) with ⟨ha, hle⟩ | hle
      · exact .inl ⟨hn.2.2.1 ▸ ha, someLe_mono hs.threads hcl (someLe_le hn.clock hle)⟩
      · exact .inr (LiveLe.mono hs.threads hcl (hle.le hn.clock))
    · exact absurd (touches_word hh hwF) hnt
  · obtain ⟨i₀, hl₀⟩ := (hloc l).mp ⟨i, hl⟩
    obtain ⟨h1, h2⟩ := hi.rel i₀ l hl₀
    refine ⟨someLe_mono hs.threads hcl h1, fun u hu => ?_⟩
    exact VClock.le_trans (h2 u hu) (hcl u (hi.live u (by rw [hu]; decide)).1)
  · obtain ⟨v, hv, hq, h1, h2⟩ := hi.wit (hs.waiters ▸ hp)
    exact ⟨v, hs.threads ▸ hv, hs.waiters ▸ hq, h1, fun hh => (hU32 _).mpr (h2 hh)⟩
  · obtain ⟨i, l, hl, hw⟩ := hi.owner u hu
    obtain ⟨j, hl'⟩ := (hloc l).mpr ⟨i, hl⟩
    exact ⟨j, l, hl', hw⟩

/-- A step of a thread on its own part keeps what the free lock owns in its frame (which has the
word, whose location has its 4 bytes). -/
theorem Owns.stepIn {P : ThreadId → LPh} {m m' : Mem} {hF h : Heap} (ho : L.Owns P m h)
    (hs : FStepIn hF m m') (hsub : ∀ l, h l ≠ none → hF l ≠ none)
    (hwF : ∀ x, L.o ≤ x → x < L.o + 4 → hF (L.b, x) ≠ none) (hok : ∀ i l, L.Loc m i l → l.len = 4) :
    L.Owns P m' h := by
  intro e he htc
  rcases hs.fp e he with ⟨e₀, he₀, hn⟩ | ⟨-, hnt, hb, -⟩
  · have htc₀ : e₀.Touches h ∨ m.blocks.size ≤ e₀.block :=
      htc.imp hn.touches fun h => hn.2.1 ▸ Nat.le_trans hs.blocks h
    rcases ho e₀ he₀ htc₀ with h | ⟨i, l, hl, hle⟩
    · exact .inl (LiveLe.mono hs.threads (fun u _ => hs.clock u) (h.le hn.clock))
    · obtain ⟨j, hl'⟩ := (L.loc_fstep hs hwF hok l).mpr ⟨i, hl⟩
      exact .inr ⟨j, l, hl', VClock.le_trans hn.clock hle⟩
  · rcases htc with ⟨x, h1, h2, h3⟩ | hb'
    · exact absurd ⟨x, h1, h2, hsub _ h3⟩ hnt
    · exact absurd hb' (Nat.not_le.mpr hb)

/-- A change of the place of thread `t` outside the lock's code: `t` is `out` before, and `out`,
`gone` or `away` after. -/
theorem WInv.ghost {P : ThreadId → LPh} {m : Mem} {t : ThreadId} {p : LPh} (hi : L.WInv P m)
    (hph : P t = .out) (hg : p = .out ∨ p = .gone ∨ p = .away)
    (hlive : p ≠ .gone → t < m.threads.size ∧ joinedB m t = false) : L.WInv (upd P t p) m := by
  have hnh : P t ≠ .holds := by rw [hph]; decide
  have hgh : p ≠ .holds := by rcases hg with h | h | h <;> rw [h] <;> decide
  have htb : (P t).busy = false := by rw [hph]; rfl
  have hphu : ∀ u, upd P t p u = if u = t then p else P u := fun u => upd_apply
  have hholds : ∀ u, upd P t p u = .holds ↔ P u = .holds := by
    intro u; rw [hphu]; split
    · rename_i h; subst h; exact ⟨fun h => absurd h hgh, fun h => absurd h hnh⟩
    · exact Iff.rfl
  have hfree : Free (upd P t p) ↔ Free P := by
    unfold LockWord.Free; exact forall_congr' fun u => not_congr (hholds u)
  have hgw : ∀ u, upd P t p u ≠ .gone → P u ≠ .gone := fun u h => by
    rw [hphu] at h; split at h
    · rename_i e; subst e; rw [hph]; decide
    · exact h
  refine ⟨hi.csize, fun u hu => ?_, hi.blk, ?_, fun u v hu hv => hi.one u v ((hholds u).mp hu)
    ((hholds v).mp hv), hi.loc, hi.wfpW hgw, fun i l hl => ?_, fun w hw => ?_, fun hp => ?_,
    fun u hu => hi.owner u ((hholds u).mp hu)⟩
  · rw [hphu] at hu
    split at hu
    · rename_i h; subst h; exact hlive hu
    · exact hi.live u hu
  · obtain ⟨w, hw, hu, hz⟩ := hi.word; exact ⟨w, hw, hu, hz.trans hfree.symm⟩
  · obtain ⟨h1, h2⟩ := hi.rel i l hl
    exact ⟨h1, fun u hu => h2 u ((hholds u).mp hu)⟩
  · have hwt : w.1 ≠ t := fun e => by
      rcases hi.fq w hw with ⟨-, h2⟩ | ⟨-, h2⟩ <;>
        rw [e, hph] at h2 <;> cases h2
    rw [upd_ne _ _ hwt]; exact hi.fq w hw
  · obtain ⟨v, hv, hq, h1, h2⟩ := hi.wit hp
    have hvt : v ≠ t := fun e => by rw [e, htb] at h1; cases h1
    exact ⟨v, hv, hq, by rw [upd_ne _ _ hvt]; exact h1,
      fun hh => h2 (by rw [upd_ne _ _ hvt] at hh; exact hh)⟩

/-! ## Spawn, join, start -/

/-- The clocks after a fork by `t`: the old ones are not smaller, the new thread's is above
`t`'s, and the others stay. -/
theorem fork_clocks {cs : Array VClock} {t : ThreadId} (ht : t < cs.size) :
    (∀ u < cs.size, VClock.le (cs[u]!) (((cs.set! t (VClock.bump (cs[t]!) t)).push
      (VClock.bump (cs[t]!) t))[u]!) = true) ∧
    VClock.le (cs[t]!) (((cs.set! t (VClock.bump (cs[t]!) t)).push
      (VClock.bump (cs[t]!) t))[cs.size]!) = true ∧
    (∀ u < cs.size, u ≠ t → ((cs.set! t (VClock.bump (cs[t]!) t)).push
      (VClock.bump (cs[t]!) t))[u]! = cs[u]!) := by
  refine ⟨fun u hu => ?_, ?_, fun u hu hut => ?_⟩
  · rw [Proto.getElem!_push, if_pos (by simp; omega), Proto.getElem!_set!_ite]
    split
    · rename_i h; rw [h.1]; exact VClock.le_bump _ _
    · exact VClock.le_refl _
  · rw [Proto.getElem!_push, if_neg (by simp), if_pos (by simp)]
    exact VClock.le_bump _ _
  · rw [Proto.getElem!_push, if_pos (by simp; omega), Proto.getElem!_set!_ite, if_neg (by omega)]

/-- A spawn by `t`, which is out of the lock's code: the new thread starts out of it. -/
theorem WInv.fork {P : ThreadId → LPh} {m m' : Mem} {t c : ThreadId} {gt : Bool}
    (hi : L.WInv P m) (hout : P t = .out)
    (hf : ((Thread.forkWith gt).run { m with current := t }).run = some (.ok (c, m'))) :
    c = m.threads.size ∧ L.WInv (upd P c .out) m' ∧
      ∀ h, L.Owns P m h → L.Owns (upd P c .out) m' h := by
  have hcs := hi.csize
  obtain ⟨ht, hjt⟩ := hi.live t (by rw [hout]; decide)
  have hjb := joinedB_fork hf
  rw [Proto.forkWith_run] at hf
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hf
  obtain ⟨rfl, rfl⟩ := hf
  refine ⟨rfl, ?_⟩
  have hct : m.threads.size ≠ t := fun h => by rw [h] at ht; exact Nat.lt_irrefl _ ht
  have hGc : P m.threads.size = .gone := by
    cases hx : P m.threads.size <;> first | rfl |
      exact absurd (hi.live _ (by rw [hx]; decide)).1 (Nat.lt_irrefl _)
  have hjc : joinedB m m.threads.size = false := by
    simp [joinedB, Array.getElem?_eq_none (Nat.le_refl _)]
  have hphu : ∀ u, u ≠ m.threads.size → upd P m.threads.size .out u = P u := fun u hu => upd_ne _ _ hu
  have hnc : ∀ u, P u ≠ .gone → u ≠ m.threads.size := fun u hu e => by
    rw [e, hGc] at hu; exact hu rfl
  obtain ⟨hcl, hcn, hco⟩ := fork_clocks (hcs ▸ ht : t < m.clocks.size)
  have hall : ∀ {c : VClock}, LiveLe P m c → LiveLe (upd P m.threads.size .out) { m with
      current := t,
      clocks := (m.clocks.set! t (VClock.bump (m.clocks[t]!) t)).push (VClock.bump (m.clocks[t]!) t),
      threads := m.threads.push { spawner := t, joined := false, gated := gt } } c := by
    intro c h u hu hg
    simp only [Array.size_push] at hu
    by_cases hu' : u < m.threads.size
    · have hu'' : u ≠ m.threads.size := Nat.ne_of_lt hu'
      exact VClock.le_trans (h u hu' (by rw [← hphu u hu'']; exact hg)) (hcl u (hcs ▸ hu'))
    · have : u = m.threads.size := by omega
      subst this; rw [← hcs]; exact VClock.le_trans (h t ht (by rw [hout]; decide)) hcn
  have hsome : ∀ {c : VClock}, SomeLe m c → SomeLe { m with
      current := t,
      clocks := (m.clocks.set! t (VClock.bump (m.clocks[t]!) t)).push (VClock.bump (m.clocks[t]!) t),
      threads := m.threads.push { spawner := t, joined := false, gated := gt } } c := by
    rintro c ⟨u, hu, hle⟩
    exact ⟨u, by simp only [Array.size_push]; exact Nat.lt_succ_of_lt hu,
      VClock.le_trans hle (hcl u (hcs ▸ hu))⟩
  have hholds : ∀ u, upd P m.threads.size .out u = .holds ↔ P u = .holds := by
    intro u
    by_cases hu : u = m.threads.size
    · subst hu; rw [upd_self, hGc]; decide
    · rw [hphu u hu]
  have hfree : Free (upd P m.threads.size .out) ↔ Free P := by
    unfold LockWord.Free; exact forall_congr' fun u => not_congr (hholds u)
  have hloc : ∀ i l, L.Loc { m with
      current := t,
      clocks := (m.clocks.set! t (VClock.bump (m.clocks[t]!) t)).push (VClock.bump (m.clocks[t]!) t),
      threads := m.threads.push { spawner := t, joined := false, gated := gt } } i l ↔ L.Loc m i l :=
    fun _ _ => Iff.rfl
  refine ⟨⟨by simp [hcs], fun u hu => ?_, hi.blk, ?_, fun u v hu hv => ?_, ⟨hi.loc.only, hi.loc.ok,
    hi.loc.plain⟩, fun e he hh => ?_, fun i l hl => ?_, fun w hw => ?_, fun hp => ?_,
    fun u hu => hi.owner u ((hholds u).mp hu)⟩, fun h ho e he htc => ?_⟩
  · by_cases hc : u = m.threads.size
    · subst hc
      exact ⟨by simp only [Array.size_push]; exact Nat.lt_succ_self _, by rw [hjb]; exact hjc⟩
    · rw [hphu u hc] at hu
      obtain ⟨h1, h2⟩ := hi.live u hu
      exact ⟨by simp only [Array.size_push]; exact Nat.lt_succ_of_lt h1, by rw [hjb]; exact h2⟩
  · obtain ⟨w, hw, hu, hz⟩ := hi.word; exact ⟨w, hw, hu, hz.trans hfree.symm⟩
  · exact hi.one u v ((hholds u).mp hu) ((hholds v).mp hv)
  · rcases hi.wfp e he hh with ⟨ha, hle⟩ | hle
    · exact .inl ⟨ha, hsome hle⟩
    · exact .inr (hall hle)
  · obtain ⟨h1, h2⟩ := hi.rel i l hl
    refine ⟨hsome h1, fun u hu => ?_⟩
    rw [hholds] at hu
    have hu' := (hi.live u (by rw [hu]; decide)).1
    have hut : u ≠ t := fun e => by rw [e, hout] at hu; cases hu
    show VClock.le _ ((_ : Array VClock)[u]!) = true
    rw [hco u (hcs ▸ hu') hut]; exact h2 u hu
  · have hwc : w.1 ≠ m.threads.size :=
      hnc w.1 (by rcases hi.fq w hw with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [h2] <;> decide)
    rcases hi.fq w hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact .inl ⟨h1, by rw [hphu w.1 hwc]; exact h2⟩
    · exact .inr ⟨h1, by rw [hphu w.1 hwc]; exact h2⟩
  · obtain ⟨v, hv, hq, h1, h2⟩ := hi.wit hp
    have hvc : v ≠ m.threads.size := hnc v (fun e => by rw [e] at h1; cases h1)
    exact ⟨v, by simp only [Array.size_push]; exact Nat.lt_succ_of_lt hv, hq,
      by rw [hphu v hvc]; exact h1, fun hh => h2 (by rw [← hphu v hvc]; exact hh)⟩
  · rcases ho e he htc with h | ⟨i, l, hl, hle⟩
    · exact .inl (hall h)
    · exact .inr ⟨i, l, hl, hle⟩

/-- A join of `u` (which has ended) by `t` (out of the lock's code). -/
theorem WInv.join {P : ThreadId → LPh} {m m' : Mem} {t u : ThreadId} (hi : L.WInv P m)
    (hut : u ≠ t) (hu0 : u ≠ 0) (hout : P t = .out) (huo : P u = .gone)
    (hj : ((Thread.join u).run { m with current := t }).run = some (.ok ((), m'))) :
    L.WInv P m' ∧ ∀ h, L.Owns P m h → L.Owns P m' h := by
  have hcs := hi.csize
  obtain ⟨ht, hjt⟩ := hi.live t (by rw [hout]; decide)
  obtain ⟨rec, hr, -, rfl⟩ := Proto.join_eq hj
  have hul : u < m.threads.size := (Array.getElem?_eq_some_iff.mp hr).1
  have hjb : ∀ w, joinedB { m with
      current := t,
      clocks := m.clocks.set! t (VClock.merge (VClock.bump (m.clocks[t]!) t) (m.clocks[u]!)),
      threads := m.threads.set! u { rec with joined := true } } w =
      if w = u then true else joinedB m w := by
    intro w
    unfold joinedB
    simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    by_cases hw : w = u
    · subst hw; simp [hu0, hul]
    · simp [hw, Ne.symm hw]
  have hcl : ∀ w : Nat, VClock.le (m.clocks[w]!) ((m.clocks.set! t (VClock.merge
      (VClock.bump (m.clocks[t]!) t) (m.clocks[u]!)))[w]!) = true := by
    intro w
    rw [getElem!_set!_ite]
    split
    · rename_i h; rw [h.1]
      exact VClock.le_trans (VClock.le_bump _ _) (VClock.le_merge_left _ _)
    · exact VClock.le_refl _
  have hco : ∀ w : Nat, w ≠ t → (m.clocks.set! t (VClock.merge (VClock.bump (m.clocks[t]!) t)
      (m.clocks[u]!)))[w]! = m.clocks[w]! := by
    intro w hw; rw [getElem!_set!_ite, if_neg (fun h => hw h.1)]
  have hsz : (m.threads.set! u { rec with joined := true }).size = m.threads.size := by simp
  have hall : ∀ {c : VClock}, LiveLe P m c → LiveLe P { m with
      current := t,
      clocks := m.clocks.set! t (VClock.merge (VClock.bump (m.clocks[t]!) t) (m.clocks[u]!)),
      threads := m.threads.set! u { rec with joined := true } } c := fun h w hw hg =>
    VClock.le_trans (h w (hsz ▸ hw) hg) (hcl w)
  have hsome : ∀ {c : VClock}, SomeLe m c → SomeLe { m with
      current := t,
      clocks := m.clocks.set! t (VClock.merge (VClock.bump (m.clocks[t]!) t) (m.clocks[u]!)),
      threads := m.threads.set! u { rec with joined := true } } c := by
    rintro c ⟨w, hw, hle⟩; exact ⟨w, by rw [hsz]; exact hw, VClock.le_trans hle (hcl w)⟩
  have hnu : ∀ w, P w ≠ .gone → w ≠ u := fun w hw e => hw (by rw [e, huo])
  refine ⟨⟨by simp [hcs], fun w hw => ?_, hi.blk, hi.word, hi.one,
    ⟨hi.loc.only, hi.loc.ok, hi.loc.plain⟩, fun e he hh => ?_,
    fun i l hl => ?_, hi.fq, fun hp => ?_, hi.owner⟩, fun h ho e he htc => ?_⟩
  · obtain ⟨h1, h2⟩ := hi.live w hw
    exact ⟨by rw [hsz]; exact h1, by rw [hjb, if_neg (hnu w hw)]; exact h2⟩
  · rcases hi.wfp e he hh with ⟨ha, hle⟩ | hle
    · exact .inl ⟨ha, hsome hle⟩
    · exact .inr (hall hle)
  · obtain ⟨h1, h2⟩ := hi.rel i l hl
    refine ⟨hsome h1, fun w hw => ?_⟩
    show VClock.le _ ((_ : Array VClock)[w]!) = true
    rw [hco w (fun e => by rw [e, hout] at hw; cases hw)]; exact h2 w hw
  · obtain ⟨v, hv, hq, h1, h2⟩ := hi.wit hp
    exact ⟨v, by rw [hsz]; exact hv, hq, h1, h2⟩
  · rcases ho e he htc with h | ⟨i, l, hl, hle⟩
    · exact .inl (hall h)
    · exact .inr ⟨i, l, hl, hle⟩

/-- The start of the lock: each thread is out of the lock's code (and alive) or gone, the word
holds `0`, no atomic location is in its block, no thread waits at a futex, and each access to the
word happened before every thread that has not ended. -/
theorem WInv.make {P : ThreadId → LPh} {m : Mem}
    (hc : m.clocks.size = m.threads.size)
    (hph : ∀ u, (P u = .out ∧ u < m.threads.size ∧ joinedB m u = false) ∨ P u = .gone)
    (hblk : L.BlkOk m) (h0 : L.U32 m 0) (hat : ∀ l ∈ m.atomics, l.block ≠ L.b) (hq : m.waiters = #[])
    (hwle : ∀ e ∈ m.footprint, L.Hits e → LiveLe P m e.clock) : L.WInv P m := by
  have hfree : Free P := fun u => by rcases hph u with ⟨h, -⟩ | h <;> rw [h] <;> decide
  have hnoloc : ∀ i l, ¬ L.Loc m i l := by
    rintro i l ⟨hf, -⟩
    obtain ⟨hi', hp, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact hat _ (Array.getElem_mem hi') hp.1
  exact ⟨hc, fun u hu => ((hph u).resolve_right hu).2, hblk,
    ⟨0, .inl rfl, h0, ⟨fun _ => hfree, fun _ => rfl⟩⟩, fun u _ hu => absurd hu (hfree u),
    ⟨fun l hl hb => absurd hb (hat l hl), fun i l hl => absurd hl (hnoloc i l),
      fun i l hl => absurd hl (hnoloc i l)⟩, fun e he hh => .inr (hwle e he hh),
    fun i l hl => absurd hl (hnoloc i l),
    fun w hw => by rw [hq] at hw; simp at hw, fun hp => by rw [hq] at hp; simp [LockWord.Waits] at hp,
    fun u hu => absurd hu (hfree u)⟩

/-! ## A step in the lock's code -/

/-- A clock below one that happened before the newest message of the word. -/
theorem before_le {m : Mem} {c c' : VClock} (h : L.Before m c') (hle : VClock.le c c' = true) :
    L.Before m c := by
  obtain ⟨i, l, hl, h'⟩ := h; exact ⟨i, l, hl, VClock.le_trans hle h'⟩

theorem Step.clocks {t : ThreadId} {m m' : Mem} (hs : L.Step t m m') (u : Nat) :
    VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true := by
  by_cases hu : u = t
  · subst hu; exact hs.mine
  · rw [hs.others u hu]; exact VClock.le_refl _

theorem Step.allLe {t : ThreadId} {m m' : Mem} {c : VClock} (hs : L.Step t m m')
    (h : AllLe m c) : AllLe m' c :=
  allLe_mono hs.threads (fun u _ => hs.clocks u) h

theorem Step.liveLe {P P' : ThreadId → LPh} {t : ThreadId} {m m' : Mem} {c : VClock}
    (hs : L.Step t m m') (hg : ∀ u, P' u ≠ .gone → P u ≠ .gone)
    (h : LiveLe P m c) : LiveLe P' m' c :=
  (LiveLe.mono hs.threads (fun u _ => hs.clocks u) h).weaken hg

theorem Step.someLe {t : ThreadId} {m m' : Mem} {c : VClock} (hs : L.Step t m m')
    (h : SomeLe m c) : SomeLe m' c :=
  someLe_mono hs.threads (fun u _ => hs.clocks u) h

theorem Step.trans {t : ThreadId} {m₁ m₂ m₃ : Mem} (h₁ : L.Step t m₁ m₂) (h₂ : L.Step t m₂ m₃)
    (hb : m₂.blocks = m₁.blocks ∨ m₃.blocks = m₂.blocks) : L.Step t m₁ m₃ := by
  refine ⟨h₂.threads.trans h₁.threads, fun e he => ?_, h₂.groups.trans h₁.groups,
    h₂.csize.trans h₁.csize,
    fun u hu => (h₂.others u hu).trans (h₁.others u hu), VClock.le_trans h₁.mine h₂.mine,
    h₂.bsize.trans h₁.bsize, ?_, fun w hw => (h₂.waiters w hw).trans (h₁.waiters w hw),
    fun c h => h₂.before c (h₁.before c h), h₁.locs.trans h₂.locs, fun e he => ?_,
    h₁.shapes.trans h₂.shapes, fun h => h₂.cov (h₁.cov h)⟩
  rotate_right
  · rcases h₂.fpt e he with h | h
    · rcases h₁.fpt e h with h' | ⟨ht, hle⟩
      · exact .inl h'
      · exact .inr ⟨ht, VClock.le_trans hle h₂.mine⟩
    · exact .inr h
  · rcases h₂.fp e he with h | h
    · rcases h₁.fp e h with h' | ⟨a, b, c, d, f⟩
      · exact .inl h'
      · exact .inr ⟨a, b, c, d, h₂.someLe f⟩
    · exact .inr h
  rcases hb with hb | hb
  · rcases h₂.blocks with e | ⟨blk, bs, h1, h2, h3, h4, h5⟩
    · exact .inl (e.trans hb)
    · refine .inr ⟨blk, bs, by rw [← hb]; exact h1, h2, h3, h4, ?_⟩
      rw [h5]; simp only [Mem.write, hb]
  · rcases h₁.blocks with e | ⟨blk, bs, h1, h2, h3, h4, h5⟩
    · exact .inl (hb.trans e)
    · exact .inr ⟨blk, bs, h1, h2, h3, h4, hb.trans h5⟩

/-- The heap after a step in the lock's code: the same, but at the word. -/
theorem Step.heap {t : ThreadId} {m m' : Mem} (hs : L.Step t m m') {l : Zig.Loc}
    (hl : ¬ L.In l) : m'.heap l = m.heap l := by
  rcases hs.blocks with e | ⟨blk, bs, h1, h2, h3, h4, h5⟩
  · obtain ⟨b, x⟩ := l; simp only [Mem.heap, e]
  · have : m'.heap l = (m.write L.b blk L.o bs).heap l := by
      obtain ⟨b, x⟩ := l; simp only [Mem.heap, h5]
    rw [this, Mem.heap_write_out h1 (by omega) l (by rw [h3]; exact hl)]

/-- The heap of the word stays outside the word after a lock step. -/
theorem Step.sub {t : ThreadId} {m m' : Mem} {h : Heap} (hs : L.Step t m m') (hoff : L.Off h)
    (hsub : h.Sub m.heap) : h.Sub m'.heap := fun l c hc => by
  have hw : ¬ L.In l := by
    rintro ⟨h1, h2, h3⟩
    obtain ⟨b, x⟩ := l; simp only at h1 h2 h3; subst h1
    rw [hoff x h2 h3] at hc; cases hc
  rw [hs.heap hw]; exact hsub l c hc

/-- A new access of a lock step touches no heap without the word's bytes. -/
theorem Step.fpOff {t : ThreadId} {m m' : Mem} {h : Heap} (hs : L.Step t m m') (hoff : L.Off h)
    {e : FootprintEntry} (he : e ∈ m'.footprint) (hn : e ∉ m.footprint) : ¬ e.Touches h := by
  rcases hs.fp e he with h' | ⟨hb, ho, hl, -⟩
  · exact absurd h' hn
  · exact not_touches_off hoff hb ho hl

/-- A lock step keeps what a clock of a thread owns without the word's bytes: `t`'s clock only
grows, and no new access touches it. -/
theorem OwnsC.step {t : ThreadId} {m m' : Mem} {h : Heap} (hs : L.Step t m m') (hoff : L.Off h)
    (hbl : L.b < m.blocks.size) (ho : m.OwnsC (m.clocks[t]!) h) : m'.OwnsC (m'.clocks[t]!) h := by
  intro e he htc
  by_cases hm : e ∈ m.footprint
  · exact VClock.le_trans (ho e hm (htc.imp id fun h => by rw [← hs.bsize]; exact h)) hs.mine
  · rcases htc with htc | hbe
    · exact absurd htc (hs.fpOff hoff he hm)
    · rcases hs.fp e he with h | ⟨heb, -⟩
      · exact absurd h hm
      · rw [heb, hs.bsize] at hbe; exact absurd hbl (Nat.not_lt.mpr hbe)

/-- A lock step keeps what the free lock owns without the word's bytes, for places with fewer
threads that have not ended. -/
theorem Owns.step {P P' : ThreadId → LPh} {t : ThreadId} {m m' : Mem} {h : Heap}
    (hs : L.Step t m m') (hoff : L.Off h) (hbl : L.b < m.blocks.size)
    (hg : ∀ u, P' u ≠ .gone → P u ≠ .gone) (ho : L.Owns P m h) : L.Owns P' m' h := by
  intro e he htc
  by_cases hm : e ∈ m.footprint
  · rcases ho e hm (htc.imp id fun h => by rw [← hs.bsize]; exact h) with h | h
    · exact .inl (hs.liveLe hg h)
    · exact .inr (hs.before _ h)
  · rcases htc with htc | hbe
    · exact absurd htc (hs.fpOff hoff he hm)
    · rcases hs.fp e he with h | ⟨heb, -⟩
      · exact absurd h hm
      · rw [heb, hs.bsize] at hbe; exact absurd hbl (Nat.not_lt.mpr hbe)

/-- An acquire after a lock step without a place change. -/
theorem Acq.pre {P : ThreadId → LPh} {t : ThreadId} {m m₁ M : Mem} (hs : L.Step t m m₁)
    (hbl : L.b < m.blocks.size) (h : L.Acq P t m₁ M) : L.Acq P t m M :=
  fun h' ho hoff => h h' (ho.step hs hoff hbl fun _ h => h) hoff

/-- An acquire followed by a lock step. -/
theorem Acq.post {P : ThreadId → LPh} {t : ThreadId} {m M M' : Mem} (h : L.Acq P t m M)
    (hs : L.Step t M M') (hbl : L.b < M.blocks.size) : L.Acq P t m M' :=
  fun h' ho hoff => OwnsC.step hs hoff hbl (h h' ho hoff)

/-- A release after a lock step. -/
theorem Rel.pre {P' : ThreadId → LPh} {t : ThreadId} {m m₁ M : Mem} (hs : L.Step t m m₁)
    (hbl : L.b < m.blocks.size) (h : L.Rel t P' m₁ M) : L.Rel t P' m M :=
  fun h' ho hoff => h h' (OwnsC.step hs hoff hbl ho) hoff

/-- A release followed by a lock step, for places with fewer threads that have not ended. -/
theorem Rel.post {P' P'' : ThreadId → LPh} {t : ThreadId} {m M M' : Mem} (h : L.Rel t P' m M)
    (hs : L.Step t M M') (hbl : L.b < M.blocks.size) (hg : ∀ u, P'' u ≠ .gone → P' u ≠ .gone) :
    L.Rel t P'' m M' :=
  fun h' ho hoff => (h h' ho hoff).step hs hoff hbl hg

/-! ## Changes that keep the blocks and the locations -/

/-- A memory with the same blocks, threads, atomic locations and futex queue, clocks that are not
smaller, and new accesses that, if they hit the word, are atomic or happened before each thread
that has not ended. -/
theorem WInv.mono {P : ThreadId → LPh} {m m' : Mem} (hi : L.WInv P m) (ht : m'.threads = m.threads)
    (hb : m'.blocks = m.blocks) (ha : m'.atomics = m.atomics) (hw : m'.waiters = m.waiters)
    (hcs : m'.clocks.size = m.clocks.size)
    (hcl : ∀ u : Nat, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (hfp : ∀ e ∈ m'.footprint, e ∈ m.footprint ∨
      (L.Hits e → (e.kind.isAtomic = true ∧ SomeLe m' e.clock) ∨ LiveLe P m' e.clock))
    (hpl : ∀ e ∈ m'.footprint, e ∈ m.footprint ∨ plainHit L.b L.o 4 e = false) : L.WInv P m' := by
  have hjb : joinedB m' = joinedB m := joinedB_congr ht
  have hcur : curBytes m' L.b L.o 4 = curBytes m L.b L.o 4 := curBytes_congr hb _ _ _
  have hU32 : ∀ v, L.U32 m' v ↔ L.U32 m v := fun v => by unfold LockWord.U32; rw [hcur]
  have hloc : ∀ i l, L.Loc m' i l ↔ L.Loc m i l := fun i l => by unfold LockWord.Loc; rw [ha]
  have hsome : ∀ {c}, SomeLe m c → SomeLe m' c := fun h => someLe_mono ht (fun u _ => hcl u) h
  refine ⟨by rw [hcs, ht]; exact hi.csize, fun u hu => ?_, ?_, ?_, hi.one,
    ⟨fun l hl => hi.loc.only l (ha ▸ hl), fun i l hl => ?_,
      fun i l hl => (hi.loc.plain i l ((hloc i l).mp hl)).of_fp hpl⟩,
    fun e he hh => ?_, fun i l hl => ?_, by rw [hw]; exact hi.fq,
    fun hp => ?_, fun u hu => let ⟨i, l, hl, hw⟩ := hi.owner u hu; ⟨i, l, (hloc i l).mpr hl, hw⟩⟩
  · rw [ht, hjb]; exact hi.live u hu
  · obtain ⟨blk, h1, h2⟩ := hi.blk; exact ⟨blk, by rw [hb]; exact h1, h2⟩
  · obtain ⟨w, hw', hu, hz⟩ := hi.word; exact ⟨w, hw', (hU32 _).mpr hu, hz⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hi.loc.ok i l ((hloc i l).mp hl)
    exact ⟨h1, h2, h3, h4, by rw [h5, hcur]⟩
  · rcases hfp e he with h' | hat
    · rcases hi.wfp e h' hh with ⟨hat', hle'⟩ | hle'
      · exact .inl ⟨hat', hsome hle'⟩
      · exact .inr (LiveLe.mono ht (fun u _ => hcl u) hle')
    · exact hat hh
  · obtain ⟨h1, h2⟩ := hi.rel i l ((hloc i l).mp hl)
    exact ⟨hsome h1, fun u hu => VClock.le_trans (h2 u hu) (hcl u)⟩
  · obtain ⟨v, hv, hq, h1, h2⟩ := hi.wit (hw ▸ hp)
    exact ⟨v, ht ▸ hv, hw ▸ hq, h1, fun hh => (hU32 _).mpr (h2 hh)⟩

/-- `Owns` over a memory with the same threads, blocks and atomic locations, clocks that are not
smaller, and new accesses that touch no byte of `h` or happened before each thread that has not
ended. -/
theorem Owns.mono {P : ThreadId → LPh} {m m' : Mem} {h : Heap} (ho : L.Owns P m h)
    (ht : m'.threads = m.threads) (hb : m'.blocks = m.blocks) (ha : m'.atomics = m.atomics)
    (hcl : ∀ u : Nat, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (hfp : ∀ e ∈ m'.footprint, e ∈ m.footprint ∨
      (¬ e.Touches h ∧ e.block < m.blocks.size) ∨ LiveLe P m' e.clock) : L.Owns P m' h := by
  intro e he htc
  rcases hfp e he with h' | ⟨hnt, hbl⟩ | hle
  · rcases ho e h' (by rw [← hb]; exact htc) with h | ⟨i, l, hl, hle⟩
    · exact .inl (LiveLe.mono ht (fun u _ => hcl u) h)
    · exact .inr ⟨i, l, by unfold LockWord.Loc; rw [ha]; exact hl, hle⟩
  · rcases htc with htc | hb'
    · exact absurd htc hnt
    · rw [hb] at hb'; exact absurd hbl (Nat.not_lt.mpr hb')
  · exact .inl hle

theorem recordAt_le (m : Mem) (b o n : Nat) (k : AccessKind) (u : Nat) :
    VClock.le (m.clocks[u]!) ((m.recordAt b o n k).clocks[u]!) = true := by
  simp only [Mem.recordAt]; rw [getElem!_set!_ite]
  split
  · rename_i h; rw [h.1]; exact VClock.le_bump _ _
  · exact VClock.le_refl _

/-- The record of an atomic access to the word by the current thread. -/
theorem WInv.record {P : ThreadId → LPh} {m : Mem} (hi : L.WInv P m) {k : AccessKind}
    (hk : k.isAtomic = true) (ht : m.current < m.threads.size) :
    L.WInv P (m.recordAt L.b L.o 4 k) := by
  have hcs : m.current < m.clocks.size := by rw [hi.csize]; exact ht
  refine hi.mono rfl rfl rfl rfl (by simp [Mem.recordAt]) (recordAt_le m _ _ _ _) (fun e he => ?_)
    fun e he => by
      simp only [Mem.recordAt, Array.mem_push] at he
      rcases he with he | rfl
      · exact .inl he
      · exact .inr (plainHit_atomic hk)
  simp only [Mem.recordAt, Array.mem_push] at he
  rcases he with he | rfl
  · exact .inl he
  · refine .inr fun _ => .inl ⟨hk, m.current, ht, ?_⟩
    simp only [Mem.recordAt]; rw [getElem!_set!_ite]; simp [hcs, VClock.le_refl]

/-- A recorded access to the word by the current thread `t` is at `t`'s new clock. -/
theorem rec_recordAt {m : Mem} {t : ThreadId} {k : AccessKind} (hc : m.current = t)
    (hcs : t < m.clocks.size) : L.Rec (m.recordAt L.b L.o 4 k) t := by
  subst hc
  rw [Rec, recordAt_clock hcs]
  exact ⟨_, Array.mem_push_self, rfl, rfl, Nat.succ_pos 3, rfl⟩

/-- Recording an atomic access to the word is a lock step, without changing its messages. -/
theorem WInv.recordStep {P : ThreadId → LPh} {m : Mem} {t : ThreadId} {k : AccessKind}
    (hi : L.WInv P m) (hc : m.current = t) (ht : t < m.threads.size)
    (hk : k.isAtomic = true) : L.Step t m (m.recordAt L.b L.o 4 k) := by
  have hcs : t < m.clocks.size := by rw [hi.csize]; exact ht
  refine ⟨rfl, fun e he => ?_, rfl, by simp [Mem.recordAt], ?_, ?_, rfl, .inl rfl,
    fun _ _ => Iff.rfl, fun _ h => h, .of_eq rfl, fun e he => ?_, .of_atomics rfl,
    Mem.MsgCov.recordAt⟩
  · simp only [Mem.recordAt, Array.mem_push] at he
    rcases he with he | rfl
    · exact .inl he
    · refine .inr ⟨rfl, rfl, rfl, hk, t, ht, ?_⟩
      simp only [Mem.recordAt, hc]
      rw [getElem!_set!_ite]; simp [hcs, VClock.le_refl]
  · intro u hu
    simp only [Mem.recordAt, hc]
    rw [getElem!_set!_ite, if_neg (fun h => hu h.1)]
  · simp only [Mem.recordAt, hc]
    rw [getElem!_set!_ite]; simp [hcs, VClock.le_bump]
  · simp only [Mem.recordAt, Array.mem_push] at he
    rcases he with he | rfl
    · exact .inl he
    · refine .inr ⟨hc, ?_⟩
      simp only [Mem.recordAt, hc]
      rw [getElem!_set!_ite]; simp [hcs, VClock.le_refl]

/-- A read (plain or atomic, `k`) by the current thread of `n` bytes at `o` of block `b`, which
are not the word's. -/
theorem WInv.readK {P : ThreadId → LPh} {m : Mem} {b o n : Nat} {k : AccessKind} (hk : k ≠ .write)
    (hi : L.WInv P m) (hnw : b ≠ L.b ∨ o + n ≤ L.o ∨ L.o + 4 ≤ o) :
    L.WInv P (m.recordAt b o n k) := by
  refine hi.mono rfl rfl rfl rfl (by simp [Mem.recordAt]) (recordAt_le m _ _ _ _) (fun e he => ?_)
    fun e he => by
      simp only [Mem.recordAt, Array.mem_push] at he
      rcases he with he | rfl
      · exact .inl he
      · exact .inr (by simp [plainHit, hk])
  simp only [Mem.recordAt, Array.mem_push] at he
  rcases he with he | rfl
  · exact .inl he
  · refine .inr fun ⟨hb', x, h1, h2, h3, h4⟩ => ?_
    exfalso
    dsimp only at hb' h1 h2
    rcases hnw with h | h | h
    · exact h hb'
    · omega
    · omega

/-- A read by the current thread of bytes that are not the word's keeps what the free lock owns
of a heap that does not have them. -/
theorem Owns.readK {P : ThreadId → LPh} {m : Mem} {b o n : Nat} {k : AccessKind} {h : Heap}
    (ho : L.Owns P m h) (hb : b < m.blocks.size)
    (hnR : ∀ x, o ≤ x → x < o + n → h (b, x) = none) :
    L.Owns P (m.recordAt b o n k) h := by
  refine ho.mono rfl rfl rfl (recordAt_le m _ _ _ _) fun e he => ?_
  simp only [Mem.recordAt, Array.mem_push] at he
  rcases he with he | rfl
  · exact .inl he
  · refine .inr (.inl ⟨fun ⟨x, h1, h2, h3⟩ => ?_, hb⟩)
    dsimp only at h1 h2 h3; exact h3 (hnR x h1 (by omega))

/-- A plain read by the current thread, the only thread that has not ended: it can read the
word. The caller shows that the read does not race. -/
theorem WInv.readAll {P : ThreadId → LPh} {m : Mem} {b o n : Nat} (hi : L.WInv P m)
    (ht : m.current < m.threads.size) (hsole : ∀ u < m.threads.size, u ≠ m.current → P u = .gone) :
    L.WInv P (m.recordAt b o n .read) := by
  have hcs : m.current < m.clocks.size := by rw [hi.csize]; exact ht
  have hle : LiveLe P (m.recordAt b o n .read) (VClock.bump (m.clocks[m.current]!) m.current) := by
    intro u hu hg
    simp only [Mem.recordAt] at hu ⊢
    by_cases hu' : u = m.current
    · subst hu'; rw [getElem!_set!_ite]; simp [hcs, VClock.le_refl]
    · exact absurd (hsole u hu hu') hg
  refine hi.mono rfl rfl rfl rfl (by simp [Mem.recordAt]) (recordAt_le m _ _ _ _) (fun e he => ?_)
    fun e he => by
      simp only [Mem.recordAt, Array.mem_push] at he
      rcases he with he | rfl
      · exact .inl he
      · exact .inr (by simp [plainHit])
  simp only [Mem.recordAt, Array.mem_push] at he
  rcases he with he | rfl
  · exact .inl he
  · exact .inr fun _ => .inr hle

/-- `Owns` after a plain read by the only thread that has not ended. -/
theorem Owns.readAll {P : ThreadId → LPh} {m : Mem} {b o n : Nat} {h : Heap} (ho : L.Owns P m h)
    (hcs : m.current < m.clocks.size) (hsole : ∀ u < m.threads.size, u ≠ m.current → P u = .gone) :
    L.Owns P (m.recordAt b o n .read) h := by
  have hle : LiveLe P (m.recordAt b o n .read) (VClock.bump (m.clocks[m.current]!) m.current) := by
    intro u hu hg
    simp only [Mem.recordAt] at hu ⊢
    by_cases hu' : u = m.current
    · subst hu'; rw [getElem!_set!_ite]; simp [hcs, VClock.le_refl]
    · exact absurd (hsole u hu hu') hg
  refine ho.mono rfl rfl rfl (recordAt_le m _ _ _ _) fun e he => ?_
  simp only [Mem.recordAt, Array.mem_push] at he
  rcases he with he | rfl
  · exact .inl he
  · exact .inr (.inr hle)

/-! ## The word's atomic location -/

theorem loc_get {m : Mem} {i : Nat} {l : ALoc} (hl : L.Loc m i l) :
    ∃ h : i < m.atomics.size, m.atomics[i] = l ∧ m.atomics[i]! = l := by
  obtain ⟨h, e⟩ := Array.getElem?_eq_some_iff.mp hl.2
  exact ⟨h, e, by rw [getElem!_pos m.atomics i h, e]⟩

theorem loc_unique {m : Mem} {i j : Nat} {l l' : ALoc} (hl : L.Loc m i l) (hl' : L.Loc m j l') :
    i = j ∧ l = l' := by
  have e : i = j := by have := hl.1; rw [hl'.1] at this; cases this; rfl
  subst e
  have := hl.2; rw [hl'.2] at this; cases this; exact ⟨rfl, rfl⟩

theorem loc_at {m : Mem} {i : Nat} {l : ALoc} (hl : L.Loc m i l) : l.block = L.b ∧ l.off = L.o := by
  obtain ⟨hi', hp, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp hl.1
  obtain ⟨h, e, -⟩ := loc_get hl
  rw [e] at hp
  simpa using hp

/-- The location after a change of location `i` that keeps its block and offset. -/
theorem loc_set {m m' : Mem} {i : Nat} {l l' : ALoc} (hl : L.Loc m i l)
    (ha : m'.atomics = m.atomics.set! i l') (hb : l'.block = l.block) (ho : l'.off = l.off) :
    L.Loc m' i l' := by
  obtain ⟨hi', hp, hj⟩ := Array.findIdx?_eq_some_iff_getElem.mp hl.1
  obtain ⟨hlb, hlo⟩ := loc_at hl
  have hs : (m.atomics.set! i l').size = m.atomics.size := by simp
  refine ⟨Array.findIdx?_eq_some_iff_getElem.mpr ⟨by rw [ha, hs]; exact hi', ?_, fun j hji => ?_⟩, ?_⟩
  · simp only [ha, Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds, ↓reduceIte]
    simp [hb, ho, hlb, hlo]
  · simp only [ha, Array.set!_eq_setIfInBounds]
    rw [Array.getElem_setIfInBounds (by omega), if_neg (Nat.ne_of_gt hji)]
    exact hj j hji
  · rw [ha, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]; simp [hi']

/-- The layout after a change of a location that keeps its shape. -/
theorem shapes_set {m m' : Mem} {i : Nat} {l' : ALoc} (hi : i < m.atomics.size)
    (ha : m'.atomics = m.atomics.set! i l') (hs : ALoc.shape l' = ALoc.shape (m.atomics[i])) :
    shapes m' = shapes m := by
  unfold shapes; rw [ha]
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.getElem_map, Array.getElem_toList, Array.set!_eq_setIfInBounds]
  rw [Array.getElem_setIfInBounds (by simpa using h2)]
  split
  · rename_i e; subst e; exact hs
  · rfl

/-- The word's location after `locIdx`: the memory is the same, or it has a new location (the
first atomic op at the word). -/
theorem WInv.locIdx {P : ThreadId → LPh} {m m₁ : Mem} {li : Nat} (hi : L.WInv P m)
    (ht : m.current < m.threads.size)
    (h : ((locIdx L.b L.o 4).run m).run = some (.ok (li, m₁))) :
    ∃ l, L.Loc m₁ li l ∧ L.WInv P m₁ ∧ m₁.blocks = m.blocks ∧ m₁.clocks = m.clocks ∧
      m₁.threads = m.threads ∧ m₁.footprint = m.footprint ∧ m₁.waiters = m.waiters ∧
      m₁.current = m.current ∧ m₁.groups = m.groups ∧ (∀ i l, L.Loc m i l → L.Loc m₁ i l) ∧
      LocsKeep L.b L.o 4 m m₁ ∧ L.ShapesStep m m₁ := by
  cases hf : m.atomics.findIdx? (fun l => l.block == L.b && l.off == L.o) with
  | some i =>
    obtain ⟨hi', -, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp hf
    have hl : L.Loc m i m.atomics[i] := ⟨hf, Array.getElem?_eq_getElem hi'⟩
    obtain ⟨hlen, -, -, -, hlast⟩ := hi.loc.ok i _ hl
    have hg : m.atomics[i]! = m.atomics[i] := getElem!_pos m.atomics i hi'
    obtain ⟨rfl, rfl⟩ := locIdx_found hf (by rw [hg]; exact hlen) (by rw [hg]; exact hlast)
      (by rw [hg]; exact hi.loc.plain i _ hl) h
    exact ⟨_, hl, hi, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ h => h, .of_eq rfl, .refl _⟩
  | none =>
    have hno := noOverlap_of_only hf hi.loc.only
    obtain ⟨rfl, rfl⟩ := locIdx_new hf hno h
    have hno' : ∀ i l, ¬ L.Loc m i l := fun i l hl => by rw [hl.1] at hf; cases hf
    let nl : ALoc := firstLoc m L.b L.o 4
    have hnl : L.Loc { m with atomics := m.atomics.push nl, nextMsg := m.nextMsg + 1 }
        m.atomics.size nl := by
      refine ⟨?_, by simp⟩
      show (m.atomics.push nl).findIdx? _ = _
      rw [Array.findIdx?_push, hf]; simp [nl, firstLoc]
    have honly : ∀ i l, L.Loc { m with atomics := m.atomics.push nl, nextMsg := m.nextMsg + 1 }
        i l → i = m.atomics.size ∧ l = nl := fun i l hl => loc_unique hl hnl
    refine ⟨nl, hnl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun i l h => absurd h (hno' i l),
      .push rfl rfl rfl rfl, .inr ⟨?_, fun s hs => ?_⟩⟩
    · obtain ⟨w, hw, hu, -⟩ := hi.word
      exact ⟨hi.csize, hi.live, hi.blk, hi.word, hi.one,
        ⟨fun l hl hb h1 h2 => by
          rcases Array.mem_push.mp hl with hl | rfl
          · exact hi.loc.only l hl hb h1 h2
          · rfl,
         fun i l hl => by
          obtain ⟨rfl, rfl⟩ := honly i l hl
          refine ⟨rfl, by simp [nl, firstLoc], fun j hj => by simp [nl, firstLoc] at hj,
            fun j hj => ?_, ?_⟩
          · simp only [nl, firstLoc, List.size_toArray, List.length_cons, List.length_nil] at hj
            obtain rfl : j = 0 := by omega
            exact ⟨w, hw, hu⟩
          · simp [ALoc.lastBytes, nl, firstLoc, firstMsg, curBytes],
         fun i l hl => by
          obtain ⟨rfl, rfl⟩ := honly i l hl
          intro e he hh
          simpa [ALoc.lastClock, nl, firstLoc, firstMsg] using plainLe_plainClock m L.b L.o 4 e he hh⟩,
        hi.wfp,
        fun i l hl => by
          obtain ⟨rfl, rfl⟩ := honly i l hl
          exact ⟨⟨m.current, ht, VClock.le_default _⟩, fun u _ => VClock.le_default _⟩,
        hi.fq, hi.wit, fun u hu =>
          let ⟨i, l, hl, _⟩ := hi.owner u hu; absurd hl (hno' i l)⟩
    · simp [shapes, nl, firstLoc, ALoc.shape, LockWord.shape]
    · simp only [shapes, List.mem_map, Array.mem_toList_iff] at hs
      obtain ⟨l, hl, rfl⟩ := hs
      intro hb
      simp only [ALoc.shape, LockWord.shape] at hb ⊢
      refine Classical.byContradiction fun hc => ?_
      exact hno l hl hb (by omega) (by omega)

/-! ## The memory after an RMW at the word -/

/-- An RMW at the word that read its newest message `rd` and wrote `new`. -/
theorem rmw_eff {m₁ m₂ M : Mem} {li : Nat} {l : ALoc} {ord : AtomicOrder} {rd : Msg}
    {new : BitVec 32} {blk : Block} (hl : L.Loc m₁ li l) (h0 : 0 < l.msgs.size)
    (hb : m₁.blocks[L.b]? = some blk) (hm₂ : m₂ = if ord.isAcq then acqM m₁ rd.relClock else m₁)
    (hM : M = rmwM m₁ li (l.msgs.size - 1) ord rd new) :
    M.threads = m₁.threads ∧ M.footprint = m₁.footprint ∧ M.waiters = m₁.waiters ∧
      M.groups = m₁.groups ∧ M.current = m₁.current ∧ M.clocks = m₂.clocks ∧
      M.blocks = (m₁.write L.b blk L.o (padTo (intSize 32) (intBytes new))).blocks ∧
      M.atomics = m₁.atomics.set! li { l with msgs := l.msgs.push (rmwMsg m₂ ord rd new) } := by
  obtain ⟨h, -, hl0⟩ := loc_get hl
  obtain ⟨hlb, hlo⟩ := loc_at hl
  have h2 : m₂.atomics = m₁.atomics ∧ m₂.blocks = m₁.blocks ∧ m₂.threads = m₁.threads ∧
      m₂.footprint = m₁.footprint ∧ m₂.waiters = m₁.waiters ∧ m₂.current = m₁.current ∧
      m₂.groups = m₁.groups := by
    subst hm₂; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨ha₂, hb₂, ht₂, hf₂, hw₂, hc₂, hg₂⟩ := h2
  have hl₂ : m₂.atomics[li]! = l := by rw [ha₂]; exact hl0
  have hblk₂ : m₂.blocks[(m₂.atomics[li]!).block]? = some blk := by rw [hl₂, hlb, hb₂]; exact hb
  have hins := insertM_last (msg := rmwMsg m₂ ord rd new) hblk₂
  rw [hl₂] at hins
  have hp : l.msgs.size - 1 + 1 = l.msgs.size := by omega
  subst hM
  unfold rmwM
  rw [← hm₂, hp]
  dsimp only
  rw [hins]
  refine ⟨ht₂, hf₂, hw₂, hg₂, hc₂, rfl, ?_, ?_⟩
  · simp only [observeM, Mem.write, hlb, hlo, hb₂]; rfl
  · simp only [observeM, ha₂]

theorem merge_le {a b c : VClock} (ha : VClock.le a c = true) (hb : VClock.le b c = true) :
    VClock.le (VClock.merge a b) c = true :=
  VClock.le_iff.mpr fun i => by
    rw [VClock.get_merge]
    have h1 := VClock.le_iff.mp ha i
    have h2 := VClock.le_iff.mp hb i
    simp only [Nat.max_def]; split <;> omega

theorem bs4 (v : BitVec 32) : (padTo (intSize 32) (intBytes v)).size = 4 :=
  LawfulEnc.size_encode (α := BitVec 32) v

theorem back_push (xs : Array Msg) (x : Msg) : (xs.push x).back! = x := by
  rw [Array.back!, getElem!_pos _ _ (by simp)]
  simp

/-! ## The holder of the word (`ALoc.holder`) -/

/-- The items newest first: the newest, then the rest. -/
theorem rev_back {α : Type} [Inhabited α] {xs : Array α} (h : 0 < xs.size) :
    ∃ r, xs.toList.reverse = xs[xs.size - 1]! :: r := by
  have hne : xs.toList ≠ [] := by
    intro e; have := congrArg List.length e; rw [Array.length_toList, List.length_nil] at this; omega
  obtain ⟨ys, y, hy⟩ : ∃ ys y, xs.toList = ys ++ [y] :=
    ⟨_, _, (List.dropLast_concat_getLast hne).symm⟩
  have hs : xs.size = ys.length + 1 := by rw [← Array.length_toList, hy]; simp
  have hb : xs[xs.size - 1]! = y := by
    rw [getElem!_pos _ _ (by omega), ← Array.getElem_toList]
    simp [hy, hs]
  exact ⟨ys.reverse, by rw [hy, hb]; simp⟩

/-- A message that is not `0` over a `0` (a successful acquire): its writer holds the word. -/
theorem holder_acq {l : ALoc} {x : Msg} (h0 : 0 < l.msgs.size) (hx : word0 x.bytes = false)
    (hb : word0 l.msgs.back!.bytes = true) :
    ALoc.holder { l with msgs := l.msgs.push x } = x.writer := by
  obtain ⟨r, hr⟩ := rev_back h0
  unfold ALoc.holder
  simp only [Array.toList_push, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append, List.map_cons, hr]
  have : l.msgs.back! = l.msgs[l.msgs.size - 1]! := rfl
  rw [this] at hb
  simp [holderRev, hx, hb]

/-- A message that is not `0` over a value that is not `0` (a waiter's write): the holder stays. -/
theorem holder_keep {l : ALoc} {x : Msg} (h0 : 0 < l.msgs.size) (hx : word0 x.bytes = false)
    (hb : word0 l.msgs.back!.bytes = false) :
    ALoc.holder { l with msgs := l.msgs.push x } = l.holder := by
  obtain ⟨r, hr⟩ := rev_back h0
  unfold ALoc.holder
  simp only [Array.toList_push, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append, List.map_cons, hr]
  have : l.msgs.back! = l.msgs[l.msgs.size - 1]! := rfl
  rw [this] at hb
  rw [holderRev]
  simp [hx, hb]

/-- `word0` of the 4 bytes of a value below `4`. -/
theorem word0_val {bs : Array Byte} {w : Nat} (hw : w < 4)
    (h : (intOfBytes 32 bs).run = some (.ok (BitVec.ofNat 32 w))) : word0 bs = (w == 0) := by
  unfold word0; rw [h]
  rcases (by omega : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3) with rfl | rfl | rfl | rfl <;> decide

theorem u32_bytes {m : Mem} {blk : Block} {v : BitVec 32} (hb : m.blocks[L.b]? = some blk) :
    L.U32 m v ↔ (intOfBytes 32 (blk.bytes.extract L.o (L.o + 4))).run = some (.ok v) := by
  unfold LockWord.U32 curBytes; rw [hb]; rfl

theorem u32_eq {m : Mem} {a b : BitVec 32} (ha : L.U32 m a) (hb : L.U32 m b) : a = b := by
  unfold LockWord.U32 at ha hb; rw [ha] at hb; cases hb; rfl

theorem ofNat_inj {a b : Nat} (ha : a < 4) (hb : b < 4)
    (h : BitVec.ofNat 32 a = BitVec.ofNat 32 b) : a = b := by
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at this
  rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this

/-- The word is `0` exactly when the lock is free. -/
theorem WInv.free_iff {P : ThreadId → LPh} {m : Mem} (hi : L.WInv P m) {w : Nat} (hw : L.Val w)
    (hu : L.U32 m (BitVec.ofNat 32 w)) : w = 0 ↔ Free P := by
  obtain ⟨w', hw', hu', hz⟩ := hi.word
  have := ofNat_inj (hw.lt) (hw'.lt) (u32_eq hu hu')
  subst this; exact hz

/-- The newest message of the word is `0` exactly when the lock is free. -/
theorem WInv.back0 {P : ThreadId → LPh} {m : Mem} {i : Nat} {l : ALoc} (hi : L.WInv P m)
    (hl : L.Loc m i l) : word0 l.msgs.back!.bytes = true ↔ Free P := by
  obtain ⟨-, h0, -, -, hlast⟩ := hi.loc.ok i l hl
  obtain ⟨w, hw, hU, hz⟩ := hi.word
  have hback : l.msgs.back? = some l.msgs.back! := by
    rw [Array.back?_eq_getElem?, Array.back!, getElem!_pos _ _ (by omega)]
    exact Array.getElem?_eq_getElem (by omega)
  have hbytes : l.msgs.back!.bytes = curBytes m L.b L.o 4 := by
    rw [← hlast]; unfold ALoc.lastBytes; rw [hback]; rfl
  rw [word0_val hw.lt (by rw [hbytes]; exact hU), ← hz]
  simp

/-- The memory `M` after an RMW at the word by thread `t` that read the newest message of `l`
and wrote the message `msg` with the value `w'`: the invariant with the places `P'`, from the
facts that depend on them. -/
theorem WInv.rmw {P P' : ThreadId → LPh} {m₁ M : Mem} {t : ThreadId} {li : Nat} {l : ALoc}
    {msg : Msg} {blk : Block} {w' : Nat} (hi : L.WInv P m₁) (hl : L.Loc m₁ li l)
    (hb : m₁.blocks[L.b]? = some blk) (hst : L.Step t m₁ M)
    (hblocks : M.blocks = (m₁.write L.b blk L.o msg.bytes).blocks)
    (hat : M.atomics = m₁.atomics.set! li { l with msgs := l.msgs.push msg })
    (hmr : msg.rmwOf = some (l.msgs[l.msgs.size - 1]!).id) (hms : msg.bytes.size = 4)
    (hw' : L.Val w') (hmv : (intOfBytes 32 msg.bytes).run = some (.ok (BitVec.ofNat 32 w')))
    (hlive : ∀ u, P' u ≠ .gone → P u ≠ .gone)
    (hz : w' = 0 ↔ Free P') (hone : ∀ u v, P' u = .holds → P' v = .holds → u = v)
    (hrel : SomeLe M msg.relClock ∧
      ∀ u, P' u = .holds → VClock.le msg.relClock (M.clocks[u]!) = true)
    (hfq : L.Queue P' M.waiters)
    (hwit : L.U32 M (BitVec.ofNat 32 w') → L.Waits M.waiters → ∃ v, v < M.threads.size ∧
      M.waiters.any (·.1 == v) = false ∧ (P' v).busy = true ∧
      (P' v = .holds → L.U32 M (BitVec.ofNat 32 L.c)))
    (hpt : P t ≠ .gone) (hmc : msg.clock = M.clocks[t]!)
    (howner : ∀ u, P' u = .holds →
      (Free P ∧ msg.writer = some u) ∨ (¬ Free P ∧ P u = .holds)) :
    L.WInv P' M := by
  obtain ⟨blk₀, hb₀, hlv, hsz, ha4, hk, hlo⟩ := hi.blk
  rw [hb] at hb₀; cases hb₀
  obtain ⟨hlen, h0, hch, hval, -⟩ := hi.loc.ok li l hl
  obtain ⟨hlb, hlo'⟩ := loc_at hl
  have hli : li < m₁.atomics.size := (loc_get hl).1
  let l' : ALoc := { l with msgs := l.msgs.push msg }
  have hl' : L.Loc M li l' := loc_set hl hat rfl rfl
  have hMb : M.blocks[L.b]? = some { blk with bytes := writeBytes blk.bytes L.o msg.bytes } := by
    rw [hblocks]; simp only [Mem.write]
    rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt
      (Array.getElem?_eq_some_iff.mp hb).1]
  have hcur : curBytes M L.b L.o 4 = msg.bytes := by
    unfold curBytes; rw [hMb]
    simp only [Option.map_some, Option.getD_some]
    have := extract_writeBytes blk.bytes L.o msg.bytes (by omega)
    rwa [hms] at this
  have hU : L.U32 M (BitVec.ofNat 32 w') := by unfold LockWord.U32; rw [hcur]; exact hmv
  have hjb : joinedB M = joinedB m₁ := joinedB_congr hst.threads
  have honly : ∀ i l₀, L.Loc M i l₀ → i = li ∧ l₀ = l' := fun i l₀ h => loc_unique h hl'
  refine ⟨by rw [hst.csize, hst.threads]; exact hi.csize, fun u hu => ?_, ?_, ⟨w', hw', hU, hz⟩,
    hone, ⟨fun l₀ hl₀ hb' h1 h2 => ?_, fun i l₀ hl₀ => ?_, fun i l₀ hl₀ => ?_⟩, fun e he hh => ?_,
    fun i l₀ hl₀ => ?_, hfq, hwit hU, fun u hu => ⟨li, l', hl', ?_⟩⟩
  · rw [hst.threads, hjb]; exact hi.live u (hlive u hu)
  · refine ⟨_, hMb, hlv, ?_, ha4, hk, hlo⟩
    show L.o + 4 ≤ (writeBytes blk.bytes L.o msg.bytes).size
    rw [writeBytes_size _ _ _ (by omega)]; exact hsz
  · rw [hat, Array.set!_eq_setIfInBounds] at hl₀
    rcases Array.mem_or_eq_of_mem_set (w := hli) (by simpa [Array.setIfInBounds, hli] using hl₀)
      with h | rfl
    · exact hi.loc.only l₀ h hb' h1 h2
    · exact hlo'
  · obtain ⟨rfl, rfl⟩ := honly i l₀ hl₀
    refine ⟨hlen, by simp [l'], hch.push h0 hmr, fun j hj => ?_, ?_⟩
    · simp only [l', Array.size_push] at hj
      simp only [l', Array.getElem_push]
      split
      · exact hval j (by assumption)
      · exact ⟨w', hw', hmv⟩
    · unfold ALoc.lastBytes; simp [l', hcur]
  · obtain ⟨rfl, rfl⟩ := honly i l₀ hl₀
    intro e he hh
    have hlc : l'.lastClock = msg.clock := by simp [l', ALoc.lastClock]
    rw [hlc, hmc]
    rcases hst.fp e he with h | ⟨-, -, -, hat', -⟩
    · rcases hi.wfp e h (hits_of_plain hh) with ⟨ha', -⟩ | hle
      · rw [plainHit_atomic ha'] at hh; cases hh
      · exact VClock.le_trans (hle t (hi.live t hpt).1 hpt) (hst.clocks t)
    · rw [plainHit_atomic hat'] at hh; cases hh
  · rcases hst.fp e he with h | ⟨-, -, -, hat', hle⟩
    · rcases hi.wfp e h hh with ⟨ha', hle⟩ | hle
      · exact .inl ⟨ha', hst.someLe hle⟩
      · exact .inr (hst.liveLe hlive hle)
    · exact .inl ⟨hat', hle⟩
  · obtain ⟨rfl, rfl⟩ := honly i l₀ hl₀
    simp only [l', back_push]
    exact hrel
  · -- the holder: the writer of an acquire over `0`, or the holder before a write over a holder
    have hx : word0 msg.bytes = false := by
      rw [word0_val hw'.lt hmv]
      simp only [beq_eq_false_iff_ne, ne_eq]
      exact fun e => (hz.mp e) u hu
    rcases howner u hu with ⟨hF, hwr⟩ | ⟨hnF, hh⟩
    · rw [holder_acq h0 hx ((hi.back0 hl).mpr hF)]; exact hwr
    · rw [holder_keep h0 hx (by simpa using mt (hi.back0 hl).mp hnF)]
      obtain ⟨i, l₀, hl₀, hw⟩ := hi.owner u hh
      obtain ⟨rfl, rfl⟩ := loc_unique hl₀ hl
      exact hw

/-- The clock of an RMW's message is its thread's clock. -/
theorem rmwMsg_clock {m₂ : Mem} {t : ThreadId} {ord : AtomicOrder} {rd : Msg} {new : BitVec 32}
    (hc : m₂.current = t) : (rmwMsg m₂ ord rd new).clock = m₂.clocks[t]! := by
  simp [rmwMsg, hc]

/-- The facts of an RMW at the word by thread `t` that read the newest message `rd`. -/
theorem WInv.rmwStep {P : ThreadId → LPh} {m₁ M : Mem} {t li : Nat} {l : ALoc} {ord : AtomicOrder}
    {new : BitVec 32} (hi : L.WInv P m₁) (hl : L.Loc m₁ li l) (hc : m₁.current = t)
    (ht : t < m₁.threads.size) (hrec : L.Rec m₁ t)
    (hM : M = rmwM m₁ li (l.msgs.size - 1) ord (l.msgs[l.msgs.size - 1]!) new) :
    ∃ blk m₂, m₁.blocks[L.b]? = some blk ∧
      m₂ = (if ord.isAcq then acqM m₁ (l.msgs[l.msgs.size - 1]!).relClock else m₁) ∧
      L.Step t m₁ M ∧ M.current = t ∧ M.waiters = m₁.waiters ∧ M.clocks = m₂.clocks ∧
      M.blocks = (m₁.write L.b blk L.o (rmwMsg m₂ ord (l.msgs[l.msgs.size - 1]!) new).bytes).blocks ∧
      M.atomics = m₁.atomics.set! li
        { l with msgs := l.msgs.push (rmwMsg m₂ ord (l.msgs[l.msgs.size - 1]!) new) } := by
  obtain ⟨blk, hb, hlv, hsz, -, -⟩ := hi.blk
  obtain ⟨-, h0, -⟩ := hi.loc.ok li l hl
  obtain ⟨hth, hfp, hwq, hg, hcur, hcl, hbl, hat⟩ := rmw_eff (new := new) hl h0 hb rfl hM
  have hcs : m₁.current < m₁.clocks.size := by rw [hi.csize, hc]; exact ht
  have hm₂ : ∀ m₂ : Mem, m₂ = (if ord.isAcq then acqM m₁ (l.msgs[l.msgs.size - 1]!).relClock
      else m₁) → m₂.clocks.size = m₁.clocks.size ∧ (∀ u, u ≠ t → m₂.clocks[u]! = m₁.clocks[u]!) ∧
      VClock.le (m₁.clocks[t]!) (m₂.clocks[t]!) = true := by
    intro m₂ e; subst e
    split
    · refine ⟨by simp [acqM], fun u hu => ?_, ?_⟩
      · simp only [acqM]; rw [getElem!_set!_ite, if_neg (fun h => hu (h.1.trans hc))]
      · rw [← hc, acqM_clock _ _ hcs]; exact VClock.le_merge_left _ _
    · exact ⟨rfl, fun _ _ => rfl, VClock.le_refl _⟩
  obtain ⟨hs1, hs2, hs3⟩ := hm₂ _ rfl
  obtain ⟨hli, hl0, -⟩ := loc_get hl
  have hcov : m₁.MsgCov → M.MsgCov := fun h => by
    obtain ⟨e, he, heb, heo, hel, hec⟩ := hrec
    obtain ⟨-, hm0, -⟩ := hi.loc.ok li l hl
    have hl1 : (m₁.atomics[li]!) = l := by rw [getElem!_pos m₁.atomics li hli, hl0]
    obtain ⟨hlb, hlo⟩ := loc_at hl
    rw [hM]
    refine (FStepIn.rmwM (hF := fun _ => none) (blk := blk) (e := e) ord _ new hcs
      (by rw [hl1]; omega) (by rw [hl1, hlb]; exact hb) (fun hin => ?_) he (by rw [hl1, hlb]; exact heb)
      (by rw [hl1, hlo]; exact heo) hel (by rw [hc]; exact hec)
      (by rw [hl1, getElem!_pos l.msgs _ (by omega)]; exact Array.getElem_mem _)).msgCov h
    have hlen : 0 < (m₁.atomics[li]!).len := by rw [hl1, (hi.loc.ok li l hl).1]; decide
    exact hin _ (Nat.le_refl _) (by omega) rfl
  refine ⟨blk, _, hb, rfl, ⟨hth, fun e he => .inl (hfp ▸ he), hg, by rw [hcl, hs1],
    fun u hu => by rw [hcl, hs2 u hu], by rw [hcl]; exact hs3, by rw [hbl]; simp [Mem.write],
    .inr ⟨blk, _, hb, hlv, bs4 new, hsz, hbl⟩, fun _ _ => by rw [hwq],
    fun c ⟨i, l₀, hl₀, hle⟩ => ?_, LocsKeep.set hl.2 (loc_at hl).1 (loc_at hl).2
      (by exact (loc_at hl).1) (by exact (loc_at hl).2) (by exact (hi.loc.ok li l hl).1) hat,
    fun e he => .inl (hfp ▸ he), .inl (shapes_set hli hat (by rw [hl0]; rfl)), hcov⟩,
    hcur.trans hc, hwq, hcl, hbl, hat⟩
  obtain ⟨rfl, rfl⟩ := loc_unique hl hl₀
  refine ⟨_, _, loc_set hl hat rfl rfl, ?_⟩
  have hbk : l.msgs.back! = l.msgs[l.msgs.size - 1]! := rfl
  simp only [back_push, rmwMsg]
  rw [hbk] at hle
  split
  · exact VClock.le_trans hle (VClock.le_merge_left _ _)
  · exact hle

theorem not_free_iff {P : ThreadId → LPh} : ¬ Free P ↔ ∃ u, P u = .holds := by
  unfold LockWord.Free
  constructor
  · intro h; exact Classical.byContradiction fun hn => h fun u hu => hn ⟨u, hu⟩
  · rintro ⟨u, hu⟩ h; exact h u hu

/-- `t` is not in the futex queue if its place is not `wait` or `away`. -/
theorem WInv.notQ {P : ThreadId → LPh} {m : Mem} {t : ThreadId} (hi : L.WInv P m)
    (hw : P t ≠ .wait) (ha : P t ≠ .away) : m.waiters.any (·.1 == t) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨i, hi', he⟩ := Array.any_eq_true.mp h
  have ht : (m.waiters[i]).1 = t := by simpa using he
  rcases hi.fq _ (Array.getElem_mem hi') with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [ht] at h2
  · exact hw h2
  · exact ha h2

/-- The futex queue without `t`, which is not at a futex wait: the waiters stay. -/
theorem fq_keep {P : ThreadId → LPh} {m : Mem} {t : ThreadId} {p : LPh} (hi : L.WInv P m)
    (hw : P t ≠ .wait) (ha : P t ≠ .away) : L.Queue (upd P t p) m.waiters :=
  hi.fq.mono (fun w hw => hw) fun w hwm => by
    have hwt : w.1 ≠ t := fun e => by
      rcases hi.fq w hwm with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [e] at h2
      · exact hw h2
      · exact ha h2
    rw [upd_ne _ _ hwt]

/-- Thread `t` takes the free lock with an acquire RMW that writes `w'` (`1` from `out`, `c` from
`spin`): it holds the lock, and its clock owns what the free lock owned. -/
theorem WInv.acquire {P : ThreadId → LPh} {m₁ M : Mem} {t li : Nat} {l : ALoc} {w' : Nat}
    (hi : L.WInv P m₁) (hl : L.Loc m₁ li l) (hc : m₁.current = t) (hrec : L.Rec m₁ t)
    (hph : (P t = .out ∧ w' = 1) ∨ (P t = .spin ∧ w' = L.c)) (hF : Free P)
    (hM : M = rmwM m₁ li (l.msgs.size - 1) .acquire (l.msgs[l.msgs.size - 1]!)
      (BitVec.ofNat 32 w')) :
    L.Step t m₁ M ∧ M.current = t ∧ L.WInv (upd P t .holds) M ∧ L.Acq P t m₁ M := by
  have hpt : P t ≠ .gone := by rcases hph with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> decide
  have hnw : P t ≠ .wait := by rcases hph with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> decide
  have hna : P t ≠ .away := by rcases hph with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> decide
  have hw3 : L.Val w' := by rcases hph with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> first | exact L.val1 | exact L.valC
  have hw0 : w' ≠ 0 := by rcases hph with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> first | decide | exact L.c_ne0
  obtain ⟨ht, -⟩ := hi.live t hpt
  obtain ⟨blk, m₂, hb, hm₂, hst, hcM, hwM, hclM, hbM, haM⟩ := hi.rmwStep hl hc ht hrec hM
  have hacq : AtomicOrder.acquire.isAcq = true := rfl
  rw [hacq, if_pos rfl] at hm₂
  subst hm₂
  have hcs : m₁.current < m₁.clocks.size := by rw [hi.csize, hc]; exact ht
  have hct : M.clocks[t]! = VClock.merge (m₁.clocks[t]!) (l.msgs[l.msgs.size - 1]!).relClock := by
    rw [hclM, ← hc, acqM_clock _ _ hcs]
  have hbl : L.b < m₁.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  have hphu : ∀ u, upd P t .holds u = if u = t then .holds else P u := fun u => upd_apply
  refine ⟨hst, hcM, hi.rmw hl hb hst hbM haM rfl (bs4 _) hw3 (intOfBytes_rmw _)
    (fun u hu => ?_) ?_ (fun u v hu hv => ?_) ?_
    (by rw [hwM]; exact fq_keep hi hnw hna) (fun hU hp => ?_)
    hpt (by rw [hclM]; exact rmwMsg_clock (by simp [acqM, hc])) (fun u hu => ?_),
    fun h ho hoff => ?_⟩
  · rw [hphu] at hu
    split at hu
    · rename_i h; subst h; exact hpt
    · exact hu
  · refine ⟨fun h => absurd h hw0, fun h => absurd (by rw [hphu]; simp) (h t)⟩
  · rw [hphu] at hu hv
    split at hu
    · split at hv
      · rename_i h1 h2; rw [h1, h2]
      · exact absurd hv (hF v)
    · exact absurd hu (hF u)
  · have hrel : (rmwMsg (acqM m₁ (l.msgs[l.msgs.size - 1]!).relClock) .acquire
        (l.msgs[l.msgs.size - 1]!) (BitVec.ofNat 32 w')).relClock =
        (l.msgs[l.msgs.size - 1]!).relClock := rfl
    rw [hrel]
    refine ⟨hst.someLe (hi.rel li l hl).1, fun u hu => ?_⟩
    rw [hphu] at hu
    split at hu
    · rename_i h; subst h; rw [hct]; exact VClock.le_merge_right _ _
    · exact absurd hu (hF u)
  · obtain ⟨v, hv, hq, h1, h2⟩ := hi.wit (hwM ▸ hp)
    refine ⟨v, by rw [hst.threads]; exact hv, hwM ▸ hq, ?_, fun hh => ?_⟩
    · rw [hphu]; split
      · rfl
      · exact h1
    · rw [hphu] at hh
      split at hh
      · rename_i h; subst h
        rcases hph with ⟨h, -⟩ | ⟨-, rfl⟩
        · rw [h] at h1; cases h1
        · exact hU
      · exact absurd hh (hF v)
  · -- the new holder `t` made the acquire
    rw [hphu] at hu
    split at hu
    · rename_i h; subst h; exact .inl ⟨hF, by simp [rmwMsg, acqM, hc]⟩
    · exact absurd hu (hF u)
  · -- the acquire adopts the release clock of the newest message
    intro e he htc
    by_cases hm : e ∈ m₁.footprint
    · rcases ho e hm (htc.imp id fun h => by rw [← hst.bsize]; exact h) with h | ⟨i, l₀, hl₀, hle⟩
      · exact VClock.le_trans (h t ht hpt) (hst.clocks t)
      · obtain ⟨rfl, rfl⟩ := loc_unique hl₀ hl
        rw [hct]
        exact VClock.le_trans hle (VClock.le_merge_right _ _)
    · rcases htc with htc | hbe
      · exact absurd htc (hst.fpOff hoff he hm)
      · rcases hst.fp e he with h | ⟨heb, -⟩
        · exact absurd h hm
        · rw [heb, hst.bsize] at hbe; exact absurd hbl (Nat.not_lt.mpr hbe)

/-- Thread `t` in `lock`'s loop writes `c` to the held lock (an acquire RMW): the holder stays,
and `t` goes to the futex wait. -/
theorem WInv.contend {P : ThreadId → LPh} {m₁ M : Mem} {t li : Nat} {l : ALoc}
    (hi : L.WInv P m₁) (hl : L.Loc m₁ li l) (hc : m₁.current = t) (hrec : L.Rec m₁ t)
    (hph : P t = .spin)
    (hnF : ¬ Free P)
    (hM : M = rmwM m₁ li (l.msgs.size - 1) .acquire (l.msgs[l.msgs.size - 1]!)
      (BitVec.ofNat 32 L.c)) :
    L.Step t m₁ M ∧ M.current = t ∧ L.WInv (upd P t .wait) M := by
  obtain ⟨ht, -⟩ := hi.live t (by rw [hph]; decide)
  obtain ⟨u0, hu0⟩ := not_free_iff.mp hnF
  have hu0t : u0 ≠ t := fun e => by rw [e, hph] at hu0; cases hu0
  obtain ⟨blk, m₂, hb, hm₂, hst, hcM, hwM, hclM, hbM, haM⟩ := hi.rmwStep hl hc ht hrec hM
  have hacq : AtomicOrder.acquire.isAcq = true := rfl
  rw [hacq, if_pos rfl] at hm₂
  subst hm₂
  have hphu : ∀ u, upd P t .wait u = if u = t then .wait else P u := fun u => upd_apply
  have hholds : ∀ u, upd P t .wait u = .holds ↔ P u = .holds := by
    intro u; rw [hphu]; split
    · rename_i h; subst h; rw [hph]; decide
    · exact Iff.rfl
  refine ⟨hst, hcM, hi.rmw hl hb hst hbM haM rfl (bs4 _) L.valC (intOfBytes_rmw _)
    (fun u hu => ?_) ?_ (fun u v hu hv => ?_) ?_
    (by rw [hwM]; exact fq_keep hi (by rw [hph]; decide) (by rw [hph]; decide)) (fun hU _ => ?_)
    (by rw [hph]; decide) (by rw [hclM]; exact rmwMsg_clock (by simp [acqM, hc]))
    (fun u hu => .inr ⟨hnF, (hholds u).mp hu⟩)⟩
  · rw [hphu] at hu
    split at hu
    · rename_i h; subst h; rw [hph]; decide
    · exact hu
  · exact ⟨fun h => absurd h L.c_ne0, fun h => absurd ((hholds u0).mpr hu0) (h u0)⟩
  · exact hi.one u v ((hholds u).mp hu) ((hholds v).mp hv)
  · refine ⟨hst.someLe (hi.rel li l hl).1, fun u hu => ?_⟩
    exact VClock.le_trans ((hi.rel li l hl).2 u ((hholds u).mp hu)) (hst.clocks u)
  · obtain ⟨hu0s, -⟩ := hi.live u0 (by rw [hu0]; decide)
    refine ⟨u0, by rw [hst.threads]; exact hu0s, ?_, by rw [upd_ne _ _ hu0t, hu0]; rfl,
      fun _ => hU⟩
    rw [hwM]; exact hi.notQ (by rw [hu0]; decide) (by rw [hu0]; decide)

/-- Thread `t` (at `out` or `spin`) writes again the value `w ≠ 0` of the held lock (an acquire
RMW, as `Thread.Mutex`'s `or 1` on a held lock): the holder stays, and `t` goes to `spin` or to the
futex wait. -/
theorem WInv.rmwKeep {P : ThreadId → LPh} {m₁ M : Mem} {t li : Nat} {l : ALoc} {w : Nat} {p : LPh}
    (hi : L.WInv P m₁) (hl : L.Loc m₁ li l) (hc : m₁.current = t) (hrec : L.Rec m₁ t)
    (hph : P t = .out ∨ P t = .spin) (hp : p = .spin ∨ p = .wait)
    (hw : L.Val w) (hU0 : L.U32 m₁ (BitVec.ofNat 32 w)) (hw0 : w ≠ 0)
    (hM : M = rmwM m₁ li (l.msgs.size - 1) .acquire (l.msgs[l.msgs.size - 1]!)
      (BitVec.ofNat 32 w)) :
    L.Step t m₁ M ∧ M.current = t ∧ L.WInv (upd P t p) M := by
  have hng : P t ≠ .gone := by rcases hph with h | h <;> rw [h] <;> decide
  have hnh : P t ≠ .holds := by rcases hph with h | h <;> rw [h] <;> decide
  have hnw : P t ≠ .wait := by rcases hph with h | h <;> rw [h] <;> decide
  have hna : P t ≠ .away := by rcases hph with h | h <;> rw [h] <;> decide
  have hph' : p ≠ .holds := by rcases hp with rfl | rfl <;> decide
  have hpb : p.busy = true := by rcases hp with rfl | rfl <;> rfl
  have hnF : ¬ Free P := fun hF => hw0 ((hi.free_iff hw hU0).mpr hF)
  obtain ⟨ht, -⟩ := hi.live t hng
  obtain ⟨u0, hu0⟩ := not_free_iff.mp hnF
  obtain ⟨blk, m₂, hb, hm₂, hst, hcM, hwM, hclM, hbM, haM⟩ := hi.rmwStep hl hc ht hrec hM
  have hacq : AtomicOrder.acquire.isAcq = true := rfl
  rw [hacq, if_pos rfl] at hm₂
  subst hm₂
  have hphu : ∀ u, upd P t p u = if u = t then p else P u := fun u => upd_apply
  have hholds : ∀ u, upd P t p u = .holds ↔ P u = .holds := by
    intro u; rw [hphu]; split
    · rename_i h; subst h; exact ⟨fun h => absurd h hph', fun h => absurd h hnh⟩
    · exact Iff.rfl
  refine ⟨hst, hcM, hi.rmw hl hb hst hbM haM rfl (bs4 _) hw (intOfBytes_rmw _)
    (fun u hu => ?_) ?_ (fun u v hu hv => ?_) ?_
    (by rw [hwM]; exact fq_keep hi hnw hna) (fun hU hq => ?_) hng
    (by rw [hclM]; exact rmwMsg_clock (by simp [acqM, hc]))
    (fun u hu => .inr ⟨hnF, (hholds u).mp hu⟩)⟩
  · rw [hphu] at hu
    split at hu
    · rename_i h; subst h; exact hng
    · exact hu
  · exact ⟨fun h => absurd h hw0, fun h => absurd ((hholds u0).mpr hu0) (h u0)⟩
  · exact hi.one u v ((hholds u).mp hu) ((hholds v).mp hv)
  · refine ⟨hst.someLe (hi.rel li l hl).1, fun u hu => ?_⟩
    exact VClock.le_trans ((hi.rel li l hl).2 u ((hholds u).mp hu)) (hst.clocks u)
  · obtain ⟨v, hv, hvq, h1, h2⟩ := hi.wit (hwM ▸ hq)
    refine ⟨v, by rw [hst.threads]; exact hv, hwM ▸ hvq, ?_, fun hh => ?_⟩
    · rw [hphu]; split
      · exact hpb
      · exact h1
    · have hvh := (hholds v).mp hh
      have e := ofNat_inj hw.lt L.c_lt (u32_eq hU0 (h2 hvh))
      rw [← e]; exact hU

/-- The holder `t` writes `0` (`unlock`, a release RMW) where the word was `w`: no thread holds the
lock, and the free lock owns what `t`'s clock owned. `t` goes to `out` (`w = 1`) or to the futex
wake (`w = c`). `w = 1` with `p = .out` needs `L.c ≠ 1`. -/
theorem WInv.release {P : ThreadId → LPh} {m₁ M : Mem} {t li : Nat} {l : ALoc} {w : Nat}
    {p : LPh} (hi : L.WInv P m₁) (hl : L.Loc m₁ li l) (hc : m₁.current = t) (hrec : L.Rec m₁ t)
    (hph : P t = .holds) (hw : L.U32 m₁ (BitVec.ofNat 32 w))
    (hp : (w = 1 ∧ p = .out ∧ L.c ≠ 1) ∨ (w = L.c ∧ p = .wake))
    (hM : M = rmwM m₁ li (l.msgs.size - 1) .release (l.msgs[l.msgs.size - 1]!)
      (BitVec.ofNat 32 0)) :
    L.Step t m₁ M ∧ M.current = t ∧ L.Before M (m₁.clocks[t]!) ∧
      L.WInv (upd P t p) M ∧ L.Rel t (upd P t p) m₁ M := by
  obtain ⟨ht, -⟩ := hi.live t (by rw [hph]; decide)
  have hpg : p ≠ .gone := by rcases hp with ⟨-, rfl, -⟩ | ⟨-, rfl⟩ <;> decide
  have hph' : p ≠ .holds := by rcases hp with ⟨-, rfl, -⟩ | ⟨-, rfl⟩ <;> decide
  have honly : ∀ u, P u = .holds → u = t := fun u hu => hi.one u t hu hph
  obtain ⟨blk, m₂, hb, hm₂, hst, hcM, hwM, hclM, hbM, haM⟩ := hi.rmwStep hl hc ht hrec hM
  have hacq : AtomicOrder.release.isAcq = false := rfl
  rw [hacq] at hm₂
  simp only [Bool.false_eq_true, ↓reduceIte] at hm₂
  subst m₂
  have hbl : L.b < m₁.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  have hphu : ∀ u, upd P t p u = if u = t then p else P u := fun u => upd_apply
  have hnh : ∀ u, upd P t p u ≠ .holds := by
    intro u hu; rw [hphu] at hu
    split at hu
    · exact hph' hu
    · rename_i h; exact h (honly u hu)
  have hg : ∀ u, upd P t p u ≠ .gone → P u ≠ .gone := by
    intro u hu; rw [hphu] at hu
    split at hu
    · rename_i h; subst h; rw [hph]; decide
    · exact hu
  have hcl : M.clocks = m₁.clocks := hclM
  have hrelM : (rmwMsg m₁ .release (l.msgs[l.msgs.size - 1]!) (BitVec.ofNat 32 0)).relClock =
      VClock.merge (l.msgs[l.msgs.size - 1]!).relClock (m₁.clocks[t]!) := by
    simp [rmwMsg, AtomicOrder.isRel, hc]
  have hrt : VClock.le (l.msgs[l.msgs.size - 1]!).relClock (m₁.clocks[t]!) = true :=
    (hi.rel li l hl).2 t hph
  have hl' := loc_set hl haM rfl rfl
  have hbf : L.Before M (m₁.clocks[t]!) := ⟨li, _, hl', by
      rw [back_push, hrelM]; exact VClock.le_merge_right _ _⟩
  refine ⟨hst, hcM, hbf,
    hi.rmw hl hb hst hbM haM rfl (bs4 _) L.val0 (intOfBytes_rmw _)
    hg ⟨fun _ => hnh, fun _ => rfl⟩ (fun u v hu _ => absurd hu (hnh u)) ?_
    (by rw [hwM]; exact fq_keep hi (by rw [hph]; decide) (by rw [hph]; decide))
    (fun hU hp' => ?_) (by rw [hph]; decide) (by rw [hclM]; exact rmwMsg_clock (by simp [acqM, hc]))
    (fun u hu => absurd hu (hnh u)), fun h ho hoff => ?_⟩
  · rw [hrelM]
    refine ⟨⟨t, by rw [hst.threads]; exact ht, ?_⟩, fun u hu => absurd hu (hnh u)⟩
    rw [hcl]; exact merge_le hrt (VClock.le_refl _)
  · rcases hp with ⟨rfl, rfl, hc1⟩ | ⟨rfl, rfl⟩
    · -- `w = 1`: the old witness is not `t`
      obtain ⟨v, hv, hq, h1, h2⟩ := hi.wit (hwM ▸ hp')
      have hvt : v ≠ t := fun e => by
        subst e
        have := ofNat_inj (by decide) L.c_lt (u32_eq hw (h2 hph))
        exact hc1 this.symm
      refine ⟨v, by rw [hst.threads]; exact hv, hwM ▸ hq, by rw [upd_ne _ _ hvt]; exact h1,
        fun hh => absurd hh (hnh v)⟩
    · -- `w = c`: `t` is at the wake
      refine ⟨t, by rw [hst.threads]; exact ht, ?_, by rw [upd_self]; rfl,
        fun hh => absurd hh (hnh t)⟩
      rw [hwM]; exact hi.notQ (by rw [hph]; decide) (by rw [hph]; decide)
  · -- the free lock owns what `t`'s clock owned: the release clock of the new message
    intro e he htc
    by_cases hm : e ∈ m₁.footprint
    · refine .inr ⟨li, _, hl', ?_⟩
      rw [back_push, hrelM]
      exact VClock.le_trans (ho e hm (htc.imp id fun h => by rw [← hst.bsize]; exact h))
        (VClock.le_merge_right _ _)
    · rcases htc with htc | hbe
      · exact absurd htc (hst.fpOff hoff he hm)
      · rcases hst.fp e he with h | ⟨heb, -⟩
        · exact absurd h hm
        · rw [heb, hst.bsize] at hbe; exact absurd hbl (Nat.not_lt.mpr hbe)

/-! ## The futex queue -/

/-- A thread that is not in the futex queue is not the thread of a waiter. -/
theorem ne_of_notQ {ws : Array (ThreadId × Ptr)} {t : ThreadId} (hq : ws.any (·.1 == t) = false)
    {w : ThreadId × Ptr} (hw : w ∈ ws) : w.1 ≠ t := fun e => by
  have : ws.any (·.1 == t) = true := Array.any_eq_true.mpr (by
    obtain ⟨i, hi', rfl⟩ := Array.mem_iff_getElem.mp hw
    exact ⟨i, hi', by simp [e]⟩)
  rw [hq] at this; cases this

/-- A change of the futex queue and of the place of thread `t` (`t` does not hold the lock and
goes to `p`, not `holds`): the memory is the same but `current`, `waiters` and `woken`. -/
theorem WInv.queue {P : ThreadId → LPh} {m : Mem} {t c : ThreadId} {p : LPh}
    {ws : Array (ThreadId × Ptr)} {wk : Array ThreadId} (hi : L.WInv P m)
    (hnh : P t ≠ .holds) (hng : P t ≠ .gone) (hp : p ≠ .holds) (hpg : p ≠ .gone)
    (hfq : L.Queue (upd P t p) ws)
    (hwit : L.Waits ws → ∃ v, v < m.threads.size ∧ ws.any (·.1 == v) = false ∧
      (upd P t p v).busy = true ∧ (upd P t p v = .holds → L.U32 m (BitVec.ofNat 32 L.c))) :
    L.WInv (upd P t p) { m with current := c, waiters := ws, woken := wk } := by
  have hphu : ∀ u, upd P t p u = if u = t then p else P u := fun u => upd_apply
  have hholds : ∀ u, upd P t p u = .holds ↔ P u = .holds := by
    intro u; rw [hphu]; split
    · rename_i h; subst h; exact ⟨fun h => absurd h hp, fun h => absurd h hnh⟩
    · exact Iff.rfl
  have hfree : Free (upd P t p) ↔ Free P := by
    unfold LockWord.Free; exact forall_congr' fun u => not_congr (hholds u)
  have hgw : ∀ u, upd P t p u ≠ .gone → P u ≠ .gone := fun u h => by
    rw [hphu] at h; split at h
    · rename_i e; subst e; exact hng
    · exact h
  refine ⟨hi.csize, fun u hu => ?_, hi.blk, ?_, fun u v hu hv => hi.one u v ((hholds u).mp hu)
    ((hholds v).mp hv), ⟨hi.loc.only, hi.loc.ok, hi.loc.plain⟩, hi.wfpW hgw, fun i l hl => ?_,
    hfq, hwit, fun u hu => hi.owner u ((hholds u).mp hu)⟩
  · rw [hphu] at hu
    split at hu
    · rename_i h; subst h; exact hi.live _ hng
    · exact hi.live u hu
  · obtain ⟨w, hw, hu, hz⟩ := hi.word; exact ⟨w, hw, hu, hz.trans hfree.symm⟩
  · obtain ⟨h1, h2⟩ := hi.rel i l hl
    exact ⟨h1, fun u hu => h2 u ((hholds u).mp hu)⟩

/-- The old witness of the queue, if `t` keeps a busy place or was not busy. -/
theorem wit_keep {P : ThreadId → LPh} {m : Mem} {t : ThreadId} {p : LPh} (hi : L.WInv P m)
    (hnh : P t ≠ .holds) (hp : p ≠ .holds) (hb : (P t).busy = true → p.busy = true) :
    L.Waits m.waiters → ∃ v, v < m.threads.size ∧ m.waiters.any (·.1 == v) = false ∧
      (upd P t p v).busy = true ∧ (upd P t p v = .holds → L.U32 m (BitVec.ofNat 32 L.c)) := by
  intro hpos
  obtain ⟨v, hv, hq, h1, h2⟩ := hi.wit hpos
  refine ⟨v, hv, hq, ?_, fun hh => ?_⟩
  · rw [upd_apply]; split
    · rename_i h; subst h; exact hb h1
    · exact h1
  · rw [upd_apply] at hh
    split at hh
    · exact absurd hh hp
    · exact h2 hh

/-- `lock`'s futex wait for `c` by thread `t` (at `wait`, not in the queue). If it sleeps, the
invariant holds with `t` in the queue: the word is `c`, so a thread holds the lock. Else `t` goes
to `spin`. -/
theorem WInv.wait {P : ThreadId → LPh} {m m' : Mem} {t : ThreadId} {b : Bool} (hi : L.WInv P m)
    (hph : P t = .wait) (hq : m.waiters.any (·.1 == t) = false)
    (h : ((Thread.futexWait L.ptr (BitVec.ofNat 32 L.c)).run { m with current := t }).run =
      some (.ok (b, m'))) :
    L.Step t m m' ∧ if b then L.WInv P m' else
      (m'.current = t ∧ L.WInv (upd P t .spin) m') := by
  have hnh : P t ≠ .holds := by rw [hph]; decide
  have hng : P t ≠ .gone := by rw [hph]; decide
  have ht : t < m.threads.size := (hi.live t hng).1
  let M := ({ m with current := t } : Mem).recordAt L.b L.o 4 .atomicRead
  have hi₀ : L.WInv P { m with current := t } := hi.current t
  have hiM : L.WInv P M := hi₀.record (by rfl) ht
  have hsM : L.Step t m M :=
    (Step.same (t := t) (m := m) (m' := { m with current := t }) rfl rfl rfl rfl rfl rfl
      (fun _ _ => Iff.rfl)).trans (hi₀.recordStep (k := .atomicRead) rfl ht rfl) (.inl rfl)
  have hspin : ∀ (mm : Mem) (wk : Array ThreadId), L.WInv P mm → mm.waiters = m.waiters →
      L.WInv (upd P t .spin) { mm with current := t, waiters := mm.waiters, woken := wk } :=
    fun mm wk hii hw =>
    hii.queue hnh hng (by decide) (by decide)
      (hii.fq.mono (fun w hw => hw) fun w hw' => by
        rw [hw] at hw'; rw [upd_ne _ _ (ne_of_notQ hq hw')])
      (wit_keep hii hnh (by decide) fun _ => rfl)
  rcases futexWait_eq h with ⟨-, rfl, rfl⟩ | ⟨-, bid, blk, o, v, ha, -, hv, ⟨rfl, rfl, rfl⟩ | ⟨-, rfl, rfl⟩⟩
  · exact ⟨Step.same rfl rfl rfl rfl rfl rfl (fun _ _ => Iff.rfl), rfl, hspin m _ hi rfl⟩
  · -- it sleeps: the word is `c`
    obtain ⟨blk₀, hb₀, -, -, ha₀, -⟩ := hi.blk.access
    have : ({ m with current := t } : Mem).access L.ptr 4 4 = m.access L.ptr 4 4 := rfl
    rw [this, ha₀] at ha
    cases ha
    refine ⟨hsM.trans (Step.same rfl rfl rfl rfl rfl rfl fun w hw => ?_) (.inr rfl), ?_⟩
    · simp only [Array.mem_push]
      exact ⟨fun h => h.resolve_right fun e => hw (by rw [e]), .inl⟩
    simp only [↓reduceIte]
    have h2 : L.U32 M (BitVec.ofNat 32 L.c) := (u32_bytes (m := M) hb₀).mpr hv
    obtain ⟨u0, hu0⟩ := not_free_iff.mp fun hF =>
      absurd ((hiM.free_iff L.valC h2).mpr hF) L.c_ne0
    have hu0t : u0 ≠ t := fun e => by rw [e, hph] at hu0; cases hu0
    have hG : upd P t .wait = P := by rw [← hph]; exact upd_same P t
    have := hiM.queue (c := t) (ws := M.waiters.push (t, L.ptr)) (wk := M.woken) (p := .wait) hnh hng
      (by decide) (by decide) (fun w hw => ?_) (fun _ => ?_)
    · rw [hG] at this; exact this
    · rw [hG]
      rcases Array.mem_push.mp hw with hw | rfl
      · exact hiM.fq w hw
      · exact .inl ⟨rfl, hph⟩
    · rw [hG]
      obtain ⟨hu0s, -⟩ := hiM.live u0 (by rw [hu0]; decide)
      refine ⟨u0, hu0s, ?_, by rw [hu0]; rfl, fun _ => h2⟩
      rw [Array.any_push, hiM.notQ (by rw [hu0]; decide) (by rw [hu0]; decide)]
      simp [Ne.symm hu0t]
  · obtain ⟨blk₀, hb₀, -, -, ha₀, -⟩ := hi.blk.access
    have : ({ m with current := t } : Mem).access L.ptr 4 4 = m.access L.ptr 4 4 := rfl
    rw [this, ha₀] at ha
    cases ha
    exact ⟨hsM, rfl, hspin M M.woken hiM rfl⟩

/-- A spurious return of `lock`'s futex wait by thread `t` (at `wait`, not in the queue): `t` goes
to `spin` with the memory before the wait. -/
theorem WInv.spurious {P : ThreadId → LPh} {m : Mem} {t : ThreadId} (hi : L.WInv P m)
    (hph : P t = .wait) (hq : m.waiters.any (·.1 == t) = false) :
    L.Step t m { m with current := t } ∧ { m with current := t }.current = t ∧
      L.WInv (upd P t .spin) { m with current := t } := by
  have hnh : P t ≠ .holds := by rw [hph]; decide
  have hng : P t ≠ .gone := by rw [hph]; decide
  exact ⟨Step.same rfl rfl rfl rfl rfl rfl (fun _ _ => Iff.rfl), rfl,
    hi.queue (wk := m.woken) hnh hng (by decide) (by decide)
      (hi.fq.mono (fun w hw => hw) fun w hw => by rw [upd_ne _ _ (ne_of_notQ hq hw)])
      (wit_keep hi hnh (by decide) fun _ => rfl)⟩

/-- `unlock`'s futex wake of `n ≥ 1` waiters by thread `t` (at `wake`): `t` goes to `out`; a woken
thread is the new witness of the queue. -/
theorem WInv.wake {P : ThreadId → LPh} {m m' : Mem} {t : ThreadId} {n : Nat} {cs : List Nat}
    (hi : L.WInv P m) (hph : P t = .wake) (hn : 1 ≤ n)
    (h : ((Thread.futexWake L.ptr n cs).run { m with current := t }).run = some (.ok ((), m'))) :
    L.Step t m m' ∧ m'.current = t ∧ L.WInv (upd P t .out) m' := by
  have hnh : P t ≠ .holds := by rw [hph]; decide
  have hng : P t ≠ .gone := by rw [hph]; decide
  have hm' := Proto.modify_ok h
  generalize hwk : Thread.wakeSet m.waiters L.ptr n cs = woke at hm'
  have hwoke : ∀ u ∈ woke, P u = .wait := by
    intro u hu
    rw [← hwk] at hu
    obtain ⟨w, hw, hp, rfl⟩ := Thread.mem_wakeSet hu
    rcases hi.fq w hw with ⟨-, h⟩ | ⟨h1, -⟩
    · exact h
    · exact absurd hp h1
  subst hm'
  refine ⟨Step.same rfl rfl rfl rfl rfl rfl fun w hw => ?_, rfl,
    hi.queue hnh hng (by decide) (by decide)
    ((fq_keep hi (by rw [hph]; decide) (by rw [hph]; decide)).mono
      (fun w hw => (Array.mem_filter.mp hw).1) fun _ _ => rfl) (fun hpos => ?_)⟩
  · simp only [Array.mem_filter, Bool.not_eq_true', and_iff_left_iff_imp]
    intro hwm
    apply Bool.eq_false_iff.mpr
    intro hc
    rcases hi.fq w hwm with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact hw h1
    · rw [hwoke w.1 (Array.contains_iff_mem.mp hc)] at h2; cases h2
  obtain ⟨u0, hw0⟩ : ∃ u0, u0 ∈ woke := by
    rw [← hwk]
    refine Thread.wakeSet_nonempty (by omega) ?_
    obtain ⟨i, hi', he⟩ := Array.any_eq_true.mp hpos
    exact ⟨_, (Array.mem_filter.mp (Array.getElem_mem hi')).1, by simpa using he⟩
  have hw0p : P u0 = .wait := hwoke _ hw0
  have hw0t : u0 ≠ t := fun e => by rw [e, hph] at hw0p; cases hw0p
  obtain ⟨hw0s, -⟩ := hi.live u0 (by rw [hw0p]; decide)
  refine ⟨u0, hw0s, ?_, by rw [upd_ne _ _ hw0t, hw0p]; rfl, fun hh => ?_⟩
  · apply Array.any_eq_false.mpr
    intro i hi' he
    have hm := Array.getElem_mem hi'
    rw [Array.mem_filter] at hm
    have : woke.contains (m.waiters.filter fun w => !woke.contains w.1)[i].1 = false := by
      simpa using hm.2
    simp only [beq_iff_eq] at he
    rw [he, Array.contains_iff_mem.mpr hw0] at this
    cases this
  · rw [upd_ne _ _ hw0t, hw0p] at hh; cases hh

/-- A change of the futex queue and the woken threads, with the same places. -/
theorem WInv.requeue {P : ThreadId → LPh} {m : Mem} {c : ThreadId} {ws : Array (ThreadId × Ptr)}
    {wk : Array ThreadId} (hi : L.WInv P m) (hfq : L.Queue P ws)
    (hwit : L.Waits ws → ∃ v, v < m.threads.size ∧ ws.any (·.1 == v) = false ∧
      (P v).busy = true ∧ (P v = .holds → L.U32 m (BitVec.ofNat 32 L.c))) :
    L.WInv P { m with current := c, waiters := ws, woken := wk } :=
  ⟨hi.csize, hi.live, hi.blk, hi.word, hi.one, ⟨hi.loc.only, hi.loc.ok, hi.loc.plain⟩, hi.wfp,
    hi.rel, hfq, hwit, hi.owner⟩

/-- A futex wait of thread `t` (`away`, not in the queue) at another futex `p`, whose bytes are
not the word's. If it sleeps, the invariant holds with `t` in the queue; else `t` goes to `out`. -/
theorem WInv.waitOff {P : ThreadId → LPh} {m m' : Mem} {t : ThreadId} {p : Ptr} {e : BitVec 32}
    {b : Bool} (hi : L.WInv P m) (hph : P t = .away) (hp : p ≠ L.ptr)
    (hoff : ∀ bid blk o, m.access p 4 4 = pure (bid, blk, o) → bid ≠ L.b ∨ o + 4 ≤ L.o ∨ L.o + 4 ≤ o)
    (hq : m.waiters.any (·.1 == t) = false)
    (h : ((Thread.futexWait p e).run { m with current := t }).run = some (.ok (b, m'))) :
    if b then L.WInv P m' else (m'.current = t ∧ L.WInv (upd P t .out) m') := by
  have hnh : P t ≠ .holds := by rw [hph]; decide
  have hng : P t ≠ .gone := by rw [hph]; decide
  have hout : ∀ (mm : Mem) (wk : Array ThreadId), L.WInv P mm → mm.waiters = m.waiters →
      L.WInv (upd P t .out) { mm with current := t, waiters := mm.waiters, woken := wk } :=
    fun mm wk hii hw =>
    hii.queue hnh hng (by decide) (by decide)
      (hii.fq.mono (fun w hw => hw) fun w hw' => by
        rw [hw] at hw'; rw [upd_ne _ _ (ne_of_notQ hq hw')])
      (wit_keep hii hnh (by decide) fun h => by rw [hph] at h; cases h)
  rcases futexWait_eq h with ⟨-, rfl, rfl⟩ | ⟨-, bid, blk, o, v, ha, -, -, hc⟩
  · exact ⟨rfl, hout m _ hi rfl⟩
  have ha' : m.access p 4 4 = pure (bid, blk, o) := ha
  have hiM : L.WInv P (({ m with current := t } : Mem).recordAt bid o 4 .atomicRead) :=
    (hi.current t).readK (by decide) (hoff bid blk o ha')
  rcases hc with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
  · refine hiM.requeue (fun w hw => ?_) fun hw => ?_
    · rcases Array.mem_push.mp hw with hw | rfl
      · exact hiM.fq w hw
      · exact .inr ⟨hp, hph⟩
    · have hw' : L.Waits m.waiters := by
        unfold LockWord.Waits at hw ⊢
        rw [Array.any_push] at hw
        simpa [hp] using hw
      obtain ⟨v, hv, hvq, h1, h2⟩ := hiM.wit hw'
      have hvt : v ≠ t := fun e => by rw [e, hph] at h1; cases h1
      have hvq' : m.waiters.any (·.1 == v) = false := hvq
      refine ⟨v, hv, ?_, h1, h2⟩
      show (m.waiters.push (t, p)).any (·.1 == v) = false
      rw [Array.any_push, hvq']; simp [Ne.symm hvt]
  · exact ⟨rfl, hout _ _ hiM rfl⟩

/-- A spurious return of a futex wait of thread `t` (`away`, not in the queue) at another
futex: `t` goes to `out` with the memory before the wait. -/
theorem WInv.spuriousOff {P : ThreadId → LPh} {m : Mem} {t : ThreadId} (hi : L.WInv P m)
    (hph : P t = .away) (hq : m.waiters.any (·.1 == t) = false) :
    ({ m with current := t } : Mem).current = t ∧
      L.WInv (upd P t .out) { m with current := t } := by
  have hnh : P t ≠ .holds := by rw [hph]; decide
  have hng : P t ≠ .gone := by rw [hph]; decide
  exact ⟨rfl, hi.queue (wk := m.woken) hnh hng (by decide) (by decide)
    (hi.fq.mono (fun w hw => hw) fun w hw => by rw [upd_ne _ _ (ne_of_notQ hq hw)])
    (wit_keep hi hnh (by decide) fun h => by rw [hph] at h; cases h)⟩

/-- A futex wake by thread `t` at another futex `p`: the threads at the word stay. -/
theorem WInv.wakeOff {P : ThreadId → LPh} {m m' : Mem} {t : ThreadId} {p : Ptr} {n : Nat}
    {cs : List Nat} (hi : L.WInv P m) (hp : p ≠ L.ptr)
    (h : ((Thread.futexWake p n cs).run { m with current := t }).run = some (.ok ((), m'))) :
    L.WInv P m' := by
  have hm' := Proto.modify_ok h
  generalize hwk : Thread.wakeSet m.waiters p n cs = woke at hm'
  have hwoke : ∀ u ∈ woke, P u = .away := by
    intro u hu
    rw [← hwk] at hu
    obtain ⟨w, hw, hwp, rfl⟩ := Thread.mem_wakeSet hu
    rcases hi.fq w hw with ⟨h1, -⟩ | ⟨-, h⟩
    · exact absurd (hwp.symm.trans h1) hp
    · exact h
  subst hm'
  have hsub : ∀ w ∈ m.waiters.filter (fun w => !woke.contains w.1), w ∈ m.waiters :=
    fun w hw => (Array.mem_filter.mp hw).1
  refine hi.requeue (hi.fq.mono hsub fun _ _ => rfl) fun hw => ?_
  have hw' : L.Waits m.waiters := by
    obtain ⟨i, hi', he⟩ := Array.any_eq_true.mp hw
    exact Array.any_eq_true.mpr (by
      obtain ⟨j, hj, hje⟩ := Array.mem_iff_getElem.mp (hsub _ (Array.getElem_mem hi'))
      exact ⟨j, hj, by rw [hje]; exact he⟩)
  obtain ⟨v, hv, hvq, h1, h2⟩ := hi.wit hw'
  refine ⟨v, hv, Bool.eq_false_iff.mpr fun hc => ?_, h1, h2⟩
  obtain ⟨i, hi', he⟩ := Array.any_eq_true.mp hc
  have := ne_of_notQ hvq (hsub _ (Array.getElem_mem hi'))
  exact this (by simpa using he)

/-! ## The ops of `Io.Mutex` -/

/-- The states of `Io.Mutex` in the generated code: an enum with the bits `0`, `1`, `c`. -/
structure States (α : Type) [Packed α 32] where
  unl : α
  one : α
  two : α
  /-- The bits of `two`: `2` (`Io.Mutex`) or `3` (`Thread.Mutex`). -/
  c : Nat
  bits0 : Packed.toBits unl = 0
  bits1 : Packed.toBits one = 1
  bits2 : Packed.toBits two = BitVec.ofNat 32 c
  dec0 : (Packed.ofBits? (α := α) (BitVec.ofNat 32 0)).run = some (.ok unl)
  dec1 : (Packed.ofBits? (α := α) (BitVec.ofNat 32 1)).run = some (.ok one)
  dec2 : (Packed.ofBits? (α := α) (BitVec.ofNat 32 c)).run = some (.ok two)
  ne01 : unl ≠ one
  ne02 : unl ≠ two
  ne12 : one ≠ two

theorem intSize32 : intSize 32 = 4 := rfl

/-- The record of an atomic access and the location: a lock step without a change of place. -/
theorem WInv.prepK {P : ThreadId → LPh} {m m₁ : Mem} {t li : Nat} {k : AccessKind}
    (hk : k.isAtomic = true) (hi : L.WInv P m) (hc : m.current = t) (ht : t < m.threads.size)
    (hl : ((Zig.locIdx L.b L.o 4).run (m.recordAt L.b L.o 4 k)).run = some (.ok (li, m₁))) :
    ∃ l, L.Loc m₁ li l ∧ L.WInv P m₁ ∧ L.Step t m m₁ ∧ m₁.current = t ∧
      m₁.waiters = m.waiters ∧ m₁.blocks = m.blocks ∧ m₁.atomics[li]! = l ∧ L.Rec m₁ t := by
  have hcs : m.current < m.clocks.size := by rw [hi.csize, hc]; exact ht
  have hir := hi.record hk (hc ▸ ht)
  have hcov : m.MsgCov → m₁.MsgCov := fun h => by
    obtain ⟨blk, hb, -, hsz, -⟩ := hi.blk
    exact (FStepIn.locIdx (m := m.recordAt L.b L.o 4 k) (hF := fun _ => none) (by decide)
      (fun _ _ _ => rfl) ⟨blk, hb, hsz⟩ hl).msgCov h.recordAt
  obtain ⟨l, hl', hi₁, hb₁, hc₁, ht₁, hf₁, hw₁, hcu₁, hg₁, hlk, hks, hsh⟩ := hir.locIdx (hc ▸ ht) hl
  have hrec : L.Rec m₁ t := by
    have := rec_recordAt (L := L) (k := k) hc (hc ▸ hcs)
    unfold Rec at this ⊢; rw [hf₁, hc₁]; exact this
  refine ⟨l, hl', hi₁, ⟨by rw [ht₁]; rfl, fun e he => ?_, by rw [hg₁]; rfl,
    by rw [hc₁]; simp [Mem.recordAt], fun u hu => ?_, ?_, by rw [hb₁]; rfl, .inl (by rw [hb₁]; rfl),
    fun _ _ => by rw [hw₁]; rfl, fun _ ⟨i, l₀, h₀, hle⟩ => ⟨i, l₀, hlk i l₀ h₀, hle⟩,
    (LocsKeep.of_eq (m := m) (m' := m.recordAt L.b L.o 4 k) rfl).trans hks, fun e he => ?_,
    (ShapesStep.of_atomics (m := m) (m' := m.recordAt L.b L.o 4 k) rfl).trans hsh, hcov⟩,
    by rw [hcu₁, ← hc]; rfl, by rw [hw₁]; rfl, by rw [hb₁]; rfl, (loc_get hl').2.2, hrec⟩
  · rw [hf₁] at he
    simp only [Mem.recordAt, Array.mem_push] at he
    rcases he with he | rfl
    · exact .inl he
    · refine .inr ⟨rfl, rfl, rfl, hk, m.current, by rw [ht₁]; exact hc ▸ ht, ?_⟩
      rw [hc₁]; simp only [Mem.recordAt]; rw [getElem!_set!_ite]; simp [hcs, VClock.le_refl]
  · rw [hc₁]; simp only [Mem.recordAt]; rw [getElem!_set!_ite, if_neg (fun h => hu (h.1.trans hc))]
  · rw [hc₁, ← hc]; simp only [Mem.recordAt]; rw [getElem!_set!_ite]; simp [hcs, VClock.le_bump]
  · rw [hf₁] at he
    simp only [Mem.recordAt, Array.mem_push] at he
    rcases he with he | rfl
    · exact .inl he
    · refine .inr ⟨hc, ?_⟩
      rw [hc₁, ← hc]; simp only [Mem.recordAt]; rw [getElem!_set!_ite]; simp [hcs, VClock.le_refl]

/-- The preparation of an atomic write op at the word by thread `t`. -/
theorem WInv.prep {P : ThreadId → LPh} {m m₁ : Mem} {t li b o : Nat} {blk : Block}
    (hi : L.WInv P m) (hc : m.current = t) (ht : t < m.threads.size)
    (hacc : m.accessW L.ptr (intSize 32) 4 = pure (b, blk, o))
    (hl : ((Zig.locIdx b o (intSize 32)).run (m.recordAt b o (intSize 32) .atomicWrite)).run =
      some (.ok (li, m₁))) :
    b = L.b ∧ o = L.o ∧ ∃ l, L.Loc m₁ li l ∧ L.WInv P m₁ ∧ L.Step t m m₁ ∧ m₁.current = t ∧
      m₁.waiters = m.waiters ∧ m₁.blocks = m.blocks ∧ m₁.atomics[li]! = l ∧ L.Rec m₁ t := by
  obtain ⟨blk₀, -, -, -, -, ha₀⟩ := hi.blk.access
  rw [intSize32] at hacc hl
  rw [ha₀] at hacc
  cases hacc
  exact ⟨rfl, rfl, hi.prepK rfl hc ht hl⟩

/-- The preparation of an atomic read at the word by thread `t`. -/
theorem WInv.prepR {P : ThreadId → LPh} {m m₁ : Mem} {t li b o : Nat} {blk : Block}
    (hi : L.WInv P m) (hc : m.current = t) (ht : t < m.threads.size)
    (hacc : m.access L.ptr (intSize 32) 4 = pure (b, blk, o))
    (hl : ((Zig.locIdx b o (intSize 32)).run (m.recordAt b o (intSize 32) .atomicRead)).run =
      some (.ok (li, m₁))) :
    b = L.b ∧ o = L.o ∧ ∃ l, L.Loc m₁ li l ∧ L.WInv P m₁ ∧ L.Step t m m₁ ∧ m₁.current = t ∧
      m₁.waiters = m.waiters ∧ m₁.blocks = m.blocks ∧ m₁.atomics[li]! = l ∧ L.Rec m₁ t := by
  obtain ⟨blk₀, -, -, -, ha₀, -⟩ := hi.blk.access
  rw [intSize32] at hacc hl
  rw [ha₀] at hacc
  cases hacc
  exact ⟨rfl, rfl, hi.prepK rfl hc ht hl⟩

/-- CAS preparation checks a writable pointer but first records a read. -/
theorem WInv.prepC {P : ThreadId → LPh} {m m₁ : Mem} {t li b o : Nat} {blk : Block}
    (hi : L.WInv P m) (hc : m.current = t) (ht : t < m.threads.size)
    (hacc : m.accessW L.ptr (intSize 32) 4 = pure (b, blk, o))
    (hl : ((Zig.locIdx b o (intSize 32)).run (m.recordAt b o (intSize 32) .atomicRead)).run =
      some (.ok (li, m₁))) :
    b = L.b ∧ o = L.o ∧ ∃ l, L.Loc m₁ li l ∧ L.WInv P m₁ ∧ L.Step t m m₁ ∧ m₁.current = t ∧
      m₁.waiters = m.waiters ∧ m₁.blocks = m.blocks ∧ m₁.atomics[li]! = l ∧ L.Rec m₁ t :=
  hi.prepR hc ht (accessW_pure (by rw [hacc]; rfl)).1 hl

/-- Each message of the word holds `0`, `1` or `c`; the newest one holds the word. -/
theorem WInv.msgVal {P : ThreadId → LPh} {m : Mem} {li j : Nat} {l : ALoc} {v : BitVec 32}
    (hi : L.WInv P m) (hl : L.Loc m li l) (hj : j < l.msgs.size)
    (h : (intOfBytes 32 (l.msgs[j]!).bytes).run = some (.ok v)) :
    ∃ w, L.Val w ∧ v = BitVec.ofNat 32 w ∧ (j = l.msgs.size - 1 → L.U32 m v) := by
  obtain ⟨-, -, -, hval, hlast⟩ := hi.loc.ok li l hl
  obtain ⟨w, hw, hv⟩ := hval j hj
  rw [getElem!_pos l.msgs _ hj, hv] at h
  cases h
  refine ⟨w, hw, rfl, fun e => ?_⟩
  subst e
  unfold LockWord.U32; rw [← hlast]
  unfold ALoc.lastBytes
  rw [Array.back?_eq_getElem?, Array.getElem?_eq_getElem hj]
  simpa using hv

theorem States.dec {α : Type} [Packed α 32] (S : States α) (hS : S.c = L.c) {w : Nat}
    (hw : L.Val w) :
    ∃ v, (Packed.ofBits? (α := α) (BitVec.ofNat 32 w)).run = some (.ok v) ∧
      ((w = 0 ∧ v = S.unl) ∨ (w = 1 ∧ v = S.one) ∨ (w = L.c ∧ v = S.two)) := by
  rcases hw with rfl | rfl | rfl
  · exact ⟨_, S.dec0, .inl ⟨rfl, rfl⟩⟩
  · exact ⟨_, S.dec1, .inr (.inl ⟨rfl, rfl⟩)⟩
  · rw [← hS]; exact ⟨_, S.dec2, .inr (.inr ⟨rfl, rfl⟩)⟩

theorem decode_eq {α : Type} [Packed α 32] {b : BitVec 32} {v v' : α}
    (h : (Packed.ofBits? (α := α) b).run = some (.ok v))
    (h' : (Packed.ofBits? (α := α) b).run = some (.ok v')) : v = v' := by
  rw [h] at h'; cases h'; rfl

theorem WInv.bl {P : ThreadId → LPh} {m : Mem} (hi : L.WInv P m) : L.b < m.blocks.size := by
  obtain ⟨blk, hb, -⟩ := hi.blk; exact (Array.getElem?_eq_some_iff.mp hb).1

/-- A read at the word that is not an acquire: the same places. -/
theorem WInv.observe {P : ThreadId → LPh} {m₁ : Mem} {li id : Nat} (hi : L.WInv P m₁) :
    L.WInv P (observeM m₁ li id) :=
  hi.mono rfl rfl rfl rfl rfl (fun _ => VClock.le_refl _) (fun e he => .inl he) fun e he => .inl he

theorem Step.observe {t : ThreadId} {m₁ : Mem} {li id : Nat} :
    L.Step t m₁ (observeM m₁ li id) :=
  Step.same rfl rfl rfl rfl rfl rfl fun _ _ => Iff.rfl

/-- The core of a CAS `0 → 1` with an acquire, by thread `t` at `out` or `spin`: on success `t`
holds the lock and its clock owns what the free lock owned; else it read `w ≠ 0`. -/
theorem WInv.casCore {P : ThreadId → LPh} {m m' : Mem} {t c : Nat} {o : Option (BitVec 32)}
    (hi : L.WInv P m) (hph : P t = .out ∨ (P t = .spin ∧ L.c = 1)) (hc : m.current = t)
    (h : ((cmpxchgAt c .acquire .relaxed 4 L.ptr (0 : BitVec 32) 1).run m).run =
      some (.ok (o, m'))) :
    L.Step t m m' ∧ m'.current = t ∧
      ((o = none ∧ Free P ∧ L.WInv (upd P t .holds) m' ∧ L.Acq P t m m') ∨
       ∃ w, L.Val w ∧ w ≠ 0 ∧ o = some (BitVec.ofNat 32 w) ∧ L.WInv P m') := by
  have hng : P t ≠ .gone := by rcases hph with h | ⟨h, -⟩ <;> rw [h] <;> decide
  obtain ⟨ht, -⟩ := hi.live t hng
  obtain ⟨b, blk, off, li, m₁, pos, old, hacc, -, hl, hpos, hold, hcase⟩ := cmpxchgAt_ok h
  obtain ⟨rfl, rfl, l, hl', hi₁, hst₁, hcu₁, -, hb₁, hl0, -⟩ := hi.prepC hc ht hacc hl
  obtain ⟨-, h0, hch, -, -⟩ := hi₁.loc.ok li l hl'
  rw [hl0] at hold
  rcases hcase with ⟨rfl, rfl, -, hm'⟩ | ⟨hne, rfl, hm'⟩
  · have hpl := cas_chain_pos (m := m₁) (li := li) (by rw [hl0]; exact hch) hpos
      (by rw [hl0]; exact hold)
    rw [hl0] at hpl hm'
    rw [hpl] at hold hm'
    obtain ⟨w, -, -, hU⟩ := hi₁.msgVal hl' (by omega) hold
    have hU0 : L.U32 m₁ (BitVec.ofNat 32 0) := hU rfl
    have hF : Free P := (hi₁.free_iff L.val0 hU0).mp rfl
    have ht₁ : t < m₁.threads.size := by rw [hst₁.threads]; exact ht
    have hi₂ := hi₁.record (k := .atomicWrite) rfl (hcu₁ ▸ ht₁)
    have hstR := hi₁.recordStep hcu₁ ht₁ (k := .atomicWrite) rfl
    obtain ⟨hst₂, hcM, hi', hacq⟩ := hi₂.acquire (w' := 1) hl' hcu₁
      (rec_recordAt hcu₁ (by rw [hi₁.csize]; exact ht₁))
      (hph.elim (fun h => .inl ⟨h, rfl⟩) fun ⟨h, hc1⟩ => .inr ⟨h, hc1.symm⟩) hF hm'
    have hbl₁ : L.b < m₁.blocks.size := hi₁.bl
    exact ⟨hst₁.trans (hstR.trans hst₂ (.inl rfl)) (.inl hb₁), hcM,
      .inl ⟨rfl, hF, hi', (hacq.pre hstR hbl₁).pre hst₁ hi.bl⟩⟩
  · obtain ⟨hlt, -⟩ := casOpts_pos hpos
    rw [hl0] at hlt
    obtain ⟨w, hw, rfl, -⟩ := hi₁.msgVal hl' hlt hold
    have hw0 : w ≠ 0 := fun e => hne (by rw [e]; rfl)
    have hmM : m' = observeM m₁ li ((m₁.atomics[li]!).msgs[pos]!).id := by
      rw [hm']; unfold loadM; rfl
    rw [hmM]
    exact ⟨hst₁.trans Step.observe (.inl hb₁), by rw [← hcu₁]; rfl, .inr ⟨w, hw, hw0, rfl, hi₁.observe⟩⟩

/-- `lock`'s first try, `cmpxchg(unlocked → locked_once)` with an acquire, by thread `t` at `out`:
on success `t` holds the lock; else it read `1` (`spin`) or `c` (`wait`). -/
theorem WInv.cas {P : ThreadId → LPh} {m m' : Mem} {t c : Nat} {α : Type} [Packed α 32]
    (S : States α) (hS : S.c = L.c) {r : Option α} (hi : L.WInv P m) (hph : P t = .out)
    (hc : m.current = t)
    (h : ((cmpxchgAs c .acquire .relaxed 4 L.ptr S.unl S.one).run m).run = some (.ok (r, m'))) :
    L.Step t m m' ∧ m'.current = t ∧
      ((r = none ∧ Free P ∧ L.WInv (upd P t .holds) m' ∧ L.Acq P t m m') ∨
       (r = some S.one ∧ L.WInv (upd P t .spin) m') ∨
       (r = some S.two ∧ L.WInv (upd P t .wait) m')) := by
  have core : ∀ o, ((cmpxchgAt c .acquire .relaxed 4 L.ptr (Packed.toBits S.unl)
      (Packed.toBits S.one)).run m).run = some (.ok (o, m')) → _ := fun o ho => by
    rw [S.bits0, S.bits1] at ho; exact hi.casCore (.inl hph) hc ho
  have hnh : P t ≠ .holds := by rw [hph]; decide
  have hng : P t ≠ .gone := by rw [hph]; decide
  rcases cmpxchgAs_ok h with ⟨rfl, ho⟩ | ⟨b, v, rfl, ho, hd⟩
  · obtain ⟨hst, hcu, h1 | ⟨w, -, -, he, -⟩⟩ := core none ho
    · exact ⟨hst, hcu, .inl ⟨rfl, h1.2⟩⟩
    · cases he
  · obtain ⟨hst, hcu, ⟨he, -⟩ | ⟨w, hw, hw0, he, hi'⟩⟩ := core (some b) ho
    · cases he
    · cases he
      have hret : ∀ p : LPh, p ≠ .holds → p ≠ .gone → L.WInv (upd P t p) m' := fun p hp hpg => by
        have := hi'.queue (c := m'.current) (ws := m'.waiters) (wk := m'.woken) hnh hng hp hpg
          (fq_keep hi' (by rw [hph]; decide) (by rw [hph]; decide))
          (wit_keep hi' hnh hp fun h => by rw [hph] at h; cases h)
        cases m'; exact this
      obtain ⟨v', hv', hcase⟩ := S.dec hS hw
      have := decode_eq hd hv'
      subst this
      refine ⟨hst, hcu, .inr ?_⟩
      rcases hcase with ⟨rfl, -⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd rfl hw0
      · exact .inl ⟨rfl, hret _ (by decide) (by decide)⟩
      · exact .inr ⟨rfl, hret _ (by decide) (by decide)⟩

/-- An RMW `op` at the word by thread `t`: it reads the newest message (a chain), whose value `w`
is the word, and writes `op.apply w v`. -/
theorem WInv.rmwAt {P : ThreadId → LPh} {m m' : Mem} {t c : Nat} {op : RmwOp} {ord : AtomicOrder}
    {v b : BitVec 32} (hi : L.WInv P m) (hc : m.current = t) (ht : t < m.threads.size)
    (h : ((atomicRmwAt c op false ord 4 L.ptr v).run m).run = some (.ok (b, m'))) :
    ∃ m₁ li l w, L.Loc m₁ li l ∧ L.WInv P m₁ ∧ L.Step t m m₁ ∧ m₁.current = t ∧
      m₁.blocks = m.blocks ∧ L.Val w ∧ b = BitVec.ofNat 32 w ∧ L.U32 m₁ (BitVec.ofNat 32 w) ∧
      L.Rec m₁ t ∧
      m' = rmwM m₁ li (l.msgs.size - 1) ord (l.msgs[l.msgs.size - 1]!) (op.apply false b v) := by
  obtain ⟨b0, blk, off, li, m₁, pos, hacc, -, hl, hpos, hold, hm'⟩ := atomicRmwAt_ok h
  obtain ⟨rfl, rfl, l, hl', hi₁, hst₁, hcu₁, -, hb₁, hl0, hrec⟩ := hi.prep hc ht hacc hl
  obtain ⟨-, h0, hch, -, -⟩ := hi₁.loc.ok li l hl'
  have hpl := rmw_chain_pos (m := m₁) (li := li) (by rw [hl0]; exact h0) (by rw [hl0]; exact hch) hpos
  rw [hl0] at hpl hold hm'
  rw [hpl] at hold hm'
  obtain ⟨w, hw, rfl, hU⟩ := hi₁.msgVal hl' (by omega) hold
  exact ⟨m₁, li, l, w, hl', hi₁, hst₁, hcu₁, hb₁, hw, rfl, hU rfl, hrec, hm'⟩

/-- An `xchg` at the word by thread `t`. -/
theorem WInv.xchgAt {P : ThreadId → LPh} {m m' : Mem} {t c : Nat} {ord : AtomicOrder}
    {v b : BitVec 32} (hi : L.WInv P m) (hc : m.current = t) (ht : t < m.threads.size)
    (h : ((atomicRmwAt c .xchg false ord 4 L.ptr v).run m).run = some (.ok (b, m'))) :
    ∃ m₁ li l w, L.Loc m₁ li l ∧ L.WInv P m₁ ∧ L.Step t m m₁ ∧ m₁.current = t ∧
      m₁.blocks = m.blocks ∧ L.Val w ∧ b = BitVec.ofNat 32 w ∧ L.U32 m₁ (BitVec.ofNat 32 w) ∧
      L.Rec m₁ t ∧ m' = rmwM m₁ li (l.msgs.size - 1) ord (l.msgs[l.msgs.size - 1]!) v := by
  obtain ⟨m₁, li, l, w, h1, h2, h3, h4, h5, h6, h7, h8, h9, hm'⟩ := hi.rmwAt hc ht h
  exact ⟨m₁, li, l, w, h1, h2, h3, h4, h5, h6, h7, h8, h9, by simpa only [RmwOp.apply] using hm'⟩

/-- `lock`'s loop, `xchg(contended)` with an acquire, by thread `t` at `spin`: if the word was `0`,
`t` holds the lock; else it goes to the futex wait. -/
theorem WInv.xchgLock {P : ThreadId → LPh} {m m' : Mem} {t c : Nat} {α : Type} [Packed α 32]
    (S : States α) (hS : S.c = L.c) {r : α} (hi : L.WInv P m) (hph : P t = .spin)
    (hc : m.current = t)
    (h : ((atomicRmwAs c .xchg .acquire 4 L.ptr S.two).run m).run = some (.ok (r, m'))) :
    L.Step t m m' ∧ m'.current = t ∧
      ((r = S.unl ∧ Free P ∧ L.WInv (upd P t .holds) m' ∧ L.Acq P t m m') ∨
       (r ≠ S.unl ∧ L.WInv (upd P t .wait) m')) := by
  obtain ⟨ht, -⟩ := hi.live t (by rw [hph]; decide)
  obtain ⟨b, hb, hd⟩ := atomicRmwAs_ok h
  obtain ⟨m₁, li, l, w, hl', hi₁, hst₁, hcu₁, hb₁, hw, rfl, hU, hrec₁, hm'⟩ := hi.xchgAt hc ht hb
  rw [S.bits2, hS] at hm'
  obtain ⟨v', hv', hcase⟩ := S.dec hS hw
  have := decode_eq hd hv'
  subst this
  by_cases hw0 : w = 0
  · subst hw0
    have hF : Free P := (hi₁.free_iff L.val0 hU).mp rfl
    obtain ⟨hst₂, hcM, hi', hacq⟩ := hi₁.acquire (w' := L.c) hl' hcu₁ hrec₁ (.inr ⟨hph, rfl⟩) hF hm'
    rcases hcase with ⟨-, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact ⟨hst₁.trans hst₂ (.inl hb₁), hcM, .inl ⟨rfl, hF, hi', hacq.pre hst₁ hi.bl⟩⟩
    · cases h
    · exact absurd h.symm L.c_ne0
  · have hnF : ¬ Free P := fun hF => hw0 ((hi₁.free_iff hw hU).mpr hF)
    obtain ⟨hst₂, hcM, hi'⟩ := hi₁.contend hl' hcu₁ hrec₁ hph hnF hm'
    refine ⟨hst₁.trans hst₂ (.inl hb₁), hcM, .inr ⟨?_, hi'⟩⟩
    rcases hcase with ⟨h, -⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact absurd h hw0
    · exact S.ne01.symm
    · exact S.ne02.symm

/-- `unlock`'s `xchg(unlocked)` with a release, by the holder `t`: the word was `1` (`t` goes to
`out`) or `c` (`t` goes to the futex wake); the free lock owns what `t`'s clock owned. -/
theorem WInv.xchgUnlock {P : ThreadId → LPh} {m m' : Mem} {t c : Nat} {α : Type} [Packed α 32]
    (S : States α) (hS : S.c = L.c) {r : α} (hi : L.WInv P m) (hph : P t = .holds)
    (hc : m.current = t)
    (h : ((atomicRmwAs c .xchg .release 4 L.ptr S.unl).run m).run = some (.ok (r, m'))) :
    L.Step t m m' ∧ m'.current = t ∧ L.Before m' (m.clocks[t]!) ∧
      ((r = S.one ∧ L.WInv (upd P t .out) m' ∧ L.Rel t (upd P t .out) m m') ∨
       (r = S.two ∧ L.WInv (upd P t .wake) m' ∧ L.Rel t (upd P t .wake) m m')) := by
  obtain ⟨ht, -⟩ := hi.live t (by rw [hph]; decide)
  obtain ⟨b, hb, hd⟩ := atomicRmwAs_ok h
  obtain ⟨m₁, li, l, w, hl', hi₁, hst₁, hcu₁, hb₁, hw, rfl, hU, hrec₁, hm'⟩ := hi.xchgAt hc ht hb
  rw [S.bits0] at hm'
  have hw0 : w ≠ 0 := fun e => (hi₁.free_iff hw hU).mp e t hph
  obtain ⟨v', hv', hcase⟩ := S.dec hS hw
  have := decode_eq hd hv'
  subst this
  have hc1 : L.c ≠ 1 := fun h =>
    S.ne12 (decode_eq S.dec1 (by have := S.dec2; rwa [hS, h] at this))
  rcases hcase with ⟨h, -⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact absurd h hw0
  · obtain ⟨hst₂, hcM, hbf, hi', hrel⟩ :=
      hi₁.release (p := .out) hl' hcu₁ hrec₁ hph hU (.inl ⟨rfl, rfl, hc1⟩) hm'
    exact ⟨hst₁.trans hst₂ (.inl hb₁), hcM, before_le hbf (hst₁.clocks t),
      .inl ⟨rfl, hi', hrel.pre hst₁ hi.bl⟩⟩
  · obtain ⟨hst₂, hcM, hbf, hi', hrel⟩ :=
      hi₁.release (p := .wake) hl' hcu₁ hrec₁ hph hU (.inr ⟨rfl, rfl⟩) hm'
    exact ⟨hst₁.trans hst₂ (.inl hb₁), hcM, before_le hbf (hst₁.clocks t),
      .inr ⟨rfl, hi', hrel.pre hst₁ hi.bl⟩⟩

/-- `Thread.Mutex`'s `tryLock`, `or(1)` with an acquire, by thread `t` at `out` (the word's values
are `0`, `1`, `3`): if the word was `0`, `t` holds the lock; else it goes to `spin`. -/
theorem WInv.orLock {P : ThreadId → LPh} {m m' : Mem} {t c : Nat} {b : BitVec 32} (hc3 : L.c = 3)
    (hi : L.WInv P m) (hph : P t = .out) (hc : m.current = t)
    (h : ((atomicRmwAt c .or false .acquire 4 L.ptr (1 : BitVec 32)).run m).run =
      some (.ok (b, m'))) :
    L.Step t m m' ∧ m'.current = t ∧
      ((b = 0 ∧ Free P ∧ L.WInv (upd P t .holds) m' ∧ L.Acq P t m m') ∨
       ((b = 1 ∨ b = 3) ∧ L.WInv (upd P t .spin) m')) := by
  obtain ⟨ht, -⟩ := hi.live t (by rw [hph]; decide)
  obtain ⟨m₁, li, l, w, hl', hi₁, hst₁, hcu₁, hb₁, hw, rfl, hU, hrec₁, hm'⟩ := hi.rmwAt hc ht h
  rcases hw with rfl | rfl | hwc
  · have hF : Free P := (hi₁.free_iff L.val0 hU).mp rfl
    have he : RmwOp.or.apply false (BitVec.ofNat 32 0) (1 : BitVec 32) = BitVec.ofNat 32 1 := by
      decide
    rw [he] at hm'
    obtain ⟨hst₂, hcM, hi', hacq⟩ := hi₁.acquire (w' := 1) hl' hcu₁ hrec₁ (.inl ⟨hph, rfl⟩) hF hm'
    exact ⟨hst₁.trans hst₂ (.inl hb₁), hcM, .inl ⟨rfl, hF, hi', hacq.pre hst₁ hi.bl⟩⟩
  · have he : RmwOp.or.apply false (BitVec.ofNat 32 1) (1 : BitVec 32) = BitVec.ofNat 32 1 := by
      decide
    rw [he] at hm'
    obtain ⟨hst₂, hcM, hi'⟩ := hi₁.rmwKeep hl' hcu₁ hrec₁ (.inl hph) (.inl rfl) L.val1 hU (by decide) hm'
    exact ⟨hst₁.trans hst₂ (.inl hb₁), hcM, .inr ⟨.inl rfl, hi'⟩⟩
  · subst hwc
    have he : RmwOp.or.apply false (BitVec.ofNat 32 L.c) (1 : BitVec 32) = BitVec.ofNat 32 L.c := by
      rw [hc3]; decide
    rw [he] at hm'
    obtain ⟨hst₂, hcM, hi'⟩ := hi₁.rmwKeep hl' hcu₁ hrec₁ (.inl hph) (.inl rfl) L.valC hU L.c_ne0 hm'
    exact ⟨hst₁.trans hst₂ (.inl hb₁), hcM, .inr ⟨.inr (by rw [hc3]; rfl), hi'⟩⟩

/-- An atomic read of the word that is not an acquire, by thread `t`: no place changes. -/
theorem WInv.load {P : ThreadId → LPh} {m m' : Mem} {t c : Nat} {ord : AtomicOrder} {v : BitVec 32}
    (hi : L.WInv P m) (hc : m.current = t) (ht : t < m.threads.size) (hord : ord.isAcq = false)
    (h : ((atomicLoadAt (n := 32) c ord 4 L.ptr).run m).run = some (.ok (v, m'))) :
    L.Step t m m' ∧ m'.current = t ∧ L.WInv P m' := by
  obtain ⟨b, blk, off, li, m₁, pos, hacc, -, hl, -, -, hm'⟩ := atomicLoadAt_ok h
  obtain ⟨rfl, rfl, l, hl', hi₁, hst₁, hcu₁, -, hb₁, -⟩ := hi.prepR hc ht hacc hl
  have hmM : m' = observeM m₁ li ((m₁.atomics[li]!).msgs[pos]!).id := by
    rw [hm']; unfold loadM; rw [hord]; rfl
  rw [hmM]
  exact ⟨hst₁.trans Step.observe (.inl hb₁), by rw [← hcu₁]; rfl, hi₁.observe⟩

/-! ## No error at the word -/

/-- The access to the word, its race check and its location do not fail. -/
theorem WInv.noRace {P : ThreadId → LPh} {m : Mem} (hi : L.WInv P m) {k : AccessKind}
    (hk : k.isAtomic = true) (ht : m.current < m.threads.size)
    (hg : P m.current ≠ .gone) : NoRace m L.b L.o 4 k := by
  refine noRace_of_pos fun e he hb hel h1 h2 => ?_
  rcases hi.wfp e he (hits_of hb hel h1 h2) with ⟨ha, -⟩ | h
  · refine .inr ?_; unfold racePair; simp [ha, hk]
  · exact .inl (h _ ht hg)

theorem WInv.prepK_ok {P : ThreadId → LPh} {m : Mem} {k : AccessKind} (hk : k.isAtomic = true)
    (hi : L.WInv P m) (ht : m.current < m.threads.size) :
    ∀ e, ((Zig.locIdx L.b L.o (intSize 32)).run (m.recordAt L.b L.o (intSize 32) k)).run ≠
      some (.error e) := by
  have hir := hi.record hk ht
  intro e
  refine locIdx_noErr_of (fun i hf => ?_) (fun hn l hl hb h1 h2 => ?_) e
  · obtain ⟨hi', -, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp hf
    rw [getElem!_pos _ i hi', intSize32]
    exact (hir.loc.ok i _ ⟨hf, Array.getElem?_eq_getElem hi'⟩).1
  · have ho := hir.loc.only l hl hb (by rw [intSize32] at h2; exact h2) h1
    have := Array.findIdx?_eq_none_iff.mp hn l hl
    simp [hb, ho] at this

/-- The access of an atomic write op at the word, its race check and its location do not fail. -/
theorem WInv.prep_ok {P : ThreadId → LPh} {m : Mem} (hi : L.WInv P m)
    (ht : m.current < m.threads.size) (hg : P m.current ≠ .gone) :
    ∃ blk, m.accessW L.ptr (intSize 32) 4 = pure (L.b, blk, L.o) ∧
      NoRace m L.b L.o (intSize 32) .atomicWrite ∧
      ∀ e, ((Zig.locIdx L.b L.o (intSize 32)).run
        (m.recordAt L.b L.o (intSize 32) .atomicWrite)).run ≠ some (.error e) := by
  obtain ⟨blk, -, -, -, -, ha⟩ := hi.blk.access
  exact ⟨blk, ha, hi.noRace rfl ht hg, hi.prepK_ok rfl ht⟩

/-- The access of an atomic read of the word, its race check and its location do not fail. -/
theorem WInv.prepR_ok {P : ThreadId → LPh} {m : Mem} (hi : L.WInv P m)
    (ht : m.current < m.threads.size) (hg : P m.current ≠ .gone) :
    ∃ blk, m.access L.ptr (intSize 32) 4 = pure (L.b, blk, L.o) ∧
      NoRace m L.b L.o (intSize 32) .atomicRead ∧
      ∀ e, ((Zig.locIdx L.b L.o (intSize 32)).run
        (m.recordAt L.b L.o (intSize 32) .atomicRead)).run ≠ some (.error e) := by
  obtain ⟨blk, -, -, -, ha, -⟩ := hi.blk.access
  exact ⟨blk, ha, hi.noRace rfl ht hg, hi.prepK_ok rfl ht⟩

/-- CAS's initial read record and writable pointer check do not fail. -/
theorem WInv.prepC_ok {P : ThreadId → LPh} {m : Mem} (hi : L.WInv P m)
    (ht : m.current < m.threads.size) (hg : P m.current ≠ .gone) :
    ∃ blk, m.accessW L.ptr (intSize 32) 4 = pure (L.b, blk, L.o) ∧
      NoRace m L.b L.o (intSize 32) .atomicRead ∧
      ∀ e, ((Zig.locIdx L.b L.o (intSize 32)).run
        (m.recordAt L.b L.o (intSize 32) .atomicRead)).run ≠ some (.error e) := by
  obtain ⟨blk, -, -, -, -, ha⟩ := hi.blk.access
  exact ⟨blk, ha, hi.noRace rfl ht hg, hi.prepK_ok rfl ht⟩

/-- A successful CAS may add its write access after preparing the read. -/
theorem WInv.casWrite_noErr {P : ThreadId → LPh} {m m₁ : Mem} {li : Nat} {opts : Array Nat}
    {expected : BitVec 32} (hi : L.WInv P m) (ht : m.current < m.threads.size)
    (hg : P m.current ≠ .gone)
    (hp : ((casPrep 32 4 L.ptr expected).run m).run = some (.ok ((li, opts), m₁))) (e : Error) :
    ((casMarkWrite 32 4 L.ptr).run m₁).run ≠ some (.error e) := by
  obtain ⟨b, blk, o, ha, -, hl, -⟩ := casPrep_ok hp
  obtain ⟨rfl, rfl, _, _, hi₁, hs, hc, -⟩ := hi.prepC rfl ht ha hl
  obtain ⟨blk₁, ha₁, hnr, -⟩ := hi₁.prep_ok
    (by rw [hc, hs.threads]; exact ht) (by rw [hc]; exact hg)
  rw [casMarkWrite_run ha₁ hnr]
  simp [pure, ExceptT.pure, ExceptT.mk, ExceptT.run]

/-- A relaxed load of the word does not throw. -/
theorem WInv.load_noErr {P : ThreadId → LPh} {m : Mem} {c : Nat} {ord : AtomicOrder}
    (hi : L.WInv P m) (ht : m.current < m.threads.size) (hg : P m.current ≠ .gone)
    (hcr : c < loadCount 32 ord 4 L.ptr m ∨ loadCount 32 ord 4 L.ptr m = 0 ∧ c = 0) (e : Error) :
    ((atomicLoadAt (n := 32) c ord 4 L.ptr).run m).run ≠ some (.error e) := by
  obtain ⟨blk, hacc, hnr, hloc⟩ := hi.prepR_ok ht hg
  refine atomicLoadAt_noErr (loadPrep_noErr (by simpa using hacc) (by simpa using hnr)
    (by simpa using hloc)) (fun li opts m₁ hp => ?_) e
  obtain ⟨b, blk', o, ha, -, hl, rfl⟩ := loadPrep_ok hp
  simp only [Bool.false_eq_true, ↓reduceIte] at ha hl
  obtain ⟨rfl, rfl, l, hl', hi₁, -, -, -, -, hl0, -⟩ := hi.prepR rfl ht ha hl
  obtain ⟨-, h0, -, hval, -⟩ := hi₁.loc.ok li l hl'
  have hne := readOpts_ne (m := m₁) (li := li) (by rw [hl0]; exact h0)
  have hcnt : loadCount 32 ord 4 L.ptr m = (readOpts m₁ li false).size := by
    unfold loadCount; rw [optCount_eq hp]
  have hc : c < (readOpts m₁ li false).size := by rw [hcnt] at hcr; omega
  have hlt := readOpts_lt (Array.getElem?_eq_getElem hc)
  rw [hl0] at hlt ⊢
  obtain ⟨w, -, hw⟩ := hval _ hlt
  exact ⟨_, Array.getElem?_eq_getElem hc, _, by rw [getElem!_pos l.msgs _ hlt]; exact hw⟩

/-- A `cmpxchg` with any expected value does not throw: each option is a message, which holds
a value. -/
theorem WInv.cmpxchgAt_noErr {P : ThreadId → LPh} {m : Mem} {c : Nat} {exp new : BitVec 32}
    (hi : L.WInv P m) (ht : m.current < m.threads.size) (hg : P m.current ≠ .gone)
    (hcr : c < casCount 32 .acquire 4 L.ptr exp m ∨ casCount 32 .acquire 4 L.ptr exp m = 0 ∧ c = 0)
    (e : Error) :
    ((cmpxchgAt c .acquire .relaxed 4 L.ptr exp new).run m).run ≠ some (.error e) := by
  obtain ⟨blk, hacc, hnr, hloc⟩ := hi.prepC_ok ht hg
  have hprep : ∀ e, ((casPrep 32 4 L.ptr exp).run m).run ≠ some (.error e) :=
    casPrep_noErr hacc hnr hloc
  refine Proto.cmpxchgAt_noErr hprep ?_ (fun _ _ _ hp => hi.casWrite_noErr ht hg hp) e
  intro li opts m₁ hp
  obtain ⟨b, blk', o, ha, -, hl, rfl⟩ := casPrep_ok hp
  obtain ⟨rfl, rfl, l, hl', hi₁, -, -, -, -, hl0, -⟩ := hi.prepC rfl ht ha hl
  obtain ⟨-, hsz, -, hval, -⟩ := hi₁.loc.ok li l hl'
  have hne := casOpts_ne (e := exp) (m := m₁) (li := li) (by rw [hl0]; exact hsz)
  have hcnt : casCount 32 .acquire 4 L.ptr exp m = (casOpts m₁ li exp).size := by
    unfold casCount; rw [optCount_eq hp]
  have hc : c < (casOpts m₁ li exp).size := by rw [hcnt] at hcr; omega
  refine ⟨_, Array.getElem?_eq_getElem hc, ?_⟩
  have hpl := (casOpts_pos (Array.getElem?_eq_getElem hc)).1
  rw [hl0] at hpl
  obtain ⟨w, -, hw⟩ := hval _ hpl
  exact ⟨_, by rw [hl0, getElem!_pos l.msgs _ hpl]; exact hw⟩

/-- `lock`'s `cmpxchg` does not throw: each option is a message, which holds a state. -/
theorem WInv.cas_noErr {P : ThreadId → LPh} {m : Mem} {c : Nat} {α : Type} [Packed α 32]
    (S : States α) (hS : S.c = L.c) (hi : L.WInv P m) (ht : m.current < m.threads.size)
    (hg : P m.current ≠ .gone)
    (hcr : c < casCount 32 .acquire 4 L.ptr (Packed.toBits S.unl) m ∨
      casCount 32 .acquire 4 L.ptr (Packed.toBits S.unl) m = 0 ∧ c = 0) (e : Error) :
    ((cmpxchgAs c .acquire .relaxed 4 L.ptr S.unl S.one).run m).run ≠ some (.error e) := by
  refine cmpxchgAs_noErr (hi.cmpxchgAt_noErr ht hg hcr) ?_ e
  intro b m' hb
  obtain ⟨b0, blk', o, li, m₁, pos, old, hacc', -, hl, hpos, hold, hcase⟩ := cmpxchgAt_ok hb
  obtain ⟨rfl, rfl, l, hl', hi₁, -, -, -, -, hl0, -⟩ := hi.prepC rfl ht hacc' hl
  rcases hcase with ⟨-, h, -⟩ | ⟨-, h, -⟩
  · cases h
  · cases h
    rw [hl0] at hold
    have hpl := (casOpts_pos hpos).1
    rw [hl0] at hpl
    obtain ⟨w, hw, rfl, -⟩ := hi₁.msgVal hl' hpl hold
    obtain ⟨v, hv, -⟩ := S.dec hS hw
    exact ⟨v, hv⟩

/-- An RMW at the word does not throw: it reads the newest message, which holds a value. -/
theorem WInv.rmw_noErr {P : ThreadId → LPh} {m : Mem} {c : Nat} {op : RmwOp} {ord : AtomicOrder}
    {v : BitVec 32} (hi : L.WInv P m) (ht : m.current < m.threads.size)
    (hg : P m.current ≠ .gone)
    (hcr : c < rmwCount 32 ord 4 L.ptr m ∨ rmwCount 32 ord 4 L.ptr m = 0 ∧ c = 0) (e : Error) :
    ((atomicRmwAt c op false ord 4 L.ptr v).run m).run ≠ some (.error e) := by
  obtain ⟨blk, hacc, hnr, hloc⟩ := hi.prep_ok ht hg
  have hprep : ∀ e, ((loadPrep 32 ord 4 L.ptr true).run m).run ≠ some (.error e) :=
    loadPrep_noErr (by simpa using hacc) (by simpa using hnr) (by simpa using hloc)
  refine atomicRmwAt_noErr hprep (fun li opts m₁ hp => ?_) e
  obtain ⟨b, blk', o, ha, -, hl, rfl⟩ := loadPrep_ok hp
  simp only [↓reduceIte] at ha hl
  obtain ⟨rfl, rfl, l, hl', hi₁, -, -, -, -, hl0, -⟩ := hi.prep rfl ht ha hl
  obtain ⟨-, hsz, hch, hval, -⟩ := hi₁.loc.ok li l hl'
  have hro : readOpts m₁ li true = #[l.msgs.size - 1] := by
    rw [readOpts_chain (by rw [hl0]; exact hsz) (by rw [hl0]; exact hch), hl0]
  have hcnt : rmwCount 32 ord 4 L.ptr m = 1 := by
    unfold rmwCount; rw [optCount_eq hp, hro]; rfl
  have hc0 : c = 0 := by rw [hcnt] at hcr; omega
  subst hc0
  refine ⟨l.msgs.size - 1, by rw [hro]; rfl, ?_⟩
  obtain ⟨w, -, hw⟩ := hval (l.msgs.size - 1) (by omega)
  exact ⟨_, by rw [hl0, getElem!_pos l.msgs _ (by omega)]; exact hw⟩

/-- An `xchg` at the word does not throw: it reads the newest message, which holds a state. -/
theorem WInv.xchg_noErr {P : ThreadId → LPh} {m : Mem} {c : Nat} {ord : AtomicOrder} {α : Type}
    [Packed α 32] (S : States α) (hS : S.c = L.c) {v : α} (hi : L.WInv P m)
    (ht : m.current < m.threads.size) (hg : P m.current ≠ .gone)
    (hcr : c < rmwCount 32 ord 4 L.ptr m ∨ rmwCount 32 ord 4 L.ptr m = 0 ∧ c = 0) (e : Error) :
    ((atomicRmwAs c .xchg ord 4 L.ptr v).run m).run ≠ some (.error e) := by
  refine atomicRmwAs_noErr (hi.rmw_noErr ht hg hcr) ?_ e
  intro b m' hb
  obtain ⟨m₁, li, l, w, -, -, -, -, -, hw, rfl, -, -⟩ := hi.xchgAt rfl ht hb
  obtain ⟨v, hv, -⟩ := S.dec hS hw
  exact ⟨v, hv⟩

/-- The futex wait at the word does not throw. -/
theorem WInv.wait_ok {P : ThreadId → LPh} {m : Mem} {t : ThreadId} {e : BitVec 32}
    (hi : L.WInv P m) (ht : t < m.threads.size) (hg : P t ≠ .gone) :
    ∃ b m', ((Thread.futexWait L.ptr e).run { m with current := t }).run = some (.ok (b, m')) := by
  by_cases hw : ({ m with current := t } : Mem).woken.contains ({ m with current := t } : Mem).current = true
  · exact ⟨_, _, futexWait_run_woken hw⟩
  · obtain ⟨blk, hb, -, -, ha, -⟩ := hi.blk.access
    obtain ⟨w, -, hu, -⟩ := hi.word
    rw [u32_bytes hb] at hu
    exact ⟨_, _, futexWait_run_go (by simpa using hw) ha
      ((hi.current t).noRace (k := .atomicRead) rfl ht hg) hu⟩

/-! ### `Thread.Mutex` (0.15.2, macOS): `os_unfair_lock`, with the word `0` or `1` (`L.c = 1`) -/

/-- `os_unfair_lock_lock`'s `cmpxchg` `0 → 1` with an acquire, by thread `t` at `out` or `spin`: on
success `t` holds the lock; else it read `1` and goes to `wait`. -/
theorem WInv.casD {P : ThreadId → LPh} {m m' : Mem} {t c : Nat} {r : Option (BitVec 32)}
    (hc1 : L.c = 1) (hi : L.WInv P m) (hph : P t = .out ∨ P t = .spin) (hc : m.current = t)
    (h : ((cmpxchgAt c .acquire .relaxed 4 L.ptr (0 : BitVec 32) 1).run m).run =
      some (.ok (r, m'))) :
    L.Step t m m' ∧ m'.current = t ∧
      ((r = none ∧ Free P ∧ L.WInv (upd P t .holds) m' ∧ L.Acq P t m m') ∨
       (r = some (BitVec.ofNat 32 L.c) ∧ L.WInv (upd P t .wait) m')) := by
  have hng : P t ≠ .gone := by rcases hph with h | h <;> rw [h] <;> decide
  have hnh : P t ≠ .holds := by rcases hph with h | h <;> rw [h] <;> decide
  have hnw : P t ≠ .wait := by rcases hph with h | h <;> rw [h] <;> decide
  have hna : P t ≠ .away := by rcases hph with h | h <;> rw [h] <;> decide
  obtain ⟨hst, hcu, h1 | ⟨w, hw, hw0, rfl, hi'⟩⟩ :=
    hi.casCore (hph.elim .inl fun h => .inr ⟨h, hc1⟩) hc h
  · exact ⟨hst, hcu, .inl h1⟩
  · have hwc : w = L.c := by rcases hw with h | h | h <;> omega
    have hq := hi'.queue (c := m'.current) (ws := m'.waiters) (wk := m'.woken) (p := .wait) hnh hng
      (by decide) (by decide) (fq_keep hi' hnw hna) (wit_keep hi' hnh (by decide) fun _ => rfl)
    refine ⟨hst, hcu, .inr ⟨by rw [hwc], ?_⟩⟩
    cases m'; exact hq

/-- `os_unfair_lock_unlock`'s `xchg` of `0` with a release, by the holder `t`: `t` goes to the
futex wake. -/
theorem WInv.xchgRel {P : ThreadId → LPh} {m m' : Mem} {t c : Nat} {b : BitVec 32}
    (hc1 : L.c = 1) (hi : L.WInv P m) (hph : P t = .holds) (hc : m.current = t)
    (h : ((atomicRmwAt c .xchg false .release 4 L.ptr (0 : BitVec 32)).run m).run =
      some (.ok (b, m'))) :
    L.Step t m m' ∧ m'.current = t ∧ L.Before m' (m.clocks[t]!) ∧
      L.WInv (upd P t .wake) m' ∧ L.Rel t (upd P t .wake) m m' := by
  obtain ⟨ht, -⟩ := hi.live t (by rw [hph]; decide)
  obtain ⟨m₁, li, l, w, hl', hi₁, hst₁, hcu₁, hb₁, hw, rfl, hU, hrec₁, hm'⟩ := hi.xchgAt hc ht h
  have hw0 : w ≠ 0 := fun e => (hi₁.free_iff hw hU).mp e t hph
  have hwc : w = L.c := by rcases hw with h | h | h <;> omega
  obtain ⟨hst₂, hcM, hbf, hi', hrel⟩ :=
    hi₁.release (p := .wake) hl' hcu₁ hrec₁ hph hU (.inr ⟨hwc, rfl⟩) hm'
  exact ⟨hst₁.trans hst₂ (.inl hb₁), hcM, before_le hbf (hst₁.clocks t), hi', hrel.pre hst₁ hi.bl⟩

/-! ### `Thread.Mutex` (0.15.2) off x86: `tryLock` is a weak `cmpxchg` -/

/-- `Thread.Mutex`'s `tryLock` off x86 (0.15.2 `FutexImpl` on aarch64): a weak acquire
`cmpxchg` `0 → 1` with a relaxed failure, by thread `t` at `out`. On success `t` holds the lock;
any failure (another value, or a spurious one at `0`) is a relaxed read, and `t` goes to `spin`. -/
theorem WInv.casWeakLock {P : ThreadId → LPh} {m m' : Mem} {t c : Nat} {r : Option (BitVec 32)}
    (hi : L.WInv P m) (hph : P t = .out) (hc : m.current = t)
    (h : ((cmpxchgWeakAt c .acquire .relaxed 4 L.ptr (0 : BitVec 32) 1).run m).run =
      some (.ok (r, m'))) :
    L.Step t m m' ∧ m'.current = t ∧
      ((r = none ∧ Free P ∧ L.WInv (upd P t .holds) m' ∧ L.Acq P t m m') ∨
       ((∃ v, r = some v) ∧ L.WInv (upd P t .spin) m')) := by
  have hng : P t ≠ .gone := by rw [hph]; decide
  have hnh : P t ≠ .holds := by rw [hph]; decide
  have hnw : P t ≠ .wait := by rw [hph]; decide
  have hna : P t ≠ .away := by rw [hph]; decide
  obtain ⟨ht, -⟩ := hi.live t hng
  obtain ⟨b, blk, off, li, m₁, pos, spurious, old, hacc, -, hl, hpos, hold, hcase⟩ :=
    cmpxchgWeakAt_ok h
  obtain ⟨rfl, rfl, l, hl', hi₁, hst₁, hcu₁, -, hb₁, hl0⟩ := hi.prepC hc ht hacc hl
  obtain ⟨-, h0, hch, -, -⟩ := hi₁.loc.ok li l hl'
  rw [hl0] at hold
  rcases hcase with ⟨rfl, rfl, rfl, -, hm'⟩ | ⟨-, rfl, hm'⟩
  · -- success: a strong choice whose message holds `0`, the newest one
    obtain ⟨j, hj⟩ := weakCasOpts_strong hpos
    have hpl := cas_chain_pos (m := m₁) (li := li) (by rw [hl0]; exact hch) hj
      (by rw [hl0]; exact hold)
    rw [hl0] at hpl hm'
    rw [hpl] at hold hm'
    obtain ⟨w, -, -, hU⟩ := hi₁.msgVal hl' (by omega) hold
    have hU0 : L.U32 m₁ (BitVec.ofNat 32 0) := hU rfl
    have hF : Free P := (hi₁.free_iff L.val0 hU0).mp rfl
    have ht₁ : t < m₁.threads.size := by rw [hst₁.threads]; exact ht
    have hi₂ := hi₁.record (k := .atomicWrite) rfl (hcu₁ ▸ ht₁)
    have hstR := hi₁.recordStep hcu₁ ht₁ (k := .atomicWrite) rfl
    obtain ⟨hst₂, hcM, hi', hacq⟩ := hi₂.acquire (w' := 1) hl' hcu₁ (.inl ⟨hph, rfl⟩) hF hm'
    exact ⟨hst₁.trans (hstR.trans hst₂ (.inl rfl)) (.inl hb₁), hcM,
      .inl ⟨rfl, hF, hi', (hacq.pre hstR hi₁.bl).pre hst₁ hi.bl⟩⟩
  · -- failure: a relaxed read
    have hmM : m' = observeM m₁ li ((m₁.atomics[li]!).msgs[pos]!).id := by
      rw [hm']; unfold loadM; rfl
    have hi' : L.WInv P m' := by rw [hmM]; exact hi₁.observe
    have hq := hi'.queue (c := m'.current) (ws := m'.waiters) (wk := m'.woken) (p := .spin) hnh hng
      (by decide) (by decide) (fq_keep hi' hnw hna) (wit_keep hi' hnh (by decide) fun _ => rfl)
    refine ⟨hst₁.trans (by rw [hmM]; exact Step.observe) (.inl hb₁), by rw [hmM, ← hcu₁]; rfl,
      .inr ⟨⟨_, rfl⟩, ?_⟩⟩
    cases m'; exact hq

/-- `tryLock`'s weak `cmpxchg` does not throw. -/
theorem WInv.casWeakLock_noErr {P : ThreadId → LPh} {m : Mem} {c : Nat} (hi : L.WInv P m)
    (ht : m.current < m.threads.size) (hg : P m.current ≠ .gone)
    (hcr : c < weakCasCount 32 .acquire 4 L.ptr (0 : BitVec 32) m ∨
      weakCasCount 32 .acquire 4 L.ptr (0 : BitVec 32) m = 0 ∧ c = 0) (e : Error) :
    ((cmpxchgWeakAt c .acquire .relaxed 4 L.ptr (0 : BitVec 32) 1).run m).run ≠
      some (.error e) := by
  obtain ⟨blk, hacc, hnr, hloc⟩ := hi.prepC_ok ht hg
  refine cmpxchgWeakAt_noErr (weakCasPrep_noErr (casPrep_noErr hacc hnr hloc))
    (fun li opts m₁ hp => ?_) (fun li opts m₁ hp e he => ?_) e
  · obtain ⟨b, blk', o, ha, -, hl, rfl⟩ := weakCasPrep_ok hp
    obtain ⟨rfl, rfl, l, hl', hi₁, -, -, -, -, hl0⟩ := hi.prepC rfl ht ha hl
    obtain ⟨-, hsz, -, hval, -⟩ := hi₁.loc.ok li l hl'
    have hne := casOpts_ne (e := (0 : BitVec 32)) (m := m₁) (li := li) (by rw [hl0]; exact hsz)
    have hcnt := weakOptCount_eq (succ := .acquire) hp
    have hsz' : 0 < (weakCasOpts m₁ li (0 : BitVec 32) (casOpts m₁ li (0 : BitVec 32))).size := by
      simp only [weakCasOpts_eq, Array.size_append, Array.size_map]
      omega
    have hc : c < (weakCasOpts m₁ li (0 : BitVec 32) (casOpts m₁ li (0 : BitVec 32))).size := by
      rw [hcnt] at hcr; omega
    have hchoice := Array.getElem?_eq_getElem hc
    obtain ⟨j, hread⟩ := weakCasOpts_read hchoice
    have hpl := readOpts_lt hread
    rw [hl0] at hpl
    obtain ⟨w, -, hw⟩ := hval _ hpl
    exact ⟨_, _, hchoice, _, by rw [hl0, getElem!_pos l.msgs _ hpl]; exact hw⟩
  · obtain ⟨b, blk', o, ha, -, hl, -⟩ := weakCasPrep_ok hp
    obtain ⟨rfl, rfl, _, _, hi₁, hs, hc, -⟩ := hi.prepC rfl ht ha hl
    obtain ⟨blk₁, ha₁, hnr₁, -⟩ := hi₁.prep_ok
      (by rw [hc, hs.threads]; exact ht) (by rw [hc]; exact hg)
    rw [casMarkWrite_run ha₁ hnr₁] at he
    simp [pure, ExceptT.pure, ExceptT.mk, ExceptT.run] at he

/-- The owner check of an unlock (`Thread.mutexOwnerCheck`) at the word `p`: it passes and changes
nothing if the current thread holds the word (`ALoc.holder`). -/
theorem mutexOwnerCheck_ok {m : Mem} {p : Ptr} {b o i : Nat} {blk : Block} {l : ALoc}
    (ha : m.access p 4 4 = pure (b, blk, o))
    (hl : m.atomics.findIdx? (fun l => l.block == b && l.off == o) = some i ∧ m.atomics[i]? = some l)
    (hh : l.holder = some m.current) :
    ((Thread.mutexOwnerCheck p).run m).run = some (.ok ((), m)) := by
  have hheld : m.mutexHeld b o = true := by
    unfold Mem.mutexHeld; rw [hl.1]; simp [hl.2, hh]
  unfold Thread.mutexOwnerCheck
  simp [ha, hheld, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    pure, StateT.pure, ExceptT.bind, ExceptT.mk, ExceptT.pure, ExceptT.bindCont, ExceptT.run,
    liftM, monadLift, MonadLift.monadLift, StateT.lift]

/-- The owner check of an unlock by the holder `t`, the current thread. -/
theorem WInv.ownerCheck {P : ThreadId → LPh} {m : Mem} {t : ThreadId}
    (hi : L.WInv P m) (hph : P t = .holds) (hc : m.current = t) :
    ((Thread.mutexOwnerCheck L.ptr).run m).run = some (.ok ((), m)) := by
  obtain ⟨blk, -, -, -, ha, -⟩ := hi.blk.access
  obtain ⟨i, l, hl, hwr⟩ := hi.owner t hph
  exact mutexOwnerCheck_ok ha hl (by rw [hwr, hc])

end LockWord

end Full
end Zig
