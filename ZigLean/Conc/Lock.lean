import ZigLean.Conc.Csl

/-!
# A lock that owns a resource

A lock (`Io.Mutex`, translated from Zig 0.16.0's std code; the futex under it is the model)
protects a resource: a part of the heap that the lock owns while it is free. `lock` gives the
resource to the thread that takes the lock, `unlock` gives it back. This file is the part of a
protocol (`ZigLean/Conc/Logic.lean`) for one lock, proved once for every protocol that has it:

- **The lock** (`Lock`). The mutex word: 4 bytes at offset `o` of block `b`; the resource `R`.
  The protocol's ghost value tells for each thread where it is in the lock's code (`LPh`), its
  part of the heap (`part`), and the resource while it holds the lock (`held`). A thread owns
  `part ∪ held` (`Lock.own`; a joined thread owns nothing).
- **The invariant** (`Lock.Inv`). The threads' parts (`Owned`). The word is `0` if no thread holds
  the lock, else `1` or `2`; at most one thread holds it. The word's atomic location is an RMW
  chain, and no other location overlaps the word; no part has a byte of the word. The free lock
  owns a heap with `R` (`Lock.Owns`): each access to it happened before every thread, or before
  the release clock of the newest message of the word. Each thread in the futex queue waits at the
  word; if the queue is not empty, a thread that is not asleep is in the lock's code and will
  take the lock or wake a waiter (`wit`), so there is no deadlock.
- **A protocol with the lock** (`Lock.Fits`): its invariant is `Lock.Inv` and the rest `U`; a
  step of the lock's code (`Lock.Step`: only the word, the futex queue and the thread's clock
  change) keeps `U`; a thread that ended or waits at a join is out of the lock's code.
- **Steps outside the lock's code**: a step of a thread on its own part (`Inv.stepIn`), a spawn
  (`Inv.fork`), a join (`Inv.join`), the start of the lock (`Inv.make`) and its end, when one
  thread is above all others (`Inv.take`).

The lock's code (`lock`, `unlock`) is in `ZigLean/Conc/LockRules.lean`.
-/

namespace Zig
namespace Conc

open Assn Proto

/-- Where a thread is in the code of a lock (`Io.Mutex`). -/
inductive LPh where
  /-- The thread has not started, or it has ended. -/
  | gone
  /-- Not in the lock's code, or at `lock`'s first try (`cmpxchg`). -/
  | out
  /-- In `lock`'s loop, before its `xchg`. -/
  | spin
  /-- At a futex wait of `lock`. -/
  | wait
  /-- It holds the lock. -/
  | holds
  /-- At the futex wake of `unlock`. -/
  | wake
  deriving DecidableEq

/-- In the lock's code, after `lock`'s first try: the thread will take the lock or wake a
waiter. -/
def LPh.busy : LPh → Bool
  | .spin | .wait | .holds | .wake => true
  | _ => false

/-- The clock `c` happened before every thread. -/
def AllLe (m : Mem) (c : VClock) : Prop :=
  ∀ u < m.threads.size, VClock.le c (m.clocks[u]!) = true

/-- The clock `c` happened before a thread. -/
def SomeLe (m : Mem) (c : VClock) : Prop :=
  ∃ u < m.threads.size, VClock.le c (m.clocks[u]!) = true

/-- A lock (module doc). -/
structure Lock (γ : Type) where
  /-- The block of the word. -/
  b : BlockId
  /-- The offset of the word in its block. -/
  o : Nat
  /-- The resource, with the ghost values of all threads. -/
  R : (ThreadId → γ) → Assn
  /-- Where the thread is in the lock's code. -/
  ph : γ → LPh
  /-- The thread's part of the heap, without the resource. -/
  part : γ → Heap
  /-- The resource, while the thread holds the lock. -/
  held : γ → Heap
  /-- `g` with the place `p` and the resource `h`. -/
  set : γ → LPh → Heap → γ
  ph_set : ∀ g p h, ph (set g p h) = p
  part_set : ∀ g p h, part (set g p h) = part g
  held_set : ∀ g p h, held (set g p h) = h
  set_self : ∀ g, set g (ph g) (held g) = g
  set_set : ∀ g p h p' h', set (set g p h) p' h' = set g p' h'
  /-- The resource does not read where a thread is in the lock's code. -/
  R_set : ∀ G t p h hL, R (upd G t (set (G t) p h)) hL ↔ R G hL

/-- A thread's ghost value for a lock: its place, its part of the heap, the resource it holds. -/
structure LG where
  ph : LPh := .gone
  part : Heap := Heap.empty
  held : Heap := Heap.empty

/-- A lock whose ghost value is `LG × X`: `X` is the rest of the protocol's ghost value. The
resource reads only `X`. -/
def Lock.prod {X : Type} (b o : Nat) (R : (ThreadId → X) → Assn) : Lock (LG × X) where
  b := b
  o := o
  R G := R fun u => (G u).2
  ph g := g.1.ph
  part g := g.1.part
  held g := g.1.held
  set g p h := ({ g.1 with ph := p, held := h }, g.2)
  ph_set _ _ _ := rfl
  part_set _ _ _ := rfl
  held_set _ _ _ := rfl
  set_self _ := rfl
  set_set _ _ _ _ _ := rfl
  R_set G t p h hL := by
    have : (fun u => (upd G t ({ (G t).1 with ph := p, held := h }, (G t).2) u).2) =
        fun u => (G u).2 := by
      funext u; unfold upd; split
      · rename_i e; subst e; rfl
      · rfl
    simp only [this]

namespace Lock

variable {γ : Type} (L : Lock γ)

/-- The address of the word. -/
def ptr : Ptr := ⟨some L.b, (L.o : Int)⟩

/-- The word holds `v`. -/
def U32 (m : Mem) (v : BitVec 32) : Prop :=
  (intOfBytes 32 (curBytes m L.b L.o 4)).run = some (.ok v)

/-- `h` has no byte of the word. -/
def Off (h : Heap) : Prop := ∀ x, L.o ≤ x → x < L.o + 4 → h (L.b, x) = none

/-- Thread `u`'s part of the heap, with the resource while it holds the lock; a joined thread
owns nothing. -/
def own (G : ThreadId → γ) (m : Mem) (u : ThreadId) : Heap :=
  if joinedB m u then Heap.empty else L.part (G u) ∪ L.held (G u)

/-- The word's atomic location is location `i`, `l`. -/
def Loc (m : Mem) (i : Nat) (l : ALoc) : Prop :=
  m.atomics.findIdx? (fun l => l.block == L.b && l.off == L.o) = some i ∧ m.atomics[i]? = some l

/-- The word's atomic location: no other location overlaps the word; the location is an RMW
chain of 4-byte messages that hold `0`, `1` or `2`, and its newest message has the word's
bytes. -/
structure LocOk (m : Mem) : Prop where
  only : ∀ l ∈ m.atomics, l.block = L.b → l.off < L.o + 4 → L.o < l.off + l.len → l.off = L.o
  ok : ∀ i l, L.Loc m i l → l.len = 4 ∧ 0 < l.msgs.size ∧ l.Chain ∧
    (∀ j (h : j < l.msgs.size), ∃ w < 3,
      (intOfBytes 32 l.msgs[j].bytes).run = some (.ok (BitVec.ofNat 32 w))) ∧
    ALoc.lastBytes l = curBytes m L.b L.o 4

/-- The free lock owns `h`: each access to it (or to a block that does not exist yet) happened
before every thread, or before the release clock of the newest message of the word. -/
def Owns (m : Mem) (h : Heap) : Prop :=
  ∀ e ∈ m.footprint, (e.Touches h ∨ m.blocks.size ≤ e.block) →
    AllLe m e.clock ∨ ∃ i l, L.Loc m i l ∧ VClock.le e.clock (l.msgs.back!).relClock = true

/-- The access `e` touches a byte of the word (`FootprintEntry.Touches`). -/
def Hits (e : FootprintEntry) : Prop :=
  e.block = L.b ∧ ∃ x, e.off ≤ x ∧ (x < e.off + e.len ∨ x = e.off) ∧ L.o ≤ x ∧ x < L.o + 4

/-- No thread holds the lock. -/
def Free (G : ThreadId → γ) : Prop := ∀ u, L.ph (G u) ≠ .holds

/-- The invariant of the lock (module doc). -/
structure Inv (G : ThreadId → γ) (m : Mem) : Prop where
  own : Owned (L.own G m) m
  pdisj : ∀ u, Heap.Disjoint (L.part (G u)) (L.held (G u))
  idle : ∀ u, L.ph (G u) ≠ .holds → L.held (G u) = Heap.empty
  live : ∀ u, L.ph (G u) ≠ .gone → u < m.threads.size ∧ joinedB m u = false
  blk : ∃ blk, m.blocks[L.b]? = some blk ∧ blk.live = true ∧ L.o + 4 ≤ blk.bytes.size ∧
    (blk.addr + L.o) % 4 = 0 ∧ blk.kind ≠ .constGlobal
  word : ∃ w < 3, L.U32 m (BitVec.ofNat 32 w) ∧ (w = 0 ↔ L.Free G)
  one : ∀ u v, L.ph (G u) = .holds → L.ph (G v) = .holds → u = v
  loc : L.LocOk m
  off : ∀ u, L.Off (L.own G m u)
  /-- An access to the word is atomic, or happened before every thread. -/
  wfp : ∀ e ∈ m.footprint, L.Hits e →
    (e.kind.isAtomic = true ∧ SomeLe m e.clock) ∨ AllLe m e.clock
  /-- The release clock of the newest message happened before a thread, and before the holder. -/
  rel : ∀ i l, L.Loc m i l → SomeLe m (l.msgs.back!).relClock ∧
    ∀ u, L.ph (G u) = .holds → VClock.le (l.msgs.back!).relClock (m.clocks[u]!) = true
  free : L.Free G → ∃ hL, L.R G hL ∧ hL.Sub m.heap ∧ (∀ u, Heap.Disjoint hL (L.own G m u)) ∧
    L.Off hL ∧ L.Owns m hL
  /-- The holder's resource. -/
  res : ∀ u, L.ph (G u) = .holds → L.R G (L.held (G u))
  fq : ∀ w ∈ m.waiters, w.2 = L.ptr ∧ L.ph (G w.1) = .wait
  wit : 0 < m.waiters.size → ∃ v, v < m.threads.size ∧ m.waiters.any (·.1 == v) = false ∧
    (L.ph (G v)).busy = true ∧ (L.ph (G v) = .holds → L.U32 m 2)

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

/-- A protocol with the lock `L` (module doc): its invariant is `Lock.Inv` and `U`. -/
structure Fits {Tgt : Type} (P : Proto Tgt γ) (U : (ThreadId → γ) → Mem → Prop) : Prop where
  inv : ∀ G m, P.inv G m ↔ L.Inv G m ∧ U G m
  fin : ∀ g, P.fin g → L.ph g = .gone
  joins : ∀ g, P.joins g → L.ph g = .out
  /-- A step of a thread in the lock's code keeps `U`. -/
  stable : ∀ G m m' t p h, L.ph (G t) ≠ .gone → U G m → L.Step t m m' →
    U (upd G t (L.set (G t) p h)) m'

variable {L}

/-! ## Basic facts -/

theorem ph_upd {G : ThreadId → γ} {t u : ThreadId} {g : γ} :
    L.ph (upd G t g u) = if u = t then L.ph g else L.ph (G u) := by
  unfold upd; split <;> rfl

theorem allLe_mono {m m' : Mem} {c : VClock} (ht : m'.threads = m.threads)
    (hcl : ∀ u < m.threads.size, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (h : AllLe m c) : AllLe m' c := fun u hu =>
  VClock.le_trans (h u (ht ▸ hu)) (hcl u (ht ▸ hu))

theorem someLe_mono {m m' : Mem} {c : VClock} (ht : m'.threads = m.threads)
    (hcl : ∀ u < m.threads.size, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (h : SomeLe m c) : SomeLe m' c := by
  obtain ⟨u, hu, hle⟩ := h
  exact ⟨u, ht ▸ hu, VClock.le_trans hle (hcl u hu)⟩

theorem Step.refl (t : ThreadId) (m : Mem) : L.Step t m m :=
  ⟨rfl, fun e he => .inl he, rfl, rfl, fun _ _ => rfl, VClock.le_refl _, rfl, .inl rfl⟩

/-- A step that keeps the threads, the groups, the blocks, the clocks and the footprint. -/
theorem Step.same {t : ThreadId} {m m' : Mem} (ht : m'.threads = m.threads)
    (hg : m'.groups = m.groups) (hb : m'.blocks = m.blocks) (hc : m'.clocks = m.clocks)
    (hf : m'.footprint = m.footprint) : L.Step t m m' :=
  ⟨ht, fun e he => .inl (hf ▸ he), hg, by rw [hc], fun _ _ => by rw [hc],
    by rw [hc]; exact VClock.le_refl _, by rw [hb], .inl hb⟩

/-- The same memory, but `current`, `seen`, `nextMsg` and `woken`. -/
theorem Inv.same {G : ThreadId → γ} {m : Mem} (hi : L.Inv G m) (c : ThreadId)
    (s : Array (ThreadId × Nat × Nat)) (k : Nat) (w : Array ThreadId) :
    L.Inv G { m with current := c, seen := s, nextMsg := k, woken := w } :=
  ⟨⟨hi.own.sub, hi.own.disj, hi.own.owns, hi.own.outside, hi.own.csize⟩, hi.pdisj, hi.idle,
    hi.live, hi.blk, hi.word, hi.one, ⟨hi.loc.only, hi.loc.ok⟩, hi.off, hi.wfp, hi.rel, hi.free,
    hi.res, hi.fq, hi.wit⟩

/-- The same memory, but the groups' tasks. -/
theorem Inv.groups {G : ThreadId → γ} {m : Mem} (hi : L.Inv G m) (gs : Array (Ptr × ThreadId)) :
    L.Inv G { m with groups := gs } :=
  ⟨⟨hi.own.sub, hi.own.disj, hi.own.owns, hi.own.outside, hi.own.csize⟩, hi.pdisj, hi.idle,
    hi.live, hi.blk, hi.word, hi.one, ⟨hi.loc.only, hi.loc.ok⟩, hi.off, hi.wfp, hi.rel, hi.free,
    hi.res, hi.fq, hi.wit⟩

theorem Inv.current {G : ThreadId → γ} {m : Mem} (hi : L.Inv G m) (t : ThreadId) :
    L.Inv G { m with current := t } :=
  hi.same t m.seen m.nextMsg m.woken

/-- The same ghost value for `t` (`set_self`). -/
theorem upd_set_self (G : ThreadId → γ) (t : ThreadId) :
    upd G t (L.set (G t) (L.ph (G t)) (L.held (G t))) = G := by
  rw [L.set_self]; funext u; unfold upd; split <;> simp_all

theorem joinedB_congr {m m' : Mem} (h : m'.threads = m.threads) : joinedB m' = joinedB m := by
  funext u; unfold joinedB; rw [h]

theorem own_upd {G : ThreadId → γ} {m m' : Mem} {t : ThreadId} {g : γ}
    (hj : joinedB m' = joinedB m) (hjt : joinedB m t = false) :
    L.own (upd G t g) m' = upd (L.own G m) t (L.part g ∪ L.held g) := by
  funext u
  unfold Lock.own; rw [hj]
  by_cases hu : u = t
  · subst hu; simp [hjt, upd]
  · simp only [upd, hu, ↓reduceIte]

/-! ## The word in the heap -/

/-- Each byte of the word is in the heap. -/
theorem Inv.wordIn {G : ThreadId → γ} {m : Mem} (hi : L.Inv G m) {x : Nat} (h1 : L.o ≤ x)
    (h2 : x < L.o + 4) : m.heap (L.b, x) ≠ none := by
  obtain ⟨blk, hb, hl, hs, -⟩ := hi.blk
  simp only [Mem.heap, hb]
  rw [dite_eq_left_of_eq_true (eq_true ⟨hl, by omega⟩)]
  simp

/-- The rest of the heap outside a thread's part has each byte of the word. -/
theorem Inv.wordRest {G : ThreadId → γ} {m : Mem} (hi : L.Inv G m) (u : ThreadId) {x : Nat}
    (h1 : L.o ≤ x) (h2 : x < L.o + 4) : m.heap.diff (L.own G m u) (L.b, x) ≠ none := by
  simp only [Heap.diff, hi.off u x h1 h2, ↓reduceIte]
  exact hi.wordIn h1 h2

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

/-- An access that overlaps the word hits it. -/
theorem hits_of {e : FootprintEntry} (hb : e.block = L.b) (h1 : L.o < e.off + e.len)
    (h2 : e.off < L.o + 4) : L.Hits e := by
  by_cases ho : e.off ≤ L.o
  · exact ⟨hb, L.o, ho, .inl h1, Nat.le_refl _, by omega⟩
  · exact ⟨hb, e.off, Nat.le_refl _, .inr rfl, by omega, h2⟩

/-- An access that hits the word touches a heap with the word's bytes. -/
theorem touches_word {e : FootprintEntry} {h : Heap} (he : L.Hits e)
    (hw : ∀ x, L.o ≤ x → x < L.o + 4 → h (L.b, x) ≠ none) : e.Touches h := by
  obtain ⟨hb, x, h1, h2, h3, h4⟩ := he
  exact ⟨x, h1, h2, by rw [hb]; exact hw x h3 h4⟩

/-- The same cells at the word: the same facts of its block, and the same word. -/
theorem word_congr {m m' : Mem}
    (hw : ∀ x, L.o ≤ x → x < L.o + 4 → m'.heap (L.b, x) = m.heap (L.b, x))
    (hb : ∃ blk, m.blocks[L.b]? = some blk ∧ blk.live = true ∧ L.o + 4 ≤ blk.bytes.size ∧
      (blk.addr + L.o) % 4 = 0 ∧ blk.kind ≠ .constGlobal) :
    (∃ blk, m'.blocks[L.b]? = some blk ∧ blk.live = true ∧ L.o + 4 ≤ blk.bytes.size ∧
      (blk.addr + L.o) % 4 = 0 ∧ blk.kind ≠ .constGlobal) ∧
      curBytes m' L.b L.o 4 = curBytes m L.b L.o 4 := by
  obtain ⟨blk, hblk, hl, hs, ha, hk⟩ := hb
  have hc : m.heap (L.b, L.o) =
      some ⟨blk.bytes[L.o]'(by omega), blk.addr, blk.bytes.size, blk.kind⟩ := by
    simp only [Mem.heap, hblk]; rw [dite_eq_left_of_eq_true (eq_true ⟨hl, by omega⟩)]
  have hc' := hw L.o (Nat.le_refl _) (by omega)
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
  have := hw (L.o + i) (by omega) (by omega)
  simp only [Mem.heap, hblk, hblk'] at this
  rw [dite_eq_left_of_eq_true (eq_true ⟨hl', by omega⟩), dite_eq_left_of_eq_true (eq_true ⟨hl, by omega⟩)] at this
  simp only [Option.some.injEq, Cell.mk.injEq] at this
  exact this.1

/-! ## A step of a thread on its own part -/

/-- A step of thread `t` on its own part (`WP.liftMem_owned`), with the new ghost value `g`: the
same place in the lock's code, and the new part `part g ∪ held g`. -/
theorem Inv.stepIn {G : ThreadId → γ} {m m' : Mem} {t : ThreadId} {g : γ} (hi : L.Inv G m)
    (hc : m.current = t) (hjt : joinedB m t = false)
    (ho' : Owned (upd (L.own G m) t (L.part g ∪ L.held g)) m')
    (hs : StepIn (m.heap.diff (L.own G m t)) m m')
    (hm' : m'.heap = (L.part g ∪ L.held g) ∪ m.heap.diff (L.own G m t))
    (hd : Heap.Disjoint (L.part g ∪ L.held g) (m.heap.diff (L.own G m t)))
    (hph : L.ph g = L.ph (G t)) (hpd : Heap.Disjoint (L.part g) (L.held g))
    (hidle : L.ph g ≠ .holds → L.held g = Heap.empty)
    (hRk : L.ph (G t) ≠ .holds → ∀ hL, L.R G hL → L.R (upd G t g) hL)
    (hres : L.ph g = .holds → L.R (upd G t g) (L.held g)) :
    L.Inv (upd G t g) m' := by
  have hjb : joinedB m' = joinedB m := joinedB_congr hs.threads
  have hown := own_upd (L := L) (G := G) (g := g) hjb hjt
  have hphu : ∀ u, L.ph (upd G t g u) = L.ph (G u) := fun u => by
    unfold upd; split <;> simp_all
  have hwF : ∀ x, L.o ≤ x → x < L.o + 4 → m.heap.diff (L.own G m t) (L.b, x) ≠ none :=
    fun x h1 h2 => hi.wordRest t h1 h2
  have hheap : ∀ x, L.o ≤ x → x < L.o + 4 → m'.heap (L.b, x) = m.heap (L.b, x) := by
    intro x h1 h2
    rw [hm', Heap.union_of_right ((hd (L.b, x)).resolve_right (hwF x h1 h2))]
    simp [Heap.diff, hi.off t x h1 h2]
  obtain ⟨hblk', hcur⟩ := word_congr hheap hi.blk
  have hcl : ∀ u < m.threads.size, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true := by
    intro u _
    by_cases hu : u = m.current
    · subst hu; exact hs.mine
    · rw [hs.others u hu]; exact VClock.le_refl _
  have hU32 : ∀ v, L.U32 m' v ↔ L.U32 m v := fun v => by unfold Lock.U32; rw [hcur]
  have hloc : ∀ i l, L.Loc m' i l ↔ L.Loc m i l := fun i l => by unfold Lock.Loc; rw [hs.atomics]
  have hfree : L.Free (upd G t g) ↔ L.Free G := by
    unfold Lock.Free; exact forall_congr' fun u => by rw [hphu]
  have hrest : ∀ hL : Heap, hL.Sub m.heap → Heap.Disjoint hL (L.own G m t) →
      hL.Sub (m.heap.diff (L.own G m t)) := fun hL h1 h2 => Heap.sub_diff h1 h2
  refine ⟨hown ▸ ho', fun u => ?_, fun u hu => ?_, fun u hu => ?_, hblk', ?_,
    fun u v hu hv => ?_, ⟨fun l hl => hi.loc.only l (hs.atomics ▸ hl), fun i l hl => ?_⟩,
    fun u => ?_, fun e he hh => ?_, fun i l hl => ?_, fun hF => ?_, fun u hu => ?_,
    fun w hw => ?_, fun hp => ?_⟩
  · by_cases hu : u = t
    · subst hu; rw [upd_self]; exact hpd
    · rw [upd_ne _ _ hu]; exact hi.pdisj u
  · by_cases hu' : u = t
    · subst hu'; rw [upd_self] at hu ⊢; exact hidle hu
    · rw [upd_ne _ _ hu'] at hu ⊢; exact hi.idle u hu
  · rw [hphu] at hu; rw [hs.threads, hjb]; exact hi.live u hu
  · obtain ⟨w, hw, hu, hz⟩ := hi.word
    exact ⟨w, hw, (hU32 _).mpr hu, hz.trans hfree.symm⟩
  · rw [hphu] at hu hv; exact hi.one u v hu hv
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hi.loc.ok i l ((hloc i l).mp hl)
    exact ⟨h1, h2, h3, h4, by rw [h5, hcur]⟩
  · rw [hown]
    by_cases hu : u = t
    · subst hu; rw [upd_self]; exact off_of_disj hd hwF
    · rw [upd_ne _ _ hu]; exact hi.off u
  · rcases hs.fp e he with he' | ⟨-, hnt, -⟩
    · rcases hi.wfp e he' hh with ⟨ha, hle⟩ | hle
      · exact .inl ⟨ha, someLe_mono hs.threads hcl hle⟩
      · exact .inr (allLe_mono hs.threads hcl hle)
    · exact absurd (touches_word hh hwF) hnt
  · obtain ⟨h1, h2⟩ := hi.rel i l ((hloc i l).mp hl)
    refine ⟨someLe_mono hs.threads hcl h1, fun u hu => ?_⟩
    rw [hphu] at hu
    exact VClock.le_trans (h2 u hu) (hcl u (hi.live u (by rw [hu]; decide)).1)
  · obtain ⟨hL, hR, hsub, hdj, hoff, how⟩ := hi.free (hfree.mp hF)
    have hsubF := hrest hL hsub (hdj t)
    refine ⟨hL, hRk (hfree.mp hF t) hL hR, ?_, fun u => ?_, hoff,
      fun e he htc => ?_⟩
    · rw [hm']; exact hsubF.trans (Heap.sub_union_right hd)
    · rw [hown]
      by_cases hu : u = t
      · subst hu; rw [upd_self]; exact (Heap.disjoint_sub hd hsubF).symm
      · rw [upd_ne _ _ hu]; exact hdj u
    · rcases hs.fp e he with he' | ⟨-, hnt, hb⟩
      · rcases how e he' (htc.imp id fun h => Nat.le_trans hs.blocks h) with h | ⟨i, l, hl, hle⟩
        · exact .inl (allLe_mono hs.threads hcl h)
        · exact .inr ⟨i, l, (hloc i l).mpr hl, hle⟩
      · rcases htc with ⟨x, hx1, hx2, hx3⟩ | hb'
        · exact absurd ⟨x, hx1, hx2, hsubF.ne hx3⟩ hnt
        · exact absurd hb' (Nat.not_le.mpr hb)
  · by_cases hut : u = t
    · subst hut; rw [upd_self] at hu ⊢; exact hres hu
    · rw [upd_ne _ _ hut] at hu ⊢
      have htn : L.ph (G t) ≠ .holds := fun h => hut (hi.one u t hu h)
      exact hRk htn _ (hi.res u hu)
  · obtain ⟨h1, h2⟩ := hi.fq w (hs.waiters ▸ hw)
    exact ⟨h1, by rw [hphu]; exact h2⟩
  · obtain ⟨v, hv, hq, h1, h2⟩ := hi.wit (hs.waiters ▸ hp)
    refine ⟨v, hs.threads ▸ hv, hs.waiters ▸ hq, by rw [hphu]; exact h1, fun hh => ?_⟩
    rw [hphu] at hh; exact (hU32 2).mpr (h2 hh)

/-- A change of thread `t`'s ghost value outside the lock's code: `t` is `out` or `gone` before
and after, keeps its part, and holds nothing. -/
theorem Inv.ghost {G : ThreadId → γ} {m : Mem} {t : ThreadId} {g : γ} (hi : L.Inv G m)
    (hph : L.ph (G t) = .out ∨ L.ph (G t) = .gone) (hg : L.ph g = .out ∨ L.ph g = .gone)
    (hpart : L.part g = L.part (G t)) (hheld : L.held g = Heap.empty)
    (hlive : L.ph g = .out → t < m.threads.size ∧ joinedB m t = false)
    (hRk : ∀ hL, L.R G hL → L.R (upd G t g) hL) : L.Inv (upd G t g) m := by
  have hnh : L.ph (G t) ≠ .holds := by rcases hph with h | h <;> rw [h] <;> decide
  have hgh : L.ph g ≠ .holds := by rcases hg with h | h <;> rw [h] <;> decide
  have hgw : L.ph g ≠ .wait := by rcases hg with h | h <;> rw [h] <;> decide
  have hgb : (L.ph g).busy = false := by rcases hg with h | h <;> rw [h] <;> rfl
  have htb : (L.ph (G t)).busy = false := by rcases hph with h | h <;> rw [h] <;> rfl
  have hown : L.own (upd G t g) m = L.own G m := by
    funext u; unfold Lock.own
    by_cases h : u = t
    · subst h; rw [upd_self, hpart, hheld, hi.idle u hnh]
    · rw [upd_ne _ _ h]
  have hphu : ∀ u, L.ph (upd G t g u) = if u = t then L.ph g else L.ph (G u) := fun u => by
    unfold upd; split <;> rfl
  have hholds : ∀ u, L.ph (upd G t g u) = .holds ↔ L.ph (G u) = .holds := by
    intro u; rw [hphu]; split
    · rename_i h; subst h; exact ⟨fun h => absurd h hgh, fun h => absurd h hnh⟩
    · exact Iff.rfl
  have hfree : L.Free (upd G t g) ↔ L.Free G := by
    unfold Lock.Free; exact forall_congr' fun u => not_congr (hholds u)
  refine ⟨hown ▸ hi.own, fun u => ?_, fun u hu => ?_, fun u hu => ?_, hi.blk, ?_,
    fun u v hu hv => hi.one u v ((hholds u).mp hu) ((hholds v).mp hv), ⟨hi.loc.only, hi.loc.ok⟩,
    fun u => hown ▸ hi.off u, hi.wfp, fun i l hl => ?_, fun hF => ?_, fun u hu => ?_,
    fun w hw => ?_, fun hp => ?_⟩
  · unfold upd; split
    · rw [hheld]; exact Heap.disjoint_empty _
    · exact hi.pdisj u
  · unfold upd; split
    · exact hheld
    · rename_i h; rw [hphu, if_neg h] at hu; exact hi.idle u hu
  · rw [hphu] at hu
    split at hu
    · rename_i h; subst h
      rcases hg with h | h
      · exact hlive h
      · exact absurd h hu
    · exact hi.live u hu
  · obtain ⟨w, hw, hu, hz⟩ := hi.word; exact ⟨w, hw, hu, hz.trans hfree.symm⟩
  · obtain ⟨h1, h2⟩ := hi.rel i l hl
    exact ⟨h1, fun u hu => h2 u ((hholds u).mp hu)⟩
  · obtain ⟨hL, hR, hsub, hdj, hoff, how⟩ := hi.free (hfree.mp hF)
    exact ⟨hL, hRk hL hR, hsub, fun u => hown ▸ hdj u, hoff, how⟩
  · have hut : u ≠ t := fun e => by
      have := (hholds u).mp hu; rw [e] at this; exact hnh this
    rw [upd_ne _ _ hut]; exact hRk _ (hi.res u ((hholds u).mp hu))
  · obtain ⟨h1, h2⟩ := hi.fq w hw
    have hwt : w.1 ≠ t := fun e => by
      rw [e] at h2; rcases hph with h | h <;> rw [h] at h2 <;> cases h2
    exact ⟨h1, by rw [upd_ne _ _ hwt]; exact h2⟩
  · obtain ⟨v, hv, hq, h1, h2⟩ := hi.wit hp
    have hvt : v ≠ t := fun e => by rw [e, htb] at h1; cases h1
    exact ⟨v, hv, hq, by rw [upd_ne _ _ hvt]; exact h1,
      fun hh => h2 (by rw [upd_ne _ _ hvt] at hh; exact hh)⟩

/-! ## Spawn and join -/

theorem fork_eq {m m' : Mem} {t c : ThreadId}
    (hf : (Thread.fork.run { m with current := t }).run = some (.ok (c, m'))) :
    c = m.threads.size ∧ m' = { m with
      current := t,
      clocks := (m.clocks.set! t (VClock.bump (m.clocks[t]!) t)).push (VClock.bump (m.clocks[t]!) t),
      threads := m.threads.push { spawner := t, joined := false } } := by
  rw [Proto.fork_run] at hf
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hf
  obtain ⟨rfl, rfl⟩ := hf
  exact ⟨rfl, rfl⟩

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

/-- A spawn by `t`, which is out of the lock's code: `t` keeps `part g₁`, the new thread gets
`part g₀` and starts out of the lock's code. -/
theorem Inv.fork {G : ThreadId → γ} {m m' : Mem} {t c : ThreadId} {g₁ g₀ : γ} (hi : L.Inv G m)
    (hout : L.ph (G t) = .out)
    (hf : (Thread.fork.run { m with current := t }).run = some (.ok (c, m')))
    (hsplit : L.part (G t) = L.part g₁ ∪ L.part g₀) (hd : Heap.Disjoint (L.part g₁) (L.part g₀))
    (h₁ : L.ph g₁ = .out) (h₁h : L.held g₁ = Heap.empty)
    (h₀ : L.ph g₀ = .out) (h₀h : L.held g₀ = Heap.empty)
    (hRk : ∀ hL, L.R G hL → L.R (upd (upd G c g₀) t g₁) hL) :
    L.Inv (upd (upd G c g₀) t g₁) m' := by
  have hcs := hi.own.csize
  obtain ⟨ht, hjt⟩ := hi.live t (by rw [hout]; decide)
  have hheld : L.held (G t) = Heap.empty := hi.idle t (by rw [hout]; decide)
  have hownt : L.own G m t = L.part g₁ ∪ L.part g₀ := by
    simp [Lock.own, hjt, hheld, hsplit]
  have ho := Owned.fork hi.own ht hownt hd hf
  have hjb := joinedB_fork hf
  obtain ⟨rfl, rfl⟩ := fork_eq hf
  have hct : m.threads.size ≠ t := fun h => by rw [h] at ht; exact Nat.lt_irrefl _ ht
  have hGc : L.ph (G m.threads.size) = .gone := by
    cases hx : L.ph (G m.threads.size) <;> first | rfl |
      exact absurd (hi.live _ (by rw [hx]; decide)).1 (Nat.lt_irrefl _)
  have hjc : joinedB m m.threads.size = false := by
    simp [joinedB, Array.getElem?_eq_none (Nat.le_refl _)]
  have hphu : ∀ u, u ≠ m.threads.size → L.ph (upd (upd G m.threads.size g₀) t g₁ u) = L.ph (G u) := by
    intro u hu; unfold upd
    by_cases h1 : u = t
    · simp [h1, h₁, hout]
    · simp [h1, hu]
  have hphc : L.ph (upd (upd G m.threads.size g₀) t g₁ m.threads.size) = .out := by
    simp [upd, hct, h₀]
  -- A thread in the lock's code or at a wait is not the new one.
  have hnc : ∀ u, L.ph (G u) ≠ .gone → u ≠ m.threads.size := fun u hu e => by
    rw [e, hGc] at hu; exact hu rfl
  have hown : L.own (upd (upd G m.threads.size g₀) t g₁) { m with
      current := t,
      clocks := (m.clocks.set! t (VClock.bump (m.clocks[t]!) t)).push (VClock.bump (m.clocks[t]!) t),
      threads := m.threads.push { spawner := t, joined := false } } =
      upd (upd (L.own G m) t (L.part g₁)) m.threads.size (L.part g₀) := by
    funext u
    unfold Lock.own; rw [hjb]
    by_cases h1 : u = t
    · subst h1; simp [upd, hjt, Ne.symm hct, h₁h]
    · by_cases h2 : u = m.threads.size
      · subst h2; simp [upd, hjc, hct, h₀h]
      · simp [upd, h1, h2, Lock.own]
  obtain ⟨hcl, hcn, hco⟩ := fork_clocks (hcs ▸ ht : t < m.clocks.size)
  have hall : ∀ {c : VClock}, AllLe m c → AllLe { m with
      current := t,
      clocks := (m.clocks.set! t (VClock.bump (m.clocks[t]!) t)).push (VClock.bump (m.clocks[t]!) t),
      threads := m.threads.push { spawner := t, joined := false } } c := by
    intro c h u hu
    simp only [Array.size_push] at hu
    by_cases hu' : u < m.threads.size
    · exact VClock.le_trans (h u hu') (hcl u (hcs ▸ hu'))
    · have : u = m.threads.size := by omega
      subst this; rw [← hcs]; exact VClock.le_trans (h t ht) hcn
  have hsome : ∀ {c : VClock}, SomeLe m c → SomeLe { m with
      current := t,
      clocks := (m.clocks.set! t (VClock.bump (m.clocks[t]!) t)).push (VClock.bump (m.clocks[t]!) t),
      threads := m.threads.push { spawner := t, joined := false } } c := by
    rintro c ⟨u, hu, hle⟩
    exact ⟨u, by simp only [Array.size_push]; exact Nat.lt_succ_of_lt hu,
      VClock.le_trans hle (hcl u (hcs ▸ hu))⟩
  have hholds : ∀ u, L.ph (upd (upd G m.threads.size g₀) t g₁ u) = .holds ↔ L.ph (G u) = .holds := by
    intro u
    by_cases hu : u = m.threads.size
    · subst hu; rw [hphc, hGc]; decide
    · rw [hphu u hu]
  have hfree : L.Free (upd (upd G m.threads.size g₀) t g₁) ↔ L.Free G := by
    unfold Lock.Free; exact forall_congr' fun u => not_congr (hholds u)
  have hs1 : (L.part g₁).Sub (L.own G m t) := by rw [hownt]; exact Heap.sub_union_left
  have hs0 : (L.part g₀).Sub (L.own G m t) := by rw [hownt]; exact Heap.sub_union_right hd
  have hparts : ∀ u, (upd (upd (L.own G m) t (L.part g₁)) m.threads.size (L.part g₀) u).Sub
      (if u = t ∨ u = m.threads.size then L.own G m t else L.own G m u) := by
    intro u; unfold upd
    by_cases h1 : u = t
    · simp [h1, hct.symm]; exact hs1
    · by_cases h2 : u = m.threads.size
      · simp [h1, h2, hct]; exact hs0
      · simp [h1, h2]; exact fun _ _ h => h
  refine ⟨hown ▸ ho, fun u => ?_, fun u hu => ?_, fun u hu => ?_, hi.blk, ?_,
    fun u v hu hv => ?_, ⟨hi.loc.only, hi.loc.ok⟩, fun u => ?_, fun e he hh => ?_,
    fun i l hl => ?_, fun hF => ?_, fun u hu => ?_, fun w hw => ?_, fun hp => ?_⟩
  · unfold upd
    by_cases h1 : u = t
    · simp only [h1, ↓reduceIte, h₁h]; exact Heap.disjoint_empty _
    · by_cases h2 : u = m.threads.size
      · simp only [h1, h2, hct, ↓reduceIte, h₀h]; exact Heap.disjoint_empty _
      · simp only [h1, h2, ↓reduceIte]; exact hi.pdisj u
  · rw [ne_eq, hholds] at hu; unfold upd
    by_cases h1 : u = t
    · simp only [h1, ↓reduceIte, h₁h]
    · by_cases h2 : u = m.threads.size
      · simp only [h1, h2, hct, ↓reduceIte, h₀h]
      · simp only [h1, h2, ↓reduceIte]; exact hi.idle u hu
  · by_cases hc : u = m.threads.size
    · subst hc
      exact ⟨by simp only [Array.size_push]; exact Nat.lt_succ_self _, by rw [hjb]; exact hjc⟩
    · rw [hphu u hc] at hu
      obtain ⟨h1, h2⟩ := hi.live u hu
      exact ⟨by simp only [Array.size_push]; exact Nat.lt_succ_of_lt h1, by rw [hjb]; exact h2⟩
  · obtain ⟨w, hw, hu, hz⟩ := hi.word; exact ⟨w, hw, hu, hz.trans hfree.symm⟩
  · exact hi.one u v ((hholds u).mp hu) ((hholds v).mp hv)
  · rw [hown]
    have hsub' := hparts u
    split at hsub'
    · exact off_sub (hi.off t) fun l hl => hsub'.ne hl
    · exact off_sub (hi.off u) fun l hl => hsub'.ne hl
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
  · obtain ⟨hL, hR, hsub, hdj, hoff, how⟩ := hi.free (hfree.mp hF)
    refine ⟨hL, hRk hL hR, hsub, fun u => ?_, hoff, fun e he htc => ?_⟩
    · rw [hown]
      have hsub' := hparts u
      split at hsub'
      · exact Heap.disjoint_sub (hdj t) hsub'
      · exact Heap.disjoint_sub (hdj u) hsub'
    · rcases how e he htc with h | ⟨i, l, hl, hle⟩
      · exact .inl (hall h)
      · exact .inr ⟨i, l, hl, hle⟩
  · rw [hholds] at hu
    have hc' : u ≠ m.threads.size := hnc u (by rw [hu]; decide)
    have hut : u ≠ t := fun e => by rw [e, hout] at hu; cases hu
    rw [show upd (upd G m.threads.size g₀) t g₁ u = G u by simp [upd, hc', hut]]
    exact hRk _ (hi.res u hu)
  · obtain ⟨h1, h2⟩ := hi.fq w hw
    refine ⟨h1, ?_⟩
    rw [hphu w.1 (hnc w.1 (by rw [h2]; decide))]; exact h2
  · obtain ⟨v, hv, hq, h1, h2⟩ := hi.wit hp
    have hvc : v ≠ m.threads.size := hnc v (fun e => by rw [e] at h1; cases h1)
    exact ⟨v, by simp only [Array.size_push]; exact Nat.lt_succ_of_lt hv, hq,
      by rw [hphu v hvc]; exact h1, fun hh => h2 (by rw [← hphu v hvc]; exact hh)⟩

/-- A join of `u` by `t`, both out of the lock's code: `t` takes `u`'s part. -/
theorem Inv.join {G : ThreadId → γ} {m m' : Mem} {t u : ThreadId} {g : γ} (hi : L.Inv G m)
    (hut : u ≠ t) (hu0 : u ≠ 0) (hout : L.ph (G t) = .out) (huo : L.ph (G u) = .gone)
    (hj : ((Thread.join u).run { m with current := t }).run = some (.ok ((), m')))
    (hg : L.part g = L.part (G t) ∪ L.own G m u) (hgo : L.ph g = .out)
    (hgh : L.held g = Heap.empty) (hRk : ∀ hL, L.R G hL → L.R (upd G t g) hL) :
    L.Inv (upd G t g) m' := by
  have hcs := hi.own.csize
  obtain ⟨ht, hjt⟩ := hi.live t (by rw [hout]; decide)
  have hheld : L.held (G t) = Heap.empty := hi.idle t (by rw [hout]; decide)
  have ho := Owned.join hi.own ht hut hj
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
  have hphu : ∀ w, L.ph (upd G t g w) = L.ph (G w) := by
    intro w; unfold upd; split
    · rename_i h; subst h; rw [hgo, hout]
    · rfl
  have hown : L.own (upd G t g) { m with
      current := t,
      clocks := m.clocks.set! t (VClock.merge (VClock.bump (m.clocks[t]!) t) (m.clocks[u]!)),
      threads := m.threads.set! u { rec with joined := true } } =
      upd (upd (L.own G m) t (L.own G m t ∪ L.own G m u)) u Heap.empty := by
    funext w
    unfold Lock.own; rw [hjb]
    by_cases h1 : w = u
    · subst h1; simp [upd]
    · by_cases h2 : w = t
      · subst h2; simp [upd, h1, hjt, hg, hgh, hheld, Lock.own]
      · simp [upd, h1, h2]
  have hcl : ∀ w : Nat, VClock.le (m.clocks[w]!) ((m.clocks.set! t (VClock.merge
      (VClock.bump (m.clocks[t]!) t) (m.clocks[u]!)))[w]!) = true := by
    intro w
    rw [Proto.getElem!_set!_ite]
    split
    · rename_i h; rw [h.1]
      exact VClock.le_trans (VClock.le_bump _ _) (VClock.le_merge_left _ _)
    · exact VClock.le_refl _
  have hco : ∀ w : Nat, w ≠ t → (m.clocks.set! t (VClock.merge (VClock.bump (m.clocks[t]!) t)
      (m.clocks[u]!)))[w]! = m.clocks[w]! := by
    intro w hw; rw [Proto.getElem!_set!_ite, if_neg (fun h => hw h.1)]
  have hsz : (m.threads.set! u { rec with joined := true }).size = m.threads.size := by simp
  have hall : ∀ {c : VClock}, AllLe m c → AllLe { m with
      current := t,
      clocks := m.clocks.set! t (VClock.merge (VClock.bump (m.clocks[t]!) t) (m.clocks[u]!)),
      threads := m.threads.set! u { rec with joined := true } } c := fun h w hw =>
    VClock.le_trans (h w (hsz ▸ hw)) (hcl w)
  have hsome : ∀ {c : VClock}, SomeLe m c → SomeLe { m with
      current := t,
      clocks := m.clocks.set! t (VClock.merge (VClock.bump (m.clocks[t]!) t) (m.clocks[u]!)),
      threads := m.threads.set! u { rec with joined := true } } c := by
    rintro c ⟨w, hw, hle⟩; exact ⟨w, by rw [hsz]; exact hw, VClock.le_trans hle (hcl w)⟩
  have hfree : L.Free (upd G t g) ↔ L.Free G := by
    unfold Lock.Free; exact forall_congr' fun w => by rw [hphu]
  have hnu : ∀ w, L.ph (G w) ≠ .gone → w ≠ u := fun w hw e => hw (by rw [e, huo])
  refine ⟨hown ▸ ho, fun w => ?_, fun w hw => ?_, fun w hw => ?_, hi.blk, ?_,
    fun v w hv hw => ?_, ⟨hi.loc.only, hi.loc.ok⟩, fun w => ?_, fun e he hh => ?_,
    fun i l hl => ?_, fun hF => ?_, fun v hv => ?_, fun w hw => ?_, fun hp => ?_⟩
  · unfold upd; split
    · rw [hgh]; exact Heap.disjoint_empty _
    · exact hi.pdisj w
  · rw [hphu] at hw; unfold upd; split
    · exact hgh
    · exact hi.idle w hw
  · rw [hphu] at hw
    obtain ⟨h1, h2⟩ := hi.live w hw
    exact ⟨by rw [hsz]; exact h1, by rw [hjb, if_neg (hnu w hw)]; exact h2⟩
  · obtain ⟨w, hw, hu, hz⟩ := hi.word; exact ⟨w, hw, hu, hz.trans hfree.symm⟩
  · rw [hphu] at hv hw; exact hi.one v w hv hw
  · rw [hown]; unfold upd
    by_cases h1 : w = u
    · simp only [h1, ↓reduceIte]; intro x _ _; rfl
    · by_cases h2 : w = t
      · simp only [h2, Ne.symm hut, ↓reduceIte]; exact off_union (hi.off t) (hi.off u)
      · simp only [h1, h2, ↓reduceIte]; exact hi.off w
  · rcases hi.wfp e he hh with ⟨ha, hle⟩ | hle
    · exact .inl ⟨ha, hsome hle⟩
    · exact .inr (hall hle)
  · obtain ⟨h1, h2⟩ := hi.rel i l hl
    refine ⟨hsome h1, fun w hw => ?_⟩
    rw [hphu] at hw
    rw [hco w (fun e => by rw [e, hout] at hw; cases hw)]; exact h2 w hw
  · obtain ⟨hL, hR, hsub, hdj, hoff, how⟩ := hi.free (hfree.mp hF)
    refine ⟨hL, hRk hL hR, hsub, fun w => ?_, hoff, fun e he htc => ?_⟩
    · rw [hown]; unfold upd
      by_cases h1 : w = u
      · simp only [h1, ↓reduceIte]; exact Heap.disjoint_empty _
      · by_cases h2 : w = t
        · simp only [h2, Ne.symm hut, ↓reduceIte]
          exact Heap.disjoint_union_right.mpr ⟨hdj t, hdj u⟩
        · simp only [h1, h2, ↓reduceIte]; exact hdj w
    · rcases how e he htc with h | ⟨i, l, hl, hle⟩
      · exact .inl (hall h)
      · exact .inr ⟨i, l, hl, hle⟩
  · rw [hphu] at hv
    have hvt : v ≠ t := fun e => by rw [e, hout] at hv; cases hv
    rw [upd_ne _ _ hvt]; exact hRk _ (hi.res v hv)
  · obtain ⟨h1, h2⟩ := hi.fq w hw; exact ⟨h1, by rw [hphu]; exact h2⟩
  · obtain ⟨v, hv, hq, h1, h2⟩ := hi.wit hp
    exact ⟨v, by rw [hsz]; exact hv, hq, by rw [hphu]; exact h1,
      fun hh => h2 (by rw [← hphu]; exact hh)⟩

/-! ## The start and the end of the lock -/

/-- The start of the lock: thread `t`, whose clock is below every thread's, gives the word `hW`
(which holds `0`) and the resource `hL` (with `R`) of its part to the lock. Each thread is out of
the lock's code (and alive) or gone, no atomic location is in the word's block, and no thread
waits at a futex. -/
theorem Inv.make {G : ThreadId → γ} {m : Mem} {own : ThreadId → Heap} {t : ThreadId}
    {hL hW : Heap} (ho : Owned own m) (hjt : joinedB m t = false)
    (hown : ∀ u, u ≠ t → L.own G m u = own u)
    (hsplit : own t = L.part (G t) ∪ (hL ∪ hW))
    (hd : Heap.Disjoint (L.part (G t)) (hL ∪ hW)) (hdLW : Heap.Disjoint hL hW)
    (hph : ∀ u, (L.ph (G u) = .out ∧ u < m.threads.size ∧ joinedB m u = false) ∨
      L.ph (G u) = .gone) (hheld : ∀ u, L.held (G u) = Heap.empty)
    (hR : L.R G hL) (hWw : ∀ x, L.o ≤ x → x < L.o + 4 → hW (L.b, x) ≠ none)
    (hblk : ∃ blk, m.blocks[L.b]? = some blk ∧ blk.live = true ∧ L.o + 4 ≤ blk.bytes.size ∧
      (blk.addr + L.o) % 4 = 0 ∧ blk.kind ≠ .constGlobal)
    (h0 : L.U32 m 0) (hat : ∀ l ∈ m.atomics, l.block ≠ L.b) (hq : m.waiters = #[])
    (hall : AllLe m (m.clocks[t]!)) (ht : t < m.threads.size) :
    L.Inv G m := by
  have hW1 : hW.Sub (own t) := by
    rw [hsplit]; exact (Heap.sub_union_right hdLW).trans (Heap.sub_union_right hd)
  have hL1 : hL.Sub (own t) := by
    rw [hsplit]; exact (Heap.sub_union_left).trans (Heap.sub_union_right hd)
  have hP1 : (L.part (G t)).Sub (own t) := by rw [hsplit]; exact Heap.sub_union_left
  have hownE : L.own G m = upd own t (L.part (G t)) := by
    funext u; unfold upd
    by_cases hu : u = t
    · subst hu; simp [Lock.own, hjt, hheld]
    · simp only [hu, ↓reduceIte]; exact hown u hu
  have hWt : ∀ x, L.o ≤ x → x < L.o + 4 → own t (L.b, x) ≠ none := fun x h1 h2 =>
    hW1.ne (hWw x h1 h2)
  have hoffu : ∀ u, L.Off (L.own G m u) := by
    intro u; rw [hownE]; unfold upd
    by_cases hu : u = t
    · simp only [hu, ↓reduceIte]
      exact off_of_disj hd fun x h1 h2 => by simp [hWw x h1 h2]
    · simp only [hu, ↓reduceIte]
      exact off_of_disj (ho.disj u t hu) hWt
  have hfree : L.Free G := fun u => by rcases hph u with ⟨h, -⟩ | h <;> rw [h] <;> decide
  have hnoloc : ∀ i l, ¬ L.Loc m i l := by
    rintro i l ⟨hf, -⟩
    obtain ⟨hi', hp, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact hat _ (Array.getElem_mem hi') hp.1
  refine ⟨hownE ▸ ho.shrink hP1, fun u => by rw [hheld]; exact Heap.disjoint_empty _,
    fun u _ => hheld u, fun u hu => ((hph u).resolve_right hu).2, hblk,
    ⟨0, by decide, h0, ⟨fun _ => hfree, fun _ => rfl⟩⟩,
    fun u _ hu => absurd hu (hfree u),
    ⟨fun l hl hb => absurd hb (hat l hl), fun i l hl => absurd hl (hnoloc i l)⟩, hoffu,
    fun e he hh => .inr fun u hu => VClock.le_trans
      (ho.owns t ht e he (.inl (touches_word hh hWt))) (hall u hu),
    fun i l hl => absurd hl (hnoloc i l), fun _ => ⟨hL, hR, hL1.trans (ho.sub t), fun u => ?_,
      off_of_disj hdLW hWw, fun e he htc => .inl fun u hu => VClock.le_trans
        (ho.owns t ht e he (htc.imp (fun ⟨x, h1, h2, h3⟩ => ⟨x, h1, h2, hL1.ne h3⟩) id))
        (hall u hu)⟩,
    fun u hu => absurd hu (hfree u),
    fun w hw => by rw [hq] at hw; simp at hw, fun hp => by rw [hq] at hp; simp at hp⟩
  rw [hownE]; unfold upd
  by_cases hu : u = t
  · simp only [hu, ↓reduceIte]
    exact (Heap.disjoint_sub hd Heap.sub_union_left).symm
  · simp only [hu, ↓reduceIte]
    exact (Heap.disjoint_sub (ho.disj u t hu) hL1).symm

/-- The word's cells in the heap. -/
def wordH (m : Mem) : Heap := fun l =>
  if l.1 = L.b ∧ L.o ≤ l.2 ∧ l.2 < L.o + 4 then m.heap l else none

/-- The end of the lock: no thread holds it, and thread `t`'s clock is above every thread's.
Then `t` takes the resource `hL` (with `R`) and the word's cells. -/
theorem Inv.take {G : ThreadId → γ} {m : Mem} {t : ThreadId} (hi : L.Inv G m)
    (ht : t < m.threads.size) (hF : L.Free G)
    (hall : ∀ u < m.threads.size, VClock.le (m.clocks[u]!) (m.clocks[t]!) = true) :
    ∃ hL, L.R G hL ∧ Heap.Disjoint hL (L.wordH m) ∧
      Heap.Disjoint (L.own G m t) (hL ∪ L.wordH m) ∧
      Owned (upd (L.own G m) t (L.own G m t ∪ (hL ∪ L.wordH m))) m := by
  obtain ⟨hL, hR, hsub, hdj, hoff, how⟩ := hi.free hF
  have hWs : (L.wordH m).Sub m.heap := fun l c hc => by
    unfold wordH at hc; split at hc
    · exact hc
    · cases hc
  have hWin : ∀ {l}, L.wordH m l ≠ none → l.1 = L.b ∧ L.o ≤ l.2 ∧ l.2 < L.o + 4 := by
    intro l hl; unfold wordH at hl; split at hl
    · assumption
    · exact absurd rfl hl
  have hdW : ∀ u, Heap.Disjoint (L.own G m u) (L.wordH m) := fun u l => by
    by_cases hw : L.wordH m l = none
    · exact .inr hw
    · obtain ⟨h1, h2, h3⟩ := hWin hw
      left; obtain ⟨b, x⟩ := l; simp only at h1 h2 h3; subst h1; exact hi.off u x h2 h3
  have hdLW : Heap.Disjoint hL (L.wordH m) := fun l => by
    by_cases hw : L.wordH m l = none
    · exact .inr hw
    · obtain ⟨h1, h2, h3⟩ := hWin hw
      left; obtain ⟨b, x⟩ := l; simp only at h1 h2 h3; subst h1; exact hoff x h2 h3
  have hd : Heap.Disjoint (L.own G m t) (hL ∪ L.wordH m) :=
    Heap.disjoint_union_right.mpr ⟨(hdj t).symm, hdW t⟩
  refine ⟨hL, hR, hdLW, hd, ⟨fun u => ?_, fun u v huv => ?_, fun u hu => ?_, fun u hu => ?_,
    hi.own.csize⟩⟩
  · unfold upd; split
    · exact Heap.union_sub (hi.own.sub t) (Heap.union_sub hsub hWs)
    · exact hi.own.sub u
  · have hx : ∀ w, w ≠ t → Heap.Disjoint (L.own G m t ∪ (hL ∪ L.wordH m)) (L.own G m w) :=
      fun w hw => Heap.disjoint_union_left.mpr ⟨hi.own.disj t w (Ne.symm hw),
        Heap.disjoint_union_left.mpr ⟨hdj w, (hdW w).symm⟩⟩
    unfold upd
    by_cases hu : u = t
    · subst hu; simp only [↓reduceIte, Ne.symm huv]; exact hx v (Ne.symm huv)
    · by_cases hv : v = t
      · subst hv; simp only [hu, ↓reduceIte]; exact (hx u hu).symm
      · simp only [hu, hv, ↓reduceIte]; exact hi.own.disj u v huv
  · unfold upd; split
    · rename_i hut; subst hut
      refine Mem.OwnsC.union (hi.own.owns u hu) (Mem.OwnsC.union (fun e he htc => ?_)
        (fun e he htc => ?_))
      · rcases how e he htc with h | ⟨i, l, hl, hle⟩
        · exact h u hu
        · obtain ⟨⟨v, hv, hle'⟩, -⟩ := hi.rel i l hl
          exact VClock.le_trans hle (VClock.le_trans hle' (hall v hv))
      · rcases htc with ⟨x, h1, h2, h3⟩ | hb
        · obtain ⟨hb, hx1, hx2⟩ := hWin h3
          rcases hi.wfp e he ⟨hb, x, h1, h2, hx1, hx2⟩ with ⟨-, v, hv, hle⟩ | h
          · exact VClock.le_trans hle (hall v hv)
          · exact h u hu
        · exact hi.own.owns u hu e he (.inr hb)
    · exact hi.own.owns u hu
  · unfold upd; split
    · rename_i hut; subst hut; exact absurd ht (Nat.not_lt.mpr hu)
    · exact hi.own.outside u hu

end Lock

end Conc
end Zig
