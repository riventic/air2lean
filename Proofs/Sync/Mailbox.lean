import Proofs.Sync.Contracts

/-!
# A producer/consumer mailbox against the `Io.Semaphore` contract (C14 client)

A model client written in Lean (it is not a Zig export): a block holds an `Io.Semaphore` with
no permit (bytes 0..24: the permit count, its mutex and its `Io.Condition`) and a two-field
message `a` (24..28), `b` (28..32). `main` stores zeros, spawns a producer and hands it the
message cells. The producer writes `a = 3`, `b = 4` and `post`s; `main` `wait`s, reads both
fields, joins the producer and returns `10 * a + b`. The result is 34 under every schedule
(`mailbox_spec`) and no schedule gives an error (`mailbox_safe`): no data race on the message,
no deadlock (the consumer may sleep at the condition before the producer posts).

`wait` is std's condition-variable loop (`while (permits == 0) cond.wait(&mutex)`): the
predicate is rechecked under the mutex after every wake-up. The client never sees that loop:
its code takes the semaphore operations as parameters (`waitOp`, `postOp`) and its proof uses
only the hypothesis `SemContract S waitOp postOp` (`Proofs/Sync/Contracts.lean`), the generic
semaphore invariant interface (`Sem.Fits`) and the lock rules. The final theorems instantiate
the operations with the translated `Io_Semaphore_waitUncancelable` / `Io_Semaphore_post`
through `Sync.Contracts.semaphore`.

**Ownership transfer.** The message cells move: `main` → producer (at the spawn, `Inv.fork`),
producer → the free permit (`post`: the contract's `h₃ ∪ hr` rule), free permit → `main`
(`wait`: the contract's `T` rule). `main` reads the cells while the producer still runs, with
no further synchronization, because it owns them.

Scope: one producer, one consumer, one message; at most one thread waits at the condition.
No fairness or termination claim.
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Conc.Lock Sync Assn Sync.Contracts

namespace Sync.Mailbox

attribute [local irreducible] Proto.WP

/-! ## The code -/

/-- The semaphore with no permit. -/
def semZ : Io_Semaphore :=
  { mutex := ({ state := ({ raw := Io_Mutex_State.unlocked } : atomic_Value_Io_Mutex_State) } : Io_Mutex),
    cond := ({ state := ({ raw := (Packed.ofBits (0 : BitVec 32) : Io_Condition_State) } :
      atomic_Value_Io_Condition_State), epoch := ({ raw := (0 : BitVec 32) } : atomic_Value_u32) } :
      Io_Condition),
    permits := (0 : BitVec 64) }

section Code

variable (waitOp postOp : Ptr → Io → ConcM Tgt Unit)

/-- The producer: write the message, then `post`. -/
def producer (p : Ptr) : ConcM Tgt Unit :=
  (do
    Zig.store (α := BitVec 32) 4 (p.add 24) 3
    Zig.store (α := BitVec 32) 4 (p.add 28) 4
    callC (postOp p ⟨⟩) : CM Tgt Unit Unit).run' ()

/-- The spawn targets: `semWork p` runs the producer. -/
def dispatch : Tgt → ConcM Tgt Unit
  | .semWork p => producer postOp p
  | _ => pure ()

/-- `main`: build the mailbox, spawn the producer, `wait`, read the message, join, free. -/
def mailMain (io : Io) : ConcM Tgt (Except ErrName (BitVec 32)) := do
  let s1 ← Zig.allocStack 32 8
  let e ← ((do
    Zig.store (α := Io_Semaphore) 8 (s1.add 0) semZ
    Zig.store (α := BitVec 32) 4 (s1.add 24) 0
    Zig.store (α := BitVec 32) 4 (s1.add 28) 0
    let t ← Zig.spawnC (Tgt.semWork s1)
    match t with
    | .error e => pure (.error e)
    | .ok tid => do
      callC (waitOp s1 io)
      let x ← Zig.load (BitVec 32) 4 (s1.add 24)
      let y ← Zig.load (BitVec 32) 4 (s1.add 28)
      Zig.joinC tid
      pure (.ok (10 * x + y))) : CM Tgt Unit (Except ErrName (BitVec 32))).run' ()
  Zig.free s1
  pure e

end Code

/-! ## The protocol -/

/-- Where a thread is, outside the semaphore's code. -/
inductive Ph where
  | none
  /-- `main` before its spawn: it owns the message cells. -/
  | pre
  /-- `main` before or in `wait`. -/
  | wt
  /-- `main` took the permit and the message. -/
  | got
  /-- `main` at its join. -/
  | joins
  /-- The producer wrote `k` of the two fields. -/
  | pr (k : Nat)
  /-- The producer posted. -/
  | pd
  /-- The producer has ended. -/
  | fin
  deriving DecidableEq

/-- The producer posted. -/
def Ph.posted : Ph → Bool
  | .pd | .fin => true
  | _ => false

/-- `main` took the permit. -/
def Ph.took : Ph → Bool
  | .got | .joins => true
  | _ => false

abbrev Gh := SGh Ph

/-- The places of the threads. -/
abbrev XG (G : ThreadId → Gh) : ThreadId → Ph := fun u => (G u).2.2

/-- The mailbox (block 0). -/
def cPtr : Ptr := ⟨some 0, 0⟩
def aPtr : Ptr := cPtr.add 24
def bPtr : Ptr := cPtr.add 28

/-- The message after `k` of the producer's two stores. -/
def Msg (k : Nat) : Assn :=
  pts aPtr 4 (if 1 ≤ k then (3 : BitVec 32) else 0) ∗ pts bPtr 4 (if 2 ≤ k then (4 : BitVec 32) else 0)

/-- The permit is free: posted and not taken. -/
def avail (Y : ThreadId → Ph) : Bool := (Y 1).posted && !(Y 0).took

theorem enc_u32 (v : BitVec 32) : (Enc.encode v).size = 4 := LawfulEnc.size_encode v

/-- The message's bytes: 24..32 of block 0. -/
theorem pts_off {p : Ptr} {v : BitVec 32} {h : Heap} (hp : pts p 4 v h)
    (hpb : p = aPtr ∨ p = bPtr) {x : Nat} (hx : x < 24) : h (0, x) = none := by
  obtain ⟨A, Sz, K, bs, -, hs, -, ⟨b, hb, -, hl⟩, -⟩ := hp
  rcases hpb with rfl | rfl <;> cases hb <;> rw [hl, if_neg] <;>
    simp [aPtr, bPtr, cPtr, Ptr.add] <;> intro _ <;> omega

theorem msg_off {k : Nat} {h : Heap} (hm : Msg k h) {x : Nat} (hx : x < 24) : h (0, x) = none := by
  obtain ⟨h₁, h₂, -, rfl, ha, hb⟩ := hm
  simp [Heap.union_apply, pts_off ha (.inl rfl) hx, pts_off hb (.inr rfl) hx]

/-- The semaphore: its free permit owns the written message. -/
def S : Sem Ph where
  b := 0
  o := 0
  pv Y := if avail Y then 1 else 0
  Res Y := if avail Y then Msg 2 else emp
  res_off Y h hR x h1 h2 := by
    by_cases ha : avail Y = true
    · simp only [ha, ↓reduceIte] at hR; exact msg_off hR (by omega)
    · simp only [ha, Bool.false_eq_true, ↓reduceIte] at hR; rw [hR]; rfl
  wx p := p = .wt

/-- A thread's part: the message while it owns it. -/
def PartOk (x : Ph) (h : Heap) : Prop :=
  match x with
  | .pre => Msg 0 h
  | .pr k => Msg k h
  | .got | .joins => Msg 2 h
  | _ => h = Heap.empty

/-- The threads: `main` alone before its spawn; then `main` and the producer. `main` takes the
permit only after the producer posted. -/
def Shape (X : ThreadId → Ph) (m : Mem) : Prop :=
  m.threads[0]? = some { spawner := 0, joined := true } ∧
  ((m.threads.size = 1 ∧ X 0 = .pre ∧ ∀ u, 1 ≤ u → X u = .none) ∨
   (m.threads.size = 2 ∧ m.threads[1]? = some { spawner := 0, joined := false } ∧
    (X 0 = .wt ∨ X 0 = .got ∨ X 0 = .joins) ∧ (X 1 = .fin ∨ X 1 = .pd ∨ ∃ k ≤ 2, X 1 = .pr k) ∧
    ((X 0).took = true → (X 1).posted = true) ∧ ∀ u, 2 ≤ u → X u = .none))

/-- Block 0 is the live mailbox: 32 bytes on the stack, 8-aligned. -/
def BlkOk (m : Mem) : Prop :=
  ∃ blk, m.blocks[0]? = some blk ∧ blk.live = true ∧ blk.bytes.size = 32 ∧ blk.addr % 8 = 0 ∧
    blk.kind = .stack

/-- The rest of the invariant. -/
structure U (G : ThreadId → Gh) (m : Mem) : Prop where
  shape : Shape (XG G) m
  parts : ∀ u, PartOk (XG G u) (G u).1.part
  blk : BlkOk m
  q : ∀ w ∈ m.waiters, w.2 = S.L.ptr ∨ w.2 = S.WE.ptr
  wx : ∀ u, (G u).2.1.waits = true → (G u).2.2 = .wt

/-- The protocol, in strict mode. -/
def proto : Proto Tgt Gh where
  inv G m := S.L.Inv G m ∧ S.Inv G m ∧ U G m
  init tgt g := match tgt with
    | .semWork p => p = cPtr ∧ ∃ h, g = (⟨.out, h, Heap.empty⟩, .none, .pr 0)
    | _ => False
  fin g := g.1.ph = .gone ∧ g.2.2 = .fin
  strict := true
  joins g := g.1.ph = .out ∧ g.2.2 = .joins

/-- `main`'s post: the result. -/
def QM : Except ErrName (BitVec 32) → (ThreadId → Gh) → Mem → Nat → Prop :=
  fun v _ m _ => v = .ok 34 ∧ joinedAll 0 m

/-! ## The protocol has the semaphore -/

theorem partOk_off {x : Ph} {h : Heap} (hp : PartOk x h) {y : Nat} (hy : y < 24) :
    h (0, y) = none := by
  cases x <;> simp only [PartOk] at hp <;> first | exact msg_off hp hy | (rw [hp]; rfl)

/-- The pad cell (byte 20 of block 0): nobody writes it. -/
theorem blk_heap {m : Mem} (hb : BlkOk m) {x : Nat} (hx : x < 32) : m.heap (0, x) ≠ none := by
  obtain ⟨blk, hblk, hl, hs, -⟩ := hb
  simp only [Mem.heap, hblk]
  rw [dite_eq_left_of_eq_true (eq_true ⟨hl, by omega⟩)]
  simp

theorem blk_keep {m m' : Mem} (hb : BlkOk m) (h : m'.heap (0, 20) = m.heap (0, 20)) : BlkOk m' := by
  obtain ⟨blk, hblk, hl, hs, ha, hk⟩ := hb
  have hc : m.heap (0, 20) = some ⟨blk.bytes[20]'(by omega), blk.addr, blk.bytes.size, blk.kind⟩ := by
    simp only [Mem.heap, hblk]; rw [dite_eq_left_of_eq_true (eq_true ⟨hl, by omega⟩)]
  rw [hc] at h
  obtain ⟨blk', hblk', hl', ho', he⟩ := Mem.heap_some h
  simp only [Cell.mk.injEq] at he
  obtain ⟨-, hA, hS, hK⟩ := he
  exact ⟨blk', hblk', by simpa using hl', by rw [← hS, hs], by rw [← hA, ha], by rw [← hK, hk]⟩

theorem shape_pr {X : ThreadId → Ph} {m : Mem} {t k : Nat} (h : Shape X m) (hx : X t = .pr k) :
    t = 1 ∧ m.threads.size = 2 ∧ k ≤ 2 := by
  obtain ⟨-, ⟨-, h0, h1⟩ | ⟨hs, -, h0, h1, -, h2⟩⟩ := h
  · by_cases ht : t = 0
    · subst ht; rw [h0] at hx; cases hx
    · rw [h1 t (Nat.pos_of_ne_zero ht)] at hx; cases hx
  · have ht : t = 1 := by
      by_cases ht0 : t = 0
      · subst ht0; rcases h0 with h0 | h0 | h0 <;> rw [h0] at hx <;> cases hx
      · by_cases ht2 : 2 ≤ t
        · rw [h2 t ht2] at hx; cases hx
        · omega
    subst ht
    rcases h1 with h1 | h1 | ⟨k', hk, h1⟩ <;> rw [h1] at hx <;> cases hx
    exact ⟨rfl, hs, hk⟩

theorem shape_wt {X : ThreadId → Ph} {m : Mem} {t : ThreadId} (h : Shape X m) (hx : X t = .wt) :
    t = 0 ∧ m.threads.size = 2 := by
  obtain ⟨-, ⟨-, h0, h1⟩ | ⟨hs, -, -, h1, -, h2⟩⟩ := h
  · by_cases ht : t = 0
    · subst ht; rw [h0] at hx; cases hx
    · rw [h1 t (Nat.pos_of_ne_zero ht)] at hx; cases hx
  · refine ⟨?_, hs⟩
    by_cases ht0 : t = 0
    · exact ht0
    · by_cases ht1 : t = 1
      · subst ht1; rcases h1 with h1 | h1 | ⟨k, -, h1⟩ <;> rw [h1] at hx <;> cases hx
      · rw [h2 t (by unfold ThreadId at *; omega)] at hx; cases hx

/-- The permit count is 0: the permit is not free. -/
theorem avail_of_pz {G : ThreadId → Gh} {m : Mem} (hl : S.L.Inv G m) (hpz : S.PZ m) :
    avail (XG G) = false := by
  obtain ⟨hz, hzp, hzs⟩ := hpz
  have hR : ∃ hL, S.L.R G hL ∧ hL.Sub m.heap := by
    by_cases hf : ∃ u, S.L.ph (G u) = .holds
    · obtain ⟨u, hu⟩ := hf
      obtain ⟨hlv, hjt⟩ := hl.live u (by rw [hu]; decide)
      refine ⟨_, hl.res u hu, fun l c h => hl.own.sub u l c ?_⟩
      rw [Lock.own_live hjt]
      show (S.L.part (G u) ∪ S.L.held (G u)) l = some c
      rw [Heap.union_of_right ((hl.pdisj u l).resolve_right (by rw [h]; simp))]; exact h
    · obtain ⟨hL, hR, hs, -⟩ := hl.free (fun u h => hf ⟨u, h⟩)
      exact ⟨hL, hR, hs⟩
  obtain ⟨hL, ⟨hp, hr, -, rfl, hpp, -⟩, hs⟩ := hR
  have := Sem.pts_eq (S := S) hpp (fun l c h => hs l c (by simp [h])) hzp hzs
  change (if avail _ then (1 : BitVec 64) else 0) = 0 at this
  split at this
  · cases this
  · rename_i h; exact (Bool.eq_false_iff.mpr h :)

theorem stable (G : ThreadId → Gh) (m m' : Mem) (t : ThreadId) (g : Gh) (hu : U G m)
    (hs : S.Step t m m') (h2 : g.2.2 = (G t).2.2) (hp : g.1.part = (G t).1.part)
    (hw : g.2.1.waits = true → (G t).2.1.waits = true ∨ S.wx g.2.2)
    (_ : (g.1.ph ≠ (G t).1.ph ∨ g.2.1 ≠ (G t).2.1) → S.inS g.2.2) : U (upd G t g) m' := by
  have hX : XG (upd G t g) = XG G := funext fun u => by
    show (upd G t g u).2.2 = _; unfold upd; split
    · rename_i e; subst e; exact h2
    · rfl
  refine ⟨?_, fun u => ?_, blk_keep hu.blk (hs.cells _ ?_), fun w hw' => ?_, fun u hu' => ?_⟩
  · rw [hX]; have := hu.shape; unfold Shape at this ⊢; rw [hs.threads]; exact this
  · rw [hX]; by_cases e : u = t
    · subst e; rw [upd_self, hp]; exact hu.parts u
    · rw [upd_ne _ _ e]; exact hu.parts u
  · rintro ⟨-, -, h1⟩; simp [S] at h1
  · by_cases h1 : w.2 = S.L.ptr
    · exact .inl h1
    · by_cases h2 : w.2 = S.WE.ptr
      · exact .inr h2
      · exact hu.q w (hs.waiters w hw' h1 h2)
  · by_cases e : u = t
    · subst e; rw [upd_self] at hu' ⊢
      rcases hw hu' with h | h
      · rw [h2]; exact hu.wx u h
      · exact h
    · rw [upd_ne _ _ e] at hu' ⊢; exact hu.wx u hu'

/-- No thread owns the pad byte 20, and the lock's resource has none. -/
theorem own_pad {G : ThreadId → Gh} {m : Mem} (hl : S.L.Inv G m) (hu : U G m) (u : ThreadId) :
    S.L.own G m u (0, 20) = none := by
  unfold Lock.own; split
  · rfl
  · show ((G u).1.part ∪ (G u).1.held) (0, 20) = none
    rw [Heap.union_apply, partOk_off (hu.parts u) (by decide), Option.none_or]
    by_cases hh : S.L.ph (G u) = .holds
    · obtain ⟨hp, hr, -, he, hpp, hrr⟩ := hl.res u hh
      rw [show (G u).1.held = S.L.held (G u) from rfl, he]
      have h1 : hp (0, 20) = none := by
        cases hc : hp (0, 20) with
        | none => rfl
        | some c =>
          have := (Sem.pts_cells (S := S) hpp (l := (0, 20)) (by rw [hc]; simp)).2.2
          simp [S] at this
      have h2 : hr (0, 20) = none := by
        change (if avail _ then Msg 2 else emp) hr at hrr
        split at hrr
        · exact msg_off hrr (by decide)
        · rw [hrr]; rfl
      simp [Heap.union_apply, h1, h2]
    · rw [show (G u).1.held = S.L.held (G u) from rfl, hl.idle u hh]; rfl

theorem own_step (G : ThreadId → Gh) (m m' : Mem) (t : ThreadId) (g : Gh) (hQ : Heap)
    (hl : S.L.Inv G m) (hu : U G m) (hs : StepIn (m.heap.diff (S.L.own G m t)) m m')
    (hm' : m'.heap = hQ ∪ m.heap.diff (S.L.own G m t))
    (hd : Heap.Disjoint hQ (m.heap.diff (S.L.own G m t))) (h2 : g.2 = (G t).2)
    (hp : g.1.part = (G t).1.part) : U (upd G t g) m' := by
  have hX : XG (upd G t g) = XG G := funext fun u => by
    show (upd G t g u).2.2 = _; unfold upd; split
    · rename_i e; subst e; rw [h2]
    · rfl
  have hS : ∀ u, (upd G t g u).2 = (G u).2 := fun u => by
    unfold upd; split
    · rename_i e; subst e; exact h2
    · rfl
  have hrest : m.heap.diff (S.L.own G m t) (0, 20) = m.heap (0, 20) := by
    simp [Heap.diff, own_pad hl hu t]
  refine ⟨?_, fun u => ?_, blk_keep hu.blk ?_, fun w hw => ?_, fun u hu' => ?_⟩
  · rw [hX]; have := hu.shape; unfold Shape at this ⊢; rw [hs.threads]; exact this
  · rw [hX]; by_cases e : u = t
    · subst e; rw [upd_self, hp]; exact hu.parts u
    · rw [upd_ne _ _ e]; exact hu.parts u
  · rw [hm', Heap.union_of_right ((hd (0, 20)).resolve_right (by
      rw [hrest]; exact blk_heap hu.blk (by decide))), hrest]
  · rw [hs.waiters] at hw; exact hu.q w hw
  · rw [hS] at hu' ⊢; exact hu.wx u hu'

theorem fits : S.Fits proto U where
  inv _ _ := Iff.rfl
  fin _ h := h.1
  joins _ h := h.1
  stable := stable
  own G m m' t g hQ hl hu hs hm' hd _ _ h2 hp _ := own_step G m m' t g hQ hl hu hs hm' hd h2 hp
  waits _ _ w _ _ _ _ hi hw _ := hi.2.2.q w hw
  live G m r i jr sn e hi hr hpz hall := by
    obtain ⟨hl, hs, hu⟩ := hi
    have hav := avail_of_pz hl hpz
    have hr0 := hu.wx r (by rw [hr]; rfl)
    obtain ⟨rfl, hs2⟩ := shape_wt hu.shape hr0
    -- the producer has not posted
    have hnp : (XG G 1).posted = false := by
      simp only [avail, Bool.and_eq_false_iff, Bool.not_eq_false'] at hav
      rcases hav with h | h
      · exact h
      · exfalso; have : (XG G 0).took = true := h; rw [show XG G 0 = .wt from hr0] at this; cases this
    rcases hall 1 (by omega) with hf | hq | hj
    · have h1 : XG G 1 = .fin := hf.2
      rw [h1] at hnp; cases hnp
    · obtain ⟨i', hi', he⟩ := Array.any_eq_true.mp hq
      have he : (m.waiters[i']).1 = 1 := by simpa using he
      have hw := Array.getElem_mem hi'
      rcases hu.q _ hw with hL | hE
      · -- a waiter at the mutex: its lock witness goes on
        obtain ⟨v', hv', hq', hb, -⟩ := hl.wit (Array.any_eq_true.mpr ⟨i', hi', by simp [hL]⟩)
        rcases hall v' hv' with h | h | h
        · rw [show S.L.ph (G v') = .gone from h.1] at hb; cases hb
        · rw [hq'] at h; cases h
        · rw [show S.L.ph (G v') = .out from h.1] at hb; cases hb
      · obtain ⟨i'', jr', e', h1, -⟩ := hs.q _ hw hE
        rw [he] at h1
        have := hu.wx 1 (by rw [h1]; rfl)
        have h1' : XG G 1 = .wt := this
        obtain ⟨h10, -⟩ := shape_wt hu.shape h1'
        cases h10
    · have h1 : XG G 1 = .joins := hj.2
      obtain ⟨-, ⟨hs1, -, -⟩ | ⟨-, -, -, h1', -, -⟩⟩ := hu.shape
      · omega
      · rw [h1] at h1'; rcases h1' with h1' | h1' | ⟨k, -, h1'⟩ <;> cases h1'

/-! ## The message, by its owner -/

theorem XG_upd (G : ThreadId → Gh) (t : ThreadId) (g : Gh) :
    XG (upd G t g) = upd (XG G) t g.2.2 := by
  funext u; show (upd G t g u).2.2 = _; unfold upd; split <;> rfl

/-- A step `c` of thread `t` on the message it owns (out of the semaphore's code): from place
`x` to `x'`, with the same permit state. -/
theorem wp_msg {σ β : Type} {c : MemM β} {s : σ} {t : ThreadId} {G : ThreadId → Gh} {m : Mem}
    {d : Nat} {h : Heap} {x x' : Ph} {P₁ P₂ : Assn} {r₀ : β}
    {Q : β × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (hi : proto.inv (upd G t (⟨.out, h, Heap.empty⟩, .none, x)) m) (hc : m.current = t)
    (hP₁ : PartOk x h → P₁ h) (hP₂ : ∀ h', P₂ h' → PartOk x' h')
    (ht : TTriple P₁ c (fun r => ⌜r = r₀⌝ ∗ P₂))
    (hoff : ∀ h', P₂ h' → ∀ y, y < 24 → h' (0, y) = none)
    (hav : avail (upd (XG G) t x') = avail (upd (XG G) t x))
    (hsh : Shape (upd (XG G) t x) m → Shape (upd (XG G) t x') m)
    (hq : ∀ m' h', m'.current = t → m'.threads = m.threads →
      proto.inv (upd G t (⟨.out, h', Heap.empty⟩, .none, x')) m' → Q (r₀, s) G m' d) :
    proto.WP t ((liftM c : CM Tgt σ β).run s) Q G m d := by
  obtain ⟨hl, hs, hu⟩ := hi
  have hph : S.L.ph (upd G t (⟨.out, h, Heap.empty⟩, SPh.none, x) t) = .out := by
    rw [upd_self]; rfl
  obtain ⟨htl, hjt⟩ := hl.live t (by rw [hph]; decide)
  have hown : S.L.own (upd G t (⟨.out, h, Heap.empty⟩, .none, x)) m t = h := by
    rw [Lock.own_live hjt, upd_self]; exact Heap.union_empty h
  have hpart : PartOk x h := by have := hu.parts t; simp only [XG, upd_self] at this; exact this
  refine WP.liftM_owned ht hl.own hc htl (by rw [hown]; exact hP₁ hpart)
    fun a m' hQ _ ho' hq' hst hm' hd => ?_
  obtain ⟨rfl, hpQ⟩ := sep_lift.mp hq'
  rw [hown] at hst hm' hd
  let g' : Gh := (⟨.out, hQ, Heap.empty⟩, .none, x')
  have hR : ∀ hL, S.L.R (upd G t (⟨.out, h, Heap.empty⟩, .none, x)) hL →
      S.L.R (upd (upd G t (⟨.out, h, Heap.empty⟩, .none, x)) t g') hL := by
    intro hL hR
    rw [upd_upd]
    change (pts S.ptr 8 (if avail (XG (upd G t _)) then (1 : BitVec 64) else 0) ∗
      (if avail (XG (upd G t _)) then Msg 2 else emp)) hL at hR
    change (pts S.ptr 8 (if avail (XG (upd G t g')) then (1 : BitVec 64) else 0) ∗
      (if avail (XG (upd G t g')) then Msg 2 else emp)) hL
    rw [XG_upd] at hR ⊢
    rw [show g'.2.2 = x' from rfl, hav]; exact hR
  have hl' := hl.stepIn (g := g') hc hjt
    (by show Owned (upd _ t (hQ ∪ Heap.empty)) m'; rw [Heap.union_empty]; exact ho')
    (by rw [hown]; exact hst)
    (by rw [hown]; show m'.heap = (hQ ∪ Heap.empty) ∪ _; rw [Heap.union_empty]; exact hm')
    (by rw [hown]; show Heap.Disjoint (hQ ∪ Heap.empty) _; rw [Heap.union_empty]; exact hd)
    (by rw [upd_self]; rfl) (Heap.disjoint_empty _) (fun _ => rfl)
    (fun _ hL hR' => hR hL hR') (fun h₀ => by cases h₀)
  rw [upd_upd] at hl'
  have hnone : ∀ y, y < 24 → m'.heap (0, y) = m.heap (0, y) := fun y hy => by
    rw [hm', Heap.union_apply, hoff hQ hpQ y hy, Option.none_or]
    simp [Heap.diff, partOk_off hpart hy]
  have hpz : S.PZ m → S.PZ m' ∨ ∃ v, (upd G t (⟨.out, h, Heap.empty⟩, .none, x) v).2.1 = .pst :=
    fun hz => .inl (Sem.PZ.mono hz fun y h1 h2 => hnone y (by simp [S] at h1 h2; omega))
  have hs' := (hs.stepIn hl (by rw [hown]; exact hst) (by rw [hown]; exact hm')
    (by rw [hown]; exact hd) hpz).congrG (G' := upd G t g') (fun u => by unfold upd; split <;> rfl)
    (fun u => by unfold upd; split <;> exact Iff.rfl) (fun u y h1 h2 => by
      by_cases e : u = t
      · subst e; rw [upd_self]; exact hoff hQ hpQ y (by simp [S] at h2; omega)
      · rw [upd_ne _ _ e]; have := hs.off u y h1 h2; rwa [upd_ne _ _ e] at this)
  have hXn : XG (upd G t g') = upd (XG (upd G t (⟨.out, h, Heap.empty⟩, .none, x))) t x' := by
    rw [XG_upd, XG_upd, upd_upd]
  refine hq m' hQ (hst.current.trans hc) hst.threads ⟨hl', hs', ⟨?_, fun u => ?_,
    blk_keep hu.blk (hnone 20 (by decide)), fun w hw => ?_, fun u hu' => ?_⟩⟩
  · have := hsh (by have := hu.shape; rwa [XG_upd] at this)
    rw [XG_upd]; unfold Shape at this ⊢; rw [hst.threads]; exact this
  · by_cases e : u = t
    · subst e; simp only [XG, upd_self]; exact hP₂ hQ hpQ
    · have := hu.parts u; simp only [XG, upd_ne _ _ e] at this
      simp only [XG, upd_ne _ _ e]; exact this
  · rw [hst.waiters] at hw; exact hu.q w hw
  · by_cases e : u = t
    · subst e; rw [upd_self] at hu'; cases hu'
    · rw [upd_ne _ _ e] at hu' ⊢; have := hu.wx u (by rw [upd_ne _ _ e]; exact hu')
      rwa [upd_ne _ _ e] at this

/-! ## The semaphore contract's obligations for this protocol -/

theorem msg_cell {k : Nat} {h : Heap} (hm : Msg k h) : h (0, 24) ≠ none := by
  obtain ⟨h₁, h₂, -, rfl, ⟨A, Sz, K, bs, -, hs, -, hb, -⟩, -⟩ := hm
  have := bytesAt_in hb rfl (by simp [aPtr, cPtr, Ptr.add]) (by
    rw [hs, show Enc.size (BitVec 32) = 4 from rfl]; simp [aPtr, cPtr, Ptr.add]) (x := 24)
  simp only [Heap.union_apply]
  cases e : h₁ (0, 24) with
  | none => exact absurd e this
  | some c => simp

theorem Msg0 : Msg 0 = (pts aPtr 4 (0 : BitVec 32) ∗ pts bPtr 4 (0 : BitVec 32)) := by simp [Msg]
theorem Msg1 : Msg 1 = (pts aPtr 4 (3 : BitVec 32) ∗ pts bPtr 4 (0 : BitVec 32)) := by simp [Msg]
theorem Msg2 : Msg 2 = (pts aPtr 4 (3 : BitVec 32) ∗ pts bPtr 4 (4 : BitVec 32)) := by simp [Msg]

/-- A change of thread `t`'s place (and parts) keeps `U` with the new shape and part. -/
theorem U_retag {G : ThreadId → Gh} {m : Mem} {t : ThreadId} {g g' : Gh} (hu : U (upd G t g) m)
    (hsh : Shape (XG (upd G t g')) m) (hpt : PartOk g'.2.2 g'.1.part)
    (hwx : g'.2.1.waits = true → g'.2.2 = .wt) : U (upd G t g') m := by
  refine ⟨hsh, fun u => ?_, hu.blk, hu.q, fun u hu' => ?_⟩
  · by_cases e : u = t
    · subst e; simp only [XG, upd_self]; exact hpt
    · have := hu.parts u; simp only [XG, upd_ne _ _ e] at this ⊢; exact this
  · by_cases e : u = t
    · subst e; rw [upd_self] at hu' ⊢; exact hwx hu'
    · rw [upd_ne _ _ e] at hu' ⊢; have := hu.wx u (by rw [upd_ne _ _ e]; exact hu')
      rwa [upd_ne _ _ e] at this

/-- A new place `p` of thread `t` (0 or 1) with two threads. -/
theorem shape_set {X : ThreadId → Ph} {m : Mem} {t : ThreadId} (h : Shape X m)
    (h2 : m.threads.size = 2) (p : Ph)
    (hp0 : t = 0 → p = .wt ∨ p = .got ∨ p = .joins)
    (hp1 : t = 1 → p = .fin ∨ p = .pd ∨ ∃ k ≤ 2, p = .pr k) (ht : t = 0 ∨ t = 1)
    (htook : (upd X t p 0).took = true → (upd X t p 1).posted = true) : Shape (upd X t p) m := by
  obtain ⟨h00, ⟨hs1, -, -⟩ | ⟨-, hr, h0, h1, -, hn⟩⟩ := h
  · omega
  refine ⟨h00, .inr ⟨h2, hr, ?_, ?_, htook, fun u hu => ?_⟩⟩
  · rcases ht with rfl | rfl
    · rw [upd_self]; exact hp0 rfl
    · rw [upd_ne _ _ (by decide)]; exact h0
  · rcases ht with rfl | rfl
    · rw [upd_ne _ _ (by decide)]; exact h1
    · rw [upd_self]; exact hp1 rfl
  · rw [upd_ne _ _ (by rcases ht with rfl | rfl <;> unfold ThreadId at * <;> omega)]; exact hn u hu

section Specs

/-- In `wait`, no other thread waits at the condition: only `main` ever waits there. -/
theorem hone_w : ∀ G' m', proto.inv G' m' → (G' 0).2.2 = .wt → (G' 0).1.ph = .holds → S.PZ m' →
    ∀ u, u ≠ 0 → ∀ i jr sn e, (G' u).2.1 ≠ .reg i jr sn e := by
  intro G' m' hi _ _ _ u hu i jr sn e hr
  exact hu (shape_wt hi.2.2.shape (hi.2.2.wx u (by rw [hr]; rfl))).1

/-- `wait` takes the free permit and the message. -/
theorem hmv_w : ∀ Y : ThreadId → Ph, Y 0 = .wt → S.pv Y ≠ 0 →
    S.pv (upd Y 0 .got) = S.pv Y - 1 ∧
    ∀ hr, S.Res Y hr → ∃ h₁ h₂, hr = h₁ ∪ h₂ ∧ Heap.Disjoint h₁ h₂ ∧
      S.Res (upd Y 0 .got) h₁ ∧ Msg 2 h₂ := by
  intro Y _ hpv
  have ha : avail Y = true := by
    cases h : avail Y
    · exact absurd (by show (if avail Y then (1 : BitVec 64) else 0) = 0; rw [h]; rfl) hpv
    · rfl
  have hn : avail (upd Y 0 .got) = false := by simp [avail, Ph.took]
  refine ⟨?_, fun hr hR => ⟨Heap.empty, hr, (Heap.empty_union hr).symm,
    (Heap.disjoint_empty _).symm, ?_, ?_⟩⟩
  · show (if avail _ then (1 : BitVec 64) else 0) = (if avail Y then (1 : BitVec 64) else 0) - 1
    rw [hn, ha]; rfl
  · show (if avail _ then Msg 2 else emp) Heap.empty; rw [hn]; rfl
  · have : (if avail Y then Msg 2 else emp) hr := hR
    rw [ha] at this; exact this

theorem hU_w : ∀ G m h₁ h₂ h₃ h₄, Msg 2 h₃ → Heap.Disjoint h₄ h₃ →
    S.Res (Sem.xs fun u => (upd G 0 (⟨.holds, Heap.empty, h₁⟩, .none, .wt) u).2) (h₄ ∪ h₃) →
    U (upd G 0 (⟨.holds, Heap.empty, h₁⟩, .none, .wt)) m →
    U (upd G 0 (⟨.holds, Heap.empty ∪ h₃, h₂⟩, .none, .got)) m := by
  intro G m h₁ h₂ h₃ h₄ hm _ hR hu
  have hR' : (if avail (XG (upd G 0 (⟨.holds, Heap.empty, h₁⟩, .none, .wt))) then Msg 2 else emp)
      (h₄ ∪ h₃) := hR
  have ha : avail (XG (upd G 0 (⟨.holds, Heap.empty, h₁⟩, .none, .wt))) = true := by
    cases h : avail (XG (upd G 0 (⟨.holds, Heap.empty, h₁⟩, .none, .wt)))
    · exfalso; rw [h] at hR'
      have := congrFun hR' (0, 24)
      simp only [Heap.union_apply, Heap.empty, Option.or_eq_none_iff] at this
      exact msg_cell hm this.2
    · rfl
  have hX' : XG (upd G 0 (⟨.holds, Heap.empty ∪ h₃, h₂⟩, .none, .got)) =
      upd (XG (upd G 0 (⟨.holds, Heap.empty, h₁⟩, .none, .wt))) 0 .got := by
    rw [XG_upd, XG_upd, upd_upd]
  have hx0 : XG (upd G 0 (⟨.holds, Heap.empty, h₁⟩, .none, .wt)) 0 = .wt := by
    simp only [XG, upd_self]
  refine U_retag hu (by
      rw [hX']
      refine shape_set hu.shape (shape_wt hu.shape hx0).2 .got (fun _ => .inr (.inl rfl))
        (fun h => by cases h) (.inl rfl) fun _ => ?_
      rw [upd_ne _ _ (by decide)]
      simp only [avail, Bool.and_eq_true] at ha
      exact ha.1)
    (by show Msg 2 (Heap.empty ∪ h₃); rw [Heap.empty_union]; exact hm) (fun h => by cases h)

/-- `post` by the producer at `pr 2`, with the message `h₃`: the permit becomes free. -/
theorem hmv_p {h₃ : Heap} (hm : Msg 2 h₃) : ∀ G m hL,
    proto.inv (upd G 1 (⟨.holds, Heap.empty ∪ h₃, hL⟩, .pst, .pr 2)) m →
    S.pv (upd (Sem.xs fun u => (upd G 1 (⟨.holds, Heap.empty ∪ h₃, hL⟩, .pst, .pr 2) u).2) 1 .pd) =
      S.pv (Sem.xs fun u => (upd G 1 (⟨.holds, Heap.empty ∪ h₃, hL⟩, .pst, .pr 2) u).2) + 1 ∧
    (S.pv (Sem.xs fun u => (upd G 1 (⟨.holds, Heap.empty ∪ h₃, hL⟩, .pst, .pr 2) u).2)).toNat
      + 1 < 2 ^ 64 ∧
    ∀ hr, S.Res (Sem.xs fun u => (upd G 1 (⟨.holds, Heap.empty ∪ h₃, hL⟩, .pst, .pr 2) u).2) hr →
      Heap.Disjoint h₃ hr →
      S.Res (upd (Sem.xs fun u => (upd G 1 (⟨.holds, Heap.empty ∪ h₃, hL⟩, .pst, .pr 2) u).2) 1
        .pd) (h₃ ∪ hr) := by
  intro G m hL hi
  have hu := hi.2.2
  have hx1 : XG (upd G 1 (⟨.holds, Heap.empty ∪ h₃, hL⟩, .pst, .pr 2)) 1 = .pr 2 := by
    simp only [XG, upd_self]
  have hy : avail (XG (upd G 1 (⟨.holds, Heap.empty ∪ h₃, hL⟩, .pst, .pr 2))) = false := by
    unfold avail; rw [hx1]; rfl
  have htk : (XG (upd G 1 (⟨.holds, Heap.empty ∪ h₃, hL⟩, .pst, .pr 2)) 0).took = false := by
    obtain ⟨-, ⟨-, h0, -⟩ | ⟨-, -, -, -, ht, -⟩⟩ := hu.shape
    · rw [h0]; rfl
    · cases e : (XG (upd G 1 (⟨.holds, Heap.empty ∪ h₃, hL⟩, .pst, .pr 2)) 0).took
      · rfl
      · have := ht e; rw [hx1] at this; cases this
  have hn : avail (upd (XG (upd G 1 (⟨.holds, Heap.empty ∪ h₃, hL⟩, .pst, .pr 2))) 1 .pd) = true := by
    simp only [avail, upd_self, upd_ne _ _ (by decide : (0 : Nat) ≠ 1), htk]; rfl
  have hxs : (Sem.xs fun u => (upd G 1 (⟨.holds, Heap.empty ∪ h₃, hL⟩, .pst, .pr 2) u).2) =
      XG (upd G 1 (⟨.holds, Heap.empty ∪ h₃, hL⟩, .pst, .pr 2)) := rfl
  rw [hxs]
  refine ⟨?_, ?_, fun hr hR _ => ?_⟩
  · show (if avail _ then (1 : BitVec 64) else 0) = (if avail _ then (1 : BitVec 64) else 0) + 1
    rw [hn, hy]; rfl
  · show (if avail _ then (1 : BitVec 64) else 0).toNat + 1 < _
    rw [hy]; decide
  · have hR' : (if avail (XG (upd G 1 (⟨.holds, Heap.empty ∪ h₃, hL⟩, .pst, .pr 2))) then Msg 2
        else emp) hr := hR
    rw [hy] at hR'
    change hr = Heap.empty at hR'
    subst hR'
    show (if avail _ then Msg 2 else emp) (h₃ ∪ Heap.empty)
    rw [hn, Heap.union_empty]; exact hm

theorem hU_p (h₃ : Heap) : ∀ G m h₁ h₂,
    U (upd G 1 (⟨.holds, Heap.empty ∪ h₃, h₁⟩, .pst, .pr 2)) m →
    U (upd G 1 (⟨.holds, Heap.empty, h₂⟩, .pst, .pd)) m := by
  intro G m h₁ h₂ hu
  have hx1 : XG (upd G 1 (⟨.holds, Heap.empty ∪ h₃, h₁⟩, .pst, .pr 2)) 1 = .pr 2 := by
    simp only [XG, upd_self]
  have hX' : XG (upd G 1 (⟨.holds, Heap.empty, h₂⟩, .pst, .pd)) =
      upd (XG (upd G 1 (⟨.holds, Heap.empty ∪ h₃, h₁⟩, .pst, .pr 2))) 1 .pd := by
    rw [XG_upd, XG_upd, upd_upd]
  refine U_retag hu (by
      rw [hX']
      exact shape_set hu.shape (shape_pr hu.shape hx1).2.1 .pd (fun h => by cases h)
        (fun _ => .inr (.inl rfl)) (.inr rfl) fun _ => by rw [upd_self]; rfl)
    rfl (fun h => by cases h)

end Specs

/-! ## Out-of-code changes of a thread's place -/

/-- Thread `t`, out of the semaphore's code, goes to the ghost value `g` with the same permit
state; its part stays, or it ends with no part. -/
theorem inv_ghost {G : ThreadId → Gh} {m : Mem} {t : ThreadId} {h : Heap} {x : Ph} {g : Gh}
    (hi : proto.inv (upd G t (⟨.out, h, Heap.empty⟩, .none, x)) m)
    (hg : g.1 = ⟨.out, h, Heap.empty⟩ ∨ (g.1 = ⟨.gone, Heap.empty, Heap.empty⟩ ∧ h = Heap.empty))
    (hg2 : g.2.1 = .none)
    (hav : avail (upd (XG G) t g.2.2) = avail (upd (XG G) t x))
    (hsh : Shape (upd (XG G) t g.2.2) m) (hpt : PartOk g.2.2 g.1.part) :
    proto.inv (upd G t g) m := by
  obtain ⟨hl, hs, hu⟩ := hi
  have hR : ∀ hL, S.L.R (upd G t (⟨.out, h, Heap.empty⟩, .none, x)) hL →
      S.L.R (upd (upd G t (⟨.out, h, Heap.empty⟩, .none, x)) t g) hL := by
    intro hL hR
    rw [upd_upd]
    change (pts S.ptr 8 (if avail (XG (upd G t _)) then (1 : BitVec 64) else 0) ∗
      (if avail (XG (upd G t _)) then Msg 2 else emp)) hL at hR
    change (pts S.ptr 8 (if avail (XG (upd G t g)) then (1 : BitVec 64) else 0) ∗
      (if avail (XG (upd G t g)) then Msg 2 else emp)) hL
    rw [XG_upd] at hR ⊢
    rw [hav]; exact hR
  have hl' := hl.ghost (t := t) (g := g) (by rw [upd_self]; rfl)
    (by rcases hg with h' | ⟨h', -⟩ <;> simp [Lock.prod, h'])
    (by rw [upd_self]; rcases hg with h' | ⟨h', rfl⟩ <;> simp [Lock.prod, h'])
    (by rcases hg with h' | ⟨h', -⟩ <;> simp [Lock.prod, h'])
    (fun _ => hl.live t (by rw [upd_self]; exact (by decide : LPh.out ≠ LPh.gone))) hR
  rw [upd_upd] at hl'
  have hs' : S.Inv (upd G t g) m := by
    have := hs.congrG (G' := upd G t g) (fun u => by
      by_cases e : u = t
      · subst e; rw [upd_self, upd_self, hg2]
      · rw [upd_ne _ _ e, upd_ne _ _ e]) (fun u => by
      by_cases e : u = t
      · subst e; rw [upd_self, upd_self]; rcases hg with h' | ⟨h', -⟩ <;> simp [h']
      · rw [upd_ne _ _ e, upd_ne _ _ e]) (fun u y h1 h2 => by
      by_cases e : u = t
      · subst e; rw [upd_self]; exact partOk_off hpt (by simp [S] at h2; omega)
      · rw [upd_ne _ _ e]; have := hs.off u y h1 h2; rwa [upd_ne _ _ e] at this)
    exact this
  exact ⟨hl', hs', U_retag hu (by rw [XG_upd]; exact hsh) hpt (fun h' => by rw [hg2] at h'; cases h')⟩

/-! ## The producer -/

section Proofs

variable {waitOp postOp : Ptr → Io → ConcM Tgt Unit} (C : SemContract S waitOp postOp)

/-- A thread out of the semaphore's code, with part `h`, at place `x`. -/
def gK (h : Heap) (x : Ph) : Gh := (⟨.out, h, Heap.empty⟩, .none, x)

theorem shape_of {G : ThreadId → Gh} {m : Mem} {t : ThreadId} {g : Gh}
    (hi : proto.inv (upd G t g) m) : Shape (upd (XG G) t g.2.2) m := by
  have := hi.2.2.shape; rwa [XG_upd] at this

/-- The producer's place goes from `pr k` to `p`. -/
theorem shape_kid {G : ThreadId → Gh} {m : Mem} {k : Nat} {p : Ph}
    (hp : p = .fin ∨ p = .pd ∨ ∃ k ≤ 2, p = .pr k)
    (hpost : (upd (XG G) 1 p 0).took = true → (upd (XG G) 1 p 1).posted = true)
    (hs : Shape (upd (XG G) 1 (.pr k)) m) : Shape (upd (XG G) 1 p) m := by
  have := shape_set hs (shape_pr hs (upd_self _ _ _)).2.1 p (fun h => by cases h) (fun _ => hp)
    (.inr rfl) (by rw [upd_upd]; exact hpost)
  rwa [upd_upd] at this

/-- The producer's place `pr k` is not posted, so `main` has not taken the permit. -/
theorem took_pr {X : ThreadId → Ph} {m : Mem} {k : Nat} (hs : Shape (upd X 1 (.pr k)) m) :
    (X 0).took = false := by
  obtain ⟨-, ⟨-, h0, -⟩ | ⟨-, -, -, -, ht, -⟩⟩ := hs
  · rw [upd_ne _ _ (by decide)] at h0; rw [h0]; rfl
  · rw [upd_ne _ _ (by decide), upd_self] at ht
    cases e : (X 0).took
    · rfl
    · have := ht e; cases this

include C in
theorem producer_spec (G : ThreadId → Gh) (m : Mem) (d : Nat) (h : Heap)
    (hi : proto.inv (upd G 1 (gK h (.pr 0))) m) (hc : m.current = 1) :
    proto.WP 1 (producer postOp cPtr) (fun _ G' m' _ => m'.current = 1 ∧
      proto.inv (upd G' 1 (gK Heap.empty .pd)) m') G m d := by
  unfold producer
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind]
  have hav : ∀ (X : ThreadId → Ph) (k k' : Nat), avail (upd X 1 (.pr k')) = avail (upd X 1 (.pr k)) :=
    fun X k k' => by simp [avail, Ph.posted]
  -- `a = 3`
  refine WP.bind (wp_msg (x' := .pr 1) (P₁ := Msg 0) (P₂ := Msg 1) (r₀ := ()) hi hc (fun h => h)
    (fun _ h => h)
    (by
      rw [Msg0, Msg1]
      exact ((TTriple.store (p := aPtr) (v := (0 : BitVec 32)) (by decide) 3).frame).conseq
        (fun _ h => h) (fun _ _ hq => sep_lift.mpr ⟨Subsingleton.elim _ _, hq⟩))
    (fun _ hm y hy => msg_off hm hy) (hav _ 0 1)
    (shape_kid (.inr (.inr ⟨1, by decide, rfl⟩)) (fun h => by
      rw [upd_ne _ _ (by decide)] at h; exact absurd h (by rw [took_pr (shape_of hi)]; decide)))
    fun m₁ h₁ hc₁ _ hi₁ => ?_)
  -- `b = 4`
  refine WP.bind (wp_msg (x' := .pr 2) (P₁ := Msg 1) (P₂ := Msg 2) (r₀ := ()) hi₁ hc₁ (fun h => h)
    (fun _ h => h)
    (by
      rw [Msg1, Msg2]
      exact ((TTriple.store (p := bPtr) (v := (0 : BitVec 32)) (by decide) 4).frameL).conseq
        (fun _ h => h) (fun _ _ hq => sep_lift.mpr ⟨Subsingleton.elim _ _, hq⟩))
    (fun _ hm y hy => msg_off hm hy) (hav _ 1 2)
    (shape_kid (.inr (.inr ⟨2, by decide, rfl⟩)) (fun h => by
      rw [upd_ne _ _ (by decide)] at h; exact absurd h (by rw [took_pr (shape_of hi₁)]; decide)))
    fun m₂ h₂ hc₂ _ hi₂ => ?_)
  -- `post`
  have hm₂ : Msg 2 h₂ := by have := hi₂.2.2.parts 1; simp only [XG, upd_self] at this; exact this
  exact WP.callC (WP.mono (fun _ G' m' _ ⟨_, hc', hi'⟩ => ⟨hc', hi'⟩)
    (C.post fits 1 Heap.empty h₂ (.pr 2) .pd ⟨⟩ trivial trivial (hmv_p hm₂) (hU_p h₂)
      (fun _ => .inl rfl) G m₂ d (by rw [Heap.empty_union]; exact hi₂)))

/-- The producer spawned no thread. -/
theorem joinedAll_kid {G : ThreadId → Gh} {m : Mem} {u : ThreadId} (hi : proto.inv G m)
    (hu : 0 < u) : joinedAll u m := by
  intro r hr hs
  obtain ⟨h0, h⟩ := hi.2.2.shape
  obtain ⟨i, hi', rfl⟩ := Array.mem_iff_getElem.mp hr
  have h0' : ∀ h : 0 < m.threads.size, (m.threads[0]'h).spawner = 0 := by
    intro h; rw [Array.getElem?_eq_getElem h] at h0; rw [Option.some.inj h0]
  rcases h with ⟨h1, -, -⟩ | ⟨h2, h1, -⟩
  · have : i = 0 := by omega
    subst this
    rw [h0' hi'] at hs; exact absurd hs (Nat.ne_of_lt hu)
  · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · rw [h0' hi'] at hs; exact absurd hs (Nat.ne_of_lt hu)
    · rw [Array.getElem?_eq_getElem hi'] at h1
      rw [Option.some.inj h1] at hs; exact absurd hs (Nat.ne_of_lt hu)

include C in
/-- The spawned producer keeps the protocol. -/
theorem dispatch_spec (tgt : Tgt) (g : Gh) (hg : proto.init tgt g) (u : ThreadId)
    (G : ThreadId → Gh) (m : Mem) (d : Nat) (hu : 0 < u) (hgu : G u = g) (hi : proto.inv G m) :
    proto.WP u (dispatch postOp tgt) (proto.QKid u) G { m with current := u } d := by
  cases tgt with
  | semWork p =>
    obtain ⟨rfl, h, rfl⟩ := hg
    have hx : XG G u = .pr 0 := by show (G u).2.2 = _; rw [hgu]
    obtain ⟨rfl, -, -⟩ := shape_pr hi.2.2.shape hx
    show proto.WP 1 (producer postOp cPtr) _ G _ d
    refine WP.mono ?_ (producer_spec C G _ d h (by
      rw [show gK h (.pr 0) = G 1 from hgu.symm, upd_same]; exact fits.cur 1 1 m.woken hi) rfl)
    rintro _ G' m' _ ⟨-, hi'⟩
    refine ⟨_, inv_ghost (g := (⟨.gone, Heap.empty, Heap.empty⟩, .none, .fin)) hi' (.inr ⟨rfl, rfl⟩)
      rfl (by unfold avail; rw [upd_self, upd_self, upd_ne _ _ (by decide), upd_ne _ _ (by decide)]; rfl)
      ?_ rfl, ⟨rfl, rfl⟩, fun _ => joinedAll_kid hi' hu⟩
    have hs := shape_of hi'
    have h2 : m'.threads.size = 2 := by
      obtain ⟨-, ⟨-, -, h1⟩ | ⟨h2, -⟩⟩ := hs
      · have := h1 1 (Nat.le_refl _); rw [upd_self] at this; cases this
      · exact h2
    have := shape_set hs h2 .fin (fun h => by cases h) (fun _ => .inl rfl) (.inr rfl)
      (fun _ => by rw [upd_upd, upd_self]; rfl)
    rwa [upd_upd] at this
  | producer p => cases hg
  | work p => cases hg
  | writer p => cases hg

end Proofs

end Sync.Mailbox
