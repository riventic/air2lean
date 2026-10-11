import ZigLean.Conc.Unroll
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

/-! ## `main` -/

theorem sem_size : (Enc.encode semZ).size = 24 := by decide +kernel
theorem sem_c : (Enc.encode semZ).extract 0 8 = Enc.encode (0 : BitVec 64) := by decide +kernel
theorem sem_w : (Enc.encode semZ).extract 8 12 = Enc.encode (0 : BitVec 32) := by decide +kernel
theorem sem_s : (Enc.encode semZ).extract 12 16 = Enc.encode (0 : BitVec 32) := by decide +kernel
theorem sem_e : (Enc.encode semZ).extract 16 20 = Enc.encode (0 : BitVec 32) := by decide +kernel

/-- `main` before its spawn, with the message cells `h`. -/
def gPre (h : Heap) : Gh := gK h .pre

/-- The start: no thread. -/
def G0 : ThreadId → Gh := fun _ => (⟨.gone, Heap.empty, Heap.empty⟩, .none, .none)

/-- The mailbox in three parts, after `main`'s stores: the semaphore, `a = 0`, `b = 0`. -/
def Parts (A : Nat) : Assn :=
  bytesAt cPtr A 32 .stack (Enc.encode semZ) ∗
    (bytesAt (cPtr.add 24) A 32 .stack (Enc.encode (0 : BitVec 32)) ∗
      bytesAt ((cPtr.add 24).add 4) A 32 .stack (Enc.encode (0 : BitVec 32)))

theorem allLe_one {m : Mem} {c : VClock} (h1 : m.threads.size = 1)
    (h : VClock.le c (m.clocks[0]!) = true) : AllLe m c := fun u hu => by
  rw [h1] at hu
  have : u = 0 := by omega
  subst this; exact h

/-- Before the spawn: `main` alone owns the mailbox. The semaphore starts with no permit: its
mutex owns the permit count; `main` keeps the message cells; the rest belongs to no thread. -/
theorem inv_pre {m : Mem} {A : Nat} {h : Heap} (ho : Owned (upd (fun _ => Heap.empty) 0 h) m)
    (hp : Parts A h) (hA : A % 8 = 0) (hth : m.threads = #[{ spawner := 0, joined := true }])
    (hat : m.atomics = #[]) (hq : m.waiters = #[]) :
    ∃ hM, Msg 0 hM ∧ proto.inv (upd G0 0 (gPre hM)) m := by
  obtain ⟨hS, h2, dS, rfl, hs, ha, hb, dAB, rfl, hwa, hwb⟩ := hp
  obtain ⟨hC, hR1, dC, rfl, hC₁, hR1'⟩ := bytesAt_split hs (k := 8) (by rw [sem_size]; decide)
  obtain ⟨hW, hCo, dW, rfl, hW₁, -⟩ := bytesAt_split hR1' (k := 4) (by simp [sem_size])
  have hsub := ho.sub 0; rw [upd_self] at hsub
  have h1 : m.threads.size = 1 := by rw [hth]; rfl
  have sS : (hC ∪ (hW ∪ hCo)).Sub m.heap := Heap.sub_union_left.trans hsub
  -- block 0 and its bytes
  obtain ⟨blk, hblk, hl, hA', hS', hK', hxs⟩ := bytesAt_blk (m := m) hs sS rfl
    (by rw [sem_size]; decide)
  have hbk : BlkOk m := ⟨blk, hblk, hl, hS', by rw [hA']; exact hA, hK'⟩
  have hword : ∀ o, o + 4 ≤ 24 → blk.bytes.extract o (o + 4) =
      (Enc.encode semZ).extract o (o + 4) := by
    intro o h2
    have := congrArg (fun a => Array.extract a o (o + 4)) hxs
    simp only [Array.extract_extract] at this
    rw [← this]
    simp only [show cPtr.off.toNat = 0 from rfl, sem_size]
    congr 1 <;> omega
  -- each access to a byte of `main`'s part happened before `main`
  have hown : ∀ e ∈ m.footprint, e.Touches ((hC ∪ (hW ∪ hCo)) ∪ (ha ∪ hb)) →
      AllLe m e.clock := fun e he ht => allLe_one h1 (by
    have := ho.owns 0 (by rw [h1]; decide) e he (.inl (by rw [upd_self]; exact ht)); exact this)
  have hcellS : ∀ x, x < 24 → ((hC ∪ (hW ∪ hCo)) ∪ (ha ∪ hb)) (0, x) ≠ none :=
    fun x hx => Heap.sub_union_left.ne
      (bytesAt_in hs rfl (by simp [cPtr]) (by simp [cPtr, sem_size]; omega))
  have hwi : ∀ W : Word 32 4, W.b = 0 → W.o % 4 = 0 → 12 ≤ W.o → W.o + 4 ≤ 20 →
      (Enc.encode semZ).extract W.o (W.o + 4) = Enc.encode (0 : BitVec 32) →
      W.Ok m ∧ (W.hist m).size = 1 ∧ (W.hist m)[0]!.Val (0 : BitVec 32) :=
    fun W hb h4 h1' h2' he =>
    Sem.word_init hb hblk hl (by omega) (by rw [hA']; omega) hK' hat
      (by rw [hword W.o (by omega), he]; exact intOfBytes_rmw 0)
      (fun e he' hh => hown e he' (Word.touches_of hh fun x a b => by
        rw [hb]; exact hcellS x (by omega)))
  obtain ⟨hwsOk, hwsz, hwsv⟩ := hwi S.WS rfl (by decide) (by decide) (by decide) sem_s
  obtain ⟨hweOk, hwez, -⟩ := hwi S.WE rfl (by decide) (by decide) (by decide) sem_e
  have hno : ∀ i l, ¬ S.WE.Loc m i l := fun i l hl => by
    have := (Word.loc_get hl).1; rw [hat] at this; simp at this
  have hE0 : (S.WE.hist m)[0]!.clock = #[] := by rw [Word.hist_none hno]; rfl
  have hcellW : ∀ x, 8 ≤ x → x < 8 + 4 → hW (0, x) ≠ none := fun x h1 h2 =>
    bytesAt_in hW₁ rfl (by simp [cPtr, Ptr.add]; omega)
      (by simp [cPtr, Ptr.add, sem_size]; omega)
  have h0 : S.L.U32 m 0 := by
    show (intOfBytes 32 (curBytes m 0 8 4)).run = _
    unfold curBytes; rw [hblk]
    simp only [Option.map_some, Option.getD_some]
    rw [hword 8 (by decide), sem_w]
    exact intOfBytes_rmw 0
  -- `main` keeps the message; the mutex owns the permit count
  obtain ⟨dCW, -⟩ := Heap.disjoint_union_right.mp dC
  obtain ⟨dCM, dWCoM⟩ := Heap.disjoint_union_left.mp dS
  obtain ⟨dWM, -⟩ := Heap.disjoint_union_left.mp dWCoM
  have hsub' : ((ha ∪ hb) ∪ (hC ∪ hW)).Sub ((hC ∪ (hW ∪ hCo)) ∪ (ha ∪ hb)) := by
    refine Heap.union_sub (Heap.sub_union_right dS) (Heap.union_sub ?_ ?_)
    · exact Heap.sub_union_left.trans Heap.sub_union_left
    · exact (Heap.sub_union_left.trans (Heap.sub_union_right dC)).trans Heap.sub_union_left
  have ho' := ho.shrink (t := 0) (by rw [upd_self]; exact hsub')
  rw [upd_upd] at ho'
  have hGu : ∀ u, u ≠ 0 → upd G0 0 (gPre (ha ∪ hb)) u = G0 u := fun u h => upd_ne _ _ h
  have hjt : joinedB m 0 = false := rfl
  have hpC : pts S.ptr 8 (0 : BitVec 64) hC :=
    ⟨A, 32, .stack, _, by simp [S, Sem.ptr]; omega, by rw [sem_c]; exact LawfulEnc.size_encode _,
      by rw [sem_c]; exact LawfulEnc.decode_encode _, hC₁, by decide⟩
  have hM : Msg 0 (ha ∪ hb) := by
    rw [Msg0]
    exact ⟨ha, hb, dAB, rfl,
      ⟨A, 32, .stack, Enc.encode (0 : BitVec 32), by simp [aPtr, cPtr, Ptr.add]; omega, enc_u32 0,
        LawfulEnc.decode_encode _, hwa, by decide⟩,
      ⟨A, 32, .stack, Enc.encode (0 : BitVec 32), by simp [bPtr, cPtr, Ptr.add]; omega, enc_u32 0,
        LawfulEnc.decode_encode _, hwb, by decide⟩⟩
  have hav0 : avail (XG (upd G0 0 (gPre (ha ∪ hb)))) = false := rfl
  have hR : S.L.R (upd G0 0 (gPre (ha ∪ hb))) hC := by
    change (pts S.ptr 8 (if avail (XG (upd G0 0 (gPre (ha ∪ hb)))) then (1 : BitVec 64) else 0) ∗
      (if avail (XG (upd G0 0 (gPre (ha ∪ hb)))) then Msg 2 else emp)) hC
    rw [hav0]
    exact ⟨hC, Heap.empty, Heap.disjoint_empty _, (Heap.union_empty hC).symm, hpC, rfl⟩
  refine ⟨ha ∪ hb, hM, Inv.make (t := 0) (hL := hC) (hW := hW) ho' hjt (fun u hu => ?_)
    (by rw [upd_self]; rfl) (by rw [upd_self]; exact Heap.disjoint_union_right.mpr ⟨dCM.symm, dWM.symm⟩)
    dCW (fun u => ?_) (fun u => ?_) hR hcellW
    ⟨blk, hblk, hl, by rw [hS']; decide, by show (blk.addr + 8) % 4 = 0; rw [hA']; omega,
      by rw [hK']; decide⟩ h0 (by rw [hat]; simp) hq (fun u hu => ?_) (by rw [h1]; decide),
    Sem.Inv.start (S := S) hwsOk hweOk hwsz hwsv hwez (by rw [hE0]; exact Sem.allLe_nil m)
      (fun u => by unfold upd; split <;> rfl) (fun w hw => by rw [hq] at hw; simp at hw)
      (fun u x _ h2 => ?_),
    ⟨⟨by rw [hth]; rfl, .inl ⟨h1, by simp only [XG, upd_self]; rfl,
      fun u hu => by simp only [XG]; rw [hGu u (by unfold ThreadId at *; omega)]; rfl⟩⟩,
      fun u => ?_, hbk, fun w hw => by rw [hq] at hw; simp at hw,
      fun u hu => by unfold upd at hu; split at hu <;> cases hu⟩⟩
  · rw [upd_ne _ _ hu]
    unfold Lock.own; rw [hGu u hu]; split <;> rfl
  · by_cases hu : u = 0
    · subst hu; rw [upd_self]; exact .inl ⟨rfl, by rw [h1]; decide, rfl⟩
    · rw [hGu u hu]; exact .inr rfl
  · by_cases hu : u = 0
    · subst hu; rw [upd_self]; rfl
    · rw [hGu u hu]; rfl
  · have : u = 0 := by rw [h1] at hu; omega
    subst this; exact VClock.le_refl _
  · by_cases hu : u = 0
    · subst hu; rw [upd_self]; exact msg_off hM (by simp [S] at h2; omega)
    · rw [hGu u hu]; rfl
  · by_cases hu : u = 0
    · subst hu; simp only [XG, upd_self]; exact hM
    · simp only [XG]; rw [hGu u hu]; rfl

include C in
theorem main_spec (σ : Placement) (io : Io) (d : Nat) :
    proto.WP 0 (mailMain waitOp io) QM G0 { mem0 σ with current := 0 } d := by
  unfold mailMain
  -- the mailbox: block 0
  refine WP.bind (WP.liftMem_owned (own := fun _ => Heap.empty) (TTriple.alloc .stack 32 8 (by decide))
    (Owned.start rfl rfl) rfl (by simp [mem0, Mem.ofGlobals]) rfl fun s1 m₁ h₁ hr₁ ho₁ hq₁ hs₁ hm₁ hd₁ => ?_)
  obtain ⟨rfl, -⟩ := alloc_ok hr₁
  obtain ⟨A, hA⟩ := hq₁
  obtain ⟨⟨-, hA8⟩, hb₁⟩ := sep_lift.mp hA
  have hc₁ : m₁.current = 0 := hs₁.current
  rw [show (⟨some ({ mem0 σ with current := 0 } : Mem).blocks.size, 0⟩ : Ptr) = cPtr from rfl] at hb₁ ⊢
  -- its three parts
  obtain ⟨hS, hR₁, dS, rfl, hS₁, hR₁'⟩ := bytesAt_split hb₁ (k := 24) (by simp)
  obtain ⟨ha, hb, dAB, rfl, ha₁, hb₁'⟩ := bytesAt_split hR₁' (k := 4) (by simp)
  have hsS : ((Array.replicate 32 Byte.undef).extract 0 24).size = 24 := by simp
  have hsA : (((Array.replicate 32 Byte.undef).extract 24).extract 0 4).size = 4 := by simp
  have hsB : (((Array.replicate 32 Byte.undef).extract 24).extract 4).size = 4 := by simp
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind]
  -- the semaphore, `a`, `b`
  have ho₁' : Owned (upd (fun _ => Heap.empty) 0 (hS ∪ (ha ∪ hb))) m₁ := ho₁
  have F₁ : (bytesAt cPtr A 32 .stack ((Array.replicate 32 Byte.undef).extract 0 24) ∗
      (bytesAt (cPtr.add 24) A 32 .stack (((Array.replicate 32 Byte.undef).extract 24).extract 0 4) ∗
        bytesAt ((cPtr.add 24).add 4) A 32 .stack
          (((Array.replicate 32 Byte.undef).extract 24).extract 4)))
      (hS ∪ (ha ∪ hb)) := ⟨hS, ha ∪ hb, dS, rfl, hS₁, ha, hb, dAB, rfl, ha₁, hb₁'⟩
  refine WP.bind (WP.liftM_owned ((TTriple.storeAt' (p := cPtr) (A := A) (S := 32) (K := .stack)
    (k := 0) (a := 8) semZ (by rw [sem_size]; rfl) rfl (by decide) (by rw [hsS]; decide)
    (by simp [cPtr]; omega) (by decide)).frame) ho₁' hc₁ (by rw [hs₁.threads]; simp [mem0, Mem.ofGlobals])
    (by rw [upd_self]; exact F₁) fun _ m₂ h₂ _ ho₂ F₂ hs₂ _ _ => ?_)
  rw [upd_upd] at ho₂
  refine WP.bind (WP.liftM_owned ((TTriple.storeAt (p := cPtr.add 24) (A := A) (S := 32)
    (K := .stack) (k := 0) (a := 4) (0 : BitVec 32) rfl (by decide) (by rw [hsA]; decide)
    (by simp [cPtr, Ptr.add]; omega) (by decide)).frame.frameL) ho₂
    (hs₂.current.trans hc₁) (by rw [hs₂.threads, hs₁.threads]; simp [mem0, Mem.ofGlobals]) (by rw [upd_self]; exact F₂)
    fun _ m₃ h₃ _ ho₃ F₃ hs₃ _ _ => ?_)
  rw [upd_upd] at ho₃
  refine WP.bind (WP.liftM_owned ((TTriple.storeAt (p := (cPtr.add 24).add 4) (A := A) (S := 32)
    (K := .stack) (k := 0) (a := 4) (0 : BitVec 32) rfl (by decide) (by rw [hsB]; decide)
    (by simp [cPtr, Ptr.add]; omega) (by decide)).frameL.frameL) ho₃
    (hs₃.current.trans (hs₂.current.trans hc₁))
    (by rw [hs₃.threads, hs₂.threads, hs₁.threads]; simp [mem0, Mem.ofGlobals]) (by rw [upd_self]; exact F₃)
    fun _ m₄ h₄ _ ho₄ F₄ hs₄ _ _ => ?_)
  rw [upd_upd] at ho₄
  have hth₄ : m₄.threads = #[{ spawner := 0, joined := true }] := by
    rw [hs₄.threads, hs₃.threads, hs₂.threads, hs₁.threads]; rfl
  have hat₄ : m₄.atomics = #[] := by rw [hs₄.atomics, hs₃.atomics, hs₂.atomics, hs₁.atomics]; rfl
  have hq₄ : m₄.waiters = #[] := by rw [hs₄.waiters, hs₃.waiters, hs₂.waiters, hs₁.waiters]; rfl
  have hP : Parts A h₄ := by
    rw [writeBytes_all (by rw [hsS, sem_size]), writeBytes_all (by rw [hsA, enc_u32]),
      writeBytes_all (by rw [hsB, enc_u32])] at F₄
    exact F₄
  obtain ⟨hM, hM0, hiP⟩ := inv_pre ho₄ hP hA8 hth₄ hat₄ hq₄
  -- the spawn: the producer gets the message cells
  refine WP.bind (WP.spawnC fun k _ => ⟨gPre hM, hiP, fun G₁ m₅ hg₁ hi₅ =>
    ⟨gK hM (.pr 0), ⟨rfl, hM, rfl⟩, fun child m₆ hf => ?_⟩⟩)
  obtain ⟨hl₅, hs₅, hu₅⟩ := hi₅
  obtain ⟨h00, ⟨hs1, -, hnone⟩ | ⟨-, -, h0, -⟩⟩ := hu₅.shape
  rotate_left
  · exfalso; rcases h0 with h0 | h0 | h0 <;> change (G₁ 0).2.2 = _ at h0 <;> rw [hg₁] at h0 <;>
      cases h0
  have hcs₅ : m₅.clocks.size = 1 := by rw [hl₅.own.csize, hs1]
  have hk : ∀ W : Word 32 4, W.Keep m₅ m₆ := fun _ =>
    Word.keep_fork (t := 0) (by rw [hs1]; decide) (by rw [hcs₅, hs1]) hf
  obtain ⟨hch, hm₆⟩ := Lock.fork_eq hf
  rw [hs1] at hch
  subst hch hm₆
  obtain ⟨hcl, hcn, -⟩ := Lock.fork_clocks (cs := m₅.clocks) (t := 0) (by rw [hcs₅]; decide)
  have hg1 : (G₁ 1).1.ph = .gone := by
    by_cases e : (G₁ 1).1.ph = .gone
    · exact e
    · exact absurd (hl₅.live 1 e).1 (by rw [hs1]; decide)
  have hX1 : (G₁ 1).2.2 = .none := hnone 1 (Nat.le_refl _)
  have h1n : (G₁ 1).2.1 = .none := by
    cases e : (G₁ 1).2.1 with
    | none => rfl
    | reg i jr sn e' =>
      have := hu₅.wx 1 (by rw [e]; rfl); rw [hX1] at this; cases this
    | _ => have := hs₅.crit 1 (by rw [e]; rfl); rw [hg1] at this; cases this
  have hGo : ∀ u, 2 ≤ u → upd (upd G₁ 1 (gK hM (.pr 0))) 0 (gK Heap.empty .wt) u = G₁ u :=
    fun u hu => by
      rw [upd_ne _ _ (by unfold ThreadId at *; omega), upd_ne _ _ (by unfold ThreadId at *; omega)]
  have hav₁ : avail (XG G₁) = false := by
    unfold avail; rw [show XG G₁ 1 = .none from hX1]; rfl
  have hav₆ : avail (XG (upd (upd G₁ 1 (gK hM (.pr 0))) 0 (gK Heap.empty .wt))) = false := rfl
  have hi₆ : proto.inv (upd (upd G₁ 1 (gK hM (.pr 0))) 0 (gK Heap.empty .wt))
      { m₅ with
        current := 0
        clocks := (m₅.clocks.set! 0 (VClock.bump (m₅.clocks[0]!) 0)).push
          (VClock.bump (m₅.clocks[0]!) 0)
        threads := m₅.threads.push { spawner := 0, joined := false } } := by
    refine ⟨hl₅.fork (t := 0) (by rw [hg₁]; rfl) hf (by rw [hg₁]; exact (Heap.empty_union hM).symm)
        (fun _ => .inl rfl) rfl rfl rfl rfl fun hL hR => ?_, ?_,
      ⟨⟨?_, .inr ⟨by simp [hs1], ?_, .inl ?_, .inr (.inr ⟨0, by decide, ?_⟩),
        fun h => ?_, fun u hu => ?_⟩⟩, fun u => ?_, hu₅.blk, hu₅.q, fun u hu => ?_⟩⟩
    · change (pts S.ptr 8 (if avail (XG G₁) then (1 : BitVec 64) else 0) ∗
        (if avail (XG G₁) then Msg 2 else emp)) hL at hR
      change (pts S.ptr 8 (if avail (XG (upd (upd G₁ 1 (gK hM (.pr 0))) 0 (gK Heap.empty .wt)))
        then (1 : BitVec 64) else 0) ∗
        (if avail (XG (upd (upd G₁ 1 (gK hM (.pr 0))) 0 (gK Heap.empty .wt))) then Msg 2
          else emp)) hL
      rw [hav₆]; rw [hav₁] at hR; exact hR
    · refine (hs₅.mono (hs₅.ws.keep (hk _)) (hs₅.we.keep (hk _)) (Word.hist_keep hs₅.ws (hk _))
        (Word.hist_keep hs₅.we (hk _)) (fun u => ?_) (fun c ⟨i, l, h1, h2⟩ => ⟨i, l, h1, h2⟩)
        (fun h => .inl h) (fun w hw _ => .inl hw) (fun c h u hu => ?_)).congrG (fun u => ?_)
        (fun u => ?_) (fun u x h1 h2 => ?_)
      · by_cases hu : u < m₅.clocks.size
        · exact hcl u hu
        · rw [getElem!_neg m₅.clocks u hu]
          exact VClock.le_iff.mpr fun i => by show (#[] : Array Nat).getD i 0 ≤ _; simp
      · simp only [Array.size_push, hs1] at hu
        rcases (by omega : u = 0 ∨ u = 1) with rfl | rfl
        · exact VClock.le_trans (h 0 (by rw [hs1]; decide)) (hcl 0 (by rw [hcs₅]; decide))
        · rw [← hcs₅]; exact VClock.le_trans (h 0 (by rw [hs1]; decide)) hcn
      · by_cases e0 : u = 0
        · subst e0; rw [upd_self, hg₁]; rfl
        · by_cases e1 : u = 1
          · subst e1; rw [upd_ne _ _ (by decide), upd_self, h1n]; rfl
          · rw [upd_ne _ _ e0, upd_ne _ _ e1]
      · by_cases e0 : u = 0
        · subst e0; rw [upd_self, hg₁]; exact Iff.rfl
        · by_cases e1 : u = 1
          · subst e1; rw [upd_ne _ _ (by decide), upd_self, hg1]
            simp [gK]
          · rw [upd_ne _ _ e0, upd_ne _ _ e1]
      · by_cases e0 : u = 0
        · subst e0; rw [upd_self]; rfl
        · by_cases e1 : u = 1
          · subst e1; rw [upd_ne _ _ (by decide), upd_self]
            exact msg_off hM0 (by simp [S] at h2; omega)
          · rw [upd_ne _ _ e0, upd_ne _ _ e1]; exact hs₅.off u x h1 h2
    · simp only [Array.getElem?_push]; rw [if_neg (by omega)]; exact h00
    · simp only [Array.getElem?_push, hs1, ↓reduceIte]
    · show (upd (upd G₁ 1 (gK hM (.pr 0))) 0 (gK Heap.empty .wt) 0).2.2 = _; rw [upd_self]; rfl
    · show (upd (upd G₁ 1 (gK hM (.pr 0))) 0 (gK Heap.empty .wt) 1).2.2 = _
      rw [upd_ne _ _ (by decide), upd_self]; rfl
    · have : (upd (upd G₁ 1 (gK hM (.pr 0))) 0 (gK Heap.empty .wt) 0).2.2.took = true := h
      rw [upd_self] at this; cases this
    · show (upd (upd G₁ 1 (gK hM (.pr 0))) 0 (gK Heap.empty .wt) u).2.2 = _
      rw [hGo u hu]; exact hnone u (by unfold ThreadId at *; omega)
    · by_cases e0 : u = 0
      · subst e0; simp only [XG, upd_self]; rfl
      · by_cases e1 : u = 1
        · subst e1; simp only [XG]; rw [upd_ne _ _ (by decide), upd_self]; exact hM0
        · simp only [XG]; rw [hGo u (by unfold ThreadId at *; omega)]
          have hn : (G₁ u).2.2 = .none := hnone u (by unfold ThreadId at *; omega)
          have := hu₅.parts u; simp only [XG] at this; rw [hn] at this ⊢; exact this
    · by_cases e0 : u = 0
      · subst e0; rw [upd_self] at hu; cases hu
      · by_cases e1 : u = 1
        · subst e1; rw [upd_ne _ _ (by decide), upd_self] at hu; cases hu
        · rw [hGo u (by unfold ThreadId at *; omega)] at hu ⊢; exact hu₅.wx u hu
  simp only [StateT.run_bind, StateT.run_pure]
  -- `wait`: `main` takes the permit and the message
  refine WP.bind (WP.callC (WP.mono ?_ (C.wait fits 0 Heap.empty .wt .got (Msg 2) io hone_w rfl
    trivial trivial hmv_w hU_w _ _ k hi₆)))
  rintro _ G₂ m₇ d₂ ⟨hd₂, hc₇, h₃, hm₃, hi₇⟩
  have hi₇' : proto.inv (upd G₂ 0 (gK (Heap.empty ∪ h₃) .got)) m₇ := hi₇
  -- the message: `a`, then `b`
  refine WP.bind (wp_msg (x' := .got) (P₁ := Msg 2) (P₂ := Msg 2) (r₀ := (3 : BitVec 32)) hi₇' hc₇
    (fun h => h) (fun _ h => h)
    (by rw [Msg2]; exact (TTriple.load (by decide)).frame_eq) (fun _ hm y hy => msg_off hm hy) rfl id
    fun m₈ h₈ hc₈ _ hi₈ => ?_)
  refine WP.bind (wp_msg (x' := .got) (P₁ := Msg 2) (P₂ := Msg 2) (r₀ := (4 : BitVec 32)) hi₈ hc₈
    (fun h => h) (fun _ h => h)
    (by rw [Msg2]; exact (TTriple.load (by decide)).frameL_eq) (fun _ hm y hy => msg_off hm hy) rfl id
    fun m₉ h₉ hc₉ _ hi₉ => ?_)
  -- the join of the producer
  have hs₉ := shape_of hi₉
  have h2₉ : m₉.threads.size = 2 := by
    obtain ⟨-, ⟨-, h0, -⟩ | ⟨h2, -⟩⟩ := hs₉
    · rw [upd_self] at h0; cases h0
    · exact h2
  have hpost : (upd (XG G₂) 0 Ph.got 1).posted = true := by
    obtain ⟨-, ⟨-, h0, -⟩ | ⟨-, -, -, -, ht, -⟩⟩ := hs₉
    · rw [upd_self] at h0; cases h0
    · exact ht (by rw [upd_self]; rfl)
  have hiJ : proto.inv (upd G₂ 0 (gK h₉ .joins)) m₉ :=
    inv_ghost (g := gK h₉ .joins) hi₉ (.inl rfl) rfl
      (by unfold avail; rw [upd_self, upd_self, upd_ne _ _ (by decide), upd_ne _ _ (by decide)]; rfl)
      (by
        have := shape_set hs₉ h2₉ .joins (fun _ => .inr (.inr rfl)) (fun h => by cases h) (.inl rfl)
          (fun _ => by rw [upd_upd, upd_ne _ _ (by decide)]; rw [upd_ne _ _ (by decide)] at hpost
                       exact hpost)
        rwa [upd_upd] at this)
      (by have := hi₉.2.2.parts 0; simp only [XG, upd_self] at this; exact this)
  refine WP.bind (WP.joinC fun k₂ hk₂ => ⟨gK h₉ .joins, hiJ, fun G₄ m₁₁ hg₄ hi₁₁ => ?_⟩)
  obtain ⟨h0₁₁, ⟨-, h0, -⟩ | ⟨hs2, hr1, -, -, -⟩⟩ := hi₁₁.2.2.shape
  · exfalso; change (G₄ 0).2.2 = _ at h0; rw [hg₄] at h0; cases h0
  refine ⟨fun _ => ⟨by decide, by rw [hs2]; decide, ⟨rfl, rfl⟩, by simp [Thread.joinValid, Mem.isGated, hr1]⟩,
    fun _ => ⟨fun _ => join_run (m := { m₁₁ with current := 0 }) hr1 rfl rfl, fun m₁₂ hj => ?_⟩⟩
  obtain ⟨rec, hrec, -, hm₁₂⟩ := join_eq hj
  refine WP.pure' ?_
  -- the free of the mailbox
  obtain ⟨blk₀, hblk₀, hl₀, -⟩ := hi₁₁.2.2.blk
  have hb₁₂ : m₁₂.blocks = m₁₁.blocks := by rw [hm₁₂]
  refine WP.bind (WP.liftMem (fun e he => (free_noErr (by rw [hb₁₂]; exact hblk₀) hl₀
      ((Mem.ClocksLe.join2 hj (by rw [hi₁₁.1.own.csize, hs2])).freeRaces _ _) e he).elim)
    fun _ m₁₃ hfr => ?_)
  obtain ⟨b', blk', -, -, rfl⟩ := free_ok hfr
  refine ⟨rfl, WP.pure' ⟨rfl, fun r hr hsp => ?_⟩⟩
  -- every thread is joined
  have hth₁₂ : m₁₂.threads = m₁₁.threads.set! 1 { rec with joined := true } := by rw [hm₁₂]
  simp only [hth₁₂] at hr
  obtain ⟨i, hi', rfl⟩ := Array.mem_iff_getElem.mp hr
  simp only [Array.size_set!] at hi'
  simp only [Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds hi'] at hsp ⊢
  split
  · rfl
  · rename_i hne
    have : i = 0 := by omega
    subst this
    rw [Array.getElem?_eq_getElem (by omega)] at h0₁₁
    rw [Option.some.inj h0₁₁]

end Proofs

/-! ## The results, for the translated `Io.Semaphore` -/

/-- The mailbox client with the translated std semaphore. -/
abbrev stdMain := mailMain Io_Semaphore_waitUncancelable

/-- The spawn targets with the translated std semaphore. -/
abbrev stdDispatch := dispatch Io_Semaphore_post

/-- **The consumer receives the whole message under every schedule**: every completed run of
the mailbox client returns 34 (every oracle, every fuel). -/
theorem mailbox_spec (env : Env) (henv : env.spawn = .available) {σ : Placement} {fuel : Nat} {o : Nat → Nat} {v : Except ErrName (BitVec 32)} {m : Mem}
    (io : Io) (h : (Sched.run env stdDispatch fuel o (stdMain io) (mem0 σ)).run = some (.ok (v, m))) :
    v = .ok 34 := by
  obtain ⟨_, _, hv, -⟩ := proto.run_sound env (Proto.of_available henv) stdDispatch G0 (dispatch_spec (semaphore S))
    (fun _ _ _ _ _ hq => hq.2) rfl (main_spec (semaphore S) σ io) h
  exact hv

/-- **No run of the mailbox client gives an error**: no data race on the message, no deadlock
(also when the consumer sleeps at the condition first), no lifetime error at the free. -/
theorem mailbox_safe (env : Env) (henv : env.spawn = .available) {σ : Placement} {fuel : Nat} {o : Nat → Nat} {e : Error} (io : Io) :
    (Sched.run env stdDispatch fuel o (stdMain io) (mem0 σ)).run ≠ some (.error e) :=
  proto.run_safe env (Proto.of_available henv) stdDispatch G0 rfl (dispatch_spec (semaphore S)) (fun _ _ _ _ hq => hq.2) rfl
    (main_spec (semaphore S) σ io)

/-- One schedule completes: under the oracle that always picks option 0, the mailbox client returns 34 within
fuel 1000, from `mem0` with the translation's spawn policy. The kernel computes the run, with
each loop cut after 10 iterations (`unroll_sched`, `ZigLean/Conc/Unroll.lean`). -/
theorem mailbox_completes :
    ∃ σ, Witness.okVal (Sched.run ⟨.any, .available⟩ stdDispatch 1000 (fun _ => 0) (stdMain ⟨⟩) (mem0 σ)) = some 34 :=
  ⟨.fresh, by unroll_sched 10⟩

end Sync.Mailbox
