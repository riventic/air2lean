import Proofs.Sync.Contracts

/-!
# A snapshot cache against the `Io.Mutex` contract (C14 client)

A model client written in Lean (it is not a Zig export): the cache is a block with an
`Io.Mutex` word (bytes 0..4) and two `u32` fields `a` (4..8) and `b` (8..12), with the
invariant `a + b = 10`. A writer thread does two updates `a += 1; b -= 1`, each under the
mutex; between its two stores the invariant is broken. `main` takes the mutex once, reads
`a` and `b`, releases it, joins the writer and returns `a + b`. The result is 10 under every
schedule (`cache_spec`) and no schedule gives an error (`cache_safe`): the reader always sees
a consistent snapshot, never the half-done update.

The client code takes the lock operations as parameters (`lk`, `ul`). Its proof uses only the
hypothesis `MutexContract lk ul` (`Proofs/Sync/Contracts.lean`) and the generic lock rules
(`ZigLean/Conc/Lock.lean`): it never unfolds the std implementation. The final theorems
instantiate `lk`, `ul` with the translated `Io_Mutex_lockUncancelable` / `Io_Mutex_unlock`
through `Sync.Contracts.mutex`.

- **The lock invariant** (`R`): `a = k (+1 while mid-update)`, `b = 10 - k`, with `k` the
  writer's finished updates. It depends only on the writer's ghost place.
- **Mid-update** (`U.mid`): a thread in the middle of an update holds the mutex, and such a
  thread runs no lock code (`ok`, `Lock.FitsOn`). So the holder `main` sees `mid = false`.
- **Ownership transfer**: `lock` moves the cache cells into the holder's `held` part, `unlock`
  moves them back (the contract's resource rule); `main` frees the block only after the join.

Scope: one reader, one writer, two updates; no fairness, no termination claim (partial
correctness and strict safety under every schedule of the model).
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Conc.Lock Sync Assn Sync.Contracts

namespace Sync.SnapshotCache

attribute [local irreducible] Proto.WP

/-! ## The code -/

section Code

variable (lk ul : Ptr → Io → ConcM Tgt Unit)

/-- One update of the cache under the mutex at `p`: `a += 1`, then `b -= 1`. -/
def update (p : Ptr) : CM Tgt Unit Unit := do
  callC (lk p ⟨⟩)
  let a ← Zig.load (BitVec 32) 4 (p.add 4)
  Zig.store (α := BitVec 32) 4 (p.add 4) (a + 1)
  let b ← Zig.load (BitVec 32) 4 (p.add 8)
  Zig.store (α := BitVec 32) 4 (p.add 8) (b - 1)
  callC (ul p ⟨⟩)

/-- The writer: two updates. -/
def writer (p : Ptr) : ConcM Tgt Unit :=
  (do update lk ul p; update lk ul p : CM Tgt Unit Unit).run' ()

/-- The spawn targets: `work p` runs the writer. -/
def dispatch : Tgt → ConcM Tgt Unit
  | .work p => writer lk ul p
  | _ => pure ()

/-- `main`: build the cache (`a = 0`, `b = 10`), spawn the writer, read a snapshot under the
mutex, join, free, and return `a + b`. -/
def cacheMain (io : Io) : ConcM Tgt (Except ErrName (BitVec 32)) := do
  let s1 ← Zig.allocStack 12 4
  let e ← ((do
    Zig.store (α := BitVec 32) 4 (s1.add 0) 0
    Zig.store (α := BitVec 32) 4 (s1.add 4) 0
    Zig.store (α := BitVec 32) 4 (s1.add 8) 10
    let t ← Zig.spawnC (Tgt.work s1)
    match t with
    | .error e => pure (.error e)
    | .ok tid => do
      callC (lk s1 io)
      let x ← Zig.load (BitVec 32) 4 (s1.add 4)
      let y ← Zig.load (BitVec 32) 4 (s1.add 8)
      callC (ul s1 io)
      Zig.joinC tid
      pure (.ok (x + y))) : CM Tgt Unit (Except ErrName (BitVec 32))).run' ()
  Zig.free s1
  pure e

end Code

/-! ## The protocol -/

/-- Where a thread is, outside the lock's code. -/
inductive Ph where
  | none
  /-- `main` before its spawn. -/
  | pre
  /-- `main` after its spawn, before its join. -/
  | run
  /-- `main` at its join. -/
  | joins
  /-- The writer after `k` updates; `mid`: it stored `a` of the next update, not yet `b`. -/
  | wk (k : Nat) (mid : Bool)
  /-- The writer has ended. -/
  | fin

/-- The writer's finished updates. -/
def Ph.cnt : Ph → Nat
  | .wk k _ => k
  | .fin => 2
  | _ => 0

/-- In the middle of an update. -/
def Ph.mid : Ph → Bool
  | .wk _ b => b
  | _ => false

abbrev Gh := LG × Ph

/-- The cache (block 0). -/
def cPtr : Ptr := ⟨some 0, 0⟩
def aPtr : Ptr := cPtr.add 4
def bPtr : Ptr := cPtr.add 8

/-- The value of `a`. -/
def aVal (x : Ph) : Nat := x.cnt + if x.mid then 1 else 0

/-- The lock invariant: `a = k (+1 mid-update)`, `b = 10 - k`, `k` the writer's updates. -/
def R (X : ThreadId → Ph) : Assn :=
  pts aPtr 4 (BitVec.ofNat 32 (aVal (X 1))) ∗ pts bPtr 4 (BitVec.ofNat 32 (10 - (X 1).cnt))

/-- The `Io.Mutex`: bytes 0..4 of block 0. It owns `a` and `b`. -/
abbrev L : Lock Gh := Lock.prod 0 0 R

/-- Only a thread that is not in the middle of an update runs the lock's code. -/
def ok (g : Gh) : Prop := g.2.mid = false

/-- The threads: `main` alone before its spawn; then `main` and the writer. -/
def Shape (X : ThreadId → Ph) (m : Mem) : Prop :=
  m.threads[0]? = some { spawner := 0, joined := true } ∧
  ((m.threads.size = 1 ∧ X 0 = .pre ∧ ∀ u, 1 ≤ u → X u = .none) ∨
   (m.threads.size = 2 ∧ m.threads[1]? = some { spawner := 0, joined := false } ∧
    (X 0 = .run ∨ X 0 = .joins) ∧
    (X 1 = .fin ∨ ∃ k ≤ 2, ∃ b, X 1 = .wk k b ∧ (b = true → k < 2)) ∧
    ∀ u, 2 ≤ u → X u = .none))

/-- Block 0 is the live cache: 12 bytes on the stack, 4-aligned. -/
def BlkOk (m : Mem) : Prop :=
  ∃ blk, m.blocks[0]? = some blk ∧ blk.live = true ∧ blk.bytes.size = 12 ∧ blk.addr % 4 = 0 ∧
    blk.kind = .stack

/-- The rest of the invariant. -/
structure U (G : ThreadId → Gh) (m : Mem) : Prop where
  shape : Shape (fun u => (G u).2) m
  parts : ∀ u, (G u).1.part = Heap.empty
  blk : BlkOk m
  mid : ∀ u, (G u).2.mid = true → (G u).1.ph = .holds

/-- The protocol, in strict mode. -/
def proto : Proto Tgt Gh where
  inv G m := L.Inv G m ∧ U G m
  init tgt g := match tgt with
    | .work p => p = cPtr ∧ g = (⟨.out, Heap.empty, Heap.empty⟩, .wk 0 false)
    | _ => False
  fin g := g.1.ph = .gone ∧ g.2 = .fin
  strict := true
  joins g := g.1.ph = .out ∧ g.2 = .joins

/-- `main`'s post: the result. -/
def QM : Except ErrName (BitVec 32) → (ThreadId → Gh) → Mem → Nat → Prop :=
  fun v _ m _ => v = .ok 10 ∧ joinedAll 0 m

/-! ## The protocol has the lock -/

theorem blk_heap {m : Mem} (hb : BlkOk m) {x : Nat} (hx : x < 12) : m.heap (0, x) ≠ none := by
  obtain ⟨blk, hblk, hl, hs, -⟩ := hb
  simp only [Mem.heap, hblk]
  rw [dite_eq_left_of_eq_true (eq_true ⟨hl, by omega⟩)]
  simp

theorem blk_keep {m m' : Mem} (hb : BlkOk m) (h : m'.heap (0, 0) = m.heap (0, 0)) : BlkOk m' := by
  obtain ⟨blk, hblk, hl, hs, ha, hk⟩ := hb
  have hc : m.heap (0, 0) = some ⟨blk.bytes[0]'(by omega), blk.addr, blk.bytes.size, blk.kind⟩ := by
    simp only [Mem.heap, hblk]; rw [dite_eq_left_of_eq_true (eq_true ⟨hl, by omega⟩)]
  rw [hc] at h
  obtain ⟨blk', hblk', hl', ho', he⟩ := Mem.heap_some h
  simp only [Cell.mk.injEq] at he
  obtain ⟨-, hA, hS, hK⟩ := he
  exact ⟨blk', hblk', by simpa using hl', by rw [← hS, hs], by rw [← hA, ha], by rw [← hK, hk]⟩

theorem stable (G : ThreadId → Gh) (m m' : Mem) (t : ThreadId) (p : LPh) (h : Heap)
    (hok : ok (G t)) (_ : L.ph (G t) ≠ .gone) (hu : U G m) (hs : L.Step t m m')
    (_ : L.ph (G t) = .holds → p ≠ .holds → L.Before m' (m.clocks[t]!)) :
    U (upd G t (L.set (G t) p h)) m' := by
  obtain ⟨hsh, hpart, hblk, hmid⟩ := hu
  refine ⟨?_, fun u => ?_, ?_, fun u hu' => ?_⟩
  · rw [snd_set]; unfold Shape at hsh ⊢; rw [hs.threads]; exact hsh
  · unfold upd; split
    · rename_i e; subst e; exact hpart u
    · exact hpart u
  · obtain ⟨blk, hb, hl, hsz, ha, hk⟩ := hblk
    rcases hs.blocks with e | ⟨blk', bs, h1, -, h3, h4, h5⟩
    · exact ⟨blk, by rw [e]; exact hb, hl, hsz, ha, hk⟩
    · have h1' : m.blocks[0]? = some blk' := h1
      rw [hb] at h1'; cases h1'
      refine ⟨{ blk with bytes := writeBytes blk.bytes 0 bs }, ?_, hl, ?_, ha, hk⟩
      · rw [h5]; show (m.blocks.set! 0 _)[0]? = _
        rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt
          (Array.getElem?_eq_some_iff.mp hb).1]; rfl
      · show (writeBytes blk.bytes 0 bs).size = 12
        rw [writeBytes_size _ _ _ (by rw [h3, hsz]; decide), hsz]
  · by_cases e : u = t
    · subst e
      rw [upd_self] at hu'
      exact absurd hu' (by change (G u).2.mid ≠ true; rw [show (G u).2.mid = false from hok]; decide)
    · rw [upd_ne _ _ e] at hu' ⊢; exact hmid u hu'

theorem fits : L.FitsOn proto U ok :=
  ⟨fun _ _ => Iff.rfl, fun _ h => h.1, fun _ h => h.1, fun _ _ _ => Iff.rfl, stable⟩

/-! ## The threads -/

theorem shape_wk {X : ThreadId → Ph} {m : Mem} {t k : Nat} {b : Bool} (h : Shape X m)
    (hx : X t = .wk k b) : t = 1 ∧ m.threads.size = 2 ∧ k ≤ 2 ∧ (b = true → k < 2) := by
  obtain ⟨-, ⟨-, h0, h1⟩ | ⟨hs, -, h0, h1, h2⟩⟩ := h
  · by_cases ht : t = 0
    · subst ht; rw [h0] at hx; cases hx
    · rw [h1 t (Nat.pos_of_ne_zero ht)] at hx; cases hx
  · have ht : t = 1 := by
      by_cases ht0 : t = 0
      · subst ht0; rcases h0 with h0 | h0 <;> rw [h0] at hx <;> cases hx
      · by_cases ht2 : 2 ≤ t
        · rw [h2 t ht2] at hx; cases hx
        · omega
    subst ht
    rcases h1 with h1 | ⟨k', hk, b', h1, hb⟩ <;> rw [h1] at hx <;> cases hx
    exact ⟨rfl, hs, hk, hb⟩

/-- The writer goes to `wk k' b'`, or to `fin`. -/
theorem shape_set {X : ThreadId → Ph} {m : Mem} {k : Nat} {b : Bool} (h : Shape X m)
    (hx : X 1 = .wk k b) (p : Ph)
    (hp : (∃ k' ≤ 2, ∃ b', p = .wk k' b' ∧ (b' = true → k' < 2)) ∨ p = .fin) :
    Shape (upd X 1 p) m := by
  obtain ⟨h00, ⟨-, -, h1⟩ | ⟨hs, hr, h0, -, h2⟩⟩ := h
  · rw [h1 1 (Nat.le_refl _)] at hx; cases hx
  refine ⟨h00, .inr ⟨hs, hr, ?_, ?_, fun u hu => ?_⟩⟩
  · rw [upd_ne _ _ (by decide)]; exact h0
  · rw [upd_self]
    rcases hp with ⟨k', hk, b', rfl, hb⟩ | rfl
    · exact .inr ⟨k', hk, b', rfl, hb⟩
    · exact .inl rfl
  · rw [upd_ne _ _ (by unfold ThreadId at *; omega)]; exact h2 u hu

/-- `main` goes from `run` to `joins`. -/
theorem shape_main {X : ThreadId → Ph} {m : Mem} (h : Shape X m) (hx : X 0 = .run ∨ X 0 = .joins)
    (p : Ph) (hp : p = .run ∨ p = .joins) : Shape (upd X 0 p) m := by
  obtain ⟨h00, ⟨-, h0, -⟩ | ⟨hs, hr, -, h1, h2⟩⟩ := h
  · rw [h0] at hx; rcases hx with hx | hx <;> cases hx
  refine ⟨h00, .inr ⟨hs, hr, ?_, ?_, fun u hu => ?_⟩⟩
  · rw [upd_self]; exact hp
  · rw [upd_ne _ _ (by decide)]; exact h1
  · rw [upd_ne _ _ (by unfold ThreadId at *; omega)]; exact h2 u hu

/-! ## A step of the holder on the cache -/

/-- A step of thread `t` on its own part keeps `U`, with `t`'s new ghost value `g`. -/
theorem U_stepIn {G : ThreadId → Gh} {m m' : Mem} {t : ThreadId} {g : Gh} {hQ : Heap}
    (hi : proto.inv G m) (hs : StepIn (m.heap.diff (L.own G m t)) m m')
    (hm' : m'.heap = hQ ∪ m.heap.diff (L.own G m t))
    (hd : Heap.Disjoint hQ (m.heap.diff (L.own G m t)))
    (hsh : Shape (upd (fun u => (G u).2) t g.2) m) (hpart : g.1.part = Heap.empty)
    (hmid : g.2.mid = true → g.1.ph = .holds) :
    U (upd G t g) m' := by
  have h0 : L.own G m t (0, 0) = none := hi.1.off t 0 (Nat.le_refl _) (by decide)
  have hrest : m.heap.diff (L.own G m t) (0, 0) = m.heap (0, 0) := by
    simp [Heap.diff, h0]
  refine ⟨?_, fun u => ?_, blk_keep hi.2.blk ?_, fun u hu => ?_⟩
  · rw [snd_upd]; unfold Shape at hsh ⊢; rw [hs.threads]; exact hsh
  · unfold upd; split
    · exact hpart
    · exact hi.2.parts u
  · rw [hm', Heap.union_of_right ((hd (0, 0)).resolve_right (by
      rw [hrest]; exact blk_heap hi.2.blk (by decide))), hrest]
  · by_cases e : u = t
    · subst e; rw [upd_self] at hu ⊢; exact hmid hu
    · rw [upd_ne _ _ e] at hu ⊢; exact hi.2.mid u hu

/-- A thread that holds the mutex, at place `x`, with the cache `h`. -/
def gH (x : Ph) (h : Heap) : Gh := (⟨.holds, Heap.empty, h⟩, x)

/-- A step `c` of the holder `t` on the cache (a load or a store of `a` or `b`): from place `x`
to `x'`, with the lock invariant before and after. -/
theorem wp_cache {σ β : Type} {c : MemM β} {s : σ} {t : ThreadId} {x x' : Ph} {hL : Heap}
    {G : ThreadId → Gh} {m : Mem} {d : Nat} {r₀ : β}
    (hi : proto.inv (upd G t (gH x hL)) m) (hc : m.current = t)
    (ht : TTriple (R (upd (fun u => (G u).2) t x)) c
      (fun r => ⌜r = r₀⌝ ∗ R (upd (fun u => (G u).2) t x')))
    (hsh : Shape (upd (fun u => (G u).2) t x') m)
    {Q : β × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ m' hQ, m'.current = t → m'.threads = m.threads →
      proto.inv (upd G t (gH x' hQ)) m' → Q (r₀, s) G m' d) :
    proto.WP t ((liftM c : CM Tgt σ β).run s) Q G m d := by
  have hh : L.ph (upd G t (gH x hL) t) = .holds := by rw [upd_self]; rfl
  obtain ⟨htl, hjt⟩ := hi.1.live t (by rw [hh]; decide)
  have hres : R (upd (fun u => (G u).2) t x) hL := by
    have := hi.1.res t hh
    rw [show L.held (upd G t (gH x hL) t) = hL by rw [upd_self]; rfl] at this
    change R (fun u => (upd G t (gH x hL) u).2) hL at this
    rwa [snd_upd] at this
  have hown : L.own (upd G t (gH x hL)) m t = hL := by
    rw [L.own_live hjt, upd_self]; exact Heap.empty_union hL
  refine WP.liftM_owned ht hi.1.own hc htl (by rw [hown]; exact hres)
    fun a m' hQ hr ho' hq hs hm' hd => ?_
  obtain ⟨rfl, hq'⟩ := sep_lift.mp hq
  have hQe : L.part (gH x' hQ) ∪ L.held (gH x' hQ) = hQ := Heap.empty_union hQ
  have hl := hi.1.stepIn (g := gH x' hQ) hc hjt (by rw [hQe]; exact ho') hs
    (by rw [hQe]; exact hm') (by rw [hQe]; exact hd) (by rw [upd_self]; rfl) (fun _ => .inl rfl)
    (fun h => absurd rfl h) (fun h => absurd hh h) (fun _ => by
      show R (fun u => (upd (upd G t (gH x hL)) t (gH x' hQ) u).2) hQ
      rw [upd_upd, snd_upd]; exact hq')
  rw [upd_upd] at hl
  refine h m' hQ (hs.current.trans hc) hs.threads ⟨hl, ?_⟩
  have := U_stepIn (g := gH x' hQ) hi hs hm' hd (by
    rw [snd_upd, upd_upd]; exact hsh) rfl (fun _ => rfl)
  rwa [upd_upd] at this

/-! ## Values -/

theorem inc_val {k : Nat} (hk : k < 2) :
    BitVec.ofNat 32 k + 1 = BitVec.ofNat 32 (k + 1) := by
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;> decide

theorem dec_val {k : Nat} (hk : k < 2) :
    BitVec.ofNat 32 (10 - k) - 1 = BitVec.ofNat 32 (10 - (k + 1)) := by
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;> decide

theorem sum_val {k : Nat} (hk : k ≤ 2) :
    BitVec.ofNat 32 k + BitVec.ofNat 32 (10 - k) = (10 : BitVec 32) := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;> decide

/-! ## The writer -/

section Proofs

variable {lk ul : Ptr → Io → ConcM Tgt Unit} (C : MutexContract lk ul)

/-- A thread out of the lock's code at place `x`. -/
def gOut (x : Ph) : Gh := (⟨.out, Heap.empty, Heap.empty⟩, x)

theorem shape_of {G : ThreadId → Gh} {m : Mem} {t : ThreadId} {g : Gh}
    (hi : proto.inv (upd G t g) m) : Shape (upd (fun u => (G u).2) t g.2) m := by
  have := hi.2.shape; rwa [snd_upd] at this

/-- The writer goes on to place `p`. -/
theorem shape_kid {G : ThreadId → Gh} {m : Mem} {g : Gh} {k : Nat} {b : Bool}
    (hi : proto.inv (upd G 1 g) m) (hg : g.2 = .wk k b) (p : Ph)
    (hp : (∃ k' ≤ 2, ∃ b', p = .wk k' b' ∧ (b' = true → k' < 2)) ∨ p = .fin) :
    Shape (upd (fun u => (G u).2) 1 p) m := by
  have := shape_set (shape_of hi) (by rw [upd_self, hg]) p hp
  rwa [upd_upd] at this

theorem R_wk0 (X : ThreadId → Ph) (k : Nat) :
    R (upd X 1 (.wk k false)) =
      (pts aPtr 4 (BitVec.ofNat 32 k) ∗ pts bPtr 4 (BitVec.ofNat 32 (10 - k))) := by
  simp [R, aVal, Ph.cnt, Ph.mid]

theorem R_wk1 (X : ThreadId → Ph) (k : Nat) :
    R (upd X 1 (.wk k true)) =
      (pts aPtr 4 (BitVec.ofNat 32 (k + 1)) ∗ pts bPtr 4 (BitVec.ofNat 32 (10 - k))) := by
  simp [R, aVal, Ph.cnt, Ph.mid]

include C in
/-- One update by the writer (thread 1), through the mutex contract only. -/
theorem update_spec {k : Nat} (hk : k < 2) (G : ThreadId → Gh) (m : Mem) (d : Nat)
    (hi : proto.inv (upd G 1 (gOut (.wk k false))) m) :
    proto.WP 1 ((update lk ul cPtr).run ()) (fun _ G' m' _ => m'.current = 1 ∧
      proto.inv (upd G' 1 (gOut (.wk (k + 1) false))) m') G m d := by
  unfold update
  simp only [StateT.run_bind]
  -- `lock`
  refine WP.bind (WP.callC (WP.mono ?_ (C.lock fits rfl 1 (gOut (.wk k false)) rfl rfl ⟨⟩ G m d hi)))
  rintro _ G₁ m₁ d₁ ⟨-, hc₁, hL, hi₁⟩
  have hi₁' : proto.inv (upd G₁ 1 (gH (.wk k false) hL)) m₁ := hi₁
  -- `a`
  refine WP.bind (wp_cache (x' := .wk k false) (r₀ := BitVec.ofNat 32 k) hi₁' hc₁
    (by rw [R_wk0]; exact (TTriple.load (by decide)).frame_eq)
    (shape_kid hi₁' rfl _ (.inl ⟨k, by omega, false, rfl, fun h => by cases h⟩))
    fun m₂ h₂ hc₂ _ hi₂ => ?_)
  refine WP.bind (wp_cache (x' := .wk k true) (r₀ := ()) hi₂ hc₂
    (by
      rw [R_wk0, R_wk1]
      exact ((TTriple.store (p := aPtr) (v := BitVec.ofNat 32 k) (by decide)
        (BitVec.ofNat 32 k + 1)).frame).conseq (fun _ h => h)
        (fun _ _ hq => sep_lift.mpr ⟨Subsingleton.elim _ _, by rw [← inc_val hk]; exact hq⟩))
    (shape_kid hi₂ rfl _ (.inl ⟨k, by omega, true, rfl, fun _ => hk⟩))
    fun m₃ h₃ hc₃ _ hi₃ => ?_)
  -- `b`
  refine WP.bind (wp_cache (x' := .wk k true) (r₀ := BitVec.ofNat 32 (10 - k)) hi₃ hc₃
    (by rw [R_wk1]; exact (TTriple.load (by decide)).frameL_eq)
    (shape_kid hi₃ rfl _ (.inl ⟨k, by omega, true, rfl, fun _ => hk⟩))
    fun m₄ h₄ hc₄ _ hi₄ => ?_)
  refine WP.bind (wp_cache (x' := .wk (k + 1) false) (r₀ := ()) hi₄ hc₄
    (by
      rw [R_wk1, R_wk0]
      exact ((TTriple.store (p := bPtr) (v := BitVec.ofNat 32 (10 - k)) (by decide)
        (BitVec.ofNat 32 (10 - k) - 1)).frameL).conseq (fun _ h => h)
        (fun _ _ hq => sep_lift.mpr ⟨Subsingleton.elim _ _, by rw [← dec_val hk]; exact hq⟩))
    (shape_kid hi₄ rfl _ (.inl ⟨k + 1, by omega, false, rfl, fun h => by cases h⟩))
    fun m₅ h₅ hc₅ _ hi₅ => ?_)
  -- `unlock`
  exact WP.callC (WP.mono (fun _ G' m' _ ⟨_, hc', hi'⟩ => ⟨hc', hi'⟩)
    (C.unlock fits rfl 1 (gH (.wk (k + 1) false) h₅) rfl rfl ⟨⟩ G₁ m₅ d₁ hi₅ hc₅))

include C in
theorem writer_spec (G : ThreadId → Gh) (m : Mem) (d : Nat)
    (hi : proto.inv (upd G 1 (gOut (.wk 0 false))) m) :
    proto.WP 1 (writer lk ul cPtr) (fun _ G' m' _ => m'.current = 1 ∧
      proto.inv (upd G' 1 (gOut (.wk 2 false))) m') G m d := by
  unfold writer
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind]
  refine WP.bind (WP.mono ?_ (update_spec C (by decide) G m d hi))
  rintro _ G₁ m₁ d₁ ⟨-, hi₁⟩
  exact update_spec C (by decide) G₁ m₁ d₁ hi₁

/-- The writer's end: it goes to `fin` and `gone`. -/
theorem kid_end {G : ThreadId → Gh} {m : Mem} (hi : proto.inv (upd G 1 (gOut (.wk 2 false))) m) :
    proto.inv (upd G 1 (⟨.gone, Heap.empty, Heap.empty⟩, .fin)) m := by
  have hl := hi.1.ghost (t := 1) (g := (⟨.gone, Heap.empty, Heap.empty⟩, .fin))
    (by rw [upd_self]; rfl) (.inr (.inl rfl)) (by rw [upd_self]; rfl) rfl
    (fun h => absurd rfl h) (fun hL hR => by
      change R (fun u => (upd G 1 (gOut (.wk 2 false)) u).2) hL at hR
      show R (fun u => (upd (upd G 1 (gOut (.wk 2 false))) 1 _ u).2) hL
      rw [snd_upd] at hR; rw [snd_upd, snd_upd, upd_upd]
      simpa [R, aVal, Ph.cnt, Ph.mid, gOut] using hR)
  rw [upd_upd] at hl
  refine ⟨hl, ?_⟩
  have hu := hi.2
  refine ⟨?_, fun u => ?_, hu.blk, fun u hu' => ?_⟩
  · rw [snd_upd]; exact shape_kid hi rfl .fin (.inr rfl)
  · unfold upd; split
    · rfl
    · rename_i h; have := hu.parts u; rwa [upd_ne _ _ h] at this
  · by_cases e : u = 1
    · subst e; rw [upd_self] at hu'; cases hu'
    · rw [upd_ne _ _ e] at hu' ⊢; have := hu.mid u; rw [upd_ne _ _ e] at this; exact this hu'

/-- The writer spawned no thread. -/
theorem joinedAll_kid {G : ThreadId → Gh} {m : Mem} {u : ThreadId} (hi : proto.inv G m)
    (hu : 0 < u) : joinedAll u m := by
  intro r hr hs
  obtain ⟨h0, h⟩ := hi.2.shape
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
/-- The spawned writer keeps the protocol. -/
theorem dispatch_spec (tgt : Tgt) (g : Gh) (hg : proto.init tgt g) (u : ThreadId)
    (G : ThreadId → Gh) (m : Mem) (d : Nat) (hu : 0 < u) (hgu : G u = g) (hi : proto.inv G m) :
    proto.WP u (dispatch lk ul tgt) (proto.QKid u) G { m with current := u } d := by
  cases tgt with
  | work p =>
    obtain ⟨rfl, rfl⟩ := hg
    have hx : (fun v => (G v).2) u = .wk 0 false := by show (G u).2 = _; rw [hgu]
    obtain ⟨rfl, -, -, -⟩ := shape_wk hi.2.shape hx
    show proto.WP 1 (writer lk ul cPtr) _ G _ d
    have hi' := fits.cur 1 hi (by rw [hgu]; rfl) (by rw [hgu]; exact (by decide : LPh.out ≠ LPh.gone))
    refine WP.mono ?_ (writer_spec C G _ d (by
      rw [show gOut (.wk 0 false) = G 1 from hgu.symm, upd_same]; exact hi'))
    rintro _ G' m' _ ⟨-, hi''⟩
    exact ⟨_, kid_end hi'', ⟨rfl, rfl⟩, fun _ => joinedAll_kid hi'' hu⟩
  | producer p => cases hg
  | semWork p => cases hg
  | writer p => cases hg

/-! ## `main` -/

theorem enc_u32 (v : BitVec 32) : (Enc.encode v).size = 4 := LawfulEnc.size_encode v

/-- `main` before its spawn. -/
def gPre : Gh := gOut .pre
/-- `main` after its spawn. -/
def gRun : Gh := gOut .run
/-- `main` at its join. -/
def gJoin : Gh := gOut .joins

/-- The start: no thread. -/
def G0 : ThreadId → Gh := fun _ => (⟨.gone, Heap.empty, Heap.empty⟩, .none)

/-- The cache in three parts, after `main`'s stores: the mutex word, `a = 0`, `b = 10`. -/
def Parts (A : Nat) : Assn :=
  bytesAt cPtr A 12 .stack (Enc.encode (0 : BitVec 32)) ∗
    (bytesAt (cPtr.add 4) A 12 .stack (Enc.encode (0 : BitVec 32)) ∗
      bytesAt ((cPtr.add 4).add 4) A 12 .stack (Enc.encode (10 : BitVec 32)))

/-- Before the spawn: `main` alone owns the cache. The lock starts: it owns `a` and `b`. -/
theorem inv_pre {m : Mem} {A : Nat} {h : Heap} (ho : Owned (upd (fun _ => Heap.empty) 0 h) m)
    (hp : Parts A h) (hA : A % 4 = 0) (hth : m.threads = #[{ spawner := 0, joined := true }])
    (hat : m.atomics = #[]) (hq : m.waiters = #[]) :
    proto.inv (upd G0 0 gPre) m := by
  obtain ⟨hW, hAB, dW, rfl, hw, ha, hb, dAB, rfl, hwa, hwb⟩ := hp
  have hs : (hW ∪ (ha ∪ hb)).Sub m.heap := by have := ho.sub 0; rwa [upd_self] at this
  have hsW : hW.Sub m.heap := Heap.sub_union_left.trans hs
  have h1 : m.threads.size = 1 := by rw [hth]; rfl
  have hcellW : ∀ x, 0 ≤ x → x < 0 + 4 → hW (0, x) ≠ none := fun x _ h2 =>
    bytesAt_in hw rfl (by simp [cPtr]) (by simp [cPtr, enc_u32]; omega)
  obtain ⟨blk, hblk, hl, hA', hS', hK', hx⟩ := bytesAt_blk (m := m) hw hsW rfl
    (by rw [enc_u32]; decide)
  have hbk : BlkOk m := ⟨blk, hblk, hl, hS', by rw [hA']; exact hA, hK'⟩
  have h0 : L.U32 m 0 := by
    show (intOfBytes 32 (curBytes m 0 0 4)).run = _
    unfold curBytes; rw [hblk]
    simp only [Option.map_some, Option.getD_some]
    rw [show (0 : Nat) = cPtr.off.toNat from rfl, show 4 = (Enc.encode (0 : BitVec 32)).size by
      rw [enc_u32], hx]
    exact intOfBytes_rmw 0
  have hsub : (Heap.empty ∪ ((ha ∪ hb) ∪ hW)).Sub (hW ∪ (ha ∪ hb)) := by
    rw [Heap.empty_union, Heap.union_comm dW.symm]; exact fun _ _ h => h
  have ho' := ho.shrink (t := 0) (by rw [upd_self]; exact hsub)
  rw [upd_upd] at ho'
  have hGu : ∀ u, u ≠ 0 → upd G0 0 gPre u = G0 u := fun u h => upd_ne _ _ h
  have hjt : joinedB m 0 = false := rfl
  refine ⟨Inv.make (t := 0) (hL := ha ∪ hb) (hW := hW) ho' hjt (fun u hu => ?_) (by rw [upd_self]; rfl)
    (by rw [upd_self]; exact fun _ => .inl rfl) dW.symm (fun u => ?_) (fun u => ?_) ?_
    (fun x h1 h2 => hcellW x h1 h2) ⟨blk, hblk, hl, by rw [hS']; decide,
      by show (blk.addr + 0) % 4 = 0; rw [hA']; omega,
      by rw [hK']; decide⟩ h0 (by rw [hat]; simp) hq (fun u hu => ?_) (by rw [h1]; decide), ?_⟩
  · rw [upd_ne _ _ hu]
    unfold Lock.own; rw [hGu u hu]; split <;> rfl
  · by_cases hu : u = 0
    · subst hu; rw [upd_self]; exact .inl ⟨rfl, by rw [h1]; decide, rfl⟩
    · rw [hGu u hu]; exact .inr rfl
  · by_cases hu : u = 0
    · subst hu; rw [upd_self]; rfl
    · rw [hGu u hu]; rfl
  · -- `a = 0`, `b = 10`
    change R (fun u => (upd G0 0 gPre u).2) (ha ∪ hb)
    have hx1 : (fun u => (upd G0 0 gPre u).2) 1 = .none := by
      show (upd G0 0 gPre 1).2 = _; rw [hGu 1 (by decide)]; rfl
    unfold R; rw [hx1]
    exact ⟨ha, hb, dAB, rfl,
      ⟨A, 12, .stack, Enc.encode (0 : BitVec 32), by simp [aPtr, cPtr, Ptr.add]; omega, enc_u32 0,
        LawfulEnc.decode_encode _, hwa, by decide⟩,
      ⟨A, 12, .stack, Enc.encode (10 : BitVec 32), by simp [bPtr, cPtr, Ptr.add]; omega, enc_u32 10,
        LawfulEnc.decode_encode _, hwb, by decide⟩⟩
  · have : u = 0 := by rw [h1] at hu; omega
    subst this; exact VClock.le_refl _
  · refine ⟨⟨by rw [hth]; rfl, .inl ⟨h1, by show (upd G0 0 gPre 0).2 = _; rw [upd_self]; rfl,
      fun u hu => ?_⟩⟩, fun u => ?_, hbk, fun u hu => ?_⟩
    · show (upd G0 0 gPre u).2 = _; rw [hGu u (by unfold ThreadId at *; omega)]; rfl
    · by_cases hu : u = 0
      · subst hu; rw [upd_self]; rfl
      · rw [hGu u hu]; rfl
    · by_cases h0 : u = 0
      · subst h0; rw [upd_self] at hu; cases hu
      · rw [hGu u h0] at hu; cases hu

/-- `main` goes from `run` to `joins` (out of the lock's code). -/
theorem main_join {G : ThreadId → Gh} {m : Mem} (hi : proto.inv (upd G 0 gRun) m) :
    proto.inv (upd G 0 gJoin) m := by
  have hR1 : ∀ x y : Ph, ∀ hL, R (upd (fun u => (G u).2) 0 x) hL →
      R (upd (fun u => (G u).2) 0 y) hL := fun x y hL h => by
    unfold R at h ⊢; rw [upd_ne _ _ (by decide)] at h ⊢; exact h
  have hl := hi.1.ghost (t := 0) (g := gJoin) (by rw [upd_self]; rfl) (.inl rfl)
    (by rw [upd_self]; rfl) rfl
    (fun _ => hi.1.live 0 (by rw [upd_self]; exact (by decide : LPh.out ≠ LPh.gone)))
    (fun hL hR => by
      change R (fun u => (upd G 0 gRun u).2) hL at hR
      show R (fun u => (upd (upd G 0 gRun) 0 gJoin u).2) hL
      rw [snd_upd] at hR; rw [snd_upd, snd_upd, upd_upd]
      exact hR1 _ _ hL hR)
  rw [upd_upd] at hl
  refine ⟨hl, ?_⟩
  have hu := hi.2
  refine ⟨?_, fun u => ?_, hu.blk, fun u hu' => ?_⟩
  · rw [snd_upd]
    have := shape_main (shape_of hi) (by rw [upd_self]; exact .inl rfl) .joins (.inr rfl)
    rwa [upd_upd] at this
  · unfold upd; split
    · rfl
    · rename_i h; have := hu.parts u; rwa [upd_ne _ _ h] at this
  · by_cases e : u = 0
    · subst e; rw [upd_self] at hu'; cases hu'
    · rw [upd_ne _ _ e] at hu' ⊢; have := hu.mid u; rw [upd_ne _ _ e] at this; exact this hu'

/-- While `main` holds the mutex, the writer is not in the middle of an update, and its
finished updates are at most 2. -/
theorem snapshot_ok {G : ThreadId → Gh} {m : Mem} {hL : Heap}
    (hi : proto.inv (upd G 0 (gH .run hL)) m) : (G 1).2.mid = false ∧ (G 1).2.cnt ≤ 2 := by
  have h10 : upd G 0 (gH .run hL) 1 = G 1 := upd_ne _ _ (by decide)
  refine ⟨?_, ?_⟩
  · cases hm : (G 1).2.mid
    · rfl
    · exfalso
      have hh := hi.2.mid 1 (by rw [h10]; exact hm)
      have := hi.1.one 1 0 hh (by rw [upd_self]; rfl)
      cases this
  · obtain ⟨-, ⟨-, h0, -⟩ | ⟨-, -, -, h1, -⟩⟩ := shape_of hi
    · rw [upd_self] at h0; cases h0
    · rw [upd_ne _ _ (by decide)] at h1
      rcases h1 with h1 | ⟨k, hk, b, h1, -⟩ <;> rw [h1]
      · exact Nat.le_refl _
      · exact hk

theorem R_main (X : ThreadId → Ph) (x : Ph) : R (upd X 0 x) = R X := by
  unfold R; rw [upd_ne _ _ (by decide)]

include C in
theorem main_spec (io : Io) (d : Nat) :
    proto.WP 0 (cacheMain lk ul io) QM G0 { mem0 with current := 0 } d := by
  unfold cacheMain
  -- the cache: block 0
  refine WP.bind (WP.liftMem_owned (own := fun _ => Heap.empty) (TTriple.alloc .stack 12 4 (by decide))
    (Owned.start rfl rfl) rfl (by decide) rfl fun s1 m₁ h₁ hr₁ ho₁ hq₁ hs₁ hm₁ hd₁ => ?_)
  obtain ⟨rfl, -⟩ := alloc_ok hr₁
  obtain ⟨A, hA⟩ := hq₁
  obtain ⟨⟨-, hA4⟩, hb₁⟩ := sep_lift.mp hA
  have hc₁ : m₁.current = 0 := hs₁.current
  rw [show (⟨some ({ mem0 with current := 0 } : Mem).blocks.size, 0⟩ : Ptr) = cPtr from rfl] at hb₁ ⊢
  -- its three parts
  obtain ⟨hW, hR₁, dW, rfl, hW₁, hR₁'⟩ := bytesAt_split hb₁ (k := 4) (by simp)
  obtain ⟨ha, hb, dAB, rfl, ha₁, hb₁'⟩ := bytesAt_split hR₁' (k := 4) (by simp)
  have hsW : ((Array.replicate 12 Byte.undef).extract 0 4).size = 4 := by simp
  have hsA : (((Array.replicate 12 Byte.undef).extract 4).extract 0 4).size = 4 := by simp
  have hsB : (((Array.replicate 12 Byte.undef).extract 4).extract 4).size = 4 := by simp
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind]
  -- the mutex word, `a`, `b`
  have ho₁' : Owned (upd (fun _ => Heap.empty) 0 (hW ∪ (ha ∪ hb))) m₁ := ho₁
  have F₁ : (bytesAt cPtr A 12 .stack ((Array.replicate 12 Byte.undef).extract 0 4) ∗
      (bytesAt (cPtr.add 4) A 12 .stack (((Array.replicate 12 Byte.undef).extract 4).extract 0 4) ∗
        bytesAt ((cPtr.add 4).add 4) A 12 .stack
          (((Array.replicate 12 Byte.undef).extract 4).extract 4)))
      (hW ∪ (ha ∪ hb)) := ⟨hW, ha ∪ hb, dW, rfl, hW₁, ha, hb, dAB, rfl, ha₁, hb₁'⟩
  refine WP.bind (WP.liftM_owned ((TTriple.storeAt (p := cPtr) (A := A) (S := 12) (K := .stack)
    (k := 0) (a := 4) (0 : BitVec 32) rfl (by decide) (by rw [hsW]; decide)
    (by simp [cPtr]; omega) (by decide)).frame) ho₁' hc₁ (by rw [hs₁.threads]; decide)
    (by rw [upd_self]; exact F₁) fun _ m₂ h₂ _ ho₂ F₂ hs₂ _ _ => ?_)
  rw [upd_upd] at ho₂
  refine WP.bind (WP.liftM_owned ((TTriple.storeAt (p := cPtr.add 4) (A := A) (S := 12) (K := .stack)
    (k := 0) (a := 4) (0 : BitVec 32) rfl (by decide) (by rw [hsA]; decide)
    (by simp [cPtr, Ptr.add]; omega) (by decide)).frame.frameL) ho₂
    (hs₂.current.trans hc₁) (by rw [hs₂.threads, hs₁.threads]; decide) (by rw [upd_self]; exact F₂)
    fun _ m₃ h₃ _ ho₃ F₃ hs₃ _ _ => ?_)
  rw [upd_upd] at ho₃
  refine WP.bind (WP.liftM_owned ((TTriple.storeAt (p := (cPtr.add 4).add 4) (A := A) (S := 12)
    (K := .stack) (k := 0) (a := 4) (10 : BitVec 32) rfl (by decide) (by rw [hsB]; decide)
    (by simp [cPtr, Ptr.add]; omega) (by decide)).frameL.frameL) ho₃
    (hs₃.current.trans (hs₂.current.trans hc₁))
    (by rw [hs₃.threads, hs₂.threads, hs₁.threads]; decide) (by rw [upd_self]; exact F₃)
    fun _ m₄ h₄ _ ho₄ F₄ hs₄ _ _ => ?_)
  rw [upd_upd] at ho₄
  have hc₄ : m₄.current = 0 := hs₄.current.trans (hs₃.current.trans (hs₂.current.trans hc₁))
  have hth₄ : m₄.threads = #[{ spawner := 0, joined := true }] := by
    rw [hs₄.threads, hs₃.threads, hs₂.threads, hs₁.threads]; rfl
  have hat₄ : m₄.atomics = #[] := by rw [hs₄.atomics, hs₃.atomics, hs₂.atomics, hs₁.atomics]; rfl
  have hq₄ : m₄.waiters = #[] := by rw [hs₄.waiters, hs₃.waiters, hs₂.waiters, hs₁.waiters]; rfl
  have hP : Parts A h₄ := by
    rw [writeBytes_all (by rw [hsW, enc_u32]), writeBytes_all (by rw [hsA, enc_u32]),
      writeBytes_all (by rw [hsB, enc_u32])] at F₄
    exact F₄
  -- the spawn
  refine WP.bind (WP.spawnC fun k _ => ⟨gPre, inv_pre ho₄ hP hA4 hth₄ hat₄ hq₄, fun G₁ m₅ hg₁ hi₅ =>
    ⟨gOut (.wk 0 false), ⟨rfl, rfl⟩, fun child m₆ hf => ?_⟩⟩)
  obtain ⟨h00, ⟨hs1, -, hnone⟩ | ⟨-, -, h0, -⟩⟩ := hi₅.2.shape
  rotate_left
  · exfalso; change (G₁ 0).2 = _ ∨ _ at h0
    simp [hg₁, gPre, gOut] at h0
  obtain ⟨hch, hm₆⟩ := Lock.fork_eq hf
  rw [hs1] at hch
  subst hch hm₆
  have hX₅ : ∀ u, (G₁ u).2 = if u = 0 then .pre else .none := by
    intro u; split
    · rename_i h; subst h; rw [hg₁]; rfl
    · exact hnone u (by unfold ThreadId at *; omega)
  have hi₆ : proto.inv (upd (upd G₁ 1 (gOut (.wk 0 false))) 0 gRun)
      { m₅ with
        current := 0
        clocks := (m₅.clocks.set! 0 (VClock.bump (m₅.clocks[0]!) 0)).push
          (VClock.bump (m₅.clocks[0]!) 0)
        threads := m₅.threads.push { spawner := 0, joined := false } } := by
    refine ⟨?_, ⟨⟨?_, .inr ⟨by simp [hs1], ?_, .inl ?_,
      .inr ⟨0, by decide, false, ?_, fun h => by cases h⟩, fun u hu => ?_⟩⟩,
      fun u => ?_, hi₅.2.blk, fun u hu => ?_⟩⟩
    · refine hi₅.1.fork (t := 0) (by rw [hg₁]; rfl) hf (by rw [hg₁]; rfl) (fun _ => .inl rfl) rfl rfl
        rfl rfl fun hL hR => ?_
      have hR' : R (fun u => (G₁ u).2) hL := hR
      change R (fun u => (upd (upd G₁ 1 (gOut (.wk 0 false))) 0 gRun u).2) hL
      unfold R at hR' ⊢
      have e1 : (G₁ 1).2 = .none := by rw [hX₅]; rfl
      have e2 : (upd (upd G₁ 1 (gOut (.wk 0 false))) 0 gRun 1).2 = .wk 0 false := by
        rw [upd_ne _ _ (by decide), upd_self]; rfl
      dsimp only at hR' ⊢
      rw [e2]; rw [e1] at hR'; exact hR'
    · simp only [Array.getElem?_push]; rw [if_neg (by omega)]; exact h00
    · simp only [Array.getElem?_push, hs1, ↓reduceIte]
    · show (upd (upd G₁ 1 (gOut (.wk 0 false))) 0 gRun 0).2 = _; rw [upd_self]; rfl
    · show (upd (upd G₁ 1 (gOut (.wk 0 false))) 0 gRun 1).2 = _
      rw [upd_ne _ _ (by decide), upd_self]; rfl
    · show (upd (upd G₁ 1 (gOut (.wk 0 false))) 0 gRun u).2 = _
      rw [upd_ne _ _ (by unfold ThreadId at *; omega), upd_ne _ _ (by unfold ThreadId at *; omega)]
      exact hnone u (by unfold ThreadId at *; omega)
    · unfold upd; split
      · rfl
      · split
        · rfl
        · exact hi₅.2.parts u
    · unfold upd at hu ⊢; split at hu
      · cases hu
      · split at hu
        · cases hu
        · rename_i h1 h2; simp only [h1, h2, ↓reduceIte]; exact hi₅.2.mid u hu
  simp only [StateT.run_bind, StateT.run_pure]
  -- `lock`
  refine WP.bind (WP.callC (WP.mono ?_ (C.lock fits rfl 0 gRun rfl rfl io _ _ k hi₆)))
  rintro _ G₂ m₇ d₂ ⟨hd₂, hc₇, hL, hi₇⟩
  have hi₇' : proto.inv (upd G₂ 0 (gH .run hL)) m₇ := hi₇
  obtain ⟨hmid, hcnt⟩ := snapshot_ok hi₇'
  have hsh₇ : Shape (upd (fun u => (G₂ u).2) 0 .run) m₇ := shape_of hi₇'
  -- the snapshot: `a`, then `b`, in one hold
  refine WP.bind (wp_cache (x' := .run) (r₀ := BitVec.ofNat 32 (aVal (G₂ 1).2)) hi₇' hc₇
    (by rw [R_main]; unfold R; exact (TTriple.load (by decide)).frame_eq) hsh₇
    fun m₈ h₈ hc₈ ht₈ hi₈ => ?_)
  have hsh₈ : Shape (upd (fun u => (G₂ u).2) 0 .run) m₈ := by
    unfold Shape at hsh₇ ⊢; rw [ht₈]; exact hsh₇
  refine WP.bind (wp_cache (x' := .run) (r₀ := BitVec.ofNat 32 (10 - (G₂ 1).2.cnt)) hi₈ hc₈
    (by rw [R_main]; unfold R; exact (TTriple.load (by decide)).frameL_eq) hsh₈
    fun m₉ h₉ hc₉ _ hi₉ => ?_)
  have hsum : BitVec.ofNat 32 (aVal (G₂ 1).2) + BitVec.ofNat 32 (10 - (G₂ 1).2.cnt) = 10 := by
    unfold aVal; rw [hmid]; exact sum_val hcnt
  -- `unlock`
  refine WP.bind (WP.callC (WP.mono ?_ (C.unlock fits rfl 0 (gH .run h₉) rfl rfl io G₂ m₉ d₂ hi₉ hc₉)))
  rintro _ G₃ m₁₀ d₃ ⟨hd₃, hc₁₀, hi₁₀⟩
  have hiJ := main_join (G := G₃) hi₁₀
  -- the join of the writer
  refine WP.bind (WP.joinC fun k₂ hk₂ => ⟨gJoin, hiJ, fun G₄ m₁₁ hg₄ hi₁₁ => ?_⟩)
  obtain ⟨h0₁₁, ⟨-, h0, -⟩ | ⟨hs2, hr1, -, -, -⟩⟩ := hi₁₁.2.shape
  · exfalso; change (G₄ 0).2 = _ at h0; rw [hg₄] at h0; cases h0
  refine ⟨fun _ => ⟨by decide, by rw [hs2]; decide, ⟨rfl, rfl⟩, by simp [Thread.joinValid, Mem.isGated, hr1]⟩,
    fun _ => ⟨fun _ => join_run (m := { m₁₁ with current := 0 }) hr1 rfl rfl, fun m₁₂ hj => ?_⟩⟩
  obtain ⟨rec, hrec, -, hm₁₂⟩ := join_eq hj
  refine WP.pure' ?_
  -- the free of the cache
  obtain ⟨blk₀, hblk₀, hl₀, -⟩ := hi₁₁.2.blk
  have hb₁₂ : m₁₂.blocks = m₁₁.blocks := by rw [hm₁₂]
  refine WP.bind (WP.liftMem (fun e he => (free_noErr (by rw [hb₁₂]; exact hblk₀) hl₀
      ((Mem.ClocksLe.join2 hj (by rw [hi₁₁.1.own.csize, hs2])).freeRaces _ _) e he).elim)
    fun _ m₁₃ hfr => ?_)
  obtain ⟨b', blk', -, -, rfl⟩ := free_ok hfr
  refine ⟨rfl, WP.pure' ⟨by rw [hsum], fun r hr hsp => ?_⟩⟩
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

/-! ## The results, for the translated `Io.Mutex` -/

/-- The cache client with the translated std mutex. -/
abbrev stdMain := cacheMain Io_Mutex_lockUncancelable Io_Mutex_unlock

/-- The spawn targets with the translated std mutex. -/
abbrev stdDispatch := dispatch Io_Mutex_lockUncancelable Io_Mutex_unlock

/-- **The reader sees a consistent snapshot under every schedule**: every completed run of the
cache client returns `a + b = 10` (every oracle, every fuel). -/
theorem cache_spec (env : Env) (henv : env.spawn = .available) {fuel : Nat} {o : Nat → Nat} {v : Except ErrName (BitVec 32)} {m : Mem}
    (io : Io) (h : (Sched.run env stdDispatch fuel o (stdMain io) mem0).run = some (.ok (v, m))) :
    v = .ok 10 := by
  obtain ⟨_, _, hv, -⟩ := proto.run_sound env (Proto.of_available henv) stdDispatch G0 (dispatch_spec mutex)
    (fun _ _ _ _ _ hq => hq.2) rfl (main_spec mutex io) h
  exact hv

/-- **No run of the cache client gives an error**: no data race on `a` or `b`, no deadlock at
the futex, no lifetime error at the free, under every schedule. -/
theorem cache_safe (env : Env) (henv : env.spawn = .available) {fuel : Nat} {o : Nat → Nat} {e : Error} (io : Io) :
    (Sched.run env stdDispatch fuel o (stdMain io) mem0).run ≠ some (.error e) :=
  proto.run_safe env (Proto.of_available henv) stdDispatch G0 rfl (dispatch_spec mutex) (fun _ _ _ _ hq => hq.2) rfl
    (main_spec mutex io)

end Sync.SnapshotCache
