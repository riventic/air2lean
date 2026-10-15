import Proofs.Sync.IoMutex
import ZigLean.Sep.Full.ThreadFacts
import ZigLean.Sep.Full.Local
import ZigLean.Sep.Full.AutoWP
import ZigLean.Sep.Full.LockSteps
import ZigLean.Conc.Unroll

/-!
# A snapshot cache against the mutex contract (C14 client)

A model client written in Lean (it is not a Zig export): the cache is a block with a mutex word
(bytes 0..4) and two `u32` fields `a` (4..8) and `b` (8..12), with the invariant `a + b = 10`.
A writer thread does two updates `a += 1; b -= 1`, each under the mutex; between its two stores
the invariant is broken. `main` takes the mutex once, reads `a` and `b`, releases it, joins the
writer and returns `a + b`. The result is 10 under every schedule (`cache_spec`) and no schedule
gives an error (`cache_safe`): the reader always sees a consistent snapshot, never the half-done
update.

The client code takes the lock operations as parameters (`lk`, `ul`). Its proof is in the
full-state concurrent separation logic (`docs/sep-threads.md`) and holds for **every mutex
implementation** with the contended value 2 (`mi : MutexImpl Tgt`, `mi.c = 2`): it uses only the
contract's two rules (`MutexImpl.lock_wp`, `unlock_wp`) and never unfolds an implementation. The
final theorems instantiate `mi` with the translated `Io.Mutex` (`Sync.ioMutex`,
`Proofs/Sync/IoMutex.lean`), whose operations are `Io_Mutex_lockUncancelable` / `Io_Mutex_unlock`.

- **The lock** (`L`, `FLock.prod`): the mutex owns `a` and `b`; `R`: `a = k (+1 while
  mid-update)`, `b = 10 - k`, with `k` the writer's finished updates. It depends only on the
  writer's ghost place.
- **Mid-update** (`U.mid`): a thread in the middle of an update holds the mutex, and such a
  thread runs no lock code (`ok`, `FLock.Fits.ofLock`). So the holder `main` sees `mid = false`.
- **Ownership transfer**: `lock` moves the cache's fields into the holder's resource, `unlock`
  moves them back (the contract); `main` frees the block only after the join. The block's full
  extent is in the protocol's rest (`U.rest`), which pins the block for every thread (`blk_of`).
- **The writer's update** (`update_spec`) is walked by `fsym`, with the contract's rules and the
  holder's steps on the fields (`wp_ldA`, `wp_ldB`, `wp_stA`, `wp_stB`).

Scope: one reader, one writer, two updates; no fairness, no termination claim (partial
correctness and strict safety under every schedule of the model).
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Full Zig.Full.FAssn Sync

namespace Sync.SnapshotCache

-- Unification must not unfold `WP` into the program (as in `Proofs/Sync/Mutex.lean`).
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

abbrev Gh := FLG × Ph

/-- The cache (block 0). -/
def cPtr : Ptr := ⟨some 0, 0⟩

/-- The value of `a`. -/
def aVal (x : Ph) : Nat := x.cnt + if x.mid then 1 else 0

/-- The lock's resource: `a = k (+1 mid-update)`, `b = 10 - k`, `k` the writer's updates. -/
def R (X : ThreadId → Ph) : FAssn :=
  up (pts (cPtr.add 4) 4 (BitVec.ofNat 32 (aVal (X 1)))) ⋆
    up (pts (cPtr.add 8) 4 (BitVec.ofNat 32 (10 - (X 1).cnt)))

/-- The mutex: bytes 0..4 of block 0. It owns `a` and `b`. -/
abbrev L : FLock Gh := FLock.prod 0 0 R

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

/-- Block 0 is the live cache: 12 bytes on the stack. -/
def BlkOk (m : Mem) : Prop :=
  ∃ blk, m.blocks[0]? = some blk ∧ blk.live = true ∧ blk.bytes.size = 12 ∧ blk.kind = .stack

/-- The rest of the invariant; the protocol's rest `rX` is the cache's full extent. -/
structure U (G : ThreadId → Gh) (rX : Res) (m : Mem) : Prop where
  shape : Shape (fun u => (G u).2) m
  parts : ∀ u, (G u).1.part = rnil
  rest : bext 0 12 .stack rX
  mid : ∀ u, (G u).2.mid = true → (G u).1.ph = .holds

/-- The protocol, in strict mode. -/
def proto : Proto Tgt Gh where
  inv G m := ∃ rX, L.Inv G rX m ∧ U G rX m
  init tgt g := match tgt with
    | .work p => p = cPtr ∧ g = (⟨.out, rnil, rnil⟩, .wk 0 false)
    | _ => False
  fin g := g.1.ph = .gone ∧ g.2 = .fin
  strict := true
  joins g := g.1.ph = .out ∧ g.2 = .joins

/-- `main`'s post: the result. -/
def QM : Except ErrName (BitVec 32) → (ThreadId → Gh) → Mem → Nat → Prop :=
  fun v _ m _ => v = .ok 10 ∧ joinedAll 0 m

/-! ## The protocol has the lock -/

theorem stable (G : ThreadId → Gh) (rX : Res) (m m' : Mem) (t : ThreadId) (p : LPh) (h : Res)
    (hok : ok (G t)) (_ : L.ph (G t) ≠ .gone) (hu : U G rX m) (hs : L.Step t m m')
    (_ : L.ph (G t) = .holds → p ≠ .holds → L.Before m' (m.clocks[t]!)) :
    U (upd G t (L.set (G t) p h)) rX m' := by
  obtain ⟨hsh, hpart, hrest, hmid⟩ := hu
  refine ⟨?_, fun u => ?_, hrest, fun u hu' => ?_⟩
  · rw [FLock.snd_set]; unfold Shape at hsh ⊢; rw [hs.threads]; exact hsh
  · unfold upd; split
    · rename_i e; subst e; exact hpart u
    · exact hpart u
  · by_cases e : u = t
    · subst e
      rw [upd_self] at hu'
      exact absurd hu' (by change (G u).2.mid ≠ true; rw [show (G u).2.mid = false from hok]; decide)
    · rw [upd_ne _ _ e] at hu' ⊢; exact hmid u hu'

theorem fits : L.Fits (FPrim.empty Gh) proto U ok :=
  .ofLock (fun _ _ => Iff.rfl) (fun _ h => h.1) (fun _ h => h.1) (fun _ _ _ => Iff.rfl)
    (fun _ _ => Iff.rfl) stable fun _ _ _ _ _ hu => ⟨hu.shape, hu.parts, hu.rest, hu.mid⟩

/-- The protocol's invariant at a stop of `t`. -/
theorem inv_cur {G : ThreadId → Gh} {m : Mem} (t : ThreadId) (hi : proto.inv G m)
    (hph : (G t).1.ph ≠ .gone) : proto.inv G { m with current := t } := by
  obtain ⟨-, -, -, h⟩ := fits.cur t hi hph
  exact h

/-- **The cache is block 0**: live, 12 bytes on the stack (the extent in the rest). -/
theorem blk_of {G : ThreadId → Gh} {rX : Res} {m : Mem} (hi : L.Inv G rX m)
    (hr : bext 0 12 .stack rX) : BlkOk m := by
  obtain ⟨rL, ho, -⟩ := hi.rest
  obtain ⟨rT, -, hh⟩ := ho.holds
  have he := hh.swap.extTrue
  simp only at he
  rw [Ghost.add_comm] at he; replace he := ExtTrue.of_add he
  rw [Ghost.add_comm] at he; replace he := ExtTrue.of_add he
  rw [bauth_eq hr] at he
  obtain ⟨blk, h1, h2, h3, h4, -⟩ := (he 0).1 12 .stack (by simp [Ghost.atExt, ECell.auth1])
  exact ⟨blk, h1, h2, h3, h4⟩

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

/-- `main` spawned every thread. -/
theorem spawners {X : ThreadId → Ph} {m : Mem} (h : Shape X m) : ∀ r ∈ m.threads, r.spawner = 0 :=
  spawners_of_getElem fun i hi => by
    obtain ⟨h0, ⟨h1, -⟩ | ⟨h2, h1, -⟩⟩ := h
    · obtain rfl : i = 0 := by omega
      rw [Array.getElem?_eq_getElem hi] at h0; rw [Option.some.inj h0]
    · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · rw [Array.getElem?_eq_getElem hi] at h0; rw [Option.some.inj h0]
      · rw [Array.getElem?_eq_getElem hi] at h1; rw [Option.some.inj h1]

/-- The lock's resource reads only the writer's `a` and `b`. -/
theorem R_congr {X Y : ThreadId → Ph} {r : Res} (ha : aVal (X 1) = aVal (Y 1))
    (hc : (X 1).cnt = (Y 1).cnt) (h : R Y r) : R X r := by
  unfold R; rw [ha, hc]; exact h

/-! ## The holder's steps on the cache -/

/-- A thread out of the lock's code at place `x`. -/
def gOut (x : Ph) : Gh := (⟨.out, rnil, rnil⟩, x)

/-- A thread that holds the mutex, at place `x`, with the cache's fields `rL`. -/
def gH (x : Ph) (rL : Res) : Gh := (⟨.holds, rnil, rL⟩, x)

/-! The ghost values of the lock's product (`rfl`), for the walks. -/
theorem set_out (x : Ph) (rL : Res) : L.set (gOut x) .holds rL = gH x rL := rfl
theorem set_hold (x : Ph) (rL : Res) : L.set (gH x rL) .out rnil = gOut x := rfl
theorem ph_out (x : Ph) : L.ph (gOut x) = .out := rfl
theorem ph_hold (x : Ph) (rL : Res) : L.ph (gH x rL) = .holds := rfl
theorem ok_out (k : Nat) : ok (gOut (.wk k false)) := rfl
theorem ok_hold (k : Nat) (rL : Res) : ok (gH (.wk k false) rL) := rfl

/-- A step of thread `t` that keeps the threads keeps `U`, with `t`'s new ghost value `g` (no
part; mid-update only while it holds the mutex) and the shape `hsh`. -/
theorem U_step {G : ThreadId → Gh} {rX : Res} {m m' : Mem} {t : ThreadId} {g : Gh}
    (hu : U G rX m) (hth : m'.threads = m.threads) (hpart : g.1.part = rnil)
    (hmid : g.2.mid = true → g.1.ph = .holds) (hsh : Shape (upd (fun u => (G u).2) t g.2) m) :
    U (upd G t g) rX m' := by
  refine ⟨?_, fun u => ?_, hu.rest, fun u hu' => ?_⟩
  · rw [upd_snd]; unfold Shape at hsh ⊢; rw [hth]; exact hsh
  · unfold upd; split
    · exact hpart
    · exact hu.parts u
  · by_cases e : u = t
    · subst e; rw [upd_self] at hu' ⊢; exact hmid hu'
    · rw [upd_ne _ _ e] at hu' ⊢; exact hu.mid u hu'

/-- The resource at the holder's place `x` (the lock's `R` over the places). -/
theorem R_hold {G : ThreadId → Gh} {t : ThreadId} {x : Ph} {r rL : Res} :
    L.R (upd G t (gH x rL)) r ↔ R (upd (fun u => (G u).2) t x) r := by
  change R (fun u => (upd G t (gH x rL) u).2) r ↔ _; rw [upd_snd]; rfl

/-- The holder's step keeps `U` (the obligation of `FLock.Fits.wp_hold`): no part, holding, the
shape at its new place `x₁`. -/
theorem U_hold {G : ThreadId → Gh} {t : ThreadId} {x₀ x₁ : Ph} {rL r rX : Res} {m m' : Mem}
    (hsh : Shape (upd (fun u => (G u).2) t x₁) m) (hu : U (upd G t (gH x₀ rL)) rX m)
    (hth : m'.threads = m.threads) : U (upd (upd G t (gH x₀ rL)) t (gH x₁ r)) rX m' :=
  U_step hu hth rfl (fun _ => rfl) (by rw [upd_snd, upd_upd]; exact hsh)

/-- The shape of the holder at its own place. -/
theorem shape_self {G : ThreadId → Gh} {m : Mem} {t : ThreadId} {x : Ph} {rL : Res}
    (hi : proto.inv (upd G t (gH x rL)) m) : Shape (upd (fun u => (G u).2) t x) m := by
  obtain ⟨rX, -, hU⟩ := hi
  have := hU.shape; rwa [upd_snd] at this

/-- The load of `a` by the holder at place `x`. -/
theorem wp_ldA {t : ThreadId} {rL : Res} {x : Ph} {G : ThreadId → Gh} {m : Mem} {d : Nat}
    {Q : BitVec 32 → (ThreadId → Gh) → Mem → Nat → Prop}
    (hi : proto.inv (upd G t (gH x rL)) m) (hc : m.current = t)
    (h : ∀ m' rQ, m'.current = t → proto.inv (upd G t (gH x rQ)) m' →
      Q (BitVec.ofNat 32 (aVal (upd (fun u => (G u).2) t x 1))) G m' d) :
    proto.WP t (ConcM.liftMem (load (BitVec 32) 4 (cPtr.add 4)) : ConcM Tgt (BitVec 32)) Q G m d := by
  have hl := (by fsym : FTTriple (up (pts (cPtr.add 4) 4
    (BitVec.ofNat 32 (aVal (upd (fun u => (G u).2) t x 1))))) (load (BitVec 32) 4 (cPtr.add 4)) _)
  refine fits.wp_hold (g' := gH x) (hl.frame
      (R := up (pts (cPtr.add 8) 4 (BitVec.ofNat 32 (10 - (upd (fun u => (G u).2) t x 1).cnt)))))
    (fun _ h => R_hold.mp h) (fun _ => ⟨rfl, by rw [upd_self]; rfl, rfl⟩) (fun a r h => ?_)
    (fun _ _ _ _ hu _ _ hth _ => U_hold (shape_self hi) hu hth) hi hc (by rw [upd_self]; rfl)
    fun a m' rQ hc' _ hq hi' => ?_
  · rw [upd_upd, R_hold]
    obtain ⟨r₁, r₂, hd, rfl, h₁, h₂⟩ := h
    exact ⟨r₁, r₂, hd, rfl, (Full.sep_lift.mp h₁).2, h₂⟩
  · obtain ⟨r₁, r₂, -, -, h₁, -⟩ := hq
    obtain ⟨rfl, -⟩ := Full.sep_lift.mp h₁
    exact h m' rQ hc' (by rwa [upd_upd] at hi')

/-- The load of `b` by the holder at place `x`. -/
theorem wp_ldB {t : ThreadId} {rL : Res} {x : Ph} {G : ThreadId → Gh} {m : Mem} {d : Nat}
    {Q : BitVec 32 → (ThreadId → Gh) → Mem → Nat → Prop}
    (hi : proto.inv (upd G t (gH x rL)) m) (hc : m.current = t)
    (h : ∀ m' rQ, m'.current = t → proto.inv (upd G t (gH x rQ)) m' →
      Q (BitVec.ofNat 32 (10 - (upd (fun u => (G u).2) t x 1).cnt)) G m' d) :
    proto.WP t (ConcM.liftMem (load (BitVec 32) 4 (cPtr.add 8)) : ConcM Tgt (BitVec 32)) Q G m d := by
  have hl := (by fsym : FTTriple (up (pts (cPtr.add 8) 4
    (BitVec.ofNat 32 (10 - (upd (fun u => (G u).2) t x 1).cnt)))) (load (BitVec 32) 4 (cPtr.add 8)) _)
  refine fits.wp_hold (g' := gH x) (hl.frameL
      (R := up (pts (cPtr.add 4) 4 (BitVec.ofNat 32 (aVal (upd (fun u => (G u).2) t x 1))))))
    (fun _ h => R_hold.mp h) (fun _ => ⟨rfl, by rw [upd_self]; rfl, rfl⟩) (fun a r h => ?_)
    (fun _ _ _ _ hu _ _ hth _ => U_hold (shape_self hi) hu hth) hi hc (by rw [upd_self]; rfl)
    fun a m' rQ hc' _ hq hi' => ?_
  · rw [upd_upd, R_hold]
    obtain ⟨r₁, r₂, hd, rfl, h₁, h₂⟩ := h
    exact ⟨r₁, r₂, hd, rfl, h₁, (Full.sep_lift.mp h₂).2⟩
  · obtain ⟨r₁, r₂, -, -, -, h₂⟩ := hq
    obtain ⟨rfl, -⟩ := Full.sep_lift.mp h₂
    exact h m' rQ hc' (by rwa [upd_upd] at hi')

/-- The writer's store of `a`'s next value after `k < 2` updates: then mid-update. -/
theorem wp_stA {rL : Res} {k : Nat} (hk : k < 2) {G : ThreadId → Gh} {m : Mem} {d : Nat}
    {v : BitVec 32} {Q : Unit → (ThreadId → Gh) → Mem → Nat → Prop}
    (hi : proto.inv (upd G 1 (gH (.wk k false) rL)) m) (hc : m.current = 1)
    (hv : v.toNat = k + 1)
    (h : ∀ m' rQ, m'.current = 1 → proto.inv (upd G 1 (gH (.wk k true) rQ)) m' → Q () G m' d) :
    proto.WP 1 (ConcM.liftMem (store 4 (cPtr.add 4) v) : ConcM Tgt Unit) Q G m d := by
  have hsh := shape_self hi
  have hv' : v = BitVec.ofNat 32 (aVal (.wk k true)) := by
    apply BitVec.eq_of_toNat_eq
    rw [hv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simp [aVal, Ph.cnt, Ph.mid]; omega)]
    simp [aVal, Ph.cnt, Ph.mid]
  have hs := (by fsym : FTTriple (up (pts (cPtr.add 4) 4 (BitVec.ofNat 32 (aVal (.wk k false)))))
    (store 4 (cPtr.add 4) v) _)
  have hsh₁ : Shape (upd (fun u => (G u).2) 1 (.wk k true)) m := by
    have := shape_set hsh (upd_self _ _ _) (.wk k true) (.inl ⟨k, by omega, true, rfl, fun _ => hk⟩)
    rwa [upd_upd] at this
  refine fits.wp_hold (g' := gH (.wk k true)) (hs.frame
      (R := up (pts (cPtr.add 8) 4 (BitVec.ofNat 32 (10 - k)))))
    (fun _ h => by have h := R_hold.mp h; unfold R at h; simpa [Ph.cnt] using h)
    (fun _ => ⟨rfl, by rw [upd_self]; rfl, rfl⟩)
    (fun a r h => by rw [upd_upd, R_hold]; unfold R; rw [upd_self, ← hv']; simpa [Ph.cnt] using h)
    (fun _ _ _ _ hu _ _ hth _ => U_hold hsh₁ hu hth) hi hc (by rw [upd_self]; rfl)
    fun a m' rQ hc' _ _ hi' => h m' rQ hc' (by rwa [upd_upd] at hi')

/-- The writer's store of `b`'s next value in the middle of its update `k < 2`: then `k + 1`
updates. -/
theorem wp_stB {rL : Res} {k : Nat} (hk : k < 2) {G : ThreadId → Gh} {m : Mem} {d : Nat}
    {v : BitVec 32} {Q : Unit → (ThreadId → Gh) → Mem → Nat → Prop}
    (hi : proto.inv (upd G 1 (gH (.wk k true) rL)) m) (hc : m.current = 1)
    (hv : v.toNat = 10 - (k + 1))
    (h : ∀ m' rQ, m'.current = 1 → proto.inv (upd G 1 (gH (.wk (k + 1) false) rQ)) m' →
      Q () G m' d) :
    proto.WP 1 (ConcM.liftMem (store 4 (cPtr.add 8) v) : ConcM Tgt Unit) Q G m d := by
  have hsh := shape_self hi
  have hv' : v = BitVec.ofNat 32 (10 - (k + 1)) := by
    apply BitVec.eq_of_toNat_eq
    rw [hv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hs := (by fsym : FTTriple (up (pts (cPtr.add 8) 4 (BitVec.ofNat 32 (10 - k))))
    (store 4 (cPtr.add 8) v) _)
  have hsh₁ : Shape (upd (fun u => (G u).2) 1 (.wk (k + 1) false)) m := by
    have := shape_set hsh (upd_self _ _ _) (.wk (k + 1) false)
      (.inl ⟨k + 1, by omega, false, rfl, fun h => by cases h⟩)
    rwa [upd_upd] at this
  refine fits.wp_hold (g' := gH (.wk (k + 1) false)) (hs.frameL
      (R := up (pts (cPtr.add 4) 4 (BitVec.ofNat 32 (aVal (.wk k true))))))
    (fun _ h => by have h := R_hold.mp h; unfold R at h; simpa [Ph.cnt] using h)
    (fun _ => ⟨rfl, by rw [upd_self]; rfl, rfl⟩)
    (fun a r h => by
      have e : aVal (.wk (k + 1) false) = aVal (.wk k true) := by simp [aVal, Ph.cnt, Ph.mid]
      rw [upd_upd, R_hold]; unfold R
      rw [upd_self, e, show (Ph.wk (k + 1) false).cnt = k + 1 from rfl, ← hv']; exact h)
    (fun _ _ _ _ hu _ _ hth _ => U_hold hsh₁ hu hth) hi hc (by rw [upd_self]; rfl)
    fun a m' rQ hc' _ _ hi' => h m' rQ hc' (by rwa [upd_upd] at hi')

/-! ## The writer -/

section Proofs

variable (mi : MutexImpl Tgt) (hmc : mi.c = 2)

include hmc in
/-- **One update by the writer** (thread 1), through the mutex contract only: walked by `fsym`,
with the contract's rules and the holder's steps on the fields. -/
theorem update_spec {k : Nat} (hk : k < 2) (G : ThreadId → Gh) (m : Mem) (d : Nat)
    (hi : proto.inv (upd G 1 (gOut (.wk k false))) m) :
    proto.WP 1 ((update mi.lock mi.unlock cPtr).run ()) (fun _ G' m' _ => m'.current = 1 ∧
      proto.inv (upd G' 1 (gOut (.wk (k + 1) false))) m') G m d := by
  unfold update
  fsym [mi.lock_wp fits rfl rfl hmc.symm, mi.unlock_wp fits rfl rfl hmc.symm,
    wp_ldA, wp_ldB, wp_stA hk, wp_stB hk, set_out, set_hold, ph_out, ph_hold, ok_out, ok_hold,
    aVal, Ph.cnt, Ph.mid]

include hmc in
theorem writer_spec (G : ThreadId → Gh) (m : Mem) (d : Nat)
    (hi : proto.inv (upd G 1 (gOut (.wk 0 false))) m) :
    proto.WP 1 (writer mi.lock mi.unlock cPtr) (fun _ G' m' _ => m'.current = 1 ∧
      proto.inv (upd G' 1 (gOut (.wk 2 false))) m') G m d := by
  unfold writer
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind]
  refine WP.bind (WP.mono ?_ (update_spec mi hmc (by decide) G m d hi))
  rintro _ G₁ m₁ d₁ ⟨-, hi₁⟩
  exact update_spec mi hmc (by decide) G₁ m₁ d₁ hi₁

end Proofs

/-- The writer's end: it goes to `fin` and `gone`. -/
theorem kid_end {G : ThreadId → Gh} {m : Mem} (hi : proto.inv (upd G 1 (gOut (.wk 2 false))) m) :
    proto.inv (upd G 1 (⟨.gone, rnil, rnil⟩, .fin)) m := by
  obtain ⟨rX, hiL, hU⟩ := hi
  have hl := hiL.ghost (t := 1) (g := (⟨.gone, rnil, rnil⟩, .fin)) (by rw [upd_self]; rfl)
    (.inr (.inl rfl)) (by rw [upd_self]; rfl) rfl (fun h => absurd rfl h) (fun r hR => by
      show R (fun u => (upd (upd G 1 (gOut (.wk 2 false))) 1 _ u).2) r
      rw [upd_upd]
      exact R_congr (Y := fun u => (upd G 1 (gOut (.wk 2 false)) u).2)
        (by simp [upd_self, gOut, aVal, Ph.cnt, Ph.mid]) (by simp [upd_self, gOut, Ph.cnt]) hR)
  rw [upd_upd] at hl
  have hsh := shape_set hU.shape (by show (upd G 1 _ 1).2 = _; rw [upd_self]; rfl) .fin (.inr rfl)
  have hU' := U_step (t := 1) (g := (⟨.gone, rnil, rnil⟩, .fin)) hU rfl rfl (fun h => by cases h) hsh
  rw [upd_upd] at hU'
  exact ⟨rX, hl, hU'⟩

section Proofs

variable (mi : MutexImpl Tgt) (hmc : mi.c = 2)

include hmc in
/-- The spawned writer keeps the protocol. -/
theorem dispatch_spec (tgt : Tgt) (g : Gh) (hg : proto.init tgt g) (u : ThreadId)
    (G : ThreadId → Gh) (m : Mem) (d : Nat) (hu : 0 < u) (hgu : G u = g) (hi : proto.inv G m) :
    proto.WP u (dispatch mi.lock mi.unlock tgt) (proto.QKid u) G { m with current := u } d := by
  cases tgt with
  | work p =>
    obtain ⟨rfl, rfl⟩ := hg
    obtain rfl : u = 1 := by
      obtain ⟨rX, -, hU⟩ := id hi
      exact (shape_wk hU.shape (t := u) (k := 0) (b := false) (by show (G u).2 = _; rw [hgu])).1
    show proto.WP 1 (writer mi.lock mi.unlock cPtr) _ G _ d
    refine WP.mono ?_ (writer_spec mi hmc G _ d (by
      rw [show gOut (.wk 0 false) = G 1 from hgu.symm, upd_same]
      exact inv_cur 1 hi (by rw [hgu]; nofun)))
    rintro _ G' m' _ ⟨-, hi'⟩
    have hk := kid_end hi'
    refine ⟨_, hk, ⟨rfl, rfl⟩, fun _ => ?_⟩
    obtain ⟨rX, -, hU⟩ := hk
    exact joinedAll_of_main (spawners hU.shape) (by decide)
  | producer p => cases hg
  | semWork p => cases hg
  | writer p => cases hg

end Proofs

/-! ## `main` -/

/-- The start: no thread. -/
def G0 : ThreadId → Gh := fun _ => (⟨.gone, rnil, rnil⟩, .none)

/-- `main` before its spawn. -/
def gPre : Gh := gOut .pre
/-- `main` after its spawn. -/
def gRun : Gh := gOut .run
/-- `main` at its join. -/
def gJoin : Gh := gOut .joins

/-- The cache's bytes `bs` in three parts: the mutex's word, `a`, `b`. -/
theorem split3 {A : Nat} {bs : Array Byte} {r : Res} (hs : bs.size = 12)
    (h : up (bytesAt cPtr A 12 .stack bs) r) :
    (up (bytesAt cPtr A 12 .stack (bs.extract 0 4)) ⋆
      (up (bytesAt (cPtr.add 4) A 12 .stack ((bs.extract 4 bs.size).extract 0 4)) ⋆
       up (bytesAt ((cPtr.add 4).add 4) A 12 .stack
        ((bs.extract 4 bs.size).extract 4 (bs.extract 4 bs.size).size)))) r :=
  sep_mono_right (fun _ h => up_sep ⟨bytesAt_split h.1 (k := 4) (by simp; omega), h.2⟩)
    (up_sep ⟨bytesAt_split h.1 (k := 4) (by omega), h.2⟩)

theorem sep_start {W A B E : FAssn} {r : Res} (h : ((W ⋆ (A ⋆ B)) ⋆ E) r) :
    (((A ⋆ B) ⋆ W) ⋆ E) r := by
  have e : ((W ⋆ (A ⋆ B)) ⋆ E) = (((A ⋆ B) ⋆ W) ⋆ E) := by ac_rfl
  rw [e] at h; exact h

theorem sep_word {W A B E : FAssn} {r : Res} (h : (((A ⋆ B) ⋆ W) ⋆ E) r) :
    ((W ⋆ E) ⋆ (A ⋆ B)) r := by
  have e : (((A ⋆ B) ⋆ W) ⋆ E) = ((W ⋆ E) ⋆ (A ⋆ B)) := by ac_rfl
  rw [e] at h; exact h

/-- A field of the cache as the lock's resource holds it (`pts`). -/
theorem pts_of {r : Res} {k A : Nat} {v : BitVec 32} (hA : A % 4 = 0) (hk : k % 4 = 0)
    (h : up (bytesAt (cPtr.add k) A 12 .stack (Enc.encode v)) r) :
    up (pts (cPtr.add k) 4 v) r :=
  ⟨⟨A, 12, .stack, Enc.encode v, by simp [cPtr, Ptr.add]; omega, LawfulEnc.size_encode _,
    LawfulEnc.decode_encode _, h.1, by decide⟩, h.2.1, h.2.2⟩

/-- **Before the spawn**: `main` owns the cache after its stores (the bytes `bs`: the mutex and
`a` are 0, `b` is 10) with its extent. It gives the extent to the protocol's rest
(`FOwned.give`), and the mutex and the fields to the lock (`FLock.Inv.make`). -/
theorem inv_start {m : Mem} {r : Res} {A : Nat} {bs : Array Byte}
    (ho : FOwned (upd (fun _ => rnil) 0 r) rnil m)
    (hF : (up (bytesAt cPtr A 12 .stack bs) ⋆ bext 0 12 .stack) r) (hs : bs.size = 12)
    (hW : bs.extract 0 4 = Enc.encode (0 : BitVec 32))
    (ha : (bs.extract 4 bs.size).extract 0 4 = Enc.encode (0 : BitVec 32))
    (hb : (bs.extract 4 bs.size).extract 4 (bs.extract 4 bs.size).size =
      Enc.encode (10 : BitVec 32))
    (hA : A % 4 = 0) (hth : m.threads = #[{ spawner := 0, joined := true }])
    (hat : m.atomics = #[]) (hq : m.waiters = #[]) :
    proto.inv (upd G0 0 gPre) m := by
  have h1 : m.threads.size = 1 := by rw [hth]; rfl
  have ht : 0 < m.threads.size := by rw [h1]; decide
  have hs4 : (Enc.encode (0 : BitVec 32)).size = 4 := LawfulEnc.size_encode _
  have hpB : (cPtr.add 4).add 4 = cPtr.add 8 := by simp only [cPtr, Ptr.add]; congr 1
  have hF' := sep_start (sep_mono_left (fun _ h => split3 hs h) hF)
  rw [hW, ha, hb, hpB] at hF'
  have hown0 := sep_word hF'
  obtain ⟨_, rE, hd, rfl, ⟨rAB, rW, hdW, rfl, hAB, hW₁⟩, hE⟩ := hF'
  -- the word's block and bytes
  obtain ⟨blk, hblk, hl, hA', hS', hK', hx⟩ :=
    ho.bytesOf ht (rfl : cPtr.block = some 0) (by rw [hs4]; decide)
      (by rw [upd_self]; exact hown0)
  have hoff : cPtr.off.toNat = 0 := rfl
  rw [hoff, hs4] at hx
  have h0 : L.U32 m 0 := by
    show (intOfBytes 32 (curBytes m 0 0 4)).run = _
    unfold curBytes; rw [hblk]
    simp only [Option.map_some, Option.getD_some]
    rw [hx]; exact intOfBytes_rmw 0
  -- the extent to the rest
  have ho' := ho.give (t := 0) ht (by rw [upd_self]) hd
  rw [upd_upd, rsum_rnil] at ho'
  have hGu : ∀ u, u ≠ 0 → upd G0 0 gPre u = G0 u := fun u h => upd_ne _ _ h
  have hjb : ∀ u, joinedB m u = false := by
    intro u; unfold joinedB
    by_cases hu : u = 0
    · subst hu; rw [hth]; rfl
    · have : m.threads.size ≤ u := by rw [h1]; unfold ThreadId at *; omega
      simp [Array.getElem?_eq_none this]
  refine ⟨rE, FLock.Inv.make (t := 0) (rL := rAB) (rW := rW) ho' (hjb 0) ht (fun u hu => ?_)
    (by rw [upd_self, upd_self]; exact (rnil_rsum _).symm)
    (by rw [upd_self]; exact (FHeap.disjoint_empty _).symm)
    hdW (fun l => ?_) hW₁.2.1 hW₁.2.2
    (fun u => ?_) (fun u => ?_) ?_ ⟨blk, hblk, hl, by rw [hS']; decide,
      by show (blk.addr + 0) % 4 = 0; rw [hA']; omega, by rw [hK']; decide,
      by rw [hK']; simp [BlockKind.mappedLo]⟩ h0 (by rw [hat]; simp) hq
      (allLe_of_one h1 (VClock.le_refl _)), ?_⟩
  · rw [upd_ne _ _ hu]
    unfold FLock.own; rw [hGu u hu]; split <;> simp [G0, FLock.prod, rnil_rsum]
  · rw [up_bytesAt_some hW₁ rfl l, hoff, hs4]
    show _ ↔ l.1 = 0 ∧ 0 ≤ l.2 ∧ l.2 < 0 + 4
    rfl
  · by_cases hu : u = 0
    · subst hu; rw [upd_self]; exact .inl ⟨rfl, ht, hjb 0⟩
    · rw [hGu u hu]; exact .inr rfl
  · by_cases hu : u = 0
    · subst hu; rw [upd_self]; rfl
    · rw [hGu u hu]; rfl
  · -- `a = 0`, `b = 10`
    change R (fun u => (upd G0 0 gPre u).2) rAB
    have e1 : (upd G0 0 gPre 1).2 = .none := by rw [hGu 1 (by decide)]; rfl
    unfold R; simp only [e1]
    obtain ⟨rA, rB, dAB, eAB, hA₁, hB₁⟩ := hAB
    exact ⟨rA, rB, dAB, eAB, pts_of hA (by decide) hA₁, pts_of hA (by decide) hB₁⟩
  · refine ⟨⟨by rw [hth]; rfl, .inl ⟨h1, by show (upd G0 0 gPre 0).2 = _; rw [upd_self]; rfl,
      fun u hu => ?_⟩⟩, fun u => ?_, hE, fun u hu => ?_⟩
    · show (upd G0 0 gPre u).2 = _; rw [hGu u (by unfold ThreadId at *; omega)]; rfl
    · by_cases hu : u = 0
      · subst hu; rw [upd_self]; rfl
      · rw [hGu u hu]; rfl
    · by_cases h0 : u = 0
      · subst h0; rw [upd_self] at hu; cases hu
      · rw [hGu u h0] at hu; cases hu

/-- **The spawn** of the writer by `main` at `pre`: `main` goes to `run`, the writer starts at
`wk 0 false` (its part is empty). -/
theorem inv_spawn {G : ThreadId → Gh} {m m' : Mem} {c : ThreadId}
    (hi : proto.inv G m) (hg : G 0 = gPre)
    (hf : (Thread.fork.run { m with current := 0 }).run = some (.ok (c, m'))) :
    c = 1 ∧ m'.current = 0 ∧ proto.inv (upd (upd G 1 (gOut (.wk 0 false))) 0 gRun) m' := by
  obtain ⟨rX, hL, hu⟩ := hi
  obtain ⟨h00, ⟨hs1, -, hnone⟩ | ⟨-, -, h0, -⟩⟩ := hu.shape
  rotate_left
  · exfalso
    have e : (G 0).2 = .pre := by rw [hg]; rfl
    rcases h0 with h0 | h0 <;> (change (G 0).2 = _ at h0; rw [e] at h0; cases h0)
  have hG1 : (G 1).2 = .none := hnone 1 (Nat.le_refl _)
  have hf' := hf
  rw [Proto.fork_run] at hf'
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hf'
  obtain ⟨rfl, rfl⟩ := hf'
  have hX : ∀ u, (upd (upd G 1 (gOut (.wk 0 false))) 0 gRun u).2 =
      if u = 0 then .run else if u = 1 then .wk 0 false else (G u).2 := fun u => by
    unfold upd; split
    · rfl
    · split <;> rfl
  have hL' := hL.fork (t := 0) (g₁ := gRun) (g₀ := gOut (.wk 0 false)) (gt := false)
    (by rw [hg]; rfl) hf (by rw [hg]; exact (rsum_rnil rnil).symm) (FHeap.disjoint_empty _) rfl rfl
    rfl rfl fun r hR => by
      show R (fun u => (upd (upd G m.threads.size (gOut (.wk 0 false))) 0 gRun u).2) r
      rw [hs1]
      exact R_congr (Y := fun u => (G u).2) (by rw [hX, hG1]; rfl) (by rw [hX, hG1]; rfl) hR
  rw [hs1] at hL'
  refine ⟨hs1, rfl, rX, hL', ⟨⟨?_, .inr ⟨by simp [hs1], ?_,
      .inl (by dsimp only; rw [hX]; rfl),
      .inr ⟨0, by decide, false, by dsimp only; rw [hX]; rfl, fun h => by cases h⟩,
      fun u hu => ?_⟩⟩, fun u => ?_, hu.rest, fun u hu' => ?_⟩⟩
  · simp only [Array.getElem?_push]; rw [ite_eq_right (by omega)]; exact h00
  · simp only [Array.getElem?_push, hs1, ↓reduceIte]
  · dsimp only
    rw [hX, ite_eq_right (by unfold ThreadId at *; omega),
      ite_eq_right (by unfold ThreadId at *; omega)]
    exact hnone u (by unfold ThreadId at *; omega)
  · unfold upd; split
    · rfl
    · split
      · rfl
      · exact hu.parts u
  · rw [hX] at hu'; unfold upd
    split at hu'
    · cases hu'
    · split at hu'
      · cases hu'
      · rename_i h0 h1; simp only [h0, h1, ↓reduceIte]; exact hu.mid u hu'

/-- `main` goes from `run` to `joins` (out of the lock's code). -/
theorem main_join {G : ThreadId → Gh} {m : Mem} (hi : proto.inv (upd G 0 gRun) m) :
    proto.inv (upd G 0 gJoin) m := by
  obtain ⟨rX, hiL, hU⟩ := hi
  have hl := hiL.ghost (t := 0) (g := gJoin) (by rw [upd_self]; rfl) (.inl rfl)
    (by rw [upd_self]; rfl) rfl
    (fun _ => hiL.ht (by rw [upd_self]; exact (by decide : LPh.out ≠ LPh.gone)))
    (fun r hR => by
      show R (fun u => (upd (upd G 0 gRun) 0 gJoin u).2) r
      rw [upd_upd]
      have e : ∀ g : Gh, (upd G 0 g 1).2 = (G 1).2 := fun _ => by rw [upd_ne _ _ (by decide)]
      exact R_congr (Y := fun u => (upd G 0 gRun u).2) (by rw [e, e]) (by rw [e, e]) hR)
  rw [upd_upd] at hl
  have hsh := shape_main hU.shape (by show (upd G 0 _ 0).2 = _ ∨ _; rw [upd_self]; exact .inl rfl)
    .joins (.inr rfl)
  have hU' := U_step (t := 0) (g := gJoin) hU rfl rfl (fun h => by cases h) hsh
  rw [upd_upd] at hU'
  exact ⟨rX, hl, hU'⟩

/-- While `main` holds the mutex, the writer is not in the middle of an update, and its
finished updates are at most 2. -/
theorem snapshot_ok {G : ThreadId → Gh} {m : Mem} {hL : Res}
    (hi : proto.inv (upd G 0 (gH .run hL)) m) : (G 1).2.mid = false ∧ (G 1).2.cnt ≤ 2 := by
  obtain ⟨rX, hiL, hU⟩ := hi
  have h10 : upd G 0 (gH .run hL) 1 = G 1 := upd_ne _ _ (by decide)
  refine ⟨?_, ?_⟩
  · cases hm : (G 1).2.mid
    · rfl
    · exfalso
      have hh := hU.mid 1 (by rw [h10]; exact hm)
      exact absurd (hiL.w.one 1 0 hh (by show L.ph (upd G 0 _ 0) = _; rw [upd_self]; rfl))
        (by decide)
  · obtain ⟨-, ⟨-, h0, -⟩ | ⟨-, -, -, h1, -⟩⟩ := hU.shape
    · change (upd G 0 _ 0).2 = _ at h0; rw [upd_self] at h0; cases h0
    · rcases h1 with h1 | ⟨k, hk, b, h1, -⟩ <;> simp only [h10] at h1 <;> rw [h1]
      · exact Nat.le_refl _
      · exact hk

theorem sum_val {k : Nat} (hk : k ≤ 2) :
    BitVec.ofNat 32 k + BitVec.ofNat 32 (10 - k) = (10 : BitVec 32) := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;> decide

/-! ## `main`'s join and free -/

/-- **`main`'s join of the writer** at `joins`: then every thread is joined, the cache is block
0 and every clock is below `main`'s. -/
theorem wp_join {σ : Type} {s : σ} {G : ThreadId → Gh} {m : Mem} {n : Nat}
    (hi : proto.inv (upd G 0 gJoin) m) {Q : Unit × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ k G₁ m', n = k + 1 → m'.current = 0 → BlkOk m' → m'.ClocksLe → joinedAll 0 m' →
      Q ((), s) G₁ m' k) :
    proto.WP 0 ((joinC 1 : CM Tgt σ Unit).run s) Q G m n := by
  refine WP.joinC fun k hk => ⟨_, hi, fun G₁ m₁ hg hi₁ => ?_⟩
  obtain ⟨rX, hL, hu⟩ := hi₁
  obtain ⟨h00, ⟨-, h0, -⟩ | ⟨hs2, hr1, -⟩⟩ := hu.shape
  · exfalso; change (G₁ 0).2 = _ at h0; rw [hg] at h0; cases h0
  refine ⟨fun _ => ⟨by show (0 : Nat) < 1; decide, by rw [hs2]; decide, ⟨rfl, rfl⟩,
    by simp [Thread.joinValid, Mem.isGated, hr1]⟩, fun _ => ⟨fun _ =>
    join_run (m := { m₁ with current := 0 }) hr1 rfl rfl, fun m' hj => ?_⟩⟩
  have hcs : m₁.clocks.size = 2 := by rw [hL.w.csize, hs2]
  obtain ⟨rec, -, -, hm'⟩ := join_eq hj
  have hth : m'.threads = m₁.threads.set! 1 { rec with joined := true } := by rw [hm']
  obtain ⟨blk, h1, h2, h3, h4⟩ := blk_of hL hu.rest
  refine h k G₁ m' hk (by rw [hm']) ⟨blk, by rw [hm']; exact h1, h2, h3, h4⟩
    (Mem.ClocksLe.join2 hj hcs) fun r hr hsp => ?_
  simp only [hth] at hr
  obtain ⟨i, hi', rfl⟩ := Array.mem_iff_getElem.mp hr
  simp only [Array.size_set!] at hi'
  simp only [Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds hi'] at hsp ⊢
  split
  · rfl
  · obtain rfl : i = 0 := by omega
    rw [Array.getElem?_eq_getElem (by omega)] at h00
    rw [Option.some.inj h00]

/-- **`main`'s free of the cache** after its join: its end races with no access. -/
theorem wp_free {G : ThreadId → Gh} {m : Mem} {n : Nat} (hb : BlkOk m) (hcl : m.ClocksLe)
    {Q : Unit → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ m', m'.threads = m.threads → Q () G m' n) :
    proto.WP 0 (ConcM.liftMem (free cPtr) : ConcM Tgt Unit) Q G m n := by
  obtain ⟨blk, hblk, hl, -, hk⟩ := hb
  refine WP.liftMem (fun e he => (free_noErr hblk hl (hcl.freeRaces _ _) (by rw [hk]; nofun) e
    he).elim) fun _ m' hfr => ?_
  obtain ⟨b', blk', -, -, rfl⟩ := free_ok hfr
  exact ⟨rfl, h _ rfl⟩

section Proofs

variable (mi : MutexImpl Tgt) (hmc : mi.c = 2)

include hmc in
theorem main_spec (σ : Placement) (io : Io) (d : Nat) :
    proto.WP 0 (cacheMain mi.lock mi.unlock io) QM G0 { mem0 σ with current := 0 } d := by
  unfold cacheMain
  have ht0 : ({ mem0 σ with current := 0 } : Mem).threads = #[{ spawner := 0, joined := true }] :=
    rfl
  -- the cache: block 0, a stack block; `main` gives up the plain mode
  refine WP.bind (WP.liftMem_fownedS (by fsym [FTriple.allocStackDrop] : FTTriple plain _ _)
    (FOwned.start0_plain σ) rfl (by rw [ht0]; decide) (by rw [plainOwn_zero]; exact plain_intro)
    fun s1 m₁ r₁ _ hr₁ ho₁ hq₁ hs₁ => ?_)
  simp only [plainOwn, upd_upd] at ho₁
  obtain ⟨rfl, hm₁e⟩ := alloc_ok hr₁
  obtain ⟨A, b, hq₁⟩ := hq₁
  obtain ⟨⟨hpb, -, hA4⟩, F₁⟩ := Full.sep_lift.mp hq₁
  obtain rfl : b = 0 := by cases hpb; rfl
  rw [show (⟨some ({ mem0 σ with current := 0 } : Mem).blocks.size, 0⟩ : Ptr) = cPtr from rfl]
    at F₁ ⊢
  have hc₁ : m₁.current = 0 := hs₁.current
  have ht₁ : m₁.threads = #[{ spawner := 0, joined := true }] := hs₁.threads.trans ht0
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind]
  -- the mutex's word, `a`, `b`
  refine WP.bind (WP.callMC_fownedS (FTTriple.storeAt (p := cPtr) (A := A) (S := 12)
    (K := .stack) (k := 0) (a := 4) (0 : BitVec 32) rfl rfl (by decide) (by decide)
    (by simp [cPtr]; omega) (by decide)) ho₁ hc₁ (by rw [ht₁]; decide)
    F₁ fun _ m₂ r₂ _ hr₂ ho₂ F₂ hs₂ => ?_)
  rw [upd_upd] at ho₂
  have hc₂ : m₂.current = 0 := hs₂.current.trans hc₁
  have ht₂ : m₂.threads = #[{ spawner := 0, joined := true }] := hs₂.threads.trans ht₁
  refine WP.bind (WP.callMC_fownedS (FTTriple.storeAt (p := cPtr) (A := A) (S := 12)
    (K := .stack) (k := 4) (a := 4) (0 : BitVec 32) rfl rfl (by decide) (by decide +kernel)
    (by simp [cPtr]; omega) (by decide)) ho₂ hc₂ (by rw [ht₂]; decide)
    F₂ fun _ m₃ r₃ _ hr₃ ho₃ F₃ hs₃ => ?_)
  rw [upd_upd] at ho₃
  have hc₃ : m₃.current = 0 := hs₃.current.trans hc₂
  have ht₃ : m₃.threads = #[{ spawner := 0, joined := true }] := hs₃.threads.trans ht₂
  refine WP.bind (WP.callMC_fownedS (FTTriple.storeAt (p := cPtr) (A := A) (S := 12)
    (K := .stack) (k := 8) (a := 4) (10 : BitVec 32) rfl rfl (by decide) (by decide +kernel)
    (by simp [cPtr]; omega) (by decide)) ho₃ hc₃ (by rw [ht₃]; decide)
    F₃ fun _ m₄ r₄ _ hr₄ ho₄ F₄ hs₄ => ?_)
  rw [upd_upd] at ho₄
  have hc₄ : m₄.current = 0 := hs₄.current.trans hc₃
  have ht₄ : m₄.threads = #[{ spawner := 0, joined := true }] := hs₄.threads.trans ht₃
  have hat₄ : m₄.atomics = #[] := by
    rw [store_atomics hr₄, store_atomics hr₃, store_atomics hr₂, hm₁e]; rfl
  have hq₄ : m₄.waiters = #[] := by
    rw [hs₄.waiters, hs₃.waiters, hs₂.waiters, hs₁.waiters]; rfl
  have hi₀ := inv_start ho₄ F₄ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hA4 ht₄ hat₄ hq₄
  -- the spawn
  refine WP.bind (WP.spawnC fun k _ => ⟨gPre, hi₀, fun G₁ m₅ hg₁ hi₅ =>
    ⟨gOut (.wk 0 false), ⟨rfl, rfl⟩, fun child m₆ hf => ?_⟩⟩)
  obtain ⟨rfl, hc₆, hi₆⟩ := inv_spawn hi₅ hg₁ hf
  simp only [StateT.run_bind]
  -- `lock`
  refine WP.bind (WP.callC (WP.mono ?_ (mi.lock_wp fits rfl rfl hmc.symm 0 gRun rfl rfl io _ _ k
    hi₆)))
  rintro _ G₂ m₇ d₂ ⟨-, hc₇, hL, hi₇⟩
  have hi₇' : proto.inv (upd G₂ 0 (gH .run hL)) m₇ := hi₇
  obtain ⟨hmid, hcnt⟩ := snapshot_ok hi₇'
  -- the snapshot: `a`, then `b`, in one hold (a step `liftM x` is `ConcM.liftMem x`)
  simp only [CNorm.run_liftM]
  refine WP.bind (WP.bind (wp_ldA hi₇' hc₇ fun m₈ h₈ hc₈ hi₈ => WP.pure' ?_))
  refine WP.bind (WP.bind (wp_ldB hi₈ hc₈ fun m₉ h₉ hc₉ hi₉ => WP.pure' ?_))
  have hsum : BitVec.ofNat 32 (aVal (upd (fun u => (G₂ u).2) 0 .run 1)) +
      BitVec.ofNat 32 (10 - (upd (fun u => (G₂ u).2) 0 .run 1).cnt) = 10 := by
    rw [upd_ne _ _ (by decide)]; unfold aVal; rw [hmid]; exact sum_val hcnt
  -- `unlock`
  refine WP.bind (WP.callC (WP.mono ?_ (mi.unlock_wp fits rfl rfl hmc.symm 0 (gH .run h₉) rfl rfl
    io G₂ m₉ d₂ hi₉ hc₉)))
  rintro _ G₃ m₁₀ d₃ ⟨-, -, hi₁₀⟩
  -- the join of the writer
  refine WP.bind (wp_join (main_join (G := G₃) hi₁₀) fun k₂ G₄ m₁₁ _ _ hb₁₁ hcl₁₁ hja => ?_)
  refine WP.pure' ?_
  -- the free of the cache
  refine WP.bind (wp_free hb₁₁ hcl₁₁ fun m₁₂ hth => ?_)
  exact WP.pure' ⟨by rw [hsum], fun r hr hsp => hja r (by rw [← hth]; exact hr) hsp⟩

end Proofs

/-! ## The results, for the translated `Io.Mutex` -/

/-- The cache client with the translated std mutex. -/
abbrev stdMain := cacheMain Io_Mutex_lockUncancelable Io_Mutex_unlock

/-- The spawn targets with the translated std mutex. -/
abbrev stdDispatch := dispatch Io_Mutex_lockUncancelable Io_Mutex_unlock

/-- **The reader sees a consistent snapshot under every schedule**: every completed run of the
cache client returns `a + b = 10` (every oracle, every fuel). -/
theorem cache_spec (env : Env) (henv : env.spawn = .available) {σ : Placement} {fuel : Nat} {o : Nat → Nat} {v : Except ErrName (BitVec 32)} {m : Mem}
    (io : Io) (h : (Sched.run env stdDispatch fuel o (stdMain io) (mem0 σ)).run = some (.ok (v, m))) :
    v = .ok 10 := by
  obtain ⟨_, _, hv, -⟩ := proto.run_sound env (Proto.of_available henv) stdDispatch G0
    (dispatch_spec ioMutex rfl) (fun _ _ _ _ _ hq => hq.2) rfl (main_spec ioMutex rfl σ io) h
  exact hv

/-- One schedule completes: under the oracle that always picks option 0, the cache client
returns 10 within fuel 1000. The kernel computes the run. -/
theorem cache_completes :
    ∃ σ, Witness.okVal (Sched.run ⟨.any, .available⟩ stdDispatch 1000 (fun _ => 0) (stdMain ⟨⟩) (mem0 σ)) = some 10 :=
  ⟨.fresh, by decide +kernel⟩

/-- **No run of the cache client gives an error**: no data race on `a` or `b`, no deadlock at
the futex, no lifetime error at the free, under every schedule. -/
theorem cache_safe (env : Env) (henv : env.spawn = .available) {σ : Placement} {fuel : Nat} {o : Nat → Nat} {e : Error} (io : Io) :
    e ≠ .stackOverflow → (Sched.run env stdDispatch fuel o (stdMain io) (mem0 σ)).run ≠ some (.error e) :=
  proto.run_safe env (Proto.of_available henv) stdDispatch G0 rfl (dispatch_spec ioMutex rfl)
    (fun _ _ _ _ hq => hq.2) rfl (main_spec ioMutex rfl σ io)

end Sync.SnapshotCache
