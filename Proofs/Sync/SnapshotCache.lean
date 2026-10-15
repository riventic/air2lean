import Proofs.Sync.IoMutex
import ZigLean.Sep.Full.ThreadFacts
import ZigLean.Sep.Full.Local
import ZigLean.Sep.Full.AutoWP

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
theorem R_congr {X Y : ThreadId → Ph} (ha : aVal (X 1) = aVal (Y 1)) (hc : (X 1).cnt = (Y 1).cnt) :
    R X = R Y := by
  unfold R; rw [ha, hc]

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
  · rw [FLock.snd_upd]; unfold Shape at hsh ⊢; rw [hth]; exact hsh
  · unfold upd; split
    · exact hpart
    · exact hu.parts u
  · by_cases e : u = t
    · subst e; rw [upd_self] at hu' ⊢; exact hmid hu'
    · rw [upd_ne _ _ e] at hu' ⊢; exact hu.mid u hu'

/-- **The holder's step on the cache**, a thread triple on its fields (`FLock.Inv.wp_liftMem`):
the holder goes from place `x₀` to `x₁`, the fields' new resource has `R` at `x₁` (`hR`), and the
shape holds at `x₁`. -/
theorem wp_hold {α : Type} {x : MemM α} {t : ThreadId} {rL : Res} {x₀ x₁ : Ph}
    {G : ThreadId → Gh} {m : Mem} {d : Nat} {Pa : FAssn} {Qa : α → FAssn}
    (htt : FTTriple Pa x Qa) (hpa : R (upd (fun u => (G u).2) t x₀) rL → Pa rL)
    (hi : proto.inv (upd G t (gH x₀ rL)) m) (hc : m.current = t)
    (hsh : Shape (upd (fun u => (G u).2) t x₁) m)
    {Q : α → (ThreadId → Gh) → Mem → Nat → Prop}
    (hR : ∀ a r, Qa a r → R (upd (fun u => (G u).2) t x₁) r)
    (h : ∀ a m' rQ, m'.current = t → m'.threads = m.threads → Qa a rQ →
      proto.inv (upd G t (gH x₁ rQ)) m' → Q a G m' d) :
    proto.WP t (ConcM.liftMem x : ConcM Tgt α) Q G m d := by
  obtain ⟨rX, hiL, hU⟩ := hi
  have e : ∀ x r, (fun u => (upd G t (gH x r) u).2) = upd (fun u => (G u).2) t x :=
    fun _ _ => FLock.snd_upd _ _ _
  have hh : L.ph (upd G t (gH x₀ rL) t) = .holds := by rw [upd_self]; rfl
  obtain ⟨ht, hjt⟩ := hiL.ht (by rw [hh]; decide)
  have hres : R (upd (fun u => (G u).2) t x₀) rL := by
    have := hiL.res t hh; rw [upd_self] at this
    change R (fun u => (upd G t (gH x₀ rL) u).2) rL at this
    rwa [e] at this
  have hd : FHeap.Disjoint rnil.heap rL.heap := by have := hiL.pdisj t; rwa [upd_self] at this
  refine hiL.wp_liftMem hc ht hjt (htt.frameL (R := fun r => r = rnil))
    (by rw [upd_self]; exact ⟨rnil, rL, hd, rfl, rfl, hpa hres⟩) fun a m' r' hr hq hs hc' hk => ?_
  obtain ⟨r₁, rQ, hdQ, e', hr₁, hq'⟩ := hq
  rw [hr₁] at e' hdQ
  have hl := hk (gH x₁ rQ) (by rw [upd_self]; rfl) e'.symm hdQ (fun h => absurd rfl h)
    (fun h => absurd hh h) (fun _ => by
      show R (fun u => (upd (upd G t (gH x₀ rL)) t (gH x₁ rQ) u).2) rQ
      rw [upd_upd, e]; exact hR a rQ hq')
  rw [upd_upd] at hl
  have hU' := U_step (g := gH x₁ rQ) hU hs.threads rfl (fun _ => rfl)
    (by rw [FLock.snd_upd, upd_upd]; exact hsh)
  rw [upd_upd] at hU'
  exact h a m' rQ hc' hs.threads hq' ⟨rX, hl, hU'⟩

/-- The shape of the holder at its own place. -/
theorem shape_self {G : ThreadId → Gh} {m : Mem} {t : ThreadId} {x : Ph} {rL : Res}
    (hi : proto.inv (upd G t (gH x rL)) m) : Shape (upd (fun u => (G u).2) t x) m := by
  obtain ⟨rX, -, hU⟩ := hi
  have := hU.shape; rwa [FLock.snd_upd] at this

/-- The load of `a` by the holder at place `x`. -/
theorem wp_ldA {t : ThreadId} {rL : Res} {x : Ph} {G : ThreadId → Gh} {m : Mem} {d : Nat}
    {Q : BitVec 32 → (ThreadId → Gh) → Mem → Nat → Prop}
    (hi : proto.inv (upd G t (gH x rL)) m) (hc : m.current = t)
    (h : ∀ m' rQ, m'.current = t → proto.inv (upd G t (gH x rQ)) m' →
      Q (BitVec.ofNat 32 (aVal (upd (fun u => (G u).2) t x 1))) G m' d) :
    proto.WP t (ConcM.liftMem (load (BitVec 32) 4 (cPtr.add 4)) : ConcM Tgt (BitVec 32)) Q G m d := by
  refine wp_hold (x₁ := x) ((FTTriple.load (q := cPtr.add 4) (a := 4)
    (v := BitVec.ofNat 32 (aVal (upd (fun u => (G u).2) t x 1))) (by decide)).frame
      (R := up (pts (cPtr.add 8) 4 (BitVec.ofNat 32 (10 - (upd (fun u => (G u).2) t x 1).cnt)))))
    (fun h => h) hi hc (shape_self hi) (fun a r h => ?_) fun a m' rQ hc' _ hq hi' => ?_
  · obtain ⟨r₁, r₂, hd, rfl, h₁, h₂⟩ := h
    exact ⟨r₁, r₂, hd, rfl, (Full.sep_lift.mp h₁).2, h₂⟩
  · obtain ⟨r₁, r₂, -, -, h₁, -⟩ := hq
    obtain ⟨rfl, -⟩ := Full.sep_lift.mp h₁
    exact h m' rQ hc' hi'

/-- The load of `b` by the holder at place `x`. -/
theorem wp_ldB {t : ThreadId} {rL : Res} {x : Ph} {G : ThreadId → Gh} {m : Mem} {d : Nat}
    {Q : BitVec 32 → (ThreadId → Gh) → Mem → Nat → Prop}
    (hi : proto.inv (upd G t (gH x rL)) m) (hc : m.current = t)
    (h : ∀ m' rQ, m'.current = t → proto.inv (upd G t (gH x rQ)) m' →
      Q (BitVec.ofNat 32 (10 - (upd (fun u => (G u).2) t x 1).cnt)) G m' d) :
    proto.WP t (ConcM.liftMem (load (BitVec 32) 4 (cPtr.add 8)) : ConcM Tgt (BitVec 32)) Q G m d := by
  refine wp_hold (x₁ := x) ((FTTriple.load (q := cPtr.add 8) (a := 4)
    (v := BitVec.ofNat 32 (10 - (upd (fun u => (G u).2) t x 1).cnt)) (by decide)).frameL
      (R := up (pts (cPtr.add 4) 4 (BitVec.ofNat 32 (aVal (upd (fun u => (G u).2) t x 1))))))
    (fun h => h) hi hc (shape_self hi) (fun a r h => ?_) fun a m' rQ hc' _ hq hi' => ?_
  · obtain ⟨r₁, r₂, hd, rfl, h₁, h₂⟩ := h
    exact ⟨r₁, r₂, hd, rfl, h₁, (Full.sep_lift.mp h₂).2⟩
  · obtain ⟨r₁, r₂, -, -, -, h₂⟩ := hq
    obtain ⟨rfl, -⟩ := Full.sep_lift.mp h₂
    exact h m' rQ hc' hi'

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
  refine wp_hold (x₁ := .wk k true) ((FTTriple.store (q := cPtr.add 4) (a := 4)
    (v := BitVec.ofNat 32 (aVal (.wk k false))) (by decide) v).frame
      (R := up (pts (cPtr.add 8) 4 (BitVec.ofNat 32 (10 - k)))))
    (fun h => by unfold R at h; simpa [Ph.cnt] using h) hi hc
    (by have := shape_set hsh (upd_self _ _ _) (.wk k true) (.inl ⟨k, by omega, true, rfl, fun _ => hk⟩)
        rwa [upd_upd] at this)
    (fun a r h => by unfold R; rw [upd_self, ← hv']; simpa [Ph.cnt] using h)
    fun a m' rQ hc' _ _ hi' => h m' rQ hc' hi'

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
  refine wp_hold (x₁ := .wk (k + 1) false) ((FTTriple.store (q := cPtr.add 8) (a := 4)
    (v := BitVec.ofNat 32 (10 - k)) (by decide) v).frameL
      (R := up (pts (cPtr.add 4) 4 (BitVec.ofNat 32 (aVal (.wk k true))))))
    (fun h => by unfold R at h; simpa [Ph.cnt] using h) hi hc
    (by have := shape_set hsh (upd_self _ _ _) (.wk (k + 1) false)
          (.inl ⟨k + 1, by omega, false, rfl, fun h => by cases h⟩)
        rwa [upd_upd] at this)
    (fun a r h => by
      have e : aVal (.wk (k + 1) false) = aVal (.wk k true) := by simp [aVal, Ph.cnt, Ph.mid]
      unfold R; rw [upd_self, e, show (Ph.wk (k + 1) false).cnt = k + 1 from rfl, ← hv']; exact h)
    fun a m' rQ hc' _ _ hi' => h m' rQ hc' hi'

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

end Proofs

end Sync.SnapshotCache
