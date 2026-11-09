import ZigLean.Sep.Full.LockProd
import ZigLean.Sep.Full.Mutex
import ZigLean.Sep.Full.WordRules

/-!
# Two nested mutexes against the mutex contract (ledger #two-lock-product, item (4))

A model client written in Lean (it is not a Zig export): a thread locks `A`, then `B`, unlocks
`B`, then `A`. The client takes the lock operations as parameters (`nested`) and its proof holds
for **every mutex implementation** (`mi : MutexImpl Tgt`: only the contract's rules
`MutexImpl.lock_wp`, `unlock_wp` and `unlock_wp_to`, never an implementation's code) and **every
pair of locks** `A`, `B` over one ghost value (`FLock.Pair`) with unshared resources, `A` outer
(its holder sleeps only at `B`'s word: `A`'s nest) and `B` inner (no nest).

- **The protocol** (`proto`) is the two-lock product (`ZigLean/Sep/Full/LockProd.lean`): `A`'s
  invariant with `B` kept in its rest (`FLock.Pair.U B`), and no rest of the client's own. Both
  locks' `Fits` come from the generic builder (`FLock.Pair.fitsOrder`, `fits`); the client
  supplies only its own (here trivial) rest's obligations.
- **Where the thread runs each lock's code.** `B`'s futex queue admits a thread asleep at another
  futex only `away` from `B` (`LockWord.Queue`), so the thread runs `A`'s code `away` from `B`
  (`okA`), and `B`'s code holding `A` at `holdsAway` (`okB`, `A`'s nest). Its relabels between the
  calls are the generic rules: `Fits.unaway` and `Fits.goAway` at `B`, `Fits.nap` and `Fits.unnap`
  at `A`, each with its `U`-stability from `FLock.Pair.U_setA`.
- `nested_wp`: from a thread out of `A` and away from `B`, `nested` returns it there again with its
  part (`Back`). `nested_prod`: the instance over two locks of one ghost value
  (`FLock.prodA`/`prodB`), so the hypotheses are satisfiable.

Scope: one thread's code from the protocol's invariant (partial correctness under every
interleaving of the protocol's other threads); no program run.
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Full Zig.Full.FAssn

namespace Sync.NestedMutex

-- Unification must not unfold `WP` into the program (as in `Proofs/Sync/Mutex.lean`).
attribute [local irreducible] Proto.WP

variable {Tgt γ : Type}

/-- The client's code (module doc), over the lock operations `lk` and `ul`. -/
def nested (lk ul : Ptr → Io → ConcM Tgt Unit) (pA pB : Ptr) (io : Io) : ConcM Tgt Unit := do
  lk pA io
  lk pB io
  ul pB io
  ul pA io

/-- The two-lock product of `A` and `B` with no rest of the client's own. -/
def proto (A B : FLock γ) : Proto Tgt γ where
  inv G m := ∃ rX, A.Inv G rX m ∧ FLock.Pair.U B (fun _ _ _ => True) G rX m
  init _ _ := False
  fin g := A.ph g = .gone ∧ B.ph g = .gone
  joins g := A.ph g = .out ∧ B.ph g = .out

/-- A thread runs `A`'s code `away` from `B`. -/
abbrev okA (B : FLock γ) (g : γ) : Prop := B.ph g = .away

/-- A thread runs `B`'s code `away` from `A`, or holding it at `holdsAway`. -/
abbrev okB (A : FLock γ) (g : γ) : Prop := A.ph g = .away ∨ A.ph g = .holdsAway

/-- The thread is back out of `A` and away from `B`, holding nothing, with the part of `g`. -/
def Back (A B : FLock γ) (g g' : γ) : Prop :=
  A.ph g' = .out ∧ B.ph g' = .away ∧ A.held g' = rnil ∧ B.held g' = rnil ∧ A.part g' = A.part g

section

variable {A B : FLock γ} (hp : A.Pair B) (hnA : ∀ p, A.nest p ↔ p = B.ptr)
  (hnB : ∀ p, ¬ B.nest p) (hRA : ∀ G, (A.R G).Unshared) (hRB : ∀ G, (B.R G).Unshared)
include hp hnA hnB hRA hRB

/-- **Both locks' `Fits`**, from the generic builder (`FLock.Pair.fitsOrder`). -/
theorem fits :
    A.Fits (FPrim.empty γ) (proto (Tgt := Tgt) A B) (FLock.Pair.U B fun _ _ _ => True) (okA B) ∧
      B.Fits (FPrim.empty γ) (proto (Tgt := Tgt) A B) (FLock.Pair.U A fun _ _ _ => True)
        (okB A) :=
  hp.fitsOrder hnA hnB (fun _ _ _ hf => FLock.NoGatherHeld.of_R hRA hf)
    (fun _ _ _ hf => FLock.NoGatherHeld.of_R hRB hf) (fun _ _ => Iff.rfl) (fun _ h => h.1)
    (fun _ h => h.2) (fun _ h => h.1) (fun _ h => h.2)
    (fun _ _ _ => by rw [okA, hp.ph_ab]) (fun _ _ => by rw [okA, hp.setPart, B.ph_setPart])
    (fun _ _ _ => by rw [okB, hp.ph_ba]) (fun _ _ => by rw [okB, ← hp.setPart, A.ph_setPart])
    (fun _ h => h) (fun _ h => h)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ => FLock.NoGather.of_R _ hRA) (fun _ _ _ _ _ _ => FLock.NoGather.of_R _ hRB)

/-- **`nested` over every mutex implementation** (module doc): walked by the contract's rules for
each lock (`MutexImpl.lock_wp`, `unlock_wp_to`, `unlock_wp`) with the builder's `Fits`, and the
generic relabels between the calls. -/
theorem nested_wp (mi : MutexImpl Tgt) (hcA : A.c = mi.c) (hcB : B.c = mi.c) (t : ThreadId)
    (g : γ) (hgA : A.ph g = .out) (hgB : B.ph g = .away)
    (hu : 0 < (A.part g).gh.ac.frag .unmetered) (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hi : (proto (Tgt := Tgt) A B).inv (upd G t g) m) :
    (proto A B).WP t (nested mi.lock mi.unlock A.ptr B.ptr io) (fun _ G' m' _ =>
      m'.current = t ∧ ∃ g', Back A B g g' ∧ (proto (Tgt := Tgt) A B).inv (upd G' t g') m')
      G m d := by
  obtain ⟨hA, hB⟩ := fits (Tgt := Tgt) hp hnA hnB hRA hRB
  -- a relabel of `t` at one lock keeps the other kept (`Pair.U_setA`)
  have setA : ∀ {G₀ : ThreadId → γ} {m₀ : Mem} {g₀ : γ} {rX : Res} (q : LPh) (h : Res),
      FLock.Pair.U B (fun _ _ _ => True) (upd G₀ t g₀) rX m₀ →
      FLock.Pair.U B (fun _ _ _ => True) (upd G₀ t (A.set g₀ q h)) rX m₀ := by
    intro G₀ m₀ g₀ rX q h hU
    have := FLock.Pair.U_setA (t := t) (p := q) (h := h) hp hU fun _ _ => trivial
    rwa [upd_self, upd_upd] at this
  have setB : ∀ {G₀ : ThreadId → γ} {m₀ : Mem} {g₀ : γ} {rX : Res} (q : LPh) (h : Res),
      FLock.Pair.U A (fun _ _ _ => True) (upd G₀ t g₀) rX m₀ →
      FLock.Pair.U A (fun _ _ _ => True) (upd G₀ t (B.set g₀ q h)) rX m₀ := by
    intro G₀ m₀ g₀ rX q h hU
    have := FLock.Pair.U_setA (t := t) (p := q) (h := h) hp.symm hU fun _ _ => trivial
    rwa [upd_self, upd_upd] at this
  unfold nested
  -- `lock A`, away from `B`
  refine WP.bind (WP.mono ?_ (mi.lock_wp hA rfl rfl hcA t g hgA hgB hu io G m d hi))
  rintro _ G₁ m₁ d₁ ⟨-, -, rL, hi₁⟩
  -- back at `B`'s `out`: `t` holds `A`, so it is not in the futex queue
  have hq₁ : ∀ w ∈ m₁.waiters, w.1 ≠ t := by
    obtain ⟨rX, hiA, -⟩ := (hA.inv _ _).mp hi₁
    have h : A.pl (upd G₁ t (A.set g .holds rL)) t = .holds := by
      show A.ph _ = _; rw [upd_self, A.ph_set]
    exact hiA.w.notQ_mem (by rw [h]; decide) (by rw [h]; decide) (by rw [h]; decide)
  have hi₂ := hB.unaway (g := A.set g .holds rL) (by rw [hp.ph_ab]; exact hgB) hi₁ hq₁
    fun _ hU _ => setB .out rnil hU
  -- `A`'s nap: its holder may now sleep at `B`'s word
  have hi₃ := hA.nap (g := B.set (A.set g .holds rL) .out rnil) (by rw [hp.ph_ba, A.ph_set]) hi₂
    fun _ hU _ => setA .holdsAway _ hU
  generalize hg₃ : A.set (B.set (A.set g .holds rL) .out rnil) .holdsAway
    (A.held (B.set (A.set g .holds rL) .out rnil)) = g₃ at hi₃
  have h3A : A.ph g₃ = .holdsAway := by rw [← hg₃, A.ph_set]
  have h3B : B.ph g₃ = .out := by rw [← hg₃, hp.ph_ab, B.ph_set]
  have h3h : B.held g₃ = rnil := by rw [← hg₃, hp.held_ab, B.held_set]
  have h3p : A.part g₃ = A.part g := by
    rw [← hg₃, A.part_set, hp.part_ba, A.part_set]
  -- `lock B`, holding `A` at `holdsAway`
  refine WP.bind (WP.mono ?_ (mi.lock_wp hB rfl rfl hcB t g₃ h3B (Or.inr h3A)
    (by rw [← hp.part, h3p]; exact hu) io G₁ m₁ d₁ hi₃))
  rintro _ G₂ m₂ d₂ ⟨-, hc₂, rL', hi₄⟩
  -- `unlock B`
  refine WP.bind (WP.mono ?_ (mi.unlock_wp_to hB rfl rfl hcB t g₃ rL' h3B h3h (Or.inr h3A) io G₂
    m₂ d₂ hi₄ hc₂))
  rintro _ G₃ m₃ d₃ ⟨-, hc₃, hi₅⟩
  -- `A`'s unnap: `t` is out of `B`'s code, so not in the futex queue
  have hq₃ : m₃.waiters.any (·.1 == t) = false := by
    obtain ⟨rX, hiB, -⟩ := (hB.inv _ _).mp hi₅
    have h : B.pl (upd G₃ t g₃) t = .out := by show B.ph _ = _; rw [upd_self, h3B]
    exact hiB.w.notQ (by rw [h]; decide) (by rw [h]; decide) (by rw [h]; decide)
  have hi₆ := hA.unnap (g := g₃) h3A hi₅ hq₃ fun _ hU _ => setA .holds _ hU
  -- away from `B` again
  have hi₇ := hB.goAway (g := A.set g₃ .holds (A.held g₃)) (by rw [hp.ph_ab, h3B]) hi₆
    fun _ hU _ => setB .away rnil hU
  -- `unlock A`
  refine WP.mono ?_ (mi.unlock_wp hA rfl rfl hcA t _ (by rw [hp.ph_ba, A.ph_set])
    (B.ph_set _ _ _) io G₃ m₃ d₃ hi₇ hc₃)
  rintro _ G₄ m₄ d₄ ⟨-, hc₄, hi₈⟩
  refine ⟨hc₄, _, ⟨A.ph_set _ _ _, ?_, A.held_set _ _ _, ?_, ?_⟩, hi₈⟩
  · rw [hp.ph_ab, B.ph_set]
  · rw [hp.held_ab, B.held_set]
  · rw [A.part_set, hp.part_ba, A.part_set, h3p]

end

/-! ## The instance: two locks of one ghost value -/

section Prod

variable {X : Type} (bA oA bB oB : Nat) (RA RB : (ThreadId → X) → FAssn) (c : Nat)
  (hc : c = 1 ∨ c = 2 ∨ c = 3)

/-- The inner lock: `B` of `FLock.prodB`, without a nest. -/
abbrev lockB : FLock (FLG2 × X) := FLock.prodB bB oB RB (fun _ => False) c hc

/-- The outer lock: `A` of `FLock.prodA`, whose holder sleeps only at `lockB`'s word. -/
abbrev lockA : FLock (FLG2 × X) :=
  FLock.prodA bA oA RA (· = (lockB bB oB RB c hc).ptr) c hc

/-- **`nested` over two locks of one ghost value** (`nested_wp` at `FLock.prodA`/`prodB`): a
thread out of `A` and away from `B` with the part `rp`, for apart words and unshared resources. -/
theorem nested_prod (mi : MutexImpl Tgt) (hmc : c = mi.c)
    (hap : (lockA bA oA bB oB RA RB c hc).ApartL (lockB bB oB RB c hc).toLockWord)
    (hRA : ∀ xs, (RA xs).Unshared) (hRB : ∀ xs, (RB xs).Unshared) (t : ThreadId) (rp : Res)
    (x : X) (hu : 0 < rp.gh.ac.frag .unmetered) (io : Io) (G : ThreadId → FLG2 × X) (m : Mem)
    (d : Nat)
    (hi : (proto (Tgt := Tgt) (lockA bA oA bB oB RA RB c hc) (lockB bB oB RB c hc)).inv
      (upd G t ({ phA := .out, phB := .away, part := rp }, x)) m) :
    (proto (lockA bA oA bB oB RA RB c hc) (lockB bB oB RB c hc)).WP t
      (nested mi.lock mi.unlock (lockA bA oA bB oB RA RB c hc).ptr (lockB bB oB RB c hc).ptr io)
      (fun _ G' m' _ => m'.current = t ∧ ∃ g', Back (lockA bA oA bB oB RA RB c hc)
        (lockB bB oB RB c hc) ({ phA := .out, phB := .away, part := rp }, x) g' ∧
        (proto (Tgt := Tgt) (lockA bA oA bB oB RA RB c hc) (lockB bB oB RB c hc)).inv
          (upd G' t g') m')
      G m d :=
  nested_wp (FLock.prodPair hap) (fun _ => Iff.rfl) (fun _ h => h) (fun _ => hRA _)
    (fun _ => hRB _) mi hmc hmc t ({ phA := .out, phB := .away, part := rp }, x) rfl rfl hu io G
    m d hi

end Prod

end Sync.NestedMutex
