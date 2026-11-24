import ZigLean.Conc.Share

/-!
# A program's own facts beside a primitive's protocol

A protocol's invariant is a primitive's (a lock's, a semaphore's, a reader/writer lock's) and the
program's own facts: which threads exist and where they are in the program, and the bytes every
thread reads and no thread owns (the `io` prefix of a shared object). The primitive's code changes
none of them, and each kind of its steps keeps them for one reason. This file states the program's
facts once (`FClient`, `FClient.Holds`) and proves them kept by each kind of step, so a
primitive's base carries them (`FRw.Base`'s `cl`) and a program proves no step lemma of its own.

- `FClient X`: the threads' fact `T` (the client parts against the thread table), the read-shared
  region `Rg` and its bytes `Io`, which the protocol's rest holds; a narrowed access of the region
  is in the region (`up`), and an access of the region touches one of its bytes (`touch`).
- `FClient.Holds`: the facts at ghost values' client parts `xs`, a rest `rX` and a memory `m`.
- `Holds.keep`: a step that keeps the thread table, makes no clock smaller, whose new accesses
  touch the rest only at the primitive's own bytes `Lk`, and whose new rest keeps every cell out
  of `Lk`, keeps the facts, when the region's bytes are out of `Lk` (`hoff`).
- `Holds.fstep`, `Holds.lstep`: the two step relations of the logic, an `FStepIn` whose frame has
  the rest's bytes out of `Lk`, and a step of a lock's code at its word.
- `Holds.read`: the record of a read keeps the facts (`FLock.Fits.wp_readRest`'s `hrec`).
- `FClient.none`: no facts (`none_holds`, `none_io`).
-/

namespace Zig
namespace Full

open Conc Proto

/-- **A program's facts beside a primitive's protocol** (module doc). -/
structure FClient (X : Type) where
  /-- The threads: the client parts against the thread table. -/
  T : (ThreadId → X) → Array ThreadRec → Prop
  /-- The accesses of the read-shared region. -/
  Rg : FootprintEntry → Prop
  /-- The region's bytes, which the protocol's rest holds. -/
  Io : Res → Prop
  /-- An access that a region's access narrows to is in the region. -/
  up : ∀ e e₀ : FootprintEntry, e.Narrows e₀ → Rg e → Rg e₀
  /-- An access of the region touches one of its bytes. -/
  touch : ∀ r e, Io r → Rg e →
    ∃ x, e.off ≤ x ∧ x < e.off + e.len ∧ r.heap (e.block, x) ≠ none

namespace FClient

variable {X : Type} {E : FClient X} {xs : ThreadId → X} {rX rX' : Res} {m m' : Mem}
  {Lk : Zig.Loc → Prop}

/-- No facts: every thread table, an empty region with no byte. -/
def none (X : Type) : FClient X where
  T _ _ := True
  Rg _ := False
  Io r := ∀ l, r.heap l = Option.none
  up _ _ _ h := h
  touch _ _ _ h := h.elim

/-- **The program's facts hold** (module doc): the threads, the region read-shared, and its bytes
in the rest. -/
structure Holds (E : FClient X) (xs : ThreadId → X) (rX : Res) (m : Mem) : Prop where
  thr : E.T xs m.threads
  sh : ReadShared E.Rg m
  io : ∃ r, E.Io r ∧ ∀ l fc, r.heap l = some fc → rX.heap l = some fc

/-- No facts hold at every rest and memory. -/
theorem none_holds (xs : ThreadId → X) (rX : Res) (m : Mem) : (none X).Holds xs rX m :=
  ⟨trivial, fun _ _ h => h.elim, ⟨FHeap.empty, Know.none, Ghost.unit⟩, fun _ => rfl,
    fun _ _ h => nomatch h⟩

/-- The empty region has no byte (a primitive's `hIo`). -/
theorem none_io {r : Res} (h : (none X).Io r) (l : Zig.Loc) : r.heap l = Option.none := h l

namespace Holds

/-- **A step that leaves the program alone keeps its facts** (module doc). -/
theorem keep (h : E.Holds xs rX m) (hoff : ∀ r l, E.Io r → Lk l → r.heap l = Option.none)
    (hth : m'.threads = m.threads)
    (hcl : ∀ u : Nat, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (hfp : ∀ e ∈ m'.footprint, (∃ e₀ ∈ m.footprint, e.Narrows e₀) ∨
      ∀ x, e.off ≤ x → x < e.off + e.len → rX.heap (e.block, x) ≠ Option.none → Lk (e.block, x))
    (hrest : ∀ l fc, ¬ Lk l → rX.heap l = some fc → rX'.heap l = some fc) :
    E.Holds xs rX' m' := by
  obtain ⟨r, hr, hsub⟩ := h.io
  have hnl : ∀ l fc, r.heap l = some fc → ¬ Lk l := fun l fc hl hk => by
    rw [hoff r l hr hk] at hl; cases hl
  refine ⟨hth ▸ h.thr, fun e he hR => ?_, r, hr, fun l fc hl => hrest l fc (hnl l fc hl)
    (hsub l fc hl)⟩
  rcases hfp e he with ⟨e₀, he₀, hn⟩ | hnew
  · have hc := hn.clock
    rcases h.sh e₀ he₀ (E.up e e₀ hn hR) with ⟨hk, h'⟩ | h'
    · exact .inl ⟨hn.2.2.1.trans hk, someLe_mono hth (fun u _ => hcl u) (LockWord.someLe_le hc h')⟩
    · exact .inr (allLe_mono hth (fun u _ => hcl u) fun u hu => VClock.le_trans hc (h' u hu))
  · obtain ⟨x, h1, h2, h3⟩ := E.touch r e hr hR
    obtain ⟨fc, hfc⟩ := Option.ne_none_iff_exists'.mp h3
    exact absurd (hnew x h1 h2 (by rw [hsub _ _ hfc]; nofun)) (hnl _ _ hfc)

/-- **A framed step keeps the program's facts**: its frame `hF` has the rest's bytes out of `Lk`,
and it reads none of them as a share (`hR`). -/
theorem fstep {hF hR : Heap} (h : E.Holds xs rX m)
    (hoff : ∀ r l, E.Io r → Lk l → r.heap l = Option.none) (hs : FStepIn hF m m' hR)
    (hcov : ∀ l, rX.heap l ≠ Option.none → ¬ Lk l → hF l ≠ Option.none ∧ hR l = Option.none)
    (hrest : ∀ l fc, ¬ Lk l → rX.heap l = some fc → rX'.heap l = some fc) :
    E.Holds xs rX' m' :=
  h.keep hoff hs.threads hs.clock (fun e he => (hs.fp e he).imp_right fun ⟨_, hrd, _⟩ x h1 h2 h3 =>
    Classical.byContradiction fun hk =>
      absurd (hcov _ h3 hk).2 (hrd x h1 h2 (hcov _ h3 hk).1).2) hrest

/-- **A step of a lock's code keeps the program's facts**: the rest has no byte of the lock's
word. -/
theorem lstep {L : LockWord} {t : ThreadId} (h : E.Holds xs rX m) (hs : L.Step t m m')
    (hnot : ∀ l, rX.heap l ≠ Option.none → ¬ L.In l) : E.Holds xs rX m' :=
  h.keep (Lk := fun _ => False) (fun _ _ _ hk => hk.elim) hs.threads hs.clocks
    (fun e he => (hs.fp e he).imp (fun h' => ⟨e, h', .refl e⟩) fun ⟨hb, ho, hl, _⟩ x h1 h2 h3 =>
      hnot _ h3 ⟨hb, by omega, by omega⟩) fun _ _ _ hh => hh

/-- A step that keeps the thread table and the record of accesses and makes no clock smaller (a
stop, a tick). -/
theorem same (h : E.Holds xs rX m) (hth : m'.threads = m.threads)
    (hcl : ∀ u : Nat, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (hfp : m'.footprint = m.footprint) : E.Holds xs rX m' :=
  h.keep (Lk := fun _ => False) (fun _ _ _ hk => hk.elim) hth hcl
    (fun e he => .inl ⟨e, hfp ▸ he, .refl e⟩) fun _ _ _ hh => hh

/-- **The record of a read keeps the program's facts** (`FLock.Fits.wp_readRest`'s `hrec`). -/
theorem read (h : E.Holds xs rX m) (ht : m.current < m.threads.size)
    (hcs : m.clocks.size = m.threads.size) (b o len : Nat) :
    E.Holds xs rX (m.recordAt b o len .read) :=
  ⟨h.thr, h.sh.read ht hcs b o len, h.io⟩

end Holds

end FClient

end Full
end Zig
