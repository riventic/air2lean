import ZigLean.Sep.Full.RwLockGhost
import ZigLean.Sep.Full.Share
import ZigLean.Sep.Full.ThreadFacts

/-!
# The protocol of `rwLockRead` and `rwLockSnapshotPair`

`rwLockRead` and `rwLockSnapshotPair` (examples/sync, Zig 0.16.0; the 0.17.1 translation of these
programs is the same code): `main` spawns a writer, which adds 1 two times to a counter `n`, each
time between `lockUncancelable` and `unlock` of an `Io.RwLock`; `main` reads `n` between
`lockSharedUncancelable` and `unlockShared`, joins the writer, and (`rwLockRead`) reads `n` again.
The `Shared` (block 0, 64 bytes, align 8, a stack block): `io` at 0, the lock at 16 (its state
word at 16, its semaphore's count at 24, the semaphore's mutex at 32, its condition's state and
epoch at 36 and 40, the outer mutex at 48), `n` at 56.

This file is the protocol of both programs for every implementation of the lock (`RwLockImpl`):
the proof uses only the contract, at the instance every client can take (`RwProd`,
`ZigLean/Sep/Full/RwLockGhost.lean`).

- **The client part** (`Ph`): where a thread is in the program. `main` before its spawn (`pre`),
  after it (`run`), at its join (`joins`) and after it (`done`); the writer after `k` increments
  (`wr k`) and ended (`fin`).
- **The protected resource** (`R`): `n`, with the writer's increments (`cnt`: the count of thread
  1). The writer at `wr` owns it in its part, changes it and its client part together, and gives
  it back; a reader holds a share of it.
- **The program's facts** (`E`, `FClient.pre`): the threads (`Thr`: `main` alone before its spawn;
  then `main` and the writer, which did at most two increments; after `main`'s join the writer has
  ended and is joined), and the bytes of `io`, which every thread reads.
- **The protocol** (`proto`): the invariant is the two-lock product at the reader/writer lock's
  base; `fits` is `RwProd.fits`. No step lemma is proved here: the base carries the program's
  facts over every step of the lock's code.
-/

namespace Zig
namespace RwRead

open Conc Conc.Proto Full Full.FAssn

/-- Where a thread is in the program (module doc). -/
inductive Ph where
  | none
  /-- `main` before its spawn. -/
  | pre
  /-- `main` after its spawn. -/
  | run
  /-- `main` at its join. -/
  | joins
  /-- `main` after its join. -/
  | done
  /-- The writer after `k` increments. -/
  | wr (k : Nat)
  /-- The writer has ended. -/
  | fin
  deriving DecidableEq

/-- The increments of a thread. -/
def Ph.count : Ph → Nat
  | .wr k => k
  | .fin => 2
  | _ => 0

abbrev Gh := RwProd.Gh Ph

/-- The `Shared` (block 0). -/
def cPtr : Ptr := ⟨some 0, 0⟩
/-- `n`. -/
def nPtr : Ptr := cPtr.add 56

theorem o0 : cPtr.off.toNat = 0 := by simp [cPtr]
theorem o56 : nPtr.off.toNat = 56 := by simp [nPtr, cPtr, Ptr.add]

/-- The writer's increments: the writer is thread 1. -/
def cnt (Y : ThreadId → Ph) : Nat := (Y 1).count

/-- The protected resource: `n`, with the writer's increments. -/
def R (Y : ThreadId → Ph) : FAssn := up (pts nPtr 4 (BitVec.ofNat 32 (cnt Y)))

theorem R_plain : ∀ (Y : ThreadId → Ph) (r : Res), R Y r → r.know = Know.none ∧ r.gh = Ghost.unit :=
  fun _ _ h => ⟨h.2.1, h.2.2⟩

theorem R_fixed : ∀ Y : ThreadId → Ph, (R Y).FixedDom := fun _ => fixedDom_pts

/-- The bytes of `n`: `56 .. 60` of block 0. -/
theorem R_heap {Y : ThreadId → Ph} {r : Res} (h : R Y r) (l : Zig.Loc) :
    r.heap l ≠ none ↔ l.1 = 0 ∧ 56 ≤ l.2 ∧ l.2 < 60 := by
  obtain ⟨A, S, K, bs, ⟨-, hs, -, -⟩, hb⟩ := FTotalTriple.up_pts_iff_bytesAt.mp h
  have e : Enc.size (BitVec 32) = 4 := rfl
  rw [up_bytesAt_some hb (b := 0) rfl l, hs, o56, e]

/-- The reader/writer lock of the `Shared`: at byte 16 of block 0, protecting `n`. -/
noncomputable abbrev W : FRw Gh Ph (RwPh × Ph) (RwProd.M 0 16) (RwProd.L 0 16 R) (RwProd.C 0 16)
    (RwProd.S 0 16 R) :=
  RwProd.W 0 16 R R_plain R_fixed

/-! ## The program's facts -/

/-- The threads (module doc). -/
def Thr (Y : ThreadId → Ph) (ts : Array ThreadRec) : Prop :=
  ts[0]? = some { spawner := 0, joined := true } ∧
  ((ts.size = 1 ∧ Y 0 = .pre ∧ ∀ u, 1 ≤ u → Y u = .none) ∨
   (ts.size = 2 ∧ (∀ u, 2 ≤ u → Y u = .none) ∧
     ((ts[1]? = some { spawner := 0, joined := false } ∧ (Y 0 = .run ∨ Y 0 = .joins) ∧
        (Y 1 = .fin ∨ ∃ k ≤ 2, Y 1 = .wr k)) ∨
      (ts[1]? = some { spawner := 0, joined := true } ∧ Y 0 = .done ∧ Y 1 = .fin))))

/-- At most two threads. -/
theorem Thr.size_le {Y : ThreadId → Ph} {ts : Array ThreadRec} (h : Thr Y ts) : ts.size ≤ 2 := by
  obtain ⟨-, ⟨hs, -⟩ | ⟨hs, -⟩⟩ := h <;> omega

/-- The writer did at most two increments. -/
theorem Thr.cnt_le {Y : ThreadId → Ph} {ts : Array ThreadRec} (h : Thr Y ts) : cnt Y ≤ 2 := by
  obtain ⟨-, ⟨-, -, hn⟩ | ⟨-, -, ⟨-, -, h1⟩ | ⟨-, -, h1⟩⟩⟩ := h
  · unfold cnt; rw [hn 1 (by decide)]; decide
  · unfold cnt
    rcases h1 with e | ⟨k, hk, e⟩
    · rw [e]; decide
    · rw [e]; exact hk
  · unfold cnt; rw [h1]; decide

/-- A thread at a place of the writer is thread 1, with at most two increments. -/
theorem Thr.wr {Y : ThreadId → Ph} {ts : Array ThreadRec} (h : Thr Y ts) {u : ThreadId} {k : Nat}
    (hu : Y u = .wr k) : u = 1 ∧ k ≤ 2 := by
  obtain ⟨-, ⟨-, h0, hn⟩ | ⟨-, hn, ⟨-, h0, h1⟩ | ⟨-, h0, h1⟩⟩⟩ := h
  · rcases u with _ | u
    · rw [h0] at hu; cases hu
    · rw [hn (u + 1) (Nat.le_add_left 1 u)] at hu; cases hu
  · rcases u with _ | _ | u
    · rcases h0 with e | e <;> rw [e] at hu <;> cases hu
    · rcases h1 with e | ⟨k', hk', e⟩
      · rw [e] at hu; cases hu
      · rw [e] at hu; cases hu; exact ⟨rfl, hk'⟩
    · rw [hn (u + 2) (Nat.le_add_left 2 u)] at hu; cases hu
  · rcases u with _ | _ | u
    · rw [h0] at hu; cases hu
    · rw [h1] at hu; cases hu
    · rw [hn (u + 2) (Nat.le_add_left 2 u)] at hu; cases hu

/-- After `main`'s join the writer did its two increments. -/
theorem Thr.done {Y : ThreadId → Ph} {ts : Array ThreadRec} (h : Thr Y ts) (h0 : Y 0 = .done) :
    cnt Y = 2 := by
  obtain ⟨-, ⟨-, h0', -⟩ | ⟨-, -, ⟨-, h0', -⟩ | ⟨-, -, h1⟩⟩⟩ := h
  · rw [h0'] at h0; cases h0
  · rcases h0' with e | e <;> rw [e] at h0 <;> cases h0
  · unfold cnt; rw [h1]; rfl

/-- The threads after the writer's move to its next increment. -/
theorem Thr.step {Y Y' : ThreadId → Ph} {ts : Array ThreadRec} (h : Thr Y ts) {k k' : Nat}
    (h1 : Y 1 = .wr k) (hk : k' ≤ 2) (h1' : Y' 1 = .wr k') (hY : ∀ u, u ≠ 1 → Y' u = Y u) :
    Thr Y' ts := by
  obtain ⟨ht0, ⟨-, -, hn⟩ | ⟨hs, hn, ⟨ht1, h0, -⟩ | ⟨-, -, hf⟩⟩⟩ := h
  · rw [hn 1 (by decide)] at h1; cases h1
  · exact ⟨ht0, .inr ⟨hs, fun u hu => by rw [hY u (Nat.ne_of_gt hu)]; exact hn u hu,
      .inl ⟨ht1, by rw [hY 0 (by decide)]; exact h0, .inr ⟨k', hk, h1'⟩⟩⟩⟩
  · rw [hf] at h1; cases h1

/-- The bytes of `io` (`0 .. 16` of the `Shared`), which decode to `io`, at the `Shared`'s
8-aligned address. -/
def IoB (r : Res) : Prop :=
  ∃ A bs, A % 8 = 0 ∧ bs.size = 16 ∧ Enc.decode bs = pure (⟨⟩ : Io) ∧
    up (bytesAt cPtr A 64 .stack bs) r

theorem IoB.heap {r : Res} (h : IoB r) (l : Zig.Loc) : r.heap l ≠ none ↔ l.1 = 0 ∧ l.2 < 16 := by
  obtain ⟨A, bs, -, hs, -, hb⟩ := h
  rw [up_bytesAt_some hb (b := 0) rfl l, hs, o0]
  exact ⟨fun ⟨a, _, c⟩ => ⟨a, by omega⟩, fun ⟨a, c⟩ => ⟨a, Nat.zero_le _, by omega⟩⟩

/-- **The program's facts**: the threads, and the read-shared bytes of `io`. -/
def E : FClient Ph :=
  FClient.pre Thr 0 16 IoB fun _ h x hx => (h.heap (0, x)).mpr ⟨rfl, hx⟩

/-- `n` has no byte of the condition's words (`RwProd.fits`'s `hRoff`). -/
theorem R_off (Y : ThreadId → Ph) (r : Res) (l : Zig.Loc) (h : R Y r)
    (hl : (RwProd.C 0 16 (Xc := Ph)).S.In l ∨ (RwProd.C 0 16 (Xc := Ph)).Ep.In l) :
    r.heap l = none := by
  refine Classical.byContradiction fun hn => ?_
  obtain ⟨-, h1, -⟩ := (R_heap h l).mp hn
  rcases hl with ⟨-, -, h4⟩ | ⟨-, -, h4⟩
  · have h4' : l.2 < 16 + 20 + 4 := h4
    omega
  · have h4' : l.2 < 16 + 24 + 4 := h4
    omega

/-- The bytes of `io` are none of the bytes the lock's code changes (`RwProd.fits`'s `hIo`). -/
theorem io_off (r : Res) (l : Zig.Loc) (h : E.Io r) (hk : W.Lk l) : r.heap l = none := by
  refine Classical.byContradiction fun hn => ?_
  obtain ⟨-, h1⟩ := (IoB.heap h l).mp hn
  rcases hk with ⟨-, h3, -⟩ | ⟨-, h3, -⟩ | ⟨-, h3, -⟩ | ⟨Y, r', hR, hr'⟩
  · have h3' : 16 ≤ l.2 := h3
    omega
  · have h3' : 16 + 20 ≤ l.2 := h3
    omega
  · have h3' : 16 + 24 ≤ l.2 := h3
    omega
  · have := ((R_heap hR l).mp hr').2.1
    omega

/-! ## The ghost values -/

/-- A thread out of the lock's code: its part `r`, its place in the program `x`. -/
def gO (r : Res) (x : Ph) : Gh := (⟨.out, rnil, .out, rnil, r⟩, { x := x })

/-- The writer with the write lock: at `wr`, holding the outer mutex with `rM`; its part `r`. -/
def gW (r rM : Res) (x : Ph) : Gh := (⟨.holds, rM, .out, rnil, r⟩, { w := .wr, x := x })

/-- A reader with the share `q` of the heap `H`: at `rd q H`; its part `r`. -/
def gR (r : Res) (q : Frac) (H : FHeap) (x : Ph) : Gh :=
  (⟨.out, rnil, .out, rnil, r⟩, { w := .rd q H, x := x })

/-! ## The protocol -/

variable {Tgt : Type}

/-- The protocol, in strict mode; `wOf` reads the writer's argument from a spawn target. -/
noncomputable def proto (wOf : Tgt → Option Ptr) : Proto Tgt Gh where
  inv G m := ∃ rX, (RwProd.M 0 16).Inv G rX m ∧
    FLock.Pair.U (RwProd.L 0 16 R) (W.Base E 64 .stack) G rX m
  init tgt g := wOf tgt = some cPtr ∧ ∃ rp, plain rp ∧ g = gO rp (.wr 0)
  fin g := g.1.phA = .gone ∧ g.1.phB = .gone ∧ g.2 = { x := .fin } ∧
    ∀ l, g.1.part.shared l = none
  strict := true
  joins g := g.1.phA = .out ∧ g.1.phB = .out ∧ g.2 = { x := .joins }

variable {wOf : Tgt → Option Ptr}

/-- **The protocol has the reader/writer lock** (`RwProd.fits`). -/
theorem fits : W.Fits (proto wOf) (FLock.Pair.U (RwProd.L 0 16 R) (W.Base E 64 .stack))
    (FLock.Pair.U (RwProd.M 0 16) (W.Base E 64 .stack)) (fun _ => True) RwProd.okS :=
  RwProd.fits (fun _ _ => Iff.rfl)
    (fun g h => ⟨h.1, h.2.1, by rw [h.2.2.1], by rw [h.2.2.1], by rw [h.2.2.1]⟩)
    (fun g h => ⟨h.1, h.2.1, by rw [h.2.2], by rw [h.2.2], by rw [h.2.2]⟩) R_off io_off

/-- `main`'s post of `rwLockRead`: `10 * first + last`, with `first` 0, 1 or 2 and `last` 2. -/
def QRead : Except ErrName (BitVec 32) → (ThreadId → Gh) → Mem → Nat → Prop :=
  fun v _ m _ => (∃ k : Nat, k ≤ 2 ∧ v = .ok (BitVec.ofNat 32 (10 * k + 2))) ∧ joinedAll 0 m

/-- `main`'s post of `rwLockSnapshotPair`: both loads read one value, 0, 1 or 2. -/
def QPair : Except ErrName (BitVec 32) → (ThreadId → Gh) → Mem → Nat → Prop :=
  fun v _ m _ => (∃ k : Nat, k ≤ 2 ∧ v = .ok (BitVec.ofNat 32 (11 * k))) ∧ joinedAll 0 m

end RwRead
end Zig
