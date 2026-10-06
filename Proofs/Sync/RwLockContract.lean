import Proofs.Sync.RwLock

/-!
# Restricted shared-lock contract boundary

This adapter reuses the existing Zig 0.16 `Sync.Tgt` primitive proofs. Its protocol still
has main reader 0, writer 1, the original layout, and the writer count bounded by 2.
`ProtectedFacts` exposes caller assertions entailed by the existing protected counter
resource; it does not replace that resource with an arbitrary heap assertion.

The full protocol invariant and semaphore `E.Spec` remain premises of acquire/release.
In particular, snapshot facts alone cannot justify unlock, join, or reclamation.
ROOT has exported the new source client; kernel qualification of this adapter and client
proof candidates is still pending.
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Conc.Lock Sync Assn
open Sync.RwLockRead

namespace Sync.RwLockContract

/-- Caller facts obtained from the concrete counter resource while the shared lock is held.
Only projections of `NPts` are admitted; this is not an arbitrary-resource RwLock kit. -/
structure ProtectedFacts (R : Nat → Assn) : Prop where
  project : ∀ k h, NPts k h → R k h

variable {S : Type} [Inhabited S] {E : Sync.RwLockRead.Sem S}

/-- The held protocol state exposes the protected counter and any admitted caller facts.
The invariant is retained by the caller; this theorem does not consume or transfer it. -/
theorem held_facts {R : Nat → Assn} (facts : ProtectedFacts R) {j : Bool}
    {G : ThreadId → Gh S} {m : Mem} {h : Heap}
    (hi : (proto E).inv (upd G 0 (gA (.sh j) h default)) m) :
    NPts (G 1).2.2.cnt h ∧ R (G 1).2.2.cnt h := by
  have hp : NPts (G 1).2.2.cnt h := by
    have hp := hi.2.1.parts 0
    rw [upd_self, upd0_1] at hp
    simpa [gA, Ph.mustN] using hp
  exact ⟨hp, facts.project _ _ hp⟩

/-- Shared acquire transfers ownership through the original resource/clock invariant.
Caller facts are exposed only after the existing primitive proof obtains the owned heap. -/
theorem acquire_shared {R : Nat → Assn} (facts : ProtectedFacts R) (hE : E.Spec)
    {j : Bool} {io : Io} {G : ThreadId → Gh S} {m : Mem} {d : Nat}
    (hi : (proto E).inv (upd G 0 (gA (.ls j) Heap.empty default)) m) :
    (proto E).WP 0 (Io_RwLock_lockSharedUncancelable (bPtr.add 16) io)
      (fun _ G' m' d' => d' ≤ d ∧ m'.current = 0 ∧ ∃ h,
        R (G' 1).2.2.cnt h ∧
        (proto E).inv (upd G' 0 (gA (.sh j) h default)) m') G m d := by
  refine WP.mono ?_ (lockS_spec hE hi)
  rintro _ G' m' d' ⟨hd, hc, h, hi'⟩
  exact ⟨hd, hc, h, (held_facts facts hi').2, hi'⟩

/-- Release is exactly the existing primitive contract, including its complete protocol
and semaphore-transfer premises. No local copy of the implementation proof is introduced. -/
abbrev release_shared := @Sync.RwLockRead.unlockS_spec

/-- The existing one-read client contract exposes an arbitrary pure snapshot consequence.
This does not claim that two separate acquisitions observe equal values. -/
theorem read_with_facts {F : Nat → Prop} (facts : ∀ k, k ≤ 2 → F k) (hE : E.Spec)
    {j : Bool} {G : ThreadId → Gh S} {m : Mem} {d : Nat}
    (hi : (proto E).inv (upd G 0 (gA (.ls j) Heap.empty default)) m)
    (hc : m.current = 0) :
    (proto E).WP 0 (readShared bPtr) (fun v G' m' _ => m'.current = 0 ∧
      (∃ k ≤ 2, v = BitVec.ofNat 32 k ∧ (j = true → k = 2) ∧ F k) ∧
      (proto E).inv (upd G' 0 (gA (.dn j) Heap.empty default)) m') G m d := by
  refine WP.mono ?_ (readS_spec hE hi hc)
  rintro v G' m' d' ⟨hc', ⟨k, hk, hv, hj⟩, hi'⟩
  exact ⟨hc', ⟨k, hk, hv, hj, facts k hk⟩, hi'⟩

/-- Two plain loads by the owner observe the same value and retain the resource.
This is a primitive memory fragment contract, not a generated client definition. -/
theorem load_pair_owned {T : Type} [Enc T] {p : Ptr} {a : Nat} {v : T}
    (hn : 0 < Enc.size T) :
    TTriple (pts p a v)
      (do let first ← Zig.load T a p
          let second ← Zig.load T a p
          pure (first, second))
      (fun pair => ⌜pair = (v, v)⌝ ∗ pts p a v) := by
  refine TTriple.bind_eq (TTriple.load hn) ?_
  refine TTriple.bind_eq (TTriple.load hn) ?_
  exact (TTriple.ret (Q := fun pair => ⌜pair = (v, v)⌝ ∗ pts p a v) (v, v)).conseq
    (fun _ hp => sep_lift.mpr ⟨rfl, hp⟩) (fun _ _ hp => hp)

/-- A disjoint owned caller frame remains unchanged across the two loads.
For a concrete sentinel instantiate `F` with its points-to assertion. This is a local
frame rule; the client must separately preserve ownership through calls, release and join. -/
theorem load_pair_frame {T : Type} [Enc T] {p : Ptr} {a : Nat} {v : T} {F : Assn}
    (hn : 0 < Enc.size T) :
    TTriple (pts p a v ∗ F)
      (do let first ← Zig.load T a p
          let second ← Zig.load T a p
          pure (first, second))
      (fun pair => ⌜pair = (v, v)⌝ ∗ (pts p a v ∗ F)) :=
  (load_pair_owned hn).frame_eq

/-- A single optimized snapshot load remains owned at the shared-held phase.
This is the bridge for an export that merges the source's two identical reads. -/
theorem held_snapshot_wp (hE : E.Spec) {σ : Type} {s : σ} {j : Bool}
    {G : ThreadId → Gh S} {m : Mem} {d : Nat} {h : Heap}
    (hi : (proto E).inv (upd G 0 (gA (.sh j) h default)) m)
    (hc : m.current = 0) :
    (proto E).WP 0
      ((liftM (Zig.load (BitVec 32) 4 nPtr) : CM Tgt σ (BitVec 32)).run s)
      (fun snapshot G' m' _ =>
        snapshot = (BitVec.ofNat 32 (G 1).2.2.cnt, s) ∧
        m'.current = 0 ∧ ∃ h',
          (proto E).inv (upd G' 0 (gA (.sh j) h' default)) m') G m d := by
  refine wp_n (r₀ := BitVec.ofNat 32 (G 1).2.2.cnt) hE hi hc rfl (.inl rfl) ?_ ?_
  · simpa only [NPts, upd0_1] using
      (TTriple.load (p := nPtr) (a := 4)
        (v := BitVec.ofNat 32 (G 1).2.2.cnt) (by decide))
  · intro m' h' hc' _ hi'
    exact ⟨rfl, hc', h', hi'⟩

/-- The restricted RwLock protocol justifies the same-held primitive two-load fragment.
There is no release, yield or reacquire between the loads. The existing `wp_n` rule carries
ownership and clock safety; no equality of snapshots is added as a hypothesis.
An actual optimized export with one load will instead use the original `wp_n` load rule. -/
theorem held_pair_wp (hE : E.Spec) {σ : Type} {s : σ} {j : Bool}
    {G : ThreadId → Gh S} {m : Mem} {d : Nat} {h : Heap}
    (hi : (proto E).inv (upd G 0 (gA (.sh j) h default)) m)
    (hc : m.current = 0) :
    (proto E).WP 0
      ((liftM (do
          let first ← Zig.load (BitVec 32) 4 nPtr
          let second ← Zig.load (BitVec 32) 4 nPtr
          pure (first, second)) : CM Tgt σ (BitVec 32 × BitVec 32)).run s)
      (fun pair G' m' _ =>
        pair = ((BitVec.ofNat 32 (G 1).2.2.cnt,
                 BitVec.ofNat 32 (G 1).2.2.cnt), s) ∧
        m'.current = 0 ∧ ∃ h',
          (proto E).inv (upd G' 0 (gA (.sh j) h' default)) m') G m d := by
  refine wp_n (r₀ := (BitVec.ofNat 32 (G 1).2.2.cnt,
    BitVec.ofNat 32 (G 1).2.2.cnt)) hE hi hc rfl (.inl rfl) ?_ ?_
  · simpa only [NPts, upd0_1] using
      (load_pair_owned (p := nPtr) (a := 4)
        (v := BitVec.ofNat 32 (G 1).2.2.cnt) (by decide))
  · intro m' h' hc' _ hi'
    exact ⟨rfl, hc', h', hi'⟩

/-- The existing protocol's join flag entails that every spawned task is joined.
This includes the `.ls true` state returned by `inv_join`; a second shared acquisition
is not needed merely to establish the allocation-lifetime boundary. -/
theorem joined_of_phase {G : ThreadId → Gh S} {m : Mem} {x : Ph}
    {h : Heap} {sx : S}
    (hi : (proto E).inv (upd G 0 (gA x h sx)) m) (hjd : x.jd = true) :
    joinedAll 0 m := by
  obtain ⟨h0, ⟨_, hp, _⟩ | ⟨hs2, hr, _, _, _⟩⟩ := hi.2.1.shape
  · change (upd G 0 _ 0).2.2 = .pre at hp
    rw [upd_self] at hp
    have hx : x = .pre := hp
    subst x
    cases hjd
  have hj1 : m.threads[1]? = some { spawner := 0, joined := true } := by
    rcases hr with ⟨_, hd⟩ | ⟨h1, _⟩
    · change (upd G 0 _ 0).2.2.jd = false at hd
      rw [upd_self] at hd
      change x.jd = false at hd
      rw [hjd] at hd
      cases hd
    · exact h1
  intro r hr _
  obtain ⟨i, hi', rfl⟩ := Array.mem_iff_getElem.mp hr
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · rw [Array.getElem?_eq_getElem hi'] at h0
    rw [Option.some.inj h0]
  · rw [Array.getElem?_eq_getElem hi'] at hj1
    rw [Option.some.inj hj1]

/-- Reclaim the original live stack allocation only at a joined protocol phase.
The successful free preserves the thread roster and the joined obligation. The full
protocol is deliberately not asserted after reclamation: its `BlkOk` requires a live
allocation. A generated client must establish this precondition through release/join. -/
theorem reclaim_joined_wp {G : ThreadId → Gh S} {m : Mem} {d : Nat} {x : Ph}
    {h : Heap} {sx : S}
    (hi : (proto E).inv (upd G 0 (gA x h sx)) m) (hjd : x.jd = true) :
    (proto E).WP 0 (ConcM.liftMem (free bPtr))
      (fun _ _ m' _ => m'.threads = m.threads ∧ joinedAll 0 m') G m d := by
  have hj := joined_of_phase hi hjd
  obtain ⟨blk, hb, hl, _⟩ := hi.2.1.blk
  refine WP.liftMem (fun e he => (free_noErr hb hl e he).elim) ?_
  intro _ m' hf
  obtain ⟨_, _, _, _, rfl⟩ := free_ok hf
  exact ⟨rfl, rfl, hj⟩

/-- Joining a finished thread transfers its part to the parent through the existing clock
merge/ownership rule. This does not itself authorize freeing an allocation: the client
still needs the allocation's live/last-access and all relevant task-join obligations. -/
abbrev join_owned_parts := @Zig.Owned.join

end Sync.RwLockContract
