import Proofs.RwRead.Ops
import ZigLean.Sep.Full.AutoWP

/-!
# The end of `rwLockRead` and `rwLockSnapshotPair`

`main`'s end, once for both programs and for every implementation of the lock: after its join
(`done`) `main` frees the `Shared` (block 0, a stack block) and returns.

- `Thr.spawner0`, `Thr.allJoined`: `main` spawned every thread, and at `done` every thread is
  joined (the program's threads' fact, `Thr`).
- `wp_free`: the free of the `Shared` by `main` at `done`, from the invariant alone. The model's
  `free` asks three things of the block: it is live, it is no `const` global, and its end races
  with no access (`Mem.freeRaces`). The block's facts are the base's pin (`FRw.Base.inv_blk`).
  The end of a block races with no access when every other thread is a child of the current
  thread that it joined (`freeRaces_of_joined`): `Mem.freeRaces` exempts the accesses of such a
  thread, so the free needs no fact about the clocks and no ownership of the block's bytes.
  `main` takes nothing out of the invariant (no `RwProd.stop`): after its join it reads `n` only
  under the read lock (`readShared`), and the free is its last step. After the free every thread
  is joined (`joinedAll 0`).
- `QRead.result`, `QPair.result`: the values of the posts (2, 12 or 22; 0, 11 or 22).
-/

namespace Zig

namespace Conc.Proto

open Full

/-- **A checked unsigned `*` that does not overflow** (as `WP.liftMem_add`): its value as a fact.
(Should move to `ZigLean/Sep/Full/AutoWP.lean`, next to `WP.liftMem_add` and `WP.liftMem_sub`,
with their `@[fsym]` registration.) -/
theorem WP.liftMem_mul {Tgt γ : Type} {P : Proto Tgt γ} {t : ThreadId} {G : ThreadId → γ}
    {m : Mem} {n : Nat} {w : Nat} {a b : BitVec w} {safe : Bool}
    {Q : BitVec w → (ThreadId → γ) → Mem → Nat → Prop}
    (hlt : a.toNat * b.toNat < 2 ^ w)
    (h : ∀ r : BitVec w, r.toNat = a.toNat * b.toNat → Q r G m n) :
    P.WP t (ConcM.liftMem (StateT.lift (Zig.mul false a b safe) : MemM (BitVec w)) :
      ConcM Tgt (BitVec w)) Q G m n :=
  WP.liftMem_pure (by rw [Auto.mul_ok hlt]; rfl) rfl
    (h _ (by rw [BitVec.toNat_mul, Nat.mod_eq_of_lt hlt]))

end Conc.Proto

namespace RwRead

open Conc Conc.Proto Full Full.FAssn

variable {Tgt : Type} {wOf : Tgt → Option Ptr}

/-! ## The threads at the end -/

/-- `main` spawned every thread. -/
theorem Thr.spawner0 {Y : ThreadId → Ph} {ts : Array ThreadRec} (h : Thr Y ts) :
    ∀ r ∈ ts, r.spawner = 0 := by
  intro r hr
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hr
  obtain ⟨h0, ⟨hs, -⟩ | ⟨hs, -, ⟨h1, -⟩ | ⟨h1, -⟩⟩⟩ := h
  · obtain rfl : i = 0 := by omega
    rw [Array.getElem?_eq_getElem hi] at h0; rw [Option.some.inj h0]
  · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · rw [Array.getElem?_eq_getElem hi] at h0; rw [Option.some.inj h0]
    · rw [Array.getElem?_eq_getElem hi] at h1; rw [Option.some.inj h1]
  · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · rw [Array.getElem?_eq_getElem hi] at h0; rw [Option.some.inj h0]
    · rw [Array.getElem?_eq_getElem hi] at h1; rw [Option.some.inj h1]

/-- After `main`'s join there are two threads, and the writer is joined. -/
theorem Thr.allJoined {Y : ThreadId → Ph} {ts : Array ThreadRec} (h : Thr Y ts)
    (h0 : Y 0 = .done) :
    ts[0]? = some { spawner := 0, joined := true } ∧ ts.size = 2 ∧
      ts[1]? = some { spawner := 0, joined := true } := by
  obtain ⟨ht0, ⟨-, h0', -⟩ | ⟨hs, -, ⟨-, h0', -⟩ | ⟨h1, -, -⟩⟩⟩ := h
  · rw [h0'] at h0; cases h0
  · rcases h0' with e | e <;> rw [e] at h0 <;> cases h0
  · exact ⟨ht0, hs, h1⟩

/-- After `main`'s join every thread is joined. -/
theorem inv_joinedAll {G : ThreadId → Gh} {m : Mem} {g : Gh} (hg : g.2.x = .done)
    (hi : (proto wOf).inv (upd G 0 g) m) : joinedAll 0 m := by
  obtain ⟨h0, hs2, h1⟩ := (thr_of hi).allJoined
    (by show (upd G 0 g 0).2.x = _; rw [upd_self]; exact hg)
  intro r hr _
  obtain ⟨i, hi', rfl⟩ := Array.mem_iff_getElem.mp hr
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · rw [Array.getElem?_eq_getElem hi'] at h0; rw [Option.some.inj h0]
  · rw [Array.getElem?_eq_getElem hi'] at h1; rw [Option.some.inj h1]

/-! ## The free of the `Shared` -/

/-- **`main`'s free of the `Shared`** after its join (module doc): the block is live and a stack
block (the base's pin), and its end races with no access: the writer is a child of `main` that
`main` joined (`freeRaces_of_joined`). After it every thread is joined. -/
theorem wp_free {G : ThreadId → Gh} {m : Mem} {n : Nat} {rp : Res}
    (hi : (proto wOf).inv (upd G 0 (gO rp .done)) m) (hc : m.current = 0)
    {Q : Unit → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ m', m'.threads = m.threads → joinedAll 0 m' → Q () G m' n) :
    (proto wOf).WP 0 (ConcM.liftMem (free cPtr) : ConcM Tgt Unit) Q G m n := by
  obtain ⟨blk, hblk, hl, -, hk⟩ := FRw.Base.inv_blk (W := W) (E := E) hi
  have hblk' : m.blocks[0]? = some blk := hblk
  have hj : joinedAll 0 m := inv_joinedAll rfl hi
  obtain ⟨-, hs2, h1⟩ := (thr_of hi).allJoined
    (by show (upd G 0 (gO rp .done) 0).2.x = _; rw [upd_self]; rfl)
  have hcs : m.clocks.size = m.threads.size := by
    obtain ⟨rX, hM, -⟩ := hi
    exact hM.w.csize
  have hnr : m.freeRaces 0 blk.bytes.size = false := freeRaces_of_joined hcs fun u hu => by
    rw [hs2] at hu
    rcases (by omega : u = 0 ∨ u = 1) with rfl | rfl
    · exact .inl hc.symm
    · exact .inr ⟨_, h1, hc.symm, rfl, rfl⟩
  refine WP.liftMem (fun e he => (free_noErr hblk' hl hnr (by rw [hk]; nofun) e he).elim)
    fun _ m' hfr => ?_
  obtain ⟨b', blk', -, -, rfl⟩ := free_ok hfr
  exact ⟨rfl, h _ rfl (joinedAll_of_threads hj rfl)⟩

/-! ## The posts' values -/

/-- `rwLockRead`'s post at its return: `10 * first + last`, with `first ≤ 2` and `last = 2`. -/
theorem QRead.intro {k : Nat} {G : ThreadId → Gh} {m : Mem} {d : Nat} (hk : k ≤ 2)
    (hj : joinedAll 0 m) : QRead (.ok (BitVec.ofNat 32 (10 * k + 2))) G m d :=
  ⟨⟨k, hk, rfl⟩, hj⟩

/-- `rwLockSnapshotPair`'s post at its return: both loads read `k ≤ 2`. -/
theorem QPair.intro {k : Nat} {G : ThreadId → Gh} {m : Mem} {d : Nat} (hk : k ≤ 2)
    (hj : joinedAll 0 m) : QPair (.ok (BitVec.ofNat 32 (11 * k))) G m d :=
  ⟨⟨k, hk, rfl⟩, hj⟩

/-- `rwLockRead`'s post from the value of its result (`10 * first + last` as the walk's checked
`*` and `+` give it). -/
theorem QRead.of_toNat {r : BitVec 32} {k : Nat} {G : ThreadId → Gh} {m : Mem} {d : Nat}
    (hr : r.toNat = 10 * k + 2) (hk : k ≤ 2) (hj : joinedAll 0 m) : QRead (.ok r) G m d :=
  ⟨⟨k, hk, by rw [← hr]; simp⟩, hj⟩

/-- `rwLockSnapshotPair`'s post from the value of its result. -/
theorem QPair.of_toNat {r : BitVec 32} {k : Nat} {G : ThreadId → Gh} {m : Mem} {d : Nat}
    (hr : r.toNat = 11 * k) (hk : k ≤ 2) (hj : joinedAll 0 m) : QPair (.ok r) G m d :=
  ⟨⟨k, hk, by rw [← hr]; simp⟩, hj⟩

/-- `rwLockRead` gives 2, 12 or 22. -/
theorem QRead.result {v : Except ErrName (BitVec 32)} {G : ThreadId → Gh} {m : Mem} {d : Nat}
    (h : QRead v G m d) : v = .ok 2 ∨ v = .ok 12 ∨ v = .ok 22 := by
  obtain ⟨⟨k, hk, rfl⟩, -⟩ := h
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr rfl)

/-- `rwLockSnapshotPair` gives 0, 11 or 22. -/
theorem QPair.result {v : Except ErrName (BitVec 32)} {G : ThreadId → Gh} {m : Mem} {d : Nat}
    (h : QPair v G m d) : v = .ok 0 ∨ v = .ok 11 ∨ v = .ok 22 := by
  obtain ⟨⟨k, hk, rfl⟩, -⟩ := h
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr rfl)

end RwRead
end Zig
