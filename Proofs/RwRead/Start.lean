import Proofs.RwRead.Protocol
import ZigLean.Sep.Full.RwProdBytes
import ZigLean.Sep.Full.Local

/-!
# The start of `rwLockRead`'s and `rwLockSnapshotPair`'s protocol

Both programs start the same way: `main` (thread 0, alone) allocates the `Shared` (block 0, a
stack block of 64 bytes) and stores `io` (bytes `0 .. 16`), the fresh `Io.RwLock` (`16 .. 56`) and
`n = 0` (`56 .. 60`; `60 .. 64` is the `Shared`'s padding).

- **The start** (`inv_start`): `main`, before its spawn, owns the `Shared`'s bytes after its
  stores, with the block's extent and the plain mode. The protocol's invariant holds with `main`
  at `pre`, its part the plain mode, and every other thread ended. The lock's 40 bytes are split
  once for every program (`RwProd.start_bytes`, at block 0, offset 16); this file says only what
  the bytes outside the lock are: `n` is the protected resource (`R` at no increment), `io` and
  the padding after `n` go to the rest (`io` is the bytes every thread reads, `IoB`).

The statement has the shape of `Proofs/SemCounter/Start.lean`'s `inv_start`, so a walk of `main`
applies it at the spawn from `FOwned.start0_facts` (`fsym [FTriple.allocStack', inv_start, …]`).
The walk of `main`'s stores into its own stack block needs the rules of
`ZigLean/Sep/Full/Local.lean` (`FTotalTriple.storeBytesAt`), which this file imports for them.
-/

namespace Zig
namespace RwRead

open Conc Conc.Proto Full Full.FAssn

variable {Tgt : Type} {wOf : Tgt → Option Ptr}

/-- No thread at the start. -/
def G0 : ThreadId → Gh := fun _ => (⟨.gone, rnil, .gone, rnil, rnil⟩, { x := .none })

/-- `n`'s pointer as the lock's library writes a pointer of block 0. -/
theorem p56 : RwProd.p 0 56 = nPtr := by
  first
    | rfl
    | simp [RwProd.p, nPtr, cPtr, Ptr.add]

/-- **Before the spawn**: `main` owns the `Shared` after its stores (the bytes `bs`: `io`, the
lock's state word 0, the semaphore's count 0, its mutex 0, the condition's state and epoch 0, the
outer mutex 0, `n = 0`), with its extent, and the plain mode (module doc). The protocol's
invariant holds with `main` at `pre`, its part the plain mode. -/
theorem inv_start {m : Mem} {r : Res} {A : Nat} {bs : Array Byte}
    (ho : FOwned (upd (fun _ => rnil) 0 r) rnil m)
    (hF : ((up (bytesAt cPtr A 64 .stack bs) ⋆ bext 0 64 .stack) ⋆ plain) r)
    (hs : bs.size = 64)
    (hIo : bs.extract 0 16 = Enc.encode (⟨⟩ : Io))
    (hSt : bs.extract 16 24 = Enc.encode (0 : BitVec 64))
    (hCn : bs.extract 24 32 = Enc.encode (0 : BitVec 64))
    (hL : bs.extract 32 36 = Enc.encode (0 : BitVec 32))
    (hS : bs.extract 36 40 = Enc.encode (0 : BitVec 32))
    (hE : bs.extract 40 44 = Enc.encode (0 : BitVec 32))
    (hM : bs.extract 48 52 = Enc.encode (0 : BitVec 32))
    (hN : bs.extract 56 60 = Enc.encode (0 : BitVec 32))
    (hA : A % 8 = 0) (hth : m.threads = #[{ spawner := 0, joined := true }])
    (hat : m.atomics = #[]) (hq : m.waiters = #[]) :
    ∃ rM, rM.Plain ∧ (proto wOf).inv (upd G0 0 (gO rM .pre)) m := by
  have h1 : m.threads.size = 1 := by rw [hth]; rfl
  have ht : 0 < m.threads.size := by rw [h1]; decide
  have hjt : joinedB m 0 = false := by simp [joinedB, hth]
  have hF' : ((up (bytesAt (RwProd.p 0 0) A 64 .stack bs) ⋆ bext 0 64 .stack) ⋆ plain)
      (upd (fun _ => rnil) 0 r 0) := by
    rw [upd_self]; exact hF
  obtain ⟨rM, hpM, H⟩ := RwProd.start_bytes (Xc := Ph) (b := 0) (o := 16) (R := R)
    (R_plain := R_plain) (R_fixed := R_fixed) (E := E) (Sz := 64) (K := .stack) (Q := plain)
    (e0 := 0) ho hjt ht hF' (by omega) (by omega) (by decide)
    (by first | decide | simp [BlockKind.mappedLo]) hSt hCn hL hS hE hM
    (fun l hl => by rw [hat] at hl; simp at hl) hq (allLe_of_one h1 (VClock.le_refl _))
  refine ⟨rM, Res.plain_of hpM, ?_⟩
  -- the ghost values
  have hGu : ∀ u, u ≠ 0 → upd G0 0 (gO rM .pre) u = G0 u := fun u h => upd_ne _ _ h
  have hcnt : cnt (fun u => (upd G0 0 (gO rM .pre) u).2.x) = 0 := by
    show ((upd G0 0 (gO rM .pre) 1).2.x).count = 0
    rw [hGu 1 (by decide)]; rfl
  -- the bytes after the lock: `n` and the padding
  have tail_cut : ∀ r', up (bytesAt (RwProd.p 0 56) A 64 .stack (bs.extract 56 64)) r' →
      (up (bytesAt (RwProd.p 0 56) A 64 .stack (bs.extract 56 60)) ⋆
        up (bytesAt (RwProd.p 0 60) A 64 .stack (bs.extract 60 64))) r' := fun r' h => by
    have h0 : up (bytesAt ((RwProd.p 0 0).add ((56 : Nat) : Int)) A 64 .stack
        (bs.extract 56 64)) r' := by
      rw [RwProd.p_add]; exact h
    have h2 := up_bytesAt_cut (b := 60) h0 (by omega) (by omega) (by omega)
    rwa [RwProd.p_add, RwProd.p_add] at h2
  have reorder : ∀ a n q : FAssn, (a ⋆ (n ⋆ q)) = (n ⋆ (a ⋆ q)) := by intros; ac_rfl
  have hR0 : ∀ r', up (bytesAt (RwProd.p 0 56) A 64 .stack (Enc.encode (0 : BitVec 32))) r' →
      R (fun u => (upd G0 0 (gO rM .pre) u).2.x) r' := fun r' hx => by
    show up (pts nPtr 4 (BitVec.ofNat 32 (cnt fun u => (upd G0 0 (gO rM .pre) u).2.x))) r'
    rw [hcnt]
    rw [p56] at hx
    exact ⟨⟨A, 64, .stack, Enc.encode (0 : BitVec 32), by rw [o56]; omega,
      LawfulEnc.size_encode _, LawfulEnc.decode_encode _, hx.1, by decide⟩, hx.2.1, hx.2.2⟩
  refine H (upd G0 0 (gO rM .pre))
    (up (bytesAt (RwProd.p 0 0) A 64 .stack (bs.extract 0 16)) ⋆
      up (bytesAt (RwProd.p 0 60) A 64 .stack (bs.extract 60 64)))
    (by rw [upd_self]; rfl) (fun u hu => ?_) (fun r' h => ?_) ?_ (fun u => ?_) (fun u => ?_)
    (fun u => ?_) ?_
  · -- the other threads own nothing
    rw [upd_ne _ _ hu]
    unfold FLock.own; rw [hGu u hu]
    split <;> first
      | rfl
      | exact rnil_rsum rnil
      | simp [G0, FLock.prodA, rnil_rsum]
  · -- `n` to the lock, `io` and the padding to the rest
    rw [hs] at h
    have h1' : (up (bytesAt (RwProd.p 0 0) A 64 .stack (bs.extract 0 16)) ⋆
        (up (bytesAt (RwProd.p 0 56) A 64 .stack (bs.extract 56 60)) ⋆
          up (bytesAt (RwProd.p 0 60) A 64 .stack (bs.extract 60 64)))) r' :=
      sep_mono_right tail_cut h
    rw [hN, reorder] at h1'
    exact sep_mono_left hR0 h1'
  · -- the rest holds the bytes of `io`
    rintro _ ⟨r₁, r₂, -, rfl, h₁, -⟩
    refine ⟨r₁, (⟨A, bs.extract 0 16, hA, by simp [hs],
      by rw [hIo]; exact LawfulEnc.decode_encode _, h₁⟩ : IoB r₁), fun l fc h => ?_⟩
    show (r₁.heap l).or (r₂.heap l) = some fc
    rw [h]; rfl
  · by_cases hu : u = 0
    · subst hu; rw [upd_self]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · rw [hGu u hu]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · by_cases hu : u = 0
    · subst hu; rw [upd_self]; exact .inl ⟨rfl, ht, hjt⟩
    · rw [hGu u hu]; exact .inr rfl
  · by_cases hu : u = 0
    · subst hu; rw [upd_self]; exact .inl ⟨rfl, ht, hjt⟩
    · rw [hGu u hu]; exact .inr rfl
  · -- the threads: `main` alone, before its spawn
    show Thr (fun u => (upd G0 0 (gO rM .pre) u).2.x) m.threads
    refine ⟨by rw [hth]; rfl, .inl ⟨h1, ?_, fun u hu => ?_⟩⟩
    · show (upd G0 0 (gO rM .pre) 0).2.x = .pre
      rw [upd_self]; rfl
    · show (upd G0 0 (gO rM .pre) u).2.x = .none
      rw [hGu u (by unfold ThreadId at *; omega)]; rfl

end RwRead
end Zig
