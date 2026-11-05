import ZigLean.Sep.Full.LockSteps

/-!
# Admission can justify a rest read without admitting every live thread

Three memory-level clock witnesses distinguish the `NoRace` premise from all-reader `ReadShared`:
reader 1 has the publication's clock; unrelated thread 2 does not. A separate conditional
32-bit-load control applies `FLock.Inv.loadRest` to points-to bytes in an arbitrary invariant's
rest. These are clock and library-interface controls, not complete RwLock executions.
-/

open Zig Zig.Conc
open Zig.Full Zig.Full.FAssn

namespace SepAuto.ReadRest

private def publication : FootprintEntry :=
  { tid := 0, clock := #[1, 0, 0], block := 0, off := 0, len := 4, kind := .write }

private def readerMemory (t : ThreadId) : Mem :=
  { current := t
    threads := #[{ spawner := 0, joined := true }, { spawner := 0, joined := false },
      { spawner := 0, joined := false }]
    clocks := #[#[1, 0, 0], #[1, 1, 0], #[0, 0, 1]]
    footprint := #[publication] }

/-- The admitted reader's clock covers the publication and its read is race-free. -/
theorem admitted_read_noRace : NoRace (readerMemory 1) 0 0 4 .read := by
  unfold NoRace
  decide +kernel

/-- An unrelated live thread did not acquire the publication; admitting it would permit a race. -/
theorem unadmitted_read_races : ¬ NoRace (readerMemory 2) 0 0 4 .read := by
  unfold NoRace
  decide +kernel

/-- Race-free admission of one reader does not imply admission of every live thread. -/
theorem admitted_is_not_readShared : ¬ ReadShared (fun e => e.block = 0) (readerMemory 1) := by
  intro hs
  have hs2 : ReadShared (fun e => e.block = 0) (readerMemory 2) := hs
  exact unadmitted_read_races
    (hs2.noRace_read (by decide) (fun _ hb _ _ _ => hb))

/-- A 32-bit points-to assertion in invariant rest supplies a direct instance of the load fact. -/
theorem load_u32_from_rest {γ : Type} {L : FLock γ} {G : ThreadId → γ} {m : Mem}
    {rX r : Res} {p : Ptr} {b : BlockId} {t : ThreadId} {v : BitVec 32}
    (hi : L.Inv G rX m) (hr : up (pts p 4 v) r)
    (hsub : ∀ l fc, r.heap l = some fc → rX.heap l = some fc)
    (hpb : p.block = some b) (hc : m.current = t) (hg : L.ph (G t) ≠ .gone)
    (hread : NoRace m b p.off.toNat 4 .read) :
    (load (BitVec 32) 4 p).run m = pure (v, m.recordAt b p.off.toNat 4 .read) ∧
      L.Inv G rX (m.recordAt b p.off.toNat 4 .read) := by
  obtain ⟨A, S, K, bs, ⟨ha, hbs, hdec, hK⟩, hbytes⟩ := FTotalTriple.up_pts_iff_bytesAt.mp hr
  exact hi.loadRest hpb (by decide) ⟨r, A, S, K, bs, hbytes, hsub, hbs, hdec, ha, hK⟩
    hc hg hread

/-- The only thread that has not left the lock reads 32 bits of the lock's complete rest (the
protocol's rest, the word's cells and the free lock's resource): `FLock.Inv.loadAll`. -/
theorem load_u32_by_sole {γ : Type} {L : FLock γ} {G : ThreadId → γ} {m : Mem}
    {rX : Res} {p : Ptr} {b : BlockId} {t : ThreadId} {v : BitVec 32}
    (hi : L.Inv G rX m)
    (hr : ∀ rL, (L.Free G → L.R G rL) → (¬ L.Free G → rL = rnil) → L.Off rL.heap.erase →
      FHeap.Disjoint rL.heap rX.heap → ∃ r, up (pts p 4 v) r ∧
      ∀ l fc, r.heap l = some fc → (rsum (L.wordR m) (rsum rL rX)).heap l = some fc)
    (hpb : p.block = some b) (hc : m.current = t) (hg : L.ph (G t) ≠ .gone)
    (hsole : ∀ u < m.threads.size, u ≠ t → L.ph (G u) = .gone)
    (hread : NoRace m b p.off.toNat 4 .read) :
    (load (BitVec 32) 4 p).run m = pure (v, m.recordAt b p.off.toNat 4 .read) ∧
      L.Inv G rX (m.recordAt b p.off.toNat 4 .read) := by
  refine hi.loadAll hpb (by decide) (fun rL hF hnF hoff hd _ => ?_) hc hg hsole hread
  obtain ⟨r, hr, hsub⟩ := hr rL hF hnF hoff hd
  obtain ⟨A, S, K, bs, ⟨ha, hbs, hdec, hK⟩, hbytes⟩ := FTotalTriple.up_pts_iff_bytesAt.mp hr
  exact ⟨r, A, S, K, bs, hbytes, fun l fc h => ⟨fc, hsub l fc h, rfl⟩, hbs, hdec, ha, hK⟩

end SepAuto.ReadRest
