import ZigLean.Sep.Full.LockWord

namespace LockWordLocations

open Zig Zig.Full

/-- The native field retains the former new-record obligation for arbitrary states. -/
theorem new_record_obligation {L : LockWord} {t : ThreadId} {m m' : Mem}
    (hs : L.Step t m m') {l : ALoc} (hl : l ∈ m'.atomics) :
    l ∈ m.atomics ∨ (l.block = L.b ∧ l.off = L.o ∧ l.len = 4) := by
  rcases hs.atomic_mem hl with h | h
  · exact .inl h
  · exact .inr (by simpa only [Zig.Full.ALoc.shape, LockWord.shape, Prod.mk.injEq] using h)

/-- The former outside-address obligation includes the index and complete record. -/
theorem outside_first_obligation {L : LockWord} {t : ThreadId} {m m' : Mem}
    (hs : L.Step t m m') (b o : Nat) (hne : b ≠ L.b ∨ o ≠ L.o) (i : Nat) (l : ALoc) :
    (m'.atomics.findIdx? (fun l => l.block == b && l.off == o) = some i ∧
      m'.atomics[i]? = some l) ↔
    (m.atomics.findIdx? (fun l => l.block == b && l.off == o) = some i ∧
      m.atomics[i]? = some l) := hs.first_iff b o hne i l

private def lock : LockWord := { b := 0, o := 8 }
private def word : ALoc := ⟨0, 8, 4, #[]⟩
private def other : ALoc := ⟨0, 10, 4, #[]⟩
private def changedOther : ALoc :=
  { other with msgs := #[{ id := 7, bytes := #[], clock := #[], relClock := #[] }] }

/-- Deliberately overlapping records: these controls test the summary without an
unstated global non-overlap or valid-message-chain premise. -/
private def before : Mem := { atomics := #[word, other] }
private def changed : Mem := { before with atomics := #[word, changedOther] }
private def retired : Mem := { before with atomics := #[word] }
private def reindexed : Mem := { before with atomics := #[other, word] }
private def duplicated : Mem := { atomics := #[word, word, other] }

private theorem before_first :
    before.atomics.findIdx? (fun l => l.block == 0 && l.off == 10) = some 1 := by
  refine Array.findIdx?_eq_some_iff_getElem.mpr ⟨by decide, by decide, ?_⟩
  intro j hj
  have : j = 0 := by omega
  subst j
  simp [before, word]

theorem overlapping_identity : lock.Step 0 before before :=
  LockWord.Step.same rfl rfl rfl rfl rfl rfl (fun _ _ => Iff.rfl)

theorem duplicate_identity : lock.Step 0 duplicated duplicated :=
  LockWord.Step.same rfl rfl rfl rfl rfl rfl (fun _ _ => Iff.rfl)

theorem reject_changed_overlap : ¬ lock.Step 0 before changed := by
  intro hs
  have kept := (hs.first_iff 0 10 (.inr (by decide)) 1 other).mpr ⟨before_first, rfl⟩
  have hsize := congrArg (fun x : Option ALoc => x.map (fun l => l.msgs.size)) kept.2
  have : (some 1 : Option Nat) = some 0 := hsize
  cases this

theorem reject_retired_overlap : ¬ lock.Step 0 before retired := by
  intro hs
  have kept := (hs.first_iff 0 10 (.inr (by decide)) 1 other).mpr ⟨before_first, rfl⟩
  have : (none : Option ALoc) = some other := kept.2
  cases this

theorem reject_reindexed_overlap : ¬ lock.Step 0 before reindexed := by
  intro hs
  have kept := (hs.first_iff 0 10 (.inr (by decide)) 1 other).mpr ⟨before_first, rfl⟩
  have : (some 8 : Option Nat) = some 10 :=
    congrArg (Option.map Zig.ALoc.off) kept.2
  cases this

end LockWordLocations
