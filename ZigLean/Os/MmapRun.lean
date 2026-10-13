import ZigLean.Os.Mmap
import ZigLean.Mem.Lemmas
import ZigLean.Mem.AllocLemmas

/-!
# Runs of the OS page-mapping model (premise OSM-01)

What `Os.mmap`, `Os.munmap` and `Os.mremap` (`ZigLean/Os/Mmap.lean`, `docs/os-mmap.md`) do from
a given memory, independent of any program logic: the page arithmetic, the `unmapCase` of a
whole mapping, its prefix and its tail, and the run of each call. The full-state rules
(`ZigLean/Sep/Full/Mmap.lean`) are proved from these.
-/

namespace Zig

/-! ## Page arithmetic -/

theorem alignUp_mod_self {n P : Nat} (hP : 0 < P) : alignUp n P % P = 0 := by
  unfold alignUp; rw [if_neg (by omega)]; exact Nat.mul_mod_left _ _

theorem alignUp_lt {n P : Nat} (hP : 0 < P) : alignUp n P < n + P := by
  unfold alignUp; rw [if_neg (by omega)]
  have := Nat.div_mul_le_self (n + P - 1) P
  omega

theorem alignUp_add_aligned {a n P : Nat} (hP : 0 < P) (ha : a % P = 0) :
    alignUp (a + n) P = a + alignUp n P := by
  unfold alignUp; rw [if_neg (by omega), if_neg (by omega)]
  obtain ⟨q, rfl⟩ : ∃ q, a = P * q := ⟨a / P, (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero ha)).symm⟩
  rw [show P * q + n + P - 1 = (n + P - 1) + q * P by rw [Nat.mul_comm]; omega,
    Nat.add_mul_div_right _ _ hP, Nat.add_mul, Nat.mul_comm q P]
  omega

theorem alignUp_zero (P : Nat) : alignUp 0 P = 0 := by
  unfold alignUp; split
  · rfl
  · rename_i h; rw [Nat.zero_add, Nat.div_eq_of_lt (by omega)]; simp

theorem alignUp_of_mod {n P : Nat} (hP : 0 < P) (h : n % P = 0) : alignUp n P = n := by
  have := alignUp_add_aligned (a := n) (n := 0) hP h
  rw [Nat.add_zero, alignUp_zero, Nat.add_zero] at this; exact this

theorem add_le_of_mod {a b P : Nat} (ha : a % P = 0) (hb : b % P = 0) (h : a < b) :
    a + P ≤ b := by
  obtain ⟨q₁, rfl⟩ := Nat.dvd_of_mod_eq_zero ha
  obtain ⟨q₂, rfl⟩ := Nat.dvd_of_mod_eq_zero hb
  have : q₁ < q₂ := Nat.lt_of_mul_lt_mul_left h
  rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ this

/-! ## The failure decision -/

/-- `mmap`/`mremap` fail exactly when `rawAlloc` would (`Mem.allocDenied`). -/
theorem mapDenied_iff (m : Mem) (n : Nat) : m.mapDenied n = true ↔ m.allocDenied n := by
  simp only [Mem.mapDenied, Mem.allocDenied, Bool.or_eq_true, decide_eq_true_eq, or_assoc]

/-! ## mmap -/

theorem Os.mmap_run (os : Os.Target) (hint : Option Ptr) (len : BitVec 64) (hlen : len.toNat ≠ 0)
    (m : Mem) :
    (Os.mmap os hint len os.protReadWrite os.mapPrivateAnonymous Os.noFd 0).run m =
      if m.mapDenied len.toNat || !os.fits (m.mapAddr os.pageSize len.toNat) len.toNat then
        pure (.error "OutOfMemory", { m with allocs := m.allocs + 1 })
      else
        pure (.ok ⟨⟨some m.blocks.size, 0⟩, len⟩,
          ({ m with allocs := m.allocs + 1 } : Mem).afterMmap os.pageSize len.toNat) := by
  by_cases hd : (m.mapDenied len.toNat || !os.fits (m.mapAddr os.pageSize len.toNat) len.toNat)
  · simp only [Bool.or_eq_true, Bool.not_eq_true'] at hd
    rcases hd with hd | hd <;> simp [Os.mmap, hlen, hd, zig_unfold, set, StateT.set, MonadStateOf.set]
  · simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false] at hd
    simp [Os.mmap, hlen, hd, zig_unfold, set, StateT.set, MonadStateOf.set]

/-! ## munmap -/

/-- `munmap` of a range of a live mapping that `unmapCase` admits: record the removed bytes as a
write, then apply the case to the block. -/
theorem Os.munmap_run {m : Mem} (os : Os.Target) (s : Slice) {b : BlockId} {blk : Block}
    {lo : Nat} {u : Os.Unmap} (hb : s.ptr.block = some b) (hblk : m.blocks[b]? = some blk)
    (hl : blk.live) (hk : blk.kind = .mapped lo) (h0 : 0 ≤ s.ptr.off)
    (hal : (blk.addr + s.ptr.off.toNat) % os.pageSize = 0)
    (hu : Os.unmapCase os.pageSize lo blk.bytes.size s.ptr.off.toNat s.len.toNat = some u)
    (hst : m.SingleThread) :
    (Os.munmap os s).run m =
      pure ((), { (m.recordAt b s.ptr.off.toNat
        (Nat.min (s.ptr.off.toNat + alignUp s.len.toNat os.pageSize) blk.bytes.size -
          s.ptr.off.toNat) .write).retire b s.ptr.off.toNat
        (Nat.min (s.ptr.off.toNat + alignUp s.len.toNat os.pageSize) blk.bytes.size -
          s.ptr.off.toNat) with blocks := m.blocks.set! b (u.apply blk) }) := by
  have hrec := recordAccess_run (noRace_of_singleThread hst b s.ptr.off.toNat
    (Nat.min (s.ptr.off.toNat + alignUp s.len.toNat os.pageSize) blk.bytes.size - s.ptr.off.toNat)
    .write)
  simp only [StateT.run] at hrec
  simp [Os.munmap, Os.mappingAt, hb, hblk, hl, hk, h0, hal, hu, zig_unfold, hrec,
    ExceptT.bindCont, set, StateT.set, MonadStateOf.set, Mem.recordAt]

theorem unmapCase_whole {P lo S n : Nat} (hS : 0 < S) (hn : 0 < n)
    (heq : alignUp n P = alignUp S P) : Os.unmapCase P lo (lo + S) lo n = some .whole := by
  unfold Os.unmapCase; dsimp only
  rw [Nat.add_sub_cancel_left, if_neg (by omega), if_pos ⟨rfl, by rw [heq]⟩]

theorem unmapCase_prefix {P lo S n : Nat} (hS : 0 < S) (hn : 0 < n)
    (hlt : alignUp n P < alignUp S P) :
    Os.unmapCase P lo (lo + S) lo n = some (.prefix (lo + alignUp n P)) := by
  unfold Os.unmapCase; dsimp only
  rw [Nat.add_sub_cancel_left, if_neg (by omega), if_neg (by omega), if_pos rfl]

theorem unmapCase_tail {P lo S k n : Nat} (hk : 0 < k) (hkS : k < S) (hn : 0 < n)
    (heq : k + alignUp n P = alignUp S P) :
    Os.unmapCase P lo (lo + S) (lo + k) n = some (.tail (lo + k)) := by
  unfold Os.unmapCase; dsimp only
  rw [Nat.add_sub_cancel_left, if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by omega)]

/-! ## mremap -/

/-- The argument checks of `mremap` pass for the whole live mapping at `p`. -/
theorem Os.mremap_eq {m : Mem} (os : Os.Target) {b : BlockId} {blk : Block} {lo : Nat}
    {oldLen newLen : BitVec 64} {flags : BitVec 32} (hhas : os.hasMremap = true)
    (hfl : flags = 0 ∨ flags = Os.mremapMayMove) (hblk : m.blocks[b]? = some blk) (hl : blk.live)
    (hK : blk.kind = .mapped lo) (hold0 : oldLen.toNat ≠ 0)
    (hold : alignUp oldLen.toNat os.pageSize = alignUp (blk.bytes.size - lo) os.pageSize) :
    (Os.mremap os (some ⟨some b, lo⟩) oldLen newLen flags none).run m =
      (Os.mremapLive os ⟨some b, lo⟩ b blk lo newLen flags).run m := by
  rcases hfl with rfl | rfl <;>
  simp [Os.mremap, Os.mappingAt, Os.mremapMayMove, hhas, hblk, hl, hK, hold0, hold, zig_unfold,
    ExceptT.bindCont]

theorem mremapFill_size (P cur n : Nat) : (mremapFill P cur n).size = n - cur := by
  simp [mremapFill]

theorem Os.mremapLive_zero {m : Mem} (os : Os.Target) (p : Ptr) (b : BlockId) (blk : Block)
    (lo : Nat) (newLen : BitVec 64) (flags : BitVec 32) (hn : newLen.toNat = 0) :
    (Os.mremapLive os p b blk lo newLen flags).run m = throw .unspecified := by
  simp [Os.mremapLive, hn, zig_unfold]

theorem Os.mremapLive_shrink {m : Mem} (os : Os.Target) (p : Ptr) (b : BlockId) (blk : Block)
    (lo : Nat) (newLen : BitVec 64) (flags : BitVec 32) (hn0 : newLen.toNat ≠ 0)
    (hn : newLen.toNat ≤ blk.bytes.size - lo) (hst : m.SingleThread) :
    (Os.mremapLive os p b blk lo newLen flags).run m =
      pure (.ok ⟨p, newLen⟩, (m.recordAt b (lo + newLen.toNat)
        (blk.bytes.size - (lo + newLen.toNat)) .write).mremapShrunk b blk lo newLen.toNat) := by
  have hrec := recordAccess_run (noRace_of_singleThread hst b (lo + newLen.toNat)
    (blk.bytes.size - (lo + newLen.toNat)) .write)
  simp only [StateT.run] at hrec
  simp [Os.mremapLive, hn0, hn, zig_unfold, hrec, ExceptT.bindCont, modify, modifyGet,
    MonadStateOf.modifyGet, StateT.modifyGet, Mem.recordAt]

theorem Os.mremapLive_grow {m : Mem} (os : Os.Target) (p : Ptr) (b : BlockId) (blk : Block)
    (lo : Nat) (newLen : BitVec 64) (flags : BitVec 32)
    (hn : blk.bytes.size - lo < newLen.toNat) (hst : m.SingleThread) :
    let n := newLen.toNat
    let m₁ : Mem := { m with allocs := m.allocs + 1 }
    (Os.mremapLive os p b blk lo newLen flags).run m =
      if m.mapDenied n then pure (.error "OutOfMemory", m₁)
      else if flags = Os.mremapMayMove ∧
          (m.allocPolicy.os.mremapMoves m.allocs n = true ∨ m.mappingRoom os.addrLimit b blk lo (alignUp n os.pageSize) = false) then
        if os.fits (m.mapAddr os.pageSize n) n = false then pure (.error "OutOfMemory", m₁)
        else pure (.ok ⟨⟨some m.blocks.size, 0⟩, newLen⟩,
          (m₁.recordAt b lo (blk.bytes.size - lo) .write).mremapMoved os.pageSize b blk lo n)
      else if m.mappingRoom os.addrLimit b blk lo (alignUp n os.pageSize) = false then pure (.error "OutOfMemory", m₁)
      else pure (.ok ⟨p, newLen⟩, m₁.mremapGrown os.pageSize b blk lo n) := by
  intro n m₁
  have hn0 : newLen.toNat ≠ 0 := by omega
  have hn' : ¬ newLen.toNat ≤ blk.bytes.size - lo := by omega
  have hnr := noRace_of_singleThread (m := m₁) hst b lo (blk.bytes.size - lo) .write
  unfold NoRace at hnr
  by_cases hd : m.mapDenied n
  · simp [Os.mremapLive, hn0, hn', hd, zig_unfold, n, m₁, set, StateT.set, MonadStateOf.set]
  by_cases hmv : flags = Os.mremapMayMove ∧
      (m.allocPolicy.os.mremapMoves m.allocs n = true ∨ m.mappingRoom os.addrLimit b blk lo (alignUp n os.pageSize) = false)
  · simp only [hd, hmv, if_true, if_false, Bool.false_eq_true]
    by_cases hf : os.fits (m.mapAddr os.pageSize n) n = false
    · simp [Os.mremapLive, hn0, hn', hd, hmv, hf, zig_unfold, n, m₁, set, StateT.set,
        MonadStateOf.set, ExceptT.bindCont]
    simp only [m₁] at hnr
    simp [hf, hnr, Os.mremapLive, hn0, hn', hd, hmv, zig_unfold, n, set, StateT.set, MonadStateOf.set,
      recordAccess, get, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind, pure, StateT.run,
      ExceptT.pure, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, Option.bind_some,
      Mem.recordAt, liftM, monadLift, MonadLift.monadLift, StateT.lift]
    rfl
  · simp only [hd, hmv, if_false, Bool.false_eq_true]
    by_cases ht : m.mappingRoom os.addrLimit b blk lo (alignUp n os.pageSize) = false
    · have hf : ¬ flags = Os.mremapMayMove := fun h => hmv ⟨h, .inr ht⟩
      simp [Os.mremapLive, hn0, hn', hd, hf, ht, zig_unfold, n, m₁, set, StateT.set,
        MonadStateOf.set, ExceptT.bindCont]
    · have hf : ¬ (flags = Os.mremapMayMove ∧ m.allocPolicy.os.mremapMoves m.allocs n = true) :=
        fun h => hmv ⟨h.1, .inl h.2⟩
      simp [Os.mremapLive, hn0, hn', hd, hf, ht, zig_unfold, n, m₁, set, StateT.set,
        MonadStateOf.set, ExceptT.bindCont, modify, modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet]

/-- A growth without `MAYMOVE` reads no recorded access, in every memory: it fails, or it grows in
place. -/
theorem Os.mremapLive_grow0 {m : Mem} (os : Os.Target) (p : Ptr) (b : BlockId) (blk : Block)
    (lo : Nat) (newLen : BitVec 64) (hn : blk.bytes.size - lo < newLen.toNat) :
    let n := newLen.toNat
    let m₁ : Mem := { m with allocs := m.allocs + 1 }
    (Os.mremapLive os p b blk lo newLen 0).run m =
      if m.mapDenied n then pure (.error "OutOfMemory", m₁)
      else if m.mappingRoom os.addrLimit b blk lo (alignUp n os.pageSize) = false then
        pure (.error "OutOfMemory", m₁)
      else pure (.ok ⟨p, newLen⟩, m₁.mremapGrown os.pageSize b blk lo n) := by
  intro n m₁
  have hn0 : newLen.toNat ≠ 0 := by omega
  have hn' : ¬ newLen.toNat ≤ blk.bytes.size - lo := by omega
  have hf : ¬ (0 : BitVec 32) = Os.mremapMayMove := by decide
  by_cases hd : m.mapDenied n
  · simp [Os.mremapLive, hn0, hn', hd, zig_unfold, n, m₁, set, StateT.set, MonadStateOf.set]
  by_cases ht : m.mappingRoom os.addrLimit b blk lo (alignUp n os.pageSize) = false
  · simp [Os.mremapLive, hn0, hn', hd, hf, ht, zig_unfold, n, m₁, set, StateT.set,
      MonadStateOf.set, ExceptT.bindCont, Os.mremapMayMove]
  · simp [Os.mremapLive, hn0, hn', hd, hf, ht, zig_unfold, n, m₁, set, StateT.set,
      MonadStateOf.set, ExceptT.bindCont, modify, modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet, Os.mremapMayMove]

end Zig
