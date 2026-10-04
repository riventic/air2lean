import ZigLean.Sep.Triple

/-! Ownership for a whole discarded read. Bytes may be undefined because no typed value
is observed. Bounds, alignment, allocation provenance and race/read records are preserved. -/

namespace Zig
open Assn

/-- Own an aligned raw byte range, without requiring that a typed decoder accepts it. -/
def readableBytes (p : Ptr) (n a : Nat) : Assn := fun h =>
  ∃ A S K bs, (A + p.off.toNat) % a = 0 ∧ bs.size = n ∧ bytesAt p A S K bs h

theorem readableBytes_discard_run {p : Ptr} {n a : Nat} {m : Mem} {h hF : Heap}
    (hp : readableBytes p n a h) (hm : m.heap = h ∪ hF) (hn : 0 < n) (hs : m.Seq) :
    ∃ m', (loadDiscardBytes n a p).run m = pure ((), m') ∧
      m'.heap = h ∪ hF ∧ m'.Seq := by
  obtain ⟨A, S, K, bs, ha, hsize, hb⟩ := hp
  obtain ⟨block, blk, hacc, -, -, -, -⟩ := bytesAt_access
    (p := p) (q := p) (k := 0) (n := n) (a := a) hb hm
    (by simp [Ptr.add]) hn (by omega) (by simpa using ha)
  simp only [Nat.add_zero] at hacc
  refine ⟨m.recordAt block p.off.toNat n .read,
    loadDiscardBytes_run hacc (noRace_of_singleThread hs.single _ _ _ _), ?_, hs.recordAt _ _ _ _⟩
  funext l; rw [Mem.heap_recordAt]; exact congrFun hm l

/-- An unused read preserves owned and framed bytes without requiring initialized values. -/
theorem Triple.loadDiscardBytes {p : Ptr} {n a : Nat} (hn : 0 < n) :
    Triple (readableBytes p n a) (Zig.loadDiscardBytes n a p)
      (fun _ => readableBytes p n a) :=
  Triple.of_run fun _ h _ hd hm hp hs => by
    obtain ⟨m', hr, hm', hs'⟩ := readableBytes_discard_run hp hm hn hs
    exact ⟨(), m', h, hr, hd, hm', hp, hs'⟩

end Zig
