import ZigLean.Sep.Alloc

/-! Byte sentinel allocation owns the entire n+1-byte heap block. The last byte is the
encoded sentinel; all payload bytes remain undefined and owned by the caller. -/
namespace Zig
open Assn

/-- Exact owned bytes on success: undefined payload, then the explicit sentinel store. -/
def sentinelBytes (n : Nat) (sentinel : BitVec 8) : Array Byte :=
  writeBytes (Array.replicate (n + 1) .undef) n (Enc.encode sentinel)

theorem sentinelBytes_size (n : Nat) (sentinel : BitVec 8) :
    (sentinelBytes n sentinel).size = n + 1 := by
  unfold sentinelBytes
  rw [writeBytes_size _ _ _ (by rw [LawfulEnc.size_encode]; simp [Enc.size, intSize, intAlign, alignUp])]
  simp

/-- Writing the sentinel preserves every payload byte. -/
theorem sentinelBytes_payload (n : Nat) (sentinel : BitVec 8) :
    (sentinelBytes n sentinel).extract 0 n = (Array.replicate (n + 1) .undef).extract 0 n := by
  unfold sentinelBytes
  simpa using extract_writeBytes_disjoint (Array.replicate (n + 1) .undef) n
    (Enc.encode sentinel) 0 n
    (by rw [LawfulEnc.size_encode]; simp [Enc.size, intSize, intAlign, alignUp])
    (by simp) (by right; omega)

/-- Reading the final owned byte yields exactly the encoded sentinel. -/
theorem sentinelBytes_sentinel (n : Nat) (sentinel : BitVec 8) :
    (sentinelBytes n sentinel).extract n (n + 1) = Enc.encode sentinel := by
  unfold sentinelBytes
  have hsz : (Enc.encode sentinel).size = 1 := by
    simpa [Enc.size, intSize, intAlign, alignUp] using LawfulEnc.size_encode sentinel
  simpa [hsz] using extract_writeBytes (Array.replicate (n + 1) .undef) n (Enc.encode sentinel)
    (by simp [hsz])

/-- The returned length is n; ownership includes the sentinel at offset n. Failure owns
no bytes and returns OutOfMemory. The policy may reject any allocation attempt. -/
def newSentinel (n : BitVec 64) (sentinel : BitVec 8) : Except ErrName Slice → Assn
  | .ok s => fun h => s.len = n ∧ s.ptr.off = 0 ∧ ∃ A,
      bytesAt s.ptr A (n.toNat + 1) .heap (sentinelBytes n.toNat sentinel) h
  | .error e => ⌜e = "OutOfMemory"⌝

/-- ReleaseSafe addition overflow panics before any allocator policy decision. -/
theorem allocSentinel_overflow (a : Allocator) (n : BitVec 64) (sentinel : BitVec 8)
    (h : 2 ^ 64 ≤ n.toNat + 1) (m : Mem) :
    (a.allocSentinel n sentinel).run m = throw .panic := by
  simp [Allocator.allocSentinel, h, zig_unfold]

/-- Includes empty payloads and every policy cap/failure trace, under the explicit
nonoverflow premise. Success owns all bytes, so Triple.freeSentinel releases the entire block. -/
theorem Triple.allocSentinel (a : Allocator) (n : BitVec 64) (sentinel : BitVec 8)
    (hn : n.toNat + 1 < 2 ^ 64) :
    Triple emp (a.allocSentinel n sentinel) (newSentinel n sentinel) := by
  apply Triple.of_run
  intro m hP hF hd hm hp hst
  have hP0 : hP = Heap.empty := hp
  subst hP0
  simp only [Heap.empty_union] at hm hd
  have ho : ¬ 2 ^ 64 ≤ n.toNat + 1 := by omega
  obtain ⟨r, m₁, h', hr, hd', hm', -, hst₁, hpost⟩ :=
    create_run (h := Heap.empty) (by simpa using hd) (by simpa using hm)
      a (n.toNat + 1) 1 (by omega) (by omega) hst
  simp only [Heap.empty_union] at hd' hm'
  cases r with
  | error e =>
    obtain ⟨he, hh⟩ := hpost
    refine ⟨.error e, m₁, h', ?_, hd', hm', ⟨he, hh⟩, hst₁⟩
    simp only [StateT.run] at hr
    simp [Allocator.allocSentinel, ho, zig_unfold, hr]
  | ok p =>
    obtain ⟨h0, A, -, hb⟩ := hpost
    have hsz : (Enc.encode sentinel).size = 1 := by
      simpa [Enc.size, intSize, intAlign, alignUp] using LawfulEnc.size_encode sentinel
    obtain ⟨m₂, hs, hst₂, h₂, hd₂, hm₂, hb₂⟩ := bytesAt_store hb hm' hd'
      (q := p.add n.toNat) (bs' := Enc.encode sentinel) rfl (by omega)
      (by simp [hsz]) (Nat.mod_one _) hst₁ (by decide)
    refine ⟨.ok ⟨p, n⟩, m₂, h₂, ?_, hd₂, hm₂, ⟨rfl, h0, A, hb₂⟩, hst₂⟩
    simp only [StateT.run] at hr hs
    simp [Allocator.allocSentinel, ho, Zig.store, zig_unfold, hr, hs, ExceptT.bindCont]

end Zig
