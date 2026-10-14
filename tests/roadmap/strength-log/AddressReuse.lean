import ZigLean.Sep.Full.Strength
import ZigLean.Sep.Full.Ops

/-!
Strength log of `tests/roadmap/address-reuse/Kernel.lean` (`ZigLean/Sep/Full/Strength.lean`;
deleted with the legacy logic). Kernel (c) now states the placement independence of the
full-state triples (`FTotalTriple.withPlacement`, `FTriple.withPlacement`). The legacy statement
(c) (`TotalTriple.withPlacement`, `ZigLean/Sep/AddrReuse.lean`) follows from it on every
`Mem.FSeq` memory without a stack budget (`Mem.NoStack`, `Mem.FSeqPlain`): a total full-state
triple over legacy assertions (size-free postcondition) gives the legacy conclusion, word for
word, from a memory with any placement and provenance mode. The legacy logic has no stack
budget; under one, a placement change can cut a thread's reserve
(`tests/roadmap/stack-region/Tokens.lean`, `placement_cx`).
-/

open Zig Zig.Full Zig.Full.FAssn

namespace StrengthLog.AddressReuse

example {α : Type} {P : Assn} {c : MemM α} {Q : α → Assn}
    (ht : FTotalTriple (up P) c (fun v => up (Q v))) (hQ : ∀ v, SizeFree (fun _ => none) (Q v))
    {m : Mem} {hP hF : Heap} (hd : Heap.Disjoint hP hF) (hm : m.heap = hP ∪ hF) (hp : P hP)
    (hs : m.Seq) (hfs : m.FSeq) (hns : m.NoStack) (σ : Placement) (pm : ProvenanceMode) :
    ∃ v m' hQ, c.run (m.withPlacement σ pm) = pure (v, m') ∧ Heap.Disjoint hQ hF ∧
      m'.heap = hQ ∪ hF ∧ Q v hQ ∧ m'.Seq :=
  FTotalTriple.toTotal_on ht hQ _ hP hF hd hm hp ⟨hs.single⟩ ⟨hfs.withPlacement σ pm, hns⟩

end StrengthLog.AddressReuse
