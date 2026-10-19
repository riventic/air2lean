import ZigLean.Sep.Full.Strength
import TryPointers.Proofs
import TryAliases.Proofs

/-!
Strength log of `tests/roadmap/try-pointers` (`TryPointers/Proofs.lean`,
`TryPointers/AliasProofs.lean`, `aliases/TryAliases/Proofs.lean`; `ZigLean/Sep/Full/Strength.lean`;
deleted with the legacy logic): each migrated triple gives back its legacy statement on every
`Mem.FSeqPlain` memory (no stack budget, which the legacy logic does not have), total instead
of partial, for a size-free frame `R`. `errorTag` and
`readableBytes` (`TryPointers/Proofs.lean`) are the assertions of the deleted legacy modules
`ZigLean.Sep.Try` and `ZigLean.Sep.Discard`, word for word (`errorTag` unfolds to `ownedBytes`).

Each statement is the legacy `TotalTripleIn Mem.FSeqPlain P c Q` (`ZigLean/Sep/Total.lean`) with
its definition unfolded, word for word, so the log does not use the legacy layer.
-/

open Zig Zig.Full Zig.Full.FAssn Zig.Assn

namespace StrengthLog.TryPointers

open TryPointersProofs

example {α : Type} [Enc α] (p : Ptr) (a : Nat) (R : Assn) (hR : SizeFree (fun _ => none) R) :
    ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF → (errorTag α p a none ∗ R) hP → m.Seq →
      m.FSeqPlain → ∃ v m' hQ, (tryPayloadPtr α a p).run m = pure (v, m') ∧
        Heap.Disjoint hQ hF ∧ m'.heap = hQ ∪ hF ∧
        ((⌜v = .ok (errPayloadPtr α p)⌝ ∗ errorTag α p a none) ∗ R) hQ ∧ m'.Seq :=
  FTotalTriple.toTotal_on (((success_with_frame (α := α) p a (up R)).pre fun _ h => up_sep h).post
      fun _ _ h => sep_up (sep_mono_left (fun _ h => up_lift.mpr (sep_lift.mp h)) h))
    fun _ => SizeFree.sep (SizeFree.sep SizeFree.lift SizeFree.ownedBytes) hR

example {α : Type} [Enc α] (p : Ptr) (a : Nat) (e : ErrName) (R : Assn)
    (hR : SizeFree (fun _ => none) R) :
    ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF → (errorTag α p a (some e) ∗ R) hP →
      m.Seq → m.FSeqPlain → ∃ v m' hQ, (tryPayloadPtr α a p).run m = pure (v, m') ∧
        Heap.Disjoint hQ hF ∧ m'.heap = hQ ∪ hF ∧
        ((⌜v = .error e⌝ ∗ errorTag α p a (some e)) ∗ R) hQ ∧ m'.Seq :=
  FTotalTriple.toTotal_on (((error_with_frame (α := α) p a e (up R)).pre fun _ h => up_sep h).post
      fun _ _ h => sep_up (sep_mono_left (fun _ h => up_lift.mpr (sep_lift.mp h)) h))
    fun _ => SizeFree.sep (SizeFree.sep SizeFree.lift SizeFree.ownedBytes) hR

example (p : Ptr) (n a : Nat) (R : Assn) (hR : SizeFree (fun _ => none) R) (hn : 0 < n) :
    ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF → (readableBytes p n a ∗ R) hP → m.Seq →
      m.FSeqPlain → ∃ v m' hQ, (loadDiscardBytes n a p).run m = pure (v, m') ∧
        Heap.Disjoint hQ hF ∧ m'.heap = hQ ∪ hF ∧ (readableBytes p n a ∗ R) hQ ∧ m'.Seq :=
  FTotalTriple.toTotal_on (((whole_read_with_frame p n a (up R) hn).pre fun _ h => up_sep h).post
      fun _ _ h => sep_up h)
    fun _ => SizeFree.sep (sizeFree_readableBytes _ _ _) hR

example {α : Type} [Enc α] (p : Ptr) (n a : Nat) (e : Option ErrName) (hdom : admittedError e) :
    ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF → readableUnion α p n a e hP → m.Seq →
      m.FSeqPlain → ∃ v m' hQ, (payloadProgram α n a p).run m = pure (v, m') ∧
        Heap.Disjoint hQ hF ∧ m'.heap = hQ ∪ hF ∧
        (⌜v = (match e with
          | none => .ok (errPayloadPtr α p) | some name => .error name)⌝ ∗
          readableUnion α p n a e) hQ ∧ m'.Seq :=
  FTotalTriple.toTotal_on ((payloadProgram_owned p n a e hdom).post
      fun _ _ h => up_lift.mpr (sep_lift.mp h))
    fun _ => SizeFree.sep SizeFree.lift (sizeFree_readableUnion _ _ _ _)

example (p : Ptr) (e : Option ErrName) (hdom : admittedError e) (R : Assn)
    (hR : SizeFree (fun _ => none) R) :
    ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF →
      (readableUnion (BitVec 8) p 4 2 e ∗ R) hP → m.Seq → m.FSeqPlain →
      ∃ v m' hQ, (TryPointers.payload8 p).run m = pure (v, m') ∧ Heap.Disjoint hQ hF ∧
        m'.heap = hQ ∪ hF ∧
        ((⌜v = (match e with
          | none => .ok (errPayloadPtr (BitVec 8) p) | some name => .error name)⌝ ∗
          readableUnion (BitVec 8) p 4 2 e) ∗ R) hQ ∧ m'.Seq :=
  FTotalTriple.toTotal_on (((payload8_owned p e hdom (up R)).pre fun _ h => up_sep h).post
      fun _ _ h => sep_up (sep_mono_left (fun _ h => up_lift.mpr (sep_lift.mp h)) h))
    fun _ => SizeFree.sep (SizeFree.sep SizeFree.lift (sizeFree_readableUnion _ _ _ _)) hR

example (p : Ptr) (e : Option ErrName) (hdom : admittedError e) (R : Assn)
    (hR : SizeFree (fun _ => none) R) :
    ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF →
      (readableUnion (BitVec 64) p 16 8 e ∗ R) hP → m.Seq → m.FSeqPlain →
      ∃ v m' hQ, (TryPointers.payload64 p).run m = pure (v, m') ∧ Heap.Disjoint hQ hF ∧
        m'.heap = hQ ∪ hF ∧
        ((⌜v = (match e with
          | none => .ok (errPayloadPtr (BitVec 64) p) | some name => .error name)⌝ ∗
          readableUnion (BitVec 64) p 16 8 e) ∗ R) hQ ∧ m'.Seq :=
  FTotalTriple.toTotal_on (((payload64_owned p e hdom (up R)).pre fun _ h => up_sep h).post
      fun _ _ h => sep_up (sep_mono_left (fun _ h => up_lift.mpr (sep_lift.mp h)) h))
    fun _ => SizeFree.sep (SizeFree.sep SizeFree.lift (sizeFree_readableUnion _ _ _ _)) hR

open TryPointersAliasProofs

example (p : Ptr) (u : Except ErrName (BitVec 8)) (y : BitVec 8) (hdom : admitted u) :
    ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF → pts p 2 u hP → m.Seq → m.FSeqPlain →
      ∃ v m' hQ, (TryPointers.writeAlias p y).run m = pure (v, m') ∧ Heap.Disjoint hQ hF ∧
        m'.heap = hQ ∪ hF ∧ (⌜v = writeView y u⌝ ∗ pts p 2 (writeView y u)) hQ ∧ m'.Seq :=
  FTotalTriple.toTotal_on ((writeAlias_owned p u y hdom).post fun _ _ h => up_lift.mpr (sep_lift.mp h))
    fun _ => SizeFree.sep SizeFree.lift (SizeFree.pts _ _ _)

example (p o e : Ptr) (u : Except ErrName (BitVec 8)) (c k : BitVec 32)
    (hdom : admitted u) (hc : c.toNat + 1 < 2 ^ 32) (hk : k.toNat + 1 < 2 ^ 32) :
    ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF →
      (pts p 2 u ∗ (pts o 4 c ∗ pts e 4 k)) hP → m.Seq → m.FSeqPlain →
      ∃ v m' hQ, (TryPointers.cleanup p o e).run m = pure (v, m') ∧ Heap.Disjoint hQ hF ∧
        m'.heap = hQ ∪ hF ∧
        (⌜v = u⌝ ∗
          (pts p 2 u ∗ (pts o 4 (c + 1) ∗ pts e 4 (match u with | .ok _ => k | .error _ => k + 1))))
          hQ ∧ m'.Seq :=
  FTotalTriple.toTotal_on (((cleanup_owned p o e u c k hdom hc hk).pre
      fun _ h => sep_mono_right (fun _ h => up_sep h) (up_sep h)).post
      fun _ _ h => have ⟨hφ, hr⟩ := sep_lift.mp h
        up_lift.mpr ⟨hφ, sep_up (sep_mono_right (fun _ h => sep_up h) hr)⟩)
    fun _ => SizeFree.sep SizeFree.lift
      (SizeFree.sep (SizeFree.pts _ _ _) (SizeFree.sep (SizeFree.pts _ _ _) (SizeFree.pts _ _ _)))

example (p c : Ptr) (u : Except ErrName (BitVec 8)) (k : BitVec 32)
    (hdom : admitted u) (hk : k.toNat + 2 < 2 ^ 32) :
    ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF → (pts p 2 u ∗ pts c 4 k) hP → m.Seq →
      m.FSeqPlain → ∃ v m' hQ, (TryPointers.cleanup p c c).run m = pure (v, m') ∧
        Heap.Disjoint hQ hF ∧ m'.heap = hQ ∪ hF ∧
        (⌜v = u⌝ ∗
          (pts p 2 u ∗ pts c 4 (match u with | .ok _ => k + 1 | .error _ => k + 1 + 1))) hQ ∧
        m'.Seq :=
  FTotalTriple.toTotal_on (((cleanup_shared_owned p c u k hdom hk).pre fun _ h => up_sep h).post
      fun _ _ h => have ⟨hφ, hr⟩ := sep_lift.mp h; up_lift.mpr ⟨hφ, sep_up hr⟩)
    fun _ => SizeFree.sep SizeFree.lift (SizeFree.sep (SizeFree.pts _ _ _) (SizeFree.pts _ _ _))

example (p e : Ptr) (u : Except ErrName (BitVec 8)) (k : BitVec 32)
    (hdom : admitted u) (hk : k.toNat + 1 < 2 ^ 32) :
    ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF → (pts p 2 u ∗ pts e 4 k) hP → m.Seq →
      m.FSeqPlain → ∃ v m' hQ, (TryPointers.coldPayload p e).run m = pure (v, m') ∧
        Heap.Disjoint hQ hF ∧ m'.heap = hQ ∪ hF ∧
        (⌜v = tryView (BitVec 8) p u⌝ ∗
          (pts p 2 u ∗ pts e 4 (match u with | .ok _ => k | .error _ => k + 1))) hQ ∧ m'.Seq :=
  FTotalTriple.toTotal_on (((coldPayload_owned p e u k hdom hk).pre fun _ h => up_sep h).post
      fun _ _ h => have ⟨hφ, hr⟩ := sep_lift.mp h; up_lift.mpr ⟨hφ, sep_up hr⟩)
    fun _ => SizeFree.sep SizeFree.lift (SizeFree.sep (SizeFree.pts _ _ _) (SizeFree.pts _ _ _))

open TryAliasesProofs

example (p : Ptr) (u : Except ErrName (BitVec 8)) (y : BitVec 8) (hdom : admitted u) :
    ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF → pts p 2 u hP → m.Seq → m.FSeqPlain →
      ∃ v m' hQ, (TryAliases.twoPaths p p y).run m = pure (v, m') ∧ Heap.Disjoint hQ hF ∧
        m'.heap = hQ ∪ hF ∧ (⌜v = writeView y u⌝ ∗ pts p 2 (writeView y u)) hQ ∧ m'.Seq :=
  FTotalTriple.toTotal_on ((twoPaths_same_owned p u y hdom).post fun _ _ h => up_lift.mpr (sep_lift.mp h))
    fun _ => SizeFree.sep SizeFree.lift (SizeFree.pts _ _ _)

example (a b : Ptr) (u w : Except ErrName (BitVec 8)) (y : BitVec 8)
    (hu : admitted u) (hw : admitted w) :
    ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF → (pts a 2 u ∗ pts b 2 w) hP → m.Seq →
      m.FSeqPlain → ∃ v m' hQ, (TryAliases.twoPaths a b y).run m = pure (v, m') ∧
        Heap.Disjoint hQ hF ∧ m'.heap = hQ ∪ hF ∧
        (⌜v = twoResult u w⌝ ∗ (pts a 2 (firstAfter y u w) ∗ pts b 2 w)) hQ ∧ m'.Seq :=
  FTotalTriple.toTotal_on (((twoPaths_distinct_owned a b u w y hu hw).pre fun _ h => up_sep h).post
      fun _ _ h => have ⟨hφ, hr⟩ := sep_lift.mp h; up_lift.mpr ⟨hφ, sep_up hr⟩)
    fun _ => SizeFree.sep SizeFree.lift (SizeFree.sep (SizeFree.pts _ _ _) (SizeFree.pts _ _ _))

example (p : Ptr) (u : Except ErrName (BitVec 8)) (f : BitVec 8) (hdom : admitted u) :
    ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF → pts p 2 u hP → m.Seq → m.FSeqPlain →
      ∃ v m' hQ, (TryAliases.resetOnError p f).run m = pure (v, m') ∧ Heap.Disjoint hQ hF ∧
        m'.heap = hQ ∪ hF ∧ (⌜v = tryView (BitVec 8) p u⌝ ∗ pts p 2 (resetAfter f u)) hQ ∧
        m'.Seq :=
  FTotalTriple.toTotal_on ((resetOnError_owned p u f hdom).post fun _ _ h => up_lift.mpr (sep_lift.mp h))
    fun _ => SizeFree.sep SizeFree.lift (SizeFree.pts _ _ _)

end StrengthLog.TryPointers
