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
-/

open Zig Zig.Full Zig.Full.FAssn Zig.Assn

namespace StrengthLog.TryPointers

open TryPointersProofs

example {α : Type} [Enc α] (p : Ptr) (a : Nat) (R : Assn) (hR : SizeFree (fun _ => none) R) :
    TotalTripleIn Mem.FSeqPlain (errorTag α p a none ∗ R) (tryPayloadPtr α a p)
      (fun result => (⌜result = .ok (errPayloadPtr α p)⌝ ∗ errorTag α p a none) ∗ R) :=
  FTotalTriple.toTotal_on (((success_with_frame (α := α) p a (up R)).pre fun _ h => up_sep h).post
      fun _ _ h => sep_up (sep_mono_left (fun _ h => up_lift.mpr (sep_lift.mp h)) h))
    fun _ => SizeFree.sep (SizeFree.sep SizeFree.lift SizeFree.ownedBytes) hR

example {α : Type} [Enc α] (p : Ptr) (a : Nat) (e : ErrName) (R : Assn)
    (hR : SizeFree (fun _ => none) R) :
    TotalTripleIn Mem.FSeqPlain (errorTag α p a (some e) ∗ R) (tryPayloadPtr α a p)
      (fun result => (⌜result = .error e⌝ ∗ errorTag α p a (some e)) ∗ R) :=
  FTotalTriple.toTotal_on (((error_with_frame (α := α) p a e (up R)).pre fun _ h => up_sep h).post
      fun _ _ h => sep_up (sep_mono_left (fun _ h => up_lift.mpr (sep_lift.mp h)) h))
    fun _ => SizeFree.sep (SizeFree.sep SizeFree.lift SizeFree.ownedBytes) hR

example (p : Ptr) (n a : Nat) (R : Assn) (hR : SizeFree (fun _ => none) R) (hn : 0 < n) :
    TotalTripleIn Mem.FSeqPlain (readableBytes p n a ∗ R) (loadDiscardBytes n a p)
      (fun _ => readableBytes p n a ∗ R) :=
  FTotalTriple.toTotal_on (((whole_read_with_frame p n a (up R) hn).pre fun _ h => up_sep h).post
      fun _ _ h => sep_up h)
    fun _ => SizeFree.sep (sizeFree_readableBytes _ _ _) hR

example {α : Type} [Enc α] (p : Ptr) (n a : Nat) (e : Option ErrName) (hdom : admittedError e) :
    TotalTripleIn Mem.FSeqPlain (readableUnion α p n a e) (payloadProgram α n a p)
      (fun result => ⌜result = (match e with
        | none => .ok (errPayloadPtr α p) | some name => .error name)⌝ ∗
        readableUnion α p n a e) :=
  FTotalTriple.toTotal_on ((payloadProgram_owned p n a e hdom).post
      fun _ _ h => up_lift.mpr (sep_lift.mp h))
    fun _ => SizeFree.sep SizeFree.lift (sizeFree_readableUnion _ _ _ _)

example (p : Ptr) (e : Option ErrName) (hdom : admittedError e) (R : Assn)
    (hR : SizeFree (fun _ => none) R) :
    TotalTripleIn Mem.FSeqPlain (readableUnion (BitVec 8) p 4 2 e ∗ R) (TryPointers.payload8 p)
      (fun result => (⌜result = (match e with
        | none => .ok (errPayloadPtr (BitVec 8) p) | some name => .error name)⌝ ∗
        readableUnion (BitVec 8) p 4 2 e) ∗ R) :=
  FTotalTriple.toTotal_on (((payload8_owned p e hdom (up R)).pre fun _ h => up_sep h).post
      fun _ _ h => sep_up (sep_mono_left (fun _ h => up_lift.mpr (sep_lift.mp h)) h))
    fun _ => SizeFree.sep (SizeFree.sep SizeFree.lift (sizeFree_readableUnion _ _ _ _)) hR

example (p : Ptr) (e : Option ErrName) (hdom : admittedError e) (R : Assn)
    (hR : SizeFree (fun _ => none) R) :
    TotalTripleIn Mem.FSeqPlain (readableUnion (BitVec 64) p 16 8 e ∗ R) (TryPointers.payload64 p)
      (fun result => (⌜result = (match e with
        | none => .ok (errPayloadPtr (BitVec 64) p) | some name => .error name)⌝ ∗
        readableUnion (BitVec 64) p 16 8 e) ∗ R) :=
  FTotalTriple.toTotal_on (((payload64_owned p e hdom (up R)).pre fun _ h => up_sep h).post
      fun _ _ h => sep_up (sep_mono_left (fun _ h => up_lift.mpr (sep_lift.mp h)) h))
    fun _ => SizeFree.sep (SizeFree.sep SizeFree.lift (sizeFree_readableUnion _ _ _ _)) hR

open TryPointersAliasProofs

example (p : Ptr) (u : Except ErrName (BitVec 8)) (y : BitVec 8) (hdom : admitted u) :
    TotalTripleIn Mem.FSeqPlain (pts p 2 u) (TryPointers.writeAlias p y)
      (fun r => ⌜r = writeView y u⌝ ∗ pts p 2 (writeView y u)) :=
  FTotalTriple.toTotal_on ((writeAlias_owned p u y hdom).post fun _ _ h => up_lift.mpr (sep_lift.mp h))
    fun _ => SizeFree.sep SizeFree.lift (SizeFree.pts _ _ _)

example (p o e : Ptr) (u : Except ErrName (BitVec 8)) (c k : BitVec 32)
    (hdom : admitted u) (hc : c.toNat + 1 < 2 ^ 32) (hk : k.toNat + 1 < 2 ^ 32) :
    TotalTripleIn Mem.FSeqPlain (pts p 2 u ∗ (pts o 4 c ∗ pts e 4 k)) (TryPointers.cleanup p o e)
      (fun r => ⌜r = u⌝ ∗
        (pts p 2 u ∗ (pts o 4 (c + 1) ∗ pts e 4 (match u with | .ok _ => k | .error _ => k + 1)))) :=
  FTotalTriple.toTotal_on (((cleanup_owned p o e u c k hdom hc hk).pre
      fun _ h => sep_mono_right (fun _ h => up_sep h) (up_sep h)).post
      fun _ _ h => have ⟨hφ, hr⟩ := sep_lift.mp h
        up_lift.mpr ⟨hφ, sep_up (sep_mono_right (fun _ h => sep_up h) hr)⟩)
    fun _ => SizeFree.sep SizeFree.lift
      (SizeFree.sep (SizeFree.pts _ _ _) (SizeFree.sep (SizeFree.pts _ _ _) (SizeFree.pts _ _ _)))

example (p c : Ptr) (u : Except ErrName (BitVec 8)) (k : BitVec 32)
    (hdom : admitted u) (hk : k.toNat + 2 < 2 ^ 32) :
    TotalTripleIn Mem.FSeqPlain (pts p 2 u ∗ pts c 4 k) (TryPointers.cleanup p c c)
      (fun r => ⌜r = u⌝ ∗
        (pts p 2 u ∗ pts c 4 (match u with | .ok _ => k + 1 | .error _ => k + 1 + 1))) :=
  FTotalTriple.toTotal_on (((cleanup_shared_owned p c u k hdom hk).pre fun _ h => up_sep h).post
      fun _ _ h => have ⟨hφ, hr⟩ := sep_lift.mp h; up_lift.mpr ⟨hφ, sep_up hr⟩)
    fun _ => SizeFree.sep SizeFree.lift (SizeFree.sep (SizeFree.pts _ _ _) (SizeFree.pts _ _ _))

example (p e : Ptr) (u : Except ErrName (BitVec 8)) (k : BitVec 32)
    (hdom : admitted u) (hk : k.toNat + 1 < 2 ^ 32) :
    TotalTripleIn Mem.FSeqPlain (pts p 2 u ∗ pts e 4 k) (TryPointers.coldPayload p e)
      (fun r => ⌜r = tryView (BitVec 8) p u⌝ ∗
        (pts p 2 u ∗ pts e 4 (match u with | .ok _ => k | .error _ => k + 1))) :=
  FTotalTriple.toTotal_on (((coldPayload_owned p e u k hdom hk).pre fun _ h => up_sep h).post
      fun _ _ h => have ⟨hφ, hr⟩ := sep_lift.mp h; up_lift.mpr ⟨hφ, sep_up hr⟩)
    fun _ => SizeFree.sep SizeFree.lift (SizeFree.sep (SizeFree.pts _ _ _) (SizeFree.pts _ _ _))

open TryAliasesProofs

example (p : Ptr) (u : Except ErrName (BitVec 8)) (y : BitVec 8) (hdom : admitted u) :
    TotalTripleIn Mem.FSeqPlain (pts p 2 u) (TryAliases.twoPaths p p y)
      (fun r => ⌜r = writeView y u⌝ ∗ pts p 2 (writeView y u)) :=
  FTotalTriple.toTotal_on ((twoPaths_same_owned p u y hdom).post fun _ _ h => up_lift.mpr (sep_lift.mp h))
    fun _ => SizeFree.sep SizeFree.lift (SizeFree.pts _ _ _)

example (a b : Ptr) (u w : Except ErrName (BitVec 8)) (y : BitVec 8)
    (hu : admitted u) (hw : admitted w) :
    TotalTripleIn Mem.FSeqPlain (pts a 2 u ∗ pts b 2 w) (TryAliases.twoPaths a b y)
      (fun r => ⌜r = twoResult u w⌝ ∗ (pts a 2 (firstAfter y u w) ∗ pts b 2 w)) :=
  FTotalTriple.toTotal_on (((twoPaths_distinct_owned a b u w y hu hw).pre fun _ h => up_sep h).post
      fun _ _ h => have ⟨hφ, hr⟩ := sep_lift.mp h; up_lift.mpr ⟨hφ, sep_up hr⟩)
    fun _ => SizeFree.sep SizeFree.lift (SizeFree.sep (SizeFree.pts _ _ _) (SizeFree.pts _ _ _))

example (p : Ptr) (u : Except ErrName (BitVec 8)) (f : BitVec 8) (hdom : admitted u) :
    TotalTripleIn Mem.FSeqPlain (pts p 2 u) (TryAliases.resetOnError p f)
      (fun r => ⌜r = tryView (BitVec 8) p u⌝ ∗ pts p 2 (resetAfter f u)) :=
  FTotalTriple.toTotal_on ((resetOnError_owned p u f hdom).post fun _ _ h => up_lift.mpr (sep_lift.mp h))
    fun _ => SizeFree.sep SizeFree.lift (SizeFree.pts _ _ _)

end StrengthLog.TryPointers
