import TryPointers.Gen
import ZigLean.Sep.Full.Try

open Zig
open scoped Zig
open Zig.Full Zig.Full.FAssn

namespace TryPointersProofs

/-- The finite domain declared by every retained source AIR function. -/
abbrev domain : ErrorDomain := ⟨#["Bad", "Other"], by decide, by decide⟩

def admittedError (e : Option ErrName) : Prop :=
  ∀ name, e = some name → domain.names.contains name = true

theorem admittedError_all {e : Option ErrName} (h : admittedError e) :
    e.all domain.names.contains = true := by
  cases e with
  | none => rfl
  | some name => exact h name rfl

/-- The two bytes of an error union's error code that hold `e`, owned (any block kind) with the
code's alignment. -/
abbrev errorTag (α : Type) [Enc α] (p : Ptr) (a : Nat) (e : Option ErrName) : Assn :=
  ownedBytes (p.add (errUnionOffsets (Enc.size α) (Enc.align α)).1) (Nat.min a 2) (errBytes e)

/-- `n` owned bytes (any block kind) at `p`, aligned to `a`, of any content. -/
def readableBytes (p : Ptr) (n a : Nat) : Assn := fun h =>
  ∃ A S K bs, (A + p.off.toNat) % a = 0 ∧ bs.size = n ∧ bytesAt p A S K bs h

/-- `readableBytes` does not read its cells' size labels. -/
theorem sizeFree_readableBytes (p : Ptr) (n a : Nat) :
    SizeFree (fun _ => none) (readableBytes p n a) := fun h h' ⟨A, S, K, bs, ha, hs, hb⟩ hn hpin hsz =>
  have ⟨A', S', K', ⟨ha', hs'⟩, hb'⟩ := SizeFree.bytesAt_ex
    (φ := fun A _ _ => (A + p.off.toNat) % a = 0 ∧ bs.size = n) (fun _ _ _ _ _ h _ => h)
    h h' ⟨A, S, K, ⟨ha, hs⟩, hb⟩ hn hpin hsz
  ⟨A', S', K', bs, ha', hs', hb'⟩

theorem errorTag_read {α : Type} [Enc α] {p : Ptr} {a : Nat} {e : Option ErrName} :
    ReadAt (p.add (errUnionOffsets (Enc.size α) (Enc.align α)).1) (Nat.min a 2) (errBytes e)
      (up (errorTag α p a e)) :=
  ReadAt.ownedBytes (by cases e <;> simp [errBytes])

-- The tag-only helper rule has no initialized-payload precondition. Generated functions
-- also perform an unused whole-object read, requiring readableBytes for that full range.
-- Payload and cleanup ownership is retained through framing; use FTotalTriple.bind afterwards.
theorem success_with_frame {α : Type} [Enc α] (p : Ptr) (a : Nat) (R : FAssn) :
    FTotalTriple (up (errorTag α p a none) ⋆ R) (tryPayloadPtr α a p)
      (fun result => (⟪result = .ok (errPayloadPtr α p)⟫ ⋆ up (errorTag α p a none)) ⋆ R) :=
  (FTotalTriple.tryPayloadPtr_of (t := none) errorTag_read rfl (errOfBytes_errBytes _)).frame

theorem error_with_frame {α : Type} [Enc α] (p : Ptr) (a : Nat) (e : ErrName) (R : FAssn) :
    FTotalTriple (up (errorTag α p a (some e)) ⋆ R) (tryPayloadPtr α a p)
      (fun result => (⟪result = .error e⟫ ⋆ up (errorTag α p a (some e))) ⋆ R) :=
  (FTotalTriple.tryPayloadPtr_of (t := some e) errorTag_read rfl (errOfBytes_errBytes _)).frame

theorem whole_read {p : Ptr} {n a : Nat} (hn : 0 < n) :
    FTotalTriple (up (readableBytes p n a)) (loadDiscardBytes n a p)
      (fun _ => up (readableBytes p n a)) :=
  (FTotalTriple.ex fun bs => FTotalTriple.lift fun (hs : bs.size = n) =>
    (FTotalTriple.loadDiscard_of (ReadAt.ownedBytes (hs ▸ hn)) hn hs).post fun _ _ h =>
      have ⟨⟨A, S, K, ha, hb⟩, hk, hg⟩ := h; ⟨⟨A, S, K, bs, ha, hs, hb⟩, hk, hg⟩).pre
    fun _ ⟨⟨A, S, K, bs, ha, hs, hb⟩, hk, hg⟩ => ⟨bs, sep_lift.mpr ⟨hs, ⟨A, S, K, ha, hb⟩, hk, hg⟩⟩

theorem whole_read_with_frame (p : Ptr) (n a : Nat) (R : FAssn) (hn : 0 < n) :
    FTotalTriple (up (readableBytes p n a) ⋆ R) (loadDiscardBytes n a p)
      (fun _ => up (readableBytes p n a) ⋆ R) :=
  (whole_read hn).frame

-- Both model layouts preserve provenance and use the compiler-model payload offset.
theorem byte_payload_address (p : Ptr) : errPayloadPtr (BitVec 8) p = p.add 2 := rfl
theorem wide_payload_address (p : Ptr) : errPayloadPtr (BitVec 64) p = p := by
  change p.add (0 : Int) = p
  cases p
  simp [Ptr.add]


-- This reference keeps the generated whole-object read and the second tag read on error.
def payloadProgram (α : Type) [Enc α] (n a : Nat) (p : Ptr) :
    MemM (Except ErrName Ptr) := do
  loadDiscardBytes n a p
  match ← finiteTryPayloadPtr domain α a p with
  | .error _ => pure (.error (← finiteErrCodeAt domain α a p))
  | .ok q => pure (.ok q)

-- MUTANT_BRIDGE_BEGIN: payload8_program
-- These equalities name the actual checked source-generated definitions.
theorem payload8_program (p : Ptr) :
    TryPointers.payload8 p = payloadProgram (BitVec 8) 4 2 p := by
  funext m
  -- The generated MM wrapper carries a local-state pair through each effect. Split
  -- the actual effect outcomes before reducing those pairs and the return wrapper.
  cases hread : loadDiscardBytes 4 2 p m with
  | none => simp [TryPointers.payload8, payloadProgram, domain, zig_unfold, hread]
  | some read =>
    cases read with
    | error failure => simp [TryPointers.payload8, payloadProgram, domain, zig_unfold, hread]
    | ok read =>
      rcases read with ⟨u, m₁⟩
      cases htag : finiteTryPayloadPtr domain (BitVec 8) 2 p m₁ with
      | none => simp [TryPointers.payload8, payloadProgram, domain, zig_unfold, hread, htag]
      | some tag =>
        cases tag with
        | error failure => simp [TryPointers.payload8, payloadProgram, domain, zig_unfold, hread, htag]
        | ok tag =>
          rcases tag with ⟨result, m₂⟩
          cases result with
          | ok q => simp [TryPointers.payload8, payloadProgram, domain, zig_unfold, hread, htag]
          | error name =>
            cases hcode : finiteErrCodeAt domain (BitVec 8) 2 p m₂ with
            | none => simp [TryPointers.payload8, payloadProgram, domain, zig_unfold, hread, htag, hcode]
            | some code =>
              cases code <;> simp [TryPointers.payload8, payloadProgram, domain, zig_unfold, hread, htag, hcode]
-- MUTANT_BRIDGE_END: payload8_program

theorem payload64_program (p : Ptr) :
    TryPointers.payload64 p = payloadProgram (BitVec 64) 16 8 p := by
  funext m
  -- The generated MM wrapper carries a local-state pair through each effect. Split
  -- the actual effect outcomes before reducing those pairs and the return wrapper.
  cases hread : loadDiscardBytes 16 8 p m with
  | none => simp [TryPointers.payload64, payloadProgram, domain, zig_unfold, hread]
  | some read =>
    cases read with
    | error failure => simp [TryPointers.payload64, payloadProgram, domain, zig_unfold, hread]
    | ok read =>
      rcases read with ⟨u, m₁⟩
      cases htag : finiteTryPayloadPtr domain (BitVec 64) 8 p m₁ with
      | none => simp [TryPointers.payload64, payloadProgram, domain, zig_unfold, hread, htag]
      | some tag =>
        cases tag with
        | error failure => simp [TryPointers.payload64, payloadProgram, domain, zig_unfold, hread, htag]
        | ok tag =>
          rcases tag with ⟨result, m₂⟩
          cases result with
          | ok q => simp [TryPointers.payload64, payloadProgram, domain, zig_unfold, hread, htag]
          | error name =>
            cases hcode : finiteErrCodeAt domain (BitVec 64) 8 p m₂ with
            | none => simp [TryPointers.payload64, payloadProgram, domain, zig_unfold, hread, htag, hcode]
            | some code =>
              cases code <;> simp [TryPointers.payload64, payloadProgram, domain, zig_unfold, hread, htag, hcode]

/-- One assertion owns the entire object. Only its two tag bytes must decode;
all payload/padding bytes may be undefined. Separate tag ownership is not assumed. -/
def readableUnion (α : Type) [Enc α] (p : Ptr) (n a : Nat) (e : Option ErrName) : Assn :=
  fun h => ∃ A S K bs,
    (A + p.off.toNat) % a = 0 ∧ bs.size = n ∧ 0 < n ∧
    (errUnionOffsets (Enc.size α) (Enc.align α)).1 + 2 ≤ bs.size ∧
    (A + p.off.toNat + (errUnionOffsets (Enc.size α) (Enc.align α)).1) % (Nat.min a 2) = 0 ∧
    errOfBytes (bs.extract (errUnionOffsets (Enc.size α) (Enc.align α)).1
      ((errUnionOffsets (Enc.size α) (Enc.align α)).1 + 2)) = pure e ∧
    bytesAt p A S K bs h

/-- `readableUnion` does not read its cells' size labels. -/
theorem sizeFree_readableUnion {α : Type} [Enc α] (p : Ptr) (n a : Nat) (e : Option ErrName) :
    SizeFree (fun _ => none) (readableUnion α p n a e) :=
  fun h h' ⟨A, S, K, bs, h1, h2, h3, h4, h5, h6, hb⟩ hn hpin hsz =>
    have ⟨A', S', K', ⟨h1', h2', h3', h4', h5', h6'⟩, hb'⟩ := SizeFree.bytesAt_ex
      (φ := fun A _ _ => (A + p.off.toNat) % a = 0 ∧ bs.size = n ∧ 0 < n ∧
        (errUnionOffsets (Enc.size α) (Enc.align α)).1 + 2 ≤ bs.size ∧
        (A + p.off.toNat + (errUnionOffsets (Enc.size α) (Enc.align α)).1) % (Nat.min a 2) = 0 ∧
        errOfBytes (bs.extract (errUnionOffsets (Enc.size α) (Enc.align α)).1
          ((errUnionOffsets (Enc.size α) (Enc.align α)).1 + 2)) = pure e)
      (fun _ _ _ _ _ h _ => h) h h' ⟨A, S, K, ⟨h1, h2, h3, h4, h5, h6⟩, hb⟩ hn hpin hsz
    ⟨A', S', K', bs, h1', h2', h3', h4', h5', h6', hb'⟩

/-- The result of `payloadProgram` on a union whose error code holds `e`. -/
def payloadResult (α : Type) [Enc α] (p : Ptr) : Option ErrName → Except ErrName Ptr
  | none => .ok (errPayloadPtr α p)
  | some name => .error name

/-- The run on the owned bytes `bs`: the whole-object read (`ReadAt.bytesAt`), then the error
code (`ReadAt.bytesAt_part`) once on success and twice on error. -/
theorem payloadProgram_bytes {α : Type} [Enc α] {p : Ptr} {n a A S : Nat} {K : BlockKind}
    {bs : Array Byte} {e : Option ErrName} (hdom : admittedError e)
    (ha : (A + p.off.toNat) % a = 0) (hn : bs.size = n) (hpos : 0 < n)
    (hbnd : (errUnionOffsets (Enc.size α) (Enc.align α)).1 + 2 ≤ bs.size)
    (hal : (A + p.off.toNat + (errUnionOffsets (Enc.size α) (Enc.align α)).1) % (Nat.min a 2) = 0)
    (he : errOfBytes (bs.extract (errUnionOffsets (Enc.size α) (Enc.align α)).1
      ((errUnionOffsets (Enc.size α) (Enc.align α)).1 + 2)) = pure e) :
    FTotalTriple (up (bytesAt p A S K bs)) (payloadProgram α n a p)
      (fun result => ⟪result = payloadResult α p e⟫ ⋆ up (bytesAt p A S K bs)) := by
  have tag : ReadAt (p.add (errUnionOffsets (Enc.size α) (Enc.align α)).1) (Nat.min a 2)
      (bs.extract (errUnionOffsets (Enc.size α) (Enc.align α)).1
        ((errUnionOffsets (Enc.size α) (Enc.align α)).1 + 2)) (up (bytesAt p A S K bs)) :=
    ReadAt.bytesAt_part hal (by decide) hbnd
  have hs2 : (bs.extract (errUnionOffsets (Enc.size α) (Enc.align α)).1
      ((errUnionOffsets (Enc.size α) (Enc.align α)).1 + 2)).size = 2 := by
    simp only [Array.size_extract]; omega
  unfold payloadProgram
  refine FTotalTriple.bind (FTotalTriple.loadDiscard_of (ReadAt.bytesAt ha (hn ▸ hpos)) hpos hn)
    fun _ => FTotalTriple.bind (FTotalTriple.finiteTryPayloadPtr_of tag hs2 he
      (admittedError_all hdom)) fun x => FTotalTriple.lift fun hx => ?_
  subst hx
  cases e with
  | none => exact FTotalTriple.pure_read rfl
  | some name =>
    exact FTotalTriple.bind (FTotalTriple.finiteErrCodeAt_of tag hs2 he (hdom name rfl)) fun y =>
      FTotalTriple.lift fun hy => by subst hy; exact FTotalTriple.pure_read rfl

/-- Both actual generated layouts preserve the whole owned object and arbitrary frame.
The first read covers every object byte. On error the generated error-code read is retained. -/
theorem payloadProgram_owned {α : Type} [Enc α] (p : Ptr) (n a : Nat) (e : Option ErrName)
    (hdom : admittedError e) :
    FTotalTriple (up (readableUnion α p n a e)) (payloadProgram α n a p)
      (fun result => ⟪result = (match e with
        | none => .ok (errPayloadPtr α p) | some name => .error name)⟫ ⋆
        up (readableUnion α p n a e)) := by
  let eo := (errUnionOffsets (Enc.size α) (Enc.align α)).1
  refine FTotalTriple.pre (P := FAssn.ex fun A : Nat => FAssn.ex fun S : Nat =>
    FAssn.ex fun K : BlockKind => FAssn.ex fun bs : Array Byte =>
      ⟪(A + p.off.toNat) % a = 0 ∧ bs.size = n ∧ 0 < n ∧ eo + 2 ≤ bs.size ∧
        (A + p.off.toNat + eo) % (Nat.min a 2) = 0 ∧ errOfBytes (bs.extract eo (eo + 2)) = pure e⟫ ⋆
      up (bytesAt p A S K bs)) ?_ ?_
  · refine FTotalTriple.ex fun A => FTotalTriple.ex fun S => FTotalTriple.ex fun K =>
      FTotalTriple.ex fun bs => FTotalTriple.lift fun hc => ?_
    obtain ⟨ha, hn, hpos, hbnd, hal, he⟩ := hc
    refine (payloadProgram_bytes (S := S) (K := K) hdom ha hn hpos hbnd hal he).post fun v r h => ?_
    obtain ⟨hv, hb, hk, hg⟩ := sep_lift.mp h
    exact sep_lift.mpr ⟨by cases e <;> exact hv, ⟨A, S, K, bs, ha, hn, hpos, hbnd, hal, he, hb⟩, hk, hg⟩
  · rintro r ⟨⟨A, S, K, bs, ha, hn, hpos, hbnd, hal, he, hb⟩, hk, hg⟩
    exact ⟨A, S, K, bs, sep_lift.mpr ⟨⟨ha, hn, hpos, hbnd, hal, he⟩, hb, hk, hg⟩⟩

theorem payload8_owned (p : Ptr) (e : Option ErrName) (hdom : admittedError e) (R : FAssn) :
    FTotalTriple (up (readableUnion (BitVec 8) p 4 2 e) ⋆ R) (TryPointers.payload8 p)
      (fun result => (⟪result = (match e with
        | none => .ok (errPayloadPtr (BitVec 8) p) | some name => .error name)⟫ ⋆
        up (readableUnion (BitVec 8) p 4 2 e)) ⋆ R) := by
  rw [payload8_program]
  exact (payloadProgram_owned p 4 2 e hdom).frame

theorem payload64_owned (p : Ptr) (e : Option ErrName) (hdom : admittedError e) (R : FAssn) :
    FTotalTriple (up (readableUnion (BitVec 64) p 16 8 e) ⋆ R) (TryPointers.payload64 p)
      (fun result => (⟪result = (match e with
        | none => .ok (errPayloadPtr (BitVec 64) p) | some name => .error name)⟫ ⋆
        up (readableUnion (BitVec 64) p 16 8 e)) ⋆ R) := by
  rw [payload64_program]
  exact (payloadProgram_owned p 16 8 e hdom).frame

end TryPointersProofs
