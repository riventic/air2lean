import ZigLean.Sep.Full.Auto
import ZigLean.Sep.Full.AllocSpec

/-!
# Views of atoms (`@[fsym_view]`, `docs/proof-automation.md` §Views)

An atom may stand for another assertion: an atomic word for the region of its 8 bytes
(`apts_view`, one way: the region does not keep the bytes' tag), a region for its owned bytes with
their alignment and kind (`regionIn_view`), owned bytes for a region again (`regionIn_fold`).
When a step is stuck because the planner did not find an atom (a rule's precondition, a return's
postcondition), `fsym` views the state atoms of that atom's block that provide its head and tries
the step again. The scenarios are the arena's `deinit`/`reset` (`tests/roadmap/alloc-arena`): a
node given back to the child allocator with its header words as plain bytes, a typed load of a
region that holds a value's encoding, a refund joined with the reservoir of fees. An entailment
(`fsym_entail`) views its state the same way and adds the facts of its atoms; half of an
extent is lent off its authority (the lists witness's start resources).
-/

namespace SepAuto.Views

open Zig Zig.Full Zig.Full.FAssn

/-! ## A node given back, its header words as plain bytes -/

/-- A grant: its bytes, as a region, and a token for their size (here a fact). -/
def Granted (p : Ptr) (bs : Array Byte) : FAssn :=
  FAssn.ex fun A => FAssn.ex fun S => FAssn.ex fun K =>
    up (regionIn p A S K 8 bs) ⋆ ⟪bs.size = 40⟫

/-- An allocator's `free` (a stand-in that keeps what it is given). -/
@[irreducible] def giveBack (_p : Ptr) : MemM Unit := pure ()

theorem giveBack_spec {p : Ptr} {bs : Array Byte} :
    FTotalTriple (Granted p bs) (giveBack p) (fun _ => Granted p bs) := by
  unfold giveBack; exact FTotalTriple.ret (Q := fun _ => _) ()

/-- A node of 40 bytes: two atomic header words, the `next` pointer and the buffer, given back
whole. The words are viewed as regions (`apts_view`), relabelled and joined with the rest into the
granted region. -/
theorem give_node (p : Ptr) (b : BlockId) (A S : Nat) (K : BlockKind) (sz ei : BitVec 64)
    (nxt : Option Ptr) (buf : Array Byte) (hb : p.block = some b) (hal : (A + p.off.toNat) % 8 = 0)
    (h0 : 0 ≤ p.off) (hbuf : buf.size = 16) :
    FTotalTriple (apts p sz ⋆ apts (p.add 8) ei ⋆ up (regionIn (p.add 16) A S K 8 (Enc.encode nxt)) ⋆
        up (regionIn (p.add 24) A S K 1 buf))
      (giveBack p) (fun _ => FAssn.ex fun bs => Granted p bs) := by
  fsym [giveBack_spec]

/-! ## A typed load of a value's encoding -/

/-- The `next` pointer of a node: a region that holds its encoding (`load_reads`,
`ReadsAt.regionInEnc`). -/
theorem load_next (p : Ptr) (A S : Nat) (K : BlockKind) (nxt : Option Ptr) :
    FTotalTriple (up (regionIn (p.add 16) A S K 8 (Enc.encode nxt)))
      (load (Option Ptr) 8 (p.add 16))
      (fun r => ⟪r = nxt⟫ ⋆ up (regionIn (p.add 16) A S K 8 (Enc.encode nxt))) := by
  fsym

/-! ## Two atoms of one head with unknown arguments -/

/-- A fee of each nonzero fraction (two halves of one: the sum). -/
structure FI where
  fee : Frac → FAssn
  fee_add : ∀ a b : Frac, 0 < a.val → 0 < b.val → fee (a.add b) = (fee a ⋆ fee b)

/-- A refund joins the reservoir (the arena's `cown_refund`). -/
theorem fee_join (I : FI) {u v : Frac} :
    EUpd ((⟪0 < u.val⟫ ⋆ I.fee u) ⋆ (⟪0 < v.val⟫ ⋆ I.fee v))
      (FAssn.ex fun χ : Frac => ⟪0 < χ.val⟫ ⋆ I.fee χ) :=
  EUpd.of_imp fun _ h => by
    obtain ⟨r₁, r₂, hd, e, h1, h2⟩ := h
    obtain ⟨hu, f1⟩ := sep_lift.mp h1
    obtain ⟨hv, f2⟩ := sep_lift.mp h2
    refine ⟨u.add v, sep_lift.mpr ⟨by simp only [Frac.add]; grind, ?_⟩⟩
    rw [I.fee_add _ _ hu hv]
    exact ⟨r₁, r₂, hd, e, f1, f2⟩

/-- The update's two fee atoms take the state's two fees (one each). -/
theorem refund (I : FI) (φ ψ : Frac) (h1 : 0 < φ.val) (h2 : 0 < ψ.val) :
    FTotalTriple (I.fee φ ⋆ I.fee ψ) (pure ())
      (fun _ => FAssn.ex fun χ : Frac => ⟪0 < χ.val⟫ ⋆ I.fee χ) := by
  fsym [fee_join]

/-! ## A region as bytes, and back -/

/-- A command over owned bytes (a stand-in that keeps them). -/
@[irreducible] def touch (_p : Ptr) : MemM Unit := pure ()

theorem touch_spec {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte} :
    FTotalTriple (up (bytesAt p A S K bs)) (touch p) (fun _ => up (bytesAt p A S K bs)) := by
  unfold touch; exact FTotalTriple.ret (Q := fun _ => _) ()

/-- The rule wants the bytes (`regionIn_view`); the postcondition names the region again
(`regionIn_fold`, its alignment and kind from the facts the view left). -/
theorem region_bytes (p : Ptr) (A S : Nat) (K : BlockKind) (bs : Array Byte) :
    FTotalTriple (up (regionIn p A S K 8 bs)) (touch p) (fun _ => up (regionIn p A S K 8 bs)) := by
  fsym [touch_spec]

/-! ## An entailment (`fsym_entail`): a global's start resources as an invariant's parts -/

/-- A buffer as a structure value (the `FixedBufferAllocator`'s witness, `ListsFba`). -/
structure Buf where
  ptr : Ptr
  cap : Nat

def bufp : Ptr := ⟨some 1, 0⟩
def buf0 : Buf := ⟨bufp, 16⟩

/-- **Owned bytes as the region a postcondition names** (ledger #48, `viewAtoms` in
`fsym_entail`), at `bufp.add 0` (#50), its bound a field of a defined structure value. -/
theorem global_tail (A : Nat) :
    EUpd (up (bytesAt ⟨some 1, 0⟩ A 16 .global (Array.replicate 16 .undef)) ⋆ bclaim 1 0 16)
      (up (regionIn (buf0.ptr.add (0 : Nat)) A 16 .global 1 (Array.replicate 16 .undef)) ⋆
        bclaim 1 (buf0.ptr.off.toNat + 0) (buf0.ptr.off.toNat + buf0.cap)) := by
  fsym_entail

/-- **A node as the grant it was** in an entailment (ledger #58): the header words viewed as
regions in the context where the claim gave the node's block, joined with the rest; the grant's
labels are its allocator's token's (`FAllocInv.tok`), which the joined region takes
(`EUpd.relabel`). -/
theorem node_grant (I : FAllocInv) (q φ : Frac) (p : Ptr) (A S : Nat)
    (K : BlockKind) (sz ei : BitVec 64) (nb buf : Array Byte) (hal : (A + p.off.toNat) % 8 = 0)
    (h0 : 0 ≤ p.off) (hnb : nb.size = 8) (hbuf : buf.size = 16) :
    EUpd (apts p sz ⋆ apts (p.add 8) ei ⋆ up (regionIn (p.add 16) A S K 8 nb) ⋆
        up (regionIn (p.add 24) A S K 1 buf) ⋆ I.tok p 40 3 A S K q φ ⋆
        pclaim p p.off.toNat (p.off.toNat + 40))
      (FAssn.ex fun bs => ⟪bs.size = 40⟫ ⋆ FAssn.ex fun A' => FAssn.ex fun S' => FAssn.ex fun K' =>
        up (regionIn p A' S' K' 8 bs) ⋆ I.tok p bs.size 3 A' S' K' q φ ⋆
          pclaim p p.off.toNat (p.off.toNat + bs.size)) := by
  fsym_entail

/-- The same with the token a local function of the caller (`tok`, not a constant): its
arguments match up to arithmetic as a constant's do. -/
theorem node_grant_local (tok : Ptr → Nat → Nat → Nat → Nat → BlockKind → Frac → Frac → FAssn)
    (q φ : Frac) (p : Ptr) (A S : Nat)
    (K : BlockKind) (sz ei : BitVec 64) (nb buf : Array Byte) (hal : (A + p.off.toNat) % 8 = 0)
    (h0 : 0 ≤ p.off) (hnb : nb.size = 8) (hbuf : buf.size = 16) :
    EUpd (apts p sz ⋆ apts (p.add 8) ei ⋆ up (regionIn (p.add 16) A S K 8 nb) ⋆
        up (regionIn (p.add 24) A S K 1 buf) ⋆ tok p 40 3 A S K q φ ⋆
        pclaim p p.off.toNat (p.off.toNat + 40))
      (FAssn.ex fun bs => ⟪bs.size = 40⟫ ⋆ FAssn.ex fun A' => FAssn.ex fun S' => FAssn.ex fun K' =>
        up (regionIn p A' S' K' 8 bs) ⋆ tok p bs.size 3 A' S' K' q φ ⋆
          pclaim p p.off.toNat (p.off.toNat + bs.size)) := by
  fsym_entail

/-- **Half of the extent lent off its authority** in an entailment (ledger #49). -/
theorem lend_half :
    EUpd (bext 1 16 .global)
      (bshare 1 Frac.one.half (buf0.ptr.off.toNat + buf0.cap) ⋆ bauth 1 16 .global Frac.one.half) := by
  fsym_entail

/-- A user fact the planner leaves (the dispatch tokenizer's `counted`): the retry with the
facts of the state's atoms closes no more, and the fact is the caller's goal. -/
def Twice (xs : List Nat) : Prop := (xs ++ xs).length = 2 * xs.length

theorem fact_left (p : Ptr) (A S : Nat) (K : BlockKind) (bs : Array Byte) (xs : List Nat) :
    EUpd (up (regionIn p A S K 8 bs)) (⟪Twice xs⟫ ⋆ up (regionIn p A S K 8 bs)) := by
  fsym_entail
  simp only [Twice, List.length_append]; omega

end SepAuto.Views
