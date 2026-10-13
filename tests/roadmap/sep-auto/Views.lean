import ZigLean.Sep.Full.Auto

/-!
# Views of atoms (`@[fsym_view]`, `docs/proof-automation.md` §Views)

An atom may stand for another assertion: an atomic word for the region of its 8 bytes
(`apts_view`, one way: the region does not keep the bytes' tag), a region for its owned bytes with
their alignment and kind (`regionIn_view`), owned bytes for a region again (`regionIn_fold`).
When a step is stuck because the planner did not find an atom (a rule's precondition, a return's
postcondition), `fsym` views the state atoms of that atom's block that provide its head and tries
the step again. The scenarios are the arena's `deinit`/`reset` (`tests/roadmap/alloc-arena`): a
node given back to the child allocator with its header words as plain bytes, a typed load of a
region that holds a value's encoding, a refund joined with the reservoir of fees.
-/

namespace SepAuto.Views

open Zig Zig.Full Zig.Full.FAssn

/-! ## A node given back, its header words as plain bytes -/

/-- The child allocator's token for a grant of `n` bytes at `p` (opaque here). -/
opaque tk (p : Ptr) (n A S : Nat) (K : BlockKind) : FAssn

/-- A grant: its bytes, as a region, and the token for them. -/
def Granted (p : Ptr) (bs : Array Byte) : FAssn :=
  FAssn.ex fun A => FAssn.ex fun S => FAssn.ex fun K =>
    up (regionIn p A S K 8 bs) ⋆ tk p bs.size A S K

/-- The child allocator's `free` (opaque here). -/
opaque giveBack (p : Ptr) : MemM Unit

/-- `free` takes a grant. -/
axiom giveBack_spec {p : Ptr} {bs : Array Byte} :
    FTotalTriple (Granted p bs) (giveBack p) (fun _ => emp)

/-- A node of 40 bytes: two atomic header words, the `next` pointer and the buffer, given back
whole. The words are viewed as regions (`apts_view`), relabelled and joined with the rest into the
granted region, whose size the token names. -/
theorem give_node (p : Ptr) (b : BlockId) (A S : Nat) (K : BlockKind) (sz ei : BitVec 64)
    (nxt : Option Ptr) (buf : Array Byte) (hb : p.block = some b) (hal : (A + p.off.toNat) % 8 = 0)
    (h0 : 0 ≤ p.off) (hbuf : buf.size = 16) :
    FTotalTriple (apts p sz ⋆ apts (p.add 8) ei ⋆ up (regionIn (p.add 16) A S K 8 (Enc.encode nxt)) ⋆
        up (regionIn (p.add 24) A S K 1 buf) ⋆ tk p 40 A S K)
      (giveBack p) (fun _ => emp) := by
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

/-- An allocator's fees (fractional). -/
structure FI where
  fee : Frac → FAssn

/-- A refund joins the reservoir (the arena's `cown_refund`, here an axiom). -/
axiom fee_join (I : FI) {u v : Frac} :
    EUpd ((⟪0 < u.val⟫ ⋆ I.fee u) ⋆ (⟪0 < v.val⟫ ⋆ I.fee v))
      (FAssn.ex fun χ : Frac => ⟪0 < χ.val⟫ ⋆ I.fee χ)

/-- The update's two fee atoms take the state's two fees (one each). -/
theorem refund (I : FI) (φ ψ : Frac) (h1 : 0 < φ.val) (h2 : 0 < ψ.val) :
    FTotalTriple (I.fee φ ⋆ I.fee ψ) (pure ())
      (fun _ => FAssn.ex fun χ : Frac => ⟪0 < χ.val⟫ ⋆ I.fee χ) := by
  fsym [fee_join]

/-! ## A region as bytes, and back -/

/-- A command over owned bytes (opaque here): it reverses them. -/
opaque reverseBytes (p : Ptr) : MemM Unit

axiom reverseBytes_spec {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte} :
    FTotalTriple (up (bytesAt p A S K bs)) (reverseBytes p)
      (fun _ => up (bytesAt p A S K bs.reverse))

/-- The rule wants the bytes (`regionIn_view`); the postcondition names the region again
(`regionIn_fold`, its alignment and kind from the facts the view left). -/
theorem region_bytes (p : Ptr) (A S : Nat) (K : BlockKind) (bs : Array Byte) :
    FTotalTriple (up (regionIn p A S K 8 bs)) (reverseBytes p)
      (fun _ => up (regionIn p A S K 8 bs.reverse)) := by
  fsym [reverseBytes_spec]

end SepAuto.Views
