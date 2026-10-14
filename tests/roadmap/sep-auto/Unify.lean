import ZigLean.Sep.Full.Auto

/-!
# `fsym`: planning order and terms equal up to arithmetic (`docs/proof-automation.md` §Planner)

The cases come from the generated `std.mem.Allocator` wrappers (`tests/roadmap/alloc-fba`,
`realloc` and `allocSentinel`) and the error-union tests (`tests/roadmap/try-pointers`):

* **planning order**: a grant whose bytes were written after the allocation (`@memset` of the
  fresh bytes, the moved prefix) still has the allocation's token `I.tok p bs.size …`. The
  postcondition's grant `I.granted p 0 φ ?bs'` with a size fact takes its bytes from the region
  (the region planner, `carve`); the token matches after that, its size up to arithmetic;
* **atoms equal up to arithmetic**: a region's bytes `replicate x.toNat …` against
  `replicate (n + 1) …` with the fact `x.toNat = n + 1` (argument by argument, `proveEq`);
* **hypotheses equal up to arithmetic** (`assumptionEq`): a rule's side condition
  `I.fits x.toNat 0` by `I.fits (n + 1) 0`;
* **hypotheses equal up to unfolding**: a side condition about a structure value's field
  (`{ names := … }.names.contains e = true`) by a hypothesis that unfolds to it.
-/

namespace SepAuto.Unify

open Zig Zig.Full Zig.Full.FAssn

/-- A grant after its bytes were written: the token still has the allocation's size. -/
theorem granted_after_write (I : FAllocInv) (p : Ptr) (A S : Nat) (K : BlockKind) (q φ : Frac)
    (bs : Array Byte) (n : Nat) (x : BitVec 64) (b : BlockId) (hb : p.block = some b)
    (hbs : bs.size = n) (hx : x.toNat = n) :
    EUpd (up (regionIn p A S K (2 ^ 0) (Array.replicate x.toNat .undef)) ⋆ (I.tok p bs.size 0 A S K q φ ⋆
        (bshare b q (p.off.toNat + bs.size) I.tag ⋆ bclaim b p.off.toNat (p.off.toNat + bs.size) I.tag)))
      (FAssn.ex fun bs' => ⟪bs'.size = n⟫ ⋆ I.granted p 0 φ bs') := by
  fsym_entail

set_option linter.unusedVariables false in
/-- Rejected: the written bytes are longer than the grant. -/
example (I : FAllocInv) (p : Ptr) (A S : Nat) (K : BlockKind) (q φ : Frac) (bs : Array Byte) (n : Nat)
    (x : BitVec 64) (b : BlockId) (hb : p.block = some b) (hbs : bs.size = n)
    (hx : x.toNat = n + 1) : True := by
  fail_if_success
    have : EUpd (up (regionIn p A S K (2 ^ 0) (Array.replicate x.toNat .undef)) ⋆ (I.tok p bs.size 0 A S K q φ ⋆
        (bshare b q (p.off.toNat + bs.size) I.tag ⋆ bclaim b p.off.toNat (p.off.toNat + bs.size) I.tag)))
      (FAssn.ex fun bs' => ⟪bs'.size = n⟫ ⋆ I.granted p 0 φ bs') := by
      fsym_entail
  trivial

set_option linter.unusedVariables false in
/-- A sentinel stored after `n` undefined bytes of a grant of `x = n + 1` bytes. -/
theorem region_upto_arith (p : Ptr) (A S : Nat) (K : BlockKind) (n x : BitVec 64) (b : BlockId)
    (hb : p.block = some b) (hx : x.toNat = n.toNat + 1) :
    EUpd (up (regionIn p A S K 1 (writeBytes (Array.replicate x.toNat .undef) (1 * (n.toNat : Int)).toNat
        (Enc.encode 7#8))))
      (up (regionIn p A S K 1 (writeBytes (Array.replicate (n.toNat + 1) .undef) n.toNat
        (Enc.encode (7 : BitVec 8))))) := by
  fsym_entail

set_option linter.unusedVariables false in
/-- Rejected: one byte more. -/
example (p : Ptr) (A S : Nat) (K : BlockKind) (n x : BitVec 64) (b : BlockId) (hb : p.block = some b)
    (hx : x.toNat = n.toNat + 2) : True := by
  fail_if_success
    have : EUpd (up (regionIn p A S K 1 (writeBytes (Array.replicate x.toNat .undef) n.toNat (Enc.encode 7#8))))
        (up (regionIn p A S K 1 (writeBytes (Array.replicate (n.toNat + 1) .undef) n.toNat
          (Enc.encode (7 : BitVec 8))))) := by
      fsym_entail
  trivial

/-- A rule's side condition by a hypothesis whose arguments are equal by arithmetic. -/
theorem side_upto_arith (I : FAllocInv) (op : BitVec 64 → MemM Unit) (n x : BitVec 64)
    (hA : ∀ len : BitVec 64, I.fits len.toNat 0 → FTotalTriple emp (op len) (fun _ => emp))
    (hfit : I.fits (n.toNat + 1) 0) (hx : x.toNat = n.toNat + 1) :
    FTotalTriple emp (op x) (fun _ => emp) := by
  fsym [hA]

set_option linter.unusedVariables false in
/-- Rejected: the hypothesis is about another size. -/
example (I : FAllocInv) (op : BitVec 64 → MemM Unit) (n x : BitVec 64)
    (hA : ∀ len : BitVec 64, I.fits len.toNat 0 → FTotalTriple emp (op len) (fun _ => emp))
    (hfit : I.fits (n.toNat + 2) 0) (hx : x.toNat = n.toNat + 1) : True := by
  fail_if_success
    have : FTotalTriple emp (op x) (fun _ => emp) := by fsym [hA]
  trivial

/-- A declared error domain (as the translator's `ErrorDomain`). -/
structure Dom where
  names : Array String

abbrev dom : Dom := ⟨#["Bad", "Other"]⟩

/-- A side condition about a field of a structure value by a hypothesis that unfolds to it. -/
theorem side_upto_unfold (g : String → MemM Unit) (e : String)
    (hR : ∀ e, ({ names := #["Bad", "Other"] } : Dom).names.contains e = true →
      FTotalTriple emp (g e) (fun _ => emp))
    (hd : Option.all dom.names.contains (some e) = true) :
    FTotalTriple emp (g e) (fun _ => emp) := by
  fsym [hR]

set_option linter.unusedVariables false in
/-- Rejected: the hypothesis is about another name. -/
example (g : String → MemM Unit) (e e' : String)
    (hR : ∀ e, ({ names := #["Bad", "Other"] } : Dom).names.contains e = true →
      FTotalTriple emp (g e) (fun _ => emp))
    (hd : Option.all dom.names.contains (some e') = true) : True := by
  fail_if_success
    have : FTotalTriple emp (g e) (fun _ => emp) := by fsym [hR]
  trivial

/-- A buffer: nothing when empty, else a region (a list's `buf`, `Proofs/Lists/Append.lean`). -/
def Buf (p : Ptr) (A S : Nat) (K : BlockKind) (bs : Array Byte) : FAssn :=
  if bs.size = 0 then emp else up (regionIn p A S K 1 bs)

/-- **A postcondition `if` on an existential**: `bs` is known only once the planner has matched
the region, so `fsym` tries each branch with its condition as a fact. -/
theorem post_if_exists (p : Ptr) (A S : Nat) (K : BlockKind) (cs : Array Byte) (hc : cs.size = 4) :
    FTotalTriple (up (regionIn p A S K 1 cs)) (pure ())
      (fun _ => FAssn.ex fun bs => ⟪bs.size = 4⟫ ⋆ Buf p A S K bs) := by
  fsym

end SepAuto.Unify
