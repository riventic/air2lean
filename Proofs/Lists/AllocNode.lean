import Proofs.Lists.Linked
import ZigLean.Sep.Full.Wrappers
import ZigLean.Sep.Full.Dispatch
import ZigLean.Sep.Full.Auto
import ZigLean.Sep.Full.Block
import ZigLean.Sep.Full.AutoPrim
import ZigLean.Sep.Full.Typed
import ZigLean.Sep.Full.Try
import ZigLean.Sep.Full.Region
import ZigLean.Sep.Full.Fields

/-!
# The nodes of `examples/lists/lists.zig` that an allocator granted, and `destroy`'s contract

The specification that `Proofs/Lists/Alloc.lean` and the generated invariant of `freeAll`'s loop
(`Proofs/Lists/AllocInv.lean`, `air2lean-invgen --spec Proofs.Lists.AllocNode --contract
Lists.Alloc.destroy_fields`) share: the generator reads the contract of the call that the loop
hands each node to, so this module is its input and comes before the invariant.

A node that `push` allocated for the fee `φ` (`FAllocInv.fee`, `docs/sep-full-state.md` §The fee
of a grant) is `node I φ p v q`: its fields `next` (offset 0) and `val` (offset 8) as typed values
(`Linked.node`), and the rest of its 16-byte grant, `nodeRest I φ p`: the four padding bytes, the
allocator's token (which records `φ`), the grant's extent share and claim. `list I φ hd xs` is the
list of such nodes.

`destroy_fields` is the contract of `a.destroy(n)` on such a node, for every allocator that meets
`CAllocSpec` (the environment's, at the vtable `fns`): the node's fields and the rest of its grant
go back, the fee `I.fee φ` returns, and the allocator tells what it knows of the freed pointer
(`FAllocInv.freed`). The node is a grant of 16 bytes again by `EUpd.granted_of_node`, which reads
the fields' labels off the memory (`ZigLean/Sep/Full/Fields.lean`).
-/

namespace Lists.Alloc

open Zig Zig.Full Zig.Full.FAssn Lists.Open Lists.Linked

/-! ## Nodes -/

/-- The rest of a node's grant for the fee `φ` besides its fields: the padding bytes, the
allocator's token, and the grant's extent share and claim (`FAllocInv.granted` of 16 bytes at
alignment `2 ^ 3`). -/
def nodeRest (I : FAllocInv) (φ : Frac) (p : Ptr) : FAssn :=
  FAssn.ex fun A => FAssn.ex fun S => FAssn.ex fun K => FAssn.ex fun q => FAssn.ex fun pad : Array Byte =>
    ⟪pad.size = 4⟫ ⋆ (up (regionIn (p.add 12) A S K 4 pad) ⋆ (I.tok p 16 3 A S K q φ ⋆
      (pshare p q (p.off.toNat + 16) I.tag ⋆ pclaim p p.off.toNat (p.off.toNat + 16) I.tag)))

-- the rest of a node's grant is handed on whole (to `destroy_fields`)
attribute [fsym_atom] nodeRest

/-- A node that `I`'s allocator granted for the fee `φ`. -/
abbrev node (I : FAllocInv) (φ : Frac) (p : Ptr) (v : BitVec 32) (q : Option Ptr) : FAssn :=
  Linked.node (nodeRest I φ) p v q

/-- The list at `hd` of nodes that `I`'s allocator granted for the fee `φ` holds `xs`. -/
abbrev list (I : FAllocInv) (φ : Frac) (hd : Option Ptr) (xs : List (BitVec 32)) : FAssn :=
  Linked.list (nodeRest I φ) hd xs

/-- A node is a grant of 16 bytes again: its fields join the padding's region (an update in the
memory, `EUpd.pts_region_join`). -/
theorem EUpd.granted_of_node {I : FAllocInv} {φ : Frac} {p : Ptr} {v : BitVec 32} {q : Option Ptr} :
    EUpd (node I φ p v q) (FAssn.ex fun bs : Array Byte => ⟪bs.size = 16⟫ ⋆ I.granted p 3 φ bs) := by
  -- the grant's labels, token, share and claim out front
  refine EUpd.trans (P' := (FAssn.ex fun A => FAssn.ex fun S => FAssn.ex fun K => FAssn.ex fun q' =>
      FAssn.ex fun pad : Array Byte => ⟪pad.size = 4⟫ ⋆
        ((up (pts (p.add 8) 4 v) ⋆ up (regionIn ((p.add 8).add (Enc.size (BitVec 32))) A S K 4 pad)) ⋆
          (up (pts p 8 q) ⋆ (I.tok p 16 3 A S K q' φ ⋆
            (pshare p q' (p.off.toNat + 16) I.tag ⋆ pclaim p p.off.toNat (p.off.toNat + 16) I.tag))))))
    (EUpd.of_imp fun r h => ?_) ?_
  · obtain ⟨r₁, r₂, hd, rfl, h1, h2⟩ := h
    obtain ⟨r₃, r₄, hd', rfl, h3, ⟨A, S, K, q', pad, h4⟩⟩ := h2
    obtain ⟨hpad, h4⟩ := sep_lift.mp h4
    refine ⟨A, S, K, q', pad, sep_lift.mpr ⟨hpad, ?_⟩⟩
    have e : (p.add 8).add (Enc.size (BitVec 32)) = p.add 12 := by rw [Ptr.add_add]; rfl
    rw [e]
    have hx : (up (pts p 8 q) ⋆ (up (pts (p.add 8) 4 v) ⋆
        (up (regionIn (p.add 12) A S K 4 pad) ⋆ (I.tok p 16 3 A S K q' φ ⋆
          (pshare p q' (p.off.toNat + 16) I.tag ⋆ pclaim p p.off.toNat (p.off.toNat + 16) I.tag))))) _ :=
      ⟨r₁, _, hd, rfl, h1, ⟨r₃, r₄, hd', rfl, h3, h4⟩⟩
    exact ac_cast hx (by ac_rfl)
  refine EUpd.exAll fun A => EUpd.exAll fun S => EUpd.exAll fun K => EUpd.exAll fun q' =>
    EUpd.exAll fun pad => EUpd.lift fun hpad => ?_
  -- `val` joins the padding, then `next` joins both
  refine EUpd.trans (EUpd.frame (EUpd.pts_region_join (by decide) (by omega))) ?_
  refine EUpd.ex fun cs => EUpd.trans (EUpd.of_imp fun _ h => sep_assoc h)
    (EUpd.lift fun ⟨hcs, _, _⟩ => ?_)
  refine EUpd.trans (P' := (up (pts p 8 q) ⋆ up (regionIn (p.add (Enc.size (Option Ptr))) A S K 4 cs)) ⋆
      (I.tok p 16 3 A S K q' φ ⋆ (pshare p q' (p.off.toNat + 16) I.tag ⋆
        pclaim p p.off.toNat (p.off.toNat + 16) I.tag)))
    (EUpd.of_imp fun _ h => ac_cast h (by ac_rfl)) ?_
  have hcs4 : 0 < cs.size := by rw [hcs, hpad]; decide
  refine EUpd.trans (EUpd.frame (EUpd.pts_region_join (T := Option Ptr) (by decide) hcs4)) ?_
  refine EUpd.ex fun ds => EUpd.trans (EUpd.of_imp fun _ h => Full.sep_assoc h)
    (EUpd.lift fun ⟨hds, _, _⟩ => EUpd.of_imp fun r h => ?_)
  have h16 : ds.size = 16 := by rw [hds, hcs, hpad]; rfl
  refine ⟨ds, sep_lift.mpr ⟨h16, A, S, K, q', ?_⟩⟩
  rw [h16]
  exact h

/-! ## The allocator -/

/-- The alignment argument of the generated entries, from its log2. -/
def al (k : Nat) : mem_Alignment := ⟨BitVec.ofNat 6 k⟩

variable [Ext]

/-- The environment's allocator entries: `Ext.call0` (`alloc`), `Ext.call1` (`remap`) and
`Ext.call2` (`free`); `e`'s `resize`, which the program never calls. -/
def env (e : AllocEnv Tgt) : AllocEnv Tgt :=
  { e with
    alloc := fun f a => Ext.call0 f a.1 a.2.1 (al a.2.2.1) a.2.2.2
    remap := fun f a => Ext.call1 f a.1 a.2.1 (al a.2.2.1) a.2.2.2.1 a.2.2.2.2
    free := fun f a => Ext.call2 f a.1 a.2.1 (al a.2.2.1) a.2.2.2 }

variable (ctx vtp : Ptr) (fns : VTableFns) (I : FAllocInv) (e : AllocEnv Tgt) (φ : Frac)

/-! ## `destroy` -/

set_option maxRecDepth 20000 in
/-- `destroy` of a grant: its fee back, and what the allocator tells about the freed pointer
(`FAllocInv.freed`). -/
theorem destroy_grant (p : Ptr) (bs : Array Byte) (hbs : bs.size = 16)
    (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted p 3 φ bs ⋆ vtR vtp fns.toList))
      (mem_Allocator_destroy__anon_a9add1f02861 ⟨ctx, vtp⟩ p)
      (fun _ => I.own ⋆ (I.fee φ ⋆ (vtR vtp fns.toList ⋆ I.freed p))) := by
  unfold mem_Allocator_destroy__anon_a9add1f02861
  fsym [CAllocSpec.free h]

set_option maxRecDepth 20000 in
/-- `destroy` of a node gives its grant back to the allocator. -/
theorem destroy_spec (p : Ptr) (v : BitVec 32) (q : Option Ptr)
    (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (node I φ p v q ⋆ vtR vtp fns.toList))
      (mem_Allocator_destroy__anon_a9add1f02861 ⟨ctx, vtp⟩ p)
      (fun _ => I.own ⋆ (I.fee φ ⋆ (vtR vtp fns.toList ⋆ I.freed p))) := by
  refine CTriple.eupd (EUpd.frameL (EUpd.frame EUpd.granted_of_node))
    (CTriple.pre (P := FAssn.ex fun bs : Array Byte => ⟪bs.size = 16⟫ ⋆
      (I.own ⋆ (I.granted p 3 φ bs ⋆ vtR vtp fns.toList)))
      (CTriple.ex fun bs => CTriple.lift fun hbs => destroy_grant ctx vtp fns I e φ p bs hbs h)
      fun _ h => ?_)
  obtain ⟨r₁, r₂, hd, rfl, h1, h2⟩ := h
  obtain ⟨bs, h2⟩ := sep_ex.mp h2
  obtain ⟨hbs, h2⟩ := sep_lift.mp (Full.sep_assoc h2)
  exact ⟨bs, sep_lift.mpr ⟨hbs, r₁, r₂, hd, rfl, h1, h2⟩⟩

set_option maxRecDepth 20000 in
/-- **The contract of `destroy` on a node**, with the node's fields in view (the form the loop
body of `freeAll` has): the contract that the generated invariant of `freeAll`'s loop is read
from (`Proofs/Lists/AllocInv.lean`). -/
theorem destroy_fields (p : Ptr) (v : BitVec 32) (q : Option Ptr)
    (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ ((up (pts p 8 q) ⋆ (up (pts (p.add 8) 4 v) ⋆ nodeRest I φ p)) ⋆ vtR vtp fns.toList))
      (mem_Allocator_destroy__anon_a9add1f02861 ⟨ctx, vtp⟩ p)
      (fun _ => I.own ⋆ (I.fee φ ⋆ (vtR vtp fns.toList ⋆ I.freed p))) :=
  destroy_spec ctx vtp fns I e φ p v q h

end Lists.Alloc
