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
# `examples/lists/lists.zig` for every allocator

`push` and `freeAll` take a `std.mem.Allocator`. In `Proofs/Lists/Open.lean` every call through
it reaches the environment (`Ext`, premise EXT-05; `docs/interfaces.md`), so the theorems here
assume only the allocator contract `CAllocSpec` of the environment's allocator at the vtable
`fns` (`CVTable.env`), with invariant `I`, and hold for every allocator that meets it: a
concrete allocator enters only through its proved contract.

A node that `push` allocated for the fee `φ` (`FAllocInv.fee`, `docs/sep-full-state.md` §The fee
of a grant) is `node I φ p v q`: its fields `next` (offset 0) and `val` (offset 8) as typed values
(`Linked.node`), and the rest of its 16-byte grant, `nodeRest I φ p`: the four padding bytes, the
allocator's token (which records `φ`), the grant's extent share and claim. `list I φ hd xs` is the
list of such nodes. `reverse` and `sum` (`Proofs/Lists/Linked.lean`) hold for it as for every
owner of the nodes.

* `push_spec`: `push` takes a fee `I.fee φ` and returns a new node in front of `next`, or
  `error.OutOfMemory` and the fee back: the allocator's state `I.own` and the fee are all it keeps.
* `freeAll_spec`: `freeAll` returns every node to the allocator: afterwards the caller owns
  `I.own`, the fee of every node (`fees I φ xs.length`) and nothing of the list.

The grant and the node are two views of the same bytes (`node_of_granted`; back:
`EUpd.granted_of_node`, which reads the fields' labels off the memory,
`ZigLean/Sep/Full/Fields.lean`). The generated code is walked by `fsym`; `freeAll`'s loop is
`CTriple.loop` with the list as its invariant. These are `CTriple`s (partial correctness, no
panic): the contract `CAllocSpec` is one, so a client of an arbitrary allocator gets no more.
-/

namespace Lists.Alloc

open Zig Zig.Full Zig.Full.FAssn Lists.Open Lists.Linked

/-! ## Nodes -/

/-- The bytes of a node that `push` wrote: `next` at 0, `val` at 8, the padding undefined. -/
abbrev nodeBytes (v : BitVec 32) (q : Option Ptr) : Array Byte :=
  writeBytes (writeBytes (Array.replicate 16 .undef) 8 (Enc.encode v)) 0 (Enc.encode q)

theorem nodeBytes_eq (v : BitVec 32) (q : Option Ptr) :
    nodeBytes v q = Enc.encode q ++ Enc.encode v ++ Array.replicate 4 .undef := by
  have h8 : (Enc.encode q).size = 8 := LawfulEnc.size_encode q
  have h4 : (Enc.encode v).size = 4 := LawfulEnc.size_encode v
  have e : (Enc.encode v).extract 0 4 = Enc.encode v := by
    rw [show (4 : Nat) = (Enc.encode v).size from h4.symm]; exact Array.extract_size
  simp [nodeBytes, writeBytes, Array.extract_append, h8, h4, e]

theorem nodeBytes_size (v : BitVec 32) (q : Option Ptr) : (nodeBytes v q).size = 16 := by
  rw [nodeBytes_eq]; simp [LawfulEnc.size_encode]; rfl

theorem nodeBytes_next (v : BitVec 32) (q : Option Ptr) :
    Enc.decode ((nodeBytes v q).extract 0 (Enc.size (Option Ptr))) = pure q := by
  rw [nodeBytes_eq, Array.append_assoc, ← LawfulEnc.size_encode q, Region.extract_append_left]
  exact LawfulEnc.decode_encode q

theorem nodeBytes_rest (v : BitVec 32) (q : Option Ptr) :
    (nodeBytes v q).extract (Enc.size (Option Ptr)) (nodeBytes v q).size =
      Enc.encode v ++ Array.replicate 4 .undef := by
  rw [nodeBytes_eq, Array.append_assoc, ← LawfulEnc.size_encode q, Region.extract_append_right]

theorem valPad_val (v : BitVec 32) :
    Enc.decode ((Enc.encode v ++ Array.replicate 4 Byte.undef).extract 0 (Enc.size (BitVec 32))) =
      pure v := by
  rw [← LawfulEnc.size_encode v, Region.extract_append_left]
  exact LawfulEnc.decode_encode v

theorem valPad_pad (v : BitVec 32) :
    (Enc.encode v ++ Array.replicate 4 Byte.undef).extract (Enc.size (BitVec 32))
      (Enc.encode v ++ Array.replicate 4 Byte.undef).size = Array.replicate 4 .undef := by
  rw [← LawfulEnc.size_encode v, Region.extract_append_right]

/-- The rest of a node's grant for the fee `φ` besides its fields: the padding bytes, the
allocator's token, and the grant's extent share and claim (`FAllocInv.granted` of 16 bytes at
alignment `2 ^ 3`). -/
def nodeRest (I : FAllocInv) (φ : Frac) (p : Ptr) : FAssn :=
  FAssn.ex fun A => FAssn.ex fun S => FAssn.ex fun K => FAssn.ex fun q => FAssn.ex fun pad : Array Byte =>
    ⟪pad.size = 4⟫ ⋆ (up (regionIn (p.add 12) A S K 4 pad) ⋆ (I.tok p 16 3 A S K q φ ⋆
      (pshare p q (p.off.toNat + 16) I.tag ⋆ pclaim p p.off.toNat (p.off.toNat + 16) I.tag)))

/-- A node that `I`'s allocator granted for the fee `φ`. -/
abbrev node (I : FAllocInv) (φ : Frac) (p : Ptr) (v : BitVec 32) (q : Option Ptr) : FAssn :=
  Linked.node (nodeRest I φ) p v q

/-- The list at `hd` of nodes that `I`'s allocator granted for the fee `φ` holds `xs`. -/
abbrev list (I : FAllocInv) (φ : Frac) (hd : Option Ptr) (xs : List (BitVec 32)) : FAssn :=
  Linked.list (nodeRest I φ) hd xs

/-- `n` fees `φ` of `I`'s allocator. -/
abbrev fees (I : FAllocInv) (φ : Frac) (n : Nat) : FAssn := sepN n fun _ => I.fee φ

theorem fees_succ {I : FAllocInv} {φ : Frac} {n : Nat} : fees I φ (n + 1) = (I.fee φ ⋆ fees I φ n) :=
  rfl

theorem fees_add {I : FAllocInv} {φ : Frac} (m n : Nat) :
    fees I φ (m + n) = (fees I φ m ⋆ fees I φ n) := by
  induction m with
  | zero => rw [Nat.zero_add]; exact (Zig.Full.emp_sep_eq _).symm
  | succ m ih => rw [Nat.succ_add, fees_succ, ih, fees_succ]; ac_rfl

section Views

variable {I : FAllocInv} {φ : Frac} {p : Ptr} {v : BitVec 32} {q : Option Ptr}

/-- The grant of a node that `push` wrote is the node: its fields split off the region. -/
theorem node_of_granted {r : Res} (h : I.granted p 3 φ (nodeBytes v q) r) : node I φ p v q r := by
  obtain ⟨A, S, K, q', h⟩ := h
  obtain ⟨-, h0, hal⟩ := Auto.facts_region.sepL h
  have e8 : ((p.add 8).off.toNat) = p.off.toNat + 8 := by simp [Ptr.add]; omega
  have h1 := sep_mono_left (fun r h => region_pts_split (T := Option Ptr) (v := q) (a' := 4)
    (by rw [nodeBytes_size]; decide) (nodeBytes_next v q)
    (by change (A + p.off.toNat + 8) % 4 = 0; omega) h) h
  rw [nodeBytes_rest] at h1
  have h2 := sep_mono_left (fun r h => sep_mono_right (fun r h =>
    region_pts_split (T := BitVec 32) (v := v) (a' := 4) (by simp [LawfulEnc.size_encode])
      (valPad_val v) (by change (A + (p.add 8).off.toNat + 4) % 4 = 0; omega) h) h) h1
  rw [valPad_pad, Ptr.add_add, nodeBytes_size] at h2
  refine sep_mono (fun _ h => h) (fun r h => sep_mono_right (fun r h => ?_) h)
    (sep_mono_right (fun _ h => Full.sep_assoc h) (Full.sep_assoc h2))
  exact ⟨A, S, K, q', Array.replicate 4 .undef, sep_lift.mpr ⟨rfl, h⟩⟩

/-- A node is a grant of 16 bytes again: its fields join the padding's region (an update in the
memory, `EUpd.pts_region_join`). -/
theorem EUpd.granted_of_node :
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

end Views

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

/-- `create`: its result slot is a stack local, so it runs in the plain mode (`plain`, #328). -/
theorem create_spec (hfit : I.fits (16 : BitVec 64).toNat 3)
    (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList) ⋆ plain)
      (mem_Allocator_create__anon_48603a336c43 ⟨ctx, vtp⟩)
      (fun r => I.own ⋆ (I.allocResult 3 16 φ r ⋆ vtR vtp fns.toList) ⋆ plain) := by
  fsym [CAllocSpec.alloc h]

/-- What `push` returns: a new node in front of `next`, or `error.OutOfMemory` and the fee back. -/
def pushed (next : Option Ptr) (v : BitVec 32) : Except ErrName Ptr → FAssn
  | .ok p => node I φ p v next
  | .error e => ⟪e = "OutOfMemory"⟫ ⋆ I.fee φ

/-- `push`'s grant, as it wrote it. -/
def pushResult (next : Option Ptr) (v : BitVec 32) : Except ErrName Ptr → FAssn
  | .ok p => I.granted p 3 φ (nodeBytes v next)
  | .error e => ⟪e = "OutOfMemory"⟫ ⋆ I.fee φ

-- the store of `next` at the start of the node's region (not a default rule, `Full/Region.lean`)
attribute [local fsym] FTotalTriple.regionStore0

theorem push_grant (next : Option Ptr) (v : BitVec 32) (hfit : I.fits (16 : BitVec 64).toNat 3)
    (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList) ⋆ plain) (push ⟨ctx, vtp⟩ next v)
      (fun r => I.own ⋆ (pushResult I φ next v r ⋆ vtR vtp fns.toList) ⋆ plain) := by
  fsym [create_spec ctx vtp fns I e φ hfit h]

/-- **`push`** takes a fee and returns a new node in front of `next`, or `error.OutOfMemory` and
the fee back, for every allocator that meets the contract. -/
theorem push_spec (next : Option Ptr) (v : BitVec 32) (hfit : I.fits (16 : BitVec 64).toNat 3)
    (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList) ⋆ plain) (push ⟨ctx, vtp⟩ next v)
      (fun r => I.own ⋆ (pushed I φ next v r ⋆ vtR vtp fns.toList) ⋆ plain) :=
  (push_grant ctx vtp fns I e φ next v hfit h).post fun r _ hr => by
    cases r with
    | ok p => exact sep_mono_right (fun _ h => sep_mono_left (fun _ h =>
        sep_mono_left (fun _ h => node_of_granted h) h) h) hr
    | error _ => exact hr

omit [Ext] in
theorem fromByteUnits_8 : mem_Alignment_fromByteUnits 8 = pure mem_Alignment.«8» := by
  have h : (8 : BitVec 64).ctz = 3 := Zig.ctz_twoPow (k := 3) (by decide)
  unfold mem_Alignment_fromByteUnits math_isPowerOfTwo__anon_38853e1fe316 debug_assert
  simp only [Zig.ctz, h]
  rfl

set_option maxRecDepth 20000 in
theorem destroy_grant (p : Ptr) (bs : Array Byte) (hbs : bs.size = 16)
    (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted p 3 φ bs ⋆ vtR vtp fns.toList))
      (mem_Allocator_destroy__anon_a9add1f02861 ⟨ctx, vtp⟩ p)
      (fun _ => I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) := by
  -- fsym does not evaluate the pure helper on its literal (fsym-engine ledger)
  unfold mem_Allocator_destroy__anon_a9add1f02861
  simp only [fromByteUnits_8]
  fsym [CAllocSpec.free h]

set_option maxRecDepth 20000 in
/-- `destroy` of a node gives its grant back to the allocator. -/
theorem destroy_spec (p : Ptr) (v : BitVec 32) (q : Option Ptr)
    (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (node I φ p v q ⋆ vtR vtp fns.toList))
      (mem_Allocator_destroy__anon_a9add1f02861 ⟨ctx, vtp⟩ p)
      (fun _ => I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) := by
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
/-- `destroy_spec` with the node's fields in view (the form the loop body of `freeAll` has). -/
theorem destroy_fields (p : Ptr) (v : BitVec 32) (q : Option Ptr)
    (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ ((up (pts p 8 q) ⋆ (up (pts (p.add 8) 4 v) ⋆ nodeRest I φ p)) ⋆ vtR vtp fns.toList))
      (mem_Allocator_destroy__anon_a9add1f02861 ⟨ctx, vtp⟩ p)
      (fun _ => I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) :=
  destroy_spec ctx vtp fns I e φ p v q h

/-! ## `freeAll` -/

-- the rest of a node's grant is handed on whole (to `destroy_fields`)
attribute [local fsym_atom] nodeRest

/-- The body at the end of the list: it exits. -/
theorem freeAll_step_nil (R : FAssn) :
    CTriple R ((freeAll.loop5 ⟨ctx, vtp⟩).run ⟨none⟩) (fun r => ⟪r = (.br4, ⟨none⟩)⟫ ⋆ R) := by
  unfold freeAll.loop5
  fsym

set_option maxRecDepth 20000 in
/-- The body at a node: it reads `next` and gives the node back to the allocator. -/
theorem freeAll_step_cons (p : Ptr) (q : Option Ptr) (z : BitVec 32) (R : FAssn)
    (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (node I φ p z q ⋆ (vtR vtp fns.toList ⋆ R))) ((freeAll.loop5 ⟨ctx, vtp⟩).run ⟨some p⟩)
      (fun r => ⟪r = (.rep5, ⟨q⟩)⟫ ⋆ (I.own ⋆ (I.fee φ ⋆ (vtR vtp fns.toList ⋆ R)))) := by
  unfold freeAll.loop5 node Linked.node
  fsym [destroy_fields ctx vtp fns I e φ (h := h)]

/-- The invariant of `freeAll`'s loop over a list of `n` nodes: `p` is a list of granted nodes,
and the fees of the nodes freed so far are back. -/
def freeInv (n : Nat) (s : freeAllLocals) : FAssn :=
  I.own ⋆ ((FAssn.ex fun zs => ⟪zs.length ≤ n⟫ ⋆ (list I φ s.p zs ⋆ fees I φ (n - zs.length))) ⋆
    vtR vtp fns.toList)

/-- After `freeAll`'s loop over a list of `n` nodes: no node is left, the `n` fees are back. -/
def freePost (n : Nat) (r : freeAllExit × freeAllLocals) : FAssn :=
  ⟪r.1 = .br4⟫ ⋆ (I.own ⋆ (fees I φ n ⋆ vtR vtp fns.toList))

theorem freeAll_step (h : CAllocSpec (CVTable.env (env e) fns) ctx I) (n : Nat) (s : freeAllLocals) :
    CTriple (freeInv vtp fns I φ n s) ((freeAll.loop5 ⟨ctx, vtp⟩).run s)
      (fun r => if freeAll.again5 r.1 then freeInv vtp fns I φ n r.2 else freePost vtp fns I φ n r) := by
  obtain ⟨cu⟩ := s
  refine CTriple.pre (P := FAssn.ex fun zs => ⟪zs.length ≤ n⟫ ⋆
      (I.own ⋆ (list I φ cu zs ⋆ (vtR vtp fns.toList ⋆ fees I φ (n - zs.length)))))
    (CTriple.ex fun zs => CTriple.lift fun hz => ?_) fun _ h => ?_
  · cases zs with
    | nil =>
      refine CTriple.pre (P := ⟪cu = none⟫ ⋆ (I.own ⋆ (vtR vtp fns.toList ⋆ fees I φ n)))
        (CTriple.lift fun hcu => ?_) fun _ h => ?_
      · subst hcu
        refine (freeAll_step_nil ctx vtp _).post fun r _ h => ?_
        obtain ⟨hr, h'⟩ := Full.sep_lift.mp h
        subst hr
        exact Full.sep_lift.mpr ⟨rfl, ac_cast h' (by ac_rfl)⟩
      · have e : list I φ cu [] = ⟪cu = none⟫ := rfl
        rw [e, List.length_nil, Nat.sub_zero] at h
        exact ac_cast h (by ac_rfl)
    | cons z zs =>
      refine CTriple.pre (P := FAssn.ex fun p => FAssn.ex fun q => ⟪cu = some p⟫ ⋆
          (I.own ⋆ (node I φ p z q ⋆
            (vtR vtp fns.toList ⋆ (list I φ q zs ⋆ fees I φ (n - (z :: zs).length))))))
        (CTriple.ex fun p => CTriple.ex fun q => CTriple.lift fun hp => ?_) fun _ h => ?_
      · subst hp
        refine (freeAll_step_cons ctx vtp fns I e φ p q z _ h).post fun r _ h => ?_
        obtain ⟨hr, h'⟩ := Full.sep_lift.mp h
        subst hr
        simp only [freeAll.again5, ↓reduceIte, freeInv]
        simp only [List.length_cons] at hz h'
        -- the node's fee joins the fees freed so far
        have e : n - zs.length = (n - (zs.length + 1)) + 1 := by omega
        refine sep_mono_right (fun _ h => sep_ex.mpr ⟨zs, ?_⟩) h'
        rw [e, fees_succ]
        exact ac_cast (sep_lift.mpr ⟨by omega, h⟩ : (⟪zs.length ≤ n⟫ ⋆ _) _) (by ac_rfl)
      · obtain ⟨r₁, r₂, hd, rfl, h1, h2⟩ := h
        obtain ⟨p, q, hp, h2⟩ := list_cons h2
        exact ⟨p, q, Full.sep_lift.mpr ⟨hp, ⟨r₁, r₂, hd, rfl, h1, ac_cast h2 (by ac_rfl)⟩⟩⟩
  · obtain ⟨r₁, r₂, hd, rfl, h1, h2⟩ := h
    obtain ⟨zs, h2⟩ := sep_ex.mp h2
    obtain ⟨hz, h2⟩ := sep_lift.mp (Full.sep_assoc h2)
    have h3 : (I.own ⋆ ((list I φ cu zs ⋆ fees I φ (n - zs.length)) ⋆ vtR vtp fns.toList)) _ :=
      ⟨r₁, r₂, hd, rfl, h1, h2⟩
    exact ⟨zs, sep_lift.mpr ⟨hz, ac_cast h3 (by ac_rfl)⟩⟩

/-- The generated loop of `freeAll`, as a rule for `fsym`: from the list at `p`, it exits with
every node given back and every node's fee back. -/
theorem freeAll_loop {mb : Lean.Order.MonoBind (CM Tgt freeAllLocals)}
    (h : CAllocSpec (CVTable.env (env e) fns) ctx I) (hd : Option Ptr) (xs : List (BitVec 32))
    (s : freeAllLocals) (hp : s.p = hd) :
    CTriple (I.own ⋆ (list I φ hd xs ⋆ vtR vtp fns.toList))
      ((@Zig.loop (CM Tgt freeAllLocals) _ _ mb _ (freeAll.loop5 ⟨ctx, vtp⟩) freeAll.again5).run s)
      (fun r => FAssn.ex fun t : freeAllLocals => ⟪r = (.br4, t)⟫ ⋆
        (I.own ⋆ (fees I φ xs.length ⋆ vtR vtp fns.toList))) :=
  (CTriple.loop (freeInv vtp fns I φ xs.length) (freePost vtp fns I φ xs.length)
      (freeAll_step ctx vtp fns I e φ h xs.length) s).pre
    (fun _ h' => sep_mono_right (fun _ h' => sep_mono_left (fun _ h' =>
      ⟨xs, sep_lift.mpr ⟨Nat.le_refl _, by
        rw [Nat.sub_self, hp]; exact (Full.sep_emp (P := list I φ hd xs)).mpr h'⟩⟩) h') h')
    |>.post fun ⟨e', t⟩ _ h' => by
      obtain ⟨he, h'⟩ := sep_lift.mp h'
      exact ⟨t, sep_lift.mpr ⟨by simp only at he; rw [he], h'⟩⟩

/-- **`freeAll`** gives every node of the list back to the allocator: afterwards the caller owns
nothing of the list, and the fee of every node is back, for every allocator that meets the
contract. -/
theorem freeAll_spec (hd : Option Ptr) (xs : List (BitVec 32))
    (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (list I φ hd xs ⋆ vtR vtp fns.toList)) (freeAll ⟨ctx, vtp⟩ hd)
      (fun _ => I.own ⋆ (fees I φ xs.length ⋆ vtR vtp fns.toList)) := by
  unfold freeAll
  fsym [freeAll_loop ctx vtp fns I e φ h]

end Lists.Alloc
