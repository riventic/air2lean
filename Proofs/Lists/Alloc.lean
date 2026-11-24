import Proofs.Lists.AllocInv
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
`ZigLean/Sep/Full/Fields.lean`). The nodes and `destroy`'s contract (`destroy_fields`) are in
`Proofs/Lists/AllocNode.lean`. The generated code is walked by `fsym`; `freeAll`'s loop by its
generated invariant (`Proofs/Lists/AllocInv.lean`, `@[fsym_inv]`), which `air2lean-invgen` reads
off that contract: the nodes left are a list of granted nodes, the nodes passed a list of what
`destroy` leaves of each. The loop with its exact step count (`freeAll_exact`) is walked from the
generated credit-mode invariant of the same body (`freeAll.loop5.credits.inv`, the second
registration of `@[fsym_inv]`, which `fsym` takes in a walk that pays its steps with credits).
These are `CTriple`s (partial correctness, no
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
  simp [nodeBytes, writeBytes_eq, Array.extract_append, h8, h4, e]

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

end Views

/-! ## The allocator -/

variable [Ext]

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

-- the 0.15.2 and 0.16.0 translations of `create` take longer to walk (`Proofs/Lists/Append.lean`);
-- budgets measured over those translations (`perf-budgets.py heartbeats record … --tree`)
set_option maxHeartbeats 400000 in
theorem push_grant (next : Option Ptr) (v : BitVec 32) (hfit : I.fits (16 : BitVec 64).toNat 3)
    (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList) ⋆ plain) (push ⟨ctx, vtp⟩ next v)
      (fun r => I.own ⋆ (pushResult I φ next v r ⋆ vtR vtp fns.toList) ⋆ plain) := by
  fsym [create_spec ctx vtp fns I e φ hfit h]

set_option maxHeartbeats 1000000 in
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

/-! ## `freeAll` -/

omit [Ext] in
/-- What the allocator told of `k` freed nodes (`FAllocInv.freed` of each), the first at `hd`,
the next pointer of the last `tl`. -/
def freedSeg : Option Ptr → Option Ptr → Nat → FAssn
  | hd, tl, 0 => ⟪hd = tl⟫
  | hd, tl, k + 1 => FAssn.ex fun p => FAssn.ex fun q =>
      ⟪hd = some p⟫ ⋆ (I.freed p ⋆ freedSeg q tl k)

omit [Ext] in
/-- One more freed node at the end of a segment. -/
theorem freedSeg_snoc {p : Ptr} (q : Option Ptr) :
    ∀ {hd : Option Ptr} (k : Nat) {r : Res},
      (freedSeg I hd (some p) k ⋆ I.freed p) r → freedSeg I hd q (k + 1) r
  | _, 0, _, h => by
    obtain ⟨hp, h⟩ := sep_lift.mp h
    exact ⟨p, q, sep_lift.mpr ⟨hp, sep_comm (Full.sep_lift.mpr ⟨rfl, h⟩)⟩⟩
  | _, k + 1, _, h => by
    obtain ⟨p', h⟩ := sep_ex.mp h
    obtain ⟨q', h⟩ := sep_ex.mp h
    obtain ⟨hp, h⟩ := sep_lift.mp (sep_assoc h)
    exact ⟨p', q', sep_lift.mpr ⟨hp, sep_mono_right (fun _ h => freedSeg_snoc q k h) (sep_assoc h)⟩⟩

omit [Ext] in
/-- The nodes that `freeAll`'s loop has passed (`freeAll.loop5.done`, what `destroy`'s contract
leaves of each: the generated invariant's list of them, `Proofs/Lists/AllocInv.lean`) are the
fee of every node and what the allocator told of the nodes. -/
theorem fees_freed_of_done :
    ∀ (vs : List (BitVec 32)) {hd tl : Option Ptr} {r : Res},
      listSegRev (freeAll.loop5.done I φ) hd tl vs r →
        (fees I φ vs.length ⋆ freedSeg I hd tl vs.length) r
  | [], hd, tl, _, h => sep_comm ((Full.sep_emp (P := freedSeg I hd tl 0)).mpr h)
  | _ :: vs, hd, tl, _, h => by
    obtain ⟨p, h⟩ := h
    have h : ((I.fee φ ⋆ I.freed p) ⋆ listSegRev (freeAll.loop5.done I φ) hd (some p) vs) _ := h
    have h := sep_mono_right (fun _ h => fees_freed_of_done vs h) h
    rw [List.length_cons, fees_succ]
    have h : ((I.fee φ ⋆ fees I φ vs.length) ⋆ (freedSeg I hd (some p) vs.length ⋆ I.freed p)) _ :=
      ac_cast h (by ac_rfl)
    exact sep_mono_right (fun _ h => freedSeg_snoc I tl _ h) h

set_option maxRecDepth 20000 in
/-- **`freeAll` hands every node of the list to `destroy`**: what is left of the list is what
`destroy`'s contract (`destroy_fields`) leaves of each node (the segment of them told from its
end, `listSegRev`). The loop is walked by `fsym` from its generated invariant
(`Proofs/Lists/AllocInv.lean`, `air2lean-invgen`'s list walk with a call, read off that
contract): no step or loop lemma. -/
theorem freeAll_done (hd : Option Ptr) (xs : List (BitVec 32))
    (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (list I φ hd xs ⋆ vtR vtp fns.toList) ⋆ plain) (freeAll ⟨ctx, vtp⟩ hd)
      (fun _ => listSegRev (freeAll.loop5.done I φ) hd none xs.reverse ⋆ I.own ⋆
        vtR vtp fns.toList ⋆ plain) := by
  unfold freeAll
  fsym [destroy_fields ctx vtp fns I e φ (h := h)]

/-- **`freeAll`, with what the allocator told of the nodes** (`FAllocInv.freed` of each, from
`hd`): every node given back, the fee of every node back. A client of the contract alone forgets
the last part (`freeAll_spec`); a client that knows the allocator reads it. -/
theorem freeAll_freed (hd : Option Ptr) (xs : List (BitVec 32))
    (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (list I φ hd xs ⋆ vtR vtp fns.toList) ⋆ plain) (freeAll ⟨ctx, vtp⟩ hd)
      (fun _ => (I.own ⋆ ((fees I φ xs.length ⋆ vtR vtp fns.toList) ⋆
        freedSeg I hd none xs.length)) ⋆ plain) :=
  (freeAll_done ctx vtp fns I e φ hd xs h).post fun _ _ h' => by
    have h' := sep_mono_left (fun _ h => fees_freed_of_done I φ xs.reverse h) h'
    rw [List.length_reverse] at h'
    exact ac_cast h' (by ac_rfl)

omit [Ext] in
/-- What the allocator told is knowledge only (`FAllocInv.freed_pers`): a contract client forgets
it (`Persistent.drop`). -/
theorem freedSeg_pers : ∀ (hd tl : Option Ptr) (k : Nat), Persistent (freedSeg I hd tl k)
  | _, _, 0 => Persistent.lift
  | _, tl, k + 1 => Persistent.ex fun _ => Persistent.ex fun q => Persistent.sep Persistent.lift
      (Persistent.sep (fun r h => I.freed_pers _ r h) (freedSeg_pers q tl k))

/-- **`freeAll`** gives every node of the list back to the allocator: afterwards the caller owns
nothing of the list, and the fee of every node is back, for every allocator that meets the
contract. -/
theorem freeAll_spec (hd : Option Ptr) (xs : List (BitVec 32))
    (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (list I φ hd xs ⋆ vtR vtp fns.toList) ⋆ plain) (freeAll ⟨ctx, vtp⟩ hd)
      (fun _ => I.own ⋆ (fees I φ xs.length ⋆ vtR vtp fns.toList) ⋆ plain) :=
  (freeAll_freed ctx vtp fns I e φ hd xs h).eupd_post fun _ =>
    EUpd.trans (EUpd.of_imp fun _ h => ac_cast h (by ac_rfl))
      (freedSeg_pers I hd none xs.length).drop

/-! ## `freeAll` with its exact step count -/

set_option maxRecDepth 20000 in
/-- **`freeAll_done` with its exact step count**: the walk pays its steps with credits, so `fsym`
takes the loop's generated credit-mode invariant (`freeAll.loop5.credits.inv`,
`Proofs/Lists/AllocInv.lean`: the plain-mode one at the exact count of the body runs left) and
the counted loop rule `CTriple.loop_exact`: no step or loop lemma. -/
theorem freeAll_done_exact (hd : Option Ptr) (xs : List (BitVec 32))
    (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple ((I.own ⋆ (list I φ hd xs ⋆ vtR vtp fns.toList)) ⋆ credits (xs.length + 1))
      (freeAll ⟨ctx, vtp⟩ hd)
      (fun _ => listSegRev (freeAll.loop5.done I φ) hd none xs.reverse ⋆ I.own ⋆
        vtR vtp fns.toList ⋆ spent (xs.length + 1)) := by
  unfold freeAll
  fsym [destroy_fields ctx vtp fns I e φ (h := h)]

/-- **`freeAll` with its exact step count**: as `freeAll_freed`, paying `xs.length + 1` credits
(one per run of its loop's body: one per node and the final null test) and returning as many
receipts, for every allocator that meets the contract. The allocator's calls take none of them. -/
theorem freeAll_exact (hd : Option Ptr) (xs : List (BitVec 32))
    (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple ((I.own ⋆ (list I φ hd xs ⋆ vtR vtp fns.toList)) ⋆ credits (xs.length + 1))
      (freeAll ⟨ctx, vtp⟩ hd)
      (fun _ => (I.own ⋆ ((fees I φ xs.length ⋆ vtR vtp fns.toList) ⋆
        freedSeg I hd none xs.length)) ⋆ spent (xs.length + 1)) :=
  (freeAll_done_exact ctx vtp fns I e φ hd xs h).post fun _ _ h' => by
    have h' := sep_mono_left (fun _ h => fees_freed_of_done I φ xs.reverse h) h'
    rw [List.length_reverse] at h'
    exact ac_cast h' (by ac_rfl)

/-- **`freeAll` runs exactly `xs.length + 1` steps**: from a credit-free start `m` that holds the
allocator's state, the list and the vtable (`r`) and a frame `rF`, every run of `freeAll` read in
one thread (`soloRun`, `CTriple.toSolo`) that returns has run exactly `xs.length + 1` steps; the
live bytes of its final memory are the frame's and a part that holds the allocator's state, every
node's fee and the vtable, and nothing of the list. Whether it returns is the allocator's
business: the contract `CAllocSpec` is partial (engine-ledger row `callocspec-partial-step-count`). -/
theorem freeAll_steps (hd : Option Ptr) (xs : List (BitVec 32))
    (h : CAllocSpec (CVTable.env (env e) fns) ctx I) (fuel : Nat) {m : Mem} {r rF : Res}
    (hh : Holds m r rF) (hp : (I.own ⋆ (list I φ hd xs ⋆ vtR vtp fns.toList)) r) (hs : m.FSeq)
    (hc : CreditFree r rF) {v : Unit} {m' : Mem}
    (hr : (Sched.soloRun fuel (freeAll ⟨ctx, vtp⟩ hd)).run m = pure (v, m')) :
    m'.ticks = m.ticks + (xs.length + 1) ∧ ∃ r', FHeap.Disjoint r'.heap rF.heap ∧
      SMatch m' (r'.heap ∪ rF.heap) (r'.gh.add rF.gh).share ∧
      (I.own ⋆ ((fees I φ xs.length ⋆ vtR vtp fns.toList) ⋆ freedSeg I hd none xs.length)) r' ∧
      m'.FSeq :=
  ((freeAll_exact ctx vtp fns I e φ hd xs h).toSolo fuel).ticks_eq_post hh hp hs hc hr

end Lists.Alloc
