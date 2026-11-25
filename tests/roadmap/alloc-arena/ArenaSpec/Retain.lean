import AllocArena.ArenaLinux
import AllocArena.Core
import AllocArena.Reset
import ZigLean.Sep.Full.AutoAll

/-!
# `ArenaSpec`: the child's tables and `reset`'s `loop78`

The module's allocators (`tables`), the child read back from the arena struct (`child_decode`),
`loop78` of `reset`'s retaining modes and `loop66`'s invariant and exit (`Inv66`, `Exit66`): what
the two heavy walks of `loop66`'s body need (`ArenaSpec/Loop66C0.lean`, `ArenaSpec/Loop66C1.lean`,
which build in parallel). `ArenaSpec.lean` imports them; its module doc describes the proofs.
-/

namespace AllocArena.ArenaSpec

open Zig Zig.Region Zig.Full Zig.Full.FAssn AllocArena.Core AllocArena.ArenaLinux

/-- The alignment argument of the generated entries, from its log2. -/
def al (k : Nat) : mem_Alignment := ⟨BitVec.ofNat 6 k⟩

/-- The module's allocators (`std.heap.page_allocator`, `ArenaAllocator`, `FixedBufferAllocator`):
the entries that an indirect call through the child's vtable can reach. -/
def tables : AllocTables Tgt where
  alloc := [(⟨some 3, 0⟩, fun a => heap_PageAllocator_alloc a.1 a.2.1 (al a.2.2.1) a.2.2.2),
    (⟨some 8, 0⟩, fun a => heap_ArenaAllocator_alloc a.1 a.2.1 (al a.2.2.1) a.2.2.2),
    (⟨some 12, 0⟩, fun a => ConcM.liftMem (heap_FixedBufferAllocator_alloc a.1 a.2.1 (al a.2.2.1) a.2.2.2))]
  resize := [(⟨some 4, 0⟩, fun a => ConcM.liftMem (heap_PageAllocator_resize a.1 a.2.1 (al a.2.2.1) a.2.2.2.1 a.2.2.2.2)),
    (⟨some 9, 0⟩, fun a => heap_ArenaAllocator_resize a.1 a.2.1 (al a.2.2.1) a.2.2.2.1 a.2.2.2.2),
    (⟨some 13, 0⟩, fun a => ConcM.liftMem (heap_FixedBufferAllocator_resize a.1 a.2.1 (al a.2.2.1) a.2.2.2.1 a.2.2.2.2))]
  remap := [(⟨some 5, 0⟩, fun a => ConcM.liftMem (heap_PageAllocator_remap a.1 a.2.1 (al a.2.2.1) a.2.2.2.1 a.2.2.2.2)),
    (⟨some 10, 0⟩, fun a => heap_ArenaAllocator_remap a.1 a.2.1 (al a.2.2.1) a.2.2.2.1 a.2.2.2.2),
    (⟨some 14, 0⟩, fun a => ConcM.liftMem (heap_FixedBufferAllocator_remap a.1 a.2.1 (al a.2.2.1) a.2.2.2.1 a.2.2.2.2))]
  free := [(⟨some 6, 0⟩, fun a => ConcM.liftMem (heap_PageAllocator_free a.1 a.2.1 (al a.2.2.1) a.2.2.2)),
    (⟨some 11, 0⟩, fun a => heap_ArenaAllocator_free a.1 a.2.1 (al a.2.2.1) a.2.2.2),
    (⟨some 15, 0⟩, fun a => ConcM.liftMem (heap_FixedBufferAllocator_free a.1 a.2.1 (al a.2.2.1) a.2.2.2))]

/-- The child allocator read back from its bytes in the arena struct. -/
theorem child_decode (CI : Child) : Enc.decode CI.bytes = pure (⟨CI.cctx, CI.vtp⟩ : mem_Allocator) := by
  simp only [Enc.decode, Child.decodeAt0, Child.decodeAt8]; rfl

/-! ## `reset`'s retaining modes

`retain_capacity` and `retain_with_limit` sum each list's buffer sizes (`count_free`), then
`loop66` handles the two lists in turn: `loop78` gives every node of a list back to the child but
the last one, which the arena keeps (`Last`, `AllocArena/Reset.lean`), resized to the list's share
of the limit (`std.mem.alignBackward(24 + limit, 2)` bytes): given back if that is just the header,
kept as it is if it has that size, else shrunk or grown in place by the child
(`CAllocSpec.resize_upTo`, the walk splitting on its released bytes' `if`), else replaced by a new node of that size
(`CAllocSpec.alloc_upTo`, the old one given back; the new node's header words are stored over the
granted bytes: `region_storePacked_wpts`, `region_store_wpts`, `region_storeAll`), else kept as
it is (the result `ok` false). Each kept node is a whole node with `end_index` `0` and no next node
(`Kept`); the walk folds it from the node's parts, whatever path made it. The child takes every
request up to `2 ^ 63` bytes (`FAllocInv.FitsUpTo`, the hypothesis `hfit`): a kept node holds at
most a list's buffer sizes and a header (`count_free`). The kept nodes are the arena at the next
epoch (`own_kept`). -/

section Retain

variable (CI : Child) (h : CAllocSpec (CVTable.dispatch tables CI.fns) CI.cctx CI.toFAllocInv)
  (ctx : Ptr) (Ac Sc : Nat) (Kc : BlockKind)

/-- `loop78`'s invariant: the head word `p`, and the list from `it`; `it` is empty only if the
list was. -/
def Inv78 (p : Ptr) (x0 : Option Ptr) (s : heap_ArenaAllocator_resetLocals) : FAssn :=
  FAssn.ex fun ns : List NodeV => ⟪s.it = none → x0 = none⟫ ⋆
    (aptsE p x0 ⋆ Chain CI true (ns.map NodeV.full) s.it ⋆ FreeCl CI ns ⋆ Cm CI ctx Ac Sc Kc ⋆ plain)

/-- `loop78`'s exits: the list's last node, or an empty list. -/
def Exit78 (p : Ptr) (x0 : Option Ptr) :
    heap_ArenaAllocator_resetExit × heap_ArenaAllocator_resetLocals → FAssn
  | (.br77 N, _) => aptsE p x0 ⋆ Last CI N ⋆ Cm CI ctx Ac Sc Kc ⋆ plain
  | (.br68, _) => ⟪x0 = none⟫ ⋆ (aptsE p x0 ⋆ Cm CI ctx Ac Sc Kc ⋆ plain)
  | _ => ⟪False⟫

attribute [local fsym_atom] Chain FreeCl in
include h in
/-- One run of `loop78`'s body: the list's last node is kept (`br77`); any other node goes back to
the child (`free` through the vtable; the refund joins the reservoir). The list's cases are split
before `fsym`: its first node, and the rest as a chain (`fsym_atom`), which the invariant names
again at the next node (ledger #chain-case-unfold). -/
theorem loop78_step (p : Ptr) (x0 : Option Ptr) (s : heap_ArenaAllocator_resetLocals) :
    CTriple (Tgt := Tgt) (Inv78 CI ctx Ac Sc Kc p x0 s) ((heap_ArenaAllocator_reset.loop78 ctx).run s)
      (fun r => if heap_ArenaAllocator_reset.again78 r.1 then Inv78 CI ctx Ac Sc Kc p x0 r.2
        else Exit78 CI ctx Ac Sc Kc p x0 r) := by
  have hd := child_decode CI
  refine CTriple.ex fun ns => ?_
  rcases s with ⟨ok, l, it⟩
  unfold heap_ArenaAllocator_reset.loop78
  rcases ns with _ | ⟨nd, _ | ⟨nd2, ns⟩⟩ <;> cases it
  · simp only [List.map_nil, Chain, FreeCl]
    fsym
  · simp only [List.map_nil, Chain]
    fsym
  · simp only [List.map_cons, List.map_nil, Chain]
    fsym
  · rw [List.map_cons, List.map_nil, chain_one, FreeCl.eq_2, FreeCl.eq_1]
    fsym [CAllocSpec.free' h, Child.cown_refund]
  · simp only [List.map_cons, Chain]
    fsym
  · rw [chain_full_cons2, FreeCl.eq_2]
    fsym [CAllocSpec.free' h, Child.cown_refund]

include h in
/-- **`loop78`** gives every node of a list back to the child but the last (`CTriple.loop`,
`Inv78`), from the list's head word `p` holding `x` and the list of whole nodes from `x`. A rule
from the loop's start state, where the invariant's implication holds (ledger #59). -/
theorem loop78_ct (p : Ptr) (x : Option Ptr) (ok : Bool) (l : BitVec 64) :
    CTriple (Tgt := Tgt) (aptsE p x ⋆ FreeList CI x ⋆ Cm CI ctx Ac Sc Kc ⋆ plain)
      ((Zig.loop (heap_ArenaAllocator_reset.loop78 ctx) heap_ArenaAllocator_reset.again78).run ⟨ok, l, x⟩)
      (fun r => FAssn.ex fun e => FAssn.ex fun s' => ⟪r = (e, s')⟫ ⋆ Exit78 CI ctx Ac Sc Kc p x (e, s')) := by
  refine CTriple.pre ((CTriple.loop (Inv78 CI ctx Ac Sc Kc p x) (Exit78 CI ctx Ac Sc Kc p x)
    (loop78_step CI h ctx Ac Sc Kc p x) ⟨ok, l, x⟩).post fun r r' h =>
      ⟨r.1, r.2, sep_lift.mpr ⟨rfl, h⟩⟩) fun r hr => ?_
  obtain ⟨r₁, r₂, hd', he, h1, h2⟩ := hr
  obtain ⟨ns, h2⟩ := sep_ex.mp h2
  refine ⟨ns, sep_lift.mpr ⟨id, ?_⟩⟩
  show (aptsE p x ⋆ Chain CI true (ns.map NodeV.full) x ⋆ FreeCl CI ns ⋆ Cm CI ctx Ac Sc Kc ⋆ plain) r
  have h3 : (aptsE p x ⋆ ((Chain CI true (ns.map NodeV.full) x ⋆ FreeCl CI ns) ⋆
    Cm CI ctx Ac Sc Kc ⋆ plain)) r := ⟨r₁, r₂, hd', he, h1, h2⟩
  exact of_eq (by ac_rfl) h3

/-- `loop66`'s invariant: the lists before index `local55` are handled (`Lst`). -/
def Inv66 (pu pf : Ptr) (xu xf : Option Ptr) (s : heap_ArenaAllocator_resetLocals) : FAssn :=
  ⟪s.local55.toNat ≤ 2⟫ ⋆ (Lst CI (decide (0 < s.local55.toNat)) pu xu ⋆
    Lst CI (decide (1 < s.local55.toNat)) pf xf ⋆ Cm CI ctx Ac Sc Kc ⋆ plain)

/-- `loop66`'s exit: both lists handled. -/
def Exit66 (pu pf : Ptr) (r : heap_ArenaAllocator_resetExit × heap_ArenaAllocator_resetLocals) : FAssn :=
  FAssn.ex fun s' => ⟪r = (.br65, s')⟫ ⋆ (KeptAt CI pu ⋆ KeptAt CI pf ⋆ Cm CI ctx Ac Sc Kc ⋆ plain)

end Retain

end AllocArena.ArenaSpec
