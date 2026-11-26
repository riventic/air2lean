import ArenaSpecMacos.Entries
import ArenaSpecMacos.Loop66C0
import ArenaSpecMacos.Loop66C1

/-!
# The stock `ArenaAllocator` on aarch64-macos: `free`, `resize` and `remap` against `FAllocSpec`

The statements of `ArenaSpec.lean` for the aarch64-macos translation (`AllocArena/ArenaMacos.lean`),
proved as there (`fsym` with the updates of `AllocArena.Core`), and `deinit`,
`reset(.free_all)` and `reset`'s retaining modes walked by `fsym` as in `ArenaSpec.lean`. The
statements and walks repeat `ArenaSpec.lean`'s over this module's own types and code (ledger
#per-translation-walks). The modules are split as `ArenaSpec.lean`'s: the entries in
`ArenaSpecMacos/Entries.lean`, `tables` and `loop78` in `ArenaSpecMacos/Retain.lean`, `loop66`'s
body per list in `ArenaSpecMacos/Loop66C0.lean` and `ArenaSpecMacos/Loop66C1.lean`.
-/

namespace AllocArena.ArenaSpecMacos

open Zig Zig.Region Zig.Full Zig.Full.FAssn AllocArena.Core AllocArena.ArenaMacos

/-! ## `deinit` and `reset` (as in `ArenaSpec.lean`) -/

/-- `countListCapacity`'s loop, by induction on the list (`ArenaSpec.count_loop`). -/
theorem count_loop (CI : Child) (free : Bool) :
    ∀ (ns : List NodeV) (it : Option Ptr) (c : BitVec 64),
      FTTotalTriple (⟪c.toNat + capOf ns < 2 ^ 64⟫ ⋆ (Chain CI free ns it ⋆ plain))
        ((Zig.loop heap_ArenaAllocator_countListCapacity.loop6
          heap_ArenaAllocator_countListCapacity.again6).run ⟨c, it⟩)
        (fun r => FAssn.ex fun c' : BitVec 64 =>
          ⟪r = (.br5, ⟨c', none⟩) ∧ c'.toNat = c.toNat + capOf ns⟫ ⋆ (Chain CI free ns it ⋆ plain))
  | [], none, c => by
    rw [Full.loop_run]
    conv in StateT.run heap_ArenaAllocator_countListCapacity.loop6 _ =>
      rw [heap_ArenaAllocator_countListCapacity.loop6]
    fsym [heap_ArenaAllocator_countListCapacity.again6.eq_def]
  | nd :: ns, some N, c => by
    rw [Full.loop_run]
    conv in StateT.run heap_ArenaAllocator_countListCapacity.loop6 _ =>
      rw [heap_ArenaAllocator_countListCapacity.loop6]
    fsym [heap_ArenaAllocator_countListCapacity.again6.eq_def, count_loop CI free]
  | [], some _, _ | _ :: _, none, _ => by
    rw [Full.loop_run]
    conv in StateT.run heap_ArenaAllocator_countListCapacity.loop6 _ =>
      rw [heap_ArenaAllocator_countListCapacity.loop6]
    fsym

/-- **`countListCapacity`** of a list of whole nodes (`ArenaSpec.count_spec`). -/
theorem count_spec (CI : Child) (ns : List NodeV) (x : Option Ptr) :
    FTTotalTriple (Chain CI true ns x ⋆ plain) (heap_ArenaAllocator_countListCapacity x)
      (fun c => ⟪c.toNat = capOf ns ∧ capOf ns + 24 ≤ 2 ^ 63⟫ ⋆ (Chain CI true ns x ⋆ plain)) :=
  FTTotalTriple.eupd (chain_capOf_le CI ns x).sepL.eupd <| FTTotalTriple.lift fun _ => by
    unfold heap_ArenaAllocator_countListCapacity
    fsym [count_loop CI true]

/-- **`countListCapacity`** of the free list (`ArenaSpec.count_free`). -/
theorem count_free (CI : Child) (x : Option Ptr) :
    FTTotalTriple (FreeList CI x ⋆ plain) (heap_ArenaAllocator_countListCapacity x)
      (fun c => ⟪c.toNat + 24 ≤ 2 ^ 63⟫ ⋆ (FreeList CI x ⋆ plain)) := by
  fsym [count_spec CI]

section Deinit

variable (CI : Child) (h : CAllocSpec (CVTable.dispatch tables CI.fns) CI.cctx CI.toFAllocInv)

def Inv19 (l : BitVec 64) (s : heap_ArenaAllocator_deinitLocals) : FAssn :=
  FAssn.ex fun ns : List NodeV => ⟪s.local1 = l⟫ ⋆
    (Chain CI true (ns.map NodeV.full) s.it ⋆ FreeCl CI ns ⋆ (CI.cown ⋆ vtR CI.vtp CI.fns.toList ⋆ plain))

def Exit19 (l : BitVec 64) (r : heap_ArenaAllocator_deinitExit × heap_ArenaAllocator_deinitLocals) :
    FAssn :=
  ⟪r = (.br18, ⟨l, none⟩)⟫ ⋆ (CI.cown ⋆ vtR CI.vtp CI.fns.toList ⋆ plain)

include h in
theorem loop19_step (st : heap_ArenaAllocator_State) (l : BitVec 64) (s : heap_ArenaAllocator_deinitLocals) :
    CTriple (Tgt := Tgt) (Inv19 CI l s) ((heap_ArenaAllocator_deinit.loop19 ⟨⟨CI.cctx, CI.vtp⟩, st⟩).run s)
      (fun r => if heap_ArenaAllocator_deinit.again19 r.1 then Inv19 CI l r.2 else Exit19 CI l r) := by
  refine CTriple.ex fun ns => ?_
  rcases s with ⟨l', it⟩
  unfold heap_ArenaAllocator_deinit.loop19
  cases ns <;> cases it <;> simp only [List.map_cons, List.map_nil] <;>
    fsym [CAllocSpec.free' h, Child.cown_refund]

include h in
theorem loop19_ct (st : heap_ArenaAllocator_State) (l : BitVec 64) (s : heap_ArenaAllocator_deinitLocals) :
    CTriple (Tgt := Tgt) (Inv19 CI l s)
      ((Zig.loop (heap_ArenaAllocator_deinit.loop19 ⟨⟨CI.cctx, CI.vtp⟩, st⟩)
        heap_ArenaAllocator_deinit.again19).run s)
      (Exit19 CI l) :=
  CTriple.loop (Inv19 CI l) _ (loop19_step CI h st l) s

def Lists9 (used fl : Option Ptr) (k : BitVec 64) : FAssn :=
  if k = 0 then FreeList CI used ⋆ FreeList CI fl else if k = 1 then FreeList CI fl else emp

def Inv9 (used fl : Option Ptr) (s : heap_ArenaAllocator_deinitLocals) : FAssn :=
  ⟪s.local1.toNat ≤ 2⟫ ⋆ (Lists9 CI used fl s.local1 ⋆ (CI.cown ⋆ vtR CI.vtp CI.fns.toList ⋆ plain))

def Exit9 (r : heap_ArenaAllocator_deinitExit × heap_ArenaAllocator_deinitLocals) : FAssn :=
  FAssn.ex fun s' => ⟪r = (.br8, s')⟫ ⋆ (CI.cown ⋆ vtR CI.vtp CI.fns.toList ⋆ plain)

include h in
theorem loop9_step (used fl : Option Ptr) (s : heap_ArenaAllocator_deinitLocals) :
    CTriple (Tgt := Tgt) (Inv9 CI used fl s)
      ((heap_ArenaAllocator_deinit.loop9 ⟨⟨CI.cctx, CI.vtp⟩, ⟨used, fl⟩⟩ #v[used, fl]).run s)
      (fun r => if heap_ArenaAllocator_deinit.again9 r.1 then Inv9 CI used fl r.2 else Exit9 CI r) := by
  rcases s with ⟨l, it⟩
  unfold heap_ArenaAllocator_deinit.loop9
  obtain rfl | rfl | hl : l = 0 ∨ l = 1 ∨ 2 ≤ l.toNat := by bv_omega
  all_goals fsym [loop19_ct CI h]

include h in
theorem loop9_ct (used fl : Option Ptr) (s : heap_ArenaAllocator_deinitLocals) :
    CTriple (Tgt := Tgt) (Inv9 CI used fl s)
      ((Zig.loop (heap_ArenaAllocator_deinit.loop9 ⟨⟨CI.cctx, CI.vtp⟩, ⟨used, fl⟩⟩ #v[used, fl])
        heap_ArenaAllocator_deinit.again9).run s)
      (Exit9 CI) :=
  CTriple.loop (Inv9 CI used fl) _ (loop9_step CI h used fl) s

include h in
/-- **`deinit` gives every node of both lists back to the child.** -/
theorem deinit_ct (used fl : Option Ptr) :
    CTriple (Tgt := Tgt) (FreeList CI used ⋆ FreeList CI fl ⋆ (CI.cown ⋆ vtR CI.vtp CI.fns.toList ⋆ plain))
      (heap_ArenaAllocator_deinit ⟨⟨CI.cctx, CI.vtp⟩, ⟨used, fl⟩⟩)
      (fun _ => CI.cown ⋆ vtR CI.vtp CI.fns.toList ⋆ plain) := by
  unfold heap_ArenaAllocator_deinit
  fsym [loop9_ct CI h]

end Deinit

/-! ## `reset`'s retaining modes (as in `ArenaSpec.lean`) -/

section Retain

variable (CI : Child) (h : CAllocSpec (CVTable.dispatch tables CI.fns) CI.cctx CI.toFAllocInv)
  (ctx : Ptr) (Ac Sc : Nat) (Kc : BlockKind)

attribute [local fsym_facts] MemFacts.region_end

include h in
/-- `loop66`'s body for every list index (`ArenaSpec.loop66_step`). -/
theorem loop66_step (hfit : CI.FitsUpTo (2 ^ 63) 3) (pu pf : Ptr) (xu xf : Option Ptr)
    (v0 v1 : BitVec 64) (hv0 : v0.toNat + 24 ≤ 2 ^ 63) (hv1 : v1.toNat + 24 ≤ 2 ^ 63)
    (s : heap_ArenaAllocator_resetLocals) :
    CTriple (Tgt := Tgt) (Inv66 CI ctx Ac Sc Kc pu pf xu xf s)
      ((heap_ArenaAllocator_reset.loop66 ctx #v[pu, pf] #v[v0, v1]).run s)
      (fun r => if heap_ArenaAllocator_reset.again66 r.1 then Inv66 CI ctx Ac Sc Kc pu pf xu xf r.2
        else Exit66 CI ctx Ac Sc Kc pu pf r) := by
  rcases s with ⟨ok, l, it⟩
  obtain rfl | rfl | hl : l = 0 ∨ l = 1 ∨ 2 ≤ l.toNat := by bv_omega
  · exact loop66_c0 CI h ctx Ac Sc Kc hfit pu pf xu xf v0 v1 hv0 ok it
  · exact loop66_c1 CI h ctx Ac Sc Kc hfit pu pf xu xf v0 v1 hv1 ok it
  · unfold heap_ArenaAllocator_reset.loop66
    fsym

include h in
/-- **`loop66`** handles both lists in turn (`ArenaSpec.loop66_ct`). -/
theorem loop66_ct (hfit : CI.FitsUpTo (2 ^ 63) 3) (pu pf : Ptr) (xu xf : Option Ptr)
    (v0 v1 : BitVec 64) (hv0 : v0.toNat + 24 ≤ 2 ^ 63) (hv1 : v1.toNat + 24 ≤ 2 ^ 63) (ok : Bool)
    (it : Option Ptr) :
    CTriple (Tgt := Tgt) (Inv66 CI ctx Ac Sc Kc pu pf xu xf ⟨ok, 0, it⟩)
      ((Zig.loop (heap_ArenaAllocator_reset.loop66 ctx #v[pu, pf] #v[v0, v1])
        heap_ArenaAllocator_reset.again66).run ⟨ok, 0, it⟩)
      (Exit66 CI ctx Ac Sc Kc pu pf) :=
  CTriple.loop (Inv66 CI ctx Ac Sc Kc pu pf xu xf) _
    (loop66_step CI h ctx Ac Sc Kc hfit pu pf xu xf v0 v1 hv0 hv1) _

end Retain

section Reset

theorem reset_free_all_ct (CI : Child) (h : CAllocSpec (CVTable.dispatch tables CI.fns) CI.cctx CI.toFAllocInv)
    (γ e : Nat) (ctx : Ptr) :
    CTriple (Tgt := Tgt) (Released CI γ e ctx ⋆ plain) (heap_ArenaAllocator_reset ctx .free_all)
      (fun r => ⟪r = true⟫ ⋆ (own CI γ (e + 1) ctx ⋆ epTok γ (e + 1) Frac.one ⋆ plain)) := by
  have hd := child_decode CI
  unfold heap_ArenaAllocator_reset
  fsym [deinit_ct CI h, own_empty]

/-- **`reset(.free_all)` meets the reset contract.** -/
theorem reset_free_all_spec (CI : Child)
    (h : CAllocSpec (CVTable.dispatch tables CI.fns) CI.cctx CI.toFAllocInv) (γ e : Nat) (ctx : Ptr) :
    CTriple (Tgt := Tgt) ((inv CI γ e ctx).own ⋆ epTok γ e Frac.one ⋆ plain) (heap_ArenaAllocator_reset ctx .free_all)
      (fun r => ⟪r = true⟫ ⋆ ((inv CI γ (e + 1) ctx).own ⋆ epTok γ (e + 1) Frac.one ⋆ plain)) :=
  CTriple.eupd (EUpd.of_imp fun _ h => sep_assoc' h) <|
    CTriple.eupd (reset_release CI γ e ctx).frame (reset_free_all_ct CI h γ e ctx)

end Reset

section ResetRetain

variable (CI : Child) (h : CAllocSpec (CVTable.dispatch tables CI.fns) CI.cctx CI.toFAllocInv)
  (hfit : CI.FitsUpTo (2 ^ 63) 3)

attribute [local fsym_atom] FreeList in
include h hfit in
/-- `reset(.retain_capacity)` from the released arena (`ArenaSpec.reset_retain_capacity_ct`;
ledger #final-match-greedy). -/
theorem reset_retain_capacity_ct (γ e : Nat) (ctx : Ptr) :
    CTriple (Tgt := Tgt) (Released CI γ e ctx ⋆ plain) (heap_ArenaAllocator_reset ctx .retain_capacity)
      (fun _ => own CI γ (e + 1) ctx ⋆ epTok γ (e + 1) Frac.one ⋆ plain) := by
  have hd := child_decode CI
  unfold heap_ArenaAllocator_reset
  fsym [count_free CI, loop66_ct CI h ctx, own_kept]

attribute [local fsym_atom] FreeList in
include h hfit in
/-- `reset(.retain_with_limit l)` from the released arena
(`ArenaSpec.reset_retain_with_limit_ct`). -/
theorem reset_retain_with_limit_ct (γ e : Nat) (ctx : Ptr) (l : BitVec 64) :
    CTriple (Tgt := Tgt) (Released CI γ e ctx ⋆ plain) (heap_ArenaAllocator_reset ctx (.retain_with_limit l))
      (fun _ => own CI γ (e + 1) ctx ⋆ epTok γ (e + 1) Frac.one ⋆ plain) := by
  have hd := child_decode CI
  unfold heap_ArenaAllocator_reset
  fsym [count_free CI, loop66_ct CI h ctx, own_kept, deinit_ct CI h, own_empty]

include h hfit in
/-- **`reset(.retain_capacity)` meets the reset contract** (`ArenaSpec.reset_retain_capacity_spec`). -/
theorem reset_retain_capacity_spec (γ e : Nat) (ctx : Ptr) :
    CTriple (Tgt := Tgt) ((inv CI γ e ctx).own ⋆ epTok γ e Frac.one ⋆ plain)
      (heap_ArenaAllocator_reset ctx .retain_capacity)
      (fun _ => (inv CI γ (e + 1) ctx).own ⋆ epTok γ (e + 1) Frac.one ⋆ plain) :=
  CTriple.eupd (EUpd.of_imp fun _ h => sep_assoc' h) <|
    CTriple.eupd (reset_release CI γ e ctx).frame (reset_retain_capacity_ct CI h hfit γ e ctx)

include h hfit in
/-- **`reset(.retain_with_limit l)` meets the reset contract**
(`ArenaSpec.reset_retain_with_limit_spec`). -/
theorem reset_retain_with_limit_spec (γ e : Nat) (ctx : Ptr) (l : BitVec 64) :
    CTriple (Tgt := Tgt) ((inv CI γ e ctx).own ⋆ epTok γ e Frac.one ⋆ plain)
      (heap_ArenaAllocator_reset ctx (.retain_with_limit l))
      (fun _ => (inv CI γ (e + 1) ctx).own ⋆ epTok γ (e + 1) Frac.one ⋆ plain) :=
  CTriple.eupd (EUpd.of_imp fun _ h => sep_assoc' h) <|
    CTriple.eupd (reset_release CI γ e ctx).frame (reset_retain_with_limit_ct CI h hfit γ e ctx l)

end ResetRetain

end AllocArena.ArenaSpecMacos

#print axioms AllocArena.ArenaSpecMacos.free_spec
#print axioms AllocArena.ArenaSpecMacos.resize_spec
#print axioms AllocArena.ArenaSpecMacos.remap_spec
#print axioms AllocArena.ArenaSpecMacos.deinit_ct
#print axioms AllocArena.ArenaSpecMacos.reset_free_all_spec
#print axioms AllocArena.ArenaSpecMacos.count_spec
#print axioms AllocArena.ArenaSpecMacos.reset_retain_capacity_spec
#print axioms AllocArena.ArenaSpecMacos.reset_retain_with_limit_spec
