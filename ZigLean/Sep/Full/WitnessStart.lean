import ZigLean.Sep.Full.Witness
import ZigLean.Sep.Full.Init
import ZigLean.Sep.Full.Claims
import ZigLean.Sep.Full.AtomicPtr

/-!
# Admissible inputs built from the start memory (`docs/claim-strength.md` §Witnesses)

A non-vacuity witness of a full-state claim shows its precondition `P` in some `Mem.FSeq` memory
(`FAdmit P`). A precondition over an allocator's invariant holds ghost state that only updates
create: shares of a block's extent lent out of its authority (`EUpd.lend`), byte-range claims
(`bclaim`), the persistent vtable (`vtR_intro`). Such a precondition is shown admissible in the
memory at program start (`FAdmit.init_claims`) and carried there by the updates that create its
ghost state, which change the resources and not the memory. Each closure lemma is proved once on
`FAdmit.At m P` (`m` holds `P`, the base of `FAdmit` and `FAdmit.Start`), and the two
admissibility predicates inherit it:

* `eupd`: an update keeps admissibility;
* `frame`: a part of an admissible input is one (the rest joins the frame);
* `ex`: an admissible existential has an admissible instance (`sep_ex_eq_right` with
  `sep_ex_eq` moves a start resource's existentials outside);
* `FAdmit.init_claims`: the globals at program start (`globals`, `FAdmit.init`) **with the claim
  on every global's bytes** (`gclaims`). Claims are created with their block
  (`FTriple.mintClaim`); no one holds a claim at program start, so the start resource can hold
  all of them (`Holds.addClaim`).
* `Holds.addGlobalClaims`: that induction over any unchanged memory and frame, preserving the
  original assertion; `initRes_holds_stack_claims` instantiates it at the actual stack-budget
  start, and `FTotalTriple.run_init_stack_claims` gives total adequacy there.
* `FAdmit.At.aptsE` makes a word's plain bytes its atomic points-to before the first atomic op
  (`Holds.retag`: no atomic location constrains a tag); a counterexample that the kernel runs
  from a given memory states its input with `FAdmit.At`.

The bound of owned bytes below `2 ^ 63` (the memory's live layout) is a facts lemma
(`MemFacts.bytesAt_bound`, `MemFacts.regionIn_bound` in `Full/Region`); a witness that needs it
makes it `local fsym_facts`, and `fsym_entail` adds it to the state's facts, e.g. for the region
view of a global's bytes.
-/

namespace Zig
namespace Witness

open Full FAssn

/-! ## In a given memory

`FAdmit.At m P` (`Full/Witness`) is the base: the closure lemmas are proved on it once, for the
memory they keep, and `FAdmit` and `FAdmit.Start` (below) inherit them with their condition on
the memory. -/

/-- **An update keeps the memory**: it replaces the resources. -/
theorem FAdmit.At.eupd {m : Mem} {P P' : FAssn} (h : FAdmit.At m P) (hs : m.FSeq) (hu : EUpd P P') :
    FAdmit.At m P' := by
  obtain ⟨r, rF, hh, hp⟩ := h
  obtain ⟨r', hh', hp'⟩ := hu m r rF hh hp hs
  exact ⟨r', rF, hh', hp'⟩

/-- **A part is held**: the other part joins the frame. -/
theorem FAdmit.At.frame {m : Mem} {P R : FAssn} (h : FAdmit.At m (P ⋆ R)) : FAdmit.At m P := by
  obtain ⟨r, rF, hh, ⟨r₁, r₂, hd, rfl, h1, -⟩⟩ := h
  exact ⟨r₁, _, Holds.split hd hh, h1⟩

/-- The left part joins the frame. -/
theorem FAdmit.At.dropL {m : Mem} {P R : FAssn} (h : FAdmit.At m (R ⋆ P)) : FAdmit.At m P :=
  (h.mono fun _ h => Full.sep_comm h).frame

/-- A held existential has a held instance. -/
theorem FAdmit.At.ex {m : Mem} {γ : Type} {P : γ → FAssn} (h : FAdmit.At m (FAssn.ex P)) :
    ∃ x, FAdmit.At m (P x) :=
  have ⟨r, rF, hh, ⟨x, h⟩⟩ := h
  ⟨x, r, rF, hh, h⟩

theorem FAdmit.At.lift {m : Mem} {φ : Prop} {P : FAssn} (h : FAdmit.At m (⟪φ⟫ ⋆ P)) :
    φ ∧ FAdmit.At m P :=
  have ⟨r, rF, hh, h⟩ := h
  ⟨(Full.sep_lift.mp h).1, r, rF, hh, (Full.sep_lift.mp h).2⟩

/-- An existential on the right of `⋆` scopes over both parts (`sep_ex_eq`, mirrored): with it
`simp` moves the existentials of a start resource (the globals' addresses) outside. -/
theorem _root_.Zig.Full.sep_ex_eq_right {γ : Type} (P : FAssn) (Q : γ → FAssn) :
    (P ⋆ FAssn.ex Q) = FAssn.ex fun x => P ⋆ Q x := by
  rw [Full.sep_comm_eq, sep_ex_eq]; congr; funext x; exact Full.sep_comm_eq _ _

/-- A `Result` that the kernel evaluates to `v` (a global's decoding, a run's value). -/
theorem result_eq {ε α : Type} [DecidableEq α] (r : Option (Except ε α)) {v : α}
    (h : (match r with | some (.ok w) => decide (w = v) | _ => false) = true) :
    r = some (.ok v) := by
  match r, h with
  | some (.ok w), h => simp only [decide_eq_true_eq] at h; subst h; rfl

/-! ## Admissible inputs -/

/-- **An update keeps admissibility**: it replaces the resources and keeps the memory. -/
theorem FAdmit.eupd {P P' : FAssn} (h : FAdmit P) (hu : EUpd P P') : FAdmit P' :=
  have ⟨m, hs, h⟩ := FAdmit.iff_at.mp h
  FAdmit.iff_at.mpr ⟨m, hs, h.eupd hs hu⟩

/-- **A part of an admissible input is admissible**: the other part joins the frame. -/
theorem FAdmit.frame {P R : FAssn} (h : FAdmit (P ⋆ R)) : FAdmit P :=
  have ⟨m, hs, h⟩ := FAdmit.iff_at.mp h
  FAdmit.iff_at.mpr ⟨m, hs, h.frame⟩

/-- An admissible existential has an admissible instance. -/
theorem FAdmit.ex {γ : Type} {P : γ → FAssn} (h : FAdmit (FAssn.ex P)) : ∃ x, FAdmit (P x) :=
  have ⟨m, hs, h⟩ := FAdmit.iff_at.mp h
  have ⟨x, h⟩ := h.ex
  ⟨x, FAdmit.iff_at.mpr ⟨m, hs, h⟩⟩

/-! ## Admissible at program start, for a thread

A concurrent claim (`CTriple`) is non-vacuous when its precondition holds in a thread's memory
that the thread owns (`CAdmit`, `FTTAdmit`). A memory with no recorded access is one (every heap
is the current thread's, `owns_of_footprint`), and the updates above keep the memory, so they keep
that too: `FAdmit.Start` is `FAdmit` in a memory with no recorded access, the memory at program
start (`FAdmit.Start.init_claims`), and gives `CAdmit` (`FAdmit.Start.cadmit`). -/

/-- An admissible input in a memory with no recorded access. -/
def FAdmit.Start (P : FAssn) : Prop := ∃ m : Mem, (m.FSeq ∧ m.footprint = #[]) ∧ FAdmit.At m P

theorem FAdmit.Start.toFAdmit {P : FAssn} (h : FAdmit.Start P) : FAdmit P :=
  have ⟨m, ⟨hs, _⟩, h⟩ := h
  FAdmit.iff_at.mpr ⟨m, hs, h⟩

/-- A thread's admissible input: the thread owns every heap of a memory with no recorded access. -/
theorem FAdmit.Start.cadmit {P : FAssn} (h : FAdmit.Start P) : CAdmit P :=
  have ⟨m, ⟨hs, hf⟩, r, rF, hh, hp⟩ := h
  CAdmit.of ⟨m, r, rF, hh, hp, hs.fconc, owns_of_footprint hf _ _, trivial⟩

theorem FAdmit.Start.eupd {P P' : FAssn} (h : FAdmit.Start P) (hu : EUpd P P') :
    FAdmit.Start P' :=
  have ⟨m, hm, h⟩ := h
  ⟨m, hm, h.eupd hm.1 hu⟩

theorem FAdmit.Start.frame {P R : FAssn} (h : FAdmit.Start (P ⋆ R)) : FAdmit.Start P :=
  have ⟨m, hm, h⟩ := h
  ⟨m, hm, h.frame⟩

theorem FAdmit.Start.ex {γ : Type} {P : γ → FAssn} (h : FAdmit.Start (FAssn.ex P)) :
    ∃ x, FAdmit.Start (P x) :=
  have ⟨m, hm, h⟩ := h
  have ⟨x, h⟩ := h.ex
  ⟨x, m, hm, h⟩

theorem FAdmit.Start.mono {P P' : FAssn} (h : FAdmit.Start P) (hp : ∀ r, P r → P' r) :
    FAdmit.Start P' :=
  have ⟨m, hm, h⟩ := h
  ⟨m, hm, h.mono hp⟩

/-- **A memory without atomic locations meets every tag constraint** (`TagSat`): a resource with
the cells of a held one, and any constraints, is held. -/
theorem _root_.Zig.Full.Holds.retag {m : Mem} {r r' rF : Res} (hh : Holds m r rF)
    (hsh : shapes m = []) (hc : ∀ l, (r'.heap l).map (·.cell) = (r.heap l).map (·.cell))
    (hk : r'.know = r.know) (hg : r'.gh = r.gh) : Holds m r' rF := by
  have hn : ∀ l, r'.heap l = none ↔ r.heap l = none := fun l => by
    have := hc l
    cases e' : r'.heap l <;> cases e : r.heap l <;> simp_all
  have hu : ∀ l, ((r'.heap ∪ rF.heap) l).map (·.cell.norm) =
      ((r.heap ∪ rF.heap) l).map (·.cell.norm) := fun l => by
    have := hc l
    simp only [FHeap.union_apply]
    cases e' : r'.heap l <;> cases e : r.heap l <;> simp_all
  refine ⟨fun l => ?_, ⟨fun l => by rw [hh.heap.1 l, hu], fun l fc _ => ?_⟩, hk ▸ hh.know,
    hh.knowF, hg ▸ hh.ghost⟩
  · rcases hh.disj l with e | e
    · exact .inl ((hn l).mpr e)
    · exact .inr e
  · rw [hsh]
    cases fc.atom with
    | none => trivial
    | some s => exact .inl rfl

/-- **An atomic word before the first atomic op** (e.g. a global at program start): in a memory
without atomic locations, owned plain bytes of an aligned word are its atomic points-to `aptsE`. -/
theorem FAdmit.At.aptsE {α : Type} [Enc α] {m : Mem} {R : FAssn} {p : Ptr} {A S : Nat}
    {K : BlockKind} {bs : Array Byte} {v : α} (h : FAdmit.At m (FAssn.up (bytesAt p A S K bs) ⋆ R))
    (hsh : shapes m = []) (hal : (A + p.off.toNat) % 8 = 0) (hK : K ≠ .constGlobal)
    (hsz : bs.size = 8) (hv : Enc.decode bs = pure v) : FAdmit.At m (Full.aptsE p v ⋆ R) := by
  obtain ⟨_, rF, hh, ⟨r₁, r₂, hd, rfl, ⟨⟨b, hpb, h0, hl⟩, hk1, hg1⟩, hR⟩⟩ := h
  -- the word's bytes, with the location `(p.off, 8)` as their constraint
  let r₁' : Res := ⟨fun l => (r₁.heap l).map fun fc => ⟨fc.cell, some (p.off.toNat, 8)⟩, r₁.know,
    r₁.gh⟩
  have hd' : FHeap.Disjoint r₁'.heap r₂.heap := fun l => by
    rcases hd l with e | e
    · exact .inl (by simp [r₁', e])
    · exact .inr e
  refine ⟨⟨r₁'.heap ∪ r₂.heap, r₁'.know.union r₂.know, r₁'.gh.add r₂.gh⟩, rF,
    Holds.retag hh hsh (fun l => ?_) rfl rfl, r₁', r₂, hd', rfl, ?_, hR⟩
  · simp only [FHeap.union_apply, r₁']
    cases r₁.heap l <;> simp
  · refine ⟨A, S, K, bs, hal, hK, hsz, hv, hk1, hg1, b, hpb, h0, fun l => ?_⟩
    have := hl l
    simp only [FHeap.erase] at this
    simp only [r₁']
    split
    · rename_i hc
      simp only [hc, and_self, ↓reduceIte] at this
      cases e : r₁.heap l with
      | none => rw [e] at this; cases this
      | some fc =>
        rw [e] at this
        simp only [Option.map_some] at this ⊢
        rw [Option.some.inj this]
    · rename_i hc
      simp only [hc, ↓reduceIte] at this
      cases e : r₁.heap l with
      | none => rfl
      | some fc => rw [e] at this; cases this

/-! ## Claims at program start -/

/-- **A claim on a block that no one claims can be added** (`GOk.addCl`, the step of
`FTriple.mintClaimOpt` without the program). -/
theorem _root_.Zig.Full.Holds.addClaim {m : Mem} {r rF : Res} {b : BlockId} {lo hi : Nat}
    (hh : Holds m r rF) (hr : ∀ x, r.gh.cl b x = ECell.unit) (hF : ∀ x, rF.gh.cl b x = ECell.unit)
    (hb : b < m.blocks.size) :
    Holds m ⟨r.heap ∪ FHeap.empty, r.know.union Know.none,
      r.gh.add (Ghost.atCl b (ECell.onRange lo hi (ECell.shareT none Frac.one 0)))⟩ rF :=
  ⟨by rw [FHeap.union_empty]; exact hh.disj, by rw [FHeap.union_empty]; exact hh.heap,
    by rw [Know.union_none]; exact hh.know, hh.knowF,
    GOk.addCl hh.ghost (fun y => by rw [hr y, hF y, ECell.add_unit]) hb
      (fun y ls hu => onRange_share_ok lo hi y ls hu) (fun y γ e k => onRange_share_tags lo hi y γ e k)⟩

/-- The claim on every byte of every global. -/
def gclaims (gs : List (Array Byte × Nat × BlockKind)) : FAssn :=
  sepN gs.length fun j => match gs[j]? with
    | some (bs, _, _) => bclaim j 0 bs.size
    | none => emp

/-- **Add the claims of existing blocks to the same memory and frame.** Neither the owned part
nor its frame may already claim one of the named blocks. The original assertion stays beside
the new claims; claims on other blocks are unrestricted. -/
theorem _root_.Zig.Full.Holds.addGlobalClaims {m : Mem} {r rF : Res} {P : FAssn}
    (hh : Holds m r rF) (gs : List (Array Byte × Nat × BlockKind)) (hp : P r)
    (hr : ∀ b x, b < gs.length → r.gh.cl b x = ECell.unit)
    (hF : ∀ b x, b < gs.length → rF.gh.cl b x = ECell.unit)
    (hb : gs.length ≤ m.blocks.size) :
    ∃ r', Holds m r' rF ∧ (P ⋆ gclaims gs) r' := by
  let f : Nat → FAssn := fun j => match gs[j]? with
    | some (bs, _, _) => bclaim j 0 bs.size
    | none => emp
  have key : ∀ n, n ≤ gs.length → ∃ r', Holds m r' rF ∧
      (P ⋆ sepN n f) r' ∧ ∀ b x, n ≤ b → b < gs.length → r'.gh.cl b x = ECell.unit := by
    intro n hn
    induction n with
    | zero => exact ⟨r, hh, Full.sep_emp.mpr hp, fun b x _ hbg => hr b x hbg⟩
    | succ n ih =>
      obtain ⟨r', hh', hp', hz⟩ := ih (by omega)
      have hgn : gs[n]? = some gs[n] := List.getElem?_eq_getElem (by omega)
      have hnb : n < m.blocks.size := Nat.lt_of_lt_of_le (by omega) hb
      refine ⟨_, hh'.addClaim (b := n) (lo := 0) (hi := (gs[n]'(by omega)).1.size)
        (fun x => hz n x (Nat.le_refl n) (by omega)) (fun x => hF n x (by omega)) hnb,
        ?_, fun b x hbn hbg => ?_⟩
      · have hc : f n ⟨FHeap.empty, Know.none,
            Ghost.atCl n (ECell.onRange 0 (gs[n]'(by omega)).1.size (ECell.shareT none Frac.one 0))⟩ := by
          simp only [f, hgn]; exact ⟨rfl, rfl, rfl⟩
        have hj : ((P ⋆ sepN n f) ⋆ f n) _ :=
          ⟨r', _, FHeap.disjoint_empty _, rfl, hp', hc⟩
        show (P ⋆ (f n ⋆ sepN n f)) _
        exact ac_cast hj (by ac_rfl)
      · simp only [Ghost.add_cl, hz b x (by omega) hbg, Ghost.atCl,
          show b ≠ n by omega, ↓reduceIte, ECell.add_unit]
  obtain ⟨r', hh', hp', -⟩ := key gs.length (Nat.le_refl _)
  exact ⟨r', hh', hp'⟩

theorem noCl_known (b : BlockId) (A : Nat) : NoCl (known b A) := by
  rintro _ ⟨-, -, hg⟩ b' x; rw [hg]; rfl

theorem noCl_sepN {n : Nat} {f : Nat → FAssn} (h : ∀ j, j < n → NoCl (f j)) : NoCl (sepN n f) := by
  induction n with
  | zero => exact noCl_emp
  | succ n ih => exact noCl_sep (h n (by omega)) (ih fun j hj => h j (by omega))

/-- The globals at program start hold no claim. -/
theorem noCl_globals (gs : List (Array Byte × Nat × BlockKind)) : NoCl (globals gs) := by
  refine noCl_sepN fun j _ => ?_
  split
  · refine noCl_ex fun _ => noCl_sep (noCl_lift _) (noCl_sep (noCl_up _) (noCl_sep (noCl_known _ _) ?_))
    unfold gext; split
    · exact noCl_bauth _ _ _ _
    · exact noCl_emp
  · exact noCl_emp

/-- **The globals at program start, with the claim on every global's bytes, are admissible**
(`FAdmit.init` with `gclaims`), under every placement, in the memory at program start, which has
no recorded access, in the plain mode (`plain`, `initRes_holds_plain`: the start memory has no
stack yet). -/
theorem FAdmit.Start.init_claims (σ : Placement) (gs : List (Array Byte × Nat × BlockKind))
    (h : Mem.GlobalsFit gs) (hK : ∀ g ∈ gs, g.2.2.mappedLo = 0) :
    FAdmit.Start ((globals gs ⋆ plain) ⋆ gclaims gs) := by
  obtain ⟨hh, hp⟩ := initRes_holds_plain σ gs hK
  obtain ⟨r, hh', hp'⟩ := hh.addGlobalClaims gs hp
    (fun b x _ => noCl_sep (noCl_globals gs) noCl_plain _ hp b x) (fun _ _ _ => rfl)
    (by simp [Mem.ofGlobals_size])
  exact ⟨_, ⟨Mem.init_fseq σ gs h, Mem.ofGlobals_footprint σ gs⟩, r, _, hh', hp'⟩

/-- **The real stack-budget start holds the globals and their claims.** The claims augment the
resources from `initRes_holds_stack`; the memory, budget and empty frame are unchanged. -/
theorem _root_.Zig.Full.initRes_holds_stack_claims (σ : Placement)
    (gs : List (Array Byte × Nat × BlockKind)) (hK : ∀ g ∈ gs, g.2.2.mappedLo = 0)
    (S : Nat) (hr : ((Mem.ofGlobals σ gs).reserveAt? 0 S).isSome) :
    ∃ r, Holds ((Mem.ofGlobals σ gs).withStack S) r ⟨FHeap.empty, Know.none, Ghost.unit⟩ ∧
      ((globals gs ⋆ stackStart S) ⋆ gclaims gs) r := by
  obtain ⟨hh, hp⟩ := initRes_holds_stack σ gs hK S hr
  refine hh.addGlobalClaims gs hp (fun b x _ => ?_) (fun _ _ _ => rfl) ?_
  · simp only [Ghost.add_cl, noCl_globals gs _ (initRes_holds σ gs hK).2 b x]
    simp [Ghost.stackStart, Ghost.cur, Ghost.ofAC, Ghost.unit]
  · unfold Mem.withStack
    split <;> simp [Mem.ofGlobals_size]

/-- **Total adequacy from the actual stack-budget start, with global claims.** The same-memory
augmentation above supplies the claims beside the stack-start resources. -/
theorem _root_.Zig.Full.FTotalTriple.run_init_stack_claims {α : Type} {c : MemM α}
    {Q : α → FAssn} (σ : Placement) (gs : List (Array Byte × Nat × BlockKind))
    (h : Mem.GlobalsFit gs) (hK : ∀ g ∈ gs, g.2.2.mappedLo = 0) (S : Nat)
    (hr : ((Mem.ofGlobals σ gs).reserveAt? 0 S).isSome)
    (ht : FTotalTriple ((globals gs ⋆ stackStart S) ⋆ gclaims gs) c Q) :
    ∃ v m' r', c.run ((Mem.ofGlobals σ gs).withStack S) = pure (v, m') ∧
      Holds m' r' ⟨FHeap.empty, Know.none, Ghost.unit⟩ ∧ Q v r' ∧ m'.FSeq := by
  obtain ⟨r, hh, hp⟩ := initRes_holds_stack_claims σ gs hK S hr
  exact ht.runs hh hp ((Mem.init_fseq σ gs h).withStack S)

/-- **The globals at program start, with their claims, are admissible** (`FAdmit.Start.init_claims`). -/
theorem FAdmit.init_claims (σ : Placement) (gs : List (Array Byte × Nat × BlockKind))
    (h : Mem.GlobalsFit gs) (hK : ∀ g ∈ gs, g.2.2.mappedLo = 0) :
    FAdmit (globals gs ⋆ gclaims gs) :=
  FAdmit.frame (R := plain) ((FAdmit.Start.init_claims σ gs h hK).toFAdmit.mono
    fun _ h => ac_cast h (by ac_rfl))

end Witness
end Zig
