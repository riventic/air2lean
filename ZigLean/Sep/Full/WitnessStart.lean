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

/-! ## Admission transported through an actual initialization run

The postcondition may depend on the initializer's returned pointers, values and ghost metadata.
These lemmas retain that result and its run equation at the supplied program start; they do not
choose a separate memory or a convenient member of the postcondition's family. The initializer
triple is an ordinary full-state proof, walked by `fsym`.
-/

theorem FAdmit.init_total {α : Type} {c : MemM α} {Q : α → FAssn}
    (σ : Placement) (gs : List (Array Byte × Nat × BlockKind))
    (h : Mem.GlobalsFit gs) (hK : ∀ g ∈ gs, g.2.2.mappedLo = 0)
    (ht : FTotalTriple (globals gs) c Q) :
    ∃ v m', c.run (Mem.ofGlobals σ gs) = pure (v, m') ∧ FAdmit (Q v) := by
  obtain ⟨hh, hp⟩ := initRes_holds σ gs hK
  exact ht.admit_run hh hp (Mem.init_fseq σ gs h)

theorem FAdmit.init_total_plain {α : Type} {c : MemM α} {Q : α → FAssn}
    (σ : Placement) (gs : List (Array Byte × Nat × BlockKind))
    (h : Mem.GlobalsFit gs) (hK : ∀ g ∈ gs, g.2.2.mappedLo = 0)
    (ht : FTotalTriple (globals gs ⋆ plain) c Q) :
    ∃ v m', c.run (Mem.ofGlobals σ gs) = pure (v, m') ∧ FAdmit (Q v) := by
  obtain ⟨hh, hp⟩ := initRes_holds_plain σ gs hK
  exact ht.admit_run hh hp (Mem.init_fseq σ gs h)

theorem FAdmit.init_total_stack {α : Type} {c : MemM α} {Q : α → FAssn}
    (σ : Placement) (gs : List (Array Byte × Nat × BlockKind))
    (h : Mem.GlobalsFit gs) (hK : ∀ g ∈ gs, g.2.2.mappedLo = 0) (S : Nat)
    (hr : ((Mem.ofGlobals σ gs).reserveAt? 0 S).isSome)
    (ht : FTotalTriple (globals gs ⋆ stackStart S) c Q) :
    ∃ v m', c.run ((Mem.ofGlobals σ gs).withStack S) = pure (v, m') ∧ FAdmit (Q v) := by
  obtain ⟨hh, hp⟩ := initRes_holds_stack σ gs hK S hr
  exact ht.admit_run hh hp ((Mem.init_fseq σ gs h).withStack S)

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

/-- At program start there are no atomic locations, so any tag constraints over the same bytes
hold. This establishes the initial atomic-word view without assuming an allocator invariant. -/
theorem _root_.Zig.Full.Holds.start_heap {m : Mem} {r rF : Res} (hh : Holds m r rF)
    {h : FHeap} (he : h.erase = r.heap.erase) (hs : shapes m = []) :
    Holds m {r with heap := h} rF := by
  exact Holds.retag hh hs (fun l => congrFun he l) rfl rfl

/-- A typed word already owned in a memory before its first atomic access has the atomic
view of those same bytes. The memory, pointer and value are retained; no seed memory is built. -/
theorem FAdmit.of_start_pts {α : Type} [Enc α] {m : Mem} {r rF : Res}
    {p : Ptr} {v : α} {R : FAssn} (hh : Holds m r rF)
    (hp : (FAssn.up (pts p 8 v) ⋆ R) r) (hs : m.FSeq) (hsh : shapes m = [])
    (hα : Enc.size α = 8) : FAdmit (aptsE p v) := by
  obtain ⟨r₁, r₂, hd, rfl, hp, hR⟩ := hp
  obtain ⟨⟨A, S, K, bs, hal, hsz, hv, hb, hK⟩, hk, hg⟩ := hp
  have h : FAdmit.At m (FAssn.up (bytesAt p A S K bs) ⋆ R) :=
    ⟨_, rF, hh, r₁, r₂, hd, rfl, ⟨hb, hk, hg⟩, hR⟩
  exact FAdmit.iff_at.mpr ⟨m, hs, (h.aptsE hsh hal hK (hsz.trans hα) hv).frame⟩

/-- Read a word directly from a block of the actual start memory, retaining its block identity.
The block lookup and decode are kernel-checkable facts about that memory, so the caller need
not copy the generated global list or construct a separate memory. -/
theorem FAdmit.of_start_block {α : Type} [Enc α] {m : Mem} {b : BlockId} {blk : Block}
    {v : α} (hb : m.blocks[b]? = some blk) (hl : blk.live)
    (hlo : blk.kind.mappedLo = 0) (hal : blk.addr % 8 = 0)
    (hsize : blk.bytes.size = Enc.size α) (hdecode : Enc.decode blk.bytes = pure v)
    (hkind : blk.kind ≠ .constGlobal) (hα : Enc.size α = 8)
    (hs : m.FSeq) (hsh : shapes m = []) (hns : m.NoStack) :
    FAdmit (aptsE ⟨some b, 0⟩ v) := by
  obtain ⟨h, hF, hd, hm, hp⟩ := Mem.heap_split hb hl hlo
  have hp : pts ⟨some b, 0⟩ 8 v h :=
    ⟨blk.addr, blk.bytes.size, blk.kind, blk.bytes, by simpa using hal,
      hsize, hdecode, hp, hkind⟩
  obtain ⟨rF, hh⟩ := holds_mem m hns
  have hp : (FAssn.up (pts ⟨some b, 0⟩ 8 v) ⋆ FAssn.up (fun _ => True))
      ⟨m.fheap, Know.none, Ghost.unit⟩ :=
    up_sep ⟨by simpa using (show (pts ⟨some b, 0⟩ 8 v ∗ (fun _ => True)) m.heap
      from ⟨h, hF, hd, hm, hp, trivial⟩), rfl, rfl⟩
  exact FAdmit.of_start_pts hh hp hs hsh hα

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
  let f : Nat → FAssn := fun j => match gs[j]? with
    | some (bs, _, _) => bclaim j 0 bs.size
    | none => emp
  -- the claims of the globals below `n`, none above
  have key : ∀ n, n ≤ gs.length → ∃ r, Holds (Mem.ofGlobals σ gs) r ⟨FHeap.empty, Know.none, Ghost.unit⟩ ∧
      ((globals gs ⋆ plain) ⋆ sepN n f) r ∧ ∀ b x, n ≤ b → r.gh.cl b x = ECell.unit := by
    intro n hn
    induction n with
    | zero =>
      obtain ⟨hh, hg⟩ := initRes_holds_plain σ gs hK
      refine ⟨_, ?_, ⟨_, ⟨FHeap.empty, Know.none, Ghost.unit⟩, FHeap.disjoint_empty _, rfl, hg,
        rfl, rfl, rfl⟩, fun b x _ => ?_⟩
      · simpa [FHeap.union_empty, Know.union_none, Ghost.add_unit] using hh
      · simp only [Ghost.add_cl, noCl_globals gs _ (initRes_holds σ gs hK).2 b x]
        simp [Ghost.plain, Ghost.ofAC, Ghost.unit, ECell.unit_add]
    | succ n ih =>
      obtain ⟨r, hh, hp, hz⟩ := ih (by omega)
      have hb : n < (Mem.ofGlobals σ gs).blocks.size := by rw [Mem.ofGlobals_size]; omega
      have hgn : gs[n]? = some gs[n] := List.getElem?_eq_getElem (by omega)
      refine ⟨_, Holds.addClaim (lo := 0) (hi := (gs[n]'(by omega)).1.size) hh (hz n · (Nat.le_refl n))
        (fun _ => rfl) hb, ?_, fun b x hbn => ?_⟩
      · have hc : f n ⟨FHeap.empty, Know.none,
            Ghost.atCl n (ECell.onRange 0 (gs[n]'(by omega)).1.size (ECell.shareT none Frac.one 0))⟩ := by
          simp only [f, hgn]; exact ⟨rfl, rfl, rfl⟩
        have hj : (((globals gs ⋆ plain) ⋆ sepN n f) ⋆ f n) _ :=
          ⟨r, _, FHeap.disjoint_empty _, rfl, hp, hc⟩
        show ((globals gs ⋆ plain) ⋆ (f n ⋆ sepN n f)) _
        exact ac_cast hj (by ac_rfl)
      · simp only [Ghost.add_cl, hz b x (by omega), Ghost.atCl, show b ≠ n by omega, ↓reduceIte,
          ECell.add_unit]
  obtain ⟨r, hh, hp, -⟩ := key gs.length (Nat.le_refl _)
  exact ⟨_, ⟨Mem.init_fseq σ gs h, Mem.ofGlobals_footprint σ gs⟩, r, _, hh, hp⟩

/-- **The globals at program start, with their claims, are admissible** (`FAdmit.Start.init_claims`). -/
theorem FAdmit.init_claims (σ : Placement) (gs : List (Array Byte × Nat × BlockKind))
    (h : Mem.GlobalsFit gs) (hK : ∀ g ∈ gs, g.2.2.mappedLo = 0) :
    FAdmit (globals gs ⋆ gclaims gs) :=
  FAdmit.frame (R := plain) ((FAdmit.Start.init_claims σ gs h hK).toFAdmit.mono
    fun _ h => ac_cast h (by ac_rfl))

end Witness
end Zig
