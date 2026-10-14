import ZigLean.Sep.Full.AutoRules
import ZigLean.Mem.Repr

/-!
# The thread backend of `fsym` (`docs/proof-automation.md` §Threads)

`fsym` walks a thread's step (`FTTriple P c Q`, `FTTotalTriple P c Q`, `ZigLean/Sep/Full/Thread.lean`)
as it walks a sequential program, with these rules:

* **The logic record** `TLogic` (`TLogic.partial`: `FTTriple`, `TLogic.total`: `FTTotalTriple`):
  the structural rules of a thread logic, as `FLogic` has them for the sequential ones. A thread
  logic has no `ofTotal`: a sequential rule about a part of the state reads that part without a
  race check, which another thread may write (a frame read races); a total thread triple is a
  triple of each thread logic (`ofThreadTotal`).
* **Structural steps** (`Th.step`, `Th.stepAll`, `Th.ret`, `Th.ex_sep`, `Th.lift_sep`, …): the
  counterparts of `Auto.step` & co. with the same arguments; `Th.P.step` for a partial thread rule
  in `TLogic.partial`.
* **Sequential rules in a thread** (`FTTotalTriple.ofSeq`, `ThreadStep.lean`): a step rule
  `FTotalTriple P₀ c Q₀` (or `FTriple`, in the partial logic) executes `c` in a thread when `c` is
  local to the thread that owns `P₀` (`ThreadLocal P₀ c`). `fsym` proves that side goal with the
  providers below, so each `@[fsym]` sequential rule is a thread rule with no copy of its own. A
  command that no provider shows local (an atomic op, a read of another thread's bytes) gets no
  thread rule from a sequential one: atomic ops have their own thread rules
  (`docs/sep-threads.md`).
* **Locality providers** (`@[fsym_provider]`, kinds `ThreadLocal` and `OwnsPtr`): an owned access
  (`load`, `store`, `loadBytes`, `storeBytes`, `@memset`, `@memmove`, `@memcpy`) is local when the
  precondition owns its bytes (`OwnsPtr`, from an owned view: `bytesAt` and `pts` here, each other
  view in its module: `regionIn` in `Region`, `region` and error-union payloads in `Typed`, `arr`
  in `Arr`); `alloc`, results (`pure`, `throw`) and pure steps (`StateT.lift`) always are.
* **Native thread rules** (`@[fsym]` with an `FTTotalTriple` conclusion): steps that read only the
  blocks (`@intFromPtr`, pointer comparisons and formation, bounds checks) are thread rules by
  their proofs (`FTTotalTriple.of_read`); `Ops`' here, `Region`'s in `Region`, and the `const`
  read `FTTotalTriple.cload` in `Const` (it records nothing, MM-20).

This module imports only the rule library (`AutoRules`), so importing it activates no step rule
of a sequential goal.
-/

namespace Zig.Full

open FAssn Conc

/-! ## Updates of total thread triples -/

namespace FTTotalTriple

variable {α : Type} {P P' : FAssn} {c : MemM α} {Q Q' : α → FAssn}

/-- **An update of the precondition** (`EUpd`, read in `m.noFp`). -/
theorem eupd (hu : EUpd P P') (ht : FTTotalTriple P' c Q) : FTTotalTriple P c Q :=
  ⟨FTTriple.eupd hu ht.1, fun m r rF hh hp hc ho => by
    obtain ⟨r', hh', hp'⟩ := hu m.noFp r rF hh.toNoFp hp hc.noFp
    exact ht.2 m r' rF hh'.ofNoFp hp' hc (ho.sub (hh.erase_sub_of hh'.ofNoFp))⟩

/-- An update of the postcondition. -/
theorem eupd_post (ht : FTTotalTriple P c Q) (hu : ∀ v, EUpd (Q v) (Q' v)) : FTTotalTriple P c Q' :=
  ⟨ht.1.eupd_post hu, ht.2⟩

end FTTotalTriple

/-! ## The logic record -/

/-- A logic of a thread's steps (module doc): `FTTriple` or `FTTotalTriple`. -/
structure TLogic where
  T : {α : Type} → FAssn → MemM α → (α → FAssn) → Prop
  ofThreadTotal : ∀ {α : Type} {P : FAssn} {c : MemM α} {Q : α → FAssn},
    FTTotalTriple P c Q → T P c Q
  toPartial : ∀ {α : Type} {P : FAssn} {c : MemM α} {Q : α → FAssn}, T P c Q → FTTriple P c Q
  conseq : ∀ {α : Type} {P P' : FAssn} {c : MemM α} {Q Q' : α → FAssn}, T P c Q →
    (∀ r, P' r → P r) → (∀ v r, Q v r → Q' v r) → T P' c Q'
  frame : ∀ {α : Type} {P R : FAssn} {c : MemM α} {Q : α → FAssn}, T P c Q →
    T (P ⋆ R) c (fun v => Q v ⋆ R)
  bind : ∀ {α β : Type} {P : FAssn} {c : MemM α} {Q : α → FAssn} {R : β → FAssn}
    {f : α → MemM β}, T P c Q → (∀ v, T (Q v) (f v) R) → T P (c >>= f) R
  ex : ∀ {α γ : Type} {P : γ → FAssn} {c : MemM α} {Q : α → FAssn}, (∀ x, T (P x) c Q) →
    T (FAssn.ex P) c Q
  lift : ∀ {α : Type} {φ : Prop} {P : FAssn} {c : MemM α} {Q : α → FAssn}, (φ → T P c Q) →
    T (⟪φ⟫ ⋆ P) c Q
  eupd : ∀ {α : Type} {P P' : FAssn} {c : MemM α} {Q : α → FAssn}, EUpd P P' → T P' c Q →
    T P c Q

/-- Partial correctness of a thread's step: `FTTriple`. -/
def TLogic.partial : TLogic where
  T := FTTriple
  ofThreadTotal := FTTotalTriple.toPartial
  toPartial := id
  conseq := FTTriple.conseq
  frame := FTTriple.frame
  bind := FTTriple.bind
  ex := FTTriple.ex
  lift := FTTriple.lift
  eupd := FTTriple.eupd

/-- Total correctness of a thread's step: `FTTotalTriple`. -/
def TLogic.total : TLogic where
  T := FTTotalTriple
  ofThreadTotal := id
  toPartial := FTTotalTriple.toPartial
  conseq := FTTotalTriple.conseq
  frame := FTTotalTriple.frame
  bind := FTTotalTriple.bind
  ex := FTTotalTriple.ex
  lift := FTTotalTriple.lift
  eupd := FTTotalTriple.eupd

/-! ## Locality providers -/

namespace ThreadLocal

variable {α : Type} {P X : FAssn} {c : MemM α}

/-- What is local to the thread that owns a part of `P` is local to the thread that owns `P`. -/
theorem of_within (h : ThreadLocal X c) (hw : Within X P) : ThreadLocal P c := by
  intro m r rF hh hp hc ho
  obtain ⟨R, hxr⟩ := hw r hp
  exact h.frame (R := R) m r rF hh hxr hc ho

/-- **A pure step** (`StateT.lift` of a `Result`) is local: it touches no memory. -/
theorem liftR (g : Result α) : ThreadLocal P (StateT.lift g : MemM α) :=
  intro fun m _ _ _ _ _ _ => ⟨RunFp.lift g, fun _ _ e => by
    obtain ⟨-, rfl⟩ := Proto.MemM.lift_ok (m := m.noFp) e
    exact ⟨FStepIn.refl _ _, fun _ _ _ h => h⟩⟩

/-- **The stack block of an escaping local** (`allocStack`) is local, as `alloc`. -/
theorem allocStack (size align : Nat) : ThreadLocal P (Zig.allocStack size align) :=
  alloc .stack size align

/-- **`free` of a whole block** is local to the thread that owns its bytes and its full extent
(two parts of `P`, first: they fix the block and the bytes): no access to the block races with
its end. -/
theorem free_of {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte} {b : BlockId}
    (hx : Within (up (Zig.bytesAt p A S K bs)) P) (he : Within (bext b S K) P)
    (hpb : p.block = some b) (hS : bs.size = S) (h0 : p.off = 0) :
    ThreadLocal P (Zig.free p) :=
  free hpb fun m r _ hh hp blk hb x hlt => by
    obtain ⟨R₁, h1⟩ := he r hp
    obtain ⟨blk', hb', -, hsz, -⟩ := hh.bauth h1
    rw [hb] at hb'; cases hb'
    obtain ⟨R₂, h2⟩ := hx r hp
    exact (OwnsAt.bytesAt hpb).sepL r h2 x (by simp [h0]) (by simp [h0]; omega)

/-- **`@returnAddress()`** is local: it reads the oracle's words, not the record or a byte. -/
theorem returnAddress : ThreadLocal P Zig.returnAddress :=
  intro fun m _ _ _ _ _ _ => ⟨rfl, fun _ m₀ e => by
    have hr : Zig.returnAddress.run m.noFp = Pure.pure (m.noFp.arbitrary.getD m.noFp.arbitraryNext 0,
        { m.noFp with arbitraryNext := m.noFp.arbitraryNext + 1 }) := rfl
    rw [hr] at e
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Result.pure_inj e)
    exact ⟨.of_stepIn ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl,
        VClock.le_refl _, Nat.le_refl _, fun _ he => .inl he, fun _ he => .inl he⟩
      (fun _ _ h => h) (fun _ he hn => absurd he hn) (fun _ h => h), fun _ _ _ h => h⟩⟩

/-- **`@ptrFromInt`'s check** is local: it reads no memory. -/
theorem checkAddr (al : Nat) (nonNull : Bool) (n : Nat) : ThreadLocal P (Zig.checkAddr al nonNull n) := by
  unfold Zig.checkAddr
  split
  · exact ThreadLocal.throw _
  · exact ThreadLocal.pure _

/-- `@ptrFromInt` reads the blocks only: its run with a record in front. -/
theorem _root_.Zig.Full.RunFp.ptrFromAddr {F : Array FootprintEntry} {m₀ : Mem} (n : Nat) :
    RunFp F m₀ (Zig.ptrFromAddr n) := by
  unfold Zig.ptrFromAddr
  refine RunFp.get_bind rfl ?_
  dsimp only
  generalize (Array.filterMap _ m₀.blocks.zipIdx).toList = l
  rcases l with _ | ⟨⟨b, blk⟩, _ | ⟨x, rest⟩⟩ <;> try exact RunFp.pure _
  cases m₀.allocPolicy.provenance
  · exact RunFp.pure _
  · repeat' split
    all_goals exact RunFp.pure _

/-- **`@ptrFromInt`** is local: it reads the blocks only and changes nothing. -/
theorem ptrFromAddr (n : Nat) : ThreadLocal P (Zig.ptrFromAddr n) :=
  intro fun m _ _ _ _ _ _ => ⟨RunFp.ptrFromAddr n, fun _ m₀ e => by
    obtain ⟨w, hw⟩ := ptrFromAddr_run n m.noFp
    rw [hw] at e
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Result.pure_inj e)
    exact ⟨FStepIn.refl _ _, fun _ _ _ h => h⟩⟩

/-- **`@ptrFromInt` to `?*T`** is local, as `ptrFromAddr`. -/
theorem optPtrFromAddr (n : Nat) : ThreadLocal P (Zig.optPtrFromAddr n) := by
  unfold Zig.optPtrFromAddr
  split
  · exact ThreadLocal.pure _
  · rw [← bind_pure_comp]
    refine intro fun m _ _ _ _ _ _ =>
      ⟨RunFp.bind (RunFp.ptrFromAddr n) fun _ _ _ => RunFp.pure _, fun v m₀ e => ?_⟩
    obtain ⟨w, hw⟩ := ptrFromAddr_run n m.noFp
    obtain ⟨w', m₁, h1, h2⟩ := Conc.Proto.MemM.bind_ok e
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Result.pure_inj (hw.symm.trans h1))
    obtain ⟨-, rfl⟩ := Conc.Proto.MemM.pure_ok h2
    exact ⟨FStepIn.refl _ _, fun _ _ _ h => h⟩

/-- Pointer formation reads the blocks only: its run with a record in front. -/
theorem _root_.Zig.Full.RunFp.ptrProject {F : Array FootprintEntry} {m₀ : Mem} (p : Ptr)
    (f : Ptr → Ptr) : RunFp F m₀ (Zig.ptrProject p f) := by
  unfold RunFp Zig.ptrProject
  simp only [StateT.run]
  have e : ∀ q, (m₀.withFp F).inBounds q = m₀.inBounds q := fun _ => rfl
  rw [e, e]
  split <;> rfl

/-- **Pointer formation** (`ptrProject`, MM-3) is local: it reads the blocks only and changes
nothing, whatever the precondition owns (a pointer known only by its block's address). -/
theorem ptrProject (p : Ptr) (f : Ptr → Ptr) : ThreadLocal P (Zig.ptrProject p f) :=
  intro fun m _ _ _ _ _ _ => ⟨RunFp.ptrProject p f, fun _ m₀ e => by
    simp only [Zig.ptrProject, StateT.run] at e
    split at e
    · obtain ⟨-, rfl⟩ := Prod.mk.inj (Result.pure_inj e)
      exact ⟨FStepIn.refl _ _, fun _ _ _ h => h⟩
    · exact (Proto.MemM.throw_ok (m := m.noFp) e).elim⟩

/-- **`@memset`** of `n` items over owned bytes, with the size of the bytes it writes (`hsz`, a
fact of `fsym_arith`). -/
theorem memset_of {δ : Type} [Enc δ] {al : Nat} {p : Ptr} {n : BitVec 64} {v : Option δ}
    (hsz : (memsetBytes n.toNat v).size = n.toNat * Enc.size δ)
    (hown : OwnsPtr P p (n.toNat * Enc.size δ)) : ThreadLocal P (Zig.memset al p n v) := by
  unfold Zig.memset
  refine ite (fun _ => pure _) fun _ => readBind (fun _ _ => rfl) fun _ => ?_
  cases v <;> simp only [memsetBytes] at hsz <;> exact storeBytes (by rw [hsz]; exact hown)

/-- **An owned typed store** of a lawful encoding: its bytes are the type's. -/
theorem store_lawful {T : Type} [Enc T] [LawfulEnc T] {a : Nat} {p : Ptr} {w : T}
    (hown : OwnsPtr P p (Enc.size T)) : ThreadLocal P (Zig.store a p w) :=
  store (by rw [LawfulEnc.size_encode]; exact hown)

end ThreadLocal

namespace OwnsPtr

variable {P X : FAssn} {p q : Ptr} {n : Nat}

theorem of_within (h : OwnsPtr X q n) (hw : Within X P) : OwnsPtr P q n := fun b hb r hp => by
  obtain ⟨R, hxr⟩ := hw r hp
  exact (h b hb).sepL r hxr

variable {A S a : Nat} {K : BlockKind} {bs : Array Byte}

/-- No bytes: owned by every precondition (`@memcpy` of no items). -/
theorem of_zero (h : n = 0) : OwnsPtr P q n := by
  subst h; intro _ _ _ _ _ h1 h2; omega

/-- The `n` bytes at `q`, inside owned bytes at `p` of the same block. -/
theorem bytesAt_in (hq : q.block = p.block) (h0 : p.off ≤ q.off)
    (hk : q.off.toNat + n ≤ p.off.toNat + bs.size) : OwnsPtr (up (Zig.bytesAt p A S K bs)) q n := by
  intro b hb r hr x hx hx'
  obtain ⟨⟨b', hb', hp0, hl⟩, -, -⟩ := hr
  rw [hq] at hb; rw [hb] at hb'; cases hb'
  rw [hl (b, x), if_pos ⟨rfl, by omega, by omega⟩]; simp

/-- The `n` bytes at `q`, inside a typed value at `p`. -/
theorem pts_in {T : Type} [Enc T] {v : T} (hq : q.block = p.block) (h0 : p.off ≤ q.off)
    (hk : q.off.toNat + n ≤ p.off.toNat + Enc.size T) : OwnsPtr (up (Zig.pts p a v)) q n := by
  rintro b hb r ⟨⟨_, _, _, bs, -, hs, -, hbt, -⟩, hk', hg⟩
  exact bytesAt_in (bs := bs) hq h0 (by omega) b hb r ⟨hbt, hk', hg⟩

end OwnsPtr

attribute [fsym_provider] ThreadLocal.load ThreadLocal.loadBytes ThreadLocal.store_lawful
  ThreadLocal.store ThreadLocal.storeBytes ThreadLocal.memset_of ThreadLocal.memmove
  ThreadLocal.memcpy ThreadLocal.alloc ThreadLocal.allocStack ThreadLocal.returnAddress
  ThreadLocal.free_of ThreadLocal.pure ThreadLocal.throw ThreadLocal.liftR ThreadLocal.checkAddr
  ThreadLocal.ptrFromAddr ThreadLocal.optPtrFromAddr OwnsPtr.pts_in OwnsPtr.bytesAt_in
  ThreadLocal.ite OwnsPtr.of_zero ThreadLocal.ptrProject

/-! ## Native thread rules -/

attribute [fsym] FTTotalTriple.ptrAddr_of FTTotalTriple.checkAlign_of FTTotalTriple.ptrEqAddr_of
  FTTotalTriple.ptrProject_of FTTotalTriple.ptrProject_elem_of

/-- The size of the bytes of `@memset`: `n` items of the type's size. -/
@[fsym_arith] theorem memsetBytes_size_none {δ : Type} [Enc δ] (n : Nat) :
    (memsetBytes n (none : Option δ)).size = n * Enc.size δ := by
  simp [memsetBytes]

@[fsym_arith] theorem memsetBytes_size_some {δ : Type} [Enc δ] [LawfulEnc δ] (n : Nat) (x : δ) :
    (memsetBytes n (some x)).size = n * Enc.size δ := by
  simp [memsetBytes, LawfulEnc.size_encode]

/-! ## Structural steps over any `TLogic` -/

namespace Auto.Th

/- The variables mirror `Auto.step` & co. (`AutoRules.lean`), with a `TLogic` in place of the
`FLogic`: `fsym` applies both families with the same arguments. -/
variable (L : TLogic) {α β γ : Type} {P P' P₀ R : FAssn} {Q : β → FAssn} {c : MemM β}

theorem pre_eq (h : P = P') (t : L.T P' c Q) : L.T P c Q := h ▸ t

theorem bind_pure (t : L.T P (c >>= pure) Q) : L.T P c Q := by
  simpa only [_root_.bind_pure] using t

/-- A command proved by a total thread rule on the part `P₀`, framed by `R`. -/
theorem step {c : MemM α} {f : α → MemM β} {Q₀ : α → FAssn} (r : FTTotalTriple P₀ c Q₀)
    (k : ∀ v, L.T (Q₀ v ⋆ R) (f v) Q) : L.T (P₀ ⋆ R) (c >>= f) Q :=
  L.bind (L.frame (L.ofThreadTotal r)) k

/-- A command proved by a total thread rule on the whole precondition. -/
theorem stepAll {c : MemM α} {f : α → MemM β} {Q₀ : α → FAssn} (r : FTTotalTriple P c Q₀)
    (k : ∀ v, L.T (Q₀ v) (f v) Q) : L.T P (c >>= f) Q :=
  L.bind (L.ofThreadTotal r) k

/-- **A return**, after a frame-preserving update into the postcondition. -/
theorem ret {v : β} (h : EUpd P (Q v)) : L.T P (pure v) Q :=
  L.eupd h (L.ofThreadTotal (FTTotalTriple.ret v))

theorem ex_sep {F : γ → FAssn} (t : ∀ x, L.T (F x ⋆ R) c Q) : L.T (FAssn.ex F ⋆ R) c Q :=
  L.conseq (L.ex (P := fun x => F x ⋆ R) t) (fun _ h => sep_ex.mp h) (fun _ _ h => h)

theorem lift_sep {φ : Prop} (t : φ → L.T R c Q) : L.T (⟪φ⟫ ⋆ R) c Q := L.lift t

theorem of_false (h : False) : L.T P c Q := h.elim

/-- The join of two branches' posts (`Auto.join_l`). -/
theorem join_l {Q₁ Q₂ : β → FAssn} (t : L.T P c Q₁) :
    L.T P c (fun v => FAssn.ex fun b : Bool => if b = true then Q₁ v else Q₂ v) :=
  L.conseq t (fun _ h => h) fun _ _ h => ⟨true, h⟩

/-- The join of two branches' posts (`Auto.join_r`). -/
theorem join_r {Q₁ Q₂ : β → FAssn} (t : L.T P c Q₂) :
    L.T P c (fun v => FAssn.ex fun b : Bool => if b = true then Q₁ v else Q₂ v) :=
  L.conseq t (fun _ h => h) fun _ _ h => ⟨false, h⟩

/-- A fact of a part `X` of the precondition, in the context. -/
theorem pre_fact {X : FAssn} {φ : Prop} (hX : AtomFacts X φ) (t : φ → L.T (X ⋆ R) c Q) :
    L.T (X ⋆ R) c Q :=
  L.conseq (L.lift t) (fun _ h => sep_lift.mpr ⟨hX.sepL h, h⟩) (fun _ _ h => h)

/-- A fact of a part `X` of the precondition that needs the memory, in the context. -/
theorem pre_mfact {X : FAssn} {φ : Prop} (hX : MemFacts X φ) (t : φ → L.T (X ⋆ R) c Q) :
    L.T (X ⋆ R) c Q :=
  L.eupd hX.sepL.eupd (L.lift t)

/-- An update of the precondition (a view of an atom, `@[fsym_view]`). -/
theorem pre_eupd (h : EUpd P P') (t : L.T P' c Q) : L.T P c Q := L.eupd h t

namespace P

/- `Th.step`/`stepAll` for a partial thread rule (`FTTriple`) in `TLogic.partial` (whose `T` is
`FTTriple`); `L` is that logic, kept for the arguments `fsym` passes. -/
variable (L : TLogic) {α β : Type} {P P₀ R : FAssn} {Q : β → FAssn}
include L

theorem step {c : MemM α} {f : α → MemM β} {Q₀ : α → FAssn} (r : FTTriple P₀ c Q₀)
    (k : ∀ v, FTTriple (Q₀ v ⋆ R) (f v) Q) : FTTriple (P₀ ⋆ R) (c >>= f) Q :=
  FTTriple.bind r.frame k

theorem stepAll {c : MemM α} {f : α → MemM β} {Q₀ : α → FAssn} (r : FTTriple P c Q₀)
    (k : ∀ v, FTTriple (Q₀ v) (f v) Q) : FTTriple P (c >>= f) Q :=
  FTTriple.bind r k

end P

end Auto.Th

end Zig.Full
