import ZigLean.Sep.Full.AutoRules
import ZigLean.Sep.Full.Extent
import ZigLean.Sep.Full.Dispatch
import ZigLean.Sep.Full.AtomicRules
import ZigLean.Mem.Repr

/-!
# The concurrent backend of `fsym`: rules for `CTriple` (`docs/proof-automation.md`)

`fsym` walks a call of a concurrent function (`CTriple P x Q`, stop by stop,
`ZigLean/Sep/Full/Conc.lean`) as it walks a thread's step, with these rules:

* **Structural steps** (`C.step`, `C.stepAll`, `C.ret`, `C.ex_sep`, `C.lift_sep`, …), the
  `CTriple` counterparts of `Auto.step` & co. A `MemM` command `ConcM.liftMem c` is executed by a
  thread rule about `c` (`FTTriple`, as in a thread logic, `AutoThread.lean`): a native one (the
  atomic rules below, `FTTotalTriple` rules read partially), or a sequential rule with the
  locality of `c` (`ofSeq`). A `CTriple` rule (`C.stepC`) executes a
  concurrent command: a call through a table (`Table.call`, `Table.callOr`, `CVTable.dispatch`,
  the `CTriple.tableCall` reading of a call site), or a loop with its invariant (`CTriple.loop`).
* **An atomic op's oracle choice**: at an owned word the pick rule of its count function
  (`CTriple.pick_load` & co., `AtomicRules.lean`: one option under `Mem.MsgCov`, tried first),
  else every choice (`C.pick`, `CTriple.pick_bind`). Before them a **bind rule**: a rule about
  the pick, its op and the rest `g` of the program (`CTriple.weakCasPtr_bind`: a weak `cmpxchg`'s
  success and spurious failure), whose premises are the triples of the resumptions about `g`;
  the walk goes on with them as with an ordinary rule's continuation (`tryBindRule`). A bind
  rule states its frame (a variable of its precondition, threaded into those premises).
* **Indirect calls**: a generated chain `if f == c₁ then x₁ else … else d` (`d` is
  `throw .illegal`, or the environment's call of an open interface) is folded into
  `callIndirect f [(c₁, x₁), …] d` before the body is normalized (`callIndirect_fold_one`/`ext`/
  `cons`), read under the locals (`callIndirect_run`), and the common continuation of its arms is
  pulled out (`callIndirect_bind`, `pullIndirect`), so the call is one command. `fsym` executes
  it by a `CTriple` rule for the table call, or reads the arm that the facts select
  (`callIndirect_pos`/`_neg`), then the last arm (`callIndirect_nil`).
* **`fsym_norm`** for concurrent bodies: the `CNorm` lemmas (`conc_norm`), the atomic ops of
  `CM` as an oracle pick and a `MemM` op, and `ConcM.liftMem` pushed through the `MemM` layer
  (`liftMem_bind`, `liftMem_ite`), so a generated `MemM` callee is walked command by command.
* Sequential step rules that generated concurrent code reaches: `@intFromPtr` of `?*T`
  (`optPtrAddr`), `@ptrFromInt` checks (`checkAddr_of`) and results (`optPtrFromAddr_any`),
  `@divExact` (`divExact_step`), and the value of `-|` (`toNat_subSat`).
-/

namespace Zig.Full.Auto

open FAssn

/-! ## Sequential rules and arithmetic that concurrent code reaches -/

section Seq

variable {w : Nat} {P : FAssn}

/-- **`@ptrFromInt`'s check** of an address that the alignment divides (null allowed). -/
@[fsym] theorem checkAddr_of {al n : Nat} (h : n % al = 0) :
    FTotalTriple P (checkAddr al false n) (fun _ => P) := by
  rw [Zig.checkAddr_ok h]; exact FTotalTriple.ret (Q := fun _ => P) ()

/-- **`@ptrFromInt` to `?*T`**: some pointer (or null); nothing changes. -/
@[fsym] theorem optPtrFromAddr_any (n : Nat) : FTotalTriple P (optPtrFromAddr n) (fun _ => P) :=
  FTotalTriple.of_run fun m r rF hh hp hs => by
    unfold optPtrFromAddr
    split
    · exact ⟨none, m, r, rfl, hh, hp, hs⟩
    · obtain ⟨v, hv⟩ := ptrFromAddr_run n m
      refine ⟨some v, m, r, ?_, hh, hp, hs⟩
      simp only [Functor.map, StateT.map, StateT.run] at hv ⊢; rw [hv]; rfl

/-- A checked unsigned `@divExact` by a nonzero divisor that divides. -/
@[fsym] theorem divExact_step {a b : BitVec w} (h0 : b ≠ 0) (h : a.toNat % b.toNat = 0) :
    FTotalTriple P (StateT.lift (Zig.divExact false a b) : MemM (BitVec w))
      (fun r => ⟪r.toNat = a.toNat / b.toNat⟫ ⋆ P) := by
  have hb : 0 < b.toNat := by
    rcases Nat.eq_zero_or_pos b.toNat with e | e
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using e)) h0
    · exact e
  have hq : a / b * b = a := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_mul, BitVec.toNat_udiv, Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h),
      Nat.mod_eq_of_lt a.isLt]
  have e : Zig.divExact false a b = pure (a / b) := by
    simp only [Zig.divExact, h0, decide_false, Bool.false_and, Bool.or_false, Bool.false_eq_true,
      ↓reduceIte, BitVec.udiv_eq, hq]
  rw [e]; exact read_val BitVec.toNat_udiv

/-- `-|` of unsigned words: truncated subtraction of the values. -/
@[fsym_arith] theorem toNat_subSat (a b : BitVec w) : (Zig.subSat false a b).toNat = a.toNat - b.toNat := by
  have ha := a.isLt
  have hc : ((2 ^ w : Nat) : Int) = (2 : Int) ^ w := by push_cast; rfl
  have hp : 0 < 2 ^ w := Nat.two_pow_pos w
  simp only [Zig.subSat, Zig.clamp, Zig.intLo_unsigned, Zig.intHi_unsigned, Zig.val,
    Bool.false_eq_true, ↓reduceIte, BitVec.toNat_ofInt]
  generalize (2 : Int) ^ w = M at *
  generalize 2 ^ w = N at *
  subst hc
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  omega

/-- A remainder by a smaller power of two through a remainder by a larger one (`2 ^ x ∣ M`):
`omega` reads `z % M` for a literal `M`, not `z % 2 ^ x`. -/
theorem mod_pow_of_le {z x c M : Nat} (hM : M = 2 ^ c) (h : x ≤ c) : z % 2 ^ x = z % M % 2 ^ x := by
  subst hM; exact (Nat.mod_mod_of_dvd z (Nat.pow_dvd_pow 2 h)).symm

theorem optPtrAddr_some (p : Ptr) : optPtrAddr (some p) = ptrAddr p := rfl
theorem optPtrAddr_none : optPtrAddr none = pure 0 := rfl

/-- Owned atomic bytes: their block reaches their end. -/
theorem Reaches.abytes {b : BlockId} {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte}
    {tg : Option (Nat × Nat)} (hpb : p.block = some b) (hpos : 0 < bs.size) :
    Reaches b (p.off.toNat + bs.size) (abytesAt p A S K bs tg) := by
  have e : p.off.toNat + bs.size = p.off.toNat + bs.size - 1 + 1 := by omega
  rw [e]
  refine Reaches.owned fun r ⟨_, _, b', hb', _, hl⟩ => ?_
  rw [hpb] at hb'; cases hb'
  rw [hl]; exact ⟨_, if_pos ⟨rfl, by omega, by omega⟩⟩

/-- An atomic word owns its 8 bytes: its block reaches its end. -/
theorem Reaches.apts {b : BlockId} {p : Ptr} {v : BitVec 64} (hpb : p.block = some b) :
    Reaches b (p.off.toNat + 8) (apts p v) := fun m r rF hh ⟨_, _, _, bs, _, _, hs, _, hab⟩ =>
  hs ▸ Reaches.abytes hpb (by omega) m r rF hh hab

/-- An atomic value owns its 8 bytes: its block reaches its end. -/
theorem Reaches.aptsE {α : Type} [Enc α] {b : BlockId} {p : Ptr} {v : α} (hpb : p.block = some b) :
    Reaches b (p.off.toNat + 8) (aptsE p v) := fun m r rF hh ⟨_, _, _, bs, _, _, hs, _, hab⟩ =>
  hs ▸ Reaches.abytes hpb (by omega) m r rF hh hab

attribute [fsym_provider] Reaches.apts Reaches.aptsE

/-- An atomic value: the block of its pointer, a nonnegative offset. -/
@[fsym_facts] theorem facts_aptsE {α : Type} [Enc α] {p : Ptr} {v : α} :
    AtomFacts (aptsE p v) ((∃ b, p.block = some b) ∧ 0 ≤ p.off) := by
  rintro r ⟨-, -, -, -, -, -, -, -, -, -, b, hb, h0, -⟩; exact ⟨⟨b, hb⟩, h0⟩

/-- A token of the current epoch names a grant of its authority's map (`gfrag_mem`). -/
@[fsym_facts] theorem facts_gfrag {γ e i : Nat} {M : GMap} {t : STag} {g : GRegion} :
    MemFacts (gauthP γ e M t ⋆ gfrag γ e i g) (M i = some g) := by
  intro m r rF hh hr _
  obtain ⟨r₁, r₂, hd, rfl, h1, h2⟩ := hr
  exact gfrag_mem ⟨r₁, r₂, hd, rfl, h1, h2⟩ (hh.ghost.1)

end Seq

attribute [fsym_norm] optPtrAddr_some optPtrAddr_none
attribute [fsym_arith] Zig.subWrap Zig.addWrap Zig.mulWrap BitVec.sub_self
attribute [fsym_norm] Option.isSome_some Option.isSome_none Option.isNone_some Option.isNone_none

/-! ## Partial rules in `FLogic.partial` -/

namespace P

/- `Auto.step`/`stepAll` for a partial rule (`FTriple`) in `FLogic.partial` (whose `T` is
`FTriple`); `L` is that logic, kept for the arguments `fsym` passes. -/
variable (L : FLogic) {α β : Type} {P P₀ R : FAssn} {Q : β → FAssn}
include L

theorem step {c : MemM α} {f : α → MemM β} {Q₀ : α → FAssn} (r : FTriple P₀ c Q₀)
    (k : ∀ v, FTriple (Q₀ v ⋆ R) (f v) Q) : FTriple (P₀ ⋆ R) (c >>= f) Q :=
  FTriple.bind r.frame k

theorem stepAll {c : MemM α} {f : α → MemM β} {Q₀ : α → FAssn} (r : FTriple P c Q₀)
    (k : ∀ v, FTriple (Q₀ v) (f v) Q) : FTriple P (c >>= f) Q :=
  FTriple.bind r k

end P

/-! ## `CTriple` steps -/

namespace C

/- The variables mirror `Auto.step` & co. (`AutoRules.lean`), with the target type `Tgt` in place
of the logic `L`: `fsym` applies both families with the same arguments. -/
variable (Tgt : Type) {α β γ : Type} {P P' P₀ R : FAssn} {Q : β → FAssn} {c : ConcM Tgt β}

theorem pre (h : ∀ r, P r → P' r) (t : CTriple P' c Q) : CTriple P c Q := t.pre h

theorem pre_eq (h : P = P') (t : CTriple P' c Q) : CTriple P c Q := h ▸ t

theorem bind_pure (t : CTriple P (c >>= pure) Q) : CTriple P c Q := by
  simpa only [_root_.bind_pure] using t

/-- A `MemM` command proved by a thread rule on the part `P₀`, framed by `R`. -/
theorem step {c : MemM α} {f : α → ConcM Tgt β} {Q₀ : α → FAssn} (r : FTTriple P₀ c Q₀)
    (k : ∀ v, CTriple (Q₀ v ⋆ R) (f v) Q) : CTriple (P₀ ⋆ R) (ConcM.liftMem c >>= f) Q :=
  CTriple.bind (CTriple.liftMem r.frame) k

/-- A `MemM` command proved by a thread rule on the whole precondition. -/
theorem stepAll {c : MemM α} {f : α → ConcM Tgt β} {Q₀ : α → FAssn} (r : FTTriple P c Q₀)
    (k : ∀ v, CTriple (Q₀ v) (f v) Q) : CTriple P (ConcM.liftMem c >>= f) Q :=
  CTriple.bind (CTriple.liftMem r) k

/-- A concurrent command proved by a `CTriple` rule on the part `P₀`, framed by `R`. -/
theorem stepC {c : ConcM Tgt α} {f : α → ConcM Tgt β} {Q₀ : α → FAssn} (r : CTriple P₀ c Q₀)
    (k : ∀ v, CTriple (Q₀ v ⋆ R) (f v) Q) : CTriple (P₀ ⋆ R) (c >>= f) Q :=
  CTriple.bind r.frame k

/-- A concurrent command proved by a `CTriple` rule on the whole precondition. -/
theorem stepAllC {c : ConcM Tgt α} {f : α → ConcM Tgt β} {Q₀ : α → FAssn} (r : CTriple P c Q₀)
    (k : ∀ v, CTriple (Q₀ v) (f v) Q) : CTriple P (c >>= f) Q :=
  CTriple.bind r k

/-- **A return**, after a frame-preserving update into the postcondition. -/
theorem ret {v : β} (h : EUpd P (Q v)) : CTriple P (pure v : ConcM Tgt β) Q :=
  CTriple.eupd h (CTriple.ret v)

theorem ex_sep {F : γ → FAssn} (t : ∀ x, CTriple (F x ⋆ R) c Q) : CTriple (FAssn.ex F ⋆ R) c Q :=
  CTriple.pre (CTriple.ex (P := fun x => F x ⋆ R) t) fun _ h => sep_ex.mp h

theorem lift_sep {φ : Prop} (t : φ → CTriple R c Q) : CTriple (⟪φ⟫ ⋆ R) c Q := CTriple.lift t

theorem of_false (h : False) : CTriple P c Q := h.elim

/-- The join of two branches' posts (`Auto.join_l`). -/
theorem join_l {Q₁ Q₂ : β → FAssn} (t : CTriple P c Q₁) :
    CTriple P c (fun v => FAssn.ex fun b : Bool => if b = true then Q₁ v else Q₂ v) :=
  t.post fun _ _ h => ⟨true, h⟩

/-- The join of two branches' posts (`Auto.join_r`). -/
theorem join_r {Q₁ Q₂ : β → FAssn} (t : CTriple P c Q₂) :
    CTriple P c (fun v => FAssn.ex fun b : Bool => if b = true then Q₁ v else Q₂ v) :=
  t.post fun _ _ h => ⟨false, h⟩

/-- A fact of a part `X` of the precondition, in the context. -/
theorem pre_fact {X : FAssn} {φ : Prop} (hX : AtomFacts X φ) (t : φ → CTriple (X ⋆ R) c Q) :
    CTriple (X ⋆ R) c Q :=
  CTriple.pre (CTriple.lift t) fun _ h => sep_lift.mpr ⟨hX.sepL h, h⟩

/-- A fact of a part `X` of the precondition that needs the memory, in the context. -/
theorem pre_mfact {X : FAssn} {φ : Prop} (hX : MemFacts X φ) (t : φ → CTriple (X ⋆ R) c Q) :
    CTriple (X ⋆ R) c Q :=
  CTriple.eupd hX.sepL.eupd (CTriple.lift t)

/-- An update of the precondition (a view of an atom, `@[fsym_view]`). -/
theorem pre_eupd (h : EUpd P P') (t : CTriple P' c Q) : CTriple P c Q := CTriple.eupd h t

/-- **An atomic op's oracle choice**: every choice. -/
theorem pick {count : Mem → Nat} {f : Nat → ConcM Tgt β} (h : ∀ c, CTriple P (f c) Q) :
    CTriple P ((ConcM.sync (.pick count) : ConcM Tgt Nat) >>= f) Q :=
  CTriple.pick_bind h

/-- The arm of an indirect call that the function pointer selects. -/
theorem callIndirect_pos {f p : Ptr} {x d : ConcM Tgt β} {arms : List (Ptr × ConcM Tgt β)}
    (h : f = p) : Full.callIndirect f ((p, x) :: arms) d = x := by
  subst h; simp [Full.callIndirect]

/-- Past an arm that the function pointer does not select. -/
theorem callIndirect_neg {f p : Ptr} {x d : ConcM Tgt β} {arms : List (Ptr × ConcM Tgt β)}
    (h : ¬ f = p) : Full.callIndirect f ((p, x) :: arms) d = Full.callIndirect f arms d := by
  simp [Full.callIndirect, h]

/-- No arm left: the last arm (`.illegal` for a closed function type, the environment's call
for an open one). -/
theorem callIndirect_nil (f : Ptr) (d : ConcM Tgt β) : Full.callIndirect f [] d = d := rfl

end C

/-! ## Normalizing concurrent bodies -/

section Norm

variable {Tgt α β : Type}

theorem liftMem_bind (x : MemM α) (f : α → MemM β) :
    (ConcM.liftMem (x >>= f) : ConcM Tgt β) = ConcM.liftMem x >>= fun a => ConcM.liftMem (f a) := by
  funext n m
  show CoN.leaf ((x >>= f).run m) = (CoN.leaf (x.run m)).bind fun p k => ConcM.liftMem (f p.1) k p.2
  rw [StateT.run_bind]
  generalize (x.run m : Option (Except Error (α × Mem))) = o
  rcases o with _ | _ | ⟨a, m'⟩ <;> rfl

theorem liftMem_ite {c : Prop} [Decidable c] (x y : MemM α) :
    (ConcM.liftMem (if c then x else y) : ConcM Tgt α) =
      if c then ConcM.liftMem x else ConcM.liftMem y := by
  split <;> rfl

theorem liftMem_throw (e : Error) : (ConcM.liftMem (throw e : MemM α) : ConcM Tgt α) = throw e := rfl

end Norm

attribute [fsym_norm] callIndirect_run List.map_cons List.map_nil StateT.run_set CNorm.run_callC CNorm.run_callMC CNorm.run_callRC CNorm.run_liftR
  CNorm.run_pickC CNorm.run_throw CNorm.throw_bind CNorm.run_get CNorm.run_modify CNorm.pick_assoc
  CNorm.liftMem_pure CNorm.liftMem_lift_pure CNorm.liftMem_lift_throw liftMem_bind liftMem_ite
  liftMem_throw
  atomicLoadC atomicStoreC atomicRmwC cmpxchgC atomicLoadAsC atomicStoreAsC atomicRmwAsC cmpxchgAsC
  cmpxchgWeakC atomicLoadUnorderedC atomicLoadUnorderedEncC atomicLoadUnorderedAsC atomicLoadPtrC
  atomicStorePtrC atomicXchgPtrC cmpxchgPtrC cmpxchgWeakPtrC

open Lean Meta Simp in
/-- The common continuation of the arms of an indirect call is pulled out
(`callIndirect_bind`): `callIndirect f [(c₁, x₁ >>= g), …] (d >>= g) = callIndirect f [(c₁, x₁),
…] d >>= g`, so the call is one command. A last arm `throw e` (a closed function type) is
`throw e >>= g` already. -/
simproc [fsym_norm] pullIndirect (Full.callIndirect _ _ _) := fun e => do
  let_expr Full.callIndirect α m f arms d := e | return .continue
  unless m.isAppOfArity ``Zig.ConcM 1 do return .continue
  -- the arms, a list literal
  let mut xs := #[]
  let mut l := arms
  while l.isAppOfArity ``List.cons 3 do
    xs := xs.push l.appFn!.appArg!
    l := l.appArg!
  unless l.isAppOfArity ``List.nil 1 && !xs.isEmpty do return .continue
  let mut g? : Option Expr := none
  let mut ys := #[]
  for a in xs do
    unless a.isAppOfArity ``Prod.mk 4 do return .continue
    let x := a.appArg!
    unless x.isAppOfArity ``Bind.bind 6 do return .continue
    let g := x.appArg!
    if let some g0 := g? then
      unless g0 == g do return .continue
    else g? := some g
    ys := ys.push (a.appFn!.appArg!, x.getArg! 4)
  let some g := g? | return .continue
  let β := (← inferType (ys[0]!.2)).appArg!
  let tgt := m.appArg!
  let cβ ← mkAppM ``Zig.ConcM #[tgt, β]
  -- the last arm without the continuation
  let d' ← if d.isAppOfArity ``Bind.bind 6 && d.appArg! == g then pure (d.getArg! 4)
    else if d.isAppOfArity ``MonadExcept.throw 5 then
      mkAppOptM ``MonadExcept.throw #[none, ← mkAppM ``Zig.ConcM #[tgt], none, β, d.appArg!]
    else return .continue
  unless ← isDefEq (← inferType d') cβ do return .continue
  let pairTy ← mkAppM ``Prod #[mkConst ``Zig.Ptr, cβ]
  let mut lst ← mkAppOptM ``List.nil #[pairTy]
  for (c, y) in ys.reverse do
    lst ← mkAppOptM ``List.cons #[pairTy, ← mkAppOptM ``Prod.mk #[none, none, c, y], lst]
  let call ← mkAppOptM ``Full.callIndirect #[β, m, f, lst, d']
  let rhs ← mkAppM ``Bind.bind #[call, g]
  let pf ← mkAppOptM ``Full.callIndirect_bind #[tgt, β, α, f, lst, d', g]
  let pf ← mkEqSymm pf
  return .done { expr := rhs, proof? := some (← mkExpectedTypeHint pf (← mkEq e rhs)) }

/-! ## Atomic rules

The thread rules of the atomic ops on an owned word (`FTTriple`: the concurrent backend and the
thread logics; the `W` rules for a word under any location, MM-21), and the sequential partial
rules (`FTriple`, `FLogic.partial`). -/

attribute [fsym] FTTriple.atomicLoadUnorderedEnc FTTriple.cmpxchgPtr FTTriple.atomicLoadPtr
  FTTriple.cmpxchgHit FTTriple.atomicLoadAs FTTriple.atomicRmwAs FTTriple.atomicLoad
  FTTriple.atomicStore FTTriple.atomicRmw FTTriple.atomicXchgPtr FTTriple.cmpxchgWeakPtr
  FTTriple.atomicLoadUnordered
  FTTriple.atomicLoadW FTTriple.atomicStoreW FTTriple.atomicRmwW FTTriple.cmpxchgHitW
  FTTriple.atomicLoadAsW FTTriple.atomicRmwAsW FTTriple.atomicStoreAsW FTTriple.atomicXchgPtrW
  FTTriple.cmpxchgWeakPtrW FTTriple.atomicLoadUnorderedW FTTriple.atomicLoadUnorderedAsW

attribute [fsym] FTriple.atomicLoadUnorderedEnc FTriple.cmpxchgPtr FTriple.atomicLoadPtr
  FTriple.cmpxchgHit FTriple.atomicLoadAs FTriple.atomicRmwAs FTriple.atomicLoad FTriple.atomicStore
  FTriple.atomicXchgPtrW FTriple.cmpxchgWeakPtrW FTriple.atomicRmwW FTriple.atomicLoadUnorderedW
  FTriple.atomicRmw FTriple.atomicXchgPtr FTriple.cmpxchgWeakPtr FTriple.atomicLoadUnordered

-- The oracle's choice at an owned word (`AtomicRules.lean`, `CTriple.pick_one`): the one option
-- of a load, a store, an RMW or a strong `cmpxchg`, both of a weak one. `fsym` tries them before
-- `C.pick` (every choice).
attribute [fsym] CTriple.pick_load CTriple.pick_loadE CTriple.pick_rmw CTriple.pick_rmwE
  CTriple.pick_store CTriple.pick_storeE CTriple.pick_cas CTriple.pick_casPtr CTriple.pick_weakCas
  CTriple.pick_weakCasPtr CTriple.pick_unordered CTriple.pick_unorderedE
  CTriple.pick_loadW CTriple.pick_loadWE CTriple.pick_rmwW CTriple.pick_rmwWE CTriple.pick_storeW
  CTriple.pick_storeWE CTriple.pick_casW CTriple.pick_casPtrW CTriple.pick_weakCasW
  CTriple.pick_weakCasPtrW CTriple.pick_unorderedW CTriple.pick_unorderedWE

-- A pick with its op and the rest of the program (a bind rule: its premises are the triples of
-- the resumptions, which the walk goes on with): a weak pointer `cmpxchg`'s two outcomes, the
-- spurious failure from the pick's `Mem.MsgCov`.
attribute [fsym] CTriple.weakCasPtr_bind

end Zig.Full.Auto
