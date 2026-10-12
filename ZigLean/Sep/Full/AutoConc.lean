import ZigLean.Sep.Full.AutoRules
import ZigLean.Sep.Full.Extent
import ZigLean.Sep.Full.Dispatch
import ZigLean.Sep.Full.AtomicRules
import ZigLean.Mem.Repr

/-!
# The concurrent backend of `fsym`: rules for `CTriple` (`docs/proof-automation.md`)

`fsym` walks a concurrent function read in the caller's thread (`CTriple P x Q`,
`ZigLean/Sep/Full/Conc.lean`) as it walks a sequential one, with these rules:

* **Structural steps** (`C.step`, `C.stepAll`, `C.ret`, `C.ex_sep`, `C.lift_sep`, …), the
  `CTriple` counterparts of `Auto.step` & co. A `MemM` command `ConcM.liftMem c` is executed by a
  sequential rule about `c`: total (`@[fsym]`, `FTotalTriple`) or partial (`FTriple`: the atomic
  rules, since `CTriple` is partial correctness). A `CTriple` rule (`C.stepC`) executes a
  concurrent command: a call through a table (`Table.call`, `CVTable.dispatch`, the
  `CTriple.tableCall` reading of a call site), or a loop with its invariant (`CTriple.loop`).
* **An atomic op's oracle choice** is `0` in one thread (`C.pick`, `CTriple.pick_bind`).
* **Indirect calls**: a generated chain `if f = c₁ then x₁ else … else throw .illegal` is folded
  into `callIndirect f [(c₁, x₁), …]` (`callIndirect_fold_one'`/`cons'`, the `Prop` forms of
  `callIndirect_fold_one`/`cons`), and the common continuation of its arms is pulled out
  (`callIndirect_bind`), so the call is one command. `fsym` executes it by a `CTriple` rule for
  the table call, or reads the arm that the facts select (`callIndirect_pos`/`_neg`).
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
  simp only [Zig.subSat, Zig.clamp, Zig.val, Bool.false_eq_true, ↓reduceIte, BitVec.toNat_ofInt]
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

end Seq

attribute [fsym_norm] optPtrAddr_some optPtrAddr_none
attribute [fsym_arith] Array.size_replicate Zig.subWrap Zig.addWrap Zig.mulWrap BitVec.sub_self
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

/-- A `MemM` command proved by a sequential partial rule on the part `P₀`, framed by `R`. -/
theorem step {c : MemM α} {f : α → ConcM Tgt β} {Q₀ : α → FAssn} (r : FTriple P₀ c Q₀)
    (k : ∀ v, CTriple (Q₀ v ⋆ R) (f v) Q) : CTriple (P₀ ⋆ R) (ConcM.liftMem c >>= f) Q :=
  CTriple.bind (CTriple.liftMem r.frame) k

/-- A `MemM` command proved by a sequential partial rule on the whole precondition. -/
theorem stepAll {c : MemM α} {f : α → ConcM Tgt β} {Q₀ : α → FAssn} (r : FTriple P c Q₀)
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

/-- **An atomic op's oracle choice**: `0` in one thread. -/
theorem pick {count : Mem → Nat} {f : Nat → ConcM Tgt β} (h : CTriple P (f 0) Q) :
    CTriple P ((ConcM.sync (.pick count) : ConcM Tgt Nat) >>= f) Q :=
  CTriple.pick_bind h

/-- The arm of an indirect call that the function pointer selects. -/
theorem callIndirect_pos {f p : Ptr} {x : ConcM Tgt β} {arms : List (Ptr × ConcM Tgt β)}
    (h : f = p) : Full.callIndirect f ((p, x) :: arms) = x := by
  subst h; simp [Full.callIndirect]

/-- Past an arm that the function pointer does not select. -/
theorem callIndirect_neg {f p : Ptr} {x : ConcM Tgt β} {arms : List (Ptr × ConcM Tgt β)}
    (h : ¬ f = p) : Full.callIndirect f ((p, x) :: arms) = Full.callIndirect f arms := by
  simp [Full.callIndirect, h]

/-- No arm left: the call is illegal. -/
theorem callIndirect_nil (f : Ptr) : (Full.callIndirect f [] : ConcM Tgt β) = throw .illegal := rfl

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

/-- The innermost arm of a generated indirect call (`callIndirect_fold_one` after `simp` has
turned the condition `f == c` into `f = c`). -/
theorem callIndirect_fold_one' {f c : Ptr} {x : ConcM Tgt α} :
    (if f = c then x else (throw .illegal : ConcM Tgt α)) = Full.callIndirect f [(c, x)] := by
  simp only [Full.callIndirect, beq_iff_eq]

/-- One more arm of a generated indirect call. -/
theorem callIndirect_fold_cons' {f c : Ptr} {x : ConcM Tgt α} {arms : List (Ptr × ConcM Tgt α)} :
    (if f = c then x else Full.callIndirect f arms) = Full.callIndirect f ((c, x) :: arms) := by
  simp only [Full.callIndirect, beq_iff_eq]

end Norm

attribute [fsym_norm] CNorm.run_callC CNorm.run_callMC CNorm.run_callRC CNorm.run_liftR
  CNorm.run_pickC CNorm.run_throw CNorm.throw_bind CNorm.run_get CNorm.run_modify CNorm.pick_assoc
  CNorm.liftMem_pure CNorm.liftMem_lift_pure CNorm.liftMem_lift_throw liftMem_bind liftMem_ite
  liftMem_throw callIndirect_fold_one' callIndirect_fold_cons'
  atomicLoadC atomicStoreC atomicRmwC cmpxchgC atomicLoadAsC atomicStoreAsC atomicRmwAsC cmpxchgAsC
  cmpxchgWeakC atomicLoadUnorderedC atomicLoadUnorderedEncC atomicLoadUnorderedAsC atomicLoadPtrC
  atomicStorePtrC atomicXchgPtrC cmpxchgPtrC cmpxchgWeakPtrC

open Lean Meta Simp in
/-- The common continuation of the arms of an indirect call is pulled out
(`callIndirect_bind`): `callIndirect f [(c₁, x₁ >>= g), …] = callIndirect f [(c₁, x₁), …] >>= g`,
so the call is one command. -/
simproc [fsym_norm] pullIndirect (Full.callIndirect _ _) := fun e => do
  let_expr Full.callIndirect α m _ f arms := e | return .continue
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
  let pairTy ← mkAppM ``Prod #[mkConst ``Zig.Ptr, ← mkAppM ``Zig.ConcM #[tgt, β]]
  let mut lst ← mkAppOptM ``List.nil #[pairTy]
  for (c, y) in ys.reverse do
    lst ← mkAppOptM ``List.cons #[pairTy, ← mkAppOptM ``Prod.mk #[none, none, c, y], lst]
  let call ← mkAppOptM ``Full.callIndirect #[β, m, none, f, lst]
  let rhs ← mkAppM ``Bind.bind #[call, g]
  let pf ← mkAppOptM ``Full.callIndirect_bind #[tgt, β, α, f, lst, g]
  let pf ← mkEqSymm pf
  return .done { expr := rhs, proof? := some (← mkExpectedTypeHint pf (← mkEq e rhs)) }

/-! ## Atomic rules (partial: the concurrent backend and `FLogic.partial`) -/

attribute [fsym] FTriple.atomicLoadUnorderedEnc FTriple.cmpxchgPtr FTriple.atomicLoadPtr
  FTriple.cmpxchgHit FTriple.atomicLoadAs FTriple.atomicLoad FTriple.atomicStore
  FTriple.atomicXchgPtrW FTriple.cmpxchgWeakPtrW FTriple.atomicRmwW FTriple.atomicLoadUnorderedW

end Zig.Full.Auto
