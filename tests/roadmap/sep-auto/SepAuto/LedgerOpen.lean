import ZigLean.Sep.Full.AutoAll
import ZigLean.Sep.Full.LockRules
import ZigLean.Sep.Full.Event

/-!
# Open engine-ledger rows: the smallest goal `fsym` does not close

One example for each open row of `assurance/engine-ledger.json` that has a small repro. Each is
an **expected failure**: the goal is true, `fsym` leaves it, and `fail_if_success` keeps the
example green until the engine closes it. When a row is fixed its example here fails; then the
goal moves to the regressions (`Walk.lean`, `Update.lean`, `WP*.lean`, …) as a theorem and the row
closes.
-/

namespace SepAuto.LedgerOpen

open Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto

set_option linter.unusedVariables false

/-! ## Row 3: a rule or a goal in a generic logic `L.T` -/

/-- The goal is in a generic logic. -/
example (L : FLogic) (c : MemM Nat) (P : FAssn) (h : L.T P c (fun r => ⟪r = 0⟫ ⋆ P)) : True := by
  fail_if_success
    have : L.T P (do let r ← c; pure (r + 1)) (fun r => ⟪r = 1⟫ ⋆ P) := by
      fsym [h]
      done
  trivial

/-- The rule is for every logic, the goal is total (the fields of `FAllocSpec L`). -/
example (c : MemM Nat) (P : FAssn) (h : ∀ L : FLogic, L.T P c (fun r => ⟪r = 0⟫ ⋆ P)) : True := by
  fail_if_success
    have : FTotalTriple P (do let r ← c; pure (r + 1)) (fun r => ⟪r = 1⟫ ⋆ P) := by
      fsym [h]
      done
  trivial

/-- … and partial. -/
example (c : MemM Nat) (P : FAssn) (h : ∀ L : FLogic, L.T P c (fun r => ⟪r = 0⟫ ⋆ P)) : True := by
  fail_if_success
    have : FTriple P (do let r ← c; pure (r + 1)) (fun r => ⟪r = 1⟫ ⋆ P) := by
      fsym [h]
      done
  trivial

/-- … and with the logic given: the rule's conclusion is `FLogic.total.T …`, not unfolded. -/
example (c : MemM Nat) (P : FAssn) (h : ∀ L : FLogic, L.T P c (fun r => ⟪r = 0⟫ ⋆ P)) : True := by
  fail_if_success
    have : FTotalTriple P (do let r ← c; pure (r + 1)) (fun r => ⟪r = 1⟫ ⋆ P) := by
      fsym [h FLogic.total]
      done
  trivial

/-! ## Row 61: a rule whose precondition has an `if` that the state holds in parts -/

/-- The `if` behind a definition, as the arena's `relBytes`. -/
def rel (A : FAssn) (n len : Nat) : FAssn := if n < len then A else emp

/-- The state holds `A`, the rule asks for `rel A n len`, the facts do not decide `n < len`: no
case split on the rule's condition. (With `rel A n len` itself in the state the rule applies.) -/
example (c : MemM Nat) (P A : FAssn) (n len : Nat)
    (h : FTotalTriple (P ⋆ rel A n len) c (fun r => ⟪r = 0⟫ ⋆ P ⋆ rel A n len)) : True := by
  fail_if_success
    have : FTotalTriple (A ⋆ P) (do let r ← c; pure r) (fun r => ⟪r = 0⟫ ⋆ P ⋆ A) := by
      fsym [h]
      done
  trivial

/-! ## Rows 64, return-bool-split: updates at a return -/

/-- A cell with some value. -/
def Pub (p : Ptr) : FAssn := fun r => (FAssn.ex fun v => apts p v) r

theorem pub {p : Ptr} {v : BitVec 64} (_h : v.toNat < 10) : EUpd (apts p v) (Pub p) :=
  EUpd.of_imp fun _ hr => ⟨v, hr⟩

theorem pub_lt {p q : Ptr} {v w : BitVec 64} {n len : Nat} (_h : n < len) :
    EUpd (apts p v ⋆ apts q w) (Pub p ⋆ Pub q) :=
  EUpd.of_imp fun _ hr => by
    obtain ⟨r₁, r₂, hd, rfl, h1, h2⟩ := hr
    exact ⟨r₁, r₂, hd, rfl, ⟨v, h1⟩, ⟨w, h2⟩⟩

theorem pub_ge {p : Ptr} {v : BitVec 64} {n len : Nat} (_h : ¬ n < len) :
    EUpd (apts p v) (Pub p) :=
  EUpd.of_imp fun _ hr => ⟨v, hr⟩

/-- Row 64: the state and the post have an undecided `if`; the entailment splits it, the updates
are not tried again in the two cases (`hc : n < len ⊢ EUpd (apts p v ⋆ apts q w) (Pub p ⋆ if n <
len then Pub q else emp)` is left). -/
example (p q : Ptr) (v w : BitVec 64) (n len : Nat) : True := by
  fail_if_success
    have : FTotalTriple (apts p v ⋆ (if n < len then apts q w else emp)) (pure ())
        (fun _ => Pub p ⋆ (if n < len then Pub q else emp)) := by
      fsym [pub_lt (n := n) (len := len), pub_ge (n := n) (len := len)]
      done
  trivial

/-- A post by cases of the returned `Bool`. -/
def PostB (p : Ptr) (n len : Nat) : Bool → FAssn
  | true => ⟪n ≤ len⟫ ⋆ Pub p
  | false => ⟪len < n⟫ ⋆ Pub p

/-- Row return-bool-split: the result is `decide (n ≤ len)`, undecided; the post's `match` on it
is not split. -/
example (p : Ptr) (v : BitVec 64) (n len : Nat) : True := by
  fail_if_success
    have : FTotalTriple (apts p v) (pure (decide (n ≤ len)) : MemM Bool)
        (fun r => PostB p n len r) := by
      fsym [pub (v := v)]
      done
  trivial

/-- … and without an update. -/
example (P : FAssn) (n len : Nat) : True := by
  fail_if_success
    have : FTotalTriple P (pure (decide (n ≤ len)) : MemM Bool)
        (fun r => (match r with | true => ⟪n ≤ len⟫ | false => ⟪len < n⟫) ⋆ P) := by
      fsym
      done
  trivial

/-! ## Row 66: regions -/

/-- An empty region beside the whole one. -/
example (p : Ptr) (A S : Nat) (K : BlockKind) (bs : Array Byte) (hb : 0 < bs.size) : True := by
  fail_if_success
    have : FTotalTriple (up (regionIn p A S K 1 bs)) (pure () : MemM Unit)
        (fun _ => (FAssn.ex fun pad : Array Byte =>
            ⟪pad.size = 0⟫ ⋆ up (regionIn p A S K 1 pad)) ⋆ up (regionIn p A S K 1 bs)) := by
      fsym
      done
  trivial

/-- A carve at the start of a region, to a larger alignment that the start has. -/
example (p : Ptr) (A S : Nat) (K : BlockKind) (bs : Array Byte) (k : Nat) (hk : k ≤ bs.size)
    (hp : 8 ∣ p.off.toNat) (hA : 8 ∣ A) : True := by
  fail_if_success
    have : FTotalTriple (up (regionIn p A S K 1 bs)) (pure () : MemM Unit)
        (fun _ => up (regionIn p A S K 8 (bs.extract 0 k)) ⋆
          FAssn.ex fun t : Array Byte =>
            ⟪t.size = bs.size - k⟫ ⋆ up (regionIn (p.add k) A S K 1 t)) := by
      fsym
      done
  trivial

/-! ## The protocol backend: rows fsym-or-witness-order, fsym-forward-bool-fact -/

section WP
open Zig.Conc Zig.Conc.Proto

attribute [local irreducible] Proto.WP

/-- Row fsym-or-witness-order: the witness is fixed by the first disjunct (`x := a`), the later
conjunct `R x` is then not provable; the second disjunct is not tried. -/
example {Tgt γ : Type} (P : Proto Tgt γ) (t : ThreadId) (G : ThreadId → γ) (m : Mem) (n : Nat)
    (R : Nat → Prop) (a b : Nat) (hR : R b) : True := by
  fail_if_success
    have : P.WP t (pure ()) (fun _ _ _ _ => ∃ x, (x = a ∨ x = b) ∧ R x) G m n := by
      fsym
      done
  trivial

end WP

section Os
open Zig.Conc Zig.Conc.Proto Zig.Full.FLock Zig.Os

attribute [local irreducible] Proto.WP

variable {Tgt γ : Type} {L : FLock γ} {K : FPrim γ} {P : Proto Tgt γ}
  {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}

/-- Row fsym-forward-bool-fact: the futex wait of a lock's slow path, with the word's fact
(`hP.wordAt hi`) and the wait's rule as terms: the error case and the wait's result are left. -/
example (hP : L.Fits K P U ok) (hcost : P.cost = none) (t : ThreadId) (g : γ)
    (hg : L.ph g = .spin) (hok : ok g) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hi : P.inv (upd G t g) m) : True := by
  fail_if_success
    have : P.WP t (Linux.futex_4arg L.ptr 0x80 (BitVec.ofNat 32 L.c) none)
        (fun r G' m' d' => (∃ w : WaitResult, w ≠ .timedOut ∧ r = Linux.waitCode w) ∧ d' < d ∧
          m'.current = t ∧ P.inv (upd G' t g) m') G m d := by
      fsym [hP.wordAt hi, wp_osWait hP rfl hg hok hi]
      done
  trivial

end Os

end SepAuto.LedgerOpen
