import ZigLean.Sep.Full.Auto
import ZigLean.Sep.Full.Pinned

/-!
# `fsym` rules for byte-range claims (`docs/sep-full-state.md` §Byte-range claims)

A claim `bclaim b lo hi t` is the union of its bytes' claims, so the planner treats claims like
regions without bytes (`docs/proof-automation.md` §Planner extensions):

* a claim of the postcondition is **carved** out of a claim of the state of the same block and
  tag that covers it (`claim_split3`, bounds by the arithmetic solver);
* when no claim of the state covers it, **adjacent claims** of the state are joined first
  (`claim_join`);
* **leftover claims** are dropped (`claim_drop`, `pclaim_drop`, `@[fsym_drop]`): a claim owns no bytes, and a
  dropped claim is never minted again, so dropping one only forgets that its bytes are exclusive.

`pclaim p lo hi t` unfolds to `bclaim b lo hi t` with the fact `p.block = some b`. Lending,
returning and revoking tagged claims (`EUpd.lendC`, `EUpd.returnC`, `EUpd.revokeC`) are ghost
updates an invariant proof applies by hand, as for tagged shares.
-/

namespace Zig.Full

open FAssn

section Rules

variable {b : BlockId} {lo m hi a c : Nat} {t : STag}

/-- **Carve a claim** at `a` and `c` (`bclaim_split` twice). -/
theorem claim_split3 (h1 : lo ≤ a) (h2 : a ≤ c) (h3 : c ≤ hi) :
    EUpd (bclaim b lo hi t) (bclaim b lo a t ⋆ (bclaim b a c t ⋆ bclaim b c hi t)) :=
  EUpd.of_imp fun r h => by
    rw [← bclaim_split (b := b) (t := t) h1 (Nat.le_trans h2 h3), ← bclaim_split (b := b) (t := t) h2 h3] at h
    exact h

/-- **Join adjacent claims** (`bclaim_split`). -/
theorem claim_join {m' : Nat} (e : m = m') (h1 : lo ≤ m) (h2 : m' ≤ hi) :
    EUpd (bclaim b lo m t ⋆ bclaim b m' hi t) (bclaim b lo hi t) := by
  subst e; exact Auto.atom_eq (bclaim_split h1 h2)

/-- **Drop a claim**: it owns no bytes and no knowledge. -/
theorem claim_drop {R : FAssn} : EUpd (bclaim b lo hi t ⋆ R) R :=
  EUpd.trans (EUpd.of_imp fun _ h => sep_comm h) (EUpd.drop fun _ h => ⟨h.1, h.2.1⟩)

end Rules

/-- **Drop a pointer's claim** (one whose block the state has not opened, e.g. the released
bytes' claim of a shrink, `FAllocInv.relBytes`). -/
theorem pclaim_drop {p : Ptr} {lo hi : Nat} {t : STag} {R : FAssn} : EUpd (pclaim p lo hi t ⋆ R) R :=
  EUpd.trans (EUpd.of_imp fun _ h => sep_comm h) (EUpd.drop fun _ h => pclaim_ghost h)

attribute [fsym_drop] claim_drop pclaim_drop

namespace Auto

open Lean Meta Elab Tactic

def claimArgs? (e : Expr) : Option (Array Expr) :=
  if e.isAppOfArity ``Zig.Full.bclaim 4 then some e.getAppArgs else none

def mkClaim (b lo hi t : Expr) : Expr := mkAppN (mkConst ``Zig.Full.bclaim) #[b, lo, hi, t]

/-- The claim `q` (block, bounds, tag) carved out of a claim of the state that covers it. -/
def carveClaim (st : St) (q : Array Expr) (reserved : Array Expr) : TacticM (Option (St × Expr)) := do
  for i in [0:st.ats.size] do
    if reserved.contains st.ats[i]! then continue
    let some x := claimArgs? st.ats[i]! | continue
    let s0 ← saveState
    try
      unless ← (withReducible (isDefEq x[0]! q[0]!) <&&> withReducible (isDefEq x[3]! q[3]!)) do
        throwError "block"
      let some h1 ← proveArith (← mkAppM ``LE.le #[x[1]!, q[1]!]) (quick := true) | throwError "lo"
      let some h2 ← proveArith (← mkAppM ``LE.le #[q[1]!, q[2]!]) (quick := true) | throwError "range"
      let some h3 ← proveArith (← mkAppM ``LE.le #[q[2]!, x[2]!]) (quick := true) | throwError "hi"
      let h ← mkAppOptM ``claim_split3 #[x[0]!, x[1]!, x[2]!, q[1]!, q[2]!, x[3]!, h1, h2, h3]
      let mid := mkClaim x[0]! q[1]! q[2]! x[3]!
      let st ← st.step #[i] #[mkClaim x[0]! x[1]! q[1]! x[3]!, mid, mkClaim x[0]! q[2]! x[2]! x[3]!] h
      return some (st, mid)
    catch ex =>
      trace[fsym] "claim carve: {ex.toMessageData}"
      s0.restore
  return none

/-- Join two adjacent claims of the state (same block and tag, the second from the first's end). -/
def joinClaims (st : St) (reserved : Array Expr) : TacticM (Option St) := do
  for i in [0:st.ats.size] do
    if reserved.contains st.ats[i]! then continue
    let some x := claimArgs? st.ats[i]! | continue
    for j in [0:st.ats.size] do
      if i == j || reserved.contains st.ats[j]! then continue
      let some y := claimArgs? st.ats[j]! | continue
      unless x[0]! == y[0]! && x[3]! == y[3]! do continue
      let s0 ← saveState
      try
        let some e ← proveArith (← mkEq x[2]! y[1]!) (quick := true) | throwError "adjacent"
        let some h1 ← proveArith (← mkAppM ``LE.le #[x[1]!, x[2]!]) (quick := true) | throwError "lo"
        let some h2 ← proveArith (← mkAppM ``LE.le #[y[1]!, y[2]!]) (quick := true) | throwError "hi"
        let h ← mkAppOptM ``claim_join #[x[0]!, x[1]!, x[2]!, y[2]!, x[3]!, y[1]!, e, h1, h2]
        return some (← st.step #[i, j] #[mkClaim x[0]! x[1]! y[2]! x[3]!] h)
      catch ex =>
        trace[fsym] "claim join: {ex.toMessageData}"
        s0.restore
  return none

/-- **The claims planner**: each determined claim of the postcondition is carved out of a claim
of the state, joining adjacent claims of the state when none covers it. -/
def planClaims (st : St) (qats : Array Expr) : TacticM St := do
  let mut st := st
  let mut reserved : Array Expr := #[]
  for a in qats do
    let a ← instantiateMVars a
    let some q := claimArgs? a | continue
    if a.hasExprMVar then continue
    if st.ats.any (fun x => x == a && !reserved.contains x) then reserved := reserved.push a; continue
    let mut done := false
    for _ in [0:16] do
      if let some (st', x) ← carveClaim st q reserved then
        st := st'; reserved := reserved.push x; done := true; break
      let some st' ← joinClaims st reserved | break
      st := st'
    unless done do trace[fsym] "claims: no claim of the state covers {a}"
  return st

/-- The claims planner (`@[fsym_plan]`). -/
@[fsym_plan] def claimsPlanner : Planner where
  heads := #[``Zig.Full.bclaim]
  run := planClaims

end Auto

end Zig.Full
