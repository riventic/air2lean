import ZigLean.Sep.Full.AutoAll
import Proofs.Basic.Gen
import Proofs.Pointers.Gen
import Proofs.Errors.Gen

/-!
Verification conditions (P02, `docs/vcs.md`) of committed generated code: `Proofs/Basic/Gen.lean`,
`Proofs/Pointers/Gen.lean` and `Proofs/Errors/Gen.lean`, generated from `examples/`. A contract is
a full-state triple of the generated function (of its lifted program for a pure `Result`
function), and its obligations are the goals that the walk of `fsym` over the generated body
leaves; `fsym.report` gives each its origin. Nothing here is written by hand except the
statements and the closing of the obligations.
-/

namespace VCExtract

open Zig Zig.Full FAssn

/-! ## A contracted loop-free function receives complete obligations

The walk discharges the safety obligation of `tardiness` (the `sub` precondition, from the branch
condition) and its result obligations, so its report is complete. `FTotalTriple.result_spec`
gives the `Result` contract. -/

/-- info: fsym-report {"residuals":[],"schemaVersion":1,"status":"complete"} -/
#guard_msgs in
theorem tardiness_total (a b : BitVec 32) :
    FTotalTriple emp (StateT.lift (Basic.tardiness a b) : MemM (BitVec 32))
      (fun v => ⟪v.toNat = a.toNat - b.toNat⟫) := by
  set_option fsym.report true in fsym

theorem tardiness_contract (a b : BitVec 32) :
    ∃ v, Basic.tardiness a b = pure v ∧ v.toNat = a.toNat - b.toNat :=
  (tardiness_total a b).result_spec

/-! ## A wrong contract leaves an unprovable obligation

The contract `v = a - b` forgets the saturation at zero. The walk does not repair it: exactly the
non-taken branch remains. -/

/--
error: unsolved goals
a b : BitVec 32
hc : ¬gt false a b = true
⊢ 0#32 = a - b
-/
#guard_msgs in
example (a b : BitVec 32) :
    FTotalTriple emp (StateT.lift (Basic.tardiness a b) : MemM (BitVec 32))
      (fun v => ⟪v = a - b⟫) := by
  fsym

-- That remaining obligation is false (a = 1, b = 2), so this contract has no proof at all.
theorem wrong_obligation_false :
    ¬ ∀ a b : BitVec 32, ¬ gt false a b = true → (0 : BitVec 32) = a - b := by
  intro h
  exact absurd (h 1 2 (by decide)) (by decide)

theorem wrong_contract_false :
    ¬ ∀ a b : BitVec 32, ∃ v, Basic.tardiness a b = pure v ∧ v = a - b := by
  intro h
  obtain ⟨v, hv, he⟩ := h 1 2
  have hrun : Basic.tardiness 1 2 = pure 0 := rfl
  rw [hrun] at hv
  cases hv
  exact absurd he (by decide)

/-! ## Compositional calls use proved contracts

`fsym [tardiness_total]` executes the call of `tardiness` by its contract: its result is the
fact `x✝³` below, not its body. Without bounds, the obligations of `weightedTardiness` are the
overflow of its `add` (the last goal) and of its `mul` (the second), each split off as the
premise of its step rule (`hc✝`, `hc`), and its result at the return (the first), where the
product is the fact `x✝` of `mul_step`. -/

/--
error: unsolved goals
j : Basic.Job
start : BitVec 32
hc✝ : start.toNat + j.duration.toNat < 2 ^ 32
x✝⁶ : BitVec 32
x✝⁵ : x✝⁶.toNat = start.toNat + j.duration.toNat
x✝⁴ : BitVec 32
x✝³ : x✝⁴.toNat = x✝⁶.toNat - j.due.toNat
x✝² : BitVec 32
x✝¹ : x✝².toNat = j.weight.toNat
hc : x✝⁴.toNat * x✝².toNat < 2 ^ 32
x : BitVec 32
x✝ : x.toNat = x✝⁴.toNat * x✝².toNat
⊢ x.toNat = (start.toNat + j.duration.toNat - j.due.toNat) * j.weight.toNat

case h
j : Basic.Job
start : BitVec 32
hc✝ : start.toNat + j.duration.toNat < 2 ^ 32
x✝⁴ : BitVec 32
x✝³ : x✝⁴.toNat = start.toNat + j.duration.toNat
x✝² : BitVec 32
x✝¹ : x✝².toNat = x✝⁴.toNat - j.due.toNat
x : BitVec 32
x✝ : x.toNat = j.weight.toNat
hc : ¬x✝².toNat * x.toNat < 2 ^ 32
⊢ x✝².toNat * x.toNat < 2 ^ 32

case h
j : Basic.Job
start : BitVec 32
hc : ¬start.toNat + j.duration.toNat < 2 ^ 32
⊢ start.toNat + j.duration.toNat < 2 ^ 32
-/
#guard_msgs in
example (j : Basic.Job) (start : BitVec 32) :
    FTotalTriple emp (StateT.lift (Basic.weightedTardiness j start) : MemM (BitVec 32))
      (fun r => ⟪r.toNat = (start.toNat + j.duration.toNat - j.due.toNat) * j.weight.toNat⟫) := by
  fsym [tardiness_total]

-- The same statement as `Proofs/Basic/Proofs.lean`'s `weightedTardiness_ok`, from its VCs.
theorem weightedTardiness_contract (j : Basic.Job) (start : BitVec 32)
    (h1 : start.toNat + j.duration.toNat < 2 ^ 32)
    (h2 : (start.toNat + j.duration.toNat - j.due.toNat) * j.weight.toNat < 2 ^ 32) :
    ∃ r, Basic.weightedTardiness j start = pure r ∧
      r.toNat = (start.toNat + j.duration.toNat - j.due.toNat) * j.weight.toNat := by
  refine FTotalTriple.result_spec ?_
  fsym [tardiness_total]
  all_goals simp_all

/-! ## Error returns

A returned Zig error is an obligation of the postcondition at its return, apart from the safety
obligations: the walk of `parseDigit` leaves one goal per return, the two error returns (each
under its branch condition `hc`) and the digit. -/

/--
error: unsolved goals
c : BitVec 8
hc : lt false c 48#8 = true
⊢ Except.error "NotDigit" = if c.toNat < 48 ∨ 57 < c.toNat then Except.error "NotDigit" else Except.ok (c - 48)

c : BitVec 8
hc✝ : ¬lt false c 48#8 = true
hc : gt false c 57#8 = true
⊢ Except.error "NotDigit" = if c.toNat < 48 ∨ 57 < c.toNat then Except.error "NotDigit" else Except.ok (c - 48)

c : BitVec 8
hc✝ : ¬lt false c 48#8 = true
hc : ¬gt false c 57#8 = true
x : BitVec 8
x✝ : x.toNat + (48#8).toNat = c.toNat
⊢ Except.ok x = if c.toNat < 48 ∨ 57 < c.toNat then Except.error "NotDigit" else Except.ok (c - 48)
-/
#guard_msgs in
example (c : BitVec 8) :
    FTotalTriple emp (StateT.lift (Errors.parseDigit c) : MemM _)
      (fun v => ⟪v = if c.toNat < 48 ∨ 57 < c.toNat then .error "NotDigit" else .ok (c - 48)⟫) := by
  fsym

theorem parseDigit_total (c : BitVec 8) :
    FTotalTriple emp (StateT.lift (Errors.parseDigit c) : MemM _)
      (fun v => ⟪v = if c.toNat < 48 ∨ 57 < c.toNat then .error "NotDigit" else .ok (c - 48)⟫) := by
  fsym
  all_goals
    simp_all [Zig.lt, Zig.gt, BitVec.ult]
    try (simp only [show ¬(c.toNat < 48 ∨ 57 < c.toNat) by omega, ↓reduceIte]; congr 1; bv_omega)

theorem parseDigit_contract (c : BitVec 8) :
    ∃ v, Errors.parseDigit c = pure v ∧
      v = if c.toNat < 48 ∨ 57 < c.toNat then .error "NotDigit" else .ok (c - 48) :=
  (parseDigit_total c).result_spec

-- `catch 0`: the callee's error return, from its contract, is consumed through the checked
-- unwrap primitives, whose preconditions are safety obligations.
theorem digitOrZero_contract (c : BitVec 8) :
    ∃ v, Errors.digitOrZero c = pure v ∧
      v = if c.toNat < 48 ∨ 57 < c.toNat then 0 else c - 48 := by
  refine FTotalTriple.result_spec ?_
  fsym [parseDigit_total]
  all_goals (by_cases h : c.toNat < 48 ∨ 57 < c.toNat <;> simp_all [Zig.isNonErr, Zig.isErr] <;> omega)

/-! ## Memory effects

Here the walk discharges every obligation: overflow from `fits`, ownership and the heap
postcondition by the planner.

Each contract has a strength example (`ZigLean/Sep/Full/Strength.lean`): the legacy statement that
it replaces, on every `Mem.FSeqPlain` memory (the memories a run reaches, `Mem.init_fseq`, no
stack budget), and total instead of partial. The examples are in
`tests/roadmap/strength-log/Vcs.lean`. -/

section Memory

theorem addTo_contract (p : Ptr) (delta : BitVec 32) (old : BitVec 64)
    (fits : old.toNat + (delta.setWidth 64).toNat < 2 ^ 64) :
    FTotalTriple (up (pts p 8 old)) (Pointers.addTo p delta)
      (fun _ => up (pts p 8 (old + delta.setWidth 64))) := by
  fsym

-- The frame rule preserves a separate client resource.
example (p : Ptr) (delta : BitVec 32) (old : BitVec 64) (R : FAssn)
    (fits : old.toNat + (delta.setWidth 64).toNat < 2 ^ 64) :
    FTotalTriple (up (pts p 8 old) ⋆ R) (Pointers.addTo p delta)
      (fun _ => up (pts p 8 (old + delta.setWidth 64)) ⋆ R) :=
  (addTo_contract p delta old fits).frame

-- Two cells: the planner splits the heap, so `swap p q` needs no separate ownership proof.
theorem swap_contract (p q : Ptr) (x y : BitVec 32) :
    FTotalTriple (up (pts p 4 x) ⋆ up (pts q 4 y)) (Pointers.swap p q)
      (fun _ => up (pts p 4 y) ⋆ up (pts q 4 x)) := by
  fsym

-- The same function on one cell (`Proofs/Pointers/Sep.lean` proves it with explicit memories).
theorem swapSelf_contract (p : Ptr) (old : BitVec 32) :
    FTotalTriple (up (pts p 4 old)) (Pointers.swap p p) (fun _ => up (pts p 4 old)) := by
  fsym

-- A functional result next to the heap effect. Pointer `==` compares addresses
-- (`ptrEqAddr_raw`): two provenance-free pointers are equal iff their addresses are.
theorem same_contract (p q : Ptr) :
    FTotalTriple ⟪p.block = none ∧ q.block = none⟫ (Pointers.same p q)
      (fun r => ⟪r = decide (p.off = q.off)⟫ ⋆ emp) := by
  fsym

/-! Mutated contracts: each leaves an obligation that the walk cannot close. -/

-- The overflow bound dropped: the `add` precondition is left.
/--
error: unsolved goals
case h
p : Ptr
delta : BitVec 32
x✝¹ x : BitVec 64
x✝ : x.toNat = delta.toNat
right✝ : 0 ≤ p.off
w✝ : BlockId
h✝ : p.block = some w✝
hc : ¬x✝¹.toNat + x.toNat < 2 ^ 64
⊢ x✝¹.toNat + x.toNat < 2 ^ 64
-/
#guard_msgs in
example (p : Ptr) (delta : BitVec 32) (old : BitVec 64) :
    FTotalTriple (up (pts p 8 old)) (Pointers.addTo p delta)
      (fun _ => up (pts p 8 (old + delta.setWidth 64))) := by
  fsym

-- The cells not swapped: the heap postcondition is left.
/--
error: unsolved goals
p q : Ptr
x✝² x✝¹ : BitVec 32
x✝ x : Unit
right✝¹ : 0 ≤ q.off
w✝¹ : BlockId
h✝¹ : q.block = some w✝¹
right✝ : 0 ≤ p.off
w✝ : BlockId
h✝ : p.block = some w✝
⊢ EUpd (up (pts q 4 x✝²) ⋆ up (pts p 4 x✝¹)) (up (pts p 4 x✝²) ⋆ up (pts q 4 x✝¹))
-/
#guard_msgs in
example (p q : Ptr) (x y : BitVec 32) :
    FTotalTriple (up (pts p 4 x) ⋆ up (pts q 4 y)) (Pointers.swap p q)
      (fun _ => up (pts p 4 x) ⋆ up (pts q 4 y)) := by
  fsym

-- The provenance premise dropped: pointers into blocks are not compared by address, and with
-- no block facts in the precondition (`FTotalTriple.ptrEqAddr_live` needs them) the comparison
-- is left.
/--
info: fsym: no rule for the command
  ptrEqAddr p q
with the precondition
  emp
---
error: unsolved goals
p q : Ptr
⊢ FLogic.total.T emp
    (ptrEqAddr p q >>= fun x =>
      (do
          let e ←
            (fun x => x.fst) <$> do
                let p ← pure (x, default)
                StateT.run (pure (Pointers.sameExit.ret p.fst)) p.snd
          match e with
            | Pointers.sameExit.ret v => pure v) >>=
        pure)
    fun r => ⟪r = decide (p.off = q.off)⟫ ⋆ emp
-/
#guard_msgs in
example (p q : Ptr) :
    FTotalTriple emp (Pointers.same p q) (fun r => ⟪r = decide (p.off = q.off)⟫ ⋆ emp) := by
  fsym

end Memory

/-! ## Loops request explicit invariants and variants; recursion needs a measure

The walk guesses no invariant: it stops at a generated loop, which is left as the request. It is
proved with the loop rules of `ZigLean/Sep/Full/Loop.lean` (`FTotalTriple.loop_ghost`,
`FTriple.loop`) and then given to callers as a contract. -/

/--
info: fsym: no rule for the command
  StateT.lift (StateT.run (loop (Basic.sum.loop7 xs (len xs)) Basic.sum.again7) { total := 0#64, local3 := 0#64 })
with the precondition
  emp
---
error: unsolved goals
xs : Array (BitVec 32)
⊢ FLogic.total.T emp
    (StateT.lift
        (StateT.run (loop (Basic.sum.loop7 xs (len xs)) Basic.sum.again7) { total := 0#64, local3 := 0#64 }) >>=
      fun x =>
      (StateT.lift do
          let e ←
            (fun x => x.fst) <$>
                StateT.run
                  (match x.fst with
                  | Basic.sumExit.br6 => do
                    let __do_lift ← get
                    let i24 ← pure __do_lift.total
                    pure (Basic.sumExit.ret i24)
                  | e => pure e)
                  x.snd
          match e with
            | Basic.sumExit.ret v => pure v
            | x => throw Error.panic) >>=
        pure)
    fun x => ⟪True⟫
-/
#guard_msgs in
example (xs : Array (BitVec 32)) :
    FTotalTriple emp (StateT.lift (Basic.sum xs) : MemM (BitVec 64)) (fun _ => ⟪True⟫) := by
  fsym

/--
info: fsym: no rule for the command
  StateT.run (loop (Pointers.sumTo.loop6 n x✝) Pointers.sumTo.again6) { acc := x✝, i := 0#32 }
with the precondition
  up (bytesAt x✝ A 8 BlockKind.stack (writeBytes (Array.replicate 8 Byte.undef) 0 (Enc.encode 0#64))) ⋆
    bauth b 8 BlockKind.stack Frac.one ⋆ plain
---
error: unsolved goals
n : BitVec 32
x✝ : Ptr
A : Nat
b : BlockId
left✝¹ : x✝.block = some b
left✝ : x✝.off = 0
right✝¹ : A % 8 = 0
x : Unit
right✝ : 0 ≤ x✝.off
h✝ : x✝.block = some b
⊢ FLogic.partial.T
    (up (bytesAt x✝ A 8 BlockKind.stack (writeBytes (Array.replicate 8 Byte.undef) 0 (Enc.encode 0#64))) ⋆
      bauth b 8 BlockKind.stack Frac.one ⋆ plain)
    (StateT.run (loop (Pointers.sumTo.loop6 n x✝) Pointers.sumTo.again6) { acc := x✝, i := 0#32 } >>= fun x =>
      (do
          let e ←
            (fun x => x.fst) <$>
                StateT.run
                  (match x.fst with
                  | Pointers.sumToExit.br5 => do
                    let i19 ← liftM (load (BitVec 64) 8 x✝)
                    pure (Pointers.sumToExit.ret i19)
                  | e => pure e)
                  x.snd
          free x✝
          match e with
            | Pointers.sumToExit.ret v => pure v
            | x => throw Error.panic) >>=
        pure)
    fun x => plain
-/
#guard_msgs in
example (n : BitVec 32) : FTriple plain (Pointers.sumTo n) (fun _ => plain) := by
  fsym

-- A recursive function is not unfolded: its call needs a contract proved by
-- `FTotalTriple.rec_group` with a measure (`Proofs/Pointers/Sep.lean`, `addDown_total`).
/--
info: fsym: no rule for the command
  Pointers.addDown p n
with the precondition
  up (pts p 8 x)
---
error: unsolved goals
p : Ptr
n : BitVec 32
x : BitVec 64
right✝ : 0 ≤ p.off
w✝ : BlockId
h✝ : p.block = some w✝
⊢ FLogic.total.T (up (pts p 8 x)) (Pointers.addDown p n >>= pure) fun x_1 => up (pts p 8 x)
-/
#guard_msgs in
example (p : Ptr) (n : BitVec 32) (x : BitVec 64) :
    FTotalTriple (up (pts p 8 x)) (Pointers.addDown p n) (fun _ => up (pts p 8 x)) := by
  fsym

end VCExtract
