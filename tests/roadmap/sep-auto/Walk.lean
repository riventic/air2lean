import ZigLean.Sep.Full.Auto
import ZigLean.Sep.Full.AutoPrim

/-!
# `fsym` on small programs (`docs/proof-automation.md`)

A walk through loads, checked arithmetic and stores; an assertion-level `if` decided by the
facts; returns that carve a region and raise a share's bound; generated functions of
constructors evaluated (a union's tag, a loop's test), a callee's result by its components, a
caller's rule about a generated loop. The programs are written by hand in the shape the
translator generates.
-/

namespace SepAuto.Walk

open Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto

/-- Add `n` to the word at `ctx`, checked; return the new value. -/
def bump (ctx : Ptr) (n : BitVec 64) : MemM (BitVec 64) := do
  let e ← Zig.load (BitVec 64) 8 ctx
  let e' ← StateT.lift (Zig.add false e n)
  Zig.store (α := BitVec 64) 8 ctx e'
  pure e'

theorem bump_spec (ctx : Ptr) (e : Nat) (n : BitVec 64) (h : e + n.toNat < 2 ^ 64) :
    FTotalTriple (up (pts ctx 8 (BitVec.ofNat 64 e))) (bump ctx n)
      (fun r => ⟪r.toNat = e + n.toNat⟫ ⋆ up (pts ctx 8 (BitVec.ofNat 64 (e + n.toNat)))) := by
  fsym

/-- An `if` of the precondition that the facts decide. -/
theorem ite_pre (ctx : Ptr) (e : Nat) (n : BitVec 64) (X : FAssn) (h : e + n.toNat < 2 ^ 64) (he : 0 < e) :
    FTotalTriple (up (pts ctx 8 (BitVec.ofNat 64 e)) ⋆ (if e = 0 then X else emp)) (bump ctx n)
      (fun _ => up (pts ctx 8 (BitVec.ofNat 64 (e + n.toNat)))) := by
  fsym

/-- A return that carves a region: a prefix of `k` bytes, and the rest at `p + k` with any bytes
of the right size. -/
theorem carve (p : Ptr) (A S : Nat) (K : BlockKind) (bs : Array Byte) (k : Nat) (hk : k ≤ bs.size)
    (b : BlockId) (hb : p.block = some b) :
    FTotalTriple (up (regionIn p A S K 1 bs)) (pure () : MemM Unit)
      (fun _ => up (regionIn p A S K 1 (bs.extract 0 k)) ⋆
        FAssn.ex fun t : Array Byte => ⟪t.size = bs.size - k⟫ ⋆ up (regionIn (p.add k) A S K 1 t)) := by
  fsym

/-- A return that raises a share's bound with another share of the block (fractions kept). -/
theorem raise (b : BlockId) (q₁ q₂ : Frac) (k₁ k₂ k : Nat) (h : k ≤ k₂) :
    FTotalTriple (bshare b q₁ k₁ ⋆ bshare b q₂ k₂) (pure () : MemM Unit)
      (fun _ => bshare b q₁ k ⋆ FAssn.ex fun q => bshare b q k₂) := by
  fsym

/-- A precondition that holds of `some` only. -/
def onlySome (p : Ptr) : Option (BitVec 32) → FAssn
  | none => ⟪False⟫
  | some v => up (pts p 4 v)

/-- The `none` case is unreachable (its precondition is `⟪False⟫` after the split): closed,
although its command has no rule. -/
theorem false_pre (p : Ptr) (o : Option (BitVec 32)) :
    FTotalTriple (onlySome p o)
      (match o with
        | none => Zig.load (BitVec 64) 8 p
        | some _ => pure 0)
      (fun _ => FAssn.ex fun v : BitVec 32 => up (pts p 4 v)) := by
  fsym

/-- An item of a vector value (`Zig.vindex`, `AutoPrim.vindex_step`). -/
theorem vindex_item (a : Vector (BitVec 64) 2) :
    FTotalTriple emp (StateT.lift (Zig.vindex a (1 : BitVec 64)) : MemM (BitVec 64))
      (fun r => ⟪r = a[1]⟫) := by
  fsym

/-- A union and its tag, as the translator writes them (`ResetMode.tag`): functions by `match`. -/
inductive Mode where
  | free_all
  | retain (n : Nat)

inductive ModeTag where
  | free_all
  | retain

def Mode.tag : Mode → ModeTag
  | .free_all => .free_all
  | .retain _ => .retain

/-- A loop's exits and its test (`again19`). -/
inductive Exit where
  | rep
  | brk

def again : Exit → Bool
  | .rep => true
  | .brk => false

/-- **A `match` on a generated function of a constructor** (ledger #40), in a body over its
locals (`(match … : StateT σ MemM α).run s`): the function's value, so the `match` reduces. -/
theorem match_tag (p : Ptr) (n : Nat) (v : BitVec 64) (s : Nat) :
    FTotalTriple (up (pts p 8 v))
      (StateT.run (match Mode.tag (.retain n) with
        | .free_all => throw .panic
        | .retain => StateT.lift (Zig.load (BitVec 64) 8 p) : StateT Nat MemM (BitVec 64)) s)
      (fun r => ⟪r.1 = v⟫ ⋆ up (pts p 8 v)) := by
  fsym

/-- **A post's `if` on a generated function of a constructor** (ledger #37: a loop step's post
`if again r.1 then inv r.2 else post r.2`): decided at the return. -/
theorem post_again (p : Ptr) (v : BitVec 64) (X : FAssn) :
    FTotalTriple (up (pts p 8 v)) (pure (Exit.rep, v) : MemM (Exit × BitVec 64))
      (fun r => if again r.1 then up (pts p 8 r.2) else X) := by
  fsym

/-- A callee that returns an exit and a value. -/
def callee : MemM (Exit × Nat) := pure (.brk, 4)

/-- Its rule fixes the exit by a projection of the result. -/
theorem callee_spec {P : FAssn} : FTotalTriple P callee (fun r => ⟪r.1 = .brk ∧ r.2 = 4⟫ ⋆ P) := by
  unfold callee; fsym

/-- **A `match` on a projection of a callee's result** (ledger #39) that the callee's post fixes
(`r.1 = .brk`): the result by its fields, so the `match` reduces (no unreachable branch left). -/
theorem match_proj (p : Ptr) (v : BitVec 64) :
    FTotalTriple (up (pts p 8 v))
      (do
        let r ← callee
        match r.1 with
        | .brk => pure r.2
        | .rep => throw .panic)
      (fun x => ⟪x = 4⟫ ⋆ up (pts p 8 v)) := by
  fsym [callee_spec]

/-- A generated loop over its locals: its `MonoBind` instance is the definition's own proof
(`cnt._proof_1`). -/
def cnt.loop6 : MM Nat Bool := do
  let s ← get
  if s == 0 then pure false else
    set (s - 1)
    pure true

def cnt (n : Nat) : MemM Nat := do
  let r ← (Zig.loop cnt.loop6 (fun b : Bool => b)).run n
  pure r.2

/-- **A caller's rule about a generated loop** (ledger #54): its statement elaborates the loop's
instance anew, a different proof than the definition's; proofs are equal for matching. The rule
is a local of the proof (`have`). -/
theorem loop_rule (n : Nat)
    (hl : ∀ k, FTotalTriple emp ((Zig.loop cnt.loop6 (fun b : Bool => b)).run k) (fun r => ⟪r.2 = 0⟫)) :
    FTotalTriple emp (cnt n) (fun r => ⟪r = 0⟫) := by
  have hl' := hl
  clear hl
  unfold cnt
  fsym [hl']

/-- **A loop rule stated at `StateT σ MemM`** (ledger #4), not at the generated monad `MM σ`: the
monads agree up to the reducible `MM`. -/
theorem loop_rule_statet (n : Nat)
    (hl : ∀ k, FTotalTriple emp ((Zig.loop (m := StateT Nat MemM) cnt.loop6 (fun b : Bool => b)).run k)
      (fun r => ⟪r.2 = 0⟫)) :
    FTotalTriple emp (cnt n) (fun r => ⟪r = 0⟫) := by
  unfold cnt
  fsym [hl]

end SepAuto.Walk
