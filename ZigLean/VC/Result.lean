import ZigLean.Lemmas

/-!
# Loop-free verification conditions for `Result`

The syntax is a proof AST, not a replacement runtime. `eval` uses the existing operations;
`vc` computes the obligations from the syntax and a requested postcondition. Primitive
safety conditions are generated, and modular calls require a proved contract. There is no
loop or recursion constructor: those need separately checked, explicitly annotated proofs.
Zig error-union values are ordinary values; `.panic` is a safety error.
-/

namespace Zig.VC

inductive ResultProgram : Type → Type 1 where
  | ret {α : Type} (value : α) : ResultProgram α
  | add {n : Nat} (left right : BitVec n) : ResultProgram (BitVec n)
  | widen {n : Nat} (value : BitVec n) (width : Nat) : ResultProgram (BitVec width)
  | guard (condition : Bool) : ResultProgram Unit
  | panic {α : Type} (error : Error) : ResultProgram α
  | call {α : Type} (label : String) (action : Result α) (pre : Prop) (post : α → Prop)
      (checked : pre → ∃ value, action = pure value ∧ post value) : ResultProgram α
  | bind {α β : Type} (first : ResultProgram α) (next : α → ResultProgram β) : ResultProgram β
  | branch {α : Type} (condition : Bool) (yes no : ResultProgram α) : ResultProgram α

namespace ResultProgram

def eval {α : Type} : ResultProgram α → Result α
  | .ret value => pure value
  | .add left right => Zig.add false left right
  | .widen value width => Zig.intCast false false width value
  | .guard condition => if condition then pure () else throw Error.panic
  | .panic error => throw error
  | .call _ action _ _ _ => action
  | .bind first next => eval first >>= fun value => eval (next value)
  | .branch condition yes no => if condition then eval yes else eval no

/-- The complete compositional obligation for the accepted AST and requested result. -/
def vc {α : Type} (program : ResultProgram α) (post : α → Prop) : Prop :=
  match program with
  | .ret value => post value
  | .add (n := n) left right => left.toNat + right.toNat < 2 ^ n ∧ post (left + right)
  | .widen (n := n) value width => n ≤ width ∧ post (value.setWidth width)
  | .guard condition => condition = true ∧ post ()
  | .panic _ => False
  | .call _ _ pre summary _ => pre ∧ ∀ value, summary value → post value
  | .bind first next => vc first (fun value => vc (next value) post)
  | .branch condition yes no => if condition then vc yes post else vc no post

/-- Every discharged VC gives an actual safe return, rather than only a no-panic claim. -/
theorem sound {α : Type} (program : ResultProgram α) :
    ∀ post, vc program post → ∃ value, eval program = pure value ∧ post value := by
  induction program with
  | ret value =>
    intro post hp
    exact ⟨value, rfl, hp⟩
  | add left right =>
    intro post hp
    refine ⟨left + right, ?_, hp.2⟩
    simp only [eval, Zig.add_unsigned]
    rw [if_neg (Nat.not_le_of_lt hp.1)]
  | widen value width =>
    intro post hp
    exact ⟨value.setWidth width, Zig.intCast_unsigned_widen value width hp.1, hp.2⟩
  | guard condition =>
    intro post hp
    exact ⟨(), by simp [eval, hp.1], hp.2⟩
  | panic error =>
    intro post hp
    exact hp.elim
  | call label action pre summary checked =>
    intro post hp
    obtain ⟨value, hr, hs⟩ := checked hp.1
    exact ⟨value, hr, hp.2 value hs⟩
  | bind first next ihFirst ihNext =>
    intro post hp
    obtain ⟨value, hr, hn⟩ := ihFirst _ hp
    obtain ⟨result, hr', hpost⟩ := ihNext value post hn
    exact ⟨result, by simp only [eval, hr, pure_bind, hr'], hpost⟩
  | branch condition yes no ihYes ihNo =>
    intro post hp
    cases condition with
    | false => exact ihNo post hp
    | true => exact ihYes post hp

/-- A user contract generates this implication; its proof is still required. -/
def obligation {α : Type} (pre : Prop) (program : ResultProgram α) (post : α → Prop) : Prop :=
  pre → vc program post

theorem verify {α : Type} {pre : Prop} {program : ResultProgram α} {post : α → Prop}
    (proof : obligation pre program post) :
    pre → ∃ value, eval program = pure value ∧ post value :=
  fun hp => sound program post (proof hp)

end ResultProgram

end Zig.VC
