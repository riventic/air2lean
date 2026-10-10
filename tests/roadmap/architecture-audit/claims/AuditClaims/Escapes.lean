import AuditClaims.Gen

/-!
H4 (docs/architecture-audit/claims.md): elaborator escape hatches in a contract. Each theorem
here is kernel-checked and true, but its statement rests on a constant whose kernel meaning is
not what runs or what a reader sees:

* `specLoop` is a `partial def`: the kernel has an opaque constant with no defining equation,
  so a hypothesis about it constrains nothing the reader can check;
* `modelInc` carries `implemented_by`: the kernel sees `x + 1`, compiled code runs `fastInc`.

The audit's policy must refuse both (`unexpected-opaque`, `unexpected-compiler-redirection`):
the module still passes kernel replay (S1), so the refusal rests on the replayed environment.
-/

namespace AuditClaims

partial def specLoop (x : Nat) : Nat := if x = 0 then 0 else specLoop (x - 1)

def fastInc (x : BitVec 8) : BitVec 8 := x

@[implemented_by fastInc] def modelInc (x : BitVec 8) : BitVec 8 := x + 1

/-- A hypothesis about a `partial def`: the kernel cannot unfold `specLoop`. -/
theorem partial_hyp (_h : specLoop 3 = 0) : root 3 = pure 4 := rfl

/-- The right-hand side is a constant whose compiled code differs from its kernel value. -/
theorem redirected_spec : root 3 = pure (modelInc 3) := rfl

end AuditClaims
