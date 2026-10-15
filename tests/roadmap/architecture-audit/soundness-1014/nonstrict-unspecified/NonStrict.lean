import ZigLean

/-!
# Audit 2026-10-14, finding S4: a non-strict protocol discharges `.unspecified`

`Proto.Safe` (`ZigLean/Conc/Logic.lean`) accepts every error leaf when `strict = false`:
`.leaf (some (.error e)) => P.strict = false ∨ e = .stackOverflow`. So `run_sound` reads
"every `ok` result satisfies `QM`" and says nothing about a run that throws. That is sound for
an error that stops the native program (`.panic`, a trap) or is illegal behaviour (`.illegal`).
It is not sound for `.unspecified` and `.unsupportedTimer`: the native program goes on and
returns a value (`docs/illegal-behavior.md`: "`.unspecified`: Zig leaves the result open. This
is not IB.").

`main` below is `@bitCast(u64, nan)` (`Float.toBits?`, `ZigLean/Float/Value.lean`), the
model of `nan.zig`. Natively it returns `0x7ff8000000000000` (no illegal behaviour; the bits of
a NaN are only unspecified). `main_never_returns` is proved with `run_sound`, in exactly the
shape of the published non-strict results (`Cancel.Group.cancelClient_spec`,
`Atomics.MPR.mpRelaxed_spec`): every result of every schedule satisfies `False`.

The same holds for any non-strict result: a path that the model ends with `.unspecified`
(a racing mixed-size atomic, a pointer `cmpxchg` whose identity and address disagree,
`@min(+0.0, -0.0)`, a timed wait without a clock) is dropped from the claim, while the native
run goes on.
-/

open Zig Zig.Conc

namespace Audit1014.NonStrict

/-- `@bitCast(u64, std.math.nan(f64))`. -/
def prog : MemM (BitVec 64) := StateT.lift (Zig.Float.toBits? (Zig.Float.nan : Zig.Float .f64))

/-- The program's `main`, a concurrent function that never syncs. -/
def main : ConcM Unit (BitVec 64) := ConcM.liftMem prog

/-- A trivial non-strict protocol (the default `strict := false`). -/
def proto : Proto Unit Unit where
  inv _ _ := True
  init _ _ := False
  fin _ := True

theorem prog_unspecified (m : Mem) : (prog.run m).run = some (.error .unspecified) := by
  rfl

theorem main_wp (n : Nat) (m : Mem) :
    proto.WP 0 main (fun _ _ _ _ => False) (fun _ => ()) m n :=
  Proto.WP.liftMem (fun _ _ => rfl) (fun a m' h => by
    rw [prog_unspecified] at h; cases h)

/-- **Every result of `main` satisfies `False`** (every oracle, every fuel): `main` "never
returns". Natively it returns the NaN's bits. -/
theorem main_never_returns (env : Env) (henv : env.spawn = .available) {fuel : Nat}
    {o : Nat → Nat} {v : BitVec 64} {m : Mem}
    (h : (Sched.run env (fun _ => pure ()) fuel o main {}).run = some (.ok (v, m))) : False := by
  obtain ⟨_, _, hq⟩ := proto.run_sound env (Proto.of_available henv) (fun _ => pure ()) (fun _ => ())
    (fun _ _ hg => hg.elim) (fun h => absurd h (by decide)) rfl (fun n => main_wp n _) h
  exact hq

end Audit1014.NonStrict

#print axioms Audit1014.NonStrict.main_never_returns
