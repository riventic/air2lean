import ZigLean.Basic


namespace Audit

opaque airAsm_1434560075 : BitVec 32

structure rdtscLowLocals where
  deriving Inhabited

inductive rdtscLowExit where
  | ret (v : BitVec 32)

def rdtscLow  : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i0 ← pure (airAsm_1434560075)
    pure (.ret i0)) : Zig.M rdtscLowLocals rdtscLowExit).run' (default : rdtscLowLocals)
  match e with
  | .ret v => pure v

structure sameTickLocals where
  deriving Inhabited

inductive sameTickExit where
  | ret (v : Bool)

def sameTick  : Zig.Result (Bool) := do
  let e ← ((do
    let i0 ← Zig.call (rdtscLow )
    let i1 ← Zig.call (rdtscLow )
    let i2 ← pure (i0 == i1)
    pure (.ret i2)) : Zig.M sameTickLocals sameTickExit).run' (default : sameTickLocals)
  match e with
  | .ret v => pure v

end Audit

/-! Counterexample (docs/architecture-audit/trust-chain.md, finding 4): natively `sameTick`
returns `false` (the time-stamp counter advances between two `asm volatile ("rdtsc")`), but the
generated model makes both reads the same `opaque` term, so it provably returns `true`. -/
theorem Audit.sameTick_true : Audit.sameTick = pure true := by
  simp [Audit.sameTick, Audit.rdtscLow, Zig.call]
