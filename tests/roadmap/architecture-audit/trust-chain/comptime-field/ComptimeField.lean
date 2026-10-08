import ZigLean.Basic


namespace Audit

structure S where
  v : BitVec 32
  k : BitVec 32
  deriving Repr, Inhabited, DecidableEq

structure mkLocals where
  local1 : S
  deriving Inhabited

inductive mkExit where
  | ret (v : S)

def mk (p0 : BitVec 32) : Zig.Result (S) := do
  let e ← ((do
    modify (fun s => { s with local1 := { s.local1 with v := p0 } })
    pure (.ret (← get).local1)) : Zig.M mkLocals mkExit).run' (default : mkLocals)
  match e with
  | .ret v => pure v

structure sumLocals where
  deriving Inhabited

inductive sumExit where
  | ret (v : BitVec 32)

def sum (p0 : S) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← pure ((p0).v)
    let i2 ← Zig.add false (7 : BitVec 32) i1
    pure (.ret i2)) : Zig.M sumLocals sumExit).run' (default : sumLocals)
  match e with
  | .ret v => pure v

structure goLocals where
  s : S
  deriving Inhabited

inductive goExit where
  | ret (v : BitVec 32)

def go (p0 : BitVec 32) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i2 ← Zig.call (mk p0)
    modify (fun s => { s with s := i2 })
    let i5 ← pure (((← get).s).v)
    let i6 ← pure (Zig.addWrap i5 (1 : BitVec 32))
    modify (fun s => { s with s := { s.s with v := i6 } })
    let i8 ← pure ((← get).s)
    let i9 ← Zig.call (sum i8)
    pure (.ret i9)) : Zig.M goLocals goExit).run' (default : goLocals)
  match e with
  | .ret v => pure v

end Audit

/-! Counterexample (docs/architecture-audit/trust-chain.md, finding 9): in Zig `S.k` is the
`comptime` field `7` for every value of `S`, but the exporter lists it as a runtime field at
offset 0 (overlapping `v`), and the model gives `mk`'s result `k = 0`. -/
theorem Audit.mk_k_zero (x : BitVec 32) : Audit.mk x = pure { v := x, k := 0 } := by
  rfl
