import BigEndian.Conc.V0_17_0.X64.Gen

/-! T03: the model of `concurrency.zig` (atomics, futexes, threads, the allocator model) on
`concurrency_native.zig`'s inputs, one line per case in its format, from the translation of one
export (`BigEndian.Conc.V0_17_0.X64.Gen`; one per Zig version, 0.17.0 and 0.15.2, and target,
s390x-linux and mips64-linux, big endian, and x86_64-linux, little endian; `Futex.lean` adds the
futex case of 0.15.2). It is written for 0.17.0 on x86_64-linux; the other modules are that one
with the version and target renamed (`concurrency.sh`, `scripts/fixtures.py instance`). Each
concurrent case runs under 24 scheduler oracles from the translation's initial memory and must
give the same result under every one; the line is that result. -/

open Zig BigEndian.Conc.V0_17_0.X64

namespace BigEndian.Conc.V0_17_0.X64.Run

/-- The line of `x` under 24 scheduler oracles: their common result (`f` formats a value), or
`schedule-dependent`. -/
def runAll {α : Type} (f : α → String) (x : ConcM Tgt α) : String :=
  let rs := (List.range 24).map fun seed =>
    match (Sched.run ⟨.any, .available⟩ dispatch 2000 (fun turn => seed + turn * 7) x
        (mem0 .fresh)).run with
    | some (.ok (v, _)) => f v
    | some (.error e) => s!"error {repr e}"
    | none => "none"
  match rs with
  | r :: rest => if rest.all (· == r) then r else "schedule-dependent"
  | [] => "none"

def bv {n : Nat} (v : BitVec n) : String := toString v.toNat
def ebv {n : Nat} : Except ErrName (BitVec n) → String
  | .ok v => bv v
  | .error e => s!"error.{e}"

end BigEndian.Conc.V0_17_0.X64.Run
