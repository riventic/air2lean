/-!
# The environment installed in `Zig.Mem` (E03)

The types that `Zig.Mem` carries for the bound OS primitives: handles, the operations record
`Ops`, request histories, boundary events and the installed `Host` (default: nothing open).
Data only, with no assumption: the contract that clients rely on (`Zig.Env.Contract`, premise
ENV-01) and the operations' meaning are in `ZigLean/Env.lean` and `ZigLean/Env/Linux.lean`. A
program or theorem that only carries the default host therefore depends on no environment
premise.
-/
namespace Zig.Env

abbrev Handle := Nat

/-- The enumerated environment error cases. A contract selects an allowed subset. -/
inductive IoError where
  | wouldBlock
  | brokenPipe
  | noSpaceLeft
  | accessDenied
  | inputOutput
  | connectionReset
  deriving DecidableEq, Repr

/-- Environment operations. Results depend only on the supplied state, which is arbitrary.
`monotonicNow` and `wallNow` are distinct observations (nanoseconds); only the monotonic
clock carries an ordering contract. -/
structure Ops (σ : Type) where
  monotonicNow : σ → Nat
  wallNow : σ → Int
  isOpen : σ → Handle → Bool
  /-- `.ok []` for a positive request means end of input. -/
  read : σ → Handle → Nat → Except IoError (List UInt8) × σ
  /-- `.ok n` reports that the first `n` bytes were accepted. -/
  write : σ → Handle → List UInt8 → Except IoError Nat × σ
  close : σ → Handle → σ

/-- Observable boundary events, in order. -/
inductive Event where
  | wrote (h : Handle) (bytes : List UInt8)
  | failed (h : Handle) (e : IoError)
  | closed (h : Handle)
  /-- A read of `h` that returned `bytes` (`[]`: end of input). -/
  | received (h : Handle) (bytes : List UInt8)
  deriving DecidableEq, Repr

/-- One environment request, as the replay records it. -/
inductive Req where
  | read (h : Handle) (max : Nat)
  | write (h : Handle) (bytes : List UInt8)
  | close (h : Handle)
  deriving DecidableEq, Repr

abbrev Hist := List Req

/-- No handle is open; reads and writes fail with `inputOutput`. The default host. -/
def Ops.closedAll : Ops Hist where
  monotonicNow _ := 0
  wallNow _ := 0
  isOpen _ _ := false
  read hist _ _ := (.error .inputOutput, hist)
  write hist _ _ := (.error .inputOutput, hist)
  close hist _ := hist

/-- The environment installed in `Zig.Mem`: operations, current state, event log. -/
structure Host where
  ops : Ops Hist := Ops.closedAll
  env : Hist := []
  log : List Event := []

instance : Inhabited Host := ⟨{}⟩

/-- The operations are functions, so they are shown opaquely. -/
instance : Repr Host where
  reprPrec h _ := f!"\{ ops := <oracle>, env := {repr h.env}, log := {repr h.log} }"

end Zig.Env
