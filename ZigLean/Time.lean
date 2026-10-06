/-! An independent, opt-in awake clock boundary. These premises describe a selected
environment; they do not establish correspondence with an operating system clock. -/
namespace Zig.Time

/-- One above the largest nonnegative signed-i96 timestamp. -/
def limit : Nat := 2 ^ 95

structure Timestamp where
  nanoseconds : Nat
  bounded : nanoseconds < limit

/-- Invalid values are rejected rather than wrapped or clamped. -/
def Timestamp.ofNat (n : Nat) : Option Timestamp :=
  if h : n < limit then some ⟨n, h⟩ else none

structure AwakeEnvironment where
  observe : Nat → Timestamp
  monotonic : ∀ i j, i ≤ j → (observe i).nanoseconds ≤ (observe j).nanoseconds

/-- Cancellation is excluded by an explicit selected-environment premise. -/
structure NoCancellation where
  requested : Nat → Bool
  absent : ∀ i, requested i = false

inductive Environment where
  | noClock
  | awake (clock : AwakeEnvironment) (policy : NoCancellation)

def defaultEnvNoClock : Environment := .noClock

/-- Only awake, nonnegative representable values enter this boundary. -/
inductive Timeout where
  | none
  | duration (ns : Timestamp)
  | deadline (expiry : Timestamp)

/-- Outer `none` rejects overflow; inner `none` is an unbounded wait. -/
def Timeout.resolve (now : Timestamp) : Timeout → Option (Option Timestamp)
  | .none => some Option.none
  | .deadline expiry => some (some expiry)
  | .duration ns => (Timestamp.ofNat (now.nanoseconds + ns.nanoseconds)).map some

theorem observations_do_not_decrease (env : AwakeEnvironment) (i : Nat) :
    (env.observe i).nanoseconds ≤ (env.observe (i + 1)).nanoseconds :=
  env.monotonic i (i + 1) (Nat.le_succ i)

end Zig.Time
