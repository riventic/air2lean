import ZigLean.Conc.TimedSched
import ZigLean.Conc.Call

/-!
Selected Zig16 public-call bridge candidate. These source-shaped values mirror the
audited AIR field/tag semantics, but have no Enc instances and are not substituted for
actual generated types. Translator signature/layout recognition remains unsupported.
Only an explicit awake/no-cancellation TimedSched environment admits clock operations.
-/
namespace Zig.TimedCall

inductive Clock where
  | real | awake | boot | cpuProcess | cpuThread
  deriving DecidableEq, Repr

structure Timestamp where
  nanoseconds : BitVec 96
  deriving DecidableEq, Repr

structure Duration where
  nanoseconds : BitVec 96
  deriving DecidableEq, Repr

structure ClockTimestamp where
  raw : Timestamp
  clock : Clock

structure ClockDuration where
  raw : Duration
  clock : Clock

inductive Timeout where
  | none
  | duration (value : ClockDuration)
  | deadline (value : ClockTimestamp)

/-- Interpret the source's signed i96; negative values are not silently unsigned-cast. -/
def checkedNanoseconds (value : BitVec 96) : Option Time.Timestamp :=
  if value.toInt < 0 then none else Time.Timestamp.ofNat value.toInt.toNat

/-- Selected timed fragment only: none and other clocks stay outside this adapter.
Duration addition overflow is independently rejected by Time.Timeout.resolve. -/
def checkedTimeout : Timeout → Option Time.Timeout
  | .none => none
  | .duration value =>
    if value.clock = .awake then
      (checkedNanoseconds value.raw.nanoseconds).map Time.Timeout.duration
    else none
  | .deadline value =>
    if value.clock = .awake then
      (checkedNanoseconds value.raw.nanoseconds).map Time.Timeout.deadline
    else none

/-- Actual public argument order: Clock.now(clock, io). A wrong clock fails closed. -/
def clockNow (clock : Clock) (_io : Io) : TimedSched.Program Timestamp :=
  if clock = .awake then
    .observe fun now => .done ⟨BitVec.ofNat 96 now.nanoseconds⟩
  else .fail .unspecified

/-- Actual public runtime argument order after comptime T specialization: io,p,e,timeout.
Return reason is deliberately hidden. The continuation is retained by Program.wait and
cannot run while the selected kernel registration is waiting. Canceled is excluded only
by the interpreter's explicit environment premise, never reclassified as timeout. -/
def futexWaitTimeout (_io : Io) (pointer : Ptr) (expected : BitVec 32)
    (timeout : Timeout) : TimedSched.Program (Except ErrName Unit) :=
  match checkedTimeout timeout with
  | none => .fail .unspecified
  | some selected => .wait pointer expected selected (fun _ => .done (.ok ()))

theorem wrong_clock_rejected (io : Io) :
    clockNow .real io = .fail .unspecified := rfl

theorem unbounded_not_selected : checkedTimeout .none = none := rfl

/-- This is a shape theorem about the bridge, not scheduler completion or correspondence. -/
theorem timed_wait_retains_continuation (io : Io) (p : Ptr) (expected : BitVec 32)
    (source : Timeout) (selected : Time.Timeout)
    (h : checkedTimeout source = some selected) :
    futexWaitTimeout io p expected source =
      .wait p expected selected (fun _ => .done (.ok ())) := by
  simp only [futexWaitTimeout, h]

end Zig.TimedCall
