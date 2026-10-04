import ScheduleSearch

open DiffTest

private def capped : String := "{\"fail\":\"Zig.Error.capped\"}"
private def illegal : String := "{\"fail\":\"Zig.Error.illegal\"}"

private def check (name : String) (actual expected : String) : IO Unit :=
  unless actual == expected do
    throw (IO.userError s!"{name}: expected {expected}, got {actual}")

/-- Three early scheduler decisions must all change. The later weak CAS succeeds on zero;
choosing one merely repeats it, extending the trace up to the mock's fuel. -/
private def retryTree (o : Nat → Nat) : String × Array Nat := Id.run do
  let mut opts := #[2, 2, 2]
  let mut failures := 0
  while failures < 128 do
    opts := opts.push 2
    if o (3 + failures) % 2 == 0 then
      let target := o 0 % 2 == 1 && o 1 % 2 == 1 && o 2 % 2 == 1
      return (if target then "wanted" else "other", opts)
    failures := failures + 1
  return ("diverge", opts)

private def finiteTree (o : Nat → Nat) : String × Array Nat :=
  (if o 0 % 3 == 2 then "wanted" else "other", #[3])

private def raceTree (o : Nat → Nat) : String × Array Nat :=
  (if o 0 % 2 == 0 then illegal else "other", #[2])

-- These regressions exercise the actual harness search, without invoking translated programs.
def main : IO Unit := do
  check "old deepest-first enumeration reaches its cap"
    (searchSchedulesWith 64 1 32 128 retryTree "wanted") capped
  check "FIFO combines several early decisions before retry suffixes"
    (searchSchedulesWith 64 32 32 128 retryTree "wanted") "wanted"
  check "production bounds find the synthetic witness" (searchSchedules retryTree "wanted") "wanted"
  check "probe queue exhaustion resumes DFS"
    (searchSchedulesWith 8 4 0 4 finiteTree "wanted") "wanted"
  check "overlength probe omission resumes DFS"
    (searchSchedulesWith 8 4 4 0 finiteTree "wanted") "wanted"
  check "finite no-witness search returns first result"
    (searchSchedulesWith 8 4 4 4 finiteTree "absent") "other"
  check "shared cap includes the initial execution"
    (searchSchedulesWith 1 4 4 4 finiteTree "wanted") capped
  check "data race survives a cap"
    (searchSchedulesWith 1 4 4 4 raceTree "absent") illegal
  check "a witnessed match wins over an earlier race"
    (searchSchedulesWith 8 4 4 4 raceTree "other") "other"
  check "one-leaf exhausted tree is not a cap"
    (searchSchedulesWith 1 4 4 4 (fun _ => ("other", #[1])) "absent") "other"
  check "zero budget runs no oracle"
    (searchSchedulesWith 0 4 4 4 (fun _ => panic! "oracle must not run") "absent") capped
  let pending := scheduleProbePrefixes 3 4 #[] (Array.replicate 100 10) []
  unless pending.length == 3 && pending.all (fun p => p.size <= 4) do
    throw (IO.userError "probe metadata exceeded queue/prefix bounds")
  let seeded := scheduleProbePrefixes 3 8 #[] #[1, 1, 1, 2, 2] [#[7], #[8]]
  unless seeded == [#[7], #[8], #[0, 0, 0, 1]] do
    throw (IO.userError "prefilled queue lost its capacity or FIFO order across deterministic choices")
  let bounded := scheduleProbePrefixes 20 2 #[] (Array.replicate 100 2) []
  unless bounded.length == 2 && bounded.all (fun p => p.size <= 2) do
    throw (IO.userError "probe prefix-length limit was not enforced")
  let nonbinary := scheduleProbePrefixes 20 4 #[2, 3] #[5, 5, 5] []
  unless nonbinary.length == 4 && nonbinary.all (fun p =>
      p.getD 0 0 == 2 && p.getD 1 0 == 3 && p.getD 2 0 > 0 && p.getD 2 0 < 5) do
    throw (IO.userError "probe alternatives lost a nonbinary prefix or selected an invalid option")
  IO.println "schedule search regressions passed"
