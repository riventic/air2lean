import LangLongTail.TlsPointers

/-! L12: the translated `tls_pointers.zig` against `probe_tls_pointers.zig`'s native output.

    lake env lean --run tests/roadmap/lang-long-tail/ModelTlsPointers.lean <native output>

(with the compiled `LangLongTail.TlsPointers` of a version on `LEAN_PATH`, as `check.sh` does)
runs the probe's calls in order on one memory, from `mem0 .fresh`, under 16 schedules, and
fails unless every schedule prints exactly the native lines. It also requires `leakedSlot`, which
reads a dead thread's instance through a pointer, to throw `.illegal` under every schedule, and
two semantic mutants (one instance shared by every thread; instances that outlive their thread)
to change an outcome. -/

open TlsPointers Zig

def env : Env := ⟨.any, .available⟩

/-- The probe's `main`: its calls in order, in one run. -/
def probeMain : ConcM Tgt (List String) := do
  let a ← perThread
  let b ← ConcM.liftMem (mainOnly 3)
  let c ← ConcM.liftMem (mainOnly 100)
  let d ← perThread
  let eu (r : Except ErrName (BitVec 32)) := match r with
    | .ok v => s!"{v.toNat}"
    | .error e => s!"error.{e}"
  pure [s!"perThread {eu a}", s!"mainOnly 3 {b.toNat}", s!"mainOnly 100 {c.toNat}",
    s!"perThread {eu d}"]

def linesWith (d : Tgt → ConcM Tgt Unit) (seed : Nat) : List String :=
  match (Sched.run env d 400 (fun turn => seed + turn * 7) probeMain (mem0 .fresh)).run with
  | some (.ok (lines, _)) => lines
  | some (.error e) => [s!"model-error {repr e}"]
  | none => ["model-none"]

/-- Mutant: every thread uses the main thread's instances (no per-thread instances). -/
def sharedDispatch : Tgt → ConcM Tgt Unit
  | .leakSlot a => discard (ConcM.liftMem (leakSlot a))
  | .worker a => discard (ConcM.liftMem (worker a))

/-- Mutant: a thread's instances outlive it (no `tlsExit`). -/
def immortalDispatch : Tgt → ConcM Tgt Unit
  | .leakSlot a => do ConcM.liftMem (tlsEnter tlsInit); discard (ConcM.liftMem (leakSlot a))
  | .worker a => do ConcM.liftMem (tlsEnter tlsInit); discard (ConcM.liftMem (worker a))

def leakedIllegal (d : Tgt → ConcM Tgt Unit) (seed : Nat) : Bool :=
  match (Sched.run env d 400 (fun turn => seed + turn * 7) leakedSlot (mem0 .fresh)).run with
  | some (.error .illegal) => true
  | _ => false

def main (args : List String) : IO UInt32 := do
  let [path] := args | IO.eprintln "usage: ModelTlsPointers.lean <native output>"; return 2
  let native := (← IO.FS.lines path).toList.filter (· ≠ "")
  let mut ok := true
  for seed in List.range 16 do
    let model := linesWith dispatch seed
    unless model == native do
      ok := false
      IO.eprintln s!"tls_pointers: schedule {seed}: the model differs from the native output"
      for m in model do IO.eprintln s!"  model:  {m}"
      for n in native do IO.eprintln s!"  native: {n}"
    unless leakedIllegal dispatch seed do
      ok := false
      IO.eprintln s!"tls_pointers: schedule {seed}: leakedSlot does not throw .illegal"
  -- Each mutant changes an outcome under some schedule.
  unless (List.range 16).any (fun seed => linesWith sharedDispatch seed != native) do
    ok := false
    IO.eprintln "tls_pointers: the shared-instance mutant survives"
  unless (List.range 16).any (fun seed => !leakedIllegal immortalDispatch seed) do
    ok := false
    IO.eprintln "tls_pointers: the immortal-instance mutant survives"
  if ok then
    IO.println s!"tls_pointers: {native.length} native lines match the model under 16 schedules; leakedSlot is .illegal; 2 mutants killed"
    return 0
  return 1
