import ZigLean.Os
import ZigLean.Conc.Sched

/-! T04 futex rows: the native observations of `futex.zig` (the `futex <case> <value>` rows of
`tests/roadmap/aarch64-abi/expected/<zig>/<triple>-<mode>.txt`) against the OS rows of
`ZigLean/Os/Futex.lean` (premises OSF-01, OSF-02; `docs/aarch64-abi.md` §Futex).

Each case of `cases` names the model's run of the same calls: `Os.Linux.futex_4arg`/`futex_3arg`
on aarch64-linux-gnu, `Os.Darwin.__ulock_wait2`/`__ulock_wait`/`__ulock_wake` on
aarch64-macos-none, under the scheduler (`Zig.Sched.runTrace`), over every schedule and every
choice of the oracle (`outcomes`; a choice among more than `width` options is cut to its first
`width`, which only removes outcomes). The model's rows are the same for every Zig version.

`lake env lean --run tests/roadmap/aarch64-abi/Futex.lean TRIPLE FILE` fails unless

* the file has exactly one well-formed row for every case of the profile, and no other `futex`
  row, and
* every observed value is an outcome of the model's run, except in a case of `refused`: there the
  model must refuse the call (`.illegal`, the documented conservative refusal of an address
  whose native result needs mapping knowledge), and the row is printed as refused, never as a
  match. A refused case that the model starts to answer fails the check (the list is stale).

The `mutex` row is the count that mutual exclusion forces, as the `litmus counters` row of
`Model.lean`: a native observation of the two calls under contention, not a run of the model. -/

open Zig Zig.Os

namespace T04Futex

/-! ## Every schedule of a run (as `tests/roadmap/os-threads/Check.lean`) -/

/-- Spawn targets are numbers; each case gives their bodies. -/
abbrev Tgt := Nat

/-- The next schedule after `pre` with the option counts `opts`, depth first. -/
def nextSchedule (pre opts : Array Nat) : Option (Array Nat) :=
  let rec go : Nat → Option (Array Nat)
    | 0 => none
    | j + 1 =>
      let c := pre.getD j 0
      if c + 1 < opts.getD j 0 then some (((Array.range j).map (pre.getD · 0)).push (c + 1))
      else go j
  go opts.size

def illegal : String := "Zig.Error.illegal"

/-- The distinct results of the schedules of `main` from `m0` (at most `cap` runs; at most the
first `width` options of each choice), sorted. An error is its name; out of fuel is `none`. -/
def outcomes (dispatch : Tgt → ConcM Tgt Unit) (main : ConcM Tgt String) (m0 : Mem := {})
    (fuel : Nat := 40) (cap : Nat := 4000) (width : Nat := 4) : List String :=
  let rec go : Nat → Array Nat → List String → List String
    | 0, _, acc => acc
    | k + 1, pre, acc =>
      let (out, opts) := Sched.runTrace { io := .any, spawn := .available } dispatch fuel
        (pre.getD · 0) main m0
      let s := match out with
        | none => "none"
        | some (.error e) => s!"{repr e}"
        | some (.ok (v, _)) => v
      let acc := if acc.contains s then acc else s :: acc
      match nextSchedule pre (opts.map (min · width)) with
      | some p => go k p acc
      | none => acc
  (go cap #[] []).mergeSort (· ≤ ·)

def noKids : Tgt → ConcM Tgt Unit := fun _ => pure ()

def lift {α : Type} (x : MemM α) : ConcM Tgt α := ConcM.liftMem x

/-! ## The probe's memory -/

/-- The futex word (`futex.zig`'s `word`, on the main thread's stack): block 0 of a fresh
memory, with the value `v`. -/
def word (v : BitVec 32) : ConcM Tgt Ptr := lift do
  let p ← alloc .stack 4 4
  store 4 p v
  pure p

def p0 : Ptr := ⟨some 0, 0⟩
/-- A waiter's return code, written before it ends: block 1. -/
def slot : Ptr := ⟨some 1, 0⟩
/-- A pointer at the numeric address `a`, into no block. -/
def addr (a : Int) : Ptr := ⟨none, a⟩

/-- A `timespec` on the stack. -/
def timespec (sec nsec : Int) : MemM Ptr := do
  let t ← alloc .stack 16 8
  store 8 t (BitVec.ofInt 64 sec)
  store 8 (t.add 8) (BitVec.ofInt 64 nsec)
  pure t

/-- A memory whose block 0 is the futex word (0, on a stack, at address 4096) with `n` threads
asleep at its key in the domain `shared`. -/
def asleep (n : Nat) (shared : Bool := false) : Mem := {
  blocks := #[{ bytes := Array.replicate 4 (.int 0), align := 4, kind := .stack, live := true,
                addr := 4096 }]
  waiters := (Array.range n).map fun i => (i + 1, ⟨shared, 4096⟩) }

def commas (xs : List Int) : String := if xs.isEmpty then "-" else ",".intercalate (xs.map toString)

/-! ## Linux (`futex.zig`'s `linuxRows`) -/

namespace Linux

open Zig.Os.Linux

/-- Bits 63 and 55 set: an address that no `access_ok` admits. -/
def kernel : Int := 2 ^ 63 + 2 ^ 55

/-- `FUTEX_WAIT` cases at a word that holds 1: the name, the timeout, the expected value and
the address (from the word's pointer). -/
def waits : List (String × Option (Int × Int) × BitVec 32 × (Ptr → Ptr)) := [
  ("mismatch", none, 0, id), ("mismatch_timed", some (0, 1000000), 0, id),
  ("timeout", some (0, 1000000), 1, id), ("timeout_zero", some (0, 0), 1, id),
  ("bad_nsec", some (0, 1000000000), 1, id), ("neg_nsec", some (0, -1), 1, id),
  ("neg_sec", some (-1, 0), 1, id), ("bad_nsec_mismatch", some (0, 1000000000), 0, id),
  ("bad_nsec_unaligned", some (0, 1000000000), 1, (·.add 1)),
  ("bad_nsec_kernel", some (0, 1000000000), 1, fun _ => addr kernel),
  ("unaligned", none, 1, (·.add 1)), ("unaligned2", none, 1, (·.add 2)),
  ("unaligned_kernel", none, 1, fun _ => addr (kernel + 1)), ("kernel", none, 1, fun _ => addr kernel),
  ("kernel_top", none, 1, fun _ => addr (2 ^ 64 - 4)), ("null", none, 1, fun _ => addr 0)]

/-- `FUTEX_WAKE` cases with nobody asleep: the name, `val` and the address. -/
def wakes : List (String × BitVec 32 × (Ptr → Ptr)) := [
  ("none", 1, id), ("none_val0", 0, id), ("none_max", 0x7fffffff, id), ("unaligned", 1, (·.add 1)),
  ("unaligned_kernel", 1, fun _ => addr (kernel + 1)), ("kernel", 1, fun _ => addr kernel),
  ("kernel_top", 1, fun _ => addr (2 ^ 64 - 4)), ("null", 1, fun _ => addr 0)]

/-- The op of a domain: `FUTEX_PRIVATE_FLAG` unless shared. -/
def op (cmd : BitVec 32) (shared : Bool) : BitVec 32 := if shared then cmd else cmd ||| FUTEX_PRIVATE

def code (r : BitVec 64) : String := toString r.toInt

def waitRun (shared : Bool) (ts : Option (Int × Int)) (val : BitVec 32) (at_ : Ptr → Ptr) :
    List String :=
  outcomes noKids do
    let p ← word 1
    let ts ← match ts with
      | some (sec, nsec) => some <$> lift (timespec sec nsec)
      | none => pure none
    code <$> futex_4arg (at_ p) (op FUTEX_WAIT shared) val ts

def wakeRun (shared : Bool) (val : BitVec 32) (at_ : Ptr → Ptr) : List String :=
  outcomes noKids do
    let p ← word 1
    code <$> futex_3arg (at_ p) (op FUTEX_WAKE shared) val

/-- The waiter of a one-waiter case: one wait at the word (0) for 0, with a 60 s timeout if
`timed`; its return goes to `slot`. -/
def waiter (shared timed : Bool) : Tgt → ConcM Tgt Unit := fun _ => do
  let ts ← if timed then some <$> lift (timespec 60 0) else pure none
  let r ← futex_4arg p0 (op FUTEX_WAIT shared) 0 ts
  lift (store 8 slot r)

/-- One waiter and a waker that repeats `FUTEX_WAKE` (here: twice) until a non-zero return:
`<the wake's return>/<the waiter's return>`. -/
def pairRun (shared timed : Bool) (val : BitVec 32) : List String :=
  outcomes (waiter shared timed) do
    let _ ← word 0
    let _ ← lift (alloc .stack 8 8)
    let t ← match ← ConcM.sync (.spawn 0) with
      | .ok t => pure t
      | .error _ => throw .unspecified
    let r ← futex_3arg p0 (op FUTEX_WAKE shared) val
    let r ← if r = 0 then futex_3arg p0 (op FUTEX_WAKE shared) val else pure r
    ConcM.sync (.join t)
    let c ← lift (load (BitVec 64) 8 slot)
    pure s!"{code r}/{code c}"

/-- The return codes of a waiter that a wake woke: the second parts of `pairRun`'s outcomes
whose wake returned non-zero. -/
def wokenCodes (shared timed : Bool) : List String :=
  ((pairRun shared timed 1).filterMap fun s => match s.splitOn "/" with
    | [r, c] => if r != "0" then some c else none
    | _ => none).eraseDups

/-- `k` calls of `FUTEX_WAKE` with `val` (private) at a word with three threads asleep: the
returns. -/
def wakeAsleep (k : Nat) (val : BitVec 32) : ConcM Tgt (List Int) :=
  (List.range k).mapM fun _ => (·.toInt) <$> futex_3arg p0 (op FUTEX_WAKE false) val

/-- Three sleepers, a wake limit of one: the three returns. -/
def threeRun (val : BitVec 32) : List String :=
  outcomes noKids (commas <$> wakeAsleep 3 val) (m0 := asleep 3)

/-- Three sleepers, a larger limit: the sum of the non-zero returns of repeated wakes, and how
many of them are above `val`. -/
def sumRun (val : BitVec 32) : List String :=
  outcomes noKids (m0 := asleep 3) do
    let rs := (← wakeAsleep 3 val).filter (· ≠ 0)
    pure s!"sum={rs.foldl (· + ·) 0},above={(rs.filter (· > (val.toNat : Int))).length}"

/-- A sleeper in the domain `shared`: a wake of all in the other domain, then a wake of one in
its own. -/
def domainRun (shared : Bool) : List String :=
  outcomes noKids (m0 := asleep 1 shared) do
    let other ← futex_3arg p0 (op FUTEX_WAKE !shared) 0x7fffffff
    let own ← futex_3arg p0 (op FUTEX_WAKE shared) 1
    pure (commas [other.toInt, own.toInt])

end Linux

/-! ## macOS (`futex.zig`'s `macosRows`) -/

namespace Darwin

open Zig.Os.Darwin

def op (all : Bool) : BitVec 32 :=
  if all then UL_COMPARE_AND_WAIT_NO_ERRNO ||| UL_WAKE_ALL else UL_COMPARE_AND_WAIT_NO_ERRNO

def code (r : BitVec 32) : String := toString r.toInt

/-- `__ulock_wait2` (timeout in ns), or with `old` `__ulock_wait` (timeout in µs). -/
def wait (old : Bool) (p : Option Ptr) (val : BitVec 64) (timeout : Nat) : ConcM Tgt (BitVec 32) :=
  if old then __ulock_wait (op false) p val (BitVec.ofNat 32 timeout)
  else __ulock_wait2 (op false) p val (BitVec.ofNat 64 timeout) 0

/-- Wait cases at a word that holds 1: the name, the address, the expected value and whether
with the call's 1 ms timeout. -/
def waits : List (String × (Ptr → Option Ptr) × BitVec 64 × Bool) := [
  ("mismatch", some, 0, false), ("mismatch_timed", some, 0, true), ("timeout", some, 1, true),
  ("null", fun _ => none, 1, false), ("null_timed", fun _ => none, 1, true),
  ("unaligned", (some <| ·.add 1), 1, false), ("unaligned2", (some <| ·.add 2), 0, false),
  ("unmapped", fun _ => some (addr 8), 1, false)]

/-- Wake cases with nobody asleep: the name and the address. -/
def wakes : List (String × (Ptr → Option Ptr)) := [
  ("none", some), ("null", fun _ => none), ("unaligned", (some <| ·.add 1)),
  ("unmapped", fun _ => some (addr 8))]

def waitRun (old : Bool) (at_ : Ptr → Option Ptr) (val : BitVec 64) (timed : Bool) : List String :=
  outcomes noKids do
    let p ← word 1
    code <$> wait old (at_ p) val (if !timed then 0 else if old then 1000 else 1000000)

def wakeRun (all : Bool) (at_ : Ptr → Option Ptr) : List String :=
  outcomes noKids do
    let p ← word 1
    code <$> __ulock_wake (op all) (at_ p) 0

/-- The waiter of a one-waiter case: one wait at the word (0) for 0; its return goes to `slot`. -/
def waiter (old timed : Bool) : Tgt → ConcM Tgt Unit := fun _ => do
  let r ← wait old (some p0) 0 (if !timed then 0 else if old then 60000000 else 0xffffffff)
  lift (store 4 slot r)

/-- One waiter and a waker that repeats `__ulock_wake` (here: twice) while it returns `-ENOENT`:
`<the wake's other returns>/<the waiter's return>`. -/
def pairRun (old timed all : Bool) : List String :=
  outcomes (waiter old timed) do
    let _ ← word 0
    let _ ← lift (alloc .stack 4 4)
    let t ← match ← ConcM.sync (.spawn 0) with
      | .ok t => pure t
      | .error _ => throw .unspecified
    let r ← __ulock_wake (op all) (some p0) 0
    let r ← if r = negErrno32 E.NOENT then __ulock_wake (op all) (some p0) 0 else pure r
    ConcM.sync (.join t)
    let c ← lift (load (BitVec 32) 4 slot)
    pure s!"{commas (if r = negErrno32 E.NOENT then [] else [r.toInt])}/{code c}"

/-- A waiter's return code as the probe prints it in a case with several waiters: `n` for a
non-negative one (`--ull_nwaiters`, which depends on when the others fell asleep). -/
def classOf (c : String) : String := if c.toInt?.any (0 ≤ ·) then "n" else c

/-- The return codes (`classOf`) of a waiter that a wake woke. -/
def wokenClasses : List String :=
  ((pairRun false false false).filterMap fun s => match s.splitOn "/" with
    | ["0", c] => some (classOf c)
    | _ => none).eraseDups

/-- `k` calls of `__ulock_wake` at a word with three threads asleep: the returns. -/
def wakeAsleep (k : Nat) (all : Bool) : List String :=
  outcomes noKids (m0 := asleep 3) do
    commas <$> (List.range k).mapM fun _ => (·.toInt) <$> __ulock_wake (op all) (some p0) 0

end Darwin

/-! ## Cases -/

/-- What a row's value must be. -/
inductive Shape where
  /-- One of the model's outcomes. -/
  | whole (outs : List String)
  /-- `<wakes>/<c1,…,cn>`: `wakes` is one of the model's outcomes, and each of the `n` waiters'
  return codes is one of `codes`. -/
  | waiters (wakes : List String) (n : Nat) (codes : List String)
  /-- `<threads>x<rounds>=<count>` with the product as count (the `mutex` row). -/
  | count

def Shape.accepts : Shape → String → Bool
  | .whole outs, v => outs.contains v
  | .waiters wakes n codes, v => match v.splitOn "/" with
    | [w, cs] => wakes.contains w && (cs.splitOn ",").length == n && (cs.splitOn ",").all codes.contains
    | _ => false
  | .count, v => match v.splitOn "=" with
    | [product, total] => match product.splitOn "x" with
      | [threads, rounds] => match threads.toNat?, rounds.toNat?, total.toNat? with
        | some t, some r, some c => 0 < t && 0 < r && t * r == c
        | _, _, _ => false
      | _ => false
    | _ => false

/-- The model's outcomes that the shape compares the value with (for the messages). -/
def Shape.model : Shape → String
  | .whole outs => toString outs
  | .waiters wakes n codes => s!"{wakes} / {n} of {codes}"
  | .count => "threads * rounds"

def hex (v : BitVec 32) : String := String.ofList (Nat.toDigits 16 v.toNat)

/-- The cases of aarch64-linux-gnu, in `futex.zig`'s order. -/
def linuxCases : List (String × Shape) :=
  ([("private", false), ("shared", true)].flatMap fun (domain, shared) =>
    (Linux.waits.map fun (name, ts, val, at_) =>
      (s!"wait_{domain}_{name}", Shape.whole (Linux.waitRun shared ts val at_))) ++
    (Linux.wakes.map fun (name, val, at_) =>
      (s!"wake_{domain}_{name}", Shape.whole (Linux.wakeRun shared val at_)))) ++
  ([("private", false, false), ("shared", true, false), ("private_timed", false, true)].flatMap
    fun (name, shared, timed) => [1, 2, 0, 0x7fffffff, 0xffffffff].map fun val =>
      (s!"wake1_{name}_val{hex val}", Shape.whole (Linux.pairRun shared timed val))) ++
  ([1, 0, 0xffffffff].map fun val =>
    (s!"wake3_private_val{hex val}",
      Shape.waiters (Linux.threeRun val) 3 (Linux.wokenCodes false false))) ++
  ([2, 0x7fffffff].map fun val =>
    (s!"wake3_private_val{hex val}",
      Shape.waiters (Linux.sumRun val) 3 (Linux.wokenCodes false false))) ++
  ([("shared", true), ("private", false)].map fun (domain, shared) =>
    (s!"domain_{domain}_waiter",
      Shape.waiters (Linux.domainRun shared) 1 (Linux.wokenCodes shared false))) ++
  [("mutex", Shape.count)]

/-- The cases of aarch64-macos-none, in `futex.zig`'s order. -/
def macosCases : List (String × Shape) :=
  ([("wait2", false), ("wait", true)].flatMap fun (call, old) =>
    Darwin.waits.map fun (name, at_, val, timed) =>
      (s!"{call}_{name}", Shape.whole (Darwin.waitRun old at_ val timed))) ++
  ([("one", false), ("all", true)].flatMap fun (call, all) =>
    Darwin.wakes.map fun (name, at_) => (s!"wake_{call}_{name}", Shape.whole (Darwin.wakeRun all at_))) ++
  ([("wait2", false, false), ("wait", true, false), ("wait2_timed", false, true),
      ("wait_timed", true, true)].flatMap fun (waiter, old, timed) =>
    [("one", false), ("all", true)].map fun (call, all) =>
      (s!"wake1_{call}_{waiter}", Shape.whole (Darwin.pairRun old timed all))) ++
  [("wake3_one", .waiters (Darwin.wakeAsleep 3 false) 3 Darwin.wokenClasses),
   -- `WAKE_ALL`: the probe prints the distinct returns other than `-ENOENT`.
   ("wake3_all", .waiters (Darwin.wakeAsleep 1 true) 3 Darwin.wokenClasses),
   ("mutex", .count)]

/-- The cases in which the model refuses the call (`.illegal`) where the kernel answers: the
address is not a live word of the model, and the native result needs mapping knowledge that the
model leaves open (`ZigLean/Os/Futex.lean`, "Address validation"; premises OSF-01, OSF-02,
"Model gaps"). Natively these return `-EFAULT`. -/
def refused : List String :=
  ["wait_private_null", "wait_shared_null", "wake_shared_null", "wait2_unmapped", "wait_unmapped"]

def casesOf : String → Option (String × List (String × Shape))
  | "aarch64-linux-gnu" => some ("linux", linuxCases)
  | "aarch64-macos-none" => some ("macos", macosCases)
  | _ => none

/-- A value that the model must not allow, per case (checked when this file is elaborated): a
wake above its limit or of a sleeper in the other domain, a success where the kernel must
report an error, and a lost increment. -/
def forbidden : List (String × String × String) := [
  ("aarch64-linux-gnu", "wake3_private_val1", "2,1/0,0,0"),
  ("aarch64-linux-gnu", "wake3_private_val0", "3/0,0,0"),
  ("aarch64-linux-gnu", "wake3_private_valffffffff", "3/0,0,0"),
  ("aarch64-linux-gnu", "wake3_private_val2", "sum=3,above=1/0,0,0"),
  ("aarch64-linux-gnu", "wake3_private_val7fffffff", "sum=2,above=0/0,0,0"),
  ("aarch64-linux-gnu", "wake1_private_val0", "1/-110"),
  ("aarch64-linux-gnu", "wake1_private_valffffffff", "2/0"),
  ("aarch64-linux-gnu", "wake1_private_val2", "2/0"),
  ("aarch64-linux-gnu", "domain_shared_waiter", "1,0/0"),
  ("aarch64-linux-gnu", "domain_private_waiter", "1,0/0"),
  ("aarch64-linux-gnu", "wait_private_mismatch", "0"),
  ("aarch64-linux-gnu", "wait_private_timeout", "0"),
  ("aarch64-linux-gnu", "wait_shared_unaligned", "-11"),
  ("aarch64-linux-gnu", "wait_private_bad_nsec_kernel", "-14"),
  ("aarch64-linux-gnu", "wake_private_none", "1"),
  ("aarch64-linux-gnu", "wake_shared_kernel", "0"),
  ("aarch64-linux-gnu", "mutex", "4x20000=79999"),
  ("aarch64-macos-none", "wait2_timeout", "0"),
  ("aarch64-macos-none", "wait2_mismatch", "-60"),
  ("aarch64-macos-none", "wait_null", "0"),
  ("aarch64-macos-none", "wait2_unaligned", "0"),
  ("aarch64-macos-none", "wake_one_null", "-2"),
  ("aarch64-macos-none", "wake_all_none", "-22"),
  ("aarch64-macos-none", "wake1_one_wait2", "0/-60"),
  ("aarch64-macos-none", "wake3_one", "0,0,0/n,n,-60"),
  ("aarch64-macos-none", "mutex", "4x20000=80001")]

#guard forbidden.all fun (triple, name, value) =>
  match (casesOf triple).bind (·.2.lookup name) with
  | some shape => !shape.accepts value
  | none => false

-- Every refused case is a case of some profile.
#guard refused.all fun name => (linuxCases ++ macosCases).any (·.1 == name)

def main (args : List String) : IO UInt32 := do
  let [triple, path] := args
    | IO.eprintln "usage: Futex.lean aarch64-linux-gnu|aarch64-macos-none FILE"; return 2
  let some (os, cases) := casesOf triple
    | IO.eprintln s!"aarch64-abi futex: no cases for {triple}"; return 2
  let lines := ((← IO.FS.readFile path).splitOn "\n").map (·.splitOn " " |>.filter (!·.isEmpty))
  unless lines.contains ["meta", "os", os] do
    IO.eprintln s!"aarch64-abi futex: {path}: no `meta os {os}` line (not a {triple} file)"
    return 1
  let rows := lines.filter (·.headD "" == "futex")
  let mut bad : List String := []
  -- A malformed, unknown or repeated row is a failure, not a skipped case.
  for row in rows do
    match row with
    | ["futex", name, _] =>
      unless cases.any (·.1 == name) do bad := bad ++ [s!"unknown case `{name}`"]
      unless (rows.filter (·[1]? == some name)).length == 1 do
        bad := bad ++ [s!"more than one row for `{name}`"]
    | _ => bad := bad ++ [s!"malformed row `{" ".intercalate row}`"]
  let mut matched := 0
  let mut refusals := 0
  for (name, shape) in cases do
    let some value := rows.findSome? fun row => match row with
        | ["futex", n, v] => if n == name then some v else none
        | _ => none
      | bad := bad ++ [s!"{name}: not in the file"]
    if refused.contains name then
      match shape with
      | .whole [out] =>
        if out != illegal then
          bad := bad ++ [s!"{name}: listed as refused, but the model answers {out} (stale)"]
        else if value.toInt?.isNone then
          bad := bad ++ [s!"{name}: `{value}` is not a return code"]
        else
          refusals := refusals + 1
          IO.println s!"refused by the model (.illegal, not a match) futex {name}: native {value}"
      | _ => bad := bad ++ [s!"{name}: listed as refused, but the model answers {shape.model} (stale)"]
    else if shape.accepts value then matched := matched + 1
    else bad := bad ++ [s!"{name}: native `{value}` is not an outcome of the model: {shape.model}"]
  for b in bad.eraseDups do IO.eprintln s!"aarch64-abi futex: {path}: {b}"
  unless bad.isEmpty do return 1
  IO.println s!"aarch64-abi futex: {triple}: {matched} native futex results are outcomes of the \
    model's OS rows (OSF-01, OSF-02); {refusals} calls the model refuses (none counted as matches)"
  return 0

end T04Futex

def main (args : List String) : IO UInt32 := T04Futex.main args
