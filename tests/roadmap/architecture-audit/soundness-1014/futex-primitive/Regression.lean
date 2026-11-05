import ZigLean.Os.Futex
import ZigLean.Os.Thread
import ZigLean.Conc.Sched

/-!
# Audit S6: regressions of the corrected OS futex primitive

Each theorem observes the actual definitions in `ZigLean/Os/Futex.lean` and
`ZigLean/Os/Thread.lean` at a fixed state, as the corrected model must behave natively. The
first observes `Sched.runTrace`; the second observes the actual call's `CoN` frontier and its
continuation, before the scheduler's separate child-handle completion check. They are not
client proofs, native executions, valid std join ownership claims or whole-program termination
claims. The open witnesses are in `CurrentModel.lean`.

Linux v6.16, commit 038d61fd642278bab63ee8ef722c50d10ab01e8f, supplies the comparison:
`kernel/futex/core.c` (`get_futex_key`) and `kernel/fork.c:1418–1428` (`mm_release`).
See `docs/architecture-audit/soundness-2026-10-14.md` §S6.
-/

open Zig Zig.Os

namespace AuditS6

private def env : Zig.Env := { io := .any, spawn := .available }
private def noKids : Nat → ConcM Nat Unit := fun _ => pure ()

private def block (addr size : Nat) : Block := {
  bytes := Array.replicate size (.int 0)
  align := 4
  kind := .heap
  live := true
  addr
}

private def p : Ptr := ⟨some 0, 0⟩
private def base : Mem := { blocks := #[block 4096 8] }

private def observeWake (call : ConcM Nat (BitVec 64)) (m : Mem) :
    Option (Except Error (Int × Array (ThreadId × Ptr) × Array ThreadId)) :=
  (Sched.runTrace env noKids 20 (fun _ => 0) call m).1.map
    (·.map fun (v, m') => (v.toInt, m'.waiters, m'.woken))

/-- Linux key validation rejects unaligned address 4097 before queue lookup: `-EINVAL`, with
the queue unchanged. -/
theorem unaligned_wake_einval :
    observeWake (Linux.futex_3arg (p.add 1) 0x81 1) base =
      some (.ok (-22, #[], #[])) := by
  decide +kernel

/-- `access_ok` (core.c:540): an address with bits 63 and 55 set, also an aligned negative offset
as a `usize`, is a kernel address on x86_64 and aarch64, tagged or not: `-EFAULT` before a key or
queue lookup, for private and shared WAKE and for WAIT. Address `2^63` is a user address under
aarch64's tagged-address ABI: a conservative refusal. -/
theorem access_ok_efault :
    observeWake (Linux.futex_3arg ⟨none, 2 ^ 63 + 2 ^ 55⟩ 0x81 1) base =
      some (.ok (-14, #[], #[])) ∧
    observeWake (Linux.futex_3arg ⟨none, 2 ^ 63⟩ 0x81 1) base = some (.error .illegal) ∧
    observeWake (Linux.futex_3arg ⟨none, -4⟩ 0x81 1) base = some (.ok (-14, #[], #[])) ∧
    observeWake (Linux.futex_3arg ⟨none, -4⟩ 1 1) base = some (.ok (-14, #[], #[])) ∧
    observeWake (Linux.futex_4arg ⟨none, -4⟩ 0x80 0 none) base = some (.ok (-14, #[], #[])) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- A private key needs a user address, not a live word (core.c:596–611): a private WAKE below
the end of a placed block returns 0. A shared key needs a writable page (`get_user_pages_fast`),
which the model knows only for a live writable word: a shared WAKE at an address without one is
a conservative refusal (`.illegal`), never a returned 0. -/
theorem private_key_shared_refusal :
    observeWake (Linux.futex_3arg ⟨none, 4096⟩ 0x81 1) { blocks := #[{ block 4096 8 with
      live := false }] } = some (.ok (0, #[], #[])) ∧
    observeWake (Linux.futex_3arg ⟨none, 4096⟩ 1 1) { blocks := #[{ block 4096 8 with
      live := false }] } = some (.error .illegal) :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- `__ulock_wait2`/`__ulock_wake` (xnu-12377.121.6 `bsd/kern/sys_ulock.c:571`, `:966`): a null
or unaligned WAIT and a null WAKE return `-EINVAL` before any compare or queue effect. -/
theorem ulock_null_einval :
    (Darwin.__ulock_wait2 0x01000001 none 0 0 0 : ConcM Nat (BitVec 32)) 0 base =
      .leaf (some (.ok (negErrno32 Darwin.E.INVAL, base))) ∧
    (Darwin.__ulock_wait2 0x01000001 (some (p.add 1)) 0 0 0 : ConcM Nat (BitVec 32)) 0 base =
      .leaf (some (.ok (negErrno32 Darwin.E.INVAL, base))) ∧
    (Darwin.__ulock_wake 0x01000001 none 0 : ConcM Nat (BitVec 32)) 0 base =
      .leaf (some (.ok (negErrno32 Darwin.E.INVAL, base))) :=
  ⟨rfl, rfl, rfl⟩

/-- After option 0 of a wait's first pick (the kernel's compare), the next stop: the count of
its pick and the result after option `c`. -/
private def ulockRet (x : CoN Nat (BitVec 32 × Mem) 3) (c : Nat) :
    Option (Nat × Option (Except Error Int)) :=
  match x with
  | .sync (.pick _) m k =>
    match k (0 : Nat) m with
    | .sync (.pick count) m' k' =>
      match k' c m' with
      | .leaf r => some (count m', r.map (·.map (·.1.toInt)))
      | .sync .. => none
    | .sync .. | .leaf _ => none
  | _ => none

/-- A word of value 3. -/
private def three : Mem := { blocks := #[{ block 4096 8 with
  bytes := #[.int 3, .int 0, .int 0, .int 0, .int 0, .int 0, .int 0, .int 0] }] }

/-- The mismatched wait of `0` at the word of value 3, after option `c` of its second pick. -/
private def mismatch (c : Nat) : Option (Nat × Option (Except Error Int)) :=
  ulockRet ((Darwin.__ulock_wait2 0x01000001 (some p) 0 0 0 : ConcM Nat (BitVec 32)) 3 three) c

/-- `__ulock_wait2` returns `--ull_nwaiters` (xnu-12377.121.6 `sys_ulock.c:826`), the other
waiters at the key, not always `0`, or `-EFAULT` for a word that is not resident (:652–663):
after a mismatch the oracle picks among `-EFAULT` and the `2^31` non-negative `c_int`s, here
`-EFAULT`, `0`, `5` and `2^31 - 1`. -/
theorem ulock_wait_nwaiters :
    mismatch 0 = some (2 ^ 31 + 1, some (.ok (-14))) ∧
    mismatch 1 = some (2 ^ 31 + 1, some (.ok 0)) ∧
    mismatch 6 = some (2 ^ 31 + 1, some (.ok 5)) ∧
    mismatch (2 ^ 31) = some (2 ^ 31 + 1, some (.ok (2 ^ 31 - 1))) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

private def twoRawWaiters : Mem := {
  base with
  blocks := #[{ block 4096 8 with
    bytes := #[.int 1, .int 0, .int 0, .int 0, .int 0, .int 0, .int 0, .int 0] }]
  threads := #[{ spawner := 0, joined := true },
    { spawner := 0, joined := false }, { spawner := 0, joined := false }]
  clocks := #[#[0, 0, 0], #[0, 0, 0], #[0, 0, 0]]
  waiters := #[(1, p), (2, p)]
}

/-- `CHILD_CLEARTID` wakes at most one waiter (Linux `mm_release`: `FUTEX_WAKE` with count 1).
With two raw waiters queued at `ctid`, the actual `cloneExit` has exactly two options, one for
each waiter: each clears the word and wakes that waiter alone, and the other stays queued. -/
theorem cleartid_wakes_one :
    ∃ (count : Mem → Nat) (k : Nat → Mem → CoN Nat (Unit × Mem) 1),
      (Linux.cloneExit p : ConcM Nat Unit) 2 twoRawWaiters =
        .sync (.pick count) twoRawWaiters k ∧
      count twoRawWaiters = 2 ∧
      (match k 0 twoRawWaiters with
       | .leaf r => r.map (·.map fun (_, m') =>
           (m'.waiters, m'.woken, m'.blocks[0]?.map fun b => b.bytes.extract 0 4))
       | .sync .. => none) =
        some (.ok (#[(2, p)], #[1], some #[.int 0, .int 0, .int 0, .int 0])) ∧
      (match k 1 twoRawWaiters with
       | .leaf r => r.map (·.map fun (_, m') =>
           (m'.waiters, m'.woken, m'.blocks[0]?.map fun b => b.bytes.extract 0 4))
       | .sync .. => none) =
        some (.ok (#[(1, p)], #[2], some #[.int 0, .int 0, .int 0, .int 0])) := by
  refine ⟨_, _, rfl, by decide +kernel, by decide +kernel, by decide +kernel⟩

end AuditS6
