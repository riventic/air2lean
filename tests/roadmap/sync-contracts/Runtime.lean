import Proofs.Sync.Proofs

/-!
# Contract-client runtime witnesses (C14)

`Proofs/Sync/SnapshotCache.lean` and `Proofs/Sync/Mailbox.lean` prove their clients for every
fuel and every oracle. The std operations they call contain `Zig.loop`, a `partial_fixpoint`
that the kernel does not unfold, so these finite runs execute the compiled model instead. They
are bounded evidence that the model clients complete (they are not fuel-exhausted vacuous
runs); they do not replace the theorems. No `native_decide`, no axioms.
-/

open Zig Sync

/-- A few fixed oracles: always the first option and four mixes. A futex wait may return
spuriously (C05, `docs/std-models.md` §Spurious wakeups), and the model has no fairness: some
oracles (plain round robin `fun n => n`, or `n % 2`) keep a waiter spinning on spurious returns
until the fuel ends, which is a permitted run without a result. These oracles complete. -/
private def oracles : List (Nat → Nat) :=
  [fun _ => 0, fun n => n % 7, fun n => n % 3, fun n => (n * 7 + 3) % 5, fun n => (n / 2) % 4]

private def completed {α : Type} (r : Result (Except ErrName α × Mem)) (ok : α → Bool) : Bool :=
  match r.run with
  | some (.ok (.ok v, m)) =>
    ok v && m.threads.all (fun t => t.joined) && m.blocks[0]?.any (fun b => !b.live)
  | _ => false

private def cacheRuns : Bool :=
  oracles.all fun o =>
    completed (Sched.run ⟨.any, .available⟩ SnapshotCache.stdDispatch 512 o (SnapshotCache.stdMain {}) (mem0 .fresh))
      (· == 10)

private def mailboxRuns : Bool :=
  oracles.all fun o =>
    completed (Sched.run ⟨.any, .available⟩ Mailbox.stdDispatch 1024 o (Mailbox.stdMain {}) (mem0 .fresh)) (· == 34)

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

def main : IO Unit := do
  require cacheRuns "snapshot cache did not complete with 10, joined writer and freed cache"
  require mailboxRuns "mailbox did not complete with 34, joined producer and freed mailbox"
  IO.println "Sync contract-client runtime witnesses passed"
