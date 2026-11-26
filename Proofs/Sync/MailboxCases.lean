import Proofs.Sync.Mailbox.Main
import Proofs.Sync.SemCases

/-!
# The mailbox client, for the Zig 0.17.1 Sync profile

`Proofs/Sync/Mailbox.lean` for the actual Zig 0.17.1 Linux translation
(`Proofs/Sync/Gen/V0_17_1/H_6c696e7578/Gen.lean`): the mailbox's code and its proof are once for
every translation (`Proofs/Sync/Mailbox/`); this file instantiates them with that translation's
spawn target `Tgt.semWork`, its semaphore value with no permit (`semZ`) and its `Io.Semaphore`
contract (`sem`, `Proofs/Sync/SemCases.lean`). `mailbox_spec` and `mailbox_safe` have the public
theorems' statements word for word, over this translation's names
(`assurance/theorem-list.json`: `cases`).
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Full Zig.Full.FAssn Sync.Mailbox

namespace Sync.CaseContracts.V0_17_1.H_6c696e7578.Mailbox

open Sync.Gen.V0_17_1.H_6c696e7578

/-- The semaphore with no permit. -/
def semZ : Io_Semaphore :=
  { mutex := ({ state := ({ raw := Io_Mutex_State.unlocked } : atomic_Value_Io_Mutex_State) } : Io_Mutex),
    cond := ({ state := ({ raw := (Packed.ofBits (0 : BitVec 32) : Io_Condition_State) } :
      atomic_Value_Io_Condition_State), epoch := ({ raw := (0 : BitVec 32) } : atomic_Value_u32) } :
      Io_Condition),
    permits := (0 : BitVec 64) }

/-- The producer's argument. -/
def swOf : Tgt → Option Ptr
  | .semWork p => some p
  | _ => none

/-! ## The results, for the translated `Io.Semaphore` -/

/-- The mailbox client with the translated std semaphore. -/
abbrev stdMain := mailMain Tgt.semWork semZ sem

/-- The spawn targets with the translated std semaphore. -/
abbrev stdDispatch := dispatch swOf sem

/-- The std semaphore's mutex value. -/
def stdK : Cfg := ⟨sem.c, .inr (.inl rfl)⟩

/-- **The consumer receives the whole message under every schedule**: every completed run of
the mailbox client returns 34 (every oracle, every fuel; the spawn does not fail). -/
theorem mailbox_spec (env : Env) (henv : env.spawn = .available) {σ : Placement} {fuel : Nat} {o : Nat → Nat} {v : Except ErrName (BitVec 32)} {m : Mem}
    (io : Io) (h : (Sched.run env stdDispatch fuel o (stdMain io) (mem0 σ)).run = some (.ok (v, m))) :
    v = .ok 34 := by
  obtain ⟨_, _, hv, -⟩ := (proto stdK swOf).run_sound env (Proto.of_available henv) stdDispatch G0
    (dispatch_spec sem rfl) (fun _ _ _ _ _ hq => hq.2) rfl
    (main_spec Tgt.semWork (fun _ => rfl) semZ (by decide +kernel) sem rfl (m₀ := mem0 σ) rfl io) h
  exact hv

/-- **No run of the mailbox client gives an error**: no data race on the message, no deadlock
(also when the consumer sleeps at the condition first), no lifetime error at the free. -/
theorem mailbox_safe (env : Env) (henv : env.spawn = .available) {σ : Placement} {fuel : Nat} {o : Nat → Nat} {e : Error} (io : Io) :
    e ≠ .stackOverflow → (Sched.run env stdDispatch fuel o (stdMain io) (mem0 σ)).run ≠ some (.error e) :=
  (proto stdK swOf).run_safe env (Proto.of_available henv) stdDispatch G0 rfl (dispatch_spec sem rfl)
    (fun _ _ _ _ hq => hq.2) rfl
    (main_spec Tgt.semWork (fun _ => rfl) semZ (by decide +kernel) sem rfl (m₀ := mem0 σ) rfl io)

end Sync.CaseContracts.V0_17_1.H_6c696e7578.Mailbox
