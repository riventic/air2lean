import ThreadLocals.Counters
import ThreadLocals.Leak

/-!
Strength log of `tests/roadmap/thread-locals/ThreadLocals/Counters.lean` (compiled by
`tests/roadmap/thread-locals/check.sh`; deleted with the legacy logic): the migrated theorems hold
under every placement; the legacy statements (the fresh placement) word for word.
-/

open Zig Zig.Conc ThreadLocals

namespace StrengthLog.ThreadLocals

example (env : Env) (henv : env.spawn = .available) {fuel : Nat} {o : Nat → Nat}
    {v : Except ErrName (BitVec 32)} {m : Mem}
    (h : (Sched.run env dispatch fuel o twoCounters (mem0 .fresh)).run = some (.ok (v, m))) :
    v = .ok 90908 :=
  Counters.twoCounters_spec env henv h

example (env : Env) (henv : env.spawn = .available) {fuel : Nat} {o : Nat → Nat} {e : Error} :
    e ≠ .stackOverflow → (Sched.run env dispatch fuel o twoCounters (mem0 .fresh)).run ≠ some (.error e) :=
  Counters.twoCounters_safe env henv

-- Retiring the TLS operational facts' legacy import changes no premise or conclusion of
-- the use-after-thread-exit exclusion theorem.
example (env : Env) (henv : env.spawn = .available) {fuel : Nat} {o : Nat → Nat}
    {v : Except ErrName (BitVec 32)} {m : Mem} :
    (Sched.run env dispatch fuel o leaked (mem0 .fresh)).run ≠ some (.ok (v, m)) :=
  Leak.leaked_never_ok env henv

end StrengthLog.ThreadLocals
