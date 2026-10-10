import ThreadLocals.Counters
import ThreadLocals.Leak

/-! Kernel-checked C02 thread-local storage contracts: the statements, and their axioms. -/

open Zig Zig.Conc

-- (1) No aliasing: the same `threadlocal` key in two threads is two blocks.
example {m : Mem} (hw : TlsWF m) {t u : ThreadId} (htu : t ≠ u) {key b c : BlockId}
    (hb : m.tlsInstance t key = some b) (hc : m.tlsInstance u key = some c) : b ≠ c :=
  hw.no_alias htu hb hc
-- `TlsWF` holds at program start and every step keeps it.
example {m m' : Mem} (hw : TlsWF m) (ht : m.current < m.threads.size)
    {inits : List (BlockId × Array Byte × Nat)} {x : Unit}
    (h : ((tlsEnter inits).run m).run = some (.ok (x, m'))) : TlsWF m' := hw.tlsEnter ht h

-- (2) Initialization per thread: each new instance holds exactly the initial bytes.
example {inits : List (BlockId × Array Byte × Nat)} {m m' : Mem} {x : Unit}
    (ht : m.current < m.threads.size) (h : ((tlsEnter inits).run m).run = some (.ok (x, m')))
    (i : Nat) (hi : i < inits.length) :
    ∃ blk, m'.blocks[m.blocks.size + i]? = some blk ∧ blk.live = true ∧
      blk.bytes = inits[i].2.1 ∧ blk.kind = .global :=
  ((tlsEnter_init ht h).2.2.2.2.2.2 i hi).2
-- The main thread's instance is the key block of `mem0`, with the same initial bytes.
example : (ThreadLocals.mem0 .fresh).blocks[0]?.map (·.bytes) = some (ThreadLocals.tlsInit[0]!.2.1) := rfl

-- (3) Two workers and `main` increment their own `counter` concurrently: every schedule.
example (env : Env) (henv : env.spawn = .available) {fuel : Nat} {o : Nat → Nat} {v : Except ErrName (BitVec 32)} {m : Mem}
    (h : (Sched.run env ThreadLocals.dispatch fuel o ThreadLocals.twoCounters (ThreadLocals.mem0 .fresh)).run =
      some (.ok (v, m))) : v = .ok 90908 :=
  ThreadLocals.Counters.twoCounters_spec env henv h
example (env : Env) (henv : env.spawn = .available) {fuel : Nat} {o : Nat → Nat} {e : Error} :
    (Sched.run env ThreadLocals.dispatch fuel o ThreadLocals.twoCounters (ThreadLocals.mem0 .fresh)).run ≠
      some (.error e) :=
  ThreadLocals.Counters.twoCounters_safe env henv

-- (4) A thread-local pointer used after its thread ended never gives a result.
example (env : Env) (henv : env.spawn = .available) {fuel : Nat} {o : Nat → Nat} {v : Except ErrName (BitVec 32)} {m : Mem} :
    (Sched.run env ThreadLocals.dispatch fuel o ThreadLocals.leaked (ThreadLocals.mem0 .fresh)).run ≠
      some (.ok (v, m)) :=
  ThreadLocals.Leak.leaked_never_ok env henv
example {T : Type} [Enc T] {m m' : Mem} {p : Ptr} {b : BlockId} {a : Nat} {v : T}
    (hd : m.Dead b) (hp : p.block = some b) : ((load T a p).run m).run ≠ some (.ok (v, m')) :=
  load_dead hd hp

-- Only the standard axioms: no `sorry`, no `native_decide` (`Lean.ofReduceBool`).
/-- info: 'ThreadLocals.Counters.twoCounters_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ThreadLocals.Counters.twoCounters_spec

/-- info: 'ThreadLocals.Counters.twoCounters_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ThreadLocals.Counters.twoCounters_safe env henv

/-- info: 'ThreadLocals.Leak.leaked_never_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ThreadLocals.Leak.leaked_never_ok env henv

/-- info: 'Zig.TlsWF.no_alias' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TlsWF.no_alias

/-- info: 'Zig.tlsEnter_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tlsEnter_init

/-- info: 'Zig.TlsWF.tlsEnter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TlsWF.tlsEnter

/-- info: 'Zig.tlsExit_dead' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tlsExit_dead
