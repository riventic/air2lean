#!/usr/bin/env bash
# The general symbolic executor `fsym` (ZigLean/Sep/Full/Auto.lean, docs/proof-automation.md) on
# small library-only examples: the arithmetic solver, walks/returns, the concurrent backend,
# variable pointers (Facts), a large generated body (Large), and the scenarios of the retired
# step/frame tactics and total-correctness checks (Steps, Frame, Total), range laws (Plan), the
# region library (Region) and providers over the whole precondition (Providers: tagged shares,
# pointer `==` across live blocks, `Within`) and the planning order with terms equal up to
# arithmetic (Unify: a grant whose bytes changed, hypotheses up to arithmetic) and the caller's
# updates at returns (Updates: `fsym [u]` with `u : EUpd P Q`) and the fields of a stored struct
# (Fields: `EncField`, whole and field access) and plain accesses of atomic words that keep
# their tag (AtomicPlain) and accesses of a struct whose fields several parts own (Parts) and
# thread steps by the sequential rules with the locality of their command (Threads) and views of
# atoms at stuck steps (Views: atomic words as bytes, a value's encoding, two fees) and structs
# as their fields (Structs: a derived layout's `LawfulEnc`, split and join, padding, fail-closed
# cases) and a packed value's bits read back (Packed: derived `LawfulPacked` of packed structs of
# bool, integer, enum, float and packed fields, a stored `fromInt`, a packed union fails closed) and a
# thread's run in a protocol (WP: `MemM` segments with inferred posts, `main`'s start at its
# spawn from the start facts and the facts of the steps' runs; WPMutex: the generated
# `Io.Mutex` lock, unlock and lock loop against the lock rules, for every protocol with the
# lock; WPHold: the lock holder's steps by `FLock.Fits.wp_hold` with the holder's next place, the
# protocol's lemmas backwards and forwards; ReadRest: a reader's rest-read race premise can
# hold while an unrelated live thread has not acquired the publication; WPOsFutex: the OS futex
# rows of std's Thread.Futex at a lock's word, by the rows' rules and the lock's OS wait and wake
# rules) and total stack pushes
# of a thread with a stack budget
# (Stack: the token rules, a thread, the start, rejected pushes without room) and step ticks
# (Ticks: memory/concurrent loops, straight-line ticks, thread locality, WP segments, one credit).
# Its large user is
# the FixedBufferAllocator
# (tests/roadmap/alloc-fba/AllocFba/Full.lean). Every example is a module of the fixture's library
# SepAuto (tests/roadmap/lakefile.toml, SepAuto/*.lean), built by Lake with what it imports
# (scripts/fixtures.py; run it under scripts/build-guard.py); runs no compiler.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
python3 -B scripts/fixtures.py build SepAuto
# Axioms of every theorem of every module, from the built environment: only the standard ones.
python3 -B scripts/fixtures.py audit --library SepAuto
echo "sep-auto: ok"
