# C02: thread-local storage

`thread_locals.zig` has one `threadlocal var counter: u32 = 7`, a worker `bumpTwice(out)` that
increments its own `counter` twice and writes what it reads to `out`, `twoCounters` (two
workers and `main` increment their own `counter`, then `a * 10000 + b * 100 + counter`), a
worker `leak(out)` that hands out `&counter`, and `leaked` (reads the worker's `counter` after
joining it).

Model (`docs/generated-code.md` §Thread-local storage, `ZigLean/Mem/Tls.lean`): the global's
`mem0` block is the main thread's instance and its key; every spawned thread makes its own
instance from `tlsInit` when it starts and frees it when it ends (`Zig.ConcM.tlsThread` in the
generated dispatcher); `runtime_nav_ptr` is `Zig.tlsPtr key`, the current thread's instance.

| Acceptance | Evidence |
|---|---|
| Equal TLS names in different threads do not alias | `TlsWF.no_alias` (`ZigLean/Conc/TlsLemmas.lean`): the same key gives two different blocks in two threads. `TlsWF` holds at program start (`TlsWF.mainTls`) and is kept by every memory step that keeps the thread records (`TlsWF.of_threads`), a spawn, a join and a thread start (`TlsWF.fork`, `.join`, `.tlsEnter`). |
| Initialization per thread | `tlsEnter_init`: each new instance is a new live block holding exactly the initial bytes; `mem0`'s main instance holds the same bytes as `tlsInit` (`Check.lean`). |
| Concurrent use, all schedules | `twoCounters_spec`/`twoCounters_safe` (`ThreadLocals/Counters.lean`): every `ok` result is 90908 (each worker read 9, `main` read 8) and no run errs (no race, panic or deadlock), for every oracle and fuel. Each thread owns its instance; the workers' instances are made by `tlsEnter` and freed by `tlsExit` inside the proof. |
| Thread exit ends the instance | `leaked_never_ok` (`ThreadLocals/Leak.lean`): no schedule returns a value; the read through the leaked pointer hits a dead block (`load_dead`). `tlsExit_dead`: after a thread end every instance of it is dead. |
| Ownership transfer | A TLS pointer is an ordinary pointer: passing it hands over nothing (race check), and a proof hands cells over with `Zig.Conc.Capture.grant` like any capture (C01). |

`ThreadLocals/Runtime.lean` runs 16 sampled schedules (90908 and `.illegal`) and two semantic
mutants: one instance shared by all threads (the run no longer returns 90908) and instances
that outlive their thread (the leaked read succeeds with 7). `test_cli.py` checks the retained
translation of both exports and the rejections: the old exporter's marker, a missing or
out-of-range `global`, a `runtime_nav_ptr` of a non-`threadlocal` global, `extern threadlocal`,
a missing initial value, pointer-holding storage, a wrong pointee type, over-alignment,
`volatile`, and a constant pointer into a `threadlocal` global (0.14.1's form).

```sh
lake build air2lean ZigLean.Conc.TlsLemmas
bash tests/roadmap/thread-locals/check.sh
```

## Export

The AIR in `air/0.16.0` and `air/0.15.2` was exported with the patched compilers built from this
revision's `zig-patch/air-json/json.zig` (which writes `runtime_nav_ptr`'s `global`). The
0.16.0 export equals, byte for byte, the earlier exporter's output with that field added; the
0.15.2 translation differs from `ThreadLocals/Gen.lean` only in its profile header.

```sh
zig-patch/build.sh 0.16.0 "$PWD/zig-air-0.16.0" && zig-patch/lock.sh "$PWD/zig-air-0.16.0"
zig-patch/build.sh 0.15.2 "$PWD/zig-air-0.15.2" && zig-patch/lock.sh "$PWD/zig-air-0.15.2"
for v in 0.16.0 0.15.2; do
  rm -rf "tests/roadmap/thread-locals/air/$v" && mkdir -p "tests/roadmap/thread-locals/air/$v"
  ZIG_AIR_JSON_DIR="$PWD/tests/roadmap/thread-locals/air/$v" ZIG_AIR_JSON_FILTER=thread_locals. \
    "zig-air-$v/bin/zig" build-obj -fno-emit-bin -target x86_64-linux -mcpu=baseline \
    -OReleaseSafe -fno-error-tracing tests/roadmap/thread-locals/thread_locals.zig
done
.lake/build/bin/air2lean tests/roadmap/thread-locals/air/0.16.0 \
  -o tests/roadmap/thread-locals/ThreadLocals/Gen.lean --namespace ThreadLocals --prefix thread_locals.
```

0.14.1 has no `runtime_nav_ptr`: it writes the address of a `threadlocal` global as a constant
pointer, which the translator rejects. Scope: no native execution of `thread_locals.zig`
(the patched compilers have no LLVM); detached threads, `extern threadlocal`, and
`threadlocal` storage holding pointers, unions or errors are outside the subset.
