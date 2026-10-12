# Error return tracing (L14)

`error_tracing.zig` is compiled with `-ferror-tracing`: Sema adds the trace operations
(`err_return_trace`, `set_err_return_trace`, `save_err_return_trace_index`, calls of
`std.builtin.returnError` / `std.lang.returnError` whose body uses `ret_addr`), and 0.14.1,
0.15.2 and 0.17.0 check a large error union returned through the result pointer with
`is_non_err_ptr`, which no `-fno-error-tracing` export of those versions contains. The exporter
format and the translation are in `docs/air-json.md` §Error return trace: the hidden trace
parameter becomes a last parameter and the current trace data flow; the trace's `StackTrace` and
address buffer are ordinary model memory, so the recorded index is exact, and a return address is
stored as undefined bytes.

| File | Content |
|---|---|
| `air/<version>` | exports of the five roots and `returnError` by patched 0.17.0, 0.16.0, 0.15.2 and 0.14.1 compilers (`export.sh`; `provenance.json`, `test_provenance.py`) |
| `Runner.lean`, `expected.txt` | the native `main`'s calls on the generated code, and their output |
| `test_cli.py` | the exports translate; an unresolved `StackTrace`, a trace without one, a nested `set_err_return_trace` and a `@returnAddress()` read as a number are rejected |

```sh
lake build ZigLean air2lean
tests/roadmap/error-tracing/check.sh                 # 4 versions: model == expected.txt, rejections
tests/roadmap/error-tracing/check.sh --native ZIG    # stock Zig, this host: native == expected.txt
AIR2LEAN_ZIG_AIR=<dir of zig-air-<version>> tests/roadmap/error-tracing/export.sh --check [VERSIONS]
```

`traced(x)` returns the trace index inside the error branch (2 after `bigRet` and `pass` recorded
their error returns) and `handledTwice(x)` shows that a handled error restores the index. The model
of every version prints `expected.txt`; so do the native runs (`check.sh --native`) of stock
0.15.2, 0.16.0 and 0.17.0 on aarch64-macos and of all four versions on x86_64-linux (linux/amd64
container) and aarch64-linux (linux/arm64 container). Not covered: error return tracing in
concurrent programs through the modelled `Thread` functions and through modelled allocator calls
(rejected), and any use of a return address other than storing it.
