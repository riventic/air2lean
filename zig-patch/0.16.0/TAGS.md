# Zig 0.16.0 vs 0.15.2

## AIR tags (`Air.Inst.Tag`)

| Only in 0.15.2 | Only in 0.16.0 |
|---|---|
| `cmp_lt_errors_len` | `cmp_lte_errors_len` (renamed) |
| `vector_store_elem` | `legalize_vec_store_elem`, `legalize_vec_elem_val`, `legalize_compiler_rt_call` |

None of the differences is in the air2lean subset.

## Exporter port

`zig-patch/air-json/json.zig` is shared by every version; its `Compat` section has the 0.16.0
branch:

- No global environment: `pt.zcu.comp.environ_map.get(…)` in place of `std.posix.getenv`.
- File I/O through `std.Io`: `std.Io.Dir.cwd().createDirPathOpen(io, …)`, `dir.createFile(io, …)`,
  `file.writer(io, &buf)`, `close(io)`, with `io = pt.zcu.comp.io`.
- Hook: after `analyzeFuncBodyInner(func_index, reason)` (renamed from `analyzeFnBodyInner`) in
  `src/Zcu/PerThread.zig`. Function bodies are still analysed on one thread, so the exporter
  needs no lock.

## Observed differences on the examples

| Difference | Examples | Handled by |
|---|---|---|
| A read of a field, the length or an element of a struct or slice parameter goes through a read-only stack copy: `alloc`, `store`, `bitcast` to a const pointer, then `struct_field_ptr_index_N` / `ptr_slice_len_ptr` / `slice_elem_ptr` and `load`. 0.15.2 reads the value (`struct_field_val`, `slice_len`, `slice_elem_val`). | `basic` (`weightedTardiness`, `totalWeightedTardiness`), `options` (`findOr`) | `Air2Lean/Air/Canon.lean` `forwardReadOnlyCopies`; the exporter writes `ptr_slice_len_ptr`'s operand |
| More `dbg_stmt` instructions (one per `switch` prong), so the AIR instruction indexes shift. | `floatops` | `Canon.lean` `renumber` |

After `Canon.lean`, the translation of every example equals the 0.15.2 one, except the float
semantics that changed in compiler_rt (`docs/floats.md` §Per-version differences). The AIR golden
files are shared (`tests/golden/<ex>/air/`); `tests/golden/0.16.0/` has no files of its own.
