# Global-backed constant payload pointers (L06)

This source-only scope resolves `opt_payload` and `eu_payload` recursively through ordinary
struct fields and existing `nav`/`uav` global identities. Checked addition accumulates every
leaf and parent byte offset; a 64-projection budget rejects deep chains and cycles. Resolution
never allocates a global identity on failure. `arr_elem` remains rejected: all three compiler
InternPools define it as an element of a comptime-only array.

Payload constants require a sized, resolved layout, ordinary leaf pointer, generic address
space and initialized, non-extern, non-threadlocal global backing. Packed/vector projections
and actual volatile pointers are rejected. Canonical parent pointers carry volatile metadata
in the compiler; they do not perform a memory access. Optional payloads begin at offset zero.
Error payload offsets use the exact compiler alignment order. A layout that differs from the
current memory model is rejected. The composed error-union alignment dependency makes
nonzero equal-alignment payloads match; the same general comparison now accepts them.
Zero-sized payloads remain outside this scope.

`payload_base: true` is diagnostic metadata on a successfully resolved constant pointer. It
records that a compiler payload base actually reached the new resolver, so a compiler fixture
which flattened to an already-supported nav-plus-offset form cannot qualify these arms.

The public client uses a cross-file frozen nested optional and byte, equal-alignment and wide error union
payloads, and runtime projections into a writable global. Native tests use actual source
pointer addresses and compiler `@offsetOf`; they cover aliasing and neighboring-field frames.
`Model.lean` separately checks provenance, runtime-projection aliases, framed read/write laws,
const-write rejection and unspecified reads of absent payload bytes. It does not infer payload
initialization from an address. The pure shared kernel tests exercise parent-offset
accumulation, both overflow sites and bounded traversal. Typed semantic mutants must compile
before named test-assertion failures can count.

All compiler and Lean execution belongs to the root's single validation lane:

1. Build core Lean libraries, then set `AIR2LEAN_LEAN` and `LEAN_PATH` to that build.
2. Set `AIR2LEAN_ZIG_NATIVE` to a stock host compiler and run `check.sh --kernel`.
3. Run `check.sh --native` for each supported compiler version.
4. Build each patched compiler from this exact exporter and `pointer-offset.zig` (build.sh
   installs both), set `AIR2LEAN_ZIG_AIR`, `AIR2LEAN_ZIG_VERSION` and `AIR2LEAN_ZIG_BACKEND`, and run `check.sh --export EMPTY_DIRECTORY`.
5. Run `check.sh --export-reject OTHER_EMPTY_DIRECTORY` to check explicit layout/volatile
   rejection. Each export mode validates schema 12, strict JSON, version and exact requested
   Linux/baseline ReleaseSafe profile. Then translate the successful fresh directory and
   compile/run its generated functions and independent aliases before any qualification claim.

No compiler output, generated Lean, native acceptance or checked proof is claimed by this
source packet. Source inventories retain unqualified review labels.
