# M04 bounded byte sentinel allocation

This change admits only Zig 0.16.0 `std.mem.Allocator.allocSentinel(u8, n, s)` returning
an alignment-1 mutable sentinel slice on the existing 64-bit little-endian memory ABI.
The pointer type carries the actual comptime sentinel; the Zig 0.16.0 exporter writes it as
`sentinel_byte`, decimal text in 0..255. Presence without value is rejected rather than
interpreted as zero. Wider element types, other Zig versions, sentinel remap, missing
metadata, const results, packed-pointer host/offset metadata and incompatible alignment remain rejected.
Normalized clients must also provide a sentinel in 0..255; JSON validation cannot substitute
for the public model signature checks. Older exporter versions retain their prior raw output. This closes a
bounded part of M04, not lower-level allocator APIs, growth or general sentinel remap.

The pristine 0.16.0 allocator implementation calls `allocWithOptionsRetAddr`, computes
`n + 1`, allocates that count, stores at `n`, and slices back to length `n`. Consequently
ReleaseSafe maximum-usize addition panics before allocation. Other nonzero requests
consume one allocation-policy decision and can return OutOfMemory. An empty payload
still requires one byte; it can fail. The model uses the ordinary checked `store`, so
out-of-block writes or omitted extra bytes do not silently succeed. Free of a sentinel
slice covers its whole n+1-byte block, including the poison write; freeing only its
payload is illegal.

`ZigLean/Sep/Sentinel.lean` defines the owned success bytes, proves their size, preserves
the complete payload range, identifies the final sentinel bytes, and gives a framed
sequential allocation triple for every failure policy under an explicit nonoverflow
premise. `allocSentinel_overflow` separately states the panic. `Triple.freeSentinel`
consumes the complete success block using `sentinelBytes_size`; ownership does not
vanish when a payload is empty or when the caller writes it.

The serialized qualification recipe is:

```sh
python3 -B tests/roadmap/byte-sentinel/static.py
AIR2LEAN_SENTINEL_ZIG_AIR=/absolute/path/to/fresh-patched-0.16.0/zig \
AIR2LEAN_SENTINEL_ZIG_NATIVE=/absolute/path/to/shipping-0.16.0/zig \
AIR2LEAN_SENTINEL_TRANSLATOR="$PWD/.lake/build/bin/air2lean" \
bash tests/roadmap/byte-sentinel/check.sh
```

The AIR compiler must be rebuilt with this exporter adaptation. An existing exporter
binary is insufficient. The gate checks fresh source-derived metadata and calls, then
runs the actual emitted code against the same source compiled natively in ReleaseSafe.
Its 13 observations cover zero/nonzero sentinel, empty/one/eight-byte payloads, repeated
failures, the extra byte crossing a request cap, full-block cleanup and writable payloads.
Overflow is a separate explicit integer-overflow panic observation with zero allocator
attempts. Synthetic pipeline checks cover 0/42/255 emission, ten parsed negative cases, and three
normalized negative cases that deliberately bypass JSON. Spawned pointer compatibility
requires equal explicit byte sentinels, rejects mixed known/missing values, and keeps the
prior presence-only comparison only when both legacy values are missing. Public capture
checks test the same boundary. External model signature fixtures also mutate only the
known byte (0 to 42 or missing); both binding checks and generated reports retain that
distinction. Missing-byte signature shapes keep their prior serialized form.
Two kernel mutants omit the extra byte or move the sentinel store to offset zero;
the existing strict bitops diagnostic classifier requires every located error to be a
complete false `decide` proposition before counting detection. A portable mixed
false-proposition/heartbeat regression prevents a partial refutation masking resource
failure. The mutation driver elaborates its standalone baseline exactly once. Neither compilation
failure nor a resource kill qualifies. Kernel Check also rejects a store into an omitted
extra byte and a payload-only free. No native_decide is used in the new kernel regressions.

ROOT qualification passed the kernel allocation/framing lemmas, all five baseline
assertions, both strict kernel mutants, the fresh source metadata/emission checks and
all 13 native/generated observations. The separate ReleaseSafe overflow observation
confirmed a panic before any allocation attempt. Registry and actual external-model CLI
tests passed for sentinel 0 versus 42 and missing metadata. Seven portable checks pass.
The qualified patched Zig 0.16.0 exporter cache key is
`13fa3296f9e768a7b6a65bdb188eb8cc88ab31ea14f2d22cc3b9eca3da1e22d2`.

Fresh Linux/baseline ReleaseSafe exports of `slices.sumZ` and `slices.subZ` passed
the strict profile and receipt checks. Each adds exactly the exported byte 0 to one
pointer type. Their CI-normalized AIR is byte-identical to the previous goldens after
removing only that new field, and their emitted executable bodies are unchanged.
The exact fresh raw exports retain schema 12 profiles and the current compiler identity;
raw bytes also differ from the older schema 11 files for those recorded metadata reasons.
Complete fresh `slices` and `lists` programs (22 raw inputs each) also passed strict
baseline profiles, receipt binding, full normalized-object comparison and unchanged
generated-body comparison. Five further exact raw exports add byte metadata in
`colorName`, `failName`, `dupeZLen`, allocator `dupeZ` and `dupeSentinel`. Together with
the original pair, seven actual raw goldens are retained in Zig 0.16.0 overlays only.
The effective Linux overlay scan covers 251 raw files and finds no remaining byte
sentinel pointer without explicit metadata. Shared and older-version goldens are unchanged.
The ordinary Linux Zig 0.16.0 slices/lists check passed fresh AIR/golden comparison,
the full generated-source guard and both generated-module builds (37 build jobs).
That run used `AIR2LEAN_DIFF=0`; the separate 13-row native qualification above remains
the differential evidence for this feature. Final parent composition/full CI remain pending.

Sampled native
agreement is correspondence evidence, not a preservation theorem or proof of native
allocation success. The model's existing fresh-address, single-allocator and policy
assumptions remain in force. No other target, Zig version or optimization mode is qualified
by this recipe.
