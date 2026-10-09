import NoreturnVariants.Gen

/-!
# Tagged unions with a `noreturn` variant (spike blocker B1)

`NoreturnVariants.Gen` is the translation of `air/0.16.0` (`noreturn_variants.zig`); `check.sh`
also runs this file against a fresh translation of `air/0.15.2`. A `noreturn` variant has no
constructor: `U` has `a` and `c`, `V` has `x` and `y`, `One` has `only`, `Io.Terminal.Mode` has
`no_color` and `escape_codes`. The tag enums keep every value the exporter reports (`Kind`: 3, 7,
9), and the memory decoders throw `.illegal` for the tag of a `noreturn` variant.

Each value below is the one `native.zig` checks on the native build of the same source.
Only the function API is used, so the file elaborates against either version's translation.
-/

open NoreturnVariants Zig

namespace NoreturnVariantsClients

/-- The result of running `f` from `mem0`. -/
def result {α : Type} (f : MemM α) : Option (Except Error α) :=
  ((f.run mem0).run).map (·.map Prod.fst)

theorem get_mk : (mk 7 >>= get_air2lean1).run = some (.ok 7) := by decide +kernel

/-- A local `U`: `a`, then `c`. -/
theorem roundTrip_7 : (roundTrip 7).run = some (.ok 8) := by decide +kernel
theorem roundTrip_255 : (roundTrip 255).run = some (.ok 256) := by decide +kernel

/-- `U` in memory: the tag at byte 4, the payload at byte 0 (8 bytes, as the exporter says). -/
theorem memRoundTrip_7 : result (memRoundTrip 7) = some (.ok 9) := by decide +kernel
theorem memRoundTrip_255 : result (memRoundTrip 255) = some (.ok 257) := by decide +kernel

theorem mkV_500 : (mkV 500 >>= vValue).run = some (.ok 500) := by decide +kernel
theorem mkV_0 : (mkV 0 >>= vValue).run = some (.ok 0) := by decide +kernel

/-- The explicit tag values survive: `x = 3`, `y = 9` (`gone = 7` is the `noreturn` one). -/
theorem vTag_x : (vTag 500).run = some (.ok 3) := by decide +kernel
theorem vTag_y : (vTag 0).run = some (.ok 9) := by decide +kernel

/-- `V` in memory: the payload at byte 0, the tag at byte 2. -/
theorem memV_1234 : result (memV 1234) = some (.ok 1234) := by decide +kernel
theorem memV_0 : result (memV 0) = some (.ok 0) := by decide +kernel

theorem oneRoundTrip_max : (oneRoundTrip 65535).run = some (.ok 65535) := by decide +kernel

/-- `std.Io.Terminal.Mode` (0.16.0) or the same shape (0.15.2). -/
theorem colorOf_1 : (colorOf 1).run = some (.ok true) := by decide +kernel
theorem colorOf_0 : (colorOf 0).run = some (.ok false) := by decide +kernel

/-- `Mode` in memory, as a field of `Holder`. -/
theorem holderRoundTrip_color : result (holderRoundTrip true 5) = some (.ok 6) := by
  decide +kernel
theorem holderRoundTrip_plain : result (holderRoundTrip false 5) = some (.ok 5) := by
  decide +kernel

/-- Bytes whose tag (byte 4) names the `noreturn` variant `b` are not a `U`. -/
theorem decode_noreturn_tag :
    (Enc.decode (α := U) #[.int 0, .int 0, .int 0, .int 0, .int 1, .int 0, .int 0, .int 0]).run
      = some (.error .illegal) := by decide +kernel

end NoreturnVariantsClients
