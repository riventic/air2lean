import PackedCasts.V0_15_2.OptItemsX64

/-! `opt_items.zig` exported for the self-hosted x86_64 backend (`air/<version>/opt_items_x64`):
its representation casts decode a payload with padding bits with the profile's storage encoding
(`Dialect.intPadding` `.extended`, `Zig.intEncExt`). The backend reads a `u24` payload's padding
byte as part of the value (in a 0.15.2 Debug x86_64 build, `intToU24s` of the bytes
`56 34 12 77` returns `0x77123456`), so the model says `.unspecified` there, where the LLVM
model (`ModelOpt.intToU24s_padding`) ignores the byte. Written for Zig 0.15.2; the module of
0.14.1 is that one with the version renamed. -/

open Zig PackedCasts.V0_15_2.OptItemsX64

namespace PackedCasts.V0_15_2.ModelOptX64

theorem intToU24s_padding : (intToU24s 0x00000001771234560000000000000000#128).run =
    some (.error .unspecified) := by
  decide +kernel
/-- Padding that is the payload's zero extension: the value. -/
theorem intToU24s_ok : (intToU24s 0x00000001001234560000000000000000#128).run =
    some (.ok 0x123456) := by
  decide +kernel
/-- Items without padding bits decode as on the LLVM backend. -/
theorem intToU8s_ok : (intToU8s 0x01340012#32).run = some (.ok 0x34) := by decide +kernel

end PackedCasts.V0_15_2.ModelOptX64
