-- TEMPORARY (F0 libm spike): the Lean side, via @[extern] into libm.a.
@[extern "air2lean_libm_sin_f64"] opaque sin64 (x : UInt64) : UInt64
@[extern "air2lean_libm_exp_f64"] opaque exp64 (x : UInt64) : UInt64
@[extern "air2lean_libm_log_f32"] opaque log32 (x : UInt64) : UInt64
@[extern "air2lean_libm_sin_f80_hi"] opaque sin80hi (hi lo : UInt64) : UInt64
@[extern "air2lean_libm_sin_f80_lo"] opaque sin80lo (hi lo : UInt64) : UInt64
@[extern "air2lean_libm_sin_f128_hi"] opaque sin128hi (hi lo : UInt64) : UInt64
@[extern "air2lean_libm_sin_f128_lo"] opaque sin128lo (hi lo : UInt64) : UInt64

def hexVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10

def parseHex (s : String) : Nat := s.foldl (fun n c => n * 16 + hexVal c) 0

def hex (n : Nat) : String := String.mk (Nat.toDigits 16 n)

def wide (f : UInt64 → UInt64 → UInt64) (g : UInt64 → UInt64 → UInt64) (x : Nat) : Nat :=
  let hi := (x >>> 64).toUInt64
  let lo := (x % 2 ^ 64).toUInt64
  (f hi lo).toNat * 2 ^ 64 + (g hi lo).toNat

def main (args : List String) : IO Unit := do
  for l in ← IO.FS.lines args[0]! do
    let cols := l.splitOn " "
    let op := cols[0]!
    let x := parseHex cols[1]!
    let y := match op with
      | "sin64" => (sin64 x.toUInt64).toNat
      | "exp64" => (exp64 x.toUInt64).toNat
      | "log32" => (log32 x.toUInt64).toNat
      | "sin80" => wide sin80hi sin80lo x
      | _ => wide sin128hi sin128lo x
    IO.println s!"{op} {cols[1]!} {hex y}"
