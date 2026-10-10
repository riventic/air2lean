import ErrorWidthRun
import ErrorWidth16.Gen
import ErrorWidth8.Gen
import ErrorWidth10.Gen
import ErrorWidth17.Gen

/-! Executes the generated hand-written fixtures of every error width (`check.sh` translates
them first); `ErrorWidthRun.run` (`RunCommon.lean`) holds the checks. -/

open Zig ErrorWidthRun

deriving instance DecidableEq for Except

def main : IO Unit := do
  run 16 ⟨ErrorWidth16.storeError, ErrorWidth16.storeOptional, ErrorWidth16.loadOptional,
    ErrorWidth16.unionTry8, ErrorWidth16.unionTry64, ErrorWidth16.setPayload, ErrorWidth16.loadUnion⟩
  run 8 ⟨ErrorWidth8.storeError, ErrorWidth8.storeOptional, ErrorWidth8.loadOptional,
    ErrorWidth8.unionTry8, ErrorWidth8.unionTry64, ErrorWidth8.setPayload, ErrorWidth8.loadUnion⟩
  run 10 ⟨ErrorWidth10.storeError, ErrorWidth10.storeOptional, ErrorWidth10.loadOptional,
    ErrorWidth10.unionTry8, ErrorWidth10.unionTry64, ErrorWidth10.setPayload, ErrorWidth10.loadUnion⟩
  run 17 ⟨ErrorWidth17.storeError, ErrorWidth17.storeOptional, ErrorWidth17.loadOptional,
    ErrorWidth17.unionTry8, ErrorWidth17.unionTry64, ErrorWidth17.setPayload, ErrorWidth17.loadUnion⟩
  -- The widths really differ: 2, 1, 2 and 4 code bytes; E!u8 is 4, 2, 4 and 8 bytes.
  check "code sizes" ([16, 8, 10, 17].map errCodeSize) [2, 1, 2, 4]
  -- A store writes `ceil(bits / 8)` bytes: the 4-byte code of 17 to 24 bits has one padding byte.
  check "code value bytes" ([16, 8, 10, 17, 24, 25].map errValueSize) [2, 1, 2, 3, 3, 4]
  check "E!u8 sizes" ([16, 8, 10, 17].map fun b => (union8 b).size) [4, 2, 4, 8]
  -- A narrower code is not a complete wider code. (Every function of one program has the
  -- same profile, so mixed-width storage does not arise from translated code.)
  check "8-bit bytes at 16 bits" ((errorEncW 16 domain).decode ((errorEncW 8 domain).encode "Bad")).run
    (some (.error .unspecified))
  check "16-bit bytes at 17 bits" ((errorEncW 17 domain).decode ((errorEncW 16 domain).encode "Bad")).run
    (some (.error .unspecified))
  IO.println "error widths 16, 8, 10, 17: generated stores, loads, unions and try passed"
