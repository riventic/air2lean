import ErrorWidth16.Gen
import ErrorWidth8.Gen
import ErrorWidth10.Gen
import ErrorWidth17.Gen

/-! Executes the generated fixtures of every error width (`check.sh` translates them first).
Each width stores and reloads `E`, `?E`, `E!u8` and `E!u64` through the generated code and
the width's own storage dictionaries, and checks the stored bytes have the width's size. -/

open Zig

deriving instance DecidableEq for Except

private def check [DecidableEq α] [Repr α] (name : String) (actual expected : α) : IO Unit := do
  unless actual = expected do
    throw (IO.userError s!"{name}: expected {reprStr expected}, got {reprStr actual}")

private def value (x : MemM α) : Option (Except Error α) :=
  (x.run {}).run.map (·.map Prod.fst)

private def domain : ErrorDomain := ⟨#["Bad", "Other"], by decide, by decide⟩

/-- The generated API, identical for every width. -/
structure Fns where
  storeError : Ptr → ErrName → MemM ErrName
  storeOptional : Ptr → Option ErrName → MemM Bool
  loadOptional : Ptr → MemM (Option ErrName)
  unionTry8 : Ptr → Except ErrName (BitVec 8) → MemM (Except ErrName (BitVec 8))
  unionTry64 : Ptr → Except ErrName (BitVec 64) → MemM (Except ErrName (BitVec 64))
  setPayload : Ptr → BitVec 8 → MemM Bool
  loadUnion : Ptr → MemM (Except ErrName (BitVec 8))

private def union8 (bits : Nat) : Enc (Except ErrName (BitVec 8)) :=
  errorUnionEncW bits domain inferInstance

private def run (bits : Nat) (f : Fns) : IO Unit := do
  let n := errCodeSize bits
  let a := errCodeAlign bits
  let u8 := union8 bits
  let tag (s : String) := s!"{bits}-bit {s}"
  -- E: store then load, both named errors; a foreign name never reloads.
  for e in ["Bad", "Other"] do
    check (tag s!"store/load {e}") (value do f.storeError (← alloc .heap n a) e) (some (.ok e))
  check (tag "foreign name") (value do f.storeError (← alloc .heap n a) "Nope")
    (some (.error .unspecified))
  -- ?E: null and members.
  check (tag "?E null") (value do f.storeOptional (← alloc .heap n a) none) (some (.ok false))
  check (tag "?E some") (value do f.storeOptional (← alloc .heap n a) (some "Other")) (some (.ok true))
  check (tag "?E reload") (value do
      let p ← alloc .heap n a
      storeBytes p a ((optionalErrorEncW bits domain).encode (some "Bad"))
      f.loadOptional p) (some (.ok (some "Bad")))
  check (tag "?E bytes") ((optionalErrorEncW bits domain).encode (some "Bad")).size n
  -- E!u8 and E!u64: the union is stored whole, then read through pointer-form try.
  for v in [(.error "Bad" : Except ErrName (BitVec 8)), .error "Other", .ok 7] do
    check (tag s!"E!u8 try {reprStr v}") (value do
        f.unionTry8 (← alloc .heap u8.size u8.align) v) (some (.ok v))
  let u64 : Enc (Except ErrName (BitVec 64)) := errorUnionEncW bits domain inferInstance
  for v in [(.error "Other" : Except ErrName (BitVec 64)), .ok 0x0123456789abcdef] do
    check (tag s!"E!u64 try {reprStr v}") (value do
        f.unionTry64 (← alloc .heap u64.size u64.align) v) (some (.ok v))
  -- errunion_payload_ptr_set writes the zero code; the union then reloads as the payload.
  check (tag "payload set") (value do
      let p ← alloc .heap u8.size u8.align
      let r ← f.setPayload p 5
      pure (r, ← f.loadUnion p)) (some (.ok (false, .ok 5)))
  -- A union stored with this width's dictionary reloads with its error.
  check (tag "union reload") (value do
      let p ← alloc .heap u8.size u8.align
      storeBytes p u8.align (u8.encode (.error "Other"))
      f.loadUnion p) (some (.ok (.error "Other")))
  check (tag "E!u8 bytes") (u8.encode (.error "Bad")).size u8.size

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
  check "E!u8 sizes" ([16, 8, 10, 17].map fun b => (union8 b).size) [4, 2, 4, 8]
  -- A narrower code is not a complete wider code. (Every function of one program has the
  -- same profile, so mixed-width storage does not arise from translated code.)
  check "8-bit bytes at 16 bits" ((errorEncW 16 domain).decode ((errorEncW 8 domain).encode "Bad")).run
    (some (.error .unspecified))
  check "16-bit bytes at 17 bits" ((errorEncW 17 domain).decode ((errorEncW 16 domain).encode "Bad")).run
    (some (.error .unspecified))
  IO.println "error widths 16, 8, 10, 17: generated stores, loads, unions and try passed"
