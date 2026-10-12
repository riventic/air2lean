import ZigLean.Mem.ErrWidth

/-! The runtime checks shared by `Runtime.lean` (hand-written fixtures) and the generated
`RuntimeExport.lean` (compiler exports). Each width stores and reloads `E`, `?E`, `E!u8` and `E!u64` through the generated code and the
width's own storage dictionaries, and checks the stored bytes have the width's size. -/

open Zig

namespace ErrorWidthRun

deriving instance DecidableEq for Except

def check [DecidableEq α] [Repr α] (name : String) (actual expected : α) : IO Unit := do
  unless actual = expected do
    throw (IO.userError s!"{name}: expected {reprStr expected}, got {reprStr actual}")

def value (x : MemM α) : Option (Except Error α) :=
  (x.run {}).run.map (·.map Prod.fst)

def domain : ErrorDomain := ⟨#["Bad", "Other"], by decide, by decide⟩

/-- The generated API, identical for every width. -/
structure Fns where
  storeError : Ptr → ErrName → MemM ErrName
  storeOptional : Ptr → Option ErrName → MemM Bool
  loadOptional : Ptr → MemM (Option ErrName)
  unionTry8 : Ptr → Except ErrName (BitVec 8) → MemM (Except ErrName (BitVec 8))
  unionTry64 : Ptr → Except ErrName (BitVec 64) → MemM (Except ErrName (BitVec 64))
  setPayload : Ptr → BitVec 8 → MemM Bool
  loadUnion : Ptr → MemM (Except ErrName (BitVec 8))

abbrev union8 (bits : Nat) : Enc (Except ErrName (BitVec 8)) :=
  errorUnionEncW bits domain inferInstance

def run (bits : Nat) (f : Fns) : IO Unit := do
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
  -- A store defines the `errValueSize` value bytes; a padding byte after them (17 to 24 bits)
  -- is undefined and is not read: a code whose padding holds any byte reloads unchanged.
  check (tag "defined code bytes")
    ((errBytesW bits (some "Bad")).toList.filter (· != .undef)).length (errValueSize bits)
  check (tag "padding not read") (value do
      let p ← alloc .heap n a
      storeBytes p a (writeBytes (errBytesW bits (some "Other")) (errValueSize bits)
        (Array.replicate (n - errValueSize bits) (.int 0xaa)))
      f.loadOptional p) (some (.ok (some "Other")))
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

end ErrorWidthRun
