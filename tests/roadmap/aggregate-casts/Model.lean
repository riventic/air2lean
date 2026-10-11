import AggregateCasts.Gen

/-! L07: the translated casts of `AggregateCasts.Gen` against `probe.zig`'s native output.

    lake env lean --run tests/roadmap/aggregate-casts/Model.lean \
      tests/roadmap/aggregate-casts/aarch64-macos-ReleaseSafe.txt

(with the compiled `AggregateCasts.Gen` on `LEAN_PATH`, as `check.sh` does). For each probe
line the model prints the result's memory bytes, `--` for an undefined (padding) byte, or
`unspecified` if the cast throws `.unspecified`. A model `--` byte matches any native byte; a
model `unspecified` line is only recorded, and must be one of `expectUnspecified`: the casts
whose result needs a padding byte. Every other byte must be equal. -/

open AggregateCasts Zig

def hex2 (x : BitVec 8) : String :=
  let s := String.ofList (Nat.toDigits 16 x.toNat)
  if s.length < 2 then "0" ++ s else s

def byteStr : Byte → String
  | .undef => "--"
  | .int x => hex2 x
  | .part _ x => hex2 x
  | _ => "??"

/-- The probe line of a cast result: its encoding, or `unspecified`. -/
def bytesLine {α : Type} [Enc α] (name : String) (r : Result α) : String :=
  match r.run with
  | some (.ok v) => name ++ String.join ((Enc.encode v).toList.map fun b => " " ++ byteStr b)
  | some (.error .unspecified) => s!"{name} unspecified"
  | _ => s!"{name} error"

def valueLine (name : String) (r : Result String) : String :=
  match r.run with
  | some (.ok v) => s!"{name} {v}"
  | _ => s!"{name} error"

def runMem {α : Type} (x : MemM α) : Result α := do
  let (v, _) ← x.run (mem0 .fresh)
  pure v

def x : Ptr := ⟨none, 0x1000⟩

def modelLines : List String := [
  bytesLine "bytes_u32" (bytesToU32 #v[0x11, 0x22, 0x33, 0x44]),
  bytesLine "u32_bytes" (u32ToBytes 0x44332211),
  bytesLine "pair_u64" (pairToU64 ⟨1, 2⟩),
  bytesLine "u64_pair" (u64ToPair 0x0000000200000001),
  bytesLine "bytes_padded.a" ((·.a) <$> bytesToPadded #v[1, 2, 3, 4, 5, 6, 7, 8]),
  bytesLine "bytes_padded.b" ((·.b) <$> bytesToPadded #v[1, 2, 3, 4, 5, 6, 7, 8]),
  bytesLine "padded_bytes" (paddedToBytes ⟨1, 0x05040302⟩),
  bytesLine "u24x2_u56" (u24x2ToU56 #v[0x112233, 0x445566]),
  bytesLine "u56_u24x2" (u56ToU24x2 0x44556600112233),
  bytesLine "u32_word.bytes" (u32ToWord 0x44332211 >>= Word.get_bytes),
  bytesLine "short_u32" (shortToU32 ⟨Raw.init 4 (0x11 : BitVec 8)⟩),
  valueLine "opt_null_addr" (runMem do pure (toString (← optAddr none).toNat)),
  valueLine "opt_from_zero_null" (runMem do pure (toString ((← optFromAddr 0) == none))),
  valueLine "opt_unwrap_same" (runMem do
    pure (toString ((← ptrAddr (← optUnwrap (some x))) == (← ptrAddr x)))),
  valueLine "opt_wrap_addr_same" (runMem do
    pure (toString ((← optAddr (← ptrWrap x)).toNat == (← ptrAddr x).toNat)))]

def expectUnspecified : List String := ["padded_bytes", "u24x2_u56", "short_u32"]

def tokenMatch (model native : String) : Bool := model == "--" || model == native

def lineMatch (model native : String) : Bool :=
  let m := model.splitOn " "
  let n := native.splitOn " "
  match m, n with
  | name :: ["unspecified"], name' :: _ => name == name' && expectUnspecified.contains name
  | _, _ => m.length == n.length && (m.zip n).all fun (a, b) => tokenMatch a b

def main (args : List String) : IO UInt32 := do
  let some path := args.head? | IO.eprintln "usage: Model.lean <probe output>"; return 2
  let native := ((← IO.FS.readFile path).splitOn "\n").filter (· ≠ "")
  let mut ok := native.length == modelLines.length
  unless ok do IO.eprintln s!"line count: native {native.length}, model {modelLines.length}"
  for (m, n) in modelLines.zip native do
    if lineMatch m n then IO.println s!"ok   {m}   (native: {n})"
    else
      ok := false
      IO.eprintln s!"DIFF model: {m}\n     native: {n}"
  -- The unspecified cases are exactly the expected ones.
  let unspecified := modelLines.filterMap fun l =>
    match l.splitOn " " with | [name, "unspecified"] => some name | _ => none
  unless unspecified == expectUnspecified do
    ok := false
    IO.eprintln s!"unspecified cases {unspecified}, expected {expectUnspecified}"
  return if ok then 0 else 1
