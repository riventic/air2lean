import LangLongTail.ExternStorage

/-! L12: the translated `extern_storage.zig` against `probe_extern_storage.zig`'s native output,
the probe linked with `provider_extern_storage.c`.

    lake env lean --run tests/roadmap/lang-long-tail/ModelExternStorage.lean <native output>

(with the compiled `LangLongTail.ExternStorage` of a version on `LEAN_PATH`, as `check.sh` does)
runs the probe's calls in order from `mem0 .fresh provider`, where `provider` is the
`ExternInit` of the C file: the values of its four definitions, and its static storage (`n1`,
`n2`, the string literal, `slot_target`) as the external blocks after the program's globals. It
fails unless the native file has exactly the model's lines. -/

open ExternStorage Zig

/-- The number of the program's own blocks: the first external block's id. -/
def firstExternal : Nat :=
  let blank : ExternInit :=
    { ext_counter := 0, ext_name := ⟨none, 0⟩, ext_head := none, ext_slot := ⟨none, 0⟩, storage := [] }
  (mem0 .fresh blank).blocks.size

def ptrTo (i : Nat) : Ptr := ⟨some (firstExternal + i), 0⟩

/-- `provider_extern_storage.c`: `n1` (block 0) → `n2` (block 1), `"provider"` (block 2, the
literal: read-only), `slot_target` (block 3). -/
def provider : ExternInit where
  ext_counter := 41
  ext_name := ptrTo 2
  ext_head := some (ptrTo 0)
  ext_slot := ptrTo 3
  storage := [
    { bytes := Enc.encode ({ v := 5, next := some (ptrTo 1) } : Node), align := 8, writable := true },
    { bytes := Enc.encode ({ v := 7, next := none } : Node), align := 8, writable := true },
    { bytes := "provider".toUTF8.toList.toArray.map (fun b => .int (BitVec.ofNat 8 b.toNat)) ++ #[.int 0],
      align := 1, writable := false },
    { bytes := Enc.encode (9 : BitVec 32), align := 4, writable := true }]

/-- The probe's calls, in order, on one memory. -/
def calls : List (String × MemM (BitVec 32)) :=
  [("sumList", sumList), ("nameLen", nameLen), ("slotValue", slotValue),
   ("pushLocal", pushLocal), ("counter", counter), ("slotValue", slotValue), ("sumList", sumList)]

def modelLines : List String := Id.run do
  let mut m := mem0 .fresh provider
  let mut out := []
  for (name, f) in calls do
    match (f.run m).run with
    | some (.ok (v, m')) => m := m'; out := out ++ [s!"{name} {v.toNat}"]
    | some (.error e) => out := out ++ [s!"{name} model-error {repr e}"]; break
    | none => out := out ++ [s!"{name} model-none"]; break
  return out

def main (args : List String) : IO UInt32 := do
  let [path] := args | IO.eprintln "usage: ModelExternStorage.lean <native output>"; return 2
  let native := (← IO.FS.lines path).toList.filter (· ≠ "")
  if native == modelLines then
    IO.println s!"extern_storage: {modelLines.length} native lines match the model"
    return 0
  IO.eprintln "extern_storage: the native output differs from the model"
  for m in modelLines do IO.eprintln s!"  model:  {m}"
  for n in native do IO.eprintln s!"  native: {n}"
  return 1
