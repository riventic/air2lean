
open Zig

deriving instance DecidableEq for Except
private def storageDomain : ErrorDomain := ⟨#["Alpha", "Beta", "Gamma"], by decide, by decide⟩
private def observe (name : ErrName) : MemM (Array Bool) := do
  letI : Enc ErrName := errorEnc storageDomain
  letI : Enc (Option ErrName) := optionalErrorEnc storageDomain
  letI : Enc (Vector (Option ErrName) 3) := Enc.vectorWith 3 (optionalErrorEnc storageDomain)
  let p ← alloc .heap 6 2
  store 2 p (⟨#[some "Gamma", none, some "Beta"], rfl⟩ : Vector (Option ErrName) 3)
  let got ← ErrorStorage.overwrite p name
  let slots ← load (Vector (Option ErrName) 3) 2 p
  let e ← alloc .heap 2 2
  store 2 e "Alpha"
  let written ← ErrorStorage.writeError e name
  let read ← ErrorStorage.readError e
  let optional ← alloc .heap 2 2
  store 2 optional (none : Option ErrName)
  let payload ← ErrorStorage.writePayload optional name
  let optionalGot ← load (Option ErrName) 2 optional
  let global ← ErrorStorage.globalRoundtrip name
  let globalStatus ← load ErrorStorage.Status 2 ⟨some @STATUS_BLOCK@, 0⟩
  let globalSlots ← load (Vector (Option ErrName) 3) 2 ⟨some @SLOTS_BLOCK@, 0⟩
  let propagation ← ErrorStorage.propagate e
  let nestedEnc := Enc.optionWith (optionalErrorEnc storageDomain)
  let outer ← alloc .heap 4 2
  letI : Enc (Option (Option ErrName)) := nestedEnc
  store 2 outer (none : Option (Option ErrName))
  let nested ← ErrorStorage.nestedOuter outer none
  let nestedStored ← load (Option (Option ErrName)) 2 outer
  let nestedError ← ErrorStorage.nestedOuter outer (some name)
  let nestedErrorStored ← load (Option (Option ErrName)) 2 outer
  letI : Enc (Except ErrName ErrorStorage.ErrorPayload) := errorUnionEnc storageDomain inferInstance
  let unionCell ← alloc .heap (Enc.size (Except ErrName ErrorStorage.ErrorPayload)) 2
  store 2 unionCell (.error "Gamma" : Except ErrName ErrorStorage.ErrorPayload)
  let unionSuccess ← ErrorStorage.payloadUnion unionCell name false
  let unionSuccessStored ← load (Except ErrName ErrorStorage.ErrorPayload) 2 unionCell
  let unionError ← ErrorStorage.payloadUnion unionCell name true
  let unionErrorStored ← load (Except ErrName ErrorStorage.ErrorPayload) 2 unionCell
  pure #[got == some name, slots[0] == none && slots[2] == some "Beta",
    written == name && read == name, payload == "Gamma" && optionalGot == some "Gamma",
    global == some name && globalStatus.guard == (37 : BitVec 16) && globalStatus.pending == some name && globalStatus.last == name && globalSlots[0] == none && globalSlots[2] == some "Beta",
    propagation == .error name,
    nested == some none && nestedStored == some none && nestedError == some (some name) && nestedErrorStored == some (some name),
    (match unionSuccess, unionSuccessStored with | .ok a, .ok b => a.code == name && b.code == name | _, _ => false),
    unionError == .error name && unionErrorStored == .error name]
private def storageSucceeded (name : ErrName) : Bool :=
  match (observe name).run ErrorStorage.mem0 |>.run with
  | some (.ok (bits, _)) => bits.size == 9 && bits.all id
  | _ => false
-- Concrete proofs over the fresh generated definitions and their actual global layout.
example : storageSucceeded "Alpha" = true := by native_decide
example : storageSucceeded "Beta" = true := by native_decide
example : storageSucceeded "Gamma" = true := by native_decide
private def digit (b : Bool) := if b then "1" else "0"
def main : IO Unit := do
  for name in #["Alpha", "Beta", "Gamma"] do
    match (observe name).run ErrorStorage.mem0 |>.run with
    | some (.ok (bits, _)) => IO.println (name ++ " " ++ String.intercalate " " (bits.toList.map digit))
    | _ => throw (IO.userError s!"storage observation failed: {name}")
