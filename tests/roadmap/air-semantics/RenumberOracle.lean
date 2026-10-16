import Air2Lean.CanonCertificate
import Air2Lean.Check

/-!
Audit regression: full live-ID renumbering cannot preserve `Sem.execFunc` for the same
arbitrary oracle. This is a counterexample to that proposed compiler-correctness equality,
not a native Zig or whole-program execution counterexample. The checked identity callee
does not manufacture a caller cell; the unrestricted per-function oracle does.
-/

namespace CanonRenumberOracle

open Air2Lean Air2Lean.Sem

def caller (base : Nat) (identities : Array Identity.Record := #[]) : Func :=
  { dialect := .ofVersion .v0_17_0, name := "canon.caller", params := #[1], ret := 0,
    types := #[.bool, .ptr "one" false 0, .void, .noreturn],
    layouts := #[{ size := some 1, align := some 1 },
      { size := some 8, align := some 8, ptrAlign := some 1 },
      { size := some 0, align := some 1 }, {}],
    globals := #[], identities,
    body := #[
      ⟨base, 1, .arg 0⟩,
      ⟨base + 1, 1, .alloc⟩,
      ⟨base + 2, 2, .store (.inst (base + 1)) (.bool false)⟩,
      ⟨base + 3, 2, .store (.inst (base + 1)) (.bool true)⟩,
      ⟨base + 4, 1, .call (.func "canon.identity" false none) #[.inst base]⟩,
      ⟨base + 5, 0, .load (.inst (base + 4))⟩,
      ⟨base + 6, 3, .ret (.inst (base + 5))⟩] }

def identity : Func :=
  { (caller 0) with
    name := "canon.identity"
    ret := 1
    body := #[⟨0, 1, .arg 0⟩, ⟨1, 3, .ret (.inst 0)⟩] }

def oracle : Oracle := fun _ _ => pure (.cell 11)

theorem identity_not_panic : panicOf? "canon.identity" = none := by rfl

theorem before_run (records : Array Identity.Record) (m : Zig.Mem) (p : Zig.Ptr) :
    ((execFunc oracle (caller 10 records) [.ptr p]).run m).run =
      some (.ok (.bool true, m)) := by
  simp only [caller, oracle, air_sem, Nat.reduceAdd, identity_not_panic] <;> rfl

theorem after_run (records : Array Identity.Record) (m : Zig.Mem) (p : Zig.Ptr) :
    ((execFunc oracle (caller 0 records) [.ptr p]).run m).run =
      some (.error .unspecified) := by
  simp only [caller, oracle, air_sem, Nat.reduceAdd, identity_not_panic] <;> rfl

theorem same_oracle_not_preserved (records : Array Identity.Record) (m : Zig.Mem) (p : Zig.Ptr) :
    (execFunc oracle (caller 10 records) [.ptr p]).run m ≠
      (execFunc oracle (caller 0 records) [.ptr p]).run m := by
  intro h
  have h' := congrArg (fun r => r.run) h
  rw [before_run, after_run] at h'
  cases h'

def source : String := r#"{
  "schema": 11, "zig_version": "0.17.0", "name": "canon.caller", "params": [1], "ret": 0,
  "types": [
    {"k": "bool", "abi_size": 1, "abi_align": 1},
    {"k": "ptr", "size": "one", "const": false, "child": 0,
     "abi_size": 8, "abi_align": 8, "ptr_align": 1},
    {"k": "void", "abi_size": 0, "abi_align": 1}, {"k": "noreturn"}],
  "body": [
    {"id": 10, "tag": "arg", "ty": 1, "param": 0},
    {"id": 11, "tag": "alloc", "ty": 1},
    {"id": 12, "tag": "store", "ty": 2, "args": [{"inst": 11}, {"ty": 0, "val": "false"}]},
    {"id": 13, "tag": "store", "ty": 2, "args": [{"inst": 11}, {"ty": 0, "val": "true"}]},
    {"id": 14, "tag": "call", "ty": 1, "callee": {"func": "canon.identity"}, "args": [{"inst": 10}]},
    {"id": 15, "tag": "load", "ty": 0, "args": [{"inst": 14}]},
    {"id": 16, "tag": "ret", "ty": 3, "args": [{"inst": 15}]}]
}"#

-- Native acceptance/binding checks are separate from the kernel-checked non-equality.
-- Two stores keep the preceding copy-forwarding pass from deleting the local.
#eval IO.ofExcept do
  let raw ← Raw.parseFile source
  Raw.validateRefs raw
  let before ← normalizeCanonical raw
  let after ← normalizeCanonical (Raw.renumber raw)
  if CanonCertificate.printFunc before != CanonCertificate.printFunc (caller 10 raw.identities) then
    throw "decoding did not produce the counterexample source"
  if CanonCertificate.printFunc after != CanonCertificate.printFunc (caller 0 raw.identities) then
    throw "renumbering did not produce the counterexample target"
  if CanonCertificate.printFunc (← normalize raw) != CanonCertificate.printFunc (caller 0 raw.identities) then
    throw "another canonicalization pass changed the counterexample"
  checkProgram #[before, identity]
  checkProgram #[after, identity]

end CanonRenumberOracle
