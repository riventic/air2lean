import Air2Lean.Air.Anon
import Air2Lean.Air.Identity

/-! Content-addressed instance names (docs/air-json.md §Instances), without a compiler:
`lake env lean tests/roadmap/instance-identity/Instances.lean`. -/

open Air2Lean

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def failsWith (r : Except String α) (fragment : String) : Bool :=
  match r with
  | .error e => (e.splitOn fragment).length > 1
  | .ok _ => false

private def json (s : String) : Lean.Json := (Lean.Json.parse s).toOption.get!

private def keyA := "a1b2c3d4e5f60718293a4b5c6d7e8f90a1b2c3d4e5f60718293a4b5c6d7e8f90"
private def keyB := "b1b2c3d4e5f60718293a4b5c6d7e8f90a1b2c3d4e5f60718293a4b5c6d7e8f90"

/-- A file of function `name` (with `key`) that calls each `(callee, key?)`. -/
private def file (name : String) (key : Option String) (calls : List (String × Option String)) :
    String :=
  let k (field : String) : Option String → String
    | some v => s!", \"{field}\": \"{v}\""
    | none => ""
  let body := ", ".intercalate (calls.map fun (c, ck) =>
    s!"\{\"callee\": \{\"func\": \"{c}\", \"module\": \"std\"{k "instance_key" ck}}}")
  s!"\{\"name\": \"{name}\", \"module\": \"std\"{k "instance_key" key}, \"body\": [{body}]}"

/-- The own names of `texts` after renaming. -/
private def names (texts : Array String) : Array String :=
  (Anon.renumberAll texts).map fun t =>
    ((json t).getObjValAs? String "name").toOption.getD ""

#eval show IO Unit from do
  -- A keyed instance gets its key's digits, whatever its compiler number and the input order;
  -- an unkeyed one a number by first use, as before.
  let prog (n m : Nat) := #[
    file "main.f" none [(s!"mem.dupe__anon_{n}", some keyA), (s!"mem.free__anon_{m}", none)],
    file s!"mem.dupe__anon_{n}" (some keyA) [],
    file s!"mem.free__anon_{m}" none []]
  let expected := #["main.f", "mem.dupe__anon_a1b2c3d4e5f6", "mem.free__anon_1"]
  require (names (prog 16959 77) == expected) s!"keyed names: {names (prog 16959 77)}"
  require (names (prog 5 123456) == expected) "a different compilation gives different names"
  require (names (prog 5 123456).reverse == expected.reverse) "the input order changes names"
  require (((Anon.renumberAll (prog 16959 77))[0]!.splitOn "\"func\":\"mem.dupe__anon_a1b2c3d4e5f6\"").length == 2)
    "reference not renamed"
  -- Without keys (a legacy export) nothing changes.
  let legacy := #[file "main.f" none [("mem.dupe__anon_16959", none)], file "mem.dupe__anon_16959" none []]
  require (names legacy == #["main.f", "mem.dupe__anon_1"]) "legacy renumbering changed"
  -- Emission order of a keyed program: the content-addressed names.
  let (order, _) := Anon.renumberAllWithNames #[file "mem.dupe__anon_9" (some keyB) [],
    file "mem.dupe__anon_10" (some keyA) []]
  require (order == #["mem.dupe__anon_b1b2c3d4e5f6", "mem.dupe__anon_a1b2c3d4e5f6"]) s!"order names {order}"
  -- Identity records carry the key; a name that is not its key's, or a malformed key, fails.
  let records (s : String) := (Identity.rewrite (json s)).map (·.2)
  require (match records (file "mem.dupe__anon_a1b2c3d4e5f6" (some keyA) []) with
    | .ok #[r] => r.instanceKey == some keyA | _ => false) "own instance key not recorded"
  require (failsWith (records (file "mem.dupe__anon_a1b2c3d4e5f6" (some keyB) [])) "names another instance")
    "a name with another key's digits accepted"
  require (failsWith (records (file "mem.dupe__anon_1" (some keyA) [])) "names another instance")
    "a numbered name with a key accepted"
  require (failsWith (records (file "mem.dupe__anon_1" (some "ABC") [])) "64 lower-case hex")
    "malformed key accepted"
  -- One compiler name with two keys (two compilations): the second keeps the first's name and
  -- is rejected.
  let mixed := Anon.renumberAll #[file "mem.dupe__anon_7" (some keyA) [],
    file "main.g" none [("mem.dupe__anon_7", some keyB)]]
  require (failsWith (Identity.rewrite (json mixed[1]!)) "names another instance") "two keys for one name accepted"
  -- Two keys with one name (a 48-bit prefix collision): checkProgram rejects them.
  let r (k : String) : Identity.Record :=
    { key := "mem.dupe__anon_a1b2c3d4e5f6", module := some "std", name := "mem.dupe__anon_a1b2c3d4e5f6", instanceKey := some k }
  require (failsWith (Identity.checkProgram #[#[r keyA], #[r ((keyA.take 63).toString ++ "1")]]) "names both")
    "two instance keys with one name accepted"
  require (Identity.checkProgram #[#[r keyA], #[r keyA]]).toOption.isSome "one instance in two files rejected"
  IO.println "instance identity unit checks passed"
