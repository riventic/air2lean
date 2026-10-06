import Air2Lean.Air.Anon

/-! Root/CI API regression; the author never invokes a compiler. -/
open Air2Lean Lean

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

#eval do
  let texts := #[
    "{\"name\":\"order.generic__anon_9\",\"source\":\"order.generic__anon_9\"}",
    "{\"name\":\"order.generic__anon_10\"}",
    "{\"name\":\"order.root\",\"body\":[{\"callee\":{\"func\":\"order.generic__anon_9\"}},{\"callee\":{\"func\":\"order.generic__anon_10\"}}],\"types\":[{\"name\":\"payload__struct_99\"},{\"name\":\"tag__enum_77\"},{\"name\":\"data__union_55\"},{\"name\":\"token__opaque_33\"}]}",
    "{\"body\":[]}", "{\"name\":9}", "\"scalar\"", "not JSON"]
  let (names, rewritten) := Anon.renumberAllWithNames texts
  require (names == #["order.generic__anon_9", "order.generic__anon_10", "order.root",
    "", "", "", ""]) "combined pipeline lost original/missing/malformed name semantics"
  require (names == texts.map Anon.fnName) "combined names differ from public fnName"
  let individual := ["__anon_", "__struct_", "__enum_", "__union_", "__opaque_"].foldl
    (fun current marker => Anon.renumberAnon current marker) texts
  require (rewritten == individual) "combined pipeline changed marker/first-use traversal"
  require (rewritten == Anon.renumberAll texts) "public renumberAll wrapper changed output"
  require (rewritten[6]? == some "not JSON") "malformed input was replaced"
  require (rewritten[5]? == some "\"scalar\"") "valid scalar fallback changed"
  require (rewritten[0]?.map Anon.fnName == some "order.generic__anon_1")
    "first reached raw instance was not renamed to one"
  require (rewritten[1]?.map Anon.fnName == some "order.generic__anon_2")
    "second reached raw instance was not renamed to two"
  let some first := rewritten[0]? | throw (IO.userError "missing rewritten first fixture")
  let first ← match Json.parse first with
    | .ok value => pure value
    | .error e => throw (IO.userError e)
  require ((first.getObjValAs? String "source").toOption == some "order.generic__anon_9")
    "observable source string was renamed"
  IO.println "combined anonymous-name and ordering API passed"
