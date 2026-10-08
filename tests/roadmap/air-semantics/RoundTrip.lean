import Air2Lean.Main
import Air2Lean.Certificate
import Proofs.Basic.AirCert
import Proofs.Recursion.AirCert

/-! The printed `Func` terms of the committed certificates are the decoded AIR.

`Certificate.printFunc` prints every field of a `Func` with its constructor, so it is
injective; a term whose print equals the print of the freshly decoded golden file is that
decoded `Func`. Run from the repository root: `lake env lean tests/roadmap/air-semantics/RoundTrip.lean`.
-/

open Air2Lean

def checkTable (dir : System.FilePath) (table : Sem.Table) : IO Unit := do
  let entries ← dir.readDir
  let texts ← (entries.filter (·.fileName.endsWith ".json")).mapM (IO.FS.readFile ·.path)
  let (_, texts) := Anon.renumberAllWithNames texts
  let decoded ← texts.mapM fun t => IO.ofExcept (processOne t)
  for (name, f) in table do
    let some g := decoded.find? (·.name == name)
      | throw (IO.userError s!"{name}: no golden AIR file")
    unless Certificate.printFunc f == Certificate.printFunc g && (Certificate.printFunc g).isSome do
      throw (IO.userError s!"{name}: the certificate's AIR is not the decoded golden AIR")
  IO.println s!"{dir}: {table.length} certified AIR terms equal the decoded golden files"

#eval checkTable "tests/golden/basic/air" Basic.AirCert.table
#eval checkTable "tests/golden/recursion/air" Recursion.AirCert.table
