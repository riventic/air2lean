import Air2Lean.Main
import Air2Lean.Certificate
import Proofs.Basic.AirCert
import Proofs.Errors.AirCert
import Proofs.Iogroup.AirCert
import Proofs.Options.AirCert
import Proofs.Pointers.AirCert
import Proofs.Recursion.AirCert
import Proofs.Threads.AirCert
import Proofs.Vectors.AirCert

/-! The printed `Func` terms of the committed certificates (every one that certifies a function) are
the decoded AIR.

`Certificate.printFunc` quotes every constructor and field, including functions outside the
certificate fragment. Compare the complete original program first, then check every selected
name against that program's lookup. Run from the repository root:
`lake env lean tests/roadmap/air-semantics/RoundTrip.lean`.
-/

open Air2Lean

def checkTable (dir : System.FilePath) (table : Sem.Table) (program : Program) : IO Unit := do
  let entries ← dir.readDir
  let texts ← (entries.filter (·.fileName.endsWith ".json")).mapM (IO.FS.readFile ·.path)
  let (_, texts) := Anon.renumberAllWithNames texts
  let decoded ← texts.mapM fun t => IO.ofExcept (processOne t)
  unless (program.funcs.map (·.name)).toList.eraseDups.length == program.funcs.size &&
      (decoded.map (·.name)).toList.eraseDups.length == decoded.size do
    throw (IO.userError s!"{dir}: duplicate names prevent complete original-program binding")
  unless program.funcs.size == decoded.size do
    throw (IO.userError s!"{dir}: the original program omits or adds AIR functions")
  for f in program.funcs do
    let some g := decoded.find? (·.name == f.name)
      | throw (IO.userError s!"{f.name}: no golden AIR file")
    unless Certificate.printFunc f == Certificate.printFunc g && (Certificate.printFunc g).isSome do
      throw (IO.userError s!"{f.name}: the original program's AIR is not the decoded golden AIR")
  for name in table do
    unless (program.lookup name).isSome do
      throw (IO.userError s!"{name}: certified name is absent from its original program")
  IO.println s!"{dir}: {program.funcs.size} original AIR terms and {table.length} certified names bound"

#eval checkTable "tests/golden/basic/air" Basic.AirCert.table Basic.AirCert.program
#eval checkTable "tests/golden/basic/air" Basic.AirCert.views Basic.AirCert.program
#eval checkTable "tests/golden/errors/air" Errors.AirCert.table Errors.AirCert.program
#eval checkTable "tests/golden/iogroup/air" Iogroup.AirCert.table Iogroup.AirCert.program
#eval checkTable "tests/golden/options/air" Options.AirCert.views Options.AirCert.program
#eval checkTable "tests/golden/pointers/air" Pointers.AirCert.table Pointers.AirCert.program
#eval checkTable "tests/golden/recursion/air" Recursion.AirCert.table Recursion.AirCert.program
#eval checkTable "tests/golden/threads/air" Threads.AirCert.table Threads.AirCert.program
#eval checkTable "tests/golden/vectors/air" Vectors.AirCert.table Vectors.AirCert.program
