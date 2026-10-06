import Air2Lean.TimedEmit
import Air2Lean.Air.StrictJson

/-! ROOT-only source translation driver. It never executes the generated program.
Ordinary translator CLI behavior is unchanged. -/
def main (args : List String) : IO UInt32 := do
  let [directory, output] := args
    | do IO.eprintln "usage: Translate.lean <retained-air-directory> <generated-output>"; return 2
  let entries ← (System.FilePath.mk directory).readDir
  let files := (entries.filter fun e => e.fileName.endsWith ".json").qsort
    (fun a b => decide (a.fileName < b.fileName))
  let contents ← files.mapM (fun e => Air2Lean.StrictJson.readFile e.path)
  match Air2Lean.Timed.translateSelected contents "DeadlineActual" "probe." with
  | .error error => IO.eprintln error; return 1
  | .ok generated => IO.FS.writeFile output generated; return 0
