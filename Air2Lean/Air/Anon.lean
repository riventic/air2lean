import Std.Data.HashMap
import Std.Data.HashSet
import Lean.Data.Json

/-!
# Stable names of generic instances

The compiler names each instance of a generic function `<name>__anon_<n>`
(`mem.Allocator.dupeZ__anon_16959`). `n` depends on how much code the compiler analysed before,
so it differs between Zig versions, host OSes and runs. The translator uses the name for the
Lean definition, so `renumberAnon` gives each instance a new number by first use, before
parsing:

- The functions without `__anon_` in their name come first, by name. Then the instances, in
  the order the scan finds them.
- The scan reads each function's JSON text in order. Each `<name>__anon_<n>` that it has not
  seen gets the next number of `<name>`: the first instance of `mem.Allocator.dupeZ` is
  `mem.Allocator.dupeZ__anon_1`. If it names a function of the program, that function is
  scanned after the current queue.
- A function that no scan reaches comes last, by name.

The number counts per name, so an instance of one function does not change the number of
another. After this, the same program gives the same names in every version and on every host,
if the compiler exports the same functions. The golden files of one example can come from two
compiles (a per-version file replaces a shared one), so one function can have two numbers `n`
there; with one instance per name, both still get `1`.

A type without a name (`os.linux.timespec__struct_2872`, a `__enum_`, `__union_` or `__opaque_`)
has such a number too, and the translator can use it as a Lean name; each of these markers gets
the same renumbering, after the functions (`renumberAll`).
-/

namespace Air2Lean.Anon

/-- An instance name: the name before `__anon_` (back to the last `"` in the JSON text) and the
number `n` after it. -/
abbrev Inst := String × String

/-- Each `<name><marker><n>` in `s`, in text order. -/
def anonInsts (s : String) (marker : String := "__anon_") : Array Inst := Id.run do
  let parts := s.splitOn marker
  let mut out := #[]
  for (p, prev) in (parts.drop 1).zip parts do
    let digits := p.takeWhile Char.isDigit
    let base := ((prev.splitOn "\"").getLast!)
    if !digits.isEmpty then out := out.push (base, digits.toString)
  out

/-- `s` with each `<name><marker><n>` changed to `<name><marker><map (name, n)>` (unchanged if
it has no entry). -/
def rename (map : Std.HashMap Inst Nat) (s : String) (marker : String := "__anon_") : String :=
  Id.run do
  let parts := s.splitOn marker
  let mut out := parts.head!
  for (p, prev) in (parts.drop 1).zip parts do
    let digits := (p.takeWhile Char.isDigit).toString
    let rest := (p.drop digits.length).toString
    match map[(((prev.splitOn "\"").getLast!), digits)]? with
    | some k => out := out ++ marker ++ toString k ++ rest
    | none => out := out ++ marker ++ p
  out

/-- The function name (the top-level `name`) of a JSON text; `""` if it has none. -/
def fnName (text : String) : String :=
  ((Lean.Json.parse text).toOption.bind fun j => (j.getObjValAs? String "name").toOption).getD ""

/-- Only compiler identities are renamed. Field/error names and asm/string data can contain
the same markers, but their spelling is observable (for example through `@tagName`). -/
partial def identityNames (j : Lean.Json) (root : Bool := true) (typeEntry : Bool := false) :
    Array String :=
  match j with
  | .arr vs => vs.flatMap fun v => identityNames v false typeEntry
  | .obj fields => fields.foldl (init := #[]) fun acc k v =>
    let isIdentity := k == "func" || k == "comptime_fn" ||
      (k == "name" && (root || typeEntry))
    if isIdentity then
      acc ++ (v.getStr?.toOption.toArray)
    else acc ++ identityNames v false (root && k == "types")
  | _ => #[]

partial def renameIdentities (map : Std.HashMap Inst Nat) (marker : String) (j : Lean.Json)
    (root : Bool := true) (typeEntry : Bool := false) : Lean.Json :=
  match j with
  | .arr vs => .arr (vs.map fun v => renameIdentities map marker v false typeEntry)
  | .obj fields => Lean.Json.mkObj (fields.foldl (init := []) fun acc k v =>
    let isIdentity := k == "func" || k == "comptime_fn" ||
      (k == "name" && (root || typeEntry))
    let v := if isIdentity then
        match v with
        | .str s => .str (rename map s marker)
        | v => v
      else renameIdentities map marker v false (root && k == "types")
    (k, v) :: acc)
  | j => j

/-- `texts`: the JSON text of each function. The same texts, with the numbers after `marker`
renamed. -/
def renumberParsed (texts : Array String) (parsed : Array (Option Lean.Json))
    (marker : String) : Array (Option Lean.Json) := Id.run do
  let names := parsed.map fun j => (j.bind fun j => (j.getObjValAs? String "name").toOption).getD ""
  let identities := parsed.map fun j =>
    let ns := (j.map identityNames).getD #[]
    (ns.flatMap fun n => anonInsts ("\"" ++ n) marker).foldl (fun s n => s.insert n)
      ({} : Std.HashSet Inst)
  let byInst : Std.HashMap Inst Nat := names.zipIdx.foldl (init := {}) fun m (name, i) =>
    match (anonInsts ("\"" ++ name) marker).back? with
    | some n => m.insert n i
    | none => m
  let sorted (xs : Array Nat) := xs.qsort (fun a b => names[a]! < names[b]!)
  let isInst (i : Nat) := !(anonInsts names[i]! marker).isEmpty
  let roots := sorted ((Array.range texts.size).filter (!isInst ·))
  let rest := sorted ((Array.range texts.size).filter isInst)
  let mut map : Std.HashMap Inst Nat := {}
  let mut count : Std.HashMap String Nat := {}
  let mut seen : Std.HashSet Nat := {}
  let mut queue := roots
  let mut qi := 0
  for i in roots do seen := seen.insert i
  -- A function that no scan reaches is scanned after the queue (`rest`, by name).
  for extra in #[none] ++ rest.map some do
    if let some i := extra then
      if !seen.contains i then
        seen := seen.insert i
        queue := queue.push i
    while h : qi < queue.size do
      let i := queue[qi]
      qi := qi + 1
      for n in anonInsts texts[i]! marker do
        unless identities[i]!.contains n do continue
        if !map.contains n then
          let k := count.getD n.1 0 + 1
          count := count.insert n.1 k
          map := map.insert n k
          if let some j := byInst[n]? then
            if !seen.contains j then
              seen := seen.insert j
              queue := queue.push j
  return parsed.map fun j => j.map (renameIdentities map marker ·)

def compressParsed (texts : Array String) (parsed : Array (Option Lean.Json)) : Array String :=
  (texts.zip parsed).map fun (text, j) => (j.map (·.compress)).getD text

def renumberAnon (texts : Array String) (marker : String := "__anon_") : Array String :=
  let parsed := texts.map fun text => (Lean.Json.parse text).toOption
  compressParsed texts (renumberParsed texts parsed marker)

/-- Internal pipeline result: original full names and all rewritten texts, sharing the
initial parse. Names are captured before any identity marker is renumbered. -/
def renumberAllWithNames (texts : Array String) : Array String × Array String := Id.run do
  let mut parsed := texts.map fun text => (Lean.Json.parse text).toOption
  let names := parsed.map fun j =>
    (j.bind fun j => (j.getObjValAs? String "name").toOption).getD ""
  let mut current := texts
  for marker in ["__anon_", "__struct_", "__enum_", "__union_", "__opaque_"] do
    parsed := renumberParsed current parsed marker
    current := compressParsed current parsed
  return (names, current)

/-- `renumberAnon` for the generic instances, then for each kind of type without a name. -/
def renumberAll (texts : Array String) : Array String :=
  (renumberAllWithNames texts).2

end Air2Lean.Anon
