import Lean.Data.Json
import Air2Lean.Air.StrictJson

/-! The opt-in device contract (L13, `--device-contract`, `docs/volatile-effects.md`).

A project declares one device per program: a register map of addresses, widths and directions.
With a contract, the checker admits a volatile load or store of an 8/16/32/64-bit integer
through a pointer to memory, and the emitter writes it as `Zig.vload`/`Zig.vstore` on the
generated `air2lean_device` (`ZigLean/Mem/Device.lean`). Without one, every volatile access stays
rejected (`VOLATILE_ACCESS`) and the output is unchanged. The registry supplies data only, never
Lean source: names are identifiers and numbers are bounded. -/
namespace Air2Lean
open Lean (Json)

inductive RegAccess where
  | read
  | write
  | readWrite
  deriving BEq, Repr, Inhabited

def RegAccess.name : RegAccess → String
  | .read => "read"
  | .write => "write"
  | .readWrite => "read-write"

structure DeviceRegister where
  name : String
  address : Nat
  bits : Nat
  access : RegAccess
  deriving BEq, Repr, Inhabited

/-- An `asm volatile` that is a device event (`Zig.vasm`): matched exactly by its template, its
ordered constraints (outputs, then inputs) and its clobbers. -/
structure DeviceAsm where
  template : String
  constraints : List String
  clobbers : List String
  deriving BEq, Repr, Inhabited

structure DeviceContract where
  device : String
  registers : Array DeviceRegister
  asms : Array DeviceAsm := #[]
  deriving BEq, Repr, Inhabited

/-- The declared device asm with exactly this template, constraints and clobbers. -/
def DeviceContract.asm? (c : DeviceContract) (template : String)
    (constraints clobbers : List String) : Option DeviceAsm :=
  c.asms.find? fun a => a.template == template && a.constraints == constraints &&
    a.clobbers == clobbers

/-- The generated register map's name (reserved in the output namespace). -/
def deviceDefName : String := "air2lean_device"

def DeviceContract.maxRegisters : Nat := 4096

namespace DeviceContract

private def fail {α : Type} (msg : String) : Except String α :=
  throw s!"device contract: {msg}"

private def keys (j : Json) (required : List String) (optional : List String := []) :
    Except String Unit := do
  for (k, _) in (← j.getObj?).toArray do
    unless required.contains k || optional.contains k do fail s!"unsupported field '{k}'"
  for k in required do
    if (j.getObjVal? k).toOption.isNone then fail s!"missing field '{k}'"

private def strings (j : Json) (k : String) : Except String (List String) := do
  let items ← (← (← j.getObjVal? k).getArr?).mapM Json.getStr?
  if items.size > 64 || items.any (fun s => s.isEmpty || s.length > 64) then
    fail s!"'{k}' must be at most 64 nonempty strings of at most 64 characters"
  pure items.toList

/-- A plain identifier: an ASCII letter or `_`, then ASCII letters, digits or `_`. -/
private def identifier (s : String) : Bool :=
  s.length ≤ 64 &&
  (s.toList.head?.map fun c => (c.isAlpha && c.toNat < 128) || c == '_').getD false &&
    s.toList.all fun c => (c.isAlphanum && c.toNat < 128) || c == '_'

def parse (contents : String) : Except String DeviceContract := do
  let j ← StrictJson.parse contents 8
  keys j ["schema", "device", "registers"] ["asm"]
  unless (← (← j.getObjVal? "schema").getNat?) == 1 do fail "unsupported schema (want 1)"
  let device ← (← j.getObjVal? "device").getStr?
  unless identifier device do fail s!"device name '{device}' is not an identifier"
  let regs ← (← j.getObjVal? "registers").getArr?
  let asmJson ← match j.getObjVal? "asm" with
    | .ok a => a.getArr?
    | .error _ => pure #[]
  if regs.isEmpty && asmJson.isEmpty then fail "no registers and no asm"
  if regs.size > maxRegisters then fail s!"more than {maxRegisters} registers"
  let registers ← regs.mapM fun r => do
    keys r ["name", "address", "bits", "access"]
    let name ← (← r.getObjVal? "name").getStr?
    unless identifier name do fail s!"register name '{name}' is not an identifier"
    let address ← (← r.getObjVal? "address").getNat?
    let bits ← (← r.getObjVal? "bits").getNat?
    unless [8, 16, 32, 64].contains bits do fail s!"register '{name}': bits must be 8, 16, 32 or 64"
    if address == 0 then fail s!"register '{name}': address 0 is the null pointer"
    if address + bits / 8 > 2 ^ 64 then fail s!"register '{name}': address is outside the 64-bit space"
    unless address % (bits / 8) == 0 do fail s!"register '{name}': address is not {bits / 8}-byte aligned"
    let access ← match ← (← r.getObjVal? "access").getStr? with
      | "read" => pure RegAccess.read
      | "write" => pure .write
      | "read-write" => pure .readWrite
      | other => fail s!"register '{name}': access '{other}' (want read, write or read-write)"
    pure { name, address, bits, access : DeviceRegister }
  for (a, i) in registers.zipIdx do
    for b in registers.extract (i + 1) registers.size do
      if a.name == b.name then fail s!"duplicate register name '{a.name}'"
      if a.address < b.address + b.bits / 8 && b.address < a.address + a.bits / 8 then
        fail s!"registers '{a.name}' and '{b.name}' overlap"
  let asms ← asmJson.mapM fun a => do
    keys a ["template", "constraints", "clobbers"]
    let template ← (← a.getObjVal? "template").getStr?
    if template.isEmpty || template.length > 4096 then
      fail "an asm template must have 1 to 4096 characters"
    let constraints ← strings a "constraints"
    let clobbers ← strings a "clobbers"
    -- DEV-01: the device neither reads nor writes model memory.
    if clobbers.contains "memory" then
      fail s!"asm '{template}': a 'memory' clobber is outside the device contract (DEV-01)"
    pure { template, constraints, clobbers : DeviceAsm }
  for (a, i) in asms.zipIdx do
    for b in asms.extract (i + 1) asms.size do
      if a.template == b.template then fail s!"duplicate asm template '{a.template}'"
  pure { device, registers, asms }

/-- The contract as recorded in the generated header and the source map. -/
def report (c : DeviceContract) : Json :=
  let registers : Json := .arr <| c.registers.map fun r => Json.mkObj [("name", .str r.name),
    ("address", Lean.toJson r.address), ("bits", Lean.toJson r.bits),
    ("access", .str r.access.name)]
  let asms : Json := .arr <| c.asms.map fun a => Json.mkObj [("template", .str a.template),
    ("constraints", Lean.toJson a.constraints), ("clobbers", Lean.toJson a.clobbers)]
  Json.mkObj <| [("schema", Lean.toJson (1 : Nat)), ("device", .str c.device),
    ("semantics", .str "trace-oracle-v1"), ("registers", registers)] ++
    -- Absent without asm entries, so a register-only contract keeps its recorded header.
    (if c.asms.isEmpty then [] else [("asm", asms)])

/-- The generated register map (`Zig.Device`). -/
def emitDef (c : DeviceContract) : String :=
  let access : RegAccess → String
    | .read => ".read" | .write => ".write" | .readWrite => ".readWrite"
  let asmsField := if c.asms.isEmpty then ""
    else s!", asms := [{", ".intercalate (c.asms.toList.map (·.template.quote))}]"
  let regs := c.registers.toList.map fun r =>
    s!"  \{ name := \"{r.name}\", addr := {r.address}, bits := {r.bits}, access := {access r.access} }"
  let regsField := if regs.isEmpty then "[]" else s!"[\n{",\n".intercalate regs}]"
  let asmDoc := if c.asms.isEmpty then "" else ", and every declared `asm volatile` is `Zig.vasm`"
  s!"/-- The declared device `{c.device}` (`--device-contract`, docs/volatile-effects.md, premise \
    DEV-01): every volatile access is `Zig.vload`/`Zig.vstore` on this register map{asmDoc}. -/\n\
    def {deviceDefName} : Zig.Device := \{ name := \"{c.device}\", regs := {regsField}{asmsField} }"

end DeviceContract
end Air2Lean
