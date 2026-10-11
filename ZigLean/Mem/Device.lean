import ZigLean.Mem.Basic

/-!
# Device effects (L13)

The opt-in semantics of volatile accesses (`air2lean --device-contract`,
`docs/volatile-effects.md`). A program declares one device: a register map of addresses,
widths and directions (`Device`, emitted as `air2lean_device`). Each volatile load or store of
an integer through a pointer to memory becomes `vload`/`vstore`:

* the pointer must be a device address: a pointer without a block (`ptrFromAddr` of an address
  that no model block covers); a volatile access to a model block, or to an address, width or
  direction that the register map does not declare, has no modelled meaning and throws
  `.unspecified`;
* a misaligned address throws `.illegal`, as for every access;
* a read asks the environment's oracle (`Mem.dev.oracle`) for the value, given the whole trace
  so far, and appends a `read` event; a write appends a `write` event. Neither touches a model
  block, the footprint or the race state.

A declared `asm volatile` (`vasm`, `vasmEffect`) is an `asm` event in the same trace, with its
outputs from `Mem.dev.asmOracle`; it shares the program order with `vload`/`vstore`.

So a device read is never a repeatable memory read: two reads are two events, and the oracle
may answer them differently. `Mem.dev.trace` lists every executed device access exactly once,
in program order. Ordinary memory accesses are not events: under the device contract (premise
DEV-01) the device neither observes nor changes model memory, so their order relative to device
events is not observable.
-/

namespace Zig

/-- What a program may do with a register. -/
inductive RegAccess where
  | read
  | write
  | readWrite
  deriving DecidableEq, Repr, Inhabited

def RegAccess.canRead : RegAccess → Bool
  | .write => false
  | _ => true

def RegAccess.canWrite : RegAccess → Bool
  | .read => false
  | _ => true

/-- One device register: `bits` wide (8, 16, 32 or 64) at address `addr`. -/
structure DevReg where
  name : String
  addr : Nat
  bits : Nat
  access : RegAccess
  deriving DecidableEq, Repr, Inhabited

/-- A program's declared device: its register map, and the templates of the `asm volatile`
that are device events (`vasm`). -/
structure Device where
  name : String
  regs : List DevReg
  asms : List String := []
  deriving DecidableEq, Repr, Inhabited

/-- A volatile read of `bits` bits at `addr` is declared. -/
def Device.readable (d : Device) (addr bits : Nat) : Bool :=
  d.regs.any fun r => r.addr == addr && r.bits == bits && r.access.canRead

/-- A volatile write of `bits` bits at `addr` is declared. -/
def Device.writable (d : Device) (addr bits : Nat) : Bool :=
  d.regs.any fun r => r.addr == addr && r.bits == bits && r.access.canWrite

/-- The device address of `p`: only a pointer without a block has one. -/
def devAddr? (p : Ptr) : Option Nat :=
  match p.block with
  | none => if 0 ≤ p.off then some p.off.toNat else none
  | some _ => none

/-- The declared register window of `d`: from its lowest register address to one past the end
of its highest register (`bits / 8` bytes each). -/
def Device.window (d : Device) : Nat × Nat :=
  match d.regs with
  | [] => (0, 0)
  | r :: rs => rs.foldl (fun (lo, hi) r => (Nat.min lo r.addr, Nat.max hi (r.addr + r.bits / 8)))
      (r.addr, r.addr + r.bits / 8)

/-- `addr` lies in `d`'s register window (one past its end included). -/
def Device.inWindow (d : Device) (addr : Nat) : Bool :=
  let (lo, hi) := d.window
  !d.regs.isEmpty && decide (lo ≤ addr) && decide (addr ≤ hi)

/-- A derived pointer of a device pointer (L13, `--device-contract`): a field or element of the
register block, such as `&uart.data`. The device's declared register window is the allocation
`getelementptr inbounds` needs, which lies outside the model (DEV-01): an offset of a block-less
pointer in the window that stays in the window is formed. Any other projection is MM-3's
`ptrProject`, so an offset of an undeclared `@ptrFromInt` address stays `.illegal`. -/
def ptrProjectDevice (d : Device) (p : Ptr) (project : Ptr → Ptr) : MemM Ptr := fun m =>
  let q := project p
  match devAddr? p, devAddr? q with
  | some a, some b => if d.inWindow a && d.inWindow b then pure (q, m) else ptrProject p project m
  | _, _ => ptrProject p project m

/-- The memory after one more event. -/
def Mem.withEvent (m : Mem) (e : DevEvent) : Mem :=
  { m with dev := { m.dev with trace := m.dev.trace ++ [e] } }

/-- A volatile load of a `bits`-bit integer through `p` (alignment `align`): one `read` event
with the oracle's answer. -/
def vload (d : Device) (bits align : Nat) (p : Ptr) : MemM (BitVec bits) := fun m =>
  match devAddr? p with
  | none => throw .unspecified
  | some addr =>
    if addr % align ≠ 0 then throw .illegal
    else if d.readable addr bits then
      match m.dev.oracle m.dev.trace addr bits with
      | none => throw .unspecified
      | some v => pure (v, m.withEvent (.read addr bits v.toNat))
    else throw .unspecified

/-- A volatile store of the `bits`-bit integer `v` through `p`: one `write` event. -/
def vstore (d : Device) (bits align : Nat) (p : Ptr) (v : BitVec bits) : MemM Unit := fun m =>
  match devAddr? p with
  | none => throw .unspecified
  | some addr =>
    if addr % align ≠ 0 then throw .illegal
    else if d.writable addr bits then pure ((), m.withEvent (.write addr bits v.toNat))
    else throw .unspecified

/-- A declared `asm volatile` with the template `t`, the register inputs `ins` and one
`bits`-bit output: one `asm` event with the asm oracle's answer. -/
def vasm (d : Device) (t : String) (ins : List Nat) (bits : Nat) : MemM (BitVec bits) := fun m =>
  if d.asms.contains t then
    match m.dev.asmOracle m.dev.trace t ins bits with
    | none => throw .unspecified
    | some v => pure (v, m.withEvent (.asm t ins bits v.toNat))
  else throw .unspecified

/-- A declared `asm volatile` without an output: one `asm` event. -/
def vasmEffect (d : Device) (t : String) (ins : List Nat) : MemM Unit := fun m =>
  if d.asms.contains t then pure ((), m.withEvent (.asm t ins 0 0)) else throw .unspecified

/-! ## Run equations -/

theorem ptrProjectDevice_run {d : Device} {p : Ptr} {project : Ptr → Ptr} {m : Mem} {a b : Nat}
    (hp : devAddr? p = some a) (hq : devAddr? (project p) = some b) (ha : d.inWindow a = true)
    (hb : d.inWindow b = true) :
    (ptrProjectDevice d p project).run m = pure (project p, m) := by
  simp [ptrProjectDevice, StateT.run, hp, hq, ha, hb]

theorem vload_run {d : Device} {bits align addr : Nat} {p : Ptr} {m : Mem} {v : BitVec bits}
    (hp : devAddr? p = some addr) (hal : addr % align = 0) (hr : d.readable addr bits = true)
    (ho : m.dev.oracle m.dev.trace addr bits = some v) :
    (vload d bits align p).run m = pure (v, m.withEvent (.read addr bits v.toNat)) := by
  simp [vload, StateT.run, hp, hal, hr, ho]

theorem vstore_run {d : Device} {bits align addr : Nat} {p : Ptr} {m : Mem} {v : BitVec bits}
    (hp : devAddr? p = some addr) (hal : addr % align = 0) (hw : d.writable addr bits = true) :
    (vstore d bits align p v).run m = pure ((), m.withEvent (.write addr bits v.toNat)) := by
  simp [vstore, StateT.run, hp, hal, hw]

theorem vasm_run {d : Device} {t : String} {ins : List Nat} {bits : Nat} {m : Mem}
    {v : BitVec bits} (hd : d.asms.contains t = true)
    (ho : m.dev.asmOracle m.dev.trace t ins bits = some v) :
    (vasm d t ins bits).run m = pure (v, m.withEvent (.asm t ins bits v.toNat)) := by
  have hm : t ∈ d.asms := by simpa using hd
  simp [vasm, StateT.run, hm, ho]

theorem vasmEffect_run {d : Device} {t : String} {ins : List Nat} {m : Mem}
    (hd : d.asms.contains t = true) :
    (vasmEffect d t ins).run m = pure ((), m.withEvent (.asm t ins 0 0)) := by
  have hm : t ∈ d.asms := by simpa using hd
  simp [vasmEffect, StateT.run, hm]

/-- A block-less pointer with a nonnegative offset is a device address. -/
theorem devAddr?_none (a : Nat) : devAddr? ⟨none, (a : Int)⟩ = some a := by
  simp [devAddr?]

theorem withEvent_trace (m : Mem) (e : DevEvent) :
    (m.withEvent e).dev.trace = m.dev.trace ++ [e] := rfl

theorem withEvent_oracle (m : Mem) (e : DevEvent) :
    (m.withEvent e).dev.oracle = m.dev.oracle := rfl

theorem withEvent_asmOracle (m : Mem) (e : DevEvent) :
    (m.withEvent e).dev.asmOracle = m.dev.asmOracle := rfl

/-- A device read through a pointer into a model block has no modelled meaning. -/
theorem vload_block (d : Device) (bits align : Nat) (b : BlockId) (off : Int) (m : Mem) :
    (vload d bits align ⟨some b, off⟩).run m = throw .unspecified := rfl

end Zig
