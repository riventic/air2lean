import ZigLean.Sep.Full.AutoAll

/-!
# Device accesses by the library's rules (`ZigLean/Sep/Full/Device.lean`)

Handwritten programs in the shapes the translator emits under `--device-contract`, for **every**
declared device `d`, register and device state `D`: a statement names the register by the
contract's facts (`devAddr?`, `Device.readable`/`writable`, the declared template) and the
oracle's answers it relies on (premise DEV-01), and `fsym` walks the code with the device rules.
The generated UART driver and `rdtsc` client (`tests/roadmap/volatile-effects`) are instances.

* `twice_spec`: two reads are two events, and the second answer is the oracle's after the first.
* `write_read_spec`: the program order of a write and a read, through a pointer derived inside
  the register window.
* `asm_twice_spec`, `asm_effect_spec`: declared `asm volatile`, with and without an output.
* `framed_spec`: other resources stay (the rules are framed), also in a partial triple.
* `start_run`: the run from program start with a device state (`FTotalTriple.run_init_dev`).
* `trace_shape`: a stored word known by its value; the two forms that do not walk yet (engine
  ledger `trace-eq-up-to-arith`) as expected failures.
* Rejected: no `devOwn`, an answer that no premise names, an undeclared direction, a read
  dropped from the trace, two reads merged into one.
-/

namespace SepAuto.Device
open Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto

variable {d : Zig.Device} {bits align addr : Nat} {p : Ptr} {D : DevState}

def twice (d : Zig.Device) (bits align : Nat) (p : Ptr) : MemM (BitVec bits × BitVec bits) := do
  let a ← Zig.vload d bits align p
  let b ← Zig.vload d bits align p
  pure (a, b)

theorem twice_spec {a b : BitVec bits} (hp : devAddr? p = some addr) (hal : addr % align = 0)
    (hr : d.readable addr bits = true) (ha : D.oracle D.trace addr bits = some a)
    (hb : D.oracle (D.trace ++ [.read addr bits a.toNat]) addr bits = some b) :
    FTotalTriple (devOwn D) (twice d bits align p)
      (fun r => ⟪r = (a, b)⟫ ⋆
        devOwn { D with trace := D.trace ++ [.read addr bits a.toNat, .read addr bits b.toNat] }) := by
  unfold twice
  fsym

/-- `reg.data = v; return reg.status;` with `&reg.data` derived from the block's pointer. -/
def writeRead (d : Zig.Device) (bits align : Nat) (p : Ptr) (k : Int) (v : BitVec bits) :
    MemM (BitVec bits) := do
  let q ← Zig.ptrProjectDevice d p (·.add k)
  Zig.vstore d bits align q v
  Zig.vload d bits align p

theorem write_read_spec {k : Int} {waddr : Nat} {v r : BitVec bits}
    (hp : devAddr? p = some addr) (hq : devAddr? (p.add k) = some waddr)
    (hin : d.inWindow addr = true) (hwin : d.inWindow waddr = true)
    (hal : addr % align = 0) (hwal : waddr % align = 0)
    (hr : d.readable addr bits = true) (hw : d.writable waddr bits = true)
    (ho : D.oracle (D.trace ++ [.write waddr bits v.toNat]) addr bits = some r) :
    FTotalTriple (devOwn D) (writeRead d bits align p k v)
      (fun x => ⟪x = r⟫ ⋆
        devOwn { D with trace := D.trace ++ [.write waddr bits v.toNat, .read addr bits r.toNat] }) := by
  unfold writeRead
  fsym

def asmTwice (d : Zig.Device) (t : String) (ins : List Nat) (bits : Nat) : MemM (BitVec bits) := do
  let a ← Zig.vasm d t ins bits
  let b ← Zig.vasm d t ins bits
  pure (b - a)

theorem asm_twice_spec {t : String} {ins : List Nat} {a b : BitVec bits}
    (hd : d.asms.contains t = true) (ha : D.asmOracle D.trace t ins bits = some a)
    (hb : D.asmOracle (D.trace ++ [.asm t ins bits a.toNat]) t ins bits = some b) :
    FTotalTriple (devOwn D) (asmTwice d t ins bits)
      (fun r => ⟪r = b - a⟫ ⋆
        devOwn { D with trace := D.trace ++ [.asm t ins bits a.toNat, .asm t ins bits b.toNat] }) := by
  unfold asmTwice
  fsym

def asmEffect (d : Zig.Device) (t : String) (ins : List Nat) : MemM Unit := do
  Zig.vasmEffect d t ins
  Zig.vasmEffect d t ins

theorem asm_effect_spec {t : String} {ins : List Nat} (hd : d.asms.contains t = true) :
    FTotalTriple (devOwn D) (asmEffect d t ins)
      (fun _ => devOwn { D with trace := D.trace ++ [.asm t ins 0 0, .asm t ins 0 0] }) := by
  unfold asmEffect
  fsym

/-- The rules are framed, and a partial triple takes them too. -/
theorem framed_spec (R : FAssn) {a : BitVec bits} (hp : devAddr? p = some addr)
    (hal : addr % align = 0) (hr : d.readable addr bits = true)
    (ha : D.oracle D.trace addr bits = some a) :
    FTriple (R ⋆ devOwn D) (Zig.vload d bits align p)
      (fun r => ⟪r = a⟫ ⋆ devOwn { D with trace := D.trace ++ [.read addr bits a.toNat] } ⋆ R) := by
  fsym

/-- **From program start**: the start memory with the device state `D` gives `devOwn D`, and the
final device state is read off the postcondition. -/
theorem start_run (σ : Placement) {a b : BitVec bits} (hp : devAddr? p = some addr)
    (hal : addr % align = 0) (hr : d.readable addr bits = true)
    (ha : D.oracle D.trace addr bits = some a)
    (hb : D.oracle (D.trace ++ [.read addr bits a.toNat]) addr bits = some b) :
    ∃ m', (twice d bits align p).run { Mem.ofGlobals σ [] with dev := D } = pure ((a, b), m') ∧
      m'.dev.trace = D.trace ++ [.read addr bits a.toNat, .read addr bits b.toNat] := by
  obtain ⟨v, m', r', hrun, hh, hq, -⟩ := FTotalTriple.run_init_dev σ [] (by decide) (by simp) D
    ((twice_spec hp hal hr ha hb).frame (R := globals []))
  obtain ⟨rfl, hd⟩ := sep_lift.mp (sep_assoc hq)
  exact ⟨m', hrun, by rw [hh.dev hd]⟩

/-! ## A stored word known by its value (engine ledger `trace-eq-up-to-arith`)

A widened byte is an opaque word `w` with the fact `w.toNat = c.toNat`, so the write's event is
equal to the statement's only up to arithmetic. The walk matches it when the statement's trace
has the state's shape and its events are written out; the other forms are the row's goals. -/

def storeByte (d : Zig.Device) (align : Nat) (p : Ptr) (c : BitVec 8) : MemM (BitVec 32) := do
  let w ← (Zig.intCast false false 32 c (safe := false) : Result (BitVec 32))
  Zig.vstore d 32 align p w
  Zig.vload d 32 align p

/-- A write event of a byte, as an abbreviation. -/
abbrev wr (addr : Nat) (c : BitVec 8) : DevEvent := .write addr 32 c.toNat

theorem trace_shape {c : BitVec 8} {v : BitVec 32} (hp : devAddr? p = some addr)
    (hal : addr % align = 0) (hr : d.readable addr 32 = true) (hw : d.writable addr 32 = true)
    (ho : D.oracle (D.trace ++ [.write addr 32 c.toNat]) addr 32 = some v) :
    FTotalTriple (devOwn D) (storeByte d align p c)
      (fun x => ⟪x = v⟫ ⋆
        devOwn { D with trace := D.trace ++ [.write addr 32 c.toNat] ++ [.read addr 32 v.toNat] }) := by
  unfold storeByte
  fsym

set_option linter.unusedVariables false in
/-- Open (1): the same trace as one list literal after `D.trace`. -/
example {c : BitVec 8} {v : BitVec 32} (hp : devAddr? p = some addr)
    (hal : addr % align = 0) (hr : d.readable addr 32 = true) (hw : d.writable addr 32 = true)
    (ho : D.oracle (D.trace ++ [.write addr 32 c.toNat]) addr 32 = some v) : True := by
  fail_if_success
    have : FTotalTriple (devOwn D) (storeByte d align p c)
        (fun x => ⟪x = v⟫ ⋆
          devOwn { D with trace := D.trace ++ [.write addr 32 c.toNat, .read addr 32 v.toNat] }) := by
      unfold storeByte
      fsym
  trivial

set_option linter.unusedVariables false in
/-- Open (2): the oracle's answer named through the abbreviation `wr`. -/
example {c : BitVec 8} {v : BitVec 32} (hp : devAddr? p = some addr)
    (hal : addr % align = 0) (hr : d.readable addr 32 = true) (hw : d.writable addr 32 = true)
    (ho : D.oracle (D.trace ++ [wr addr c]) addr 32 = some v) : True := by
  fail_if_success
    have : FTotalTriple (devOwn D) (storeByte d align p c)
        (fun x => ⟪x = v⟫ ⋆
          devOwn { D with trace := D.trace ++ [.write addr 32 c.toNat] ++ [.read addr 32 v.toNat] }) := by
      unfold storeByte
      fsym
  trivial

/-! ## Rejected attempts -/

set_option linter.unusedVariables false

/-- No `devOwn`: no rule applies (and no triple exists, `tests/roadmap/sep-full/DeviceCX.lean`). -/
example (R : FAssn) {a : BitVec bits} (hp : devAddr? p = some addr) (hal : addr % align = 0)
    (hr : d.readable addr bits = true) : True := by
  fail_if_success
    have : FTotalTriple R (Zig.vload d bits align p) (fun _ => R) := by
      fsym
  trivial

/-- An answer that no premise names: the read has no rule. -/
example (hp : devAddr? p = some addr) (hal : addr % align = 0)
    (hr : d.readable addr bits = true) : True := by
  fail_if_success
    have : FTotalTriple (devOwn D) (Zig.vload d bits align p) (fun _ => FAssn.ex fun D' => devOwn D') := by
      fsym
  trivial

/-- The second read's answer is the oracle's after the first event, not before it. -/
example {a b : BitVec bits} (hp : devAddr? p = some addr) (hal : addr % align = 0)
    (hr : d.readable addr bits = true) (ha : D.oracle D.trace addr bits = some a)
    (hb : D.oracle D.trace addr bits = some b) : True := by
  fail_if_success
    have : FTotalTriple (devOwn D) (twice d bits align p)
        (fun r => FAssn.ex fun D' => devOwn D') := by
      unfold twice
      fsym
  trivial

/-- A register declared write-only is not read. -/
example {a : BitVec bits} (hp : devAddr? p = some addr) (hal : addr % align = 0)
    (hw : d.writable addr bits = true) (ha : D.oracle D.trace addr bits = some a) : True := by
  fail_if_success
    have : FTotalTriple (devOwn D) (Zig.vload d bits align p) (fun _ => FAssn.ex fun D' => devOwn D') := by
      fsym
  trivial

/-- A read is an event: the trace without it is rejected. -/
example {a : BitVec bits} (hp : devAddr? p = some addr) (hal : addr % align = 0)
    (hr : d.readable addr bits = true) (ha : D.oracle D.trace addr bits = some a) : True := by
  fail_if_success
    have : FTotalTriple (devOwn D) (Zig.vload d bits align p) (fun _ => devOwn D) := by
      fsym
  trivial

/-- Two reads are never one: a trace with one event is rejected. -/
example {a b : BitVec bits} (hp : devAddr? p = some addr) (hal : addr % align = 0)
    (hr : d.readable addr bits = true) (ha : D.oracle D.trace addr bits = some a)
    (hb : D.oracle (D.trace ++ [.read addr bits a.toNat]) addr bits = some b) : True := by
  fail_if_success
    have : FTotalTriple (devOwn D) (twice d bits align p)
        (fun r => devOwn { D with trace := D.trace ++ [.read addr bits a.toNat] }) := by
      unfold twice
      fsym
  trivial

end SepAuto.Device
