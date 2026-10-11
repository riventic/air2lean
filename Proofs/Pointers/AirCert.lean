-- air2lean AIR semantics certificate (docs/air-semantics.md). Generated; do not edit.
import Air2Lean.Sem
import Proofs.Pointers.Gen

set_option linter.unusedSimpArgs false

namespace Pointers.AirCert

open Air2Lean Air2Lean.Sem

/-! Certified: `pointers.addTo`, `pointers.delay`, `pointers.dueOf`, `pointers.same`, `pointers.sumTo`, `pointers.swap`

Outside the certificate fragment:

* `pointers.addDown`: a recursive function that uses memory (stack budget `Zig.enterFrame`, STK-01)
* `pointers.bumpOpt`: inst 2: an instruction outside the fragment
* `pointers.copyJob`: inst 2: a load of a type outside the fragment
* `pointers.maxPtr`: a parameter that is not an integer, bool, plain pointer or slice
* `pointers.setOpt`: a parameter that is not an integer, bool, plain pointer or slice
* `pointers.setOptJob`: inst 2: an instruction outside the fragment
-/

/-- The decoded canonical AIR of `pointers.addTo`. -/
def air_addTo : Func :=
{ zigVersion := "0.15.2", name := "pointers.addTo",
  params := #[0, 1], ret := 2,
  types := #[(.ptr "one" false 3), (.int false 32), .void, (.int false 64), .noreturn],
  layouts := #[{ size := (some 8), align := (some 8), offsets := #[], ptrAlign := (some 8), sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 4), align := (some 4), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 0), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 8), align := (some 8), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := none, align := none, offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }],
  globals := #[],
  errorSetBits := 16,
  body := #[⟨0, 0, (.arg 0)⟩,
    ⟨1, 1, (.arg 1)⟩,
    ⟨7, 2, (.line 2)⟩,
    ⟨2, 3, (.load (.inst 0))⟩,
    ⟨3, 3, (.intCast (.inst 1))⟩,
    ⟨8, 2, (.line 2)⟩,
    ⟨4, 3, (.arith .add .checked (.inst 2) (.inst 3))⟩,
    ⟨5, 2, (.store (.inst 0) (.inst 4))⟩,
    ⟨6, 4, (.ret .void)⟩] }

/-- The decoded canonical AIR of `pointers.delay`. -/
def air_delay : Func :=
{ zigVersion := "0.15.2", name := "pointers.delay",
  params := #[0, 1], ret := 2,
  types := #[(.ptr "one" false 7), (.int false 32), .void, (.ptr "one" false 0), (.ptr "one" true 0), (.ptr "one" false 1), .noreturn, (.struct "pointers.Job" "auto" #[("duration", 1), ("due", 1), ("weight", 8)]), (.int false 8)],
  layouts := #[{ size := (some 8), align := (some 8), offsets := #[], ptrAlign := (some 4), sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 4), align := (some 4), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 0), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 8), align := (some 8), offsets := #[], ptrAlign := (some 8), sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 8), align := (some 8), offsets := #[], ptrAlign := (some 8), sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 8), align := (some 8), offsets := #[], ptrAlign := (some 4), sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := none, align := none, offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 12), align := (some 4), offsets := #[0, 4, 8], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 1), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }],
  globals := #[],
  errorSetBits := 16,
  body := #[⟨0, 0, (.arg 0)⟩,
    ⟨1, 1, (.arg 1)⟩,
    ⟨7, 2, (.line 2)⟩,
    ⟨2, 5, (.fieldPtr (.inst 0) 0)⟩,
    ⟨3, 1, (.load (.inst 2))⟩,
    ⟨8, 2, (.line 2)⟩,
    ⟨4, 1, (.arith .add .checked (.inst 3) (.inst 1))⟩,
    ⟨5, 2, (.store (.inst 2) (.inst 4))⟩,
    ⟨6, 6, (.ret .void)⟩] }

/-- The decoded canonical AIR of `pointers.dueOf`. -/
def air_dueOf : Func :=
{ zigVersion := "0.15.2", name := "pointers.dueOf",
  params := #[0], ret := 1,
  types := #[(.ptr "one" false 6), (.ptr "one" false 7), (.ptr "one" false 0), .void, (.ptr "one" true 0), .noreturn, (.struct "pointers.Job" "auto" #[("duration", 7), ("due", 7), ("weight", 8)]), (.int false 32), (.int false 8)],
  layouts := #[{ size := (some 8), align := (some 8), offsets := #[], ptrAlign := (some 4), sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 8), align := (some 8), offsets := #[], ptrAlign := (some 4), sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 8), align := (some 8), offsets := #[], ptrAlign := (some 8), sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 0), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 8), align := (some 8), offsets := #[], ptrAlign := (some 8), sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := none, align := none, offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 12), align := (some 4), offsets := #[0, 4, 8], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 4), align := (some 4), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 1), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }],
  globals := #[],
  errorSetBits := 16,
  body := #[⟨0, 0, (.arg 0)⟩,
    ⟨3, 3, (.line 2)⟩,
    ⟨1, 1, (.fieldPtr (.inst 0) 1)⟩,
    ⟨4, 3, (.line 2)⟩,
    ⟨2, 5, (.ret (.inst 1))⟩] }

/-- The decoded canonical AIR of `pointers.same`. -/
def air_same : Func :=
{ zigVersion := "0.15.2", name := "pointers.same",
  params := #[0, 0], ret := 1,
  types := #[(.ptr "one" true 4), .bool, .void, .noreturn, (.int false 32)],
  layouts := #[{ size := (some 8), align := (some 8), offsets := #[], ptrAlign := (some 4), sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 1), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 0), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := none, align := none, offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 4), align := (some 4), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }],
  globals := #[],
  errorSetBits := 16,
  body := #[⟨0, 0, (.arg 0)⟩,
    ⟨1, 0, (.arg 1)⟩,
    ⟨4, 2, (.line 2)⟩,
    ⟨2, 1, (.cmp .eq (.inst 0) (.inst 1))⟩,
    ⟨5, 2, (.line 2)⟩,
    ⟨3, 3, (.ret (.inst 2))⟩] }

/-- The decoded canonical AIR of `pointers.sumTo`. -/
def air_sumTo : Func :=
{ zigVersion := "0.15.2", name := "pointers.sumTo",
  params := #[0], ret := 1,
  types := #[(.int false 32), (.int false 64), .void, (.ptr "one" false 1), (.ptr "one" false 0), .noreturn, .bool, (.other "fn (*u64, u32) void")],
  layouts := #[{ size := (some 4), align := (some 4), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 8), align := (some 8), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 0), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 8), align := (some 8), offsets := #[], ptrAlign := (some 8), sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 8), align := (some 8), offsets := #[], ptrAlign := (some 4), sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := none, align := none, offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 1), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := none, align := none, offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }],
  globals := #[],
  errorSetBits := 16,
  body := #[⟨0, 0, (.arg 0)⟩,
    ⟨21, 2, (.line 2)⟩,
    ⟨1, 3, .alloc⟩,
    ⟨2, 2, (.store (.inst 1) (.int 1 (0 : Int)))⟩,
    ⟨22, 2, (.dbg (some "acc") (some (.inst 1)))⟩,
    ⟨23, 2, (.line 3)⟩,
    ⟨3, 4, .alloc⟩,
    ⟨4, 2, (.store (.inst 3) (.int 0 (0 : Int)))⟩,
    ⟨24, 2, (.dbg (some "i") (some (.inst 3)))⟩,
    ⟨5, 2, (.block #[⟨6, 5, (.loop #[⟨7, 2, (.block #[⟨25, 2, (.line 4)⟩,
    ⟨8, 0, (.load (.inst 3))⟩,
    ⟨9, 6, (.cmp .lt (.inst 8) (.inst 0))⟩,
    ⟨10, 5, (.condBr (.inst 9) #[⟨26, 2, (.line 4)⟩,
    ⟨11, 0, (.load (.inst 3))⟩,
    ⟨27, 2, (.line 4)⟩,
    ⟨12, 2, (.call (.func "pointers.addTo" false none) #[(.inst 1), (.inst 11)])⟩,
    ⟨28, 2, (.line 4)⟩,
    ⟨29, 2, (.dbg none none)⟩,
    ⟨30, 2, (.line 4)⟩,
    ⟨13, 0, (.load (.inst 3))⟩,
    ⟨31, 2, (.line 4)⟩,
    ⟨14, 0, (.arith .add .checked (.inst 13) (.int 0 (1 : Int)))⟩,
    ⟨15, 2, (.store (.inst 3) (.inst 14))⟩,
    ⟨16, 5, (.br 7 .void)⟩] #[⟨17, 5, (.br 5 .void)⟩])⟩])⟩,
    ⟨18, 5, (.repeat 6)⟩])⟩])⟩,
    ⟨32, 2, (.line 5)⟩,
    ⟨19, 1, (.load (.inst 1))⟩,
    ⟨33, 2, (.line 5)⟩,
    ⟨20, 5, (.ret (.inst 19))⟩] }

/-- The decoded canonical AIR of `pointers.swap`. -/
def air_swap : Func :=
{ zigVersion := "0.15.2", name := "pointers.swap",
  params := #[0, 0], ret := 1,
  types := #[(.ptr "one" false 2), .void, (.int false 32), .noreturn],
  layouts := #[{ size := (some 8), align := (some 8), offsets := #[], ptrAlign := (some 4), sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 0), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 4), align := (some 4), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := none, align := none, offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }],
  globals := #[],
  errorSetBits := 16,
  body := #[⟨0, 0, (.arg 0)⟩,
    ⟨1, 0, (.arg 1)⟩,
    ⟨7, 1, (.line 2)⟩,
    ⟨2, 2, (.load (.inst 0))⟩,
    ⟨8, 1, (.dbg (some "t") (some (.inst 2)))⟩,
    ⟨9, 1, (.line 3)⟩,
    ⟨3, 2, (.load (.inst 1))⟩,
    ⟨4, 1, (.store (.inst 0) (.inst 3))⟩,
    ⟨10, 1, (.line 4)⟩,
    ⟨5, 1, (.store (.inst 1) (.inst 2))⟩,
    ⟨6, 3, (.ret .void)⟩] }

/-- The certified functions, by fully qualified name. -/
def table : Table := [
  ("pointers.addTo", air_addTo),
  ("pointers.delay", air_delay),
  ("pointers.dueOf", air_dueOf),
  ("pointers.same", air_same),
  ("pointers.sumTo", air_sumTo),
  ("pointers.swap", air_swap)]

/-- The generated definitions as a call oracle (arguments decoded by type). -/
def gen : Oracle
  | "pointers.addTo", args =>
    (fun _ => Value.void) <$> Pointers.addTo ((args.getD 0 .void).toPtr) ((args.getD 1 .void).toBV 32)
  | "pointers.delay", args =>
    (fun _ => Value.void) <$> Pointers.delay ((args.getD 0 .void).toPtr) ((args.getD 1 .void).toBV 32)
  | "pointers.dueOf", args =>
    (fun v => (Value.ptr v)) <$> Pointers.dueOf ((args.getD 0 .void).toPtr)
  | "pointers.same", args =>
    (fun v => (Value.bool v)) <$> Pointers.same ((args.getD 0 .void).toPtr) ((args.getD 1 .void).toPtr)
  | "pointers.sumTo", args =>
    (fun v => (Value.int false 64 v)) <$> Pointers.sumTo ((args.getD 0 .void).toBV 32)
  | "pointers.swap", args =>
    (fun _ => Value.void) <$> Pointers.swap ((args.getD 0 .void).toPtr) ((args.getD 1 .void).toPtr)
  | _, _ => StateT.lift stuck

theorem callee_0 : panicOf? "pointers.addTo" = none := rfl

/-- `pointers.addTo`: the AIR semantics of the decoded function (under any call oracle) equals the generated definition. -/
theorem addTo_step (call : Oracle) (p0 : Zig.Ptr) (p1 : BitVec 32) (m : Zig.Mem) :
    (execFunc call air_addTo [(Value.ptr p0), (Value.int false 32 p1)]).run m =
      (fun r => (Value.void, r.2)) <$> (Pointers.addTo p0 p1).run m := by
  conv => rhs; rw [Pointers.addTo]
  simp only [air_addTo, air_sem]

theorem addTo_fix (args : List Value)
    (h : argsOk air_addTo air_addTo.params.toList args = true) :
    execFunc gen air_addTo args = gen "pointers.addTo" args := by
  replace h : argsOk air_addTo [0, 1] args = true := h
  obtain ⟨v0, args, rfl, h0, h⟩ := argsOk_cons h
  obtain ⟨v1, args, rfl, h1, h⟩ := argsOk_cons h
  obtain rfl := argsOk_nil h
  replace h0 : valOk (.ptr "one" false 3) v0 = true := h0
  rw [valOk_ptr (hs := by decide) h0]
  replace h1 : valOk (.int false 32) v1 = true := h1
  rw [valOk_int h1]
  funext m
  show (execFunc gen air_addTo _).run m = (gen _ _).run m
  rw [addTo_step gen v0.toPtr (v1.toBV 32)]
  simp only [gen, air_sem]

/-- `pointers.delay`: the AIR semantics of the decoded function (under any call oracle) equals the generated definition. -/
theorem delay_step (call : Oracle) (p0 : Zig.Ptr) (p1 : BitVec 32) (m : Zig.Mem) :
    (execFunc call air_delay [(Value.ptr p0), (Value.int false 32 p1)]).run m =
      (fun r => (Value.void, r.2)) <$> (Pointers.delay p0 p1).run m := by
  conv => rhs; rw [Pointers.delay]
  simp only [air_delay, air_sem]

theorem delay_fix (args : List Value)
    (h : argsOk air_delay air_delay.params.toList args = true) :
    execFunc gen air_delay args = gen "pointers.delay" args := by
  replace h : argsOk air_delay [0, 1] args = true := h
  obtain ⟨v0, args, rfl, h0, h⟩ := argsOk_cons h
  obtain ⟨v1, args, rfl, h1, h⟩ := argsOk_cons h
  obtain rfl := argsOk_nil h
  replace h0 : valOk (.ptr "one" false 7) v0 = true := h0
  rw [valOk_ptr (hs := by decide) h0]
  replace h1 : valOk (.int false 32) v1 = true := h1
  rw [valOk_int h1]
  funext m
  show (execFunc gen air_delay _).run m = (gen _ _).run m
  rw [delay_step gen v0.toPtr (v1.toBV 32)]
  simp only [gen, air_sem]

/-- `pointers.dueOf`: the AIR semantics of the decoded function (under any call oracle) equals the generated definition. -/
theorem dueOf_step (call : Oracle) (p0 : Zig.Ptr) (m : Zig.Mem) :
    (execFunc call air_dueOf [(Value.ptr p0)]).run m =
      (fun r => ((Value.ptr r.1), r.2)) <$> (Pointers.dueOf p0).run m := by
  conv => rhs; rw [Pointers.dueOf]
  simp only [air_dueOf, air_sem]

theorem dueOf_fix (args : List Value)
    (h : argsOk air_dueOf air_dueOf.params.toList args = true) :
    execFunc gen air_dueOf args = gen "pointers.dueOf" args := by
  replace h : argsOk air_dueOf [0] args = true := h
  obtain ⟨v0, args, rfl, h0, h⟩ := argsOk_cons h
  obtain rfl := argsOk_nil h
  replace h0 : valOk (.ptr "one" false 6) v0 = true := h0
  rw [valOk_ptr (hs := by decide) h0]
  funext m
  show (execFunc gen air_dueOf _).run m = (gen _ _).run m
  rw [dueOf_step gen v0.toPtr]
  simp only [gen, air_sem]

/-- `pointers.same`: the AIR semantics of the decoded function (under any call oracle) equals the generated definition. -/
theorem same_step (call : Oracle) (p0 : Zig.Ptr) (p1 : Zig.Ptr) (m : Zig.Mem) :
    (execFunc call air_same [(Value.ptr p0), (Value.ptr p1)]).run m =
      (fun r => ((Value.bool r.1), r.2)) <$> (Pointers.same p0 p1).run m := by
  conv => rhs; rw [Pointers.same]
  simp only [air_same, air_sem]

theorem same_fix (args : List Value)
    (h : argsOk air_same air_same.params.toList args = true) :
    execFunc gen air_same args = gen "pointers.same" args := by
  replace h : argsOk air_same [0, 0] args = true := h
  obtain ⟨v0, args, rfl, h0, h⟩ := argsOk_cons h
  obtain ⟨v1, args, rfl, h1, h⟩ := argsOk_cons h
  obtain rfl := argsOk_nil h
  replace h0 : valOk (.ptr "one" true 4) v0 = true := h0
  rw [valOk_ptr (hs := by decide) h0]
  replace h1 : valOk (.ptr "one" true 4) v1 = true := h1
  rw [valOk_ptr (hs := by decide) h1]
  funext m
  show (execFunc gen air_same _).run m = (gen _ _).run m
  rw [same_step gen v0.toPtr v1.toPtr]
  simp only [gen, air_sem]

theorem air_sumTo_body : air_sumTo.body =
  #[⟨0, 0, (.arg 0)⟩,
    ⟨21, 2, (.line 2)⟩,
    ⟨1, 3, .alloc⟩,
    ⟨2, 2, (.store (.inst 1) (.int 1 (0 : Int)))⟩,
    ⟨22, 2, (.dbg (some "acc") (some (.inst 1)))⟩,
    ⟨23, 2, (.line 3)⟩,
    ⟨3, 4, .alloc⟩,
    ⟨4, 2, (.store (.inst 3) (.int 0 (0 : Int)))⟩,
    ⟨24, 2, (.dbg (some "i") (some (.inst 3)))⟩,
    ⟨5, 2, (.block #[⟨6, 5, (.loop #[⟨7, 2, (.block #[⟨25, 2, (.line 4)⟩,
    ⟨8, 0, (.load (.inst 3))⟩,
    ⟨9, 6, (.cmp .lt (.inst 8) (.inst 0))⟩,
    ⟨10, 5, (.condBr (.inst 9) #[⟨26, 2, (.line 4)⟩,
    ⟨11, 0, (.load (.inst 3))⟩,
    ⟨27, 2, (.line 4)⟩,
    ⟨12, 2, (.call (.func "pointers.addTo" false none) #[(.inst 1), (.inst 11)])⟩,
    ⟨28, 2, (.line 4)⟩,
    ⟨29, 2, (.dbg none none)⟩,
    ⟨30, 2, (.line 4)⟩,
    ⟨13, 0, (.load (.inst 3))⟩,
    ⟨31, 2, (.line 4)⟩,
    ⟨14, 0, (.arith .add .checked (.inst 13) (.int 0 (1 : Int)))⟩,
    ⟨15, 2, (.store (.inst 3) (.inst 14))⟩,
    ⟨16, 5, (.br 7 .void)⟩] #[⟨17, 5, (.br 5 .void)⟩])⟩])⟩,
    ⟨18, 5, (.repeat 6)⟩])⟩])⟩,
    ⟨32, 2, (.line 5)⟩,
    ⟨19, 1, (.load (.inst 1))⟩,
    ⟨33, 2, (.line 5)⟩,
    ⟨20, 5, (.ret (.inst 19))⟩] := rfl
theorem air_sumTo_types : air_sumTo.types = #[(.int false 32), (.int false 64), .void, (.ptr "one" false 1), (.ptr "one" false 0), .noreturn, .bool, (.other "fn (*u64, u32) void")] := rfl
theorem air_sumTo_layouts : air_sumTo.layouts = #[{ size := (some 4), align := (some 4), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 8), align := (some 8), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 0), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 8), align := (some 8), offsets := #[], ptrAlign := (some 8), sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 8), align := (some 8), offsets := #[], ptrAlign := (some 4), sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := none, align := none, offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 1), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := none, align := none, offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }] := rfl
theorem air_sumTo_params : air_sumTo.params = #[0] := rfl

/-- The generated exits of `pointers.sumTo` as AIR exits. -/
def enc_sumTo : Pointers.sumToExit → Exit
  | .ret v => .ret (Value.int false 64 v)
  | .br7 => .br 7 .void
  | .br5 => .br 5 .void
  | .rep6 => .rep 6

theorem sumTo_loop6_body (args : List Value) (env : Env) (st : Frame) (x0 : BitVec 32) (x1 : Zig.Ptr)
    (h0 : env 0 = some (0, (Value.int false 32 x0))) (h1 : env 1 = some (3, (Value.ptr x1))) (h3 : env 3 = some (4, .cell 3)) (s : Pointers.sumToLocals) (m : Zig.Mem) :
    ((execBody ⟨air_sumTo, args, gen⟩ (Array.toList #[⟨7, 2, (.block #[⟨25, 2, (.line 4)⟩,
    ⟨8, 0, (.load (.inst 3))⟩,
    ⟨9, 6, (.cmp .lt (.inst 8) (.inst 0))⟩,
    ⟨10, 5, (.condBr (.inst 9) #[⟨26, 2, (.line 4)⟩,
    ⟨11, 0, (.load (.inst 3))⟩,
    ⟨27, 2, (.line 4)⟩,
    ⟨12, 2, (.call (.func "pointers.addTo" false none) #[(.inst 1), (.inst 11)])⟩,
    ⟨28, 2, (.line 4)⟩,
    ⟨29, 2, (.dbg none none)⟩,
    ⟨30, 2, (.line 4)⟩,
    ⟨13, 0, (.load (.inst 3))⟩,
    ⟨31, 2, (.line 4)⟩,
    ⟨14, 0, (.arith .add .checked (.inst 13) (.int 0 (1 : Int)))⟩,
    ⟨15, 2, (.store (.inst 3) (.inst 14))⟩,
    ⟨16, 5, (.br 7 .void)⟩] #[⟨17, 5, (.br 5 .void)⟩])⟩])⟩,
    ⟨18, 5, (.repeat 6)⟩]) env).run (Frame.setCell st 3 (some (Value.int false 32 s.i)))).run m =
      ((fun r => (enc_sumTo r.1, (Frame.setCell st 3 (some (Value.int false 32 r.2.i))))) <$> (Pointers.sumTo.loop6 x0 x1).run s).run m := by
  conv => rhs; rw [Pointers.sumTo.loop6]
  simp only [air_sumTo_body, air_sumTo_types, air_sumTo_layouts, air_sumTo_params, air_sem, enc_sumTo, callee_0, gen, h0, h1, h3, Env.val, Frame.cell]
  all_goals repeat (first
    | rfl
    | (refine bind_congr fun _ => ?_))

theorem sumTo_loop6_comm (args : List Value) (env : Env) (st : Frame) (x0 : BitVec 32) (x1 : Zig.Ptr)
    (h0 : env 0 = some (0, (Value.int false 32 x0))) (h1 : env 1 = some (3, (Value.ptr x1))) (h3 : env 3 = some (4, .cell 3)) (s : Pointers.sumToLocals) :
    (execLoop ⟨air_sumTo, args, gen⟩ 6 #[⟨7, 2, (.block #[⟨25, 2, (.line 4)⟩,
    ⟨8, 0, (.load (.inst 3))⟩,
    ⟨9, 6, (.cmp .lt (.inst 8) (.inst 0))⟩,
    ⟨10, 5, (.condBr (.inst 9) #[⟨26, 2, (.line 4)⟩,
    ⟨11, 0, (.load (.inst 3))⟩,
    ⟨27, 2, (.line 4)⟩,
    ⟨12, 2, (.call (.func "pointers.addTo" false none) #[(.inst 1), (.inst 11)])⟩,
    ⟨28, 2, (.line 4)⟩,
    ⟨29, 2, (.dbg none none)⟩,
    ⟨30, 2, (.line 4)⟩,
    ⟨13, 0, (.load (.inst 3))⟩,
    ⟨31, 2, (.line 4)⟩,
    ⟨14, 0, (.arith .add .checked (.inst 13) (.int 0 (1 : Int)))⟩,
    ⟨15, 2, (.store (.inst 3) (.inst 14))⟩,
    ⟨16, 5, (.br 7 .void)⟩] #[⟨17, 5, (.br 5 .void)⟩])⟩])⟩,
    ⟨18, 5, (.repeat 6)⟩] env).run (Frame.setCell st 3 (some (Value.int false 32 s.i))) =
      mapRes enc_sumTo (fun s : Pointers.sumToLocals => (Frame.setCell st 3 (some (Value.int false 32 s.i)))) <$> (Zig.loop (Pointers.sumTo.loop6 x0 x1) Pointers.sumTo.again6).run s := by
  unfold execLoop
  exact loop_comm _ _ (Exit.again 6) Pointers.sumTo.again6 enc_sumTo (fun s : Pointers.sumToLocals => (Frame.setCell st 3 (some (Value.int false 32 s.i))))
    (fun s => by funext m; exact sumTo_loop6_body args env st x0 x1 h0 h1 h3 s m)
    (by intro e; cases e <;> rfl) s

theorem sumTo_loop6_exits (x0 : BitVec 32) (x1 : Zig.Ptr) (s : Pointers.sumToLocals) (m : Zig.Mem) (r : (Pointers.sumToExit × Pointers.sumToLocals) × Zig.Mem)
    (hr : (((Zig.loop (Pointers.sumTo.loop6 x0 x1) Pointers.sumTo.again6).run s).run m).run = some (.ok r)) :
    Exit.again 6 (enc_sumTo r.1.1) = false ∧ exitOk [5] [] (enc_sumTo r.1.1) = true := by
  let env : Env := (Env.set (Env.set (Env.set (fun _ => none) 0 0 (Value.int false 32 x0)) 1 3 (Value.ptr x1)) 3 4 (.cell 3))
  exact ok_transfer (F := fun s : Pointers.sumToLocals => (Frame.setCell ({} : Frame) 3 (some (Value.int false 32 s.i))))
    (sumTo_loop6_comm [] env {} x0 x1 (by simp [env, Env.set]) (by simp [env, Env.set]) (by simp [env, Env.set]) s)
    (execLoop_ok _ 6 _ env [5] [] (by simp [wfBody, wfInst, wfCases])) m r hr

theorem sumTo_loop6 (args : List Value) (env : Env) (st : Frame) (B : Array Inst)
    (hB : B = #[⟨7, 2, (.block #[⟨25, 2, (.line 4)⟩,
    ⟨8, 0, (.load (.inst 3))⟩,
    ⟨9, 6, (.cmp .lt (.inst 8) (.inst 0))⟩,
    ⟨10, 5, (.condBr (.inst 9) #[⟨26, 2, (.line 4)⟩,
    ⟨11, 0, (.load (.inst 3))⟩,
    ⟨27, 2, (.line 4)⟩,
    ⟨12, 2, (.call (.func "pointers.addTo" false none) #[(.inst 1), (.inst 11)])⟩,
    ⟨28, 2, (.line 4)⟩,
    ⟨29, 2, (.dbg none none)⟩,
    ⟨30, 2, (.line 4)⟩,
    ⟨13, 0, (.load (.inst 3))⟩,
    ⟨31, 2, (.line 4)⟩,
    ⟨14, 0, (.arith .add .checked (.inst 13) (.int 0 (1 : Int)))⟩,
    ⟨15, 2, (.store (.inst 3) (.inst 14))⟩,
    ⟨16, 5, (.br 7 .void)⟩] #[⟨17, 5, (.br 5 .void)⟩])⟩])⟩,
    ⟨18, 5, (.repeat 6)⟩])
    (h0 : env 0 = some (0, (Value.int false 32 (Value.toBV 32 (env.val 0))))) (h1 : env 1 = some (3, (Value.ptr (Value.toPtr (env.val 1))))) (h3 : env 3 = some (4, .cell 3))
    (hc3 : st.cells 3 = some (Value.int false 32 (Value.toBV 32 (st.cell 3)))) :
    (execLoop ⟨air_sumTo, args, gen⟩ 6 B env).run st =
      mapRes enc_sumTo (fun s : Pointers.sumToLocals => (Frame.setCell st 3 (some (Value.int false 32 s.i)))) <$>
        (Zig.loop (Pointers.sumTo.loop6 (Value.toBV 32 (env.val 0)) (Value.toPtr (env.val 1))) Pointers.sumTo.again6).run { (default : Pointers.sumToLocals) with i := (Value.toBV 32 (st.cell 3)), acc := Value.toPtr (env.val 1) } := by
  subst hB
  have e : (Frame.setCell st 3 (some (Value.int false 32 { (default : Pointers.sumToLocals) with i := (Value.toBV 32 (st.cell 3)), acc := Value.toPtr (env.val 1) }.i))) = st := by
    dsimp only
    rw [Frame.setCell_eq _ _ _ hc3]
  conv => lhs; rw [← e]
  exact sumTo_loop6_comm args env st (Value.toBV 32 (env.val 0)) (Value.toPtr (env.val 1)) h0 h1 h3 { (default : Pointers.sumToLocals) with i := (Value.toBV 32 (st.cell 3)), acc := Value.toPtr (env.val 1) }

/-- `pointers.sumTo`: the AIR semantics of the decoded function, with the generated program answering its calls, equals the generated definition. -/
theorem sumTo_step (p0 : BitVec 32) (m : Zig.Mem) :
    (execFunc gen air_sumTo [(Value.int false 32 p0)]).run m =
      (fun r => ((Value.int false 64 r.1), r.2)) <$> (Pointers.sumTo p0).run m := by
  conv => rhs; rw [Pointers.sumTo]
  simp only [air_sumTo_body, air_sumTo_types, air_sumTo_layouts, air_sumTo_params, air_sem, enc_sumTo, callee_0, gen, sumTo_loop6, Env.val, Frame.cell]
  all_goals repeat (first
    | rfl
    | (refine bind_congr_ok _ _ (fun r hr => sumTo_loop6_exits _ _ _ _ r hr) ?_
       rintro ⟨⟨e, s⟩, m⟩ ⟨h1, h2⟩
       cases e <;> simp (config := { failIfUnchanged := false }) only [air_sumTo_body, air_sumTo_types, air_sumTo_layouts, air_sumTo_params, air_sem, enc_sumTo, callee_0, gen, Env.val, Frame.cell, Exit.again, exitOk] at h1 h2 ⊢)
    | (refine bind_congr fun _ => ?_))

theorem sumTo_fix (args : List Value)
    (h : argsOk air_sumTo air_sumTo.params.toList args = true) :
    execFunc gen air_sumTo args = gen "pointers.sumTo" args := by
  replace h : argsOk air_sumTo [0] args = true := h
  obtain ⟨v0, args, rfl, h0, h⟩ := argsOk_cons h
  obtain rfl := argsOk_nil h
  replace h0 : valOk (.int false 32) v0 = true := h0
  rw [valOk_int h0]
  funext m
  show (execFunc gen air_sumTo _).run m = (gen _ _).run m
  rw [sumTo_step (v0.toBV 32)]
  simp only [gen, air_sem]

/-- `pointers.swap`: the AIR semantics of the decoded function (under any call oracle) equals the generated definition. -/
theorem swap_step (call : Oracle) (p0 : Zig.Ptr) (p1 : Zig.Ptr) (m : Zig.Mem) :
    (execFunc call air_swap [(Value.ptr p0), (Value.ptr p1)]).run m =
      (fun r => (Value.void, r.2)) <$> (Pointers.swap p0 p1).run m := by
  conv => rhs; rw [Pointers.swap]
  simp only [air_swap, air_sem]

theorem swap_fix (args : List Value)
    (h : argsOk air_swap air_swap.params.toList args = true) :
    execFunc gen air_swap args = gen "pointers.swap" args := by
  replace h : argsOk air_swap [0, 0] args = true := h
  obtain ⟨v0, args, rfl, h0, h⟩ := argsOk_cons h
  obtain ⟨v1, args, rfl, h1, h⟩ := argsOk_cons h
  obtain rfl := argsOk_nil h
  replace h0 : valOk (.ptr "one" false 2) v0 = true := h0
  rw [valOk_ptr (hs := by decide) h0]
  replace h1 : valOk (.ptr "one" false 2) v1 = true := h1
  rw [valOk_ptr (hs := by decide) h1]
  funext m
  show (execFunc gen air_swap _).run m = (gen _ _).run m
  rw [swap_step gen v0.toPtr v1.toPtr]
  simp only [gen, air_sem]

/-- The generated program satisfies every certified function's AIR equation. -/
theorem gen_fixpoint : Fixpoint gen table :=
  ⟨addTo_fix, delay_fix, dueOf_fix, same_fix, sumTo_fix, swap_fix, trivial⟩

/-- The AIR semantics of the certified program (`Sem.run`, the least fixpoint) is below the
generated program: every terminating AIR behaviour is the generated definition's. -/
theorem run_le_gen : Lean.Order.PartialOrder.rel (run (progOf table)) gen :=
  run_le_of_table gen_fixpoint

/-- `pointers.addTo` makes no certified call: its AIR semantics equals the generated definition. -/
theorem addTo_run (p0 : Zig.Ptr) (p1 : BitVec 32) (m : Zig.Mem) :
    (run (progOf table) "pointers.addTo" [(Value.ptr p0), (Value.int false 32 p1)]).run m =
      (fun r => (Value.void, r.2)) <$> (Pointers.addTo p0 p1).run m := by
  rw [run_of_lookup (by rfl)]
  exact addTo_step _ p0 p1 m

theorem addTo_complete (p0 : Zig.Ptr) (p1 : BitVec 32) (m : Zig.Mem) :
    Lean.Order.PartialOrder.rel ((fun r => (Value.void, r.2)) <$> (Pointers.addTo p0 p1).run m)
      ((run (progOf table) "pointers.addTo" [(Value.ptr p0), (Value.int false 32 p1)]).run m) :=
  rel_of_eq (addTo_run p0 p1 m).symm

/-- `pointers.delay` makes no certified call: its AIR semantics equals the generated definition. -/
theorem delay_run (p0 : Zig.Ptr) (p1 : BitVec 32) (m : Zig.Mem) :
    (run (progOf table) "pointers.delay" [(Value.ptr p0), (Value.int false 32 p1)]).run m =
      (fun r => (Value.void, r.2)) <$> (Pointers.delay p0 p1).run m := by
  rw [run_of_lookup (by rfl)]
  exact delay_step _ p0 p1 m

theorem delay_complete (p0 : Zig.Ptr) (p1 : BitVec 32) (m : Zig.Mem) :
    Lean.Order.PartialOrder.rel ((fun r => (Value.void, r.2)) <$> (Pointers.delay p0 p1).run m)
      ((run (progOf table) "pointers.delay" [(Value.ptr p0), (Value.int false 32 p1)]).run m) :=
  rel_of_eq (delay_run p0 p1 m).symm

/-- `pointers.dueOf` makes no certified call: its AIR semantics equals the generated definition. -/
theorem dueOf_run (p0 : Zig.Ptr) (m : Zig.Mem) :
    (run (progOf table) "pointers.dueOf" [(Value.ptr p0)]).run m =
      (fun r => ((Value.ptr r.1), r.2)) <$> (Pointers.dueOf p0).run m := by
  rw [run_of_lookup (by rfl)]
  exact dueOf_step _ p0 m

theorem dueOf_complete (p0 : Zig.Ptr) (m : Zig.Mem) :
    Lean.Order.PartialOrder.rel ((fun r => ((Value.ptr r.1), r.2)) <$> (Pointers.dueOf p0).run m)
      ((run (progOf table) "pointers.dueOf" [(Value.ptr p0)]).run m) :=
  rel_of_eq (dueOf_run p0 m).symm

/-- `pointers.same` makes no certified call: its AIR semantics equals the generated definition. -/
theorem same_run (p0 : Zig.Ptr) (p1 : Zig.Ptr) (m : Zig.Mem) :
    (run (progOf table) "pointers.same" [(Value.ptr p0), (Value.ptr p1)]).run m =
      (fun r => ((Value.bool r.1), r.2)) <$> (Pointers.same p0 p1).run m := by
  rw [run_of_lookup (by rfl)]
  exact same_step _ p0 p1 m

theorem same_complete (p0 : Zig.Ptr) (p1 : Zig.Ptr) (m : Zig.Mem) :
    Lean.Order.PartialOrder.rel ((fun r => ((Value.bool r.1), r.2)) <$> (Pointers.same p0 p1).run m)
      ((run (progOf table) "pointers.same" [(Value.ptr p0), (Value.ptr p1)]).run m) :=
  rel_of_eq (same_run p0 p1 m).symm

/-- `pointers.swap` makes no certified call: its AIR semantics equals the generated definition. -/
theorem swap_run (p0 : Zig.Ptr) (p1 : Zig.Ptr) (m : Zig.Mem) :
    (run (progOf table) "pointers.swap" [(Value.ptr p0), (Value.ptr p1)]).run m =
      (fun r => (Value.void, r.2)) <$> (Pointers.swap p0 p1).run m := by
  rw [run_of_lookup (by rfl)]
  exact swap_step _ p0 p1 m

theorem swap_complete (p0 : Zig.Ptr) (p1 : Zig.Ptr) (m : Zig.Mem) :
    Lean.Order.PartialOrder.rel ((fun r => (Value.void, r.2)) <$> (Pointers.swap p0 p1).run m)
      ((run (progOf table) "pointers.swap" [(Value.ptr p0), (Value.ptr p1)]).run m) :=
  rel_of_eq (swap_run p0 p1 m).symm

/-- `pointers.sumTo`: every terminating AIR run is the generated definition's. -/
theorem sumTo_sound (p0 : BitVec 32) (m : Zig.Mem) :
    Lean.Order.PartialOrder.rel ((run (progOf table) "pointers.sumTo" [(Value.int false 32 p0)]).run m)
      ((fun r => ((Value.int false 64 r.1), r.2)) <$> (Pointers.sumTo p0).run m) := by
  have h : Lean.Order.PartialOrder.rel ((run (progOf table) "pointers.sumTo" [(Value.int false 32 p0)]).run m)
      ((gen "pointers.sumTo" [(Value.int false 32 p0)]).run m) := run_le_gen "pointers.sumTo" [(Value.int false 32 p0)] m
  simp only [gen, air_sem] at h
  exact h

-- `pointers.sumTo`: no completeness theorem (arity, memory or callee outside this generator's scheme).
end Pointers.AirCert
