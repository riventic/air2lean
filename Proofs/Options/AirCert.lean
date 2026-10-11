-- air2lean AIR semantics certificate (docs/air-semantics.md). Generated; do not edit.
import Air2Lean.SemView
import Proofs.Options.Gen

set_option linter.unusedSimpArgs false

namespace Options.AirCert

open Air2Lean Air2Lean.Sem

/-! Certified: `options.find`

Outside the certificate fragment:

* `options.findOr`: a function with a slice parameter that reads memory other than through its items (`Sem.roBody`)
* `options.firstIndexPlusOne`: a function with a slice parameter that reads memory other than through its items (`Sem.roBody`)
-/

/-- The decoded canonical AIR of `options.find`. -/
def air_find : Func :=
{ dialect := { version := Air2Lean.ZigVersion.v0_15_2, arch := "", ptrBytes := 8, endian := Air2Lean.Endian.little, errorSetBits := 16, backend := "unverified", buildMode := "unverified" }, name := "options.find",
  params := #[0, 1], ret := 2,
  types := #[(.ptr "slice" true 1), (.int false 32), (.optional 5), (.ptr "one" false 5), .void, (.int false 64), .noreturn, (.int false 64), .bool],
  layouts := #[{ size := (some 16), align := (some 8), offsets := #[], ptrAlign := (some 4), sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 4), align := (some 4), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 16), align := (some 8), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 8), align := (some 8), offsets := #[], ptrAlign := (some 8), sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 0), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 8), align := (some 8), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := none, align := none, offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 8), align := (some 8), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 1), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }],
  globals := #[],
  body := #[⟨0, 0, (.arg 0)⟩,
    ⟨1, 1, (.arg 1)⟩,
    ⟨2, 3, .alloc⟩,
    ⟨3, 4, (.store (.inst 2) (.int 5 (0 : Int)))⟩,
    ⟨26, 4, (.line 2)⟩,
    ⟨4, 5, (.sliceLen (.inst 0))⟩,
    ⟨5, 4, (.block #[⟨6, 6, (.loop #[⟨7, 5, (.load (.inst 2))⟩,
    ⟨8, 4, (.block #[⟨9, 7, (.bitcast (.inst 7))⟩,
    ⟨10, 7, (.bitcast (.inst 4))⟩,
    ⟨11, 8, (.cmp .lt (.inst 9) (.inst 10))⟩,
    ⟨12, 6, (.condBr (.inst 11) #[⟨13, 1, (.sliceElemVal (.inst 0) (.inst 7))⟩,
    ⟨27, 4, (.dbg (some "v") (some (.inst 13)))⟩,
    ⟨28, 4, (.dbg (some "i") (some (.inst 7)))⟩,
    ⟨29, 4, (.line 3)⟩,
    ⟨14, 4, (.block #[⟨15, 8, (.cmp .eq (.inst 13) (.inst 1))⟩,
    ⟨16, 6, (.condBr (.inst 15) #[⟨30, 4, (.line 3)⟩,
    ⟨17, 2, (.wrapOptional (.inst 7))⟩,
    ⟨18, 6, (.ret (.inst 17))⟩] #[⟨19, 6, (.br 14 .void)⟩])⟩])⟩,
    ⟨31, 4, (.line 4)⟩,
    ⟨32, 4, (.dbg none none)⟩,
    ⟨20, 6, (.br 8 .void)⟩] #[⟨21, 6, (.br 5 .void)⟩])⟩])⟩,
    ⟨22, 5, (.arith .add .checked (.inst 7) (.int 5 (1 : Int)))⟩,
    ⟨23, 4, (.store (.inst 2) (.inst 22))⟩,
    ⟨24, 6, (.repeat 6)⟩])⟩])⟩,
    ⟨33, 4, (.line 5)⟩,
    ⟨25, 6, (.ret (.optNull 2))⟩] }


/-- The items of `options.find`'s slice parameters, by their `arg` instruction. -/
def view_find (a0 : Array (BitVec 32)) : InstId → Option (Array Value) :=
  fun k => if k = 0 then some (a0.map (fun x => (Value.int false 32 x))) else none

/-- The item type of each viewed slice. -/
def viewTy_find : InstId → TyId :=
  fun k => if k = 0 then 1 else 0

theorem air_find_body : air_find.body =
  #[⟨0, 0, (.arg 0)⟩,
    ⟨1, 1, (.arg 1)⟩,
    ⟨2, 3, .alloc⟩,
    ⟨3, 4, (.store (.inst 2) (.int 5 (0 : Int)))⟩,
    ⟨26, 4, (.line 2)⟩,
    ⟨4, 5, (.sliceLen (.inst 0))⟩,
    ⟨5, 4, (.block #[⟨6, 6, (.loop #[⟨7, 5, (.load (.inst 2))⟩,
    ⟨8, 4, (.block #[⟨9, 7, (.bitcast (.inst 7))⟩,
    ⟨10, 7, (.bitcast (.inst 4))⟩,
    ⟨11, 8, (.cmp .lt (.inst 9) (.inst 10))⟩,
    ⟨12, 6, (.condBr (.inst 11) #[⟨13, 1, (.sliceElemVal (.inst 0) (.inst 7))⟩,
    ⟨27, 4, (.dbg (some "v") (some (.inst 13)))⟩,
    ⟨28, 4, (.dbg (some "i") (some (.inst 7)))⟩,
    ⟨29, 4, (.line 3)⟩,
    ⟨14, 4, (.block #[⟨15, 8, (.cmp .eq (.inst 13) (.inst 1))⟩,
    ⟨16, 6, (.condBr (.inst 15) #[⟨30, 4, (.line 3)⟩,
    ⟨17, 2, (.wrapOptional (.inst 7))⟩,
    ⟨18, 6, (.ret (.inst 17))⟩] #[⟨19, 6, (.br 14 .void)⟩])⟩])⟩,
    ⟨31, 4, (.line 4)⟩,
    ⟨32, 4, (.dbg none none)⟩,
    ⟨20, 6, (.br 8 .void)⟩] #[⟨21, 6, (.br 5 .void)⟩])⟩])⟩,
    ⟨22, 5, (.arith .add .checked (.inst 7) (.int 5 (1 : Int)))⟩,
    ⟨23, 4, (.store (.inst 2) (.inst 22))⟩,
    ⟨24, 6, (.repeat 6)⟩])⟩])⟩,
    ⟨33, 4, (.line 5)⟩,
    ⟨25, 6, (.ret (.optNull 2))⟩] := rfl
theorem air_find_types : air_find.types = #[(.ptr "slice" true 1), (.int false 32), (.optional 5), (.ptr "one" false 5), .void, (.int false 64), .noreturn, (.int false 64), .bool] := rfl
theorem air_find_layouts : air_find.layouts = #[{ size := (some 16), align := (some 8), offsets := #[], ptrAlign := (some 4), sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 4), align := (some 4), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 16), align := (some 8), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 8), align := (some 8), offsets := #[], ptrAlign := (some 8), sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 0), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 8), align := (some 8), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := none, align := none, offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 8), align := (some 8), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }, { size := (some 1), align := (some 1), offsets := #[], ptrAlign := none, sentinel := false, sentinelByte := none, isVolatile := false, allowzero := false, hostSize := 0, bitOffset := 0, packedLanes := false, vectorIndex := none, runtimeLane := false, vectorIndexExported := false }] := rfl
theorem air_find_params : air_find.params = #[0, 1] := rfl

/-- The generated exits of `options.find` as AIR exits. -/
def enc_find : Options.findExit → Exit
  | .ret v => .ret (Value.ofOpt (fun x => (Value.int false 64 x)) v)
  | .br14 => .br 14 .void
  | .br8 => .br 8 .void
  | .br5 => .br 5 .void
  | .rep6 => .rep 6

theorem find_loop6_body (call : Oracle) (a0 : Array (BitVec 32)) (p0 : Zig.Slice) (hs0 : a0.size = p0.len.toNat) (args : List Value) (env : Env) (st : Frame) (x1 : BitVec 32) (x4 : BitVec 64)
    (h0 : env 0 = some (0, (Value.slice p0))) (h1 : env 1 = some (1, (Value.int false 32 x1))) (h4 : env 4 = some (5, (Value.int false 64 x4))) (h2 : env 2 = some (3, .cell 2)) (s : Options.findLocals) (m : Zig.Mem) :
    ((execBody ⟨air_find, args, call, (view_find a0)⟩ (Array.toList #[⟨7, 5, (.load (.inst 2))⟩,
    ⟨8, 4, (.block #[⟨9, 7, (.bitcast (.inst 7))⟩,
    ⟨10, 7, (.bitcast (.inst 4))⟩,
    ⟨11, 8, (.cmp .lt (.inst 9) (.inst 10))⟩,
    ⟨12, 6, (.condBr (.inst 11) #[⟨13, 1, (.sliceElemVal (.inst 0) (.inst 7))⟩,
    ⟨27, 4, (.dbg (some "v") (some (.inst 13)))⟩,
    ⟨28, 4, (.dbg (some "i") (some (.inst 7)))⟩,
    ⟨29, 4, (.line 3)⟩,
    ⟨14, 4, (.block #[⟨15, 8, (.cmp .eq (.inst 13) (.inst 1))⟩,
    ⟨16, 6, (.condBr (.inst 15) #[⟨30, 4, (.line 3)⟩,
    ⟨17, 2, (.wrapOptional (.inst 7))⟩,
    ⟨18, 6, (.ret (.inst 17))⟩] #[⟨19, 6, (.br 14 .void)⟩])⟩])⟩,
    ⟨31, 4, (.line 4)⟩,
    ⟨32, 4, (.dbg none none)⟩,
    ⟨20, 6, (.br 8 .void)⟩] #[⟨21, 6, (.br 5 .void)⟩])⟩])⟩,
    ⟨22, 5, (.arith .add .checked (.inst 7) (.int 5 (1 : Int)))⟩,
    ⟨23, 4, (.store (.inst 2) (.inst 22))⟩,
    ⟨24, 6, (.repeat 6)⟩]) env).run (Frame.setCell st 2 (some (Value.int false 64 s.local2)))).run m =
      (fun r => ((enc_find r.1, (Frame.setCell st 2 (some (Value.int false 64 r.2.local2)))), m)) <$> (Options.find.loop6 a0 x1 x4).run s := by
  conv => rhs; rw [Options.find.loop6]
  simp only [air_find_body, air_find_types, air_find_layouts, air_find_params, air_sem, enc_find, execFuncV, view_find, len_of_size hs0, hs0, h0, h1, h4, h2, Env.val, Frame.cell]
  all_goals repeat (first
    | rfl
    | (refine bind_congr fun _ => ?_))

theorem find_loop6_comm (call : Oracle) (a0 : Array (BitVec 32)) (p0 : Zig.Slice) (hs0 : a0.size = p0.len.toNat) (args : List Value) (env : Env) (st : Frame) (x1 : BitVec 32) (x4 : BitVec 64)
    (h0 : env 0 = some (0, (Value.slice p0))) (h1 : env 1 = some (1, (Value.int false 32 x1))) (h4 : env 4 = some (5, (Value.int false 64 x4))) (h2 : env 2 = some (3, .cell 2)) (s : Options.findLocals) (m : Zig.Mem) :
    ((execLoop ⟨air_find, args, call, (view_find a0)⟩ 6 #[⟨7, 5, (.load (.inst 2))⟩,
    ⟨8, 4, (.block #[⟨9, 7, (.bitcast (.inst 7))⟩,
    ⟨10, 7, (.bitcast (.inst 4))⟩,
    ⟨11, 8, (.cmp .lt (.inst 9) (.inst 10))⟩,
    ⟨12, 6, (.condBr (.inst 11) #[⟨13, 1, (.sliceElemVal (.inst 0) (.inst 7))⟩,
    ⟨27, 4, (.dbg (some "v") (some (.inst 13)))⟩,
    ⟨28, 4, (.dbg (some "i") (some (.inst 7)))⟩,
    ⟨29, 4, (.line 3)⟩,
    ⟨14, 4, (.block #[⟨15, 8, (.cmp .eq (.inst 13) (.inst 1))⟩,
    ⟨16, 6, (.condBr (.inst 15) #[⟨30, 4, (.line 3)⟩,
    ⟨17, 2, (.wrapOptional (.inst 7))⟩,
    ⟨18, 6, (.ret (.inst 17))⟩] #[⟨19, 6, (.br 14 .void)⟩])⟩])⟩,
    ⟨31, 4, (.line 4)⟩,
    ⟨32, 4, (.dbg none none)⟩,
    ⟨20, 6, (.br 8 .void)⟩] #[⟨21, 6, (.br 5 .void)⟩])⟩])⟩,
    ⟨22, 5, (.arith .add .checked (.inst 7) (.int 5 (1 : Int)))⟩,
    ⟨23, 4, (.store (.inst 2) (.inst 22))⟩,
    ⟨24, 6, (.repeat 6)⟩] env).run (Frame.setCell st 2 (some (Value.int false 64 s.local2)))).run m =
      (fun r => (mapRes enc_find (fun s : Options.findLocals => (Frame.setCell st 2 (some (Value.int false 64 s.local2)))) r, m)) <$> (Zig.loop (Options.find.loop6 a0 x1 x4) Options.find.again6).run s := by
  unfold execLoop
  exact loop_comm_pure _ _ (Exit.again 6) Options.find.again6 enc_find (fun s : Options.findLocals => (Frame.setCell st 2 (some (Value.int false 64 s.local2))))
    (fun s m => find_loop6_body call a0 p0 hs0 args env st x1 x4 h0 h1 h4 h2 s m)
    (by intro e; cases e <;> rfl) s m

theorem find_loop6_exits (a0 : Array (BitVec 32)) (p0 : Zig.Slice) (hs0 : a0.size = p0.len.toNat) (x1 : BitVec 32) (x4 : BitVec 64) (s : Options.findLocals) (r : Options.findExit × Options.findLocals)
    (hr : ((Zig.loop (Options.find.loop6 a0 x1 x4) Options.find.again6).run s).run = some (.ok r)) :
    Exit.again 6 (enc_find r.1) = false ∧ exitOk [5] [] (enc_find r.1) = true := by
  let env : Env := (Env.set (Env.set (Env.set (Env.set (fun _ => none) 0 0 (Value.slice p0)) 1 1 (Value.int false 32 x1)) 4 5 (Value.int false 64 x4)) 2 3 (.cell 2))
  exact ok_transfer_pure (F := fun s : Options.findLocals => (Frame.setCell ({} : Frame) 2 (some (Value.int false 64 s.local2))))
    (fun m => find_loop6_comm (fun _ _ => StateT.lift stuck) a0 p0 hs0 [] env {} x1 x4 (by simp [env, Env.set]) (by simp [env, Env.set]) (by simp [env, Env.set]) (by simp [env, Env.set]) s m)
    (execLoop_ok _ 6 _ env [5] [] (by simp [wfBody, wfInst, wfCases])) r hr

theorem find_loop6 (call : Oracle) (a0 : Array (BitVec 32)) (args : List Value) (env : Env) (st : Frame) (B : Array Inst)
    (hB : B = #[⟨7, 5, (.load (.inst 2))⟩,
    ⟨8, 4, (.block #[⟨9, 7, (.bitcast (.inst 7))⟩,
    ⟨10, 7, (.bitcast (.inst 4))⟩,
    ⟨11, 8, (.cmp .lt (.inst 9) (.inst 10))⟩,
    ⟨12, 6, (.condBr (.inst 11) #[⟨13, 1, (.sliceElemVal (.inst 0) (.inst 7))⟩,
    ⟨27, 4, (.dbg (some "v") (some (.inst 13)))⟩,
    ⟨28, 4, (.dbg (some "i") (some (.inst 7)))⟩,
    ⟨29, 4, (.line 3)⟩,
    ⟨14, 4, (.block #[⟨15, 8, (.cmp .eq (.inst 13) (.inst 1))⟩,
    ⟨16, 6, (.condBr (.inst 15) #[⟨30, 4, (.line 3)⟩,
    ⟨17, 2, (.wrapOptional (.inst 7))⟩,
    ⟨18, 6, (.ret (.inst 17))⟩] #[⟨19, 6, (.br 14 .void)⟩])⟩])⟩,
    ⟨31, 4, (.line 4)⟩,
    ⟨32, 4, (.dbg none none)⟩,
    ⟨20, 6, (.br 8 .void)⟩] #[⟨21, 6, (.br 5 .void)⟩])⟩])⟩,
    ⟨22, 5, (.arith .add .checked (.inst 7) (.int 5 (1 : Int)))⟩,
    ⟨23, 4, (.store (.inst 2) (.inst 22))⟩,
    ⟨24, 6, (.repeat 6)⟩])
    (h0 : env 0 = some (0, Value.slice (Value.toSlice (env.val 0)))) (h1 : env 1 = some (1, (Value.int false 32 (Value.toBV 32 (env.val 1))))) (h4 : env 4 = some (5, (Value.int false 64 (Value.toBV 64 (env.val 4))))) (h2 : env 2 = some (3, .cell 2)) (hs0 : a0.size = (Value.toSlice (env.val 0)).len.toNat)
    (hc2 : st.cells 2 = some (Value.int false 64 (Value.toBV 64 (st.cell 2)))) :
    (execLoop ⟨air_find, args, call, (view_find a0)⟩ 6 B env).run st =
      StateT.lift (mapRes enc_find (fun s : Options.findLocals => (Frame.setCell st 2 (some (Value.int false 64 s.local2)))) <$>
        (Zig.loop (Options.find.loop6 a0 (Value.toBV 32 (env.val 1)) (Value.toBV 64 (env.val 4))) Options.find.again6).run { (default : Options.findLocals) with local2 := (Value.toBV 64 (st.cell 2)) }) := by
  subst hB
  have e : (Frame.setCell st 2 (some (Value.int false 64 { (default : Options.findLocals) with local2 := (Value.toBV 64 (st.cell 2)) }.local2))) = st := by
    dsimp only
    rw [Frame.setCell_eq _ _ _ hc2]
  conv => lhs; rw [← e]
  apply StateT.ext; intro m
  rw [lift_map_run]
  exact find_loop6_comm call a0 (Value.toSlice (env.val 0)) hs0 args env st (Value.toBV 32 (env.val 1)) (Value.toBV 64 (env.val 4)) h0 h1 h4 h2 { (default : Options.findLocals) with local2 := (Value.toBV 64 (st.cell 2)) } m

/-- `options.find` run with the items of its slices as a view equals the generated definition. -/
theorem find_view (call : Oracle) (p0 : Zig.Slice) (a0 : Array (BitVec 32)) (hs0 : a0.size = p0.len.toNat) (p1 : BitVec 32) (m : Zig.Mem) :
    (execFuncV call (view_find a0) air_find [Value.slice p0, (Value.int false 32 p1)]).run m =
      (fun v => ((Value.ofOpt (fun x => (Value.int false 64 x)) v), m)) <$> Options.find a0 p1 := by
  conv => rhs; rw [Options.find]
  simp only [air_find_body, air_find_types, air_find_layouts, air_find_params, air_sem, enc_find, execFuncV, view_find, len_of_size hs0, hs0, find_loop6, Env.val, Frame.cell]
  all_goals repeat (first
    | rfl
    | (refine bind_congr_ok _ _ (fun r hr => find_loop6_exits a0 p0 hs0 _ _ _ r hr) ?_
       rintro ⟨e, s⟩ ⟨h1, h2⟩
       cases e <;> simp (config := { failIfUnchanged := false }) only [air_find_body, air_find_types, air_find_layouts, air_find_params, air_sem, enc_find, execFuncV, view_find, len_of_size hs0, hs0, Env.val, Frame.cell, Exit.again, exitOk] at h1 h2 ⊢)
    | (refine bind_congr fun _ => ?_))

/-- `options.find`, called with the items its caller read (`Zig.readSlice`, from `m`): the AIR
semantics has the generated definition's values and errors, and its memory is `m` up to read
entries of the running thread (`UpToReads`). -/
theorem find_step (call : Oracle) (p0 : Zig.Slice) (p1 : BitVec 32) (m : Zig.Mem) (hwf : m.ClockWf)
    (a0 : Array (BitVec 32)) (m0 : Zig.Mem)
    (r0 : ((Zig.readSlice (BitVec 32) 4 p0).run m).run = some (.ok (a0, m0))) :
    RelR (fun p q => p.1 = q.1 ∧ UpToReads m p.2 ∧ q.2 = m)
      ((execFunc call air_find [Value.slice p0, (Value.int false 32 p1)]).run m)
      ((fun v => ((Value.ofOpt (fun x => (Value.int false 64 x)) v), m)) <$> Options.find a0 p1) := by
  obtain ⟨v0, hs0, -⟩ := holds_of_readSlice (f := air_find) (t := 1) (a := 4)
    (fun x => (Value.int false 32 x)) r0 hwf (fun q al => by simp only [air_find, air_sem])
    (fun size al h => by
      simp only [air_find, air_sem, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      decide)
  rw [← find_view call p0 a0 hs0 p1 m]
  refine execFunc_view m air_find _ call (view_find a0) viewTy_find
    (by simp only [roBody, roNested, roCases, roInst, argAt, air_find, air_sem, view_find, viewTy_find,
      List.find?_cons, List.find?_nil, cond_true, cond_false, Option.isSome_some])
    ⟨by simp [Value.noPtr], ?_⟩
  intro k items idx t hk ha
  simp only [view_find] at hk
  split at hk
  · cases hk
    subst_vars
    rw [show argAt air_find 0 = some (0, 0) from rfl] at ha
    cases ha
    exact ⟨p0, 4, rfl, rfl, v0, by simp [Value.noPtr]⟩
  all_goals cases hk

/-- The functions certified through a view of their slices, by fully qualified name. -/
def views : Table := [
  ("options.find", air_find)]

end Options.AirCert
