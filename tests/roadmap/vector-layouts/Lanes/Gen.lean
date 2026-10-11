-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.19-musl","zig_version":"0.16.0"}}
import ZigLean


namespace Lanes

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ []

structure flipBoolLocals where
  deriving Inhabited

inductive flipBoolExit where
  | ret

def flipBool (p0 : Zig.Ptr) : Zig.MemM (Unit) := do
  let e ← ((do
    let i1 ← Zig.loadLane (Bool) 1 1 3 p0
    let i2 ← pure (!i1)
    Zig.storeLane (α := Bool) 1 1 3 p0 i2
    pure .ret) : Zig.MM flipBoolLocals flipBoolExit).run' (default : flipBoolLocals)
  match e with
  | .ret => pure ()

structure boolLaneLocals where
  v : Zig.Ptr
  local46 : Zig.Ptr
  r : BitVec 8
  deriving Inhabited

inductive boolLaneExit where
  | ret (v : BitVec 8)
  | br3
  | br9
  | br16
  | br23
  | br30
  | br51
  | br59
  | br68
  | br77
  | br86

def boolLane (p0 : BitVec 8) : Zig.MemM (BitVec 8) := do
  let s1 ← Zig.allocStack 1 1
  let s46 ← Zig.allocStack 5 1
  let e ← ((do
    let i1 ← pure (← get).v
    Zig.storeUndef (Zig.Vec (Bool) 5) 1 i1
    match ← ((do
      let i4 ← pure i1
      let i5 ← pure (p0 &&& (1 : BitVec 8))
      let i6 ← pure (i5 != (0 : BitVec 8))
      Zig.storeLane (α := Bool) 1 1 0 i4 i6
      pure .br3) : Zig.MM boolLaneLocals boolLaneExit) with
    | .br3 => (do
      match ← ((do
        let i10 ← pure i1
        let i11 ← pure (Zig.shr false p0 (1 : BitVec 3))
        let i12 ← pure (i11 &&& (1 : BitVec 8))
        let i13 ← pure (i12 != (0 : BitVec 8))
        Zig.storeLane (α := Bool) 1 1 1 i10 i13
        pure .br9) : Zig.MM boolLaneLocals boolLaneExit) with
      | .br9 => (do
        match ← ((do
          let i17 ← pure i1
          let i18 ← pure (Zig.shr false p0 (2 : BitVec 3))
          let i19 ← pure (i18 &&& (1 : BitVec 8))
          let i20 ← pure (i19 != (0 : BitVec 8))
          Zig.storeLane (α := Bool) 1 1 2 i17 i20
          pure .br16) : Zig.MM boolLaneLocals boolLaneExit) with
        | .br16 => (do
          match ← ((do
            let i24 ← pure i1
            let i25 ← pure (Zig.shr false p0 (3 : BitVec 3))
            let i26 ← pure (i25 &&& (1 : BitVec 8))
            let i27 ← pure (i26 != (0 : BitVec 8))
            Zig.storeLane (α := Bool) 1 1 3 i24 i27
            pure .br23) : Zig.MM boolLaneLocals boolLaneExit) with
          | .br23 => (do
            match ← ((do
              let i31 ← pure i1
              let i32 ← pure (Zig.shr false p0 (4 : BitVec 3))
              let i33 ← pure (i32 &&& (1 : BitVec 8))
              let i34 ← pure (i33 != (0 : BitVec 8))
              Zig.storeLane (α := Bool) 1 1 4 i31 i34
              pure .br30) : Zig.MM boolLaneLocals boolLaneExit) with
            | .br30 => (do
              let i37 ← pure i1
              let _i38 ← Zig.callM (flipBool i37)
              let i39 ← Zig.load (Zig.Vec (Bool) 5) 1 i1
              let i40 ← Zig.callR (Zig.vindex i39.lanes (0 : BitVec 64))
              let i41 ← Zig.callR (Zig.vindex i39.lanes (1 : BitVec 64))
              let i42 ← Zig.callR (Zig.vindex i39.lanes (2 : BitVec 64))
              let i43 ← Zig.callR (Zig.vindex i39.lanes (3 : BitVec 64))
              let i44 ← Zig.callR (Zig.vindex i39.lanes (4 : BitVec 64))
              let i45 ← pure (#v[i40, i41, i42, i43, i44] : Vector (Bool) 5)
              let i46 ← pure (← get).local46
              Zig.store (α := Vector (Bool) 5) 1 i46 i45
              let i48 ← pure (i46)
              modify (fun s => { s with r := (0 : BitVec 8) })
              match ← ((do
                let i52 ← pure ((← get).r)
                let i53 ← Zig.callM (Zig.load (Bool) 1 (i48.elem 1 (0 : BitVec 64)))
                let i54 ← pure (if i53 then 1 else 0 : BitVec 1)
                let i55 ← Zig.intCast false false 8 i54
                let i56 ← pure (i52 ||| i55)
                modify (fun s => { s with r := i56 })
                pure .br51) : Zig.MM boolLaneLocals boolLaneExit) with
              | .br51 => (do
                match ← ((do
                  let i60 ← pure ((← get).r)
                  let i61 ← Zig.callM (Zig.load (Bool) 1 (i48.elem 1 (1 : BitVec 64)))
                  let i62 ← pure (if i61 then 1 else 0 : BitVec 1)
                  let i63 ← Zig.intCast false false 8 i62
                  let i64 ← pure (Zig.shl i63 (1 : BitVec 3))
                  let i65 ← pure (i60 ||| i64)
                  modify (fun s => { s with r := i65 })
                  pure .br59) : Zig.MM boolLaneLocals boolLaneExit) with
                | .br59 => (do
                  match ← ((do
                    let i69 ← pure ((← get).r)
                    let i70 ← Zig.callM (Zig.load (Bool) 1 (i48.elem 1 (2 : BitVec 64)))
                    let i71 ← pure (if i70 then 1 else 0 : BitVec 1)
                    let i72 ← Zig.intCast false false 8 i71
                    let i73 ← pure (Zig.shl i72 (2 : BitVec 3))
                    let i74 ← pure (i69 ||| i73)
                    modify (fun s => { s with r := i74 })
                    pure .br68) : Zig.MM boolLaneLocals boolLaneExit) with
                  | .br68 => (do
                    match ← ((do
                      let i78 ← pure ((← get).r)
                      let i79 ← Zig.callM (Zig.load (Bool) 1 (i48.elem 1 (3 : BitVec 64)))
                      let i80 ← pure (if i79 then 1 else 0 : BitVec 1)
                      let i81 ← Zig.intCast false false 8 i80
                      let i82 ← pure (Zig.shl i81 (3 : BitVec 3))
                      let i83 ← pure (i78 ||| i82)
                      modify (fun s => { s with r := i83 })
                      pure .br77) : Zig.MM boolLaneLocals boolLaneExit) with
                    | .br77 => (do
                      match ← ((do
                        let i87 ← pure ((← get).r)
                        let i88 ← Zig.callM (Zig.load (Bool) 1 (i48.elem 1 (4 : BitVec 64)))
                        let i89 ← pure (if i88 then 1 else 0 : BitVec 1)
                        let i90 ← Zig.intCast false false 8 i89
                        let i91 ← pure (Zig.shl i90 (4 : BitVec 3))
                        let i92 ← pure (i87 ||| i91)
                        modify (fun s => { s with r := i92 })
                        pure .br86) : Zig.MM boolLaneLocals boolLaneExit) with
                      | .br86 => (do
                        let i95 ← pure ((← get).r)
                        pure (.ret i95))
                      | e => pure e)
                    | e => pure e)
                  | e => pure e)
                | e => pure e)
              | e => pure e)
            | e => pure e)
          | e => pure e)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.MM boolLaneLocals boolLaneExit).run' { (default : boolLaneLocals) with v := s1, local46 := s46 }
  Zig.free s1
  Zig.free s46
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure getU3Locals where
  deriving Inhabited

inductive getU3Exit where
  | ret (v : BitVec 3)

def getU3 (p0 : Zig.Ptr) : Zig.MemM (BitVec 3) := do
  let e ← ((do
    let i1 ← Zig.loadLane (BitVec 3) 3 1 15 p0
    pure (.ret i1)) : Zig.MM getU3Locals getU3Exit).run' (default : getU3Locals)
  match e with
  | .ret v => pure v

structure putU3Locals where
  deriving Inhabited

inductive putU3Exit where
  | ret

def putU3 (p0 : Zig.Ptr) (p1 : BitVec 3) : Zig.MemM (Unit) := do
  let e ← ((do
    Zig.storeLane (α := BitVec 3) 3 1 15 p0 p1
    pure .ret) : Zig.MM putU3Locals putU3Exit).run' (default : putU3Locals)
  match e with
  | .ret => pure ()

structure u24LaneLocals where
  v : Zig.Ptr
  local22 : Zig.Ptr
  deriving Inhabited

inductive u24LaneExit where
  | ret (v : BitVec 32)

def u24Lane (p0 : BitVec 32) (p1 : BitVec 32) : Zig.MemM (BitVec 32) := do
  let s2 ← Zig.allocStack 16 16
  let s22 ← Zig.allocStack 12 4
  let e ← ((do
    let i2 ← pure (← get).v
    let i3 ← pure i2
    let i4 ← pure (Zig.trunc 24 p0)
    Zig.storeLane (α := BitVec 24) 9 4 0 i3 i4
    let i6 ← pure i2
    let i7 ← pure (Zig.shr false p0 (8 : BitVec 5))
    let i8 ← pure (Zig.trunc 24 i7)
    Zig.storeLane (α := BitVec 24) 9 4 24 i6 i8
    let i10 ← pure i2
    let i11 ← pure (Zig.addWrap p0 (1 : BitVec 32))
    let i12 ← pure (Zig.trunc 24 i11)
    Zig.storeLane (α := BitVec 24) 9 4 48 i10 i12
    let i14 ← pure i2
    let i15 ← pure (Zig.trunc 24 p1)
    Zig.storeLane (α := BitVec 24) 9 4 24 i14 i15
    let i17 ← Zig.load (Zig.Vec (BitVec 24) 3) 16 i2
    let i18 ← Zig.callR (Zig.vindex i17.lanes (0 : BitVec 64))
    let i19 ← Zig.callR (Zig.vindex i17.lanes (1 : BitVec 64))
    let i20 ← Zig.callR (Zig.vindex i17.lanes (2 : BitVec 64))
    let i21 ← pure (#v[i18, i19, i20] : Vector (BitVec 24) 3)
    let i22 ← pure (← get).local22
    Zig.store (α := Vector (BitVec 24) 3) 4 i22 i21
    let i24 ← pure (i22)
    let i25 ← Zig.callM (Zig.load (BitVec 24) 4 (i24.elem 4 (0 : BitVec 64)))
    let i26 ← Zig.callM (Zig.load (BitVec 24) 4 (i24.elem 4 (2 : BitVec 64)))
    let i27 ← pure (i25 ^^^ i26)
    let i28 ← Zig.callM (Zig.load (BitVec 24) 4 (i24.elem 4 (1 : BitVec 64)))
    let i29 ← pure (Zig.addWrap i27 i28)
    let i30 ← Zig.intCast false false 32 i29
    pure (.ret i30)) : Zig.MM u24LaneLocals u24LaneExit).run' { (default : u24LaneLocals) with v := s2, local22 := s22 }
  Zig.free s2
  Zig.free s22
  match e with
  | .ret v => pure v

structure u3LaneLocals where
  v : Zig.Ptr
  local67 : Zig.Ptr
  r : BitVec 32
  deriving Inhabited

inductive u3LaneExit where
  | ret (v : BitVec 32)
  | br4
  | br9
  | br15
  | br21
  | br27
  | br33
  | br39
  | br45
  | br72
  | br79
  | br87
  | br95
  | br103
  | br111
  | br119
  | br127

def u3Lane (p0 : BitVec 32) (p1 : BitVec 8) : Zig.MemM (BitVec 32) := do
  let s2 ← Zig.allocStack 4 4
  let s67 ← Zig.allocStack 8 1
  let e ← ((do
    let i2 ← pure (← get).v
    Zig.storeUndef (Zig.Vec (BitVec 3) 8) 4 i2
    match ← ((do
      let i5 ← pure i2
      let i6 ← pure (Zig.trunc 3 p0)
      Zig.storeLane (α := BitVec 3) 3 1 0 i5 i6
      pure .br4) : Zig.MM u3LaneLocals u3LaneExit) with
    | .br4 => (do
      match ← ((do
        let i10 ← pure i2
        let i11 ← pure (Zig.shr false p0 (3 : BitVec 5))
        let i12 ← pure (Zig.trunc 3 i11)
        Zig.storeLane (α := BitVec 3) 3 1 3 i10 i12
        pure .br9) : Zig.MM u3LaneLocals u3LaneExit) with
      | .br9 => (do
        match ← ((do
          let i16 ← pure i2
          let i17 ← pure (Zig.shr false p0 (6 : BitVec 5))
          let i18 ← pure (Zig.trunc 3 i17)
          Zig.storeLane (α := BitVec 3) 3 1 6 i16 i18
          pure .br15) : Zig.MM u3LaneLocals u3LaneExit) with
        | .br15 => (do
          match ← ((do
            let i22 ← pure i2
            let i23 ← pure (Zig.shr false p0 (9 : BitVec 5))
            let i24 ← pure (Zig.trunc 3 i23)
            Zig.storeLane (α := BitVec 3) 3 1 9 i22 i24
            pure .br21) : Zig.MM u3LaneLocals u3LaneExit) with
          | .br21 => (do
            match ← ((do
              let i28 ← pure i2
              let i29 ← pure (Zig.shr false p0 (12 : BitVec 5))
              let i30 ← pure (Zig.trunc 3 i29)
              Zig.storeLane (α := BitVec 3) 3 1 12 i28 i30
              pure .br27) : Zig.MM u3LaneLocals u3LaneExit) with
            | .br27 => (do
              match ← ((do
                let i34 ← pure i2
                let i35 ← pure (Zig.shr false p0 (15 : BitVec 5))
                let i36 ← pure (Zig.trunc 3 i35)
                Zig.storeLane (α := BitVec 3) 3 1 15 i34 i36
                pure .br33) : Zig.MM u3LaneLocals u3LaneExit) with
              | .br33 => (do
                match ← ((do
                  let i40 ← pure i2
                  let i41 ← pure (Zig.shr false p0 (18 : BitVec 5))
                  let i42 ← pure (Zig.trunc 3 i41)
                  Zig.storeLane (α := BitVec 3) 3 1 18 i40 i42
                  pure .br39) : Zig.MM u3LaneLocals u3LaneExit) with
                | .br39 => (do
                  match ← ((do
                    let i46 ← pure i2
                    let i47 ← pure (Zig.shr false p0 (21 : BitVec 5))
                    let i48 ← pure (Zig.trunc 3 i47)
                    Zig.storeLane (α := BitVec 3) 3 1 21 i46 i48
                    pure .br45) : Zig.MM u3LaneLocals u3LaneExit) with
                  | .br45 => (do
                    let i51 ← pure i2
                    let i52 ← pure (Zig.trunc 3 p1)
                    let _i53 ← Zig.callM (putU3 i51 i52)
                    let i54 ← pure i2
                    let i55 ← Zig.callM (getU3 i54)
                    let i56 ← Zig.intCast false false 32 i55
                    let i57 ← Zig.load (Zig.Vec (BitVec 3) 8) 4 i2
                    let i58 ← Zig.callR (Zig.vindex i57.lanes (0 : BitVec 64))
                    let i59 ← Zig.callR (Zig.vindex i57.lanes (1 : BitVec 64))
                    let i60 ← Zig.callR (Zig.vindex i57.lanes (2 : BitVec 64))
                    let i61 ← Zig.callR (Zig.vindex i57.lanes (3 : BitVec 64))
                    let i62 ← Zig.callR (Zig.vindex i57.lanes (4 : BitVec 64))
                    let i63 ← Zig.callR (Zig.vindex i57.lanes (5 : BitVec 64))
                    let i64 ← Zig.callR (Zig.vindex i57.lanes (6 : BitVec 64))
                    let i65 ← Zig.callR (Zig.vindex i57.lanes (7 : BitVec 64))
                    let i66 ← pure (#v[i58, i59, i60, i61, i62, i63, i64, i65] : Vector (BitVec 3) 8)
                    let i67 ← pure (← get).local67
                    Zig.store (α := Vector (BitVec 3) 8) 1 i67 i66
                    let i69 ← pure (i67)
                    modify (fun s => { s with r := (0 : BitVec 32) })
                    match ← ((do
                      let i73 ← pure ((← get).r)
                      let i74 ← Zig.callM (Zig.load (BitVec 3) 1 (i69.elem 1 (0 : BitVec 64)))
                      let i75 ← Zig.intCast false false 32 i74
                      let i76 ← pure (i73 ||| i75)
                      modify (fun s => { s with r := i76 })
                      pure .br72) : Zig.MM u3LaneLocals u3LaneExit) with
                    | .br72 => (do
                      match ← ((do
                        let i80 ← pure ((← get).r)
                        let i81 ← Zig.callM (Zig.load (BitVec 3) 1 (i69.elem 1 (1 : BitVec 64)))
                        let i82 ← Zig.intCast false false 32 i81
                        let i83 ← pure (Zig.shl i82 (3 : BitVec 5))
                        let i84 ← pure (i80 ||| i83)
                        modify (fun s => { s with r := i84 })
                        pure .br79) : Zig.MM u3LaneLocals u3LaneExit) with
                      | .br79 => (do
                        match ← ((do
                          let i88 ← pure ((← get).r)
                          let i89 ← Zig.callM (Zig.load (BitVec 3) 1 (i69.elem 1 (2 : BitVec 64)))
                          let i90 ← Zig.intCast false false 32 i89
                          let i91 ← pure (Zig.shl i90 (6 : BitVec 5))
                          let i92 ← pure (i88 ||| i91)
                          modify (fun s => { s with r := i92 })
                          pure .br87) : Zig.MM u3LaneLocals u3LaneExit) with
                        | .br87 => (do
                          match ← ((do
                            let i96 ← pure ((← get).r)
                            let i97 ← Zig.callM (Zig.load (BitVec 3) 1 (i69.elem 1 (3 : BitVec 64)))
                            let i98 ← Zig.intCast false false 32 i97
                            let i99 ← pure (Zig.shl i98 (9 : BitVec 5))
                            let i100 ← pure (i96 ||| i99)
                            modify (fun s => { s with r := i100 })
                            pure .br95) : Zig.MM u3LaneLocals u3LaneExit) with
                          | .br95 => (do
                            match ← ((do
                              let i104 ← pure ((← get).r)
                              let i105 ← Zig.callM (Zig.load (BitVec 3) 1 (i69.elem 1 (4 : BitVec 64)))
                              let i106 ← Zig.intCast false false 32 i105
                              let i107 ← pure (Zig.shl i106 (12 : BitVec 5))
                              let i108 ← pure (i104 ||| i107)
                              modify (fun s => { s with r := i108 })
                              pure .br103) : Zig.MM u3LaneLocals u3LaneExit) with
                            | .br103 => (do
                              match ← ((do
                                let i112 ← pure ((← get).r)
                                let i113 ← Zig.callM (Zig.load (BitVec 3) 1 (i69.elem 1 (5 : BitVec 64)))
                                let i114 ← Zig.intCast false false 32 i113
                                let i115 ← pure (Zig.shl i114 (15 : BitVec 5))
                                let i116 ← pure (i112 ||| i115)
                                modify (fun s => { s with r := i116 })
                                pure .br111) : Zig.MM u3LaneLocals u3LaneExit) with
                              | .br111 => (do
                                match ← ((do
                                  let i120 ← pure ((← get).r)
                                  let i121 ← Zig.callM (Zig.load (BitVec 3) 1 (i69.elem 1 (6 : BitVec 64)))
                                  let i122 ← Zig.intCast false false 32 i121
                                  let i123 ← pure (Zig.shl i122 (18 : BitVec 5))
                                  let i124 ← pure (i120 ||| i123)
                                  modify (fun s => { s with r := i124 })
                                  pure .br119) : Zig.MM u3LaneLocals u3LaneExit) with
                                | .br119 => (do
                                  match ← ((do
                                    let i128 ← pure ((← get).r)
                                    let i129 ← Zig.callM (Zig.load (BitVec 3) 1 (i69.elem 1 (7 : BitVec 64)))
                                    let i130 ← Zig.intCast false false 32 i129
                                    let i131 ← pure (Zig.shl i130 (21 : BitVec 5))
                                    let i132 ← pure (i128 ||| i131)
                                    modify (fun s => { s with r := i132 })
                                    pure .br127) : Zig.MM u3LaneLocals u3LaneExit) with
                                  | .br127 => (do
                                    let i135 ← pure ((← get).r)
                                    let i136 ← pure (Zig.shl i56 (24 : BitVec 5))
                                    let i137 ← pure (i135 ||| i136)
                                    pure (.ret i137))
                                  | e => pure e)
                                | e => pure e)
                              | e => pure e)
                            | e => pure e)
                          | e => pure e)
                        | e => pure e)
                      | e => pure e)
                    | e => pure e)
                  | e => pure e)
                | e => pure e)
              | e => pure e)
            | e => pure e)
          | e => pure e)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.MM u3LaneLocals u3LaneExit).run' { (default : u3LaneLocals) with v := s2, local67 := s67 }
  Zig.free s2
  Zig.free s67
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure u9LaneLocals where
  v : Zig.Ptr
  local27 : Zig.Ptr
  deriving Inhabited

inductive u9LaneExit where
  | ret (v : BitVec 64)

def u9Lane (p0 : BitVec 16) (p1 : BitVec 16) (p2 : BitVec 16) : Zig.MemM (BitVec 64) := do
  let s3 ← Zig.allocStack 8 8
  let s27 ← Zig.allocStack 8 2
  let e ← ((do
    let i3 ← pure (← get).v
    let i4 ← pure i3
    let i5 ← pure (Zig.trunc 9 p0)
    Zig.storeLane (α := BitVec 9) 5 2 0 i4 i5
    let i7 ← pure i3
    let i8 ← pure (Zig.trunc 9 p1)
    Zig.storeLane (α := BitVec 9) 5 2 9 i7 i8
    let i10 ← pure i3
    let i11 ← pure (Zig.trunc 9 p0)
    Zig.storeLane (α := BitVec 9) 5 2 18 i10 i11
    let i13 ← pure i3
    let i14 ← pure (Zig.trunc 9 p1)
    Zig.storeLane (α := BitVec 9) 5 2 27 i13 i14
    let i16 ← pure i3
    let i17 ← pure (Zig.trunc 9 p2)
    Zig.storeLane (α := BitVec 9) 5 2 18 i16 i17
    let i19 ← Zig.loadLane (BitVec 9) 5 2 18 i16
    let i20 ← Zig.intCast false false 64 i19
    let i21 ← Zig.load (Zig.Vec (BitVec 9) 4) 8 i3
    let i22 ← Zig.callR (Zig.vindex i21.lanes (0 : BitVec 64))
    let i23 ← Zig.callR (Zig.vindex i21.lanes (1 : BitVec 64))
    let i24 ← Zig.callR (Zig.vindex i21.lanes (2 : BitVec 64))
    let i25 ← Zig.callR (Zig.vindex i21.lanes (3 : BitVec 64))
    let i26 ← pure (#v[i22, i23, i24, i25] : Vector (BitVec 9) 4)
    let i27 ← pure (← get).local27
    Zig.store (α := Vector (BitVec 9) 4) 2 i27 i26
    let i29 ← pure (i27)
    let i30 ← Zig.callM (Zig.load (BitVec 9) 2 (i29.elem 2 (0 : BitVec 64)))
    let i31 ← Zig.intCast false false 64 i30
    let i32 ← Zig.callM (Zig.load (BitVec 9) 2 (i29.elem 2 (1 : BitVec 64)))
    let i33 ← Zig.intCast false false 64 i32
    let i34 ← pure (Zig.shl i33 (9 : BitVec 6))
    let i35 ← pure (i31 ||| i34)
    let i36 ← Zig.callM (Zig.load (BitVec 9) 2 (i29.elem 2 (2 : BitVec 64)))
    let i37 ← Zig.intCast false false 64 i36
    let i38 ← pure (Zig.shl i37 (18 : BitVec 6))
    let i39 ← pure (i35 ||| i38)
    let i40 ← Zig.callM (Zig.load (BitVec 9) 2 (i29.elem 2 (3 : BitVec 64)))
    let i41 ← Zig.intCast false false 64 i40
    let i42 ← pure (Zig.shl i41 (27 : BitVec 6))
    let i43 ← pure (i39 ||| i42)
    let i44 ← pure (Zig.shl i20 (36 : BitVec 6))
    let i45 ← pure (i43 ||| i44)
    pure (.ret i45)) : Zig.MM u9LaneLocals u9LaneExit).run' { (default : u9LaneLocals) with v := s3, local27 := s27 }
  Zig.free s3
  Zig.free s27
  match e with
  | .ret v => pure v

end Lanes