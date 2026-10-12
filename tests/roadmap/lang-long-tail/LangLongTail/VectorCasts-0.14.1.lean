-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.4.19...6.13.4-musl","zig_version":"0.14.1"}}
import ZigLean


namespace VectorCasts

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ [
  -- 0: a constant
  (Zig.Enc.encode ((#v[] : Vector (BitVec 8) 0) : Vector (BitVec 8) 0), 1, .constGlobal)]

structure mem_eqlBytesLocals where
  x : BitVec 32
  local101 : BitVec 64
  local172 : BitVec 64
  deriving Inhabited

inductive mem_eqlBytesExit where
  | ret (v : Bool)
  | br2
  | br15 (v : Bool)
  | br11
  | br37
  | br45
  | br56
  | br66
  | br78
  | br88
  | br30
  | br130
  | br143
  | br118
  | br115
  | br25
  | br162
  | br164
  | br166
  | br168
  | br170
  | br192
  | br206
  | br214 (v : Bool)
  | br213
  | br180
  | br177
  | br234
  | br249
  | br256 (v : Bool)
  | rep116
  | rep178

def mem_eqlBytes.again178 : mem_eqlBytesExit → Bool
  | .rep178 => true
  | _ => false

def mem_eqlBytes.again116 : mem_eqlBytesExit → Bool
  | .rep116 => true
  | _ => false

def mem_eqlBytes.loop178 (p0 : Zig.Slice) (p1 : Zig.Slice) (i176 : BitVec 64) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit := do
  let i179 ← pure ((← get).local172)
  match ← ((do
    let i181 ← pure (i179)
    let i182 ← pure (i176)
    let i183 ← pure (Zig.lt false i181 i182)
    if i183 then (do
      let i185 ← Zig.mul false i179 (16 : BitVec 64)
      let i186 ← pure p0.ptr
      let i187 ← Zig.callM (Zig.ptrProject i186 (·.elem 1 i185))
      let i188 ← Zig.add false i185 (16 : BitVec 64)
      let i189 ← pure (i187)
      let i190 ← pure p0.len
      let i191 ← pure (Zig.le false i188 i190)
      match ← ((do
        if i191 then (do
          pure .br192)
        else (do
          throw .outOfBounds)) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
      | .br192 => (do
        let i197 ← Zig.load (Vector (BitVec 8) 16) 1 i189
        let i198 ← pure (⟨i197⟩ : Zig.Vec (BitVec 8) 16)
        let i199 ← Zig.mul false i179 (16 : BitVec 64)
        let i200 ← pure p1.ptr
        let i201 ← Zig.callM (Zig.ptrProject i200 (·.elem 1 i199))
        let i202 ← Zig.add false i199 (16 : BitVec 64)
        let i203 ← pure (i201)
        let i204 ← pure p1.len
        let i205 ← pure (Zig.le false i202 i204)
        match ← ((do
          if i205 then (do
            pure .br206)
          else (do
            throw .outOfBounds)) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
        | .br206 => (do
          let i211 ← Zig.load (Vector (BitVec 8) 16) 1 i203
          let i212 ← pure (⟨i211⟩ : Zig.Vec (BitVec 8) 16)
          match ← ((do
            match ← ((do
              let i215 ← Zig.Vec.map2M (fun x0 x1 => pure (x0 != x1)) i198 i212
              let i216 ← pure (Zig.Vec.reduce (· || ·) i215)
              pure (.br214 i216)) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
            | .br214 v214 => (do
              if v214 then (do
                pure (.ret false))
              else (do
                pure .br213))
            | e => pure e) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
          | .br213 => (do
            pure .br180)
          | e => pure e)
        | e => pure e)
      | e => pure e)
    else (do
      pure .br177)) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
  | .br180 => (do
    let i223 ← Zig.add false i179 (1 : BitVec 64)
    modify (fun s => { s with local172 := i223 })
    pure .rep178)
  | e => pure e

def mem_eqlBytes.loop116 (p0 : Zig.Slice) (p1 : Zig.Slice) (i114 : Vector (BitVec 64) 4) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit := do
  let i117 ← pure ((← get).local101)
  match ← ((do
    let i119 ← pure (i117)
    let i120 ← pure (Zig.lt false i119 (4 : BitVec 64))
    if i120 then (do
      let i122 ← Zig.callR (Zig.vindex i114 i117)
      let i123 ← pure ((← get).x)
      let i124 ← pure p0.ptr
      let i125 ← Zig.callM (Zig.ptrProject i124 (·.elem 1 i122))
      let i126 ← Zig.add false i122 (4 : BitVec 64)
      let i127 ← pure (i125)
      let i128 ← pure p0.len
      let i129 ← pure (Zig.le false i126 i128)
      match ← ((do
        if i129 then (do
          pure .br130)
        else (do
          throw .outOfBounds)) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
      | .br130 => (do
        let i135 ← Zig.load (Vector (BitVec 8) 4) 1 i127
        let i136 ← Zig.reprCast (BitVec 32) (i135 : Vector (BitVec 8) 4)
        let i137 ← pure p1.ptr
        let i138 ← Zig.callM (Zig.ptrProject i137 (·.elem 1 i122))
        let i139 ← Zig.add false i122 (4 : BitVec 64)
        let i140 ← pure (i138)
        let i141 ← pure p1.len
        let i142 ← pure (Zig.le false i139 i141)
        match ← ((do
          if i142 then (do
            pure .br143)
          else (do
            throw .outOfBounds)) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
        | .br143 => (do
          let i148 ← Zig.load (Vector (BitVec 8) 4) 1 i140
          let i149 ← Zig.reprCast (BitVec 32) (i148 : Vector (BitVec 8) 4)
          let i150 ← pure (i136 ^^^ i149)
          let i151 ← pure (i123 ||| i150)
          modify (fun s => { s with x := i151 })
          pure .br118)
        | e => pure e)
      | e => pure e)
    else (do
      pure .br115)) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
  | .br118 => (do
    let i155 ← Zig.add false i117 (1 : BitVec 64)
    modify (fun s => { s with local101 := i155 })
    pure .rep116)
  | e => pure e

def mem_eqlBytes (p0 : Zig.Slice) (p1 : Zig.Slice) : Zig.MemM (Bool) := do
  let e ← ((do
    match ← ((do
      let i3 ← pure p0.len
      let i4 ← pure p1.len
      let i5 ← pure (i3)
      let i6 ← pure (i4)
      let i7 ← pure (i5 != i6)
      if i7 then (do
        pure (.ret false))
      else (do
        pure .br2)) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
    | .br2 => (do
      match ← ((do
        let i12 ← pure p0.len
        let i13 ← pure (i12)
        let i14 ← pure (i13 == (0 : BitVec 64))
        match ← ((do
          if i14 then (do
            pure (.br15 true))
          else (do
            let i18 ← pure p0.ptr
            let i19 ← pure p1.ptr
            let i20 ← Zig.callM (Zig.ptrEqAddr i18 i19)
            pure (.br15 i20))) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
        | .br15 v15 => (do
          if v15 then (do
            pure (.ret true))
          else (do
            pure .br11))
        | e => pure e) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
      | .br11 => (do
        match ← ((do
          let i26 ← pure p0.len
          let i27 ← pure (i26)
          let i28 ← pure (Zig.le false i27 (16 : BitVec 64))
          if i28 then (do
            match ← ((do
              let i31 ← pure p0.len
              let i32 ← pure (i31)
              let i33 ← pure (Zig.lt false i32 (4 : BitVec 64))
              if i33 then (do
                let i35 ← pure p0.len
                let i36 ← pure (Zig.lt false (0 : BitVec 64) i35)
                match ← ((do
                  if i36 then (do
                    pure .br37)
                  else (do
                    throw .outOfBounds)) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
                | .br37 => (do
                  let i42 ← Zig.callM (Zig.checkIndex p0.len (0 : BitVec 64) >>= fun _ => Zig.load (BitVec 8) 1 (p0.ptr.elem 1 (0 : BitVec 64)))
                  let i43 ← pure p1.len
                  let i44 ← pure (Zig.lt false (0 : BitVec 64) i43)
                  match ← ((do
                    if i44 then (do
                      pure .br45)
                    else (do
                      throw .outOfBounds)) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
                  | .br45 => (do
                    let i50 ← Zig.callM (Zig.checkIndex p1.len (0 : BitVec 64) >>= fun _ => Zig.load (BitVec 8) 1 (p1.ptr.elem 1 (0 : BitVec 64)))
                    let i51 ← pure (i42 ^^^ i50)
                    let i52 ← pure p0.len
                    let i53 ← Zig.sub false i52 (1 : BitVec 64)
                    let i54 ← pure p0.len
                    let i55 ← pure (Zig.lt false i53 i54)
                    match ← ((do
                      if i55 then (do
                        pure .br56)
                      else (do
                        throw .outOfBounds)) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
                    | .br56 => (do
                      let i61 ← Zig.callM (Zig.checkIndex p0.len i53 >>= fun _ => Zig.load (BitVec 8) 1 (p0.ptr.elem 1 i53))
                      let i62 ← pure p0.len
                      let i63 ← Zig.sub false i62 (1 : BitVec 64)
                      let i64 ← pure p1.len
                      let i65 ← pure (Zig.lt false i63 i64)
                      match ← ((do
                        if i65 then (do
                          pure .br66)
                        else (do
                          throw .outOfBounds)) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
                      | .br66 => (do
                        let i71 ← Zig.callM (Zig.checkIndex p1.len i63 >>= fun _ => Zig.load (BitVec 8) 1 (p1.ptr.elem 1 i63))
                        let i72 ← pure (i61 ^^^ i71)
                        let i73 ← pure (i51 ||| i72)
                        let i74 ← pure p0.len
                        let i75 ← Zig.divTrunc false i74 (2 : BitVec 64)
                        let i76 ← pure p0.len
                        let i77 ← pure (Zig.lt false i75 i76)
                        match ← ((do
                          if i77 then (do
                            pure .br78)
                          else (do
                            throw .outOfBounds)) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
                        | .br78 => (do
                          let i83 ← Zig.callM (Zig.checkIndex p0.len i75 >>= fun _ => Zig.load (BitVec 8) 1 (p0.ptr.elem 1 i75))
                          let i84 ← pure p0.len
                          let i85 ← Zig.divTrunc false i84 (2 : BitVec 64)
                          let i86 ← pure p1.len
                          let i87 ← pure (Zig.lt false i85 i86)
                          match ← ((do
                            if i87 then (do
                              pure .br88)
                            else (do
                              throw .outOfBounds)) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
                          | .br88 => (do
                            let i93 ← Zig.callM (Zig.checkIndex p1.len i85 >>= fun _ => Zig.load (BitVec 8) 1 (p1.ptr.elem 1 i85))
                            let i94 ← pure (i83 ^^^ i93)
                            let i95 ← pure (i73 ||| i94)
                            let i96 ← pure (i95 == (0 : BitVec 8))
                            pure (.ret i96))
                          | e => pure e)
                        | e => pure e)
                      | e => pure e)
                    | e => pure e)
                  | e => pure e)
                | e => pure e)
              else (do
                pure .br30)) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
            | .br30 => (do
              modify (fun s => { s with x := (0 : BitVec 32) })
              modify (fun s => { s with local101 := (0 : BitVec 64) })
              let i103 ← pure p0.len
              let i104 ← Zig.sub false i103 (4 : BitVec 64)
              let i105 ← pure p0.len
              let i106 ← Zig.divTrunc false i105 (8 : BitVec 64)
              let i107 ← Zig.mul false i106 (4 : BitVec 64)
              let i108 ← pure p0.len
              let i109 ← Zig.sub false i108 (4 : BitVec 64)
              let i110 ← pure p0.len
              let i111 ← Zig.divTrunc false i110 (8 : BitVec 64)
              let i112 ← Zig.mul false i111 (4 : BitVec 64)
              let i113 ← Zig.sub false i109 i112
              let i114 ← pure (#v[(0 : BitVec 64), i104, i107, i113] : Vector (BitVec 64) 4)
              match ← ((do
                Zig.loop (mem_eqlBytes.loop116 p0 p1 i114) mem_eqlBytes.again116) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
              | .br115 => (do
                let i158 ← pure ((← get).x)
                let i159 ← pure (i158 == (0 : BitVec 32))
                pure (.ret i159))
              | e => pure e)
            | e => pure e)
          else (do
            pure .br25)) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
        | .br25 => (do
          match ← ((do
            pure .br162) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
          | .br162 => (do
            match ← ((do
              pure .br164) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
            | .br164 => (do
              match ← ((do
                pure .br166) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
              | .br166 => (do
                match ← ((do
                  pure .br168) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
                | .br168 => (do
                  match ← ((do
                    pure .br170) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
                  | .br170 => (do
                    modify (fun s => { s with local172 := (0 : BitVec 64) })
                    let i174 ← pure p0.len
                    let i175 ← Zig.sub false i174 (1 : BitVec 64)
                    let i176 ← Zig.divTrunc false i175 (16 : BitVec 64)
                    match ← ((do
                      Zig.loop (mem_eqlBytes.loop178 p0 p1 i176) mem_eqlBytes.again178) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
                    | .br177 => (do
                      let i226 ← pure p0.len
                      let i227 ← Zig.sub false i226 (16 : BitVec 64)
                      let i228 ← pure p0.ptr
                      let i229 ← Zig.callM (Zig.ptrProject i228 (·.elem 1 i227))
                      let i230 ← Zig.add false i227 (16 : BitVec 64)
                      let i231 ← pure (i229)
                      let i232 ← pure p0.len
                      let i233 ← pure (Zig.le false i230 i232)
                      match ← ((do
                        if i233 then (do
                          pure .br234)
                        else (do
                          throw .outOfBounds)) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
                      | .br234 => (do
                        let i239 ← Zig.load (Vector (BitVec 8) 16) 1 i231
                        let i240 ← pure (⟨i239⟩ : Zig.Vec (BitVec 8) 16)
                        let i241 ← pure p0.len
                        let i242 ← Zig.sub false i241 (16 : BitVec 64)
                        let i243 ← pure p1.ptr
                        let i244 ← Zig.callM (Zig.ptrProject i243 (·.elem 1 i242))
                        let i245 ← Zig.add false i242 (16 : BitVec 64)
                        let i246 ← pure (i244)
                        let i247 ← pure p1.len
                        let i248 ← pure (Zig.le false i245 i247)
                        match ← ((do
                          if i248 then (do
                            pure .br249)
                          else (do
                            throw .outOfBounds)) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
                        | .br249 => (do
                          let i254 ← Zig.load (Vector (BitVec 8) 16) 1 i246
                          let i255 ← pure (⟨i254⟩ : Zig.Vec (BitVec 8) 16)
                          match ← ((do
                            let i257 ← Zig.Vec.map2M (fun x0 x1 => pure (x0 != x1)) i240 i255
                            let i258 ← pure (Zig.Vec.reduce (· || ·) i257)
                            pure (.br256 i258)) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
                          | .br256 v256 => (do
                            let i260 ← pure (!v256)
                            pure (.ret i260))
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
    | e => pure e) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit).run' (default : mem_eqlBytesLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mem_sliceAsBytes__anon_ea9612f03fedLocals where
  deriving Inhabited

inductive mem_sliceAsBytes__anon_ea9612f03fedExit where
  | ret (v : Zig.Slice)
  | br8
  | br7
  | br5 (v : Bool)
  | br1

def mem_sliceAsBytes__anon_ea9612f03fed (p0 : Zig.Slice) : Zig.MemM (Zig.Slice) := do
  let e ← ((do
    match ← ((do
      let i2 ← pure p0.len
      let i3 ← pure (i2)
      let i4 ← pure (i3 == (0 : BitVec 64))
      match ← ((do
        if i4 then (do
          match ← ((do
            match ← ((do
              pure .br8) : Zig.MM mem_sliceAsBytes__anon_ea9612f03fedLocals mem_sliceAsBytes__anon_ea9612f03fedExit) with
            | .br8 => (do
              pure .br7)
            | e => pure e) : Zig.MM mem_sliceAsBytes__anon_ea9612f03fedLocals mem_sliceAsBytes__anon_ea9612f03fedExit) with
          | .br7 => (do
            pure (.br5 true))
          | e => pure e)
        else (do
          pure (.br5 false))) : Zig.MM mem_sliceAsBytes__anon_ea9612f03fedLocals mem_sliceAsBytes__anon_ea9612f03fedExit) with
      | .br5 v5 => (do
        if v5 then (do
          pure (.ret (⟨(⟨some 0, 0⟩ : Zig.Ptr), (0 : BitVec 64)⟩ : Zig.Slice)))
        else (do
          pure .br1))
      | e => pure e) : Zig.MM mem_sliceAsBytes__anon_ea9612f03fedLocals mem_sliceAsBytes__anon_ea9612f03fedExit) with
    | .br1 => (do
      let i16 ← pure p0.ptr
      let i17 ← pure p0.len
      let i18 ← pure i16
      let i19 ← Zig.callM (Zig.checkSliceEnd p0.len (0 : BitVec 64) i17 0 >>= fun _ => pure (⟨i18, i17⟩ : Zig.Slice))
      pure (.ret i19))
    | e => pure e) : Zig.MM mem_sliceAsBytes__anon_ea9612f03fedLocals mem_sliceAsBytes__anon_ea9612f03fedExit).run' (default : mem_sliceAsBytes__anon_ea9612f03fedLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure mem_eql__anon_f1fdef28237dLocals where
  deriving Inhabited

inductive mem_eql__anon_f1fdef28237dExit where
  | ret (v : Bool)
  | br3
  | br2

def mem_eql__anon_f1fdef28237d (p0 : Zig.Slice) (p1 : Zig.Slice) : Zig.MemM (Bool) := do
  let e ← ((do
    match ← ((do
      match ← ((do
        pure .br3) : Zig.MM mem_eql__anon_f1fdef28237dLocals mem_eql__anon_f1fdef28237dExit) with
      | .br3 => (do
        pure .br2)
      | e => pure e) : Zig.MM mem_eql__anon_f1fdef28237dLocals mem_eql__anon_f1fdef28237dExit) with
    | .br2 => (do
      let i6 ← Zig.callM (mem_sliceAsBytes__anon_ea9612f03fed p0)
      let i7 ← Zig.callM (mem_sliceAsBytes__anon_ea9612f03fed p1)
      let i8 ← Zig.callM (mem_eqlBytes i6 i7)
      pure (.ret i8))
    | e => pure e) : Zig.MM mem_eql__anon_f1fdef28237dLocals mem_eql__anon_f1fdef28237dExit).run' (default : mem_eql__anon_f1fdef28237dLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure boolItemToLaneLocals where
  deriving Inhabited

inductive boolItemToLaneExit where
  | ret (v : Zig.Vec (Bool) 1)

def boolItemToLane (p0 : Vector (Bool) 1) : Zig.Result (Zig.Vec (Bool) 1) := do
  let e ← ((do
    let i1 ← pure (⟨p0⟩ : Zig.Vec (Bool) 1)
    pure (.ret i1)) : Zig.M boolItemToLaneLocals boolItemToLaneExit).run' (default : boolItemToLaneLocals)
  match e with
  | .ret v => pure v

structure boolLanesToByteLocals where
  deriving Inhabited

inductive boolLanesToByteExit where
  | ret (v : BitVec 8)

def boolLanesToByte (p0 : Zig.Vec (Bool) 8) : Zig.Result (BitVec 8) := do
  let e ← ((do
    let i1 ← Zig.reprCast (BitVec 8) (p0 : Zig.Vec (Bool) 8)
    pure (.ret i1)) : Zig.M boolLanesToByteLocals boolLanesToByteExit).run' (default : boolLanesToByteLocals)
  match e with
  | .ret v => pure v

structure bytesToHalvesLocals where
  deriving Inhabited

inductive bytesToHalvesExit where
  | ret (v : Zig.Vec (BitVec 16) 2)

def bytesToHalves (p0 : Vector (BitVec 8) 4) : Zig.Result (Zig.Vec (BitVec 16) 2) := do
  let e ← ((do
    let i1 ← Zig.reprCast (Zig.Vec (BitVec 16) 2) (p0 : Vector (BitVec 8) 4)
    pure (.ret i1)) : Zig.M bytesToHalvesLocals bytesToHalvesExit).run' (default : bytesToHalvesLocals)
  match e with
  | .ret v => pure v

structure bytesToLanesLocals where
  deriving Inhabited

inductive bytesToLanesExit where
  | ret (v : Zig.Vec (BitVec 8) 4)

def bytesToLanes (p0 : Vector (BitVec 8) 4) : Zig.Result (Zig.Vec (BitVec 8) 4) := do
  let e ← ((do
    let i1 ← pure (⟨p0⟩ : Zig.Vec (BitVec 8) 4)
    pure (.ret i1)) : Zig.M bytesToLanesLocals bytesToLanesExit).run' (default : bytesToLanesLocals)
  match e with
  | .ret v => pure v

structure eqlChunkLocals where
  deriving Inhabited

inductive eqlChunkExit where
  | ret (v : Bool)

def eqlChunk (p0 : Vector (BitVec 8) 16) (p1 : Vector (BitVec 8) 16) : Zig.Result (Bool) := do
  let e ← ((do
    let i2 ← pure (⟨p0⟩ : Zig.Vec (BitVec 8) 16)
    let i3 ← pure (⟨p1⟩ : Zig.Vec (BitVec 8) 16)
    let i4 ← Zig.Vec.map2M (fun x0 x1 => pure (x0 != x1)) i2 i3
    let i5 ← pure (Zig.Vec.reduce (· || ·) i4)
    let i6 ← pure (!i5)
    pure (.ret i6)) : Zig.M eqlChunkLocals eqlChunkExit).run' (default : eqlChunkLocals)
  match e with
  | .ret v => pure v

structure halvesToBytesLocals where
  deriving Inhabited

inductive halvesToBytesExit where
  | ret (v : Vector (BitVec 8) 4)

def halvesToBytes (p0 : Zig.Vec (BitVec 16) 2) : Zig.Result (Vector (BitVec 8) 4) := do
  let e ← ((do
    let i1 ← Zig.reprCast (Vector (BitVec 8) 4) (p0 : Zig.Vec (BitVec 16) 2)
    pure (.ret i1)) : Zig.M halvesToBytesLocals halvesToBytesExit).run' (default : halvesToBytesLocals)
  match e with
  | .ret v => pure v

structure intToPackedLanesLocals where
  deriving Inhabited

inductive intToPackedLanesExit where
  | ret (v : Zig.Vec (BitVec 3) 3)

def intToPackedLanes (p0 : BitVec 9) : Zig.Result (Zig.Vec (BitVec 3) 3) := do
  let e ← ((do
    let i1 ← Zig.reprCast (Zig.Vec (BitVec 3) 3) (p0 : BitVec 9)
    pure (.ret i1)) : Zig.M intToPackedLanesLocals intToPackedLanesExit).run' (default : intToPackedLanesLocals)
  match e with
  | .ret v => pure v

structure lanesToBytesLocals where
  deriving Inhabited

inductive lanesToBytesExit where
  | ret (v : Vector (BitVec 8) 4)

def lanesToBytes (p0 : Zig.Vec (BitVec 8) 4) : Zig.Result (Vector (BitVec 8) 4) := do
  let e ← ((do
    let i1 ← pure (p0 : Zig.Vec (BitVec 8) 4).lanes
    pure (.ret i1)) : Zig.M lanesToBytesLocals lanesToBytesExit).run' (default : lanesToBytesLocals)
  match e with
  | .ret v => pure v

structure lanesToWordLocals where
  deriving Inhabited

inductive lanesToWordExit where
  | ret (v : BitVec 32)

def lanesToWord (p0 : Zig.Vec (BitVec 8) 4) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← Zig.reprCast (BitVec 32) (p0 : Zig.Vec (BitVec 8) 4)
    pure (.ret i1)) : Zig.M lanesToWordLocals lanesToWordExit).run' (default : lanesToWordLocals)
  match e with
  | .ret v => pure v

structure packedLanesToIntLocals where
  deriving Inhabited

inductive packedLanesToIntExit where
  | ret (v : BitVec 9)

def packedLanesToInt (p0 : Zig.Vec (BitVec 3) 3) : Zig.Result (BitVec 9) := do
  let e ← ((do
    let i1 ← Zig.reprCast (BitVec 9) (p0 : Zig.Vec (BitVec 3) 3)
    pure (.ret i1)) : Zig.M packedLanesToIntLocals packedLanesToIntExit).run' (default : packedLanesToIntLocals)
  match e with
  | .ret v => pure v

structure stdEqlLocals where
  deriving Inhabited

inductive stdEqlExit where
  | ret (v : Bool)

def stdEql (p0 : Zig.Ptr) (p1 : Zig.Ptr) : Zig.MemM (Bool) := do
  let e ← ((do
    let i2 ← pure (⟨p0, (40 : BitVec 64)⟩ : Zig.Slice)
    let i3 ← pure (⟨p1, (40 : BitVec 64)⟩ : Zig.Slice)
    let i4 ← Zig.callM (mem_eql__anon_f1fdef28237d i2 i3)
    pure (.ret i4)) : Zig.MM stdEqlLocals stdEqlExit).run' (default : stdEqlLocals)
  match e with
  | .ret v => pure v

structure u24ItemToLaneLocals where
  deriving Inhabited

inductive u24ItemToLaneExit where
  | ret (v : Zig.Vec (BitVec 24) 1)

def u24ItemToLane (p0 : Vector (BitVec 24) 1) : Zig.Result (Zig.Vec (BitVec 24) 1) := do
  let e ← ((do
    let i1 ← pure (⟨p0⟩ : Zig.Vec (BitVec 24) 1)
    pure (.ret i1)) : Zig.M u24ItemToLaneLocals u24ItemToLaneExit).run' (default : u24ItemToLaneLocals)
  match e with
  | .ret v => pure v

structure u24LaneToItemLocals where
  deriving Inhabited

inductive u24LaneToItemExit where
  | ret (v : Vector (BitVec 24) 1)

def u24LaneToItem (p0 : Zig.Vec (BitVec 24) 1) : Zig.Result (Vector (BitVec 24) 1) := do
  let e ← ((do
    let i1 ← pure (p0 : Zig.Vec (BitVec 24) 1).lanes
    pure (.ret i1)) : Zig.M u24LaneToItemLocals u24LaneToItemExit).run' (default : u24LaneToItemLocals)
  match e with
  | .ret v => pure v

structure wordToLanesLocals where
  deriving Inhabited

inductive wordToLanesExit where
  | ret (v : Zig.Vec (BitVec 8) 4)

def wordToLanes (p0 : BitVec 32) : Zig.Result (Zig.Vec (BitVec 8) 4) := do
  let e ← ((do
    let i1 ← Zig.reprCast (Zig.Vec (BitVec 8) 4) (p0 : BitVec 32)
    pure (.ret i1)) : Zig.M wordToLanesLocals wordToLanesExit).run' (default : wordToLanesLocals)
  match e with
  | .ret v => pure v

end VectorCasts