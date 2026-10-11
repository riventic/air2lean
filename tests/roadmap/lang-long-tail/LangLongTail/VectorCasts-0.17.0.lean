-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...7.2-musl","zig_version":"0.17.0"}}
import ZigLean


namespace VectorCasts

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ [
  -- 0: a constant
  (Zig.Enc.encode ((#v[] : Vector (BitVec 8) 0) : Vector (BitVec 8) 0), 1, .constGlobal)]

structure mem_eqlBytesLocals where
  local2 : Zig.Slice
  local5 : Zig.Slice
  x : BitVec 32
  local124 : BitVec 64
  local201 : BitVec 64
  deriving Inhabited

inductive mem_eqlBytesExit where
  | ret (v : Bool)
  | br8
  | br24 (v : Bool)
  | br19
  | br51
  | br60
  | br73
  | br85
  | br99
  | br111
  | br42
  | br158
  | br172
  | br145
  | br142
  | br36
  | br191
  | br193
  | br195
  | br197
  | br199
  | br223
  | br238
  | br246 (v : Bool)
  | br245
  | br210
  | br207
  | br268
  | br285
  | br292 (v : Bool)
  | rep143
  | rep208

def mem_eqlBytes.again208 : mem_eqlBytesExit → Bool
  | .rep208 => true
  | _ => false

def mem_eqlBytes.again143 : mem_eqlBytesExit → Bool
  | .rep143 => true
  | _ => false

def mem_eqlBytes.loop208 (i206 : BitVec 64) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit := do
  let i209 ← pure ((← get).local201)
  match ← ((do
    let i211 ← pure (i209)
    let i212 ← pure (i206)
    let i213 ← pure (Zig.lt false i211 i212)
    if i213 then (do
      let i215 ← Zig.mul false i209 (16 : BitVec 64)
      let i216 ← pure ((← get).local2)
      let i217 ← pure i216.ptr
      let i218 ← Zig.callM (Zig.ptrProject i217 (·.elem 1 i215))
      let i219 ← Zig.add false i215 (16 : BitVec 64)
      let i220 ← pure (i218)
      let i221 ← pure i216.len
      let i222 ← pure (Zig.le false i219 i221)
      match ← ((do
        if i222 then (do
          pure .br223)
        else (do
          throw .outOfBounds)) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
      | .br223 => (do
        let i228 ← Zig.load (Vector (BitVec 8) 16) 1 i220
        let i229 ← (((pure (Zig.BitCast.ofLanes (i228)) : Zig.Result (BitVec 128)) >>= fun bits => pure ⟨Zig.BitCast.toLanes (n := 16) (w := 8) (bits)⟩) : Zig.Result (Zig.Vec (BitVec 8) 16))
        let i230 ← Zig.mul false i209 (16 : BitVec 64)
        let i231 ← pure ((← get).local5)
        let i232 ← pure i231.ptr
        let i233 ← Zig.callM (Zig.ptrProject i232 (·.elem 1 i230))
        let i234 ← Zig.add false i230 (16 : BitVec 64)
        let i235 ← pure (i233)
        let i236 ← pure i231.len
        let i237 ← pure (Zig.le false i234 i236)
        match ← ((do
          if i237 then (do
            pure .br238)
          else (do
            throw .outOfBounds)) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
        | .br238 => (do
          let i243 ← Zig.load (Vector (BitVec 8) 16) 1 i235
          let i244 ← (((pure (Zig.BitCast.ofLanes (i243)) : Zig.Result (BitVec 128)) >>= fun bits => pure ⟨Zig.BitCast.toLanes (n := 16) (w := 8) (bits)⟩) : Zig.Result (Zig.Vec (BitVec 8) 16))
          match ← ((do
            match ← ((do
              let i247 ← Zig.Vec.map2M (fun x0 x1 => pure (x0 != x1)) i229 i244
              let i248 ← pure (Zig.Vec.reduce (· || ·) i247)
              pure (.br246 i248)) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
            | .br246 v246 => (do
              if v246 then (do
                pure (.ret false))
              else (do
                pure .br245))
            | e => pure e) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
          | .br245 => (do
            pure .br210)
          | e => pure e)
        | e => pure e)
      | e => pure e)
    else (do
      pure .br207)) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
  | .br210 => (do
    let i255 ← Zig.add false i209 (1 : BitVec 64)
    modify (fun s => { s with local201 := i255 })
    pure .rep208)
  | e => pure e

def mem_eqlBytes.loop143 (i141 : Vector (BitVec 64) 4) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit := do
  let i144 ← pure ((← get).local124)
  match ← ((do
    let i146 ← pure (i144)
    let i147 ← pure (Zig.lt false i146 (4 : BitVec 64))
    if i147 then (do
      let i149 ← Zig.callR (Zig.vindex i141 i144)
      let i150 ← pure ((← get).x)
      let i151 ← pure ((← get).local2)
      let i152 ← pure i151.ptr
      let i153 ← Zig.callM (Zig.ptrProject i152 (·.elem 1 i149))
      let i154 ← Zig.add false i149 (4 : BitVec 64)
      let i155 ← pure (i153)
      let i156 ← pure i151.len
      let i157 ← pure (Zig.le false i154 i156)
      match ← ((do
        if i157 then (do
          pure .br158)
        else (do
          throw .outOfBounds)) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
      | .br158 => (do
        let i163 ← Zig.load (Vector (BitVec 8) 4) 1 i155
        let i164 ← (pure (Zig.BitCast.ofLanes (i163)) : Zig.Result (BitVec 32))
        let i165 ← pure ((← get).local5)
        let i166 ← pure i165.ptr
        let i167 ← Zig.callM (Zig.ptrProject i166 (·.elem 1 i149))
        let i168 ← Zig.add false i149 (4 : BitVec 64)
        let i169 ← pure (i167)
        let i170 ← pure i165.len
        let i171 ← pure (Zig.le false i168 i170)
        match ← ((do
          if i171 then (do
            pure .br172)
          else (do
            throw .outOfBounds)) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
        | .br172 => (do
          let i177 ← Zig.load (Vector (BitVec 8) 4) 1 i169
          let i178 ← (pure (Zig.BitCast.ofLanes (i177)) : Zig.Result (BitVec 32))
          let i179 ← pure (i164 ^^^ i178)
          let i180 ← pure (i150 ||| i179)
          modify (fun s => { s with x := i180 })
          pure .br145)
        | e => pure e)
      | e => pure e)
    else (do
      pure .br142)) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
  | .br145 => (do
    let i184 ← Zig.add false i144 (1 : BitVec 64)
    modify (fun s => { s with local124 := i184 })
    pure .rep143)
  | e => pure e

def mem_eqlBytes (p0 : Zig.Slice) (p1 : Zig.Slice) : Zig.MemM (Bool) := do
  let e ← ((do
    modify (fun s => { s with local2 := p0 })
    modify (fun s => { s with local5 := p1 })
    match ← ((do
      let i10 ← pure (((← get).local2).len)
      let i12 ← pure (((← get).local5).len)
      let i13 ← pure (i10)
      let i14 ← pure (i12)
      let i15 ← pure (i13 != i14)
      if i15 then (do
        pure (.ret false))
      else (do
        pure .br8)) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
    | .br8 => (do
      match ← ((do
        let i21 ← pure (((← get).local2).len)
        let i22 ← pure (i21)
        let i23 ← pure (i22 == (0 : BitVec 64))
        match ← ((do
          if i23 then (do
            pure (.br24 true))
          else (do
            let i28 ← pure (((← get).local2).ptr)
            let i30 ← pure (((← get).local5).ptr)
            let i31 ← Zig.callM (Zig.ptrEqAddr i28 i30)
            pure (.br24 i31))) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
        | .br24 v24 => (do
          if v24 then (do
            pure (.ret true))
          else (do
            pure .br19))
        | e => pure e) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
      | .br19 => (do
        match ← ((do
          let i38 ← pure (((← get).local2).len)
          let i39 ← pure (i38)
          let i40 ← pure (Zig.le false i39 (16 : BitVec 64))
          if i40 then (do
            match ← ((do
              let i44 ← pure (((← get).local2).len)
              let i45 ← pure (i44)
              let i46 ← pure (Zig.lt false i45 (4 : BitVec 64))
              if i46 then (do
                let i48 ← pure ((← get).local2)
                let i49 ← pure i48.len
                let i50 ← pure (Zig.lt false (0 : BitVec 64) i49)
                match ← ((do
                  if i50 then (do
                    pure .br51)
                  else (do
                    throw .outOfBounds)) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
                | .br51 => (do
                  let i56 ← Zig.callM (Zig.checkIndex i48 (0 : BitVec 64) >>= fun _ => Zig.load (BitVec 8) 1 (i48.ptr.elem 1 (0 : BitVec 64)))
                  let i57 ← pure ((← get).local5)
                  let i58 ← pure i57.len
                  let i59 ← pure (Zig.lt false (0 : BitVec 64) i58)
                  match ← ((do
                    if i59 then (do
                      pure .br60)
                    else (do
                      throw .outOfBounds)) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
                  | .br60 => (do
                    let i65 ← Zig.callM (Zig.checkIndex i57 (0 : BitVec 64) >>= fun _ => Zig.load (BitVec 8) 1 (i57.ptr.elem 1 (0 : BitVec 64)))
                    let i66 ← pure (i56 ^^^ i65)
                    let i68 ← pure (((← get).local2).len)
                    let i69 ← Zig.sub false i68 (1 : BitVec 64)
                    let i70 ← pure ((← get).local2)
                    let i71 ← pure i70.len
                    let i72 ← pure (Zig.lt false i69 i71)
                    match ← ((do
                      if i72 then (do
                        pure .br73)
                      else (do
                        throw .outOfBounds)) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
                    | .br73 => (do
                      let i78 ← Zig.callM (Zig.checkIndex i70 i69 >>= fun _ => Zig.load (BitVec 8) 1 (i70.ptr.elem 1 i69))
                      let i80 ← pure (((← get).local2).len)
                      let i81 ← Zig.sub false i80 (1 : BitVec 64)
                      let i82 ← pure ((← get).local5)
                      let i83 ← pure i82.len
                      let i84 ← pure (Zig.lt false i81 i83)
                      match ← ((do
                        if i84 then (do
                          pure .br85)
                        else (do
                          throw .outOfBounds)) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
                      | .br85 => (do
                        let i90 ← Zig.callM (Zig.checkIndex i82 i81 >>= fun _ => Zig.load (BitVec 8) 1 (i82.ptr.elem 1 i81))
                        let i91 ← pure (i78 ^^^ i90)
                        let i92 ← pure (i66 ||| i91)
                        let i94 ← pure (((← get).local2).len)
                        let i95 ← Zig.divTrunc false i94 (2 : BitVec 64)
                        let i96 ← pure ((← get).local2)
                        let i97 ← pure i96.len
                        let i98 ← pure (Zig.lt false i95 i97)
                        match ← ((do
                          if i98 then (do
                            pure .br99)
                          else (do
                            throw .outOfBounds)) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
                        | .br99 => (do
                          let i104 ← Zig.callM (Zig.checkIndex i96 i95 >>= fun _ => Zig.load (BitVec 8) 1 (i96.ptr.elem 1 i95))
                          let i106 ← pure (((← get).local2).len)
                          let i107 ← Zig.divTrunc false i106 (2 : BitVec 64)
                          let i108 ← pure ((← get).local5)
                          let i109 ← pure i108.len
                          let i110 ← pure (Zig.lt false i107 i109)
                          match ← ((do
                            if i110 then (do
                              pure .br111)
                            else (do
                              throw .outOfBounds)) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
                          | .br111 => (do
                            let i116 ← Zig.callM (Zig.checkIndex i108 i107 >>= fun _ => Zig.load (BitVec 8) 1 (i108.ptr.elem 1 i107))
                            let i117 ← pure (i104 ^^^ i116)
                            let i118 ← pure (i92 ||| i117)
                            let i119 ← pure (i118 == (0 : BitVec 8))
                            pure (.ret i119))
                          | e => pure e)
                        | e => pure e)
                      | e => pure e)
                    | e => pure e)
                  | e => pure e)
                | e => pure e)
              else (do
                pure .br42)) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
            | .br42 => (do
              modify (fun s => { s with x := (0 : BitVec 32) })
              modify (fun s => { s with local124 := (0 : BitVec 64) })
              let i127 ← pure (((← get).local2).len)
              let i128 ← Zig.sub false i127 (4 : BitVec 64)
              let i130 ← pure (((← get).local2).len)
              let i131 ← Zig.divTrunc false i130 (8 : BitVec 64)
              let i132 ← Zig.mul false i131 (4 : BitVec 64)
              let i134 ← pure (((← get).local2).len)
              let i135 ← Zig.sub false i134 (4 : BitVec 64)
              let i137 ← pure (((← get).local2).len)
              let i138 ← Zig.divTrunc false i137 (8 : BitVec 64)
              let i139 ← Zig.mul false i138 (4 : BitVec 64)
              let i140 ← Zig.sub false i135 i139
              let i141 ← pure (#v[(0 : BitVec 64), i128, i132, i140] : Vector (BitVec 64) 4)
              match ← ((do
                Zig.loop (mem_eqlBytes.loop143 i141) mem_eqlBytes.again143) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
              | .br142 => (do
                let i187 ← pure ((← get).x)
                let i188 ← pure (i187 == (0 : BitVec 32))
                pure (.ret i188))
              | e => pure e)
            | e => pure e)
          else (do
            pure .br36)) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
        | .br36 => (do
          match ← ((do
            pure .br191) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
          | .br191 => (do
            match ← ((do
              pure .br193) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
            | .br193 => (do
              match ← ((do
                pure .br195) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
              | .br195 => (do
                match ← ((do
                  pure .br197) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
                | .br197 => (do
                  match ← ((do
                    pure .br199) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
                  | .br199 => (do
                    modify (fun s => { s with local201 := (0 : BitVec 64) })
                    let i204 ← pure (((← get).local2).len)
                    let i205 ← Zig.sub false i204 (1 : BitVec 64)
                    let i206 ← Zig.divTrunc false i205 (16 : BitVec 64)
                    match ← ((do
                      Zig.loop (mem_eqlBytes.loop208 i206) mem_eqlBytes.again208) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
                    | .br207 => (do
                      let i259 ← pure (((← get).local2).len)
                      let i260 ← Zig.sub false i259 (16 : BitVec 64)
                      let i261 ← pure ((← get).local2)
                      let i262 ← pure i261.ptr
                      let i263 ← Zig.callM (Zig.ptrProject i262 (·.elem 1 i260))
                      let i264 ← Zig.add false i260 (16 : BitVec 64)
                      let i265 ← pure (i263)
                      let i266 ← pure i261.len
                      let i267 ← pure (Zig.le false i264 i266)
                      match ← ((do
                        if i267 then (do
                          pure .br268)
                        else (do
                          throw .outOfBounds)) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
                      | .br268 => (do
                        let i273 ← Zig.load (Vector (BitVec 8) 16) 1 i265
                        let i274 ← (((pure (Zig.BitCast.ofLanes (i273)) : Zig.Result (BitVec 128)) >>= fun bits => pure ⟨Zig.BitCast.toLanes (n := 16) (w := 8) (bits)⟩) : Zig.Result (Zig.Vec (BitVec 8) 16))
                        let i276 ← pure (((← get).local2).len)
                        let i277 ← Zig.sub false i276 (16 : BitVec 64)
                        let i278 ← pure ((← get).local5)
                        let i279 ← pure i278.ptr
                        let i280 ← Zig.callM (Zig.ptrProject i279 (·.elem 1 i277))
                        let i281 ← Zig.add false i277 (16 : BitVec 64)
                        let i282 ← pure (i280)
                        let i283 ← pure i278.len
                        let i284 ← pure (Zig.le false i281 i283)
                        match ← ((do
                          if i284 then (do
                            pure .br285)
                          else (do
                            throw .outOfBounds)) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
                        | .br285 => (do
                          let i290 ← Zig.load (Vector (BitVec 8) 16) 1 i282
                          let i291 ← (((pure (Zig.BitCast.ofLanes (i290)) : Zig.Result (BitVec 128)) >>= fun bits => pure ⟨Zig.BitCast.toLanes (n := 16) (w := 8) (bits)⟩) : Zig.Result (Zig.Vec (BitVec 8) 16))
                          match ← ((do
                            let i293 ← Zig.Vec.map2M (fun x0 x1 => pure (x0 != x1)) i274 i291
                            let i294 ← pure (Zig.Vec.reduce (· || ·) i293)
                            pure (.br292 i294)) : Zig.MM mem_eqlBytesLocals mem_eqlBytesExit) with
                          | .br292 v292 => (do
                            let i296 ← pure (!v292)
                            pure (.ret i296))
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
      let i18 ← Zig.mul false i17 (1 : BitVec 64)
      let i19 ← pure i16
      let i20 ← Zig.sub false i18 (0 : BitVec 64)
      let i21 ← Zig.callM (Zig.checkSliceEnd p0.len (0 : BitVec 64) i20 0 >>= fun _ => pure (⟨i19, i20⟩ : Zig.Slice))
      pure (.ret i21))
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
    let i1 ← (((pure (Zig.BitCast.ofBools (p0)) : Zig.Result (BitVec 1)) >>= fun bits => pure ⟨Zig.BitCast.toBools (bits)⟩) : Zig.Result (Zig.Vec (Bool) 1))
    pure (.ret i1)) : Zig.M boolItemToLaneLocals boolItemToLaneExit).run' (default : boolItemToLaneLocals)
  match e with
  | .ret v => pure v

structure boolLanesToByteLocals where
  deriving Inhabited

inductive boolLanesToByteExit where
  | ret (v : BitVec 8)

def boolLanesToByte (p0 : Zig.Vec (Bool) 8) : Zig.Result (BitVec 8) := do
  let e ← ((do
    let i1 ← (pure (Zig.BitCast.ofBools (p0).lanes) : Zig.Result (BitVec 8))
    pure (.ret i1)) : Zig.M boolLanesToByteLocals boolLanesToByteExit).run' (default : boolLanesToByteLocals)
  match e with
  | .ret v => pure v

structure bytesToHalvesLocals where
  deriving Inhabited

inductive bytesToHalvesExit where
  | ret (v : Zig.Vec (BitVec 16) 2)

def bytesToHalves (p0 : Vector (BitVec 8) 4) : Zig.Result (Zig.Vec (BitVec 16) 2) := do
  let e ← ((do
    let i1 ← (((pure (Zig.BitCast.ofLanes (p0)) : Zig.Result (BitVec 32)) >>= fun bits => pure ⟨Zig.BitCast.toLanes (n := 2) (w := 16) (bits)⟩) : Zig.Result (Zig.Vec (BitVec 16) 2))
    pure (.ret i1)) : Zig.M bytesToHalvesLocals bytesToHalvesExit).run' (default : bytesToHalvesLocals)
  match e with
  | .ret v => pure v

structure bytesToLanesLocals where
  deriving Inhabited

inductive bytesToLanesExit where
  | ret (v : Zig.Vec (BitVec 8) 4)

def bytesToLanes (p0 : Vector (BitVec 8) 4) : Zig.Result (Zig.Vec (BitVec 8) 4) := do
  let e ← ((do
    let i1 ← (((pure (Zig.BitCast.ofLanes (p0)) : Zig.Result (BitVec 32)) >>= fun bits => pure ⟨Zig.BitCast.toLanes (n := 4) (w := 8) (bits)⟩) : Zig.Result (Zig.Vec (BitVec 8) 4))
    pure (.ret i1)) : Zig.M bytesToLanesLocals bytesToLanesExit).run' (default : bytesToLanesLocals)
  match e with
  | .ret v => pure v

structure eqlChunkLocals where
  deriving Inhabited

inductive eqlChunkExit where
  | ret (v : Bool)

def eqlChunk (p0 : Vector (BitVec 8) 16) (p1 : Vector (BitVec 8) 16) : Zig.Result (Bool) := do
  let e ← ((do
    let i2 ← (((pure (Zig.BitCast.ofLanes (p0)) : Zig.Result (BitVec 128)) >>= fun bits => pure ⟨Zig.BitCast.toLanes (n := 16) (w := 8) (bits)⟩) : Zig.Result (Zig.Vec (BitVec 8) 16))
    let i3 ← (((pure (Zig.BitCast.ofLanes (p1)) : Zig.Result (BitVec 128)) >>= fun bits => pure ⟨Zig.BitCast.toLanes (n := 16) (w := 8) (bits)⟩) : Zig.Result (Zig.Vec (BitVec 8) 16))
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
    let i1 ← (((pure (Zig.BitCast.ofLanes (p0).lanes) : Zig.Result (BitVec 32)) >>= fun bits => pure (Zig.BitCast.toLanes (n := 4) (w := 8) (bits))) : Zig.Result (Vector (BitVec 8) 4))
    pure (.ret i1)) : Zig.M halvesToBytesLocals halvesToBytesExit).run' (default : halvesToBytesLocals)
  match e with
  | .ret v => pure v

structure intToPackedLanesLocals where
  deriving Inhabited

inductive intToPackedLanesExit where
  | ret (v : Zig.Vec (BitVec 3) 3)

def intToPackedLanes (p0 : BitVec 9) : Zig.Result (Zig.Vec (BitVec 3) 3) := do
  let e ← ((do
    let i1 ← (pure ⟨Zig.BitCast.toLanes (n := 3) (w := 3) (p0)⟩ : Zig.Result (Zig.Vec (BitVec 3) 3))
    pure (.ret i1)) : Zig.M intToPackedLanesLocals intToPackedLanesExit).run' (default : intToPackedLanesLocals)
  match e with
  | .ret v => pure v

structure lanesToBytesLocals where
  deriving Inhabited

inductive lanesToBytesExit where
  | ret (v : Vector (BitVec 8) 4)

def lanesToBytes (p0 : Zig.Vec (BitVec 8) 4) : Zig.Result (Vector (BitVec 8) 4) := do
  let e ← ((do
    let i1 ← (((pure (Zig.BitCast.ofLanes (p0).lanes) : Zig.Result (BitVec 32)) >>= fun bits => pure (Zig.BitCast.toLanes (n := 4) (w := 8) (bits))) : Zig.Result (Vector (BitVec 8) 4))
    pure (.ret i1)) : Zig.M lanesToBytesLocals lanesToBytesExit).run' (default : lanesToBytesLocals)
  match e with
  | .ret v => pure v

structure lanesToWordLocals where
  deriving Inhabited

inductive lanesToWordExit where
  | ret (v : BitVec 32)

def lanesToWord (p0 : Zig.Vec (BitVec 8) 4) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← (pure (Zig.BitCast.ofLanes (p0).lanes) : Zig.Result (BitVec 32))
    pure (.ret i1)) : Zig.M lanesToWordLocals lanesToWordExit).run' (default : lanesToWordLocals)
  match e with
  | .ret v => pure v

structure packedLanesToIntLocals where
  deriving Inhabited

inductive packedLanesToIntExit where
  | ret (v : BitVec 9)

def packedLanesToInt (p0 : Zig.Vec (BitVec 3) 3) : Zig.Result (BitVec 9) := do
  let e ← ((do
    let i1 ← (pure (Zig.BitCast.ofLanes (p0).lanes) : Zig.Result (BitVec 9))
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
    let i1 ← (((pure (Zig.BitCast.ofLanes (p0)) : Zig.Result (BitVec 24)) >>= fun bits => pure ⟨Zig.BitCast.toLanes (n := 1) (w := 24) (bits)⟩) : Zig.Result (Zig.Vec (BitVec 24) 1))
    pure (.ret i1)) : Zig.M u24ItemToLaneLocals u24ItemToLaneExit).run' (default : u24ItemToLaneLocals)
  match e with
  | .ret v => pure v

structure u24LaneToItemLocals where
  deriving Inhabited

inductive u24LaneToItemExit where
  | ret (v : Vector (BitVec 24) 1)

def u24LaneToItem (p0 : Zig.Vec (BitVec 24) 1) : Zig.Result (Vector (BitVec 24) 1) := do
  let e ← ((do
    let i1 ← (((pure (Zig.BitCast.ofLanes (p0).lanes) : Zig.Result (BitVec 24)) >>= fun bits => pure (Zig.BitCast.toLanes (n := 1) (w := 24) (bits))) : Zig.Result (Vector (BitVec 24) 1))
    pure (.ret i1)) : Zig.M u24LaneToItemLocals u24LaneToItemExit).run' (default : u24LaneToItemLocals)
  match e with
  | .ret v => pure v

structure wordToLanesLocals where
  deriving Inhabited

inductive wordToLanesExit where
  | ret (v : Zig.Vec (BitVec 8) 4)

def wordToLanes (p0 : BitVec 32) : Zig.Result (Zig.Vec (BitVec 8) 4) := do
  let e ← ((do
    let i1 ← (pure ⟨Zig.BitCast.toLanes (n := 4) (w := 8) (p0)⟩ : Zig.Result (Zig.Vec (BitVec 8) 4))
    pure (.ret i1)) : Zig.M wordToLanesLocals wordToLanesExit).run' (default : wordToLanesLocals)
  match e with
  | .ret v => pure v

end VectorCasts