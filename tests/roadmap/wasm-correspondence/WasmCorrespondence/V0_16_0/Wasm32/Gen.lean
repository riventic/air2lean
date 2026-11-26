-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"none","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"lime1","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["bulk_memory_opt","call_indirect_overlong","extended_const","multivalue","mutable_globals","nontrapping_fptoint","sign_ext"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":32,"schema":12,"target_triple":"wasm32-freestanding-none","zig_version":"0.16.0"}}
import ZigLean


namespace WasmCorrespondence.V0_16_0.Wasm32

open scoped Zig.Wasm32

structure Event where
  time : BitVec 64
  seq : BitVec 32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Event where
  size := 16
  align := 8
  encode v := Zig.Enc.fields 16 [(0, Zig.Enc.encode v.time), (8, Zig.Enc.encode v.seq)]
  decode bs := do pure { time := ← Zig.Enc.decodeAt bs 0, seq := ← Zig.Enc.decodeAt bs 8 }

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ []

structure addDuration__anon_416c8a64dc69Locals where
  deriving Inhabited

inductive addDuration__anon_416c8a64dc69Exit where
  | ret (v : Except Zig.ErrName (BitVec 64))
  | br6 (v : Bool)
  | br3

def addDuration__anon_416c8a64dc69 (p0 : BitVec 64) (p1 : BitVec 64) : Zig.Result (Except Zig.ErrName (BitVec 64)) := do
  let e ← ((do
    let i2 ← pure (Zig.addWithOverflow false p0 p1)
    match ← ((do
      let i4 ← pure ((i2).2)
      let i5 ← pure (i4 != (0 : BitVec 1))
      match ← ((do
        if i5 then (do
          pure (.br6 true))
        else (do
          let i9 ← pure ((i2).1)
          let i10 ← pure (i9 == (18446744073709551615 : BitVec 64))
          pure (.br6 i10))) : Zig.M addDuration__anon_416c8a64dc69Locals addDuration__anon_416c8a64dc69Exit) with
      | .br6 v6 => (do
        if v6 then (do
          pure (.ret (.error "TimeOverflow" : Except Zig.ErrName (BitVec 64))))
        else (do
          pure .br3))
      | e => pure e) : Zig.M addDuration__anon_416c8a64dc69Locals addDuration__anon_416c8a64dc69Exit) with
    | .br3 => (do
      let i15 ← pure ((i2).1)
      let i16 ← pure ((.ok i15) : Except Zig.ErrName (BitVec 64))
      pure (.ret i16))
    | e => pure e) : Zig.M addDuration__anon_416c8a64dc69Locals addDuration__anon_416c8a64dc69Exit).run' (default : addDuration__anon_416c8a64dc69Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] addDuration__anon_416c8a64dc69

structure addDuration__anon_59ee9d3fd631Locals where
  deriving Inhabited

inductive addDuration__anon_59ee9d3fd631Exit where
  | ret (v : Except Zig.ErrName (BitVec 32))
  | br6 (v : Bool)
  | br3

def addDuration__anon_59ee9d3fd631 (p0 : BitVec 32) (p1 : BitVec 32) : Zig.Result (Except Zig.ErrName (BitVec 32)) := do
  let e ← ((do
    let i2 ← pure (Zig.addWithOverflow false p0 p1)
    match ← ((do
      let i4 ← pure ((i2).2)
      let i5 ← pure (i4 != (0 : BitVec 1))
      match ← ((do
        if i5 then (do
          pure (.br6 true))
        else (do
          let i9 ← pure ((i2).1)
          let i10 ← pure (i9 == (4294967295 : BitVec 32))
          pure (.br6 i10))) : Zig.M addDuration__anon_59ee9d3fd631Locals addDuration__anon_59ee9d3fd631Exit) with
      | .br6 v6 => (do
        if v6 then (do
          pure (.ret (.error "TimeOverflow" : Except Zig.ErrName (BitVec 32))))
        else (do
          pure .br3))
      | e => pure e) : Zig.M addDuration__anon_59ee9d3fd631Locals addDuration__anon_59ee9d3fd631Exit) with
    | .br3 => (do
      let i15 ← pure ((i2).1)
      let i16 ← pure ((.ok i15) : Except Zig.ErrName (BitVec 32))
      pure (.ret i16))
    | e => pure e) : Zig.M addDuration__anon_59ee9d3fd631Locals addDuration__anon_59ee9d3fd631Exit).run' (default : addDuration__anon_59ee9d3fd631Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] addDuration__anon_59ee9d3fd631

structure beforeLocals where
  deriving Inhabited

inductive beforeExit where
  | ret (v : Bool)
  | br5 (v : Bool)
  | br11 (v : Bool)

def before (p0 : Event) (p1 : Event) : Zig.Result (Bool) := do
  let e ← ((do
    let i2 ← pure ((p0).time)
    let i3 ← pure ((p1).time)
    let i4 ← pure (Zig.lt false i2 i3)
    match ← ((do
      if i4 then (do
        pure (.br5 true))
      else (do
        let i8 ← pure ((p0).time)
        let i9 ← pure ((p1).time)
        let i10 ← pure (i8 == i9)
        match ← ((do
          if i10 then (do
            let i13 ← pure ((p0).seq)
            let i14 ← pure ((p1).seq)
            let i15 ← pure (Zig.lt false i13 i14)
            pure (.br11 i15))
          else (do
            pure (.br11 false))) : Zig.M beforeLocals beforeExit) with
        | .br11 v11 => (do
          pure (.br5 v11))
        | e => pure e)) : Zig.M beforeLocals beforeExit) with
    | .br5 v5 => (do
      pure (.ret v5))
    | e => pure e) : Zig.M beforeLocals beforeExit).run' (default : beforeLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] before

structure des_event_beforeLocals where
  deriving Inhabited

inductive des_event_beforeExit where
  | ret (v : BitVec 64)
  | br5 (v : Bool)
  | br9 (v : Bool)

def des_event_before (p0 : BitVec 64) (p1 : BitVec 64) (p2 : BitVec 64) (p3 : BitVec 64) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i4 ← pure (Zig.lt false p0 p2)
    match ← ((do
      if i4 then (do
        pure (.br5 true))
      else (do
        let i8 ← pure (p0 == p2)
        match ← ((do
          if i8 then (do
            let i11 ← pure (Zig.trunc 32 p1)
            let i12 ← pure (Zig.trunc 32 p3)
            let i13 ← pure (Zig.lt false i11 i12)
            pure (.br9 i13))
          else (do
            pure (.br9 false))) : Zig.M des_event_beforeLocals des_event_beforeExit) with
        | .br9 v9 => (do
          pure (.br5 v9))
        | e => pure e)) : Zig.M des_event_beforeLocals des_event_beforeExit) with
    | .br5 v5 => (do
      let i17 ← pure (if v5 then 1 else 0 : BitVec 1)
      let i18 ← Zig.intCast false false 64 i17 (safe := false)
      pure (.ret i18))
    | e => pure e) : Zig.M des_event_beforeLocals des_event_beforeExit).run' (default : des_event_beforeLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] des_event_before

structure des_queue_drainLocals where
  heap : Zig.Ptr
  len : BitVec 32
  x : BitVec 64
  seq : BitVec 32
  i : BitVec 32
  hash : BitVec 64
  last : Option (Event)
  i_air2lean1 : BitVec 32
  m : BitVec 32
  deriving Inhabited

inductive des_queue_drainExit where
  | ret (v : BitVec 64)
  | br37
  | br70
  | br77
  | br56
  | br67
  | br90
  | br98
  | br105
  | br63
  | br58
  | br19
  | br15
  | br13
  | br145
  | br172
  | br180
  | br169 (v : Bool)
  | br164
  | br201
  | br209
  | br198 (v : Bool)
  | br193
  | br154
  | br222
  | br233
  | br241
  | br249
  | br258
  | br156
  | br274
  | br269
  | br137
  | br132
  | br130
  | rep57
  | rep14
  | rep155
  | rep131

def des_queue_drain.again155 : des_queue_drainExit → Bool
  | .rep155 => true
  | _ => false

def des_queue_drain.again131 : des_queue_drainExit → Bool
  | .rep131 => true
  | _ => false

def des_queue_drain.again57 : des_queue_drainExit → Bool
  | .rep57 => true
  | _ => false

def des_queue_drain.again14 : des_queue_drainExit → Bool
  | .rep14 => true
  | _ => false

def des_queue_drain.loop155 (i2 : Zig.Ptr) : Zig.MM des_queue_drainLocals des_queue_drainExit := do
  Zig.callM Zig.tick
  match ← ((do
    let i157 ← pure ((← get).i_air2lean1)
    let i158 ← Zig.mul false (2 : BitVec 32) i157
    let i159 ← Zig.add false i158 (1 : BitVec 32)
    let i160 ← Zig.add false i159 (1 : BitVec 32)
    let i162 ← pure ((← get).i_air2lean1)
    modify (fun s => { s with m := i162 })
    match ← ((do
      let i165 ← pure ((← get).len)
      let i166 ← pure (i159)
      let i167 ← pure (i165)
      let i168 ← pure (Zig.lt false i166 i167)
      match ← ((do
        if i168 then (do
          let i171 ← pure (Zig.lt false i159 (32 : BitVec 32))
          match ← ((do
            if i171 then (do
              pure .br172)
            else (do
              throw .outOfBounds)) : Zig.MM des_queue_drainLocals des_queue_drainExit) with
          | .br172 => (do
            let i177 ← Zig.callM (Zig.checkIndex (32 : BitVec 32) i159 >>= fun _ => Zig.load (Event) 8 (i2.elemOf 16 i159))
            let i178 ← pure ((← get).m)
            let i179 ← pure (Zig.lt false i178 (32 : BitVec 32))
            match ← ((do
              if i179 then (do
                pure .br180)
              else (do
                throw .outOfBounds)) : Zig.MM des_queue_drainLocals des_queue_drainExit) with
            | .br180 => (do
              let i185 ← Zig.callM (Zig.checkIndex (32 : BitVec 32) i178 >>= fun _ => Zig.load (Event) 8 (i2.elemOf 16 i178))
              let i186 ← Zig.callR (before i177 i185)
              pure (.br169 i186))
            | e => pure e)
          | e => pure e)
        else (do
          pure (.br169 false))) : Zig.MM des_queue_drainLocals des_queue_drainExit) with
      | .br169 v169 => (do
        if v169 then (do
          modify (fun s => { s with m := i159 })
          pure .br164)
        else (do
          pure .br164))
      | e => pure e) : Zig.MM des_queue_drainLocals des_queue_drainExit) with
    | .br164 => (do
      match ← ((do
        let i194 ← pure ((← get).len)
        let i195 ← pure (i160)
        let i196 ← pure (i194)
        let i197 ← pure (Zig.lt false i195 i196)
        match ← ((do
          if i197 then (do
            let i200 ← pure (Zig.lt false i160 (32 : BitVec 32))
            match ← ((do
              if i200 then (do
                pure .br201)
              else (do
                throw .outOfBounds)) : Zig.MM des_queue_drainLocals des_queue_drainExit) with
            | .br201 => (do
              let i206 ← Zig.callM (Zig.checkIndex (32 : BitVec 32) i160 >>= fun _ => Zig.load (Event) 8 (i2.elemOf 16 i160))
              let i207 ← pure ((← get).m)
              let i208 ← pure (Zig.lt false i207 (32 : BitVec 32))
              match ← ((do
                if i208 then (do
                  pure .br209)
                else (do
                  throw .outOfBounds)) : Zig.MM des_queue_drainLocals des_queue_drainExit) with
              | .br209 => (do
                let i214 ← Zig.callM (Zig.checkIndex (32 : BitVec 32) i207 >>= fun _ => Zig.load (Event) 8 (i2.elemOf 16 i207))
                let i215 ← Zig.callR (before i206 i214)
                pure (.br198 i215))
              | e => pure e)
            | e => pure e)
          else (do
            pure (.br198 false))) : Zig.MM des_queue_drainLocals des_queue_drainExit) with
        | .br198 v198 => (do
          if v198 then (do
            modify (fun s => { s with m := i160 })
            pure .br193)
          else (do
            pure .br193))
        | e => pure e) : Zig.MM des_queue_drainLocals des_queue_drainExit) with
      | .br193 => (do
        match ← ((do
          let i223 ← pure ((← get).m)
          let i224 ← pure ((← get).i_air2lean1)
          let i225 ← pure (i223)
          let i226 ← pure (i224)
          let i227 ← pure (i225 == i226)
          if i227 then (do
            pure .br154)
          else (do
            pure .br222)) : Zig.MM des_queue_drainLocals des_queue_drainExit) with
        | .br222 => (do
          let i231 ← pure ((← get).i_air2lean1)
          let i232 ← pure (Zig.lt false i231 (32 : BitVec 32))
          match ← ((do
            if i232 then (do
              pure .br233)
            else (do
              throw .outOfBounds)) : Zig.MM des_queue_drainLocals des_queue_drainExit) with
          | .br233 => (do
            let i238 ← Zig.callM (Zig.checkIndex (32 : BitVec 32) i231 >>= fun _ => Zig.load (Event) 8 (i2.elemOf 16 i231))
            let i239 ← pure ((← get).i_air2lean1)
            let i240 ← pure (Zig.lt false i239 (32 : BitVec 32))
            match ← ((do
              if i240 then (do
                pure .br241)
              else (do
                throw .outOfBounds)) : Zig.MM des_queue_drainLocals des_queue_drainExit) with
            | .br241 => (do
              let i246 ← Zig.callM (Zig.checkIndex (32 : BitVec 32) i239) >>= fun _ => Zig.callM (Zig.ptrProject i2 (·.elemOf 16 i239))
              let i247 ← pure ((← get).m)
              let i248 ← pure (Zig.lt false i247 (32 : BitVec 32))
              match ← ((do
                if i248 then (do
                  pure .br249)
                else (do
                  throw .outOfBounds)) : Zig.MM des_queue_drainLocals des_queue_drainExit) with
              | .br249 => (do
                let i254 ← Zig.callM (Zig.checkIndex (32 : BitVec 32) i247 >>= fun _ => Zig.load (Event) 8 (i2.elemOf 16 i247))
                Zig.store (α := Event) 8 i246 i254
                let i256 ← pure ((← get).m)
                let i257 ← pure (Zig.lt false i256 (32 : BitVec 32))
                match ← ((do
                  if i257 then (do
                    pure .br258)
                  else (do
                    throw .outOfBounds)) : Zig.MM des_queue_drainLocals des_queue_drainExit) with
                | .br258 => (do
                  let i263 ← Zig.callM (Zig.checkIndex (32 : BitVec 32) i256) >>= fun _ => Zig.callM (Zig.ptrProject i2 (·.elemOf 16 i256))
                  Zig.store (α := Event) 8 i263 i238
                  let i265 ← pure ((← get).m)
                  modify (fun s => { s with i_air2lean1 := i265 })
                  pure .br156)
                | e => pure e)
              | e => pure e)
            | e => pure e)
          | e => pure e)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.MM des_queue_drainLocals des_queue_drainExit) with
  | .br156 => (do
    pure .rep155)
  | e => pure e

def des_queue_drain.loop131 (i2 : Zig.Ptr) : Zig.MM des_queue_drainLocals des_queue_drainExit := do
  Zig.callM Zig.tick
  match ← ((do
    let i133 ← pure ((← get).len)
    let i134 ← pure (i133)
    let i135 ← pure (Zig.gt false i134 (0 : BitVec 32))
    if i135 then (do
      match ← ((do
        let i138 ← Zig.callM (Zig.load (Event) 8 (i2.elemOf 16 (0 : BitVec 32)))
        let i139 ← pure ((← get).len)
        let i140 ← Zig.sub false i139 (1 : BitVec 32)
        modify (fun s => { s with len := i140 })
        let i142 ← pure i2
        let i143 ← pure ((← get).len)
        let i144 ← pure (Zig.lt false i143 (32 : BitVec 32))
        match ← ((do
          if i144 then (do
            pure .br145)
          else (do
            throw .outOfBounds)) : Zig.MM des_queue_drainLocals des_queue_drainExit) with
        | .br145 => (do
          let i150 ← Zig.callM (Zig.checkIndex (32 : BitVec 32) i143 >>= fun _ => Zig.load (Event) 8 (i2.elemOf 16 i143))
          Zig.store (α := Event) 8 i142 i150
          modify (fun s => { s with i_air2lean1 := (0 : BitVec 32) })
          match ← ((do
            Zig.loop (des_queue_drain.loop155 i2) des_queue_drain.again155) : Zig.MM des_queue_drainLocals des_queue_drainExit) with
          | .br154 => (do
            match ← ((do
              let i270 ← pure ((← get).last)
              let i271 ← pure ((i270).isSome)
              if i271 then (do
                let i273 ← Zig.optPayload i270
                match ← ((do
                  let i275 ← Zig.callR (before i138 i273)
                  if i275 then (do
                    pure (.ret (18446744073709551615 : BitVec 64)))
                  else (do
                    pure .br274)) : Zig.MM des_queue_drainLocals des_queue_drainExit) with
                | .br274 => (do
                  pure .br269)
                | e => pure e)
              else (do
                pure .br269)) : Zig.MM des_queue_drainLocals des_queue_drainExit) with
            | .br269 => (do
              let i281 ← pure (some i138)
              modify (fun s => { s with last := i281 })
              let i283 ← pure ((← get).hash)
              let i284 ← pure ((i138).time)
              let i285 ← pure (Zig.shl i284 (32 : BitVec 6))
              let i286 ← pure ((i138).seq)
              let i287 ← Zig.intCast false false 64 i286 (safe := false)
              let i288 ← pure (i285 ||| i287)
              let i289 ← pure (i283 ^^^ i288)
              let i290 ← pure (Zig.mulWrap i289 (1099511628211 : BitVec 64))
              modify (fun s => { s with hash := i290 })
              pure .br137)
            | e => pure e)
          | e => pure e)
        | e => pure e) : Zig.MM des_queue_drainLocals des_queue_drainExit) with
      | .br137 => (do
        pure .br132)
      | e => pure e)
    else (do
      pure .br130)) : Zig.MM des_queue_drainLocals des_queue_drainExit) with
  | .br132 => (do
    pure .rep131)
  | e => pure e

def des_queue_drain.loop57 (i2 : Zig.Ptr) : Zig.MM des_queue_drainLocals des_queue_drainExit := do
  Zig.callM Zig.tick
  match ← ((do
    let i59 ← pure ((← get).i)
    let i60 ← pure (i59)
    let i61 ← pure (Zig.gt false i60 (0 : BitVec 32))
    if i61 then (do
      match ← ((do
        let i64 ← pure ((← get).i)
        let i65 ← Zig.sub false i64 (1 : BitVec 32)
        let i66 ← Zig.divTrunc false i65 (2 : BitVec 32)
        match ← ((do
          let i68 ← pure ((← get).i)
          let i69 ← pure (Zig.lt false i68 (32 : BitVec 32))
          match ← ((do
            if i69 then (do
              pure .br70)
            else (do
              throw .outOfBounds)) : Zig.MM des_queue_drainLocals des_queue_drainExit) with
          | .br70 => (do
            let i75 ← Zig.callM (Zig.checkIndex (32 : BitVec 32) i68 >>= fun _ => Zig.load (Event) 8 (i2.elemOf 16 i68))
            let i76 ← pure (Zig.lt false i66 (32 : BitVec 32))
            match ← ((do
              if i76 then (do
                pure .br77)
              else (do
                throw .outOfBounds)) : Zig.MM des_queue_drainLocals des_queue_drainExit) with
            | .br77 => (do
              let i82 ← Zig.callM (Zig.checkIndex (32 : BitVec 32) i66 >>= fun _ => Zig.load (Event) 8 (i2.elemOf 16 i66))
              let i83 ← Zig.callR (before i75 i82)
              let i84 ← pure (!i83)
              if i84 then (do
                pure .br56)
              else (do
                pure .br67))
            | e => pure e)
          | e => pure e) : Zig.MM des_queue_drainLocals des_queue_drainExit) with
        | .br67 => (do
          let i88 ← pure ((← get).i)
          let i89 ← pure (Zig.lt false i88 (32 : BitVec 32))
          match ← ((do
            if i89 then (do
              pure .br90)
            else (do
              throw .outOfBounds)) : Zig.MM des_queue_drainLocals des_queue_drainExit) with
          | .br90 => (do
            let i95 ← Zig.callM (Zig.checkIndex (32 : BitVec 32) i88 >>= fun _ => Zig.load (Event) 8 (i2.elemOf 16 i88))
            let i96 ← pure ((← get).i)
            let i97 ← pure (Zig.lt false i96 (32 : BitVec 32))
            match ← ((do
              if i97 then (do
                pure .br98)
              else (do
                throw .outOfBounds)) : Zig.MM des_queue_drainLocals des_queue_drainExit) with
            | .br98 => (do
              let i103 ← Zig.callM (Zig.checkIndex (32 : BitVec 32) i96) >>= fun _ => Zig.callM (Zig.ptrProject i2 (·.elemOf 16 i96))
              let i104 ← pure (Zig.lt false i66 (32 : BitVec 32))
              match ← ((do
                if i104 then (do
                  pure .br105)
                else (do
                  throw .outOfBounds)) : Zig.MM des_queue_drainLocals des_queue_drainExit) with
              | .br105 => (do
                let i110 ← Zig.callM (Zig.checkIndex (32 : BitVec 32) i66 >>= fun _ => Zig.load (Event) 8 (i2.elemOf 16 i66))
                Zig.store (α := Event) 8 i103 i110
                let i112 ← Zig.callM (Zig.checkIndex (32 : BitVec 32) i66) >>= fun _ => Zig.callM (Zig.ptrProject i2 (·.elemOf 16 i66))
                Zig.store (α := Event) 8 i112 i95
                modify (fun s => { s with i := i66 })
                pure .br63)
              | e => pure e)
            | e => pure e)
          | e => pure e)
        | e => pure e) : Zig.MM des_queue_drainLocals des_queue_drainExit) with
      | .br63 => (do
        pure .br58)
      | e => pure e)
    else (do
      pure .br56)) : Zig.MM des_queue_drainLocals des_queue_drainExit) with
  | .br58 => (do
    pure .rep57)
  | e => pure e

def des_queue_drain.loop14 (i2 : Zig.Ptr) (i10 : BitVec 32) : Zig.MM des_queue_drainLocals des_queue_drainExit := do
  Zig.callM Zig.tick
  match ← ((do
    let i16 ← pure ((← get).seq)
    let i17 ← pure (Zig.lt false i16 i10)
    if i17 then (do
      match ← ((do
        let i20 ← pure ((← get).x)
        let i21 ← pure ((← get).x)
        let i22 ← pure (Zig.shl i21 (13 : BitVec 6))
        let i23 ← pure (i20 ^^^ i22)
        modify (fun s => { s with x := i23 })
        let i25 ← pure ((← get).x)
        let i26 ← pure ((← get).x)
        let i27 ← pure (Zig.shr false i26 (7 : BitVec 6))
        let i28 ← pure (i25 ^^^ i27)
        modify (fun s => { s with x := i28 })
        let i30 ← pure ((← get).x)
        let i31 ← pure ((← get).x)
        let i32 ← pure (Zig.shl i31 (17 : BitVec 6))
        let i33 ← pure (i30 ^^^ i32)
        modify (fun s => { s with x := i33 })
        let i35 ← pure ((← get).len)
        let i36 ← pure (Zig.lt false i35 (32 : BitVec 32))
        match ← ((do
          if i36 then (do
            pure .br37)
          else (do
            throw .outOfBounds)) : Zig.MM des_queue_drainLocals des_queue_drainExit) with
        | .br37 => (do
          let i42 ← Zig.callM (Zig.checkIndex (32 : BitVec 32) i35) >>= fun _ => Zig.callM (Zig.ptrProject i2 (·.elemOf 16 i35))
          let i43 ← pure i42
          let i44 ← pure ((← get).x)
          let i45 ← Zig.rem false i44 (8 : BitVec 64)
          Zig.store (α := BitVec 64) 8 i43 i45
          let i47 ← Zig.callM (Zig.ptrProject i42 (·.add 8))
          let i48 ← pure ((← get).seq)
          Zig.store (α := BitVec 32) 4 i47 i48
          let i51 ← pure ((← get).len)
          modify (fun s => { s with i := i51 })
          let i53 ← pure ((← get).len)
          let i54 ← Zig.add false i53 (1 : BitVec 32)
          modify (fun s => { s with len := i54 })
          match ← ((do
            Zig.loop (des_queue_drain.loop57 i2) des_queue_drain.again57) : Zig.MM des_queue_drainLocals des_queue_drainExit) with
          | .br56 => (do
            pure .br19)
          | e => pure e)
        | e => pure e) : Zig.MM des_queue_drainLocals des_queue_drainExit) with
      | .br19 => (do
        let i120 ← pure ((← get).seq)
        let i121 ← Zig.add false i120 (1 : BitVec 32)
        modify (fun s => { s with seq := i121 })
        pure .br15)
      | e => pure e)
    else (do
      pure .br13)) : Zig.MM des_queue_drainLocals des_queue_drainExit) with
  | .br15 => (do
    pure .rep14)
  | e => pure e

def des_queue_drain (p0 : BitVec 64) (p1 : BitVec 64) : Zig.MemM (BitVec 64) := do
  let s2 ← Zig.allocStack 512 8
  let e ← ((do
    let i2 ← pure (← get).heap
    Zig.storeUndef (Vector (Event) 32) 8 i2
    modify (fun s => { s with len := (0 : BitVec 32) })
    let i7 ← pure (p0 ||| (1 : BitVec 64))
    modify (fun s => { s with x := i7 })
    let i9 ← Zig.rem false p1 (33 : BitVec 64)
    let i10 ← Zig.intCast false false 32 i9
    modify (fun s => { s with seq := (0 : BitVec 32) })
    match ← ((do
      Zig.loop (des_queue_drain.loop14 i2 i10) des_queue_drain.again14) : Zig.MM des_queue_drainLocals des_queue_drainExit) with
    | .br13 => (do
      modify (fun s => { s with hash := (14695981039346656037 : BitVec 64) })
      modify (fun s => { s with last := none })
      match ← ((do
        Zig.loop (des_queue_drain.loop131 i2) des_queue_drain.again131) : Zig.MM des_queue_drainLocals des_queue_drainExit) with
      | .br130 => (do
        let i296 ← pure ((← get).hash)
        pure (.ret i296))
      | e => pure e)
    | e => pure e) : Zig.MM des_queue_drainLocals des_queue_drainExit).run' { (default : des_queue_drainLocals) with heap := s2 }
  Zig.free s2
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] des_queue_drain.loop155 des_queue_drain.loop131 des_queue_drain.loop57 des_queue_drain.loop14 des_queue_drain

structure des_time_add32Locals where
  deriving Inhabited

inductive des_time_add32Exit where
  | ret (v : BitVec 64)
  | br2 (v : BitVec 64)

def des_time_add32 (p0 : BitVec 64) (p1 : BitVec 64) : Zig.Result (BitVec 64) := do
  let e ← ((do
    match ← ((do
      let i3 ← pure (Zig.trunc 32 p0)
      let i4 ← pure (Zig.trunc 32 p1)
      let i5 ← Zig.call (addDuration__anon_59ee9d3fd631 i3 i4)
      let i6 ← pure (Zig.isNonErr i5)
      if i6 then (do
        let i8 ← Zig.call (Zig.unwrapPayload i5)
        let i9 ← Zig.intCast false false 64 i8 (safe := false)
        pure (.br2 i9))
      else (do
        let _i11 ← Zig.call (Zig.unwrapErr i5)
        pure (.br2 (18446744073709551615 : BitVec 64)))) : Zig.M des_time_add32Locals des_time_add32Exit) with
    | .br2 v2 => (do
      pure (.ret v2))
    | e => pure e) : Zig.M des_time_add32Locals des_time_add32Exit).run' (default : des_time_add32Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] des_time_add32

structure des_time_add64Locals where
  deriving Inhabited

inductive des_time_add64Exit where
  | ret (v : BitVec 64)
  | br2 (v : BitVec 64)

def des_time_add64 (p0 : BitVec 64) (p1 : BitVec 64) : Zig.Result (BitVec 64) := do
  let e ← ((do
    match ← ((do
      let i3 ← Zig.call (addDuration__anon_416c8a64dc69 p0 p1)
      let i4 ← pure (Zig.isNonErr i3)
      if i4 then (do
        let i6 ← Zig.call (Zig.unwrapPayload i3)
        pure (.br2 i6))
      else (do
        let _i8 ← Zig.call (Zig.unwrapErr i3)
        pure (.br2 (18446744073709551615 : BitVec 64)))) : Zig.M des_time_add64Locals des_time_add64Exit) with
    | .br2 v2 => (do
      pure (.ret v2))
    | e => pure e) : Zig.M des_time_add64Locals des_time_add64Exit).run' (default : des_time_add64Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] des_time_add64

structure f32_fmaLocals where
  deriving Inhabited

inductive f32_fmaExit where
  | ret (v : BitVec 64)

def f32_fma (p0 : BitVec 64) (p1 : BitVec 64) (p2 : BitVec 64) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i3 ← pure (Zig.trunc 32 p0)
    let i4 ← pure ((Zig.Float.ofBits i3) : Zig.F32)
    let i5 ← pure (Zig.trunc 32 p1)
    let i6 ← pure ((Zig.Float.ofBits i5) : Zig.F32)
    let i7 ← pure (Zig.trunc 32 p2)
    let i8 ← pure ((Zig.Float.ofBits i7) : Zig.F32)
    let i9 ← Zig.Float.fmaChk i4 i6 i8
    let i10 ← Zig.Float.toBits? i9
    let i11 ← Zig.intCast false false 64 i10 (safe := false)
    pure (.ret i11)) : Zig.M f32_fmaLocals f32_fmaExit).run' (default : f32_fmaLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] f32_fma

structure f64ofLocals where
  deriving Inhabited

inductive f64ofExit where
  | ret (v : Zig.F64)

def f64of (p0 : BitVec 64) : Zig.Result (Zig.F64) := do
  let e ← ((do
    let i1 ← pure ((Zig.Float.ofBits p0) : Zig.F64)
    pure (.ret i1)) : Zig.M f64ofLocals f64ofExit).run' (default : f64ofLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] f64of

structure f64_arithLocals where
  deriving Inhabited

inductive f64_arithExit where
  | ret (v : BitVec 64)

def f64_arith (p0 : BitVec 64) (p1 : BitVec 64) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i2 ← Zig.call (f64of p0)
    let i3 ← Zig.call (f64of p1)
    let i4 ← pure (Zig.Float.mul i2 i3)
    let i5 ← pure (Zig.Float.div i2 i3)
    let i6 ← pure (Zig.Float.add i4 i5)
    let i7 ← pure (Zig.Float.sub i6 i3)
    let i8 ← Zig.Float.toBits? i7
    pure (.ret i8)) : Zig.M f64_arithLocals f64_arithExit).run' (default : f64_arithLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] f64_arith

structure f64_sinLocals where
  deriving Inhabited

inductive f64_sinExit where
  | ret (v : BitVec 64)

def f64_sin (p0 : BitVec 64) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i1 ← Zig.call (f64of p0)
    let i2 ← pure (Zig.Float.libm .sin i1)
    let i3 ← Zig.Float.toBits? i2
    pure (.ret i3)) : Zig.M f64_sinLocals f64_sinExit).run' (default : f64_sinLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] f64_sin

structure f64_sqrtLocals where
  deriving Inhabited

inductive f64_sqrtExit where
  | ret (v : BitVec 64)

def f64_sqrt (p0 : BitVec 64) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i1 ← Zig.call (f64of p0)
    let i2 ← pure (Zig.Float.sqrt i1)
    let i3 ← Zig.Float.toBits? i2
    pure (.ret i3)) : Zig.M f64_sqrtLocals f64_sqrtExit).run' (default : f64_sqrtLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] f64_sqrt

structure f64_to_i64Locals where
  deriving Inhabited

inductive f64_to_i64Exit where
  | ret (v : BitVec 64)

def f64_to_i64 (p0 : BitVec 64) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i1 ← Zig.call (f64of p0)
    let i2 ← Zig.Float.toInt true 64 true i1
    let i3 ← pure (i2)
    pure (.ret i3)) : Zig.M f64_to_i64Locals f64_to_i64Exit).run' (default : f64_to_i64Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] f64_to_i64

structure int_add_checkedLocals where
  deriving Inhabited

inductive int_add_checkedExit where
  | ret (v : BitVec 64)

def int_add_checked (p0 : BitVec 64) (p1 : BitVec 64) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i2 ← Zig.add false p0 p1
    pure (.ret i2)) : Zig.M int_add_checkedLocals int_add_checkedExit).run' (default : int_add_checkedLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] int_add_checked

structure int_divmodLocals where
  deriving Inhabited

inductive int_divmodExit where
  | ret (v : BitVec 64)
  | br7
  | br13

def int_divmod (p0 : BitVec 64) (p1 : BitVec 64) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i2 ← pure (p0)
    let i3 ← pure (p1)
    let i4 ← pure (i2 != (-(9223372036854775808 : BitVec 64)))
    let i5 ← pure (i3 != (-(1 : BitVec 64)))
    let i6 ← pure (i4 || i5)
    match ← ((do
      if i6 then (do
        pure .br7)
      else (do
        throw .overflow)) : Zig.M int_divmodLocals int_divmodExit) with
    | .br7 => (do
      let i12 ← pure (i3 != (0 : BitVec 64))
      match ← ((do
        if i12 then (do
          pure .br13)
        else (do
          throw .divByZero)) : Zig.M int_divmodLocals int_divmodExit) with
      | .br13 => (do
        let i18 ← Zig.divTrunc true i2 i3
        let i19 ← Zig.mod true i2 i3
        let i20 ← pure (Zig.mulWrap i18 (31 : BitVec 64))
        let i21 ← pure (Zig.addWrap i20 i19)
        let i22 ← pure (i21)
        pure (.ret i22))
      | e => pure e)
    | e => pure e) : Zig.M int_divmodLocals int_divmodExit).run' (default : int_divmodLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] int_divmod

structure math_rotl__anon_bafa38080fd5Locals where
  deriving Inhabited

inductive math_rotl__anon_bafa38080fd5Exit where
  | ret (v : BitVec 64)

def math_rotl__anon_bafa38080fd5 (p0 : BitVec 64) (p1 : BitVec 7) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i2 ← Zig.intCast false false 16 p1 (safe := false)
    let i3 ← Zig.mod false i2 (64 : BitVec 16)
    let i4 ← Zig.intCast false false 6 i3
    let i5 ← pure (Zig.shl p0 i4)
    let i6 ← pure (~~~i4)
    let i7 ← pure (Zig.addWrap (1 : BitVec 6) i6)
    let i8 ← pure (Zig.shr false p0 i7)
    let i9 ← pure (i5 ||| i8)
    pure (.ret i9)) : Zig.M math_rotl__anon_bafa38080fd5Locals math_rotl__anon_bafa38080fd5Exit).run' (default : math_rotl__anon_bafa38080fd5Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] math_rotl__anon_bafa38080fd5

structure int_mixLocals where
  r : BitVec 64
  deriving Inhabited

inductive int_mixExit where
  | ret (v : BitVec 64)

def int_mix (p0 : BitVec 64) (p1 : BitVec 64) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i2 ← pure (Zig.trunc 32 p0)
    let i3 ← pure (Zig.trunc 16 p1)
    let i4 ← Zig.intCast false false 128 p0 (safe := false)
    let i5 ← Zig.intCast false false 128 p1 (safe := false)
    let i6 ← Zig.mul false i4 i5
    let i8 ← pure (Zig.shr false i6 (64 : BitVec 7))
    let i9 ← pure (Zig.trunc 64 i8)
    modify (fun s => { s with r := i9 })
    let i11 ← pure ((← get).r)
    let i12 ← Zig.rem false p1 (64 : BitVec 64)
    let i13 ← pure (Zig.trunc 7 i12)
    let i14 ← Zig.call (math_rotl__anon_bafa38080fd5 p0 i13)
    let i15 ← pure (Zig.mulWrap p1 (11400714819323198485 : BitVec 64))
    let i16 ← pure (Zig.addWrap i14 i15)
    let i17 ← pure (i11 ^^^ i16)
    modify (fun s => { s with r := i17 })
    let i19 ← pure ((← get).r)
    let i20 ← pure (Zig.clz 7 p0)
    let i21 ← Zig.intCast false false 64 i20 (safe := false)
    let i22 ← pure (Zig.ctz 7 p1)
    let i23 ← Zig.intCast false false 64 i22 (safe := false)
    let i24 ← pure (Zig.shl i23 (8 : BitVec 6))
    let i25 ← pure (i21 ||| i24)
    let i26 ← pure (p0 ^^^ p1)
    let i27 ← pure (Zig.popcount 7 i26)
    let i28 ← Zig.intCast false false 64 i27 (safe := false)
    let i29 ← pure (Zig.shl i28 (16 : BitVec 6))
    let i30 ← pure (i25 ||| i29)
    let i31 ← pure (Zig.addWrap i19 i30)
    modify (fun s => { s with r := i31 })
    let i33 ← pure ((← get).r)
    let i34 ← pure (Zig.byteSwap i2)
    let i35 ← Zig.intCast false false 64 i34 (safe := false)
    let i36 ← pure (Zig.shl i35 (24 : BitVec 6))
    let i37 ← pure (Zig.bitReverse p1)
    let i38 ← pure (i36 ^^^ i37)
    let i39 ← pure (i33 ^^^ i38)
    modify (fun s => { s with r := i39 })
    let i41 ← pure ((← get).r)
    let i42 ← pure (Zig.byteSwap i3)
    let i43 ← Zig.intCast false false 64 i42 (safe := false)
    let i44 ← pure (Zig.trunc 7 p0)
    let i45 ← Zig.intCast false false 64 i44 (safe := false)
    let i46 ← pure (Zig.mulWrap i43 i45)
    let i47 ← pure (Zig.subWrap i41 i46)
    modify (fun s => { s with r := i47 })
    let i49 ← pure ((← get).r)
    pure (.ret i49)) : Zig.M int_mixLocals int_mixExit).run' (default : int_mixLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] int_mix

structure math_shl__anon_09022bf2362dLocals where
  deriving Inhabited

inductive math_shl__anon_09022bf2362dExit where
  | ret (v : BitVec 64)
  | br2 (v : BitVec 6)
  | br3

def math_shl__anon_09022bf2362d (p0 : BitVec 64) (p1 : BitVec 64) : Zig.Result (BitVec 64) := do
  let e ← ((do
    match ← ((do
      match ← ((do
        let i4 ← pure (Zig.lt false p1 (64 : BitVec 64))
        if i4 then (do
          let i6 ← Zig.intCast false false 6 p1
          pure (.br2 i6))
        else (do
          pure .br3)) : Zig.M math_shl__anon_09022bf2362dLocals math_shl__anon_09022bf2362dExit) with
      | .br3 => (do
        pure (.ret (0 : BitVec 64)))
      | e => pure e) : Zig.M math_shl__anon_09022bf2362dLocals math_shl__anon_09022bf2362dExit) with
    | .br2 v2 => (do
      let i10 ← pure (Zig.shl p0 v2)
      pure (.ret i10))
    | e => pure e) : Zig.M math_shl__anon_09022bf2362dLocals math_shl__anon_09022bf2362dExit).run' (default : math_shl__anon_09022bf2362dLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] math_shl__anon_09022bf2362d

structure int_shl_exactLocals where
  deriving Inhabited

inductive int_shl_exactExit where
  | ret (v : BitVec 64)

def int_shl_exact (p0 : BitVec 64) (p1 : BitVec 64) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i2 ← Zig.call (math_shl__anon_09022bf2362d p0 p1)
    let i3 ← Zig.intCast false false 6 p1
    let i4 ← pure (Zig.shl p0 i3)
    let i5 ← pure (i2 ^^^ i4)
    pure (.ret i5)) : Zig.M int_shl_exactLocals int_shl_exactExit).run' (default : int_shl_exactLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] int_shl_exact

structure math_cast__anon_7b3bcc53abd1Locals where
  deriving Inhabited

inductive math_cast__anon_7b3bcc53abd1Exit where
  | ret (v : Option (BitVec 32))

def math_cast__anon_7b3bcc53abd1 (p0 : BitVec 64) : Zig.Result (Option (BitVec 32)) := do
  let e ← ((do
    let i1 ← pure (Zig.gt false p0 (4294967295 : BitVec 64))
    if i1 then (do
      pure (.ret none))
    else (do
      let i4 ← Zig.intCast false false 32 p0
      let i5 ← pure (some i4)
      pure (.ret i5))) : Zig.M math_cast__anon_7b3bcc53abd1Locals math_cast__anon_7b3bcc53abd1Exit).run' (default : math_cast__anon_7b3bcc53abd1Locals)
  match e with
  | .ret v => pure v

attribute [zig_run] math_cast__anon_7b3bcc53abd1

structure pointer_width_pointer_width_byteCountLocals where
  deriving Inhabited

inductive pointer_width_pointer_width_byteCountExit where
  | ret (v : Option (BitVec 32))
  | br2

def pointer_width_pointer_width_byteCount (p0 : BitVec 32) : Zig.Result (Option (BitVec 32)) := do
  let e ← ((do
    let i1 ← pure (Zig.mulWithOverflow false p0 (4 : BitVec 32))
    match ← ((do
      let i3 ← pure ((i1).2)
      let i4 ← pure (i3 != (0 : BitVec 1))
      if i4 then (do
        pure (.ret none))
      else (do
        pure .br2)) : Zig.M pointer_width_pointer_width_byteCountLocals pointer_width_pointer_width_byteCountExit) with
    | .br2 => (do
      let i8 ← pure ((i1).1)
      let i9 ← pure (some i8)
      pure (.ret i9))
    | e => pure e) : Zig.M pointer_width_pointer_width_byteCountLocals pointer_width_pointer_width_byteCountExit).run' (default : pointer_width_pointer_width_byteCountLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] pointer_width_pointer_width_byteCount

structure pw_byte_countLocals where
  deriving Inhabited

inductive pw_byte_countExit where
  | ret (v : BitVec 64)
  | br1 (v : BitVec 32)
  | br8 (v : BitVec 64)

def pw_byte_count (p0 : BitVec 64) : Zig.Result (BitVec 64) := do
  let e ← ((do
    match ← ((do
      let i2 ← Zig.call (math_cast__anon_7b3bcc53abd1 p0)
      let i3 ← pure ((i2).isSome)
      if i3 then (do
        let i5 ← Zig.optPayload i2
        pure (.br1 i5))
      else (do
        pure (.ret (18446744073709551615 : BitVec 64)))) : Zig.M pw_byte_countLocals pw_byte_countExit) with
    | .br1 v1 => (do
      match ← ((do
        let i9 ← Zig.call (pointer_width_pointer_width_byteCount v1)
        let i10 ← pure ((i9).isSome)
        if i10 then (do
          let i12 ← Zig.optPayload i9
          let i13 ← Zig.intCast false false 64 i12 (safe := false)
          pure (.br8 i13))
        else (do
          pure (.br8 (18446744073709551615 : BitVec 64)))) : Zig.M pw_byte_countLocals pw_byte_countExit) with
      | .br8 v8 => (do
        pure (.ret v8))
      | e => pure e)
    | e => pure e) : Zig.M pw_byte_countLocals pw_byte_countExit).run' (default : pw_byte_countLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

attribute [zig_run] pw_byte_count

structure pointer_width_pointer_width_succLocals where
  deriving Inhabited

inductive pointer_width_pointer_width_succExit where
  | ret (v : BitVec 32)

def pointer_width_pointer_width_succ (p0 : BitVec 32) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← Zig.add false p0 (1 : BitVec 32)
    pure (.ret i1)) : Zig.M pointer_width_pointer_width_succLocals pointer_width_pointer_width_succExit).run' (default : pointer_width_pointer_width_succLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] pointer_width_pointer_width_succ

structure pw_succLocals where
  deriving Inhabited

inductive pw_succExit where
  | ret (v : BitVec 64)

def pw_succ (p0 : BitVec 64) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i1 ← pure (Zig.trunc 32 p0)
    let i2 ← Zig.call (pointer_width_pointer_width_succ i1)
    let i3 ← Zig.intCast false false 64 i2 (safe := false)
    pure (.ret i3)) : Zig.M pw_succLocals pw_succExit).run' (default : pw_succLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] pw_succ

structure usize_bitsLocals where
  deriving Inhabited

inductive usize_bitsExit where
  | ret (v : BitVec 64)

def usize_bits  : Zig.Result (BitVec 64) := do
  let e ← ((do
    pure (.ret (32 : BitVec 64))) : Zig.M usize_bitsLocals usize_bitsExit).run' (default : usize_bitsLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] usize_bits

end WasmCorrespondence.V0_16_0.Wasm32