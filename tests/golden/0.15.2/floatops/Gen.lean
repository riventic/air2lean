import ZigLean


namespace Floatops

structure cmp64Locals where
  m : BitVec 8
  deriving Inhabited

inductive cmp64Exit where
  | ret (v : BitVec 8)
  | br4
  | br12
  | br20
  | br28
  | br36
  | br44

def cmp64 (p0 : Zig.F64) (p1 : Zig.F64) : Zig.Result (BitVec 8) := do
  let e ← ((do
    modify (fun s => { s with m := (0 : BitVec 8) })
    match ← ((do
      let i5 ← pure (Zig.Float.lt p0 p1)
      if i5 then (do
        let i7 ← pure ((← get).m)
        let i8 ← pure (i7 ||| (1 : BitVec 8))
        modify (fun s => { s with m := i8 })
        pure .br4)
      else (do
        pure .br4)) : Zig.M cmp64Locals cmp64Exit) with
    | .br4 => (do
      match ← ((do
        let i13 ← pure (Zig.Float.le p0 p1)
        if i13 then (do
          let i15 ← pure ((← get).m)
          let i16 ← pure (i15 ||| (2 : BitVec 8))
          modify (fun s => { s with m := i16 })
          pure .br12)
        else (do
          pure .br12)) : Zig.M cmp64Locals cmp64Exit) with
      | .br12 => (do
        match ← ((do
          let i21 ← pure (Zig.Float.eq p0 p1)
          if i21 then (do
            let i23 ← pure ((← get).m)
            let i24 ← pure (i23 ||| (4 : BitVec 8))
            modify (fun s => { s with m := i24 })
            pure .br20)
          else (do
            pure .br20)) : Zig.M cmp64Locals cmp64Exit) with
        | .br20 => (do
          match ← ((do
            let i29 ← pure (Zig.Float.ne p0 p1)
            if i29 then (do
              let i31 ← pure ((← get).m)
              let i32 ← pure (i31 ||| (8 : BitVec 8))
              modify (fun s => { s with m := i32 })
              pure .br28)
            else (do
              pure .br28)) : Zig.M cmp64Locals cmp64Exit) with
          | .br28 => (do
            match ← ((do
              let i37 ← pure (Zig.Float.ge p0 p1)
              if i37 then (do
                let i39 ← pure ((← get).m)
                let i40 ← pure (i39 ||| (16 : BitVec 8))
                modify (fun s => { s with m := i40 })
                pure .br36)
              else (do
                pure .br36)) : Zig.M cmp64Locals cmp64Exit) with
            | .br36 => (do
              match ← ((do
                let i45 ← pure (Zig.Float.gt p0 p1)
                if i45 then (do
                  let i47 ← pure ((← get).m)
                  let i48 ← pure (i47 ||| (32 : BitVec 8))
                  modify (fun s => { s with m := i48 })
                  pure .br44)
                else (do
                  pure .br44)) : Zig.M cmp64Locals cmp64Exit) with
              | .br44 => (do
                let i52 ← pure ((← get).m)
                pure (.ret i52))
              | e => pure e)
            | e => pure e)
          | e => pure e)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.M cmp64Locals cmp64Exit).run' (default : cmp64Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure divExact64Locals where
  deriving Inhabited

inductive divExact64Exit where
  | ret (v : Zig.F64)
  | br5

def divExact64 (p0 : Zig.F64) (p1 : Zig.F64) : Zig.Result (Zig.F64) := do
  let e ← ((do
    let i2 ← pure (Zig.Float.divTruncRt p0 p1)
    let i3 ← Zig.Float.floorRtLegacyChk i2
    let i4 ← pure (Zig.Float.eq i2 i3)
    match ← ((do
      if i4 then (do
        pure .br5)
      else (do
        throw .panic)) : Zig.M divExact64Locals divExact64Exit) with
    | .br5 => (do
      pure (.ret i2))
    | e => pure e) : Zig.M divExact64Locals divExact64Exit).run' (default : divExact64Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure op128Locals where
  deriving Inhabited

inductive op128Exit where
  | ret (v : Zig.F128)
  | br5 (v : Zig.F128)
  | br4 (v : Zig.F128)

def op128 (p0 : BitVec 8) (p1 : Zig.F128) (p2 : Zig.F128) (p3 : Zig.F128) : Zig.Result (Zig.F128) := do
  let e ← ((do
    match ← ((do
      match ← ((do
        if p0 == (0 : BitVec 8) then (do
          let i8 ← pure (Zig.Float.add p1 p2)
          pure (.br5 i8))
        else (do
          if p0 == (1 : BitVec 8) then (do
            let i10 ← pure (Zig.Float.sub p1 p2)
            pure (.br5 i10))
          else (do
            if p0 == (2 : BitVec 8) then (do
              let i12 ← pure (Zig.Float.mulRt p1 p2)
              pure (.br5 i12))
            else (do
              if p0 == (3 : BitVec 8) then (do
                let i14 ← pure (Zig.Float.divRt p1 p2)
                pure (.br5 i14))
              else (do
                if p0 == (4 : BitVec 8) then (do
                  let i16 ← Zig.Float.fmaRtChk p1 p2 p3
                  pure (.br5 i16))
                else (do
                  if p0 == (5 : BitVec 8) then (do
                    let i18 ← pure (Zig.Float.divTruncRt p1 p2)
                    pure (.br5 i18))
                  else (do
                    if p0 == (6 : BitVec 8) then (do
                      let i20 ← pure (Zig.Float.divFloorRt p1 p2)
                      pure (.br5 i20))
                    else (do
                      if p0 == (7 : BitVec 8) then (do
                        let i22 ← Zig.Float.remRtChk p1 p2
                        pure (.br5 i22))
                      else (do
                        if p0 == (8 : BitVec 8) then (do
                          let i24 ← Zig.Float.modRtChk p1 p2
                          pure (.br5 i24))
                        else (do
                          if p0 == (9 : BitVec 8) then (do
                            let i26 ← pure (Zig.Float.sqrtF128ViaF64 p1)
                            pure (.br5 i26))
                          else (do
                            if p0 == (10 : BitVec 8) then (do
                              let i28 ← Zig.Float.floorRtLegacyChk p1
                              pure (.br5 i28))
                            else (do
                              if p0 == (11 : BitVec 8) then (do
                                let i30 ← Zig.Float.ceilRtLegacyChk p1
                                pure (.br5 i30))
                              else (do
                                if p0 == (12 : BitVec 8) then (do
                                  let i32 ← Zig.Float.truncChk p1
                                  pure (.br5 i32))
                                else (do
                                  if p0 == (13 : BitVec 8) then (do
                                    let i34 ← Zig.Float.roundChk p1
                                    pure (.br5 i34))
                                  else (do
                                    if p0 == (14 : BitVec 8) then (do
                                      let i36 ← pure (Zig.Float.abs p1)
                                      pure (.br5 i36))
                                    else (do
                                      if p0 == (15 : BitVec 8) then (do
                                        let i38 ← pure (Zig.Float.neg p1)
                                        pure (.br5 i38))
                                      else (do
                                        if p0 == (16 : BitVec 8) then (do
                                          let i40 ← Zig.Float.minChk p1 p2
                                          pure (.br5 i40))
                                        else (do
                                          if p0 == (17 : BitVec 8) then (do
                                            let i42 ← Zig.Float.maxChk p1 p2
                                            pure (.br5 i42))
                                          else (do
                                            if p0 == (18 : BitVec 8) then (do
                                              let i44 ← pure (Zig.Float.libm .sin p1)
                                              pure (.br5 i44))
                                            else (do
                                              if p0 == (19 : BitVec 8) then (do
                                                let i46 ← pure (Zig.Float.libm .cos p1)
                                                pure (.br5 i46))
                                              else (do
                                                if p0 == (20 : BitVec 8) then (do
                                                  let i48 ← pure (Zig.Float.libm .tan p1)
                                                  pure (.br5 i48))
                                                else (do
                                                  if p0 == (21 : BitVec 8) then (do
                                                    let i50 ← pure (Zig.Float.libm .exp p1)
                                                    pure (.br5 i50))
                                                  else (do
                                                    if p0 == (22 : BitVec 8) then (do
                                                      let i52 ← pure (Zig.Float.libm .exp2 p1)
                                                      pure (.br5 i52))
                                                    else (do
                                                      if p0 == (23 : BitVec 8) then (do
                                                        let i54 ← pure (Zig.Float.libm .log p1)
                                                        pure (.br5 i54))
                                                      else (do
                                                        if p0 == (24 : BitVec 8) then (do
                                                          let i56 ← pure (Zig.Float.libm .log2 p1)
                                                          pure (.br5 i56))
                                                        else (do
                                                          if p0 == (25 : BitVec 8) then (do
                                                            let i58 ← pure (Zig.Float.libm .log10 p1)
                                                            pure (.br5 i58))
                                                          else (do
                                                            pure (.br5 p1)))))))))))))))))))))))))))) : Zig.M op128Locals op128Exit) with
      | .br5 v5 => (do
        pure (.br4 v5))
      | e => pure e) : Zig.M op128Locals op128Exit) with
    | .br4 v4 => (do
      pure (.ret v4))
    | e => pure e) : Zig.M op128Locals op128Exit).run' (default : op128Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure op16Locals where
  deriving Inhabited

inductive op16Exit where
  | ret (v : Zig.F16)
  | br5 (v : Zig.F16)
  | br4 (v : Zig.F16)

def op16 (p0 : BitVec 8) (p1 : Zig.F16) (p2 : Zig.F16) (p3 : Zig.F16) : Zig.Result (Zig.F16) := do
  let e ← ((do
    match ← ((do
      match ← ((do
        if p0 == (0 : BitVec 8) then (do
          let i8 ← pure (Zig.Float.add p1 p2)
          pure (.br5 i8))
        else (do
          if p0 == (1 : BitVec 8) then (do
            let i10 ← pure (Zig.Float.sub p1 p2)
            pure (.br5 i10))
          else (do
            if p0 == (2 : BitVec 8) then (do
              let i12 ← pure (Zig.Float.mulRt p1 p2)
              pure (.br5 i12))
            else (do
              if p0 == (3 : BitVec 8) then (do
                let i14 ← pure (Zig.Float.divRt p1 p2)
                pure (.br5 i14))
              else (do
                if p0 == (4 : BitVec 8) then (do
                  let i16 ← Zig.Float.fmaRtChk p1 p2 p3
                  pure (.br5 i16))
                else (do
                  if p0 == (5 : BitVec 8) then (do
                    let i18 ← pure (Zig.Float.divTruncRt p1 p2)
                    pure (.br5 i18))
                  else (do
                    if p0 == (6 : BitVec 8) then (do
                      let i20 ← pure (Zig.Float.divFloorRt p1 p2)
                      pure (.br5 i20))
                    else (do
                      if p0 == (7 : BitVec 8) then (do
                        let i22 ← Zig.Float.remRtChk p1 p2
                        pure (.br5 i22))
                      else (do
                        if p0 == (8 : BitVec 8) then (do
                          let i24 ← Zig.Float.modRtChk p1 p2
                          pure (.br5 i24))
                        else (do
                          if p0 == (9 : BitVec 8) then (do
                            let i26 ← pure (Zig.Float.sqrt p1)
                            pure (.br5 i26))
                          else (do
                            if p0 == (10 : BitVec 8) then (do
                              let i28 ← Zig.Float.floorRtLegacyChk p1
                              pure (.br5 i28))
                            else (do
                              if p0 == (11 : BitVec 8) then (do
                                let i30 ← Zig.Float.ceilRtLegacyChk p1
                                pure (.br5 i30))
                              else (do
                                if p0 == (12 : BitVec 8) then (do
                                  let i32 ← Zig.Float.truncChk p1
                                  pure (.br5 i32))
                                else (do
                                  if p0 == (13 : BitVec 8) then (do
                                    let i34 ← Zig.Float.roundChk p1
                                    pure (.br5 i34))
                                  else (do
                                    if p0 == (14 : BitVec 8) then (do
                                      let i36 ← pure (Zig.Float.abs p1)
                                      pure (.br5 i36))
                                    else (do
                                      if p0 == (15 : BitVec 8) then (do
                                        let i38 ← pure (Zig.Float.neg p1)
                                        pure (.br5 i38))
                                      else (do
                                        if p0 == (16 : BitVec 8) then (do
                                          let i40 ← Zig.Float.minChk p1 p2
                                          pure (.br5 i40))
                                        else (do
                                          if p0 == (17 : BitVec 8) then (do
                                            let i42 ← Zig.Float.maxChk p1 p2
                                            pure (.br5 i42))
                                          else (do
                                            if p0 == (18 : BitVec 8) then (do
                                              let i44 ← pure (Zig.Float.libm .sin p1)
                                              pure (.br5 i44))
                                            else (do
                                              if p0 == (19 : BitVec 8) then (do
                                                let i46 ← pure (Zig.Float.libm .cos p1)
                                                pure (.br5 i46))
                                              else (do
                                                if p0 == (20 : BitVec 8) then (do
                                                  let i48 ← pure (Zig.Float.libm .tan p1)
                                                  pure (.br5 i48))
                                                else (do
                                                  if p0 == (21 : BitVec 8) then (do
                                                    let i50 ← pure (Zig.Float.libm .exp p1)
                                                    pure (.br5 i50))
                                                  else (do
                                                    if p0 == (22 : BitVec 8) then (do
                                                      let i52 ← pure (Zig.Float.libm .exp2 p1)
                                                      pure (.br5 i52))
                                                    else (do
                                                      if p0 == (23 : BitVec 8) then (do
                                                        let i54 ← pure (Zig.Float.libm .log p1)
                                                        pure (.br5 i54))
                                                      else (do
                                                        if p0 == (24 : BitVec 8) then (do
                                                          let i56 ← pure (Zig.Float.libm .log2 p1)
                                                          pure (.br5 i56))
                                                        else (do
                                                          if p0 == (25 : BitVec 8) then (do
                                                            let i58 ← pure (Zig.Float.libm .log10 p1)
                                                            pure (.br5 i58))
                                                          else (do
                                                            pure (.br5 p1)))))))))))))))))))))))))))) : Zig.M op16Locals op16Exit) with
      | .br5 v5 => (do
        pure (.br4 v5))
      | e => pure e) : Zig.M op16Locals op16Exit) with
    | .br4 v4 => (do
      pure (.ret v4))
    | e => pure e) : Zig.M op16Locals op16Exit).run' (default : op16Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure op32Locals where
  deriving Inhabited

inductive op32Exit where
  | ret (v : Zig.F32)
  | br5 (v : Zig.F32)
  | br4 (v : Zig.F32)

def op32 (p0 : BitVec 8) (p1 : Zig.F32) (p2 : Zig.F32) (p3 : Zig.F32) : Zig.Result (Zig.F32) := do
  let e ← ((do
    match ← ((do
      match ← ((do
        if p0 == (0 : BitVec 8) then (do
          let i8 ← pure (Zig.Float.add p1 p2)
          pure (.br5 i8))
        else (do
          if p0 == (1 : BitVec 8) then (do
            let i10 ← pure (Zig.Float.sub p1 p2)
            pure (.br5 i10))
          else (do
            if p0 == (2 : BitVec 8) then (do
              let i12 ← pure (Zig.Float.mulRt p1 p2)
              pure (.br5 i12))
            else (do
              if p0 == (3 : BitVec 8) then (do
                let i14 ← pure (Zig.Float.divRt p1 p2)
                pure (.br5 i14))
              else (do
                if p0 == (4 : BitVec 8) then (do
                  let i16 ← Zig.Float.fmaRtChk p1 p2 p3
                  pure (.br5 i16))
                else (do
                  if p0 == (5 : BitVec 8) then (do
                    let i18 ← pure (Zig.Float.divTruncRt p1 p2)
                    pure (.br5 i18))
                  else (do
                    if p0 == (6 : BitVec 8) then (do
                      let i20 ← pure (Zig.Float.divFloorRt p1 p2)
                      pure (.br5 i20))
                    else (do
                      if p0 == (7 : BitVec 8) then (do
                        let i22 ← Zig.Float.remRtChk p1 p2
                        pure (.br5 i22))
                      else (do
                        if p0 == (8 : BitVec 8) then (do
                          let i24 ← Zig.Float.modRtChk p1 p2
                          pure (.br5 i24))
                        else (do
                          if p0 == (9 : BitVec 8) then (do
                            let i26 ← pure (Zig.Float.sqrt p1)
                            pure (.br5 i26))
                          else (do
                            if p0 == (10 : BitVec 8) then (do
                              let i28 ← Zig.Float.floorRtLegacyChk p1
                              pure (.br5 i28))
                            else (do
                              if p0 == (11 : BitVec 8) then (do
                                let i30 ← Zig.Float.ceilRtLegacyChk p1
                                pure (.br5 i30))
                              else (do
                                if p0 == (12 : BitVec 8) then (do
                                  let i32 ← Zig.Float.truncChk p1
                                  pure (.br5 i32))
                                else (do
                                  if p0 == (13 : BitVec 8) then (do
                                    let i34 ← Zig.Float.roundChk p1
                                    pure (.br5 i34))
                                  else (do
                                    if p0 == (14 : BitVec 8) then (do
                                      let i36 ← pure (Zig.Float.abs p1)
                                      pure (.br5 i36))
                                    else (do
                                      if p0 == (15 : BitVec 8) then (do
                                        let i38 ← pure (Zig.Float.neg p1)
                                        pure (.br5 i38))
                                      else (do
                                        if p0 == (16 : BitVec 8) then (do
                                          let i40 ← Zig.Float.minChk p1 p2
                                          pure (.br5 i40))
                                        else (do
                                          if p0 == (17 : BitVec 8) then (do
                                            let i42 ← Zig.Float.maxChk p1 p2
                                            pure (.br5 i42))
                                          else (do
                                            if p0 == (18 : BitVec 8) then (do
                                              let i44 ← pure (Zig.Float.libm .sin p1)
                                              pure (.br5 i44))
                                            else (do
                                              if p0 == (19 : BitVec 8) then (do
                                                let i46 ← pure (Zig.Float.libm .cos p1)
                                                pure (.br5 i46))
                                              else (do
                                                if p0 == (20 : BitVec 8) then (do
                                                  let i48 ← pure (Zig.Float.libm .tan p1)
                                                  pure (.br5 i48))
                                                else (do
                                                  if p0 == (21 : BitVec 8) then (do
                                                    let i50 ← pure (Zig.Float.libm .exp p1)
                                                    pure (.br5 i50))
                                                  else (do
                                                    if p0 == (22 : BitVec 8) then (do
                                                      let i52 ← pure (Zig.Float.libm .exp2 p1)
                                                      pure (.br5 i52))
                                                    else (do
                                                      if p0 == (23 : BitVec 8) then (do
                                                        let i54 ← pure (Zig.Float.libm .log p1)
                                                        pure (.br5 i54))
                                                      else (do
                                                        if p0 == (24 : BitVec 8) then (do
                                                          let i56 ← pure (Zig.Float.libm .log2 p1)
                                                          pure (.br5 i56))
                                                        else (do
                                                          if p0 == (25 : BitVec 8) then (do
                                                            let i58 ← pure (Zig.Float.libm .log10 p1)
                                                            pure (.br5 i58))
                                                          else (do
                                                            pure (.br5 p1)))))))))))))))))))))))))))) : Zig.M op32Locals op32Exit) with
      | .br5 v5 => (do
        pure (.br4 v5))
      | e => pure e) : Zig.M op32Locals op32Exit) with
    | .br4 v4 => (do
      pure (.ret v4))
    | e => pure e) : Zig.M op32Locals op32Exit).run' (default : op32Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure op64Locals where
  deriving Inhabited

inductive op64Exit where
  | ret (v : Zig.F64)
  | br5 (v : Zig.F64)
  | br4 (v : Zig.F64)

def op64 (p0 : BitVec 8) (p1 : Zig.F64) (p2 : Zig.F64) (p3 : Zig.F64) : Zig.Result (Zig.F64) := do
  let e ← ((do
    match ← ((do
      match ← ((do
        if p0 == (0 : BitVec 8) then (do
          let i8 ← pure (Zig.Float.add p1 p2)
          pure (.br5 i8))
        else (do
          if p0 == (1 : BitVec 8) then (do
            let i10 ← pure (Zig.Float.sub p1 p2)
            pure (.br5 i10))
          else (do
            if p0 == (2 : BitVec 8) then (do
              let i12 ← pure (Zig.Float.mulRt p1 p2)
              pure (.br5 i12))
            else (do
              if p0 == (3 : BitVec 8) then (do
                let i14 ← pure (Zig.Float.divRt p1 p2)
                pure (.br5 i14))
              else (do
                if p0 == (4 : BitVec 8) then (do
                  let i16 ← Zig.Float.fmaRtChk p1 p2 p3
                  pure (.br5 i16))
                else (do
                  if p0 == (5 : BitVec 8) then (do
                    let i18 ← pure (Zig.Float.divTruncRt p1 p2)
                    pure (.br5 i18))
                  else (do
                    if p0 == (6 : BitVec 8) then (do
                      let i20 ← pure (Zig.Float.divFloorRt p1 p2)
                      pure (.br5 i20))
                    else (do
                      if p0 == (7 : BitVec 8) then (do
                        let i22 ← Zig.Float.remRtChk p1 p2
                        pure (.br5 i22))
                      else (do
                        if p0 == (8 : BitVec 8) then (do
                          let i24 ← Zig.Float.modRtChk p1 p2
                          pure (.br5 i24))
                        else (do
                          if p0 == (9 : BitVec 8) then (do
                            let i26 ← pure (Zig.Float.sqrt p1)
                            pure (.br5 i26))
                          else (do
                            if p0 == (10 : BitVec 8) then (do
                              let i28 ← Zig.Float.floorRtLegacyChk p1
                              pure (.br5 i28))
                            else (do
                              if p0 == (11 : BitVec 8) then (do
                                let i30 ← Zig.Float.ceilRtLegacyChk p1
                                pure (.br5 i30))
                              else (do
                                if p0 == (12 : BitVec 8) then (do
                                  let i32 ← Zig.Float.truncChk p1
                                  pure (.br5 i32))
                                else (do
                                  if p0 == (13 : BitVec 8) then (do
                                    let i34 ← Zig.Float.roundChk p1
                                    pure (.br5 i34))
                                  else (do
                                    if p0 == (14 : BitVec 8) then (do
                                      let i36 ← pure (Zig.Float.abs p1)
                                      pure (.br5 i36))
                                    else (do
                                      if p0 == (15 : BitVec 8) then (do
                                        let i38 ← pure (Zig.Float.neg p1)
                                        pure (.br5 i38))
                                      else (do
                                        if p0 == (16 : BitVec 8) then (do
                                          let i40 ← Zig.Float.minChk p1 p2
                                          pure (.br5 i40))
                                        else (do
                                          if p0 == (17 : BitVec 8) then (do
                                            let i42 ← Zig.Float.maxChk p1 p2
                                            pure (.br5 i42))
                                          else (do
                                            if p0 == (18 : BitVec 8) then (do
                                              let i44 ← pure (Zig.Float.libm .sin p1)
                                              pure (.br5 i44))
                                            else (do
                                              if p0 == (19 : BitVec 8) then (do
                                                let i46 ← pure (Zig.Float.libm .cos p1)
                                                pure (.br5 i46))
                                              else (do
                                                if p0 == (20 : BitVec 8) then (do
                                                  let i48 ← pure (Zig.Float.libm .tan p1)
                                                  pure (.br5 i48))
                                                else (do
                                                  if p0 == (21 : BitVec 8) then (do
                                                    let i50 ← pure (Zig.Float.libm .exp p1)
                                                    pure (.br5 i50))
                                                  else (do
                                                    if p0 == (22 : BitVec 8) then (do
                                                      let i52 ← pure (Zig.Float.libm .exp2 p1)
                                                      pure (.br5 i52))
                                                    else (do
                                                      if p0 == (23 : BitVec 8) then (do
                                                        let i54 ← pure (Zig.Float.libm .log p1)
                                                        pure (.br5 i54))
                                                      else (do
                                                        if p0 == (24 : BitVec 8) then (do
                                                          let i56 ← pure (Zig.Float.libm .log2 p1)
                                                          pure (.br5 i56))
                                                        else (do
                                                          if p0 == (25 : BitVec 8) then (do
                                                            let i58 ← pure (Zig.Float.libm .log10 p1)
                                                            pure (.br5 i58))
                                                          else (do
                                                            pure (.br5 p1)))))))))))))))))))))))))))) : Zig.M op64Locals op64Exit) with
      | .br5 v5 => (do
        pure (.br4 v5))
      | e => pure e) : Zig.M op64Locals op64Exit) with
    | .br4 v4 => (do
      pure (.ret v4))
    | e => pure e) : Zig.M op64Locals op64Exit).run' (default : op64Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure op80Locals where
  deriving Inhabited

inductive op80Exit where
  | ret (v : Zig.F80)
  | br5 (v : Zig.F80)
  | br4 (v : Zig.F80)

def op80 (p0 : BitVec 8) (p1 : Zig.F80) (p2 : Zig.F80) (p3 : Zig.F80) : Zig.Result (Zig.F80) := do
  let e ← ((do
    match ← ((do
      match ← ((do
        if p0 == (0 : BitVec 8) then (do
          let i8 ← pure (Zig.Float.add p1 p2)
          pure (.br5 i8))
        else (do
          if p0 == (1 : BitVec 8) then (do
            let i10 ← pure (Zig.Float.sub p1 p2)
            pure (.br5 i10))
          else (do
            if p0 == (2 : BitVec 8) then (do
              let i12 ← pure (Zig.Float.mulRt p1 p2)
              pure (.br5 i12))
            else (do
              if p0 == (3 : BitVec 8) then (do
                let i14 ← pure (Zig.Float.divRt p1 p2)
                pure (.br5 i14))
              else (do
                if p0 == (4 : BitVec 8) then (do
                  let i16 ← Zig.Float.fmaRtChk p1 p2 p3
                  pure (.br5 i16))
                else (do
                  if p0 == (5 : BitVec 8) then (do
                    let i18 ← pure (Zig.Float.divTruncRt p1 p2)
                    pure (.br5 i18))
                  else (do
                    if p0 == (6 : BitVec 8) then (do
                      let i20 ← pure (Zig.Float.divFloorRt p1 p2)
                      pure (.br5 i20))
                    else (do
                      if p0 == (7 : BitVec 8) then (do
                        let i22 ← Zig.Float.remRtChk p1 p2
                        pure (.br5 i22))
                      else (do
                        if p0 == (8 : BitVec 8) then (do
                          let i24 ← Zig.Float.modRtChk p1 p2
                          pure (.br5 i24))
                        else (do
                          if p0 == (9 : BitVec 8) then (do
                            let i26 ← pure (Zig.Float.sqrt p1)
                            pure (.br5 i26))
                          else (do
                            if p0 == (10 : BitVec 8) then (do
                              let i28 ← Zig.Float.floorRtLegacyChk p1
                              pure (.br5 i28))
                            else (do
                              if p0 == (11 : BitVec 8) then (do
                                let i30 ← Zig.Float.ceilRtLegacyChk p1
                                pure (.br5 i30))
                              else (do
                                if p0 == (12 : BitVec 8) then (do
                                  let i32 ← Zig.Float.truncChk p1
                                  pure (.br5 i32))
                                else (do
                                  if p0 == (13 : BitVec 8) then (do
                                    let i34 ← Zig.Float.roundChk p1
                                    pure (.br5 i34))
                                  else (do
                                    if p0 == (14 : BitVec 8) then (do
                                      let i36 ← pure (Zig.Float.abs p1)
                                      pure (.br5 i36))
                                    else (do
                                      if p0 == (15 : BitVec 8) then (do
                                        let i38 ← pure (Zig.Float.neg p1)
                                        pure (.br5 i38))
                                      else (do
                                        if p0 == (16 : BitVec 8) then (do
                                          let i40 ← Zig.Float.minChk p1 p2
                                          pure (.br5 i40))
                                        else (do
                                          if p0 == (17 : BitVec 8) then (do
                                            let i42 ← Zig.Float.maxChk p1 p2
                                            pure (.br5 i42))
                                          else (do
                                            if p0 == (18 : BitVec 8) then (do
                                              let i44 ← pure (Zig.Float.libm .sin p1)
                                              pure (.br5 i44))
                                            else (do
                                              if p0 == (19 : BitVec 8) then (do
                                                let i46 ← pure (Zig.Float.libm .cos p1)
                                                pure (.br5 i46))
                                              else (do
                                                if p0 == (20 : BitVec 8) then (do
                                                  let i48 ← pure (Zig.Float.libm .tan p1)
                                                  pure (.br5 i48))
                                                else (do
                                                  if p0 == (21 : BitVec 8) then (do
                                                    let i50 ← pure (Zig.Float.libm .exp p1)
                                                    pure (.br5 i50))
                                                  else (do
                                                    if p0 == (22 : BitVec 8) then (do
                                                      let i52 ← pure (Zig.Float.libm .exp2 p1)
                                                      pure (.br5 i52))
                                                    else (do
                                                      if p0 == (23 : BitVec 8) then (do
                                                        let i54 ← pure (Zig.Float.libm .log p1)
                                                        pure (.br5 i54))
                                                      else (do
                                                        if p0 == (24 : BitVec 8) then (do
                                                          let i56 ← pure (Zig.Float.libm .log2 p1)
                                                          pure (.br5 i56))
                                                        else (do
                                                          if p0 == (25 : BitVec 8) then (do
                                                            let i58 ← pure (Zig.Float.libm .log10 p1)
                                                            pure (.br5 i58))
                                                          else (do
                                                            pure (.br5 p1)))))))))))))))))))))))))))) : Zig.M op80Locals op80Exit) with
      | .br5 v5 => (do
        pure (.br4 v5))
      | e => pure e) : Zig.M op80Locals op80Exit) with
    | .br4 v4 => (do
      pure (.ret v4))
    | e => pure e) : Zig.M op80Locals op80Exit).run' (default : op80Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

end Floatops