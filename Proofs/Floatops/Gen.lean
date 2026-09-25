import ZigLean


namespace Floatops

structure cmp64Locals where
  m : BitVec 8
  deriving Inhabited

inductive cmp64Exit where
  | ret (v : BitVec 8)
  | br7
  | br18
  | br29
  | br40
  | br51
  | br62

def cmp64 (p0 : Zig.F64) (p1 : Zig.F64) : Zig.Result (BitVec 8) := do
  let e ← ((do
    modify (fun s => { s with m := (0 : BitVec 8) })
    match ← ((do
      let i8 ← pure (Zig.Float.lt p0 p1)
      if i8 then (do
        let i10 ← pure ((← get).m)
        let i12 ← pure (i10 ||| (1 : BitVec 8))
        modify (fun s => { s with m := i12 })
        pure .br7)
      else (do
        pure .br7)) : Zig.M cmp64Locals cmp64Exit) with
    | .br7 => (do
      match ← ((do
        let i19 ← pure (Zig.Float.le p0 p1)
        if i19 then (do
          let i21 ← pure ((← get).m)
          let i23 ← pure (i21 ||| (2 : BitVec 8))
          modify (fun s => { s with m := i23 })
          pure .br18)
        else (do
          pure .br18)) : Zig.M cmp64Locals cmp64Exit) with
      | .br18 => (do
        match ← ((do
          let i30 ← pure (Zig.Float.eq p0 p1)
          if i30 then (do
            let i32 ← pure ((← get).m)
            let i34 ← pure (i32 ||| (4 : BitVec 8))
            modify (fun s => { s with m := i34 })
            pure .br29)
          else (do
            pure .br29)) : Zig.M cmp64Locals cmp64Exit) with
        | .br29 => (do
          match ← ((do
            let i41 ← pure (Zig.Float.ne p0 p1)
            if i41 then (do
              let i43 ← pure ((← get).m)
              let i45 ← pure (i43 ||| (8 : BitVec 8))
              modify (fun s => { s with m := i45 })
              pure .br40)
            else (do
              pure .br40)) : Zig.M cmp64Locals cmp64Exit) with
          | .br40 => (do
            match ← ((do
              let i52 ← pure (Zig.Float.ge p0 p1)
              if i52 then (do
                let i54 ← pure ((← get).m)
                let i56 ← pure (i54 ||| (16 : BitVec 8))
                modify (fun s => { s with m := i56 })
                pure .br51)
              else (do
                pure .br51)) : Zig.M cmp64Locals cmp64Exit) with
            | .br51 => (do
              match ← ((do
                let i63 ← pure (Zig.Float.gt p0 p1)
                if i63 then (do
                  let i65 ← pure ((← get).m)
                  let i67 ← pure (i65 ||| (32 : BitVec 8))
                  modify (fun s => { s with m := i67 })
                  pure .br62)
                else (do
                  pure .br62)) : Zig.M cmp64Locals cmp64Exit) with
              | .br62 => (do
                let i73 ← pure ((← get).m)
                pure (.ret i73))
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
  | br8

def divExact64 (p0 : Zig.F64) (p1 : Zig.F64) : Zig.Result (Zig.F64) := do
  let e ← ((do
    let i3 ← pure (Zig.Float.divTrunc p0 p1)
    let i4 ← pure (Zig.Float.floor i3)
    let i5 ← pure (Zig.Float.eq i3 i4)
    match ← ((do
      if i5 then (do
        pure .br8)
      else (do
        throw .panic)) : Zig.M divExact64Locals divExact64Exit) with
    | .br8 => (do
      pure (.ret i3))
    | e => pure e) : Zig.M divExact64Locals divExact64Exit).run' (default : divExact64Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure op128Locals where
  deriving Inhabited

inductive op128Exit where
  | ret (v : Zig.F128)
  | br11 (v : Zig.F128)
  | br5 (v : Zig.F128)

def op128 (p0 : BitVec 8) (p1 : Zig.F128) (p2 : Zig.F128) (p3 : Zig.F128) : Zig.Result (Zig.F128) := do
  let e ← ((do
    match ← ((do
      match ← ((do
        if p0 == (0 : BitVec 8) then (do
          let i13 ← pure (Zig.Float.add p1 p2)
          pure (.br11 i13))
        else (do
          if p0 == (1 : BitVec 8) then (do
            let i16 ← pure (Zig.Float.sub p1 p2)
            pure (.br11 i16))
          else (do
            if p0 == (2 : BitVec 8) then (do
              let i19 ← pure (Zig.Float.mul p1 p2)
              pure (.br11 i19))
            else (do
              if p0 == (3 : BitVec 8) then (do
                let i22 ← pure (Zig.Float.div p1 p2)
                pure (.br11 i22))
              else (do
                if p0 == (4 : BitVec 8) then (do
                  let i24 ← pure (Zig.Float.fma p1 p2 p3)
                  pure (.br11 i24))
                else (do
                  if p0 == (5 : BitVec 8) then (do
                    let i27 ← pure (Zig.Float.divTrunc p1 p2)
                    pure (.br11 i27))
                  else (do
                    if p0 == (6 : BitVec 8) then (do
                      let i30 ← pure (Zig.Float.divFloor p1 p2)
                      pure (.br11 i30))
                    else (do
                      if p0 == (7 : BitVec 8) then (do
                        let i33 ← pure (Zig.Float.rem p1 p2)
                        pure (.br11 i33))
                      else (do
                        if p0 == (8 : BitVec 8) then (do
                          let i36 ← pure (Zig.Float.mod p1 p2)
                          pure (.br11 i36))
                        else (do
                          if p0 == (9 : BitVec 8) then (do
                            let i38 ← pure (Zig.Float.sqrt p1)
                            pure (.br11 i38))
                          else (do
                            if p0 == (10 : BitVec 8) then (do
                              let i40 ← pure (Zig.Float.floor p1)
                              pure (.br11 i40))
                            else (do
                              if p0 == (11 : BitVec 8) then (do
                                let i42 ← pure (Zig.Float.ceil p1)
                                pure (.br11 i42))
                              else (do
                                if p0 == (12 : BitVec 8) then (do
                                  let i44 ← pure (Zig.Float.trunc p1)
                                  pure (.br11 i44))
                                else (do
                                  if p0 == (13 : BitVec 8) then (do
                                    let i46 ← pure (Zig.Float.round p1)
                                    pure (.br11 i46))
                                  else (do
                                    if p0 == (14 : BitVec 8) then (do
                                      let i48 ← pure (Zig.Float.abs p1)
                                      pure (.br11 i48))
                                    else (do
                                      if p0 == (15 : BitVec 8) then (do
                                        let i50 ← pure (Zig.Float.neg p1)
                                        pure (.br11 i50))
                                      else (do
                                        if p0 == (16 : BitVec 8) then (do
                                          let i52 ← pure (Zig.Float.min p1 p2)
                                          pure (.br11 i52))
                                        else (do
                                          if p0 == (17 : BitVec 8) then (do
                                            let i54 ← pure (Zig.Float.max p1 p2)
                                            pure (.br11 i54))
                                          else (do
                                            if p0 == (18 : BitVec 8) then (do
                                              let i56 ← pure (Zig.Float.libm .sin p1)
                                              pure (.br11 i56))
                                            else (do
                                              if p0 == (19 : BitVec 8) then (do
                                                let i58 ← pure (Zig.Float.libm .cos p1)
                                                pure (.br11 i58))
                                              else (do
                                                if p0 == (20 : BitVec 8) then (do
                                                  let i60 ← pure (Zig.Float.libm .tan p1)
                                                  pure (.br11 i60))
                                                else (do
                                                  if p0 == (21 : BitVec 8) then (do
                                                    let i62 ← pure (Zig.Float.libm .exp p1)
                                                    pure (.br11 i62))
                                                  else (do
                                                    if p0 == (22 : BitVec 8) then (do
                                                      let i64 ← pure (Zig.Float.libm .exp2 p1)
                                                      pure (.br11 i64))
                                                    else (do
                                                      if p0 == (23 : BitVec 8) then (do
                                                        let i66 ← pure (Zig.Float.libm .log p1)
                                                        pure (.br11 i66))
                                                      else (do
                                                        if p0 == (24 : BitVec 8) then (do
                                                          let i68 ← pure (Zig.Float.libm .log2 p1)
                                                          pure (.br11 i68))
                                                        else (do
                                                          if p0 == (25 : BitVec 8) then (do
                                                            let i70 ← pure (Zig.Float.libm .log10 p1)
                                                            pure (.br11 i70))
                                                          else (do
                                                            pure (.br11 p1)))))))))))))))))))))))))))) : Zig.M op128Locals op128Exit) with
      | .br11 v11 => (do
        pure (.br5 v11))
      | e => pure e) : Zig.M op128Locals op128Exit) with
    | .br5 v5 => (do
      pure (.ret v5))
    | e => pure e) : Zig.M op128Locals op128Exit).run' (default : op128Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure op16Locals where
  deriving Inhabited

inductive op16Exit where
  | ret (v : Zig.F16)
  | br11 (v : Zig.F16)
  | br5 (v : Zig.F16)

def op16 (p0 : BitVec 8) (p1 : Zig.F16) (p2 : Zig.F16) (p3 : Zig.F16) : Zig.Result (Zig.F16) := do
  let e ← ((do
    match ← ((do
      match ← ((do
        if p0 == (0 : BitVec 8) then (do
          let i13 ← pure (Zig.Float.add p1 p2)
          pure (.br11 i13))
        else (do
          if p0 == (1 : BitVec 8) then (do
            let i16 ← pure (Zig.Float.sub p1 p2)
            pure (.br11 i16))
          else (do
            if p0 == (2 : BitVec 8) then (do
              let i19 ← pure (Zig.Float.mul p1 p2)
              pure (.br11 i19))
            else (do
              if p0 == (3 : BitVec 8) then (do
                let i22 ← pure (Zig.Float.div p1 p2)
                pure (.br11 i22))
              else (do
                if p0 == (4 : BitVec 8) then (do
                  let i24 ← pure (Zig.Float.fma p1 p2 p3)
                  pure (.br11 i24))
                else (do
                  if p0 == (5 : BitVec 8) then (do
                    let i27 ← pure (Zig.Float.divTrunc p1 p2)
                    pure (.br11 i27))
                  else (do
                    if p0 == (6 : BitVec 8) then (do
                      let i30 ← pure (Zig.Float.divFloor p1 p2)
                      pure (.br11 i30))
                    else (do
                      if p0 == (7 : BitVec 8) then (do
                        let i33 ← pure (Zig.Float.rem p1 p2)
                        pure (.br11 i33))
                      else (do
                        if p0 == (8 : BitVec 8) then (do
                          let i36 ← pure (Zig.Float.mod p1 p2)
                          pure (.br11 i36))
                        else (do
                          if p0 == (9 : BitVec 8) then (do
                            let i38 ← pure (Zig.Float.sqrt p1)
                            pure (.br11 i38))
                          else (do
                            if p0 == (10 : BitVec 8) then (do
                              let i40 ← pure (Zig.Float.floor p1)
                              pure (.br11 i40))
                            else (do
                              if p0 == (11 : BitVec 8) then (do
                                let i42 ← pure (Zig.Float.ceil p1)
                                pure (.br11 i42))
                              else (do
                                if p0 == (12 : BitVec 8) then (do
                                  let i44 ← pure (Zig.Float.trunc p1)
                                  pure (.br11 i44))
                                else (do
                                  if p0 == (13 : BitVec 8) then (do
                                    let i46 ← pure (Zig.Float.round p1)
                                    pure (.br11 i46))
                                  else (do
                                    if p0 == (14 : BitVec 8) then (do
                                      let i48 ← pure (Zig.Float.abs p1)
                                      pure (.br11 i48))
                                    else (do
                                      if p0 == (15 : BitVec 8) then (do
                                        let i50 ← pure (Zig.Float.neg p1)
                                        pure (.br11 i50))
                                      else (do
                                        if p0 == (16 : BitVec 8) then (do
                                          let i52 ← pure (Zig.Float.min p1 p2)
                                          pure (.br11 i52))
                                        else (do
                                          if p0 == (17 : BitVec 8) then (do
                                            let i54 ← pure (Zig.Float.max p1 p2)
                                            pure (.br11 i54))
                                          else (do
                                            if p0 == (18 : BitVec 8) then (do
                                              let i56 ← pure (Zig.Float.libm .sin p1)
                                              pure (.br11 i56))
                                            else (do
                                              if p0 == (19 : BitVec 8) then (do
                                                let i58 ← pure (Zig.Float.libm .cos p1)
                                                pure (.br11 i58))
                                              else (do
                                                if p0 == (20 : BitVec 8) then (do
                                                  let i60 ← pure (Zig.Float.libm .tan p1)
                                                  pure (.br11 i60))
                                                else (do
                                                  if p0 == (21 : BitVec 8) then (do
                                                    let i62 ← pure (Zig.Float.libm .exp p1)
                                                    pure (.br11 i62))
                                                  else (do
                                                    if p0 == (22 : BitVec 8) then (do
                                                      let i64 ← pure (Zig.Float.libm .exp2 p1)
                                                      pure (.br11 i64))
                                                    else (do
                                                      if p0 == (23 : BitVec 8) then (do
                                                        let i66 ← pure (Zig.Float.libm .log p1)
                                                        pure (.br11 i66))
                                                      else (do
                                                        if p0 == (24 : BitVec 8) then (do
                                                          let i68 ← pure (Zig.Float.libm .log2 p1)
                                                          pure (.br11 i68))
                                                        else (do
                                                          if p0 == (25 : BitVec 8) then (do
                                                            let i70 ← pure (Zig.Float.libm .log10 p1)
                                                            pure (.br11 i70))
                                                          else (do
                                                            pure (.br11 p1)))))))))))))))))))))))))))) : Zig.M op16Locals op16Exit) with
      | .br11 v11 => (do
        pure (.br5 v11))
      | e => pure e) : Zig.M op16Locals op16Exit) with
    | .br5 v5 => (do
      pure (.ret v5))
    | e => pure e) : Zig.M op16Locals op16Exit).run' (default : op16Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure op32Locals where
  deriving Inhabited

inductive op32Exit where
  | ret (v : Zig.F32)
  | br11 (v : Zig.F32)
  | br5 (v : Zig.F32)

def op32 (p0 : BitVec 8) (p1 : Zig.F32) (p2 : Zig.F32) (p3 : Zig.F32) : Zig.Result (Zig.F32) := do
  let e ← ((do
    match ← ((do
      match ← ((do
        if p0 == (0 : BitVec 8) then (do
          let i13 ← pure (Zig.Float.add p1 p2)
          pure (.br11 i13))
        else (do
          if p0 == (1 : BitVec 8) then (do
            let i16 ← pure (Zig.Float.sub p1 p2)
            pure (.br11 i16))
          else (do
            if p0 == (2 : BitVec 8) then (do
              let i19 ← pure (Zig.Float.mul p1 p2)
              pure (.br11 i19))
            else (do
              if p0 == (3 : BitVec 8) then (do
                let i22 ← pure (Zig.Float.div p1 p2)
                pure (.br11 i22))
              else (do
                if p0 == (4 : BitVec 8) then (do
                  let i24 ← pure (Zig.Float.fma p1 p2 p3)
                  pure (.br11 i24))
                else (do
                  if p0 == (5 : BitVec 8) then (do
                    let i27 ← pure (Zig.Float.divTrunc p1 p2)
                    pure (.br11 i27))
                  else (do
                    if p0 == (6 : BitVec 8) then (do
                      let i30 ← pure (Zig.Float.divFloor p1 p2)
                      pure (.br11 i30))
                    else (do
                      if p0 == (7 : BitVec 8) then (do
                        let i33 ← pure (Zig.Float.rem p1 p2)
                        pure (.br11 i33))
                      else (do
                        if p0 == (8 : BitVec 8) then (do
                          let i36 ← pure (Zig.Float.mod p1 p2)
                          pure (.br11 i36))
                        else (do
                          if p0 == (9 : BitVec 8) then (do
                            let i38 ← pure (Zig.Float.sqrt p1)
                            pure (.br11 i38))
                          else (do
                            if p0 == (10 : BitVec 8) then (do
                              let i40 ← pure (Zig.Float.floor p1)
                              pure (.br11 i40))
                            else (do
                              if p0 == (11 : BitVec 8) then (do
                                let i42 ← pure (Zig.Float.ceil p1)
                                pure (.br11 i42))
                              else (do
                                if p0 == (12 : BitVec 8) then (do
                                  let i44 ← pure (Zig.Float.trunc p1)
                                  pure (.br11 i44))
                                else (do
                                  if p0 == (13 : BitVec 8) then (do
                                    let i46 ← pure (Zig.Float.round p1)
                                    pure (.br11 i46))
                                  else (do
                                    if p0 == (14 : BitVec 8) then (do
                                      let i48 ← pure (Zig.Float.abs p1)
                                      pure (.br11 i48))
                                    else (do
                                      if p0 == (15 : BitVec 8) then (do
                                        let i50 ← pure (Zig.Float.neg p1)
                                        pure (.br11 i50))
                                      else (do
                                        if p0 == (16 : BitVec 8) then (do
                                          let i52 ← pure (Zig.Float.min p1 p2)
                                          pure (.br11 i52))
                                        else (do
                                          if p0 == (17 : BitVec 8) then (do
                                            let i54 ← pure (Zig.Float.max p1 p2)
                                            pure (.br11 i54))
                                          else (do
                                            if p0 == (18 : BitVec 8) then (do
                                              let i56 ← pure (Zig.Float.libm .sin p1)
                                              pure (.br11 i56))
                                            else (do
                                              if p0 == (19 : BitVec 8) then (do
                                                let i58 ← pure (Zig.Float.libm .cos p1)
                                                pure (.br11 i58))
                                              else (do
                                                if p0 == (20 : BitVec 8) then (do
                                                  let i60 ← pure (Zig.Float.libm .tan p1)
                                                  pure (.br11 i60))
                                                else (do
                                                  if p0 == (21 : BitVec 8) then (do
                                                    let i62 ← pure (Zig.Float.libm .exp p1)
                                                    pure (.br11 i62))
                                                  else (do
                                                    if p0 == (22 : BitVec 8) then (do
                                                      let i64 ← pure (Zig.Float.libm .exp2 p1)
                                                      pure (.br11 i64))
                                                    else (do
                                                      if p0 == (23 : BitVec 8) then (do
                                                        let i66 ← pure (Zig.Float.libm .log p1)
                                                        pure (.br11 i66))
                                                      else (do
                                                        if p0 == (24 : BitVec 8) then (do
                                                          let i68 ← pure (Zig.Float.libm .log2 p1)
                                                          pure (.br11 i68))
                                                        else (do
                                                          if p0 == (25 : BitVec 8) then (do
                                                            let i70 ← pure (Zig.Float.libm .log10 p1)
                                                            pure (.br11 i70))
                                                          else (do
                                                            pure (.br11 p1)))))))))))))))))))))))))))) : Zig.M op32Locals op32Exit) with
      | .br11 v11 => (do
        pure (.br5 v11))
      | e => pure e) : Zig.M op32Locals op32Exit) with
    | .br5 v5 => (do
      pure (.ret v5))
    | e => pure e) : Zig.M op32Locals op32Exit).run' (default : op32Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure op64Locals where
  deriving Inhabited

inductive op64Exit where
  | ret (v : Zig.F64)
  | br11 (v : Zig.F64)
  | br5 (v : Zig.F64)

def op64 (p0 : BitVec 8) (p1 : Zig.F64) (p2 : Zig.F64) (p3 : Zig.F64) : Zig.Result (Zig.F64) := do
  let e ← ((do
    match ← ((do
      match ← ((do
        if p0 == (0 : BitVec 8) then (do
          let i13 ← pure (Zig.Float.add p1 p2)
          pure (.br11 i13))
        else (do
          if p0 == (1 : BitVec 8) then (do
            let i16 ← pure (Zig.Float.sub p1 p2)
            pure (.br11 i16))
          else (do
            if p0 == (2 : BitVec 8) then (do
              let i19 ← pure (Zig.Float.mul p1 p2)
              pure (.br11 i19))
            else (do
              if p0 == (3 : BitVec 8) then (do
                let i22 ← pure (Zig.Float.div p1 p2)
                pure (.br11 i22))
              else (do
                if p0 == (4 : BitVec 8) then (do
                  let i24 ← pure (Zig.Float.fma p1 p2 p3)
                  pure (.br11 i24))
                else (do
                  if p0 == (5 : BitVec 8) then (do
                    let i27 ← pure (Zig.Float.divTrunc p1 p2)
                    pure (.br11 i27))
                  else (do
                    if p0 == (6 : BitVec 8) then (do
                      let i30 ← pure (Zig.Float.divFloor p1 p2)
                      pure (.br11 i30))
                    else (do
                      if p0 == (7 : BitVec 8) then (do
                        let i33 ← pure (Zig.Float.rem p1 p2)
                        pure (.br11 i33))
                      else (do
                        if p0 == (8 : BitVec 8) then (do
                          let i36 ← pure (Zig.Float.mod p1 p2)
                          pure (.br11 i36))
                        else (do
                          if p0 == (9 : BitVec 8) then (do
                            let i38 ← pure (Zig.Float.sqrt p1)
                            pure (.br11 i38))
                          else (do
                            if p0 == (10 : BitVec 8) then (do
                              let i40 ← pure (Zig.Float.floor p1)
                              pure (.br11 i40))
                            else (do
                              if p0 == (11 : BitVec 8) then (do
                                let i42 ← pure (Zig.Float.ceil p1)
                                pure (.br11 i42))
                              else (do
                                if p0 == (12 : BitVec 8) then (do
                                  let i44 ← pure (Zig.Float.trunc p1)
                                  pure (.br11 i44))
                                else (do
                                  if p0 == (13 : BitVec 8) then (do
                                    let i46 ← pure (Zig.Float.round p1)
                                    pure (.br11 i46))
                                  else (do
                                    if p0 == (14 : BitVec 8) then (do
                                      let i48 ← pure (Zig.Float.abs p1)
                                      pure (.br11 i48))
                                    else (do
                                      if p0 == (15 : BitVec 8) then (do
                                        let i50 ← pure (Zig.Float.neg p1)
                                        pure (.br11 i50))
                                      else (do
                                        if p0 == (16 : BitVec 8) then (do
                                          let i52 ← pure (Zig.Float.min p1 p2)
                                          pure (.br11 i52))
                                        else (do
                                          if p0 == (17 : BitVec 8) then (do
                                            let i54 ← pure (Zig.Float.max p1 p2)
                                            pure (.br11 i54))
                                          else (do
                                            if p0 == (18 : BitVec 8) then (do
                                              let i56 ← pure (Zig.Float.libm .sin p1)
                                              pure (.br11 i56))
                                            else (do
                                              if p0 == (19 : BitVec 8) then (do
                                                let i58 ← pure (Zig.Float.libm .cos p1)
                                                pure (.br11 i58))
                                              else (do
                                                if p0 == (20 : BitVec 8) then (do
                                                  let i60 ← pure (Zig.Float.libm .tan p1)
                                                  pure (.br11 i60))
                                                else (do
                                                  if p0 == (21 : BitVec 8) then (do
                                                    let i62 ← pure (Zig.Float.libm .exp p1)
                                                    pure (.br11 i62))
                                                  else (do
                                                    if p0 == (22 : BitVec 8) then (do
                                                      let i64 ← pure (Zig.Float.libm .exp2 p1)
                                                      pure (.br11 i64))
                                                    else (do
                                                      if p0 == (23 : BitVec 8) then (do
                                                        let i66 ← pure (Zig.Float.libm .log p1)
                                                        pure (.br11 i66))
                                                      else (do
                                                        if p0 == (24 : BitVec 8) then (do
                                                          let i68 ← pure (Zig.Float.libm .log2 p1)
                                                          pure (.br11 i68))
                                                        else (do
                                                          if p0 == (25 : BitVec 8) then (do
                                                            let i70 ← pure (Zig.Float.libm .log10 p1)
                                                            pure (.br11 i70))
                                                          else (do
                                                            pure (.br11 p1)))))))))))))))))))))))))))) : Zig.M op64Locals op64Exit) with
      | .br11 v11 => (do
        pure (.br5 v11))
      | e => pure e) : Zig.M op64Locals op64Exit) with
    | .br5 v5 => (do
      pure (.ret v5))
    | e => pure e) : Zig.M op64Locals op64Exit).run' (default : op64Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure op80Locals where
  deriving Inhabited

inductive op80Exit where
  | ret (v : Zig.F80)
  | br11 (v : Zig.F80)
  | br5 (v : Zig.F80)

def op80 (p0 : BitVec 8) (p1 : Zig.F80) (p2 : Zig.F80) (p3 : Zig.F80) : Zig.Result (Zig.F80) := do
  let e ← ((do
    match ← ((do
      match ← ((do
        if p0 == (0 : BitVec 8) then (do
          let i13 ← pure (Zig.Float.add p1 p2)
          pure (.br11 i13))
        else (do
          if p0 == (1 : BitVec 8) then (do
            let i16 ← pure (Zig.Float.sub p1 p2)
            pure (.br11 i16))
          else (do
            if p0 == (2 : BitVec 8) then (do
              let i19 ← pure (Zig.Float.mul p1 p2)
              pure (.br11 i19))
            else (do
              if p0 == (3 : BitVec 8) then (do
                let i22 ← pure (Zig.Float.div p1 p2)
                pure (.br11 i22))
              else (do
                if p0 == (4 : BitVec 8) then (do
                  let i24 ← pure (Zig.Float.fma p1 p2 p3)
                  pure (.br11 i24))
                else (do
                  if p0 == (5 : BitVec 8) then (do
                    let i27 ← pure (Zig.Float.divTrunc p1 p2)
                    pure (.br11 i27))
                  else (do
                    if p0 == (6 : BitVec 8) then (do
                      let i30 ← pure (Zig.Float.divFloor p1 p2)
                      pure (.br11 i30))
                    else (do
                      if p0 == (7 : BitVec 8) then (do
                        let i33 ← pure (Zig.Float.rem p1 p2)
                        pure (.br11 i33))
                      else (do
                        if p0 == (8 : BitVec 8) then (do
                          let i36 ← pure (Zig.Float.mod p1 p2)
                          pure (.br11 i36))
                        else (do
                          if p0 == (9 : BitVec 8) then (do
                            let i38 ← pure (Zig.Float.sqrt p1)
                            pure (.br11 i38))
                          else (do
                            if p0 == (10 : BitVec 8) then (do
                              let i40 ← pure (Zig.Float.floor p1)
                              pure (.br11 i40))
                            else (do
                              if p0 == (11 : BitVec 8) then (do
                                let i42 ← pure (Zig.Float.ceil p1)
                                pure (.br11 i42))
                              else (do
                                if p0 == (12 : BitVec 8) then (do
                                  let i44 ← pure (Zig.Float.trunc p1)
                                  pure (.br11 i44))
                                else (do
                                  if p0 == (13 : BitVec 8) then (do
                                    let i46 ← pure (Zig.Float.round p1)
                                    pure (.br11 i46))
                                  else (do
                                    if p0 == (14 : BitVec 8) then (do
                                      let i48 ← pure (Zig.Float.abs p1)
                                      pure (.br11 i48))
                                    else (do
                                      if p0 == (15 : BitVec 8) then (do
                                        let i50 ← pure (Zig.Float.neg p1)
                                        pure (.br11 i50))
                                      else (do
                                        if p0 == (16 : BitVec 8) then (do
                                          let i52 ← pure (Zig.Float.min p1 p2)
                                          pure (.br11 i52))
                                        else (do
                                          if p0 == (17 : BitVec 8) then (do
                                            let i54 ← pure (Zig.Float.max p1 p2)
                                            pure (.br11 i54))
                                          else (do
                                            if p0 == (18 : BitVec 8) then (do
                                              let i56 ← pure (Zig.Float.libm .sin p1)
                                              pure (.br11 i56))
                                            else (do
                                              if p0 == (19 : BitVec 8) then (do
                                                let i58 ← pure (Zig.Float.libm .cos p1)
                                                pure (.br11 i58))
                                              else (do
                                                if p0 == (20 : BitVec 8) then (do
                                                  let i60 ← pure (Zig.Float.libm .tan p1)
                                                  pure (.br11 i60))
                                                else (do
                                                  if p0 == (21 : BitVec 8) then (do
                                                    let i62 ← pure (Zig.Float.libm .exp p1)
                                                    pure (.br11 i62))
                                                  else (do
                                                    if p0 == (22 : BitVec 8) then (do
                                                      let i64 ← pure (Zig.Float.libm .exp2 p1)
                                                      pure (.br11 i64))
                                                    else (do
                                                      if p0 == (23 : BitVec 8) then (do
                                                        let i66 ← pure (Zig.Float.libm .log p1)
                                                        pure (.br11 i66))
                                                      else (do
                                                        if p0 == (24 : BitVec 8) then (do
                                                          let i68 ← pure (Zig.Float.libm .log2 p1)
                                                          pure (.br11 i68))
                                                        else (do
                                                          if p0 == (25 : BitVec 8) then (do
                                                            let i70 ← pure (Zig.Float.libm .log10 p1)
                                                            pure (.br11 i70))
                                                          else (do
                                                            pure (.br11 p1)))))))))))))))))))))))))))) : Zig.M op80Locals op80Exit) with
      | .br11 v11 => (do
        pure (.br5 v11))
      | e => pure e) : Zig.M op80Locals op80Exit) with
    | .br5 v5 => (do
      pure (.ret v5))
    | e => pure e) : Zig.M op80Locals op80Exit).run' (default : op80Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

end Floatops