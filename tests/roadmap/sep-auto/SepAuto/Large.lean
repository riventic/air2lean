import ZigLean.Sep.Full.Auto

/-!
# `fsym` on a large generated body (`docs/proof-automation.md`)

`fsym` normalizes only the head of the program at each step (`Auto.lazyMethods`): a bind's
continuation is left as it is until it is the head. Normalizing the whole body at every step
would push each continuation into both branches of every `if` before it (`ite_bind`): `2 ^ 64`
copies for `ite_chain`. The programs are written in the shape the translator generates (one
`let` per instruction, labelled blocks as `match ← (…) with | .br => … | e => pure e`).
-/

namespace SepAuto.Large

open Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto

/-- 64 instructions, each an `if` that the facts decide. -/
def iteChain (x : BitVec 64) : MemM (BitVec 64) := do
  let a0 ← pure x
  let a1 ← if a0.toNat < 100 then pure a0 else pure (a0 + 1)
  let a2 ← if a1.toNat < 100 then pure a1 else pure (a1 + 1)
  let a3 ← if a2.toNat < 100 then pure a2 else pure (a2 + 1)
  let a4 ← if a3.toNat < 100 then pure a3 else pure (a3 + 1)
  let a5 ← if a4.toNat < 100 then pure a4 else pure (a4 + 1)
  let a6 ← if a5.toNat < 100 then pure a5 else pure (a5 + 1)
  let a7 ← if a6.toNat < 100 then pure a6 else pure (a6 + 1)
  let a8 ← if a7.toNat < 100 then pure a7 else pure (a7 + 1)
  let a9 ← if a8.toNat < 100 then pure a8 else pure (a8 + 1)
  let a10 ← if a9.toNat < 100 then pure a9 else pure (a9 + 1)
  let a11 ← if a10.toNat < 100 then pure a10 else pure (a10 + 1)
  let a12 ← if a11.toNat < 100 then pure a11 else pure (a11 + 1)
  let a13 ← if a12.toNat < 100 then pure a12 else pure (a12 + 1)
  let a14 ← if a13.toNat < 100 then pure a13 else pure (a13 + 1)
  let a15 ← if a14.toNat < 100 then pure a14 else pure (a14 + 1)
  let a16 ← if a15.toNat < 100 then pure a15 else pure (a15 + 1)
  let a17 ← if a16.toNat < 100 then pure a16 else pure (a16 + 1)
  let a18 ← if a17.toNat < 100 then pure a17 else pure (a17 + 1)
  let a19 ← if a18.toNat < 100 then pure a18 else pure (a18 + 1)
  let a20 ← if a19.toNat < 100 then pure a19 else pure (a19 + 1)
  let a21 ← if a20.toNat < 100 then pure a20 else pure (a20 + 1)
  let a22 ← if a21.toNat < 100 then pure a21 else pure (a21 + 1)
  let a23 ← if a22.toNat < 100 then pure a22 else pure (a22 + 1)
  let a24 ← if a23.toNat < 100 then pure a23 else pure (a23 + 1)
  let a25 ← if a24.toNat < 100 then pure a24 else pure (a24 + 1)
  let a26 ← if a25.toNat < 100 then pure a25 else pure (a25 + 1)
  let a27 ← if a26.toNat < 100 then pure a26 else pure (a26 + 1)
  let a28 ← if a27.toNat < 100 then pure a27 else pure (a27 + 1)
  let a29 ← if a28.toNat < 100 then pure a28 else pure (a28 + 1)
  let a30 ← if a29.toNat < 100 then pure a29 else pure (a29 + 1)
  let a31 ← if a30.toNat < 100 then pure a30 else pure (a30 + 1)
  let a32 ← if a31.toNat < 100 then pure a31 else pure (a31 + 1)
  let a33 ← if a32.toNat < 100 then pure a32 else pure (a32 + 1)
  let a34 ← if a33.toNat < 100 then pure a33 else pure (a33 + 1)
  let a35 ← if a34.toNat < 100 then pure a34 else pure (a34 + 1)
  let a36 ← if a35.toNat < 100 then pure a35 else pure (a35 + 1)
  let a37 ← if a36.toNat < 100 then pure a36 else pure (a36 + 1)
  let a38 ← if a37.toNat < 100 then pure a37 else pure (a37 + 1)
  let a39 ← if a38.toNat < 100 then pure a38 else pure (a38 + 1)
  let a40 ← if a39.toNat < 100 then pure a39 else pure (a39 + 1)
  let a41 ← if a40.toNat < 100 then pure a40 else pure (a40 + 1)
  let a42 ← if a41.toNat < 100 then pure a41 else pure (a41 + 1)
  let a43 ← if a42.toNat < 100 then pure a42 else pure (a42 + 1)
  let a44 ← if a43.toNat < 100 then pure a43 else pure (a43 + 1)
  let a45 ← if a44.toNat < 100 then pure a44 else pure (a44 + 1)
  let a46 ← if a45.toNat < 100 then pure a45 else pure (a45 + 1)
  let a47 ← if a46.toNat < 100 then pure a46 else pure (a46 + 1)
  let a48 ← if a47.toNat < 100 then pure a47 else pure (a47 + 1)
  let a49 ← if a48.toNat < 100 then pure a48 else pure (a48 + 1)
  let a50 ← if a49.toNat < 100 then pure a49 else pure (a49 + 1)
  let a51 ← if a50.toNat < 100 then pure a50 else pure (a50 + 1)
  let a52 ← if a51.toNat < 100 then pure a51 else pure (a51 + 1)
  let a53 ← if a52.toNat < 100 then pure a52 else pure (a52 + 1)
  let a54 ← if a53.toNat < 100 then pure a53 else pure (a53 + 1)
  let a55 ← if a54.toNat < 100 then pure a54 else pure (a54 + 1)
  let a56 ← if a55.toNat < 100 then pure a55 else pure (a55 + 1)
  let a57 ← if a56.toNat < 100 then pure a56 else pure (a56 + 1)
  let a58 ← if a57.toNat < 100 then pure a57 else pure (a57 + 1)
  let a59 ← if a58.toNat < 100 then pure a58 else pure (a58 + 1)
  let a60 ← if a59.toNat < 100 then pure a59 else pure (a59 + 1)
  let a61 ← if a60.toNat < 100 then pure a60 else pure (a60 + 1)
  let a62 ← if a61.toNat < 100 then pure a61 else pure (a61 + 1)
  let a63 ← if a62.toNat < 100 then pure a62 else pure (a62 + 1)
  let a64 ← if a63.toNat < 100 then pure a63 else pure (a63 + 1)
  pure a64

theorem ite_chain (x : BitVec 64) (h : x.toNat < 100) :
    FTotalTriple emp (iteChain x) (fun r => ⟪r = x⟫) := by
  unfold iteChain
  fsym

/-- The exits of a generated function's labelled blocks. -/
inductive Exit where
  | br
  | ret (v : BitVec 64)

/-- 32 nested labelled blocks, each after a checked increment, with an early exit. -/
def labelChain (x : BitVec 64) : MemM (BitVec 64) := do
  let a0 ← pure x
  let a1 ← StateT.lift (Zig.add false a0 1)
  match ← (if a1.toNat < 1000 then pure Exit.br else pure (Exit.ret a1) : MemM Exit) with
  | .br => (do
    let a2 ← StateT.lift (Zig.add false a1 1)
    match ← (if a2.toNat < 1000 then pure Exit.br else pure (Exit.ret a2) : MemM Exit) with
    | .br => (do
      let a3 ← StateT.lift (Zig.add false a2 1)
      match ← (if a3.toNat < 1000 then pure Exit.br else pure (Exit.ret a3) : MemM Exit) with
      | .br => (do
        let a4 ← StateT.lift (Zig.add false a3 1)
        match ← (if a4.toNat < 1000 then pure Exit.br else pure (Exit.ret a4) : MemM Exit) with
        | .br => (do
          let a5 ← StateT.lift (Zig.add false a4 1)
          match ← (if a5.toNat < 1000 then pure Exit.br else pure (Exit.ret a5) : MemM Exit) with
          | .br => (do
            let a6 ← StateT.lift (Zig.add false a5 1)
            match ← (if a6.toNat < 1000 then pure Exit.br else pure (Exit.ret a6) : MemM Exit) with
            | .br => (do
              let a7 ← StateT.lift (Zig.add false a6 1)
              match ← (if a7.toNat < 1000 then pure Exit.br else pure (Exit.ret a7) : MemM Exit) with
              | .br => (do
                let a8 ← StateT.lift (Zig.add false a7 1)
                match ← (if a8.toNat < 1000 then pure Exit.br else pure (Exit.ret a8) : MemM Exit) with
                | .br => (do
                  let a9 ← StateT.lift (Zig.add false a8 1)
                  match ← (if a9.toNat < 1000 then pure Exit.br else pure (Exit.ret a9) : MemM Exit) with
                  | .br => (do
                    let a10 ← StateT.lift (Zig.add false a9 1)
                    match ← (if a10.toNat < 1000 then pure Exit.br else pure (Exit.ret a10) : MemM Exit) with
                    | .br => (do
                      let a11 ← StateT.lift (Zig.add false a10 1)
                      match ← (if a11.toNat < 1000 then pure Exit.br else pure (Exit.ret a11) : MemM Exit) with
                      | .br => (do
                        let a12 ← StateT.lift (Zig.add false a11 1)
                        match ← (if a12.toNat < 1000 then pure Exit.br else pure (Exit.ret a12) : MemM Exit) with
                        | .br => (do
                          let a13 ← StateT.lift (Zig.add false a12 1)
                          match ← (if a13.toNat < 1000 then pure Exit.br else pure (Exit.ret a13) : MemM Exit) with
                          | .br => (do
                            let a14 ← StateT.lift (Zig.add false a13 1)
                            match ← (if a14.toNat < 1000 then pure Exit.br else pure (Exit.ret a14) : MemM Exit) with
                            | .br => (do
                              let a15 ← StateT.lift (Zig.add false a14 1)
                              match ← (if a15.toNat < 1000 then pure Exit.br else pure (Exit.ret a15) : MemM Exit) with
                              | .br => (do
                                let a16 ← StateT.lift (Zig.add false a15 1)
                                match ← (if a16.toNat < 1000 then pure Exit.br else pure (Exit.ret a16) : MemM Exit) with
                                | .br => (do
                                  let a17 ← StateT.lift (Zig.add false a16 1)
                                  match ← (if a17.toNat < 1000 then pure Exit.br else pure (Exit.ret a17) : MemM Exit) with
                                  | .br => (do
                                    let a18 ← StateT.lift (Zig.add false a17 1)
                                    match ← (if a18.toNat < 1000 then pure Exit.br else pure (Exit.ret a18) : MemM Exit) with
                                    | .br => (do
                                      let a19 ← StateT.lift (Zig.add false a18 1)
                                      match ← (if a19.toNat < 1000 then pure Exit.br else pure (Exit.ret a19) : MemM Exit) with
                                      | .br => (do
                                        let a20 ← StateT.lift (Zig.add false a19 1)
                                        match ← (if a20.toNat < 1000 then pure Exit.br else pure (Exit.ret a20) : MemM Exit) with
                                        | .br => (do
                                          let a21 ← StateT.lift (Zig.add false a20 1)
                                          match ← (if a21.toNat < 1000 then pure Exit.br else pure (Exit.ret a21) : MemM Exit) with
                                          | .br => (do
                                            let a22 ← StateT.lift (Zig.add false a21 1)
                                            match ← (if a22.toNat < 1000 then pure Exit.br else pure (Exit.ret a22) : MemM Exit) with
                                            | .br => (do
                                              let a23 ← StateT.lift (Zig.add false a22 1)
                                              match ← (if a23.toNat < 1000 then pure Exit.br else pure (Exit.ret a23) : MemM Exit) with
                                              | .br => (do
                                                let a24 ← StateT.lift (Zig.add false a23 1)
                                                match ← (if a24.toNat < 1000 then pure Exit.br else pure (Exit.ret a24) : MemM Exit) with
                                                | .br => (do
                                                  let a25 ← StateT.lift (Zig.add false a24 1)
                                                  match ← (if a25.toNat < 1000 then pure Exit.br else pure (Exit.ret a25) : MemM Exit) with
                                                  | .br => (do
                                                    let a26 ← StateT.lift (Zig.add false a25 1)
                                                    match ← (if a26.toNat < 1000 then pure Exit.br else pure (Exit.ret a26) : MemM Exit) with
                                                    | .br => (do
                                                      let a27 ← StateT.lift (Zig.add false a26 1)
                                                      match ← (if a27.toNat < 1000 then pure Exit.br else pure (Exit.ret a27) : MemM Exit) with
                                                      | .br => (do
                                                        let a28 ← StateT.lift (Zig.add false a27 1)
                                                        match ← (if a28.toNat < 1000 then pure Exit.br else pure (Exit.ret a28) : MemM Exit) with
                                                        | .br => (do
                                                          let a29 ← StateT.lift (Zig.add false a28 1)
                                                          match ← (if a29.toNat < 1000 then pure Exit.br else pure (Exit.ret a29) : MemM Exit) with
                                                          | .br => (do
                                                            let a30 ← StateT.lift (Zig.add false a29 1)
                                                            match ← (if a30.toNat < 1000 then pure Exit.br else pure (Exit.ret a30) : MemM Exit) with
                                                            | .br => (do
                                                              let a31 ← StateT.lift (Zig.add false a30 1)
                                                              match ← (if a31.toNat < 1000 then pure Exit.br else pure (Exit.ret a31) : MemM Exit) with
                                                              | .br => (do
                                                                let a32 ← StateT.lift (Zig.add false a31 1)
                                                                match ← (if a32.toNat < 1000 then pure Exit.br else pure (Exit.ret a32) : MemM Exit) with
                                                                | .br => (do
                                                                  pure a32)
                                                                | .ret v => pure v)
                                                              | .ret v => pure v)
                                                            | .ret v => pure v)
                                                          | .ret v => pure v)
                                                        | .ret v => pure v)
                                                      | .ret v => pure v)
                                                    | .ret v => pure v)
                                                  | .ret v => pure v)
                                                | .ret v => pure v)
                                              | .ret v => pure v)
                                            | .ret v => pure v)
                                          | .ret v => pure v)
                                        | .ret v => pure v)
                                      | .ret v => pure v)
                                    | .ret v => pure v)
                                  | .ret v => pure v)
                                | .ret v => pure v)
                              | .ret v => pure v)
                            | .ret v => pure v)
                          | .ret v => pure v)
                        | .ret v => pure v)
                      | .ret v => pure v)
                    | .ret v => pure v)
                  | .ret v => pure v)
                | .ret v => pure v)
              | .ret v => pure v)
            | .ret v => pure v)
          | .ret v => pure v)
        | .ret v => pure v)
      | .ret v => pure v)
    | .ret v => pure v)
  | .ret v => pure v

theorem label_chain (x : BitVec 64) (h : x.toNat < 100) :
    FTotalTriple emp (labelChain x) (fun r => ⟪r.toNat = x.toNat + 32⟫) := by
  unfold labelChain
  fsym

end SepAuto.Large
