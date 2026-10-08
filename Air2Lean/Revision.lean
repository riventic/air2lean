import Lean.Elab.Term

/-!
# Translator revision

Semantic fingerprints (`scripts/semantic-fingerprints.py`, `docs/stable-generation.md`) hash
translator inputs, not emitted Lean. An emitter change can alter every generated body without
changing any input, so the fingerprints must also cover the translator that produced them.

`translator_revision%` is elaborated where it is used (the CLI, `Air2Lean/Main.lean`). It
reads the source of every imported `Air2Lean` module and of the using file itself, and returns
SHA-256 digests of each and of their ordered list together with the Lean version. Lake
rebuilds the using module whenever an imported module changes, so the embedded revision
always describes the translator that was built. Comments and documentation count: the key is
conservative, never a semantic-equivalence claim.
-/

namespace Air2Lean.Revision

private def k : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

@[inline] private def rotr (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-- One 64-byte block at `offset` of `msg`. -/
private def compress (h : Array UInt32) (msg : ByteArray) (offset : Nat) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := Array.mkEmpty 64
  for i in [0:16] do
    let b (j : Nat) : UInt32 := (msg.get! (offset + 4 * i + j)).toUInt32
    w := w.push ((b 0 <<< 24) ||| (b 1 <<< 16) ||| (b 2 <<< 8) ||| b 3)
  for i in [16:64] do
    let x := w[i - 15]!
    let y := w[i - 2]!
    let s0 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
    let s1 := rotr y 17 ^^^ rotr y 19 ^^^ (y >>> 10)
    w := w.push (w[i - 16]! + s0 + w[i - 7]! + s1)
  let mut a := h[0]!; let mut b := h[1]!; let mut c := h[2]!; let mut d := h[3]!
  let mut e := h[4]!; let mut f := h[5]!; let mut g := h[6]!; let mut hh := h[7]!
  for i in [0:64] do
    let t1 := hh + (rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25) + ((e &&& f) ^^^ (~~~e &&& g)) + k[i]! + w[i]!
    let t2 := (rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22) + ((a &&& b) ^^^ (a &&& c) ^^^ (b &&& c))
    hh := g; g := f; f := e; e := d + t1; d := c; c := b; b := a; a := t1 + t2
  return #[h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d, h[4]! + e, h[5]! + f, h[6]! + g, h[7]! + hh]

private def hex2 (n : Nat) : String :=
  let digit (d : Nat) : Char := "0123456789abcdef".toList[d]!
  String.ofList [digit (n / 16 % 16), digit (n % 16)]

/-- Lowercase hexadecimal SHA-256 (FIPS 180-4) of `data`. -/
def sha256 (data : ByteArray) : String := Id.run do
  let bits := data.size * 8
  let mut msg := data.push 0x80
  while msg.size % 64 != 56 do msg := msg.push 0
  for i in [0:8] do msg := msg.push (bits >>> (8 * (7 - i))).toUInt8
  let mut h : Array UInt32 := #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]
  for block in [0:msg.size / 64] do h := compress h msg (64 * block)
  return String.join (h.toList.map fun (x : UInt32) =>
    hex2 (x >>> 24).toNat ++ hex2 ((x >>> 16) % 256).toNat ++ hex2 ((x >>> 8) % 256).toNat ++
      hex2 (x % 256).toNat)

/-- `revision` digests `"<lean version>\n"` followed by `"<module> <sha256>\n"` for each
module in name order. Recomputable with `hashlib` from `modules`. -/
structure Translator where
  lean : String
  modules : Array (String × String)
  revision : String
  deriving Inhabited

def Translator.of (lean : String) (sources : Array (String × ByteArray)) : Translator :=
  let modules := (sources.map fun (m, bytes) => (m, sha256 bytes)).qsort (fun a b => a.1 < b.1)
  let listing := lean ++ "\n" ++ String.join (modules.toList.map fun (m, h) => s!"{m} {h}\n")
  { lean, modules, revision := sha256 listing.toUTF8 }

open Lean Elab Term in
/-- The `Translator` record of the imported `Air2Lean` modules and the current file. -/
elab "translator_revision%" : term => do
  let file ← IO.FS.realPath (System.FilePath.mk (← getFileName))
  let mainModule := (← getEnv).mainModule
  -- `<root>/Air2Lean/Main.lean` for module `Air2Lean.Main`: walk up one directory per component.
  let root := (List.range mainModule.components.length).foldl
    (fun (p : System.FilePath) _ => p.parent.getD p) file
  let imported := (← getEnv).allImportedModuleNames.filter fun m =>
    m.getRoot == `Air2Lean
  let mut sources : Array (String × ByteArray) := #[(mainModule.toString, ← IO.FS.readBinFile file)]
  for m in imported do
    let path := (m.components.foldl (fun (p : System.FilePath) c => p / c.toString) root).withExtension "lean"
    sources := sources.push (m.toString, ← IO.FS.readBinFile path)
  let t := Translator.of Lean.versionString sources
  elabTerm (← `(Translator.mk $(quote t.lean) $(quote t.modules) $(quote t.revision)))
    (some (mkConst ``Translator))

end Air2Lean.Revision
