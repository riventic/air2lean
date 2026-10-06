#!/usr/bin/env python3
"""Create independent, typed semantic dictionary mutants; compiler execution is root-only.
Compile .defs.lean first. Then .lean must fail specifically at semantic_oracle by native_decide;
syntax/import/tool failures never count as killed. The control must prove the same oracle.
"""
import sys
from pathlib import Path
out = Path(sys.argv[1]); out.mkdir(parents=True, exist_ok=True)
prefix = r'''import ZigLean.Mem.Enc
open Zig
deriving instance DecidableEq for Except
private def d : ErrorDomain := ⟨#["Alpha", "Beta"], by decide, by decide⟩
'''
mutants = {
    "control": "errorEnc d",
    "collapse_names": "{ errorEnc d with encode := fun _ => errBytes (some \"Alpha\") }",
    "standalone_accepts_zero": "{ errorEnc d with decode := fun bs => if bs == errBytes none then pure \"Alpha\" else (errorEnc d).decode bs }",
    "swap_indices": "{ errorEnc d with encode := fun e => #[.errFrag e 1, .errFrag e 0] }",
    "foreign_domain": "{ errorEnc d with decode := fun bs => do let some e ← errOfBytes bs | throw .unspecified; pure e }",
}
# Every mutant changes an actual product dictionary via record override; its oracle combines
# two distinct identities, zero exclusion, partial/mixed fragments, and finite membership.
oracle = r'''
private def semanticOracle : Bool :=
  ((enc.decode (enc.encode "Alpha")).run == some (.ok "Alpha")) &&
  ((enc.decode (enc.encode "Beta")).run == some (.ok "Beta")) &&
  ((enc.decode (errBytes none)).run == some (.error .unspecified)) &&
  ((enc.decode (errBytes (some "Foreign"))).run == some (.error .unspecified)) &&
  ((enc.decode #[.errFrag "Alpha" 0, .errFrag "Beta" 1]).run == some (.error .unspecified))
'''
for name, expression in mutants.items():
    defs = prefix + f"private def enc : Enc ErrName := {expression}\n" + oracle
    (out / f"{name}.defs.lean").write_text(defs)
    (out / f"{name}.lean").write_text(defs + "theorem semantic_oracle : semanticOracle = true := by native_decide\n")
optional = prefix + r'''
private def enc : Enc (Option ErrName) := Enc.optionWith (errorEnc d)
private def semanticOracle : Bool :=
  enc.size == 2 && (enc.encode none == errBytes none) &&
  ((enc.decode (errBytes none)).run == some (.ok none))
'''
(out / "optional_flag.defs.lean").write_text(optional)
(out / "optional_flag.lean").write_text(optional + "theorem semantic_oracle : semanticOracle = true := by native_decide\n")

(out / "mutants.txt").write_text("\n".join([name for name in mutants if name != "control"] + ["optional_flag"]) + "\n")
