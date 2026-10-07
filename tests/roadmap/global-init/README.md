# Global initialization and external initial state (L12)

No absent initial value is replaced by a default. The translator either represents a missing
initial value explicitly or rejects it with a stable diagnostic:

| Global | Translation |
|---|---|
| `var`/`const` with a resolved value | its encoding in `mem0` (unchanged) |
| wholly `undefined` (`var x: T = undefined`) | `Zig.Enc.size T` undefined bytes; a load before the first store throws `.unspecified` |
| partly `undefined` (aggregate, optional, error-union or union payload) | rejected, `GLOBAL_FAILURE`: "a partly `undefined` initial value" |
| no `init`, not `extern` (Sema had not resolved it) | rejected: "the AIR file has no initial value" (`STRUCTURE_FAILURE` in `--diagnostics-json`) |
| `extern`, pointer-free and error-free | a field of `ExternInit`; `mem0 (ext : ExternInit)` encodes `ext.<field>` |
| `extern` holding a pointer, union, function or error storage; `extern` with an `init`; unnamed `extern` | rejected, `GLOBAL_FAILURE` |
| `threadlocal` | rejected, `GLOBAL_FAILURE` |

`ExternInit` lists the `extern` globals in block order, which is also `mem0`'s initialization
order (`Mem.ofGlobals` adds the blocks in order, so addresses do not depend on external
values). A proof about program start quantifies over `ext`; its assumptions about external
storage are hypotheses on `ext`. Programs without an `extern` global keep `mem0 : Zig.Mem` and
byte-identical output.

The fixture is hand-written AIR in the exporter's schema (`air/0.16.0`) for:

```zig
extern var counter: u32;
extern const limit: u32;
var scratch: u32 = undefined;
export fn bump() u32 { counter += 1; return counter; }
export fn readLimit() u32 { return limit; }
export fn readScratch() u32 { return scratch; }
export fn setScratch(v: u32) u32 { scratch = v; return scratch; }
```

`GlobalInit/Gen.lean` is its retained translation. `GlobalInit/Proofs.lean` proves, for every
`ext`: the block layout and order of `mem0 ext`, that program start owns `counter` with value
`ext.counter`, that `bump` from program start returns `ext.counter + 1` under the explicit
hypothesis `ext.counter.toNat + 1 < 2 ^ 32`, that `readLimit` returns `ext.limit`, and that
`readScratch` from program start throws `.unspecified`. `test_cli.py` checks the retained
translation byte for byte and the rejections above through the CLI and `--diagnostics-json`.

```sh
lake build air2lean ZigLean.Sep
bash tests/roadmap/global-init/check.sh
```

Scope: the model's contract is that external storage holds a valid encoding of the field type
before the program starts. External writes during the run, symbol interposition, dynamic linking,
TLS and the source/native correspondence of `extern` storage are not modelled; the fixture is
not compiler-exported. A partly `undefined` constant operand of an instruction (not a global
initializer) is outside this check.
