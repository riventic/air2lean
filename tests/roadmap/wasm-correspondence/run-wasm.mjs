// T05 wasm32 driver: call the exports of a wasm32-freestanding kernels module.
// stdin: {"kernel": [[arg, ...], ...], ...} with decimal u64 strings; stdout: the same shape
// with each result a decimal u64 string, or "trap" when the call trapped (a Zig safety panic
// is `unreachable`). A fresh instance follows every trap: a trap leaves the shadow stack
// pointer and memory as they were mid-call. Any other exception fails the run.
import { readFile } from 'node:fs/promises';
import process from 'node:process';

const [path] = process.argv.slice(2);
if (!path) {
  console.error('usage: node run-wasm.mjs KERNELS.wasm < calls.json');
  process.exit(2);
}
const module = await WebAssembly.compile(await readFile(path));
const fresh = () => WebAssembly.instantiate(module, {});
let instance = await fresh();
let input = '';
for await (const chunk of process.stdin) input += chunk;
const calls = JSON.parse(input);
const out = {};
for (const [name, cases] of Object.entries(calls)) {
  if (typeof instance.exports[name] !== 'function') throw new Error(`missing export ${name}`);
  out[name] = [];
  for (const args of cases) {
    try {
      const r = instance.exports[name](...args.map((a) => BigInt.asUintN(64, BigInt(a))));
      out[name].push(BigInt.asUintN(64, r).toString());
    } catch (e) {
      if (!(e instanceof WebAssembly.RuntimeError)) throw e;
      out[name].push('trap');
      instance = await fresh();
    }
  }
}
process.stdout.write(JSON.stringify(out));
