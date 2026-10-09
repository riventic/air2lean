// Run a wasm32-wasi Zig test binary under Node's WASI (preview1); exit with its status.
import { readFile } from 'node:fs/promises';
import { WASI } from 'node:wasi';
import process from 'node:process';

const [path, ...args] = process.argv.slice(2);
if (!path) {
  console.error('usage: node run-wasi.mjs TEST.wasm [ARGS...]');
  process.exit(2);
}
const wasi = new WASI({ version: 'preview1', args: [path, ...args], env: {}, returnOnExit: true });
const module = await WebAssembly.compile(await readFile(path));
const instance = await WebAssembly.instantiate(module, wasi.getImportObject());
process.exit(wasi.start(instance));
