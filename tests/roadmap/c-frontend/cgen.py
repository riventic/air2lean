#!/usr/bin/env python3
"""Seeded generator of small UB-free C programs for the C front-end harness.

  cgen.py emit START COUNT OUT_DIR [--goto]   # write gen_s<SEED>.c for each seed
  cgen.py light [--seeds N]                   # determinism + structural invariants; no tools

csmith is not installed on the development host and has no local Docker image, so this is
a minimal typed generator in the spirit of tests/roadmap/fuzz/zig_gen.py. Every program
defines `unsigned entry(unsigned a, unsigned b)` (the Q01 input vector applies) and is
UB-free by construction:

  * arithmetic is on `unsigned` (wrapping is defined); `unsigned char` values are narrowed
    explicitly and promoted by C's rules;
  * shift counts are masked with `& 31u`; divisors are `(e | 1u)`; array indices are `& 7u`;
  * signed values appear only through implementation-defined conversions `(int)e` that feed
    comparisons (never signed arithmetic, so no signed overflow);
  * loops have constant trip counts; helper calls are acyclic (callee index < caller index);
  * every global is reset at the start of `entry`, so `entry` is deterministic per input.

Expected values are not computed here: the harness takes them from the C program compiled
natively with UBSan traps, which also rejects any generator bug that introduced UB.
`--goto` adds forward-goto skips (translate-c 0.16 rejects goto; off by default so the
generated population measures the rest of the pipeline).
"""
import argparse
from pathlib import Path
import random
import sys

BIN = ["+", "-", "*", "&", "|", "^"]
CMP = ["<", "<=", ">", ">=", "==", "!="]
ASSIGN = ["=", "+=", "-=", "*=", "^=", "|=", "&="]


class Gen:
    def __init__(self, seed, use_goto=False):
        self.rng = random.Random(seed)
        self.seed = seed
        self.use_goto = use_goto
        self.labels = 0
        self.names = 0
        self.globals = [f"g{i}" for i in range(self.rng.randint(0, 2))]
        self.helpers = []

    def expr(self, scope, depth):
        r = self.rng
        if depth <= 0 or r.random() < 0.3:
            choice = r.random()
            scalars = [v for v in scope if v != "arr"]
            if choice < 0.55 and scalars:
                return r.choice(scalars)
            if choice < 0.7 and "arr" in scope:
                return f"arr[{r.choice([v for v in scope if v != 'arr'] or ['0u'])} & 7u]"
            return f"{r.randrange(0, 1 << r.choice([3, 8, 16, 32]))}u"
        scalars = [v for v in scope if v != "arr"]
        kind = r.randrange(9)
        a, b = self.expr(scalars, depth - 1), self.expr(scalars, depth - 1)
        if kind < 3:
            return f"({a} {r.choice(BIN)} {b})"
        if kind == 3:
            return f"({a} {r.choice(['<<', '>>'])} ({b} & 31u))"
        if kind == 4:
            return f"({a} {r.choice(['/', '%'])} ({b} | 1u))"
        if kind == 5:
            op = r.choice(CMP)
            signed = r.random() < 0.4
            lhs, rhs = (f"(int){a}", f"(int){b}") if signed else (a, b)
            return f"(unsigned)({lhs} {op} {rhs})"
        if kind == 6:
            return f"({self.expr(scalars, depth - 1)} ? {a} : {b})"
        if kind == 7:
            return f"(unsigned)(unsigned char)({a} + {b})"
        if self.helpers:
            name, arity = r.choice(self.helpers)
            args = ", ".join(self.expr(scalars, depth - 1) for _ in range(arity))
            return f"{name}({args})"
        return f"(~{a})"

    def block(self, scope, depth, indent, n):
        lines = []
        scope = list(scope)
        for _ in range(n):
            lines += self.stmt(scope, depth, indent)
        return lines

    def stmt(self, scope, depth, indent):
        r = self.rng
        pad = "    " * indent
        scalars = [v for v in scope if v != "arr"]
        kind = r.randrange(10) if depth > 0 else r.choice([0, 1, 1, 2])
        if kind == 0:
            self.names += 1
            name = f"v{self.names}"
            line = f"{pad}unsigned {name} = {self.expr(scope, 2)};"
            scope.append(name)
            return [line]
        if kind in (1, 2):
            target = r.choice(scalars)
            if r.random() < 0.3 and "arr" in scope:
                target = f"arr[{self.expr(scalars, 1)} & 7u]"
            return [f"{pad}{target} {r.choice(ASSIGN)} {self.expr(scope, 2)};"]
        if kind == 3:
            return ([f"{pad}if ({self.expr(scope, 2)}) {{"] + self.block(scope, depth - 1, indent + 1, 2)
                    + [f"{pad}}} else {{"] + self.block(scope, depth - 1, indent + 1, 1) + [f"{pad}}}"])
        if kind == 4:
            i = f"i{indent}"
            body = self.block(scope + [i], depth - 1, indent + 1, 2)
            if r.random() < 0.3:
                body.insert(0, f"{pad}    if ({i} == {r.randrange(4)}u) {r.choice(['continue', 'break'])};")
            return [f"{pad}for (unsigned {i} = 0; {i} < {r.randint(1, 5)}u; {i}++) {{"] + body + [f"{pad}}}"]
        if kind == 5:
            lines = [f"{pad}switch ({self.expr(scalars, 1)} & 3u) {{"]
            for case in range(3):
                lines.append(f"{pad}case {case}u: {{")
                lines += self.block(scope, depth - 1, indent + 1, 1)
                lines.append(f"{pad}    break;\n{pad}}}" if r.random() < 0.75 else f"{pad}}}")
            lines += ([f"{pad}default: {{"] + self.block(scope, depth - 1, indent + 1, 1)
                      + [f"{pad}    break;", f"{pad}}}", f"{pad}}}"])
            return lines
        if kind == 6 and "arr" in scope:
            self.names += 1
            p = f"p{self.names}"
            return [f"{pad}{{", f"{pad}    unsigned *{p} = &arr[{self.expr(scalars, 1)} & 7u];",
                    f"{pad}    *{p} {r.choice(ASSIGN[1:])} {self.expr(scalars, 1)};", f"{pad}}}"]
        if kind == 7 and self.globals:
            return [f"{pad}{r.choice(self.globals)} {r.choice(ASSIGN)} {self.expr(scope, 2)};"]
        if kind == 8 and self.use_goto:
            self.labels += 1
            label = f"skip{self.labels}"
            return ([f"{pad}if ({self.expr(scalars, 1)}) goto {label};"] + self.block(scope, 0, indent, 1)
                    + [f"{label}:;"])
        return [f"{pad}{r.choice(scalars)} ^= {self.expr(scope, 1)};"]

    def function(self, name, params, depth):
        scope = list(params)
        body = [f"    unsigned arr[8] = {{{', '.join(f'{self.rng.randrange(256)}u' for _ in range(8))}}};"]
        scope.append("arr")
        body += self.block(scope, depth, 1, self.rng.randint(2, 5))
        scalars = [v for v in scope if v != "arr"]
        result = " ^ ".join(scalars[:2]) + f" ^ arr[{self.rng.randrange(8)}]"
        sig = ", ".join(f"unsigned {p}" for p in params)
        static = "static " if name != "entry" else ""
        return [f"{static}unsigned {name}({sig}) {{"] + body + [f"    return {result};", "}", ""]

    def program(self):
        lines = [f"/* Generated by tests/roadmap/c-frontend/cgen.py from seed {self.seed}; do not edit. */"]
        lines += [f"static unsigned {g};" for g in self.globals] + [""]
        for i in range(self.rng.randint(0, 2)):
            arity = self.rng.randint(1, 2)
            name = f"h{i}"
            lines += self.function(name, [f"x{k}" for k in range(arity)], 2)
            self.helpers.append((name, arity))
        entry = self.function("entry", ["a", "b"], 3)
        resets = [f"    {g} = {self.rng.randrange(100)}u;" for g in self.globals]
        tail = [f"    return {' ^ '.join(['r'] + self.globals)};" if self.globals else None]
        if self.globals:  # wrap: reset globals, call the body, mix the globals into the result
            body_name = "entry_body"
            entry[0] = entry[0].replace("unsigned entry(", f"static unsigned {body_name}(")
            entry += ["unsigned entry(unsigned a, unsigned b) {"] + resets + [
                f"    unsigned r = {body_name}(a, b);"] + tail + ["}", ""]
        return "\n".join(lines + entry)


def emit(seed, out, use_goto=False):
    path = Path(out) / f"gen_s{seed}.c"
    path.write_text(Gen(seed, use_goto).program())
    return path


def cmd_emit(args):
    Path(args.out).mkdir(parents=True, exist_ok=True)
    for seed in range(args.start, args.start + args.count):
        print(emit(seed, args.out, args.goto))
    return 0


def cmd_light(args):
    for seed in range(args.seeds):
        text = Gen(seed).program()
        if text != Gen(seed).program():
            print(f"seed {seed}: nondeterministic generation", file=sys.stderr)
            return 1
        if "unsigned entry(unsigned a, unsigned b) {" not in text or "goto" in text:
            print(f"seed {seed}: missing entry or unexpected goto", file=sys.stderr)
            return 1
        if text.count("{") != text.count("}"):
            print(f"seed {seed}: unbalanced braces", file=sys.stderr)
            return 1
    print(f"cgen light ok: {args.seeds} seeds")
    return 0


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = parser.add_subparsers(dest="cmd", required=True)
    e = sub.add_parser("emit")
    e.add_argument("start", type=int)
    e.add_argument("count", type=int)
    e.add_argument("out")
    e.add_argument("--goto", action="store_true")
    light = sub.add_parser("light")
    light.add_argument("--seeds", type=int, default=200)
    args = parser.parse_args(argv)
    return {"emit": cmd_emit, "light": cmd_light}[args.cmd](args)


if __name__ == "__main__":
    sys.exit(main())
