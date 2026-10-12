#!/usr/bin/env python3
"""Q01 seeded typed Zig program generator, reference evaluator and AST shrinker.

  zig_gen.py light [--seeds N] [--start S]   # generate + typecheck + evaluate; no tools
  zig_gen.py emit SEED OUT_DIR               # write fuzz_s<SEED>.zig, program.json, expected.json
  zig_gen.py lean-checks SEED GEN.lean OUT   # append #guard value checks to a translated file
  zig_gen.py shrink PROGRAM.json --command 'CMD {dir}' OUT_DIR
                                             # reduce a failing program (command exit != 0)

A program is a JSON-serializable AST. `typecheck` states the generator's invariants (scoping,
types, no shadowing, Zig's unused/never-mutated/unreachable-code rules, bounded loops, acyclic
calls); `evaluate` is the Python reference semantics (wrapping arithmetic, left-to-right
evaluation, LIFO defers, errdefer only on error return). Programs exercise pointer aliasing,
globals, defer/errdefer cleanup, tagged unions, casts and nested loops/switches. The `wide` profile
adds u16/u64/i64 arithmetic and a cast table, arrays (also aliased through element pointers),
slices with `for` loops, optionals with `orelse`/capturing `if`, and structs (value copies, field
pointers, pointer-taking helpers). The `core` profile generates exactly the original subset, so its
seeds keep their meaning. The heavy differential (native Zig test, AIR export, translation, Lean
evaluation) is check.sh --heavy.
"""
import argparse
import copy
import json
from pathlib import Path
import random
import shlex
import subprocess
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parent))
from shrink import get_path as _get, nodes as _nodes, with_path as _set  # noqa: E402

INPUTS = [(0, 0), (1, 2), (4294967295, 7), (305419896, 2863311530)]
CORE_SCALARS = ("u32", "i32", "u8")
SCALARS = CORE_SCALARS + ("u16", "u64", "i64")  # what the typechecker accepts; the core profile uses CORE_SCALARS
BITS = {"u32": 32, "i32": 32, "u8": 8, "u16": 16, "u64": 64, "i64": 64}
MAX_LOOP = 4
ARRAY_LEN = 4
FEATURES = ("alias", "global", "defer", "errdefer", "union", "cast", "nested_control")
WIDE_FEATURES = FEATURES + ("wide_int", "array", "slice", "optional", "struct")
PROFILES = {"core": FEATURES, "wide": WIDE_FEATURES}
FIELD_TY = {"x": "u32", "y": "i32"}
# name -> (source type, target type, form); the legacy core casts come first.
CASTS = {"i2u": ("i32", "u32", "bitcast"), "widen8": ("u8", "u32", "widen"), "u2i": ("u32", "i32", "bitcast"),
         "trunc8": ("u32", "u8", "trunc"), "intcast8": ("u32", "u8", "intcast8"),
         "widen16": ("u16", "u32", "widen"), "trunc16": ("u32", "u16", "trunc"),
         "widen64": ("u32", "u64", "widen"), "trunc64": ("u64", "u32", "trunc"),
         "i2l": ("i32", "i64", "widen"), "l2i": ("i64", "i32", "trunc"),
         "u2l": ("u64", "i64", "bitcast"), "l2u": ("i64", "u64", "bitcast"),
         "w8to16": ("u8", "u16", "widen"), "intcast16": ("u32", "u16", "intcast16")}
WIDE_LITS = {"u16": [0, 1, 255, 256, 32768, 65535],
             "u64": [0, 1, 4294967296, 81985529216486895, 18446744073709551615],
             "i64": [0, 1, -1, 4294967296, 9223372036854775807, -9223372036854775808]}


class TypeError_(Exception):
    pass


# --- values ------------------------------------------------------------------------------

def wrap(ty, v):
    v &= (1 << BITS[ty]) - 1
    if ty[0] == "i" and v >= 1 << (BITS[ty] - 1):
        v -= 1 << BITS[ty]
    return v


# --- generator ---------------------------------------------------------------------------

class Gen:
    def __init__(self, seed, profile="core"):
        self.rng = random.Random(seed)
        self.seed = seed
        self.profile = profile
        self.wide = profile == "wide"
        self.scalars = SCALARS if self.wide else CORE_SCALARS
        self.counter = 0
        self.funcs = []
        self.globals = []

    def fresh(self, prefix):
        self.counter += 1
        return f"{prefix}{self.counter}"

    def program(self):
        rng = self.rng
        for k in range(rng.randint(0, 2)):
            ty = rng.choice(["u32", "i32"])
            self.globals.append({"name": f"g{k}", "ty": ty, "init": rng.choice([0, 1, 5, 1000, 70000])
                                 if ty == "u32" else rng.choice([0, -1, 3, -70000])})
        for k in range(rng.randint(0, 2)):
            err = rng.random() < 0.5
            params = [[f"p{j}", rng.choice(["u32", "i32"])] for j in range(rng.randint(0, 2))]
            self.funcs.append(self.function(f"f{k}", params, err))
        self.funcs.append(self.function("work", [["p0", "u32"], ["p1", "u32"]], False))
        program = {"seed": self.seed, "globals": self.globals, "funcs": self.funcs}
        if self.wide:
            program["profile"] = "wide"
        return program

    def function(self, name, params, err):
        self.scope = {"vals": {n: ty for n, ty in params}, "muts": {}, "ptrs": {}, "unions": [],
                      "arrays": [], "slices": {}, "opts": [], "structs": []}
        for g in self.globals:
            self.scope["muts"][g["name"]] = g["ty"]
        self.err = err
        # The final return sits in the body's scope, so it may read the body's locals.
        body = self.block(depth=0, loop=False, allow_exit=False, keep_scope=True)
        return {"name": name, "params": params, "err": err, "body": body,
                "ret": self.expr("u32", 2)}

    # Scope helpers. Names are unique per program, so a flat visible set per block suffices.
    def visible(self, ty):
        names = [n for n, t in self.scope["vals"].items() if t == ty]
        names += [n for n, t in self.scope["muts"].items() if t == ty]
        return names

    def block(self, depth, loop, allow_exit, in_defer=False, keep_scope=False):
        saved = None if keep_scope else copy.deepcopy(self.scope)
        stmts = [self.stmt(depth, loop, in_defer) for _ in range(self.rng.randint(1, 3 if depth else 5))]
        if allow_exit and not in_defer and self.rng.random() < 0.35:
            choices = [["return", self.expr("u32", 2)]]
            if loop:
                choices.append(["break"])
            if self.err:
                choices.append(["fail"])
            stmts.append(self.rng.choice(choices))
        if saved is not None:
            self.scope = saved
        return stmts

    def stmt(self, depth, loop, in_defer):
        rng = self.rng
        kinds = ["let", "set", "store", "helper"]
        if not in_defer:
            kinds += ["let", "ptr", "let_union", "set_union"]
            if self.wide:
                kinds += ["let_array", "arr_set", "ptr_elem", "let_slice", "let_slice", "sstore", "let_opt",
                          "set_opt", "let_struct", "set_field", "copy_struct", "ptr_field", "bump_struct"]
            if depth < 3:
                kinds += ["if", "while", "switch", "switch_union", "defer"]
                if self.wide:
                    kinds += ["for_slice", "for_slice", "if_opt"]
                if self.err:
                    kinds.append("errdefer")
        elif depth < 2:
            kinds.append("if")
        for _ in range(20):
            kind = rng.choice(kinds)
            built = getattr(self, "s_" + kind)(depth, loop, in_defer)
            if built is not None:
                return built
        expr = self.expr("u32", 2)
        name = self.fresh("x")
        self.scope["muts"][name] = "u32"
        return ["let", name, "u32", expr]

    def s_let(self, depth, loop, in_defer):
        ty = self.rng.choice(self.scalars + ("bool",))
        name = self.fresh("x")
        expr = self.expr(ty, 2)
        self.scope["muts"][name] = ty
        return ["let", name, ty, expr]

    def s_set(self, depth, loop, in_defer):
        names = [n for n, t in self.scope["muts"].items() if t in self.scalars]
        if not names:
            return None
        name = self.rng.choice(names)
        ty = self.scope["muts"][name]
        return ["set", name, self.rng.choice(["=", "+%=", "^="] if ty[0] != "i" else ["=", "+%="]),
                self.expr(ty, 2)]

    def s_store(self, depth, loop, in_defer):
        if not self.scope["ptrs"]:
            return None
        name = self.rng.choice(sorted(self.scope["ptrs"]))
        ty = self.scope["ptrs"][name]
        return ["store", name, self.rng.choice(["=", "+%="]), self.expr(ty, 2)]

    def pointer_arg(self):
        ptrs = [n for n, t in self.scope["ptrs"].items() if t == "u32"]
        targets = [n for n, t in self.scope["muts"].items() if t == "u32"]
        options = [["pvar", n] for n in ptrs] + [["addr", n] for n in targets]
        return self.rng.choice(options) if options else None

    def s_helper(self, depth, loop, in_defer):
        a = self.pointer_arg()
        if a is None:
            return None
        if self.rng.random() < 0.5:
            return ["helper", "bump", [a, self.expr("u32", 1)]]
        b = a if self.rng.random() < 0.4 else self.pointer_arg()  # aliasing swap(&x, &x)
        return ["helper", "swap", [a, b]]

    def s_ptr(self, depth, loop, in_defer):
        names = [n for n, t in self.scope["muts"].items() if t in ("u32", "i32")]
        if not names:
            return None
        target = self.rng.choice(names)
        name = self.fresh("q")
        self.scope["ptrs"][name] = self.scope["muts"][target]
        return ["ptr", name, target]

    def s_let_union(self, depth, loop, in_defer):
        name = self.fresh("un")
        tag = self.rng.choice("ab")
        self.scope["unions"].append(name)
        return ["let_union", name, tag, self.expr("u32" if tag == "a" else "i32", 2)]

    def s_set_union(self, depth, loop, in_defer):
        if not self.scope["unions"]:
            return None
        tag = self.rng.choice("ab")
        return ["set_union", self.rng.choice(self.scope["unions"]), tag,
                self.expr("u32" if tag == "a" else "i32", 2)]

    # --- wide profile: arrays, slices, optionals, structs --------------------------------
    def index(self):
        """A side-effect-free index: a literal or locals (never globals, which a call may change)."""
        local = [n for n in self.visible("u32") if n not in {g["name"] for g in self.globals}]
        pick = self.rng.random()
        if not local or pick < 0.3:
            return ["lit", "u32", self.rng.choice([0, 1, 2, 3, 5, 4294967295])]
        if pick < 0.7:
            return ["var", self.rng.choice(local)]
        return ["bin", self.rng.choice(["+%", "^"]), ["var", self.rng.choice(local)],
                ["lit", "u32", self.rng.choice([1, 2, 3])]]

    def s_let_array(self, depth, loop, in_defer):
        name = self.fresh("ar")
        elems = [self.expr("u32", 1) for _ in range(ARRAY_LEN)]
        self.scope["arrays"].append(name)
        return ["let_array", name, elems]

    def s_arr_set(self, depth, loop, in_defer):
        if not self.scope["arrays"]:
            return None
        name = self.rng.choice(self.scope["arrays"])
        return ["arr_set", name, self.index(), self.rng.choice(["=", "+%="]), self.expr("u32", 2)]

    def s_ptr_elem(self, depth, loop, in_defer):
        if not self.scope["arrays"]:
            return None
        name = self.fresh("q")
        self.scope["ptrs"][name] = "u32"
        return ["ptr_elem", name, self.rng.choice(self.scope["arrays"]), self.index()]

    def s_let_slice(self, depth, loop, in_defer):
        if not self.scope["arrays"]:
            return None
        lo = self.rng.randint(0, ARRAY_LEN - 1)
        hi = self.rng.randint(lo, ARRAY_LEN)
        name = self.fresh("sl")
        self.scope["slices"][name] = hi - lo
        return ["let_slice", name, self.rng.choice(self.scope["arrays"]), lo, hi]

    def s_for_slice(self, depth, loop, in_defer):
        if not self.scope["slices"]:
            return None
        cap = self.fresh("e")
        self.scope["vals"][cap] = "u32"
        body = self.block(depth + 1, True, True)
        del self.scope["vals"][cap]
        return ["for_slice", self.rng.choice(sorted(self.scope["slices"])), cap, body]

    def s_sstore(self, depth, loop, in_defer):
        names = sorted(n for n, length in self.scope["slices"].items() if length)
        if not names:
            return None
        return ["sstore", self.rng.choice(names), self.index(), self.rng.choice(["=", "+%="]), self.expr("u32", 2)]

    def s_let_opt(self, depth, loop, in_defer):
        name = self.fresh("op")
        built = ["let_opt", name, self.expr("bool", 2), self.expr("u32", 2)]
        self.scope["opts"].append(name)
        return built

    def s_set_opt(self, depth, loop, in_defer):
        if not self.scope["opts"]:
            return None
        return ["set_opt", self.rng.choice(self.scope["opts"]), self.expr("bool", 2), self.expr("u32", 2)]

    def s_if_opt(self, depth, loop, in_defer):
        if not self.scope["opts"]:
            return None
        name, cap = self.rng.choice(self.scope["opts"]), self.fresh("o")
        self.scope["vals"][cap] = "u32"
        then = self.block(depth + 1, loop, not in_defer, in_defer)
        del self.scope["vals"][cap]
        other = self.block(depth + 1, loop, False, in_defer) if self.rng.random() < 0.6 else []
        return ["if_opt", name, cap, then, other]

    def s_let_struct(self, depth, loop, in_defer):
        name = self.fresh("st")
        built = ["let_struct", name, self.expr("u32", 2), self.expr("i32", 2)]
        self.scope["structs"].append(name)
        return built

    def s_set_field(self, depth, loop, in_defer):
        if not self.scope["structs"]:
            return None
        field = self.rng.choice("xy")
        return ["set_field", self.rng.choice(self.scope["structs"]), field, self.rng.choice(["=", "+%="]),
                self.expr(FIELD_TY[field], 2)]

    def s_copy_struct(self, depth, loop, in_defer):
        if not self.scope["structs"]:
            return None
        name = self.fresh("st")
        source = self.rng.choice(self.scope["structs"])
        self.scope["structs"].append(name)
        return ["copy_struct", name, source]

    def s_ptr_field(self, depth, loop, in_defer):
        if not self.scope["structs"]:
            return None
        field, name = self.rng.choice("xy"), self.fresh("q")
        self.scope["ptrs"][name] = FIELD_TY[field]
        return ["ptr_field", name, self.rng.choice(self.scope["structs"]), field]

    def s_bump_struct(self, depth, loop, in_defer):
        if not self.scope["structs"]:
            return None
        return ["bump_struct", self.rng.choice(self.scope["structs"]), self.expr("u32", 1)]

    def s_if(self, depth, loop, in_defer):
        cond = self.expr("bool", 2)
        then = self.block(depth + 1, loop, not in_defer, in_defer)
        other = self.block(depth + 1, loop, False, in_defer) if self.rng.random() < 0.6 else []
        return ["if", cond, then, other]

    def s_while(self, depth, loop, in_defer):
        name = self.fresh("lp")
        self.scope["vals"][name] = "u32"
        body = self.block(depth + 1, True, True)
        del self.scope["vals"][name]
        return ["while", name, self.rng.randint(0, MAX_LOOP), body]

    def s_switch(self, depth, loop, in_defer):
        keys = sorted(self.rng.sample(range(4), self.rng.randint(1, 3)))
        arms = [[k, self.block(depth + 1, loop, True)] for k in keys]
        return ["switch", ["mod", self.expr("u32", 1), 4], arms, self.block(depth + 1, loop, False)]

    def s_switch_union(self, depth, loop, in_defer):
        if not self.scope["unions"]:
            return None
        arms = {}
        for tag, ty in (("a", "u32"), ("b", "i32")):
            cap = self.fresh("c")
            self.scope["vals"][cap] = ty
            arms[tag] = [cap, self.block(depth + 1, loop, tag == "a")]
            del self.scope["vals"][cap]
        return ["switch_union", self.rng.choice(self.scope["unions"]), arms]

    def s_defer(self, depth, loop, in_defer):
        return ["defer", self.block(depth + 1, False, False, in_defer=True)]

    def s_errdefer(self, depth, loop, in_defer):
        return ["errdefer", self.block(depth + 1, False, False, in_defer=True)]

    def callable(self, err):
        out = []
        for f in self.funcs:
            if f["err"] == err:
                out.append(f)
        return out

    def expr(self, ty, depth):
        rng = self.rng
        leaf = depth <= 0 or rng.random() < 0.3
        options = ["lit"]
        if self.visible(ty):
            options += ["var", "var"]
        if ty in ("u32", "i32") and any(t == ty for t in self.scope["ptrs"].values()):
            options.append("deref")
        if self.wide and ty == "u32":
            if self.scope["arrays"]:
                options.append("index")
            if any(length for length in self.scope["slices"].values()):
                options.append("sindex")
            if self.scope["opts"]:
                options.append("orelse")
        if self.wide and ty in FIELD_TY.values() and self.scope["structs"]:
            options.append("field")
        if not leaf:
            if ty == "bool":
                options += ["cmp", "cmp", "not", "logic"]
            else:
                options += ["bin", "bin", "cast"]
                if ty == "u32":
                    options += ["shr", "mod"]
                    if self.callable(False):
                        options.append("call")
                    if self.callable(True):
                        options.append("catch")
        kind = rng.choice(options)
        if kind == "lit":
            if ty == "bool":
                return ["lit", "bool", rng.random() < 0.5]
            if ty == "i32":
                return ["lit", ty, rng.choice([0, 1, -1, 7, -2147483648, 2147483647, 1234])]
            if ty == "u8":
                return ["lit", ty, rng.choice([0, 1, 127, 128, 255])]
            if ty in WIDE_LITS:
                return ["lit", ty, rng.choice(WIDE_LITS[ty])]
            return ["lit", ty, rng.choice([0, 1, 2, 3, 255, 65536, 4294967295, 2654435761])]
        if kind == "var":
            return ["var", rng.choice(self.visible(ty))]
        if kind == "deref":
            return ["deref", rng.choice([n for n, t in self.scope["ptrs"].items() if t == ty])]
        if kind == "index":
            return ["index", rng.choice(self.scope["arrays"]), self.index()]
        if kind == "sindex":
            return ["sindex", rng.choice(sorted(n for n, length in self.scope["slices"].items() if length)),
                    self.index()]
        if kind == "orelse":
            return ["orelse", rng.choice(self.scope["opts"]), self.expr("u32", depth - 1)]
        if kind == "field":
            field = rng.choice([f for f, t in FIELD_TY.items() if t == ty])
            return ["field", rng.choice(self.scope["structs"]), field]
        if kind == "cmp":
            sub = rng.choice(self.scalars)
            return ["cmp", rng.choice(["<", "==", "!=", ">="]), self.expr(sub, depth - 1), self.expr(sub, depth - 1)]
        if kind == "not":
            return ["not", self.expr("bool", depth - 1)]
        if kind == "logic":
            return ["bin", rng.choice(["and", "or"]), self.expr("bool", depth - 1), self.expr("bool", depth - 1)]
        if kind == "bin":
            ops = ["+%", "-%", "*%"] + (["^", "&", "|"] if ty[0] != "i" else [])
            return ["bin", rng.choice(ops), self.expr(ty, depth - 1), self.expr(ty, depth - 1)]
        if kind == "shr":
            return ["shr", self.expr("u32", depth - 1), rng.randint(0, 31)]
        if kind == "mod":
            return ["mod", self.expr("u32", depth - 1), rng.randint(1, 9)]
        if kind == "cast" and self.wide:
            name = rng.choice([c for c, (_, target, _) in CASTS.items() if target == ty])
            return ["cast", name, self.expr(CASTS[name][0], depth - 1)]
        if kind == "cast":
            if ty == "u32":
                return rng.choice([["cast", "i2u", self.expr("i32", depth - 1)],
                                   ["cast", "widen8", self.expr("u8", depth - 1)]])
            if ty == "i32":
                return ["cast", "u2i", self.expr("u32", depth - 1)]
            return ["cast", rng.choice(["trunc8", "intcast8"]), self.expr("u32", depth - 1)]
        f = rng.choice(self.callable(kind == "catch"))
        args = [self.expr(t, depth - 1) for _, t in f["params"]]
        if kind == "call":
            return ["call", f["name"], args]
        return ["catch", f["name"], args, self.expr("u32", depth - 1)]


def generate(seed, profile="core"):
    return Gen(seed, profile).program()


# --- typechecker (the generator's invariants) --------------------------------------------

EXIT = {"return", "fail", "break"}
CORE_CASTS = ("i2u", "widen8", "u2i", "trunc8", "intcast8")
WIDE_STMT_TAGS = {"let_array", "arr_set", "ptr_elem", "let_slice", "for_slice", "sstore", "let_opt", "set_opt",
                  "if_opt", "let_struct", "set_field", "copy_struct", "ptr_field", "bump_struct"}


def _exits(stmt):
    tag = stmt[0]
    if tag in EXIT:
        return True
    if tag == "if":
        return bool(stmt[2]) and bool(stmt[3]) and _block_exits(stmt[2]) and _block_exits(stmt[3])
    if tag == "switch":
        return all(_block_exits(b) for _, b in stmt[2]) and _block_exits(stmt[3])
    if tag == "switch_union":
        return all(_block_exits(arm[1]) for arm in stmt[2].values())
    if tag == "if_opt":
        return bool(stmt[3]) and bool(stmt[4]) and _block_exits(stmt[3]) and _block_exits(stmt[4])
    return False


def _block_exits(block):
    return any(_exits(s) for s in block)


RESERVED = {"U", "P", "FuzzError", "std", "bump", "bumpP", "swap", "entry", "r", "a", "b", "t", "p", "d"}
PURE_TAGS = {"lit", "var", "bin", "shr", "mod", "cast"}


class Checker:
    def __init__(self, program):
        self.program = program
        self.wide = program.get("profile", "core") == "wide"
        self.funcs = {}
        self.globals = {}
        self.top = set(RESERVED)
        for f in program["funcs"]:
            self._unique(self.top, f["name"])
        for g in program["globals"]:
            self._unique(self.top, g["name"])
            if g["ty"] not in ("u32", "i32"):
                raise TypeError_(f"global {g['name']} type")
            self._lit(g["ty"], g["init"])
            self.globals[g["name"]] = g["ty"]

    @staticmethod
    def _unique(names, name):
        if not isinstance(name, str) or name in names:
            raise TypeError_(f"duplicate or reserved name {name}")
        names.add(name)

    def _lit(self, ty, v):
        if ty == "bool":
            if not isinstance(v, bool):
                raise TypeError_("bool literal")
            return
        if isinstance(v, bool) or not isinstance(v, int) or wrap(ty, v) != v:
            raise TypeError_(f"{ty} literal {v}")

    def check(self):
        funcs = self.program["funcs"]
        if not funcs or funcs[-1]["name"] != "work" or funcs[-1]["err"] or \
                funcs[-1]["params"] != [["p0", "u32"], ["p1", "u32"]]:
            raise TypeError_("last function must be work(p0: u32, p1: u32) u32")
        for f in funcs:
            self.function(f)
            self.funcs[f["name"]] = f
        return True

    def function(self, f):
        self.err = f["err"]
        self.scopes = [{}]
        self.locals = set(self.top)  # Zig forbids shadowing globals, functions and outer locals
        for name, ty in f["params"]:
            if ty not in ("u32", "i32"):
                raise TypeError_("param type")
            self._declare(name, ("param", ty))
        if _block_exits(f["body"]):
            raise TypeError_("unreachable final return")
        self.block(f["body"] + [["return", f["ret"]]], loop=False, in_defer=False)

    def _declare(self, name, info):
        self._unique(self.locals, name)
        self.scopes[-1][name] = info

    def lookup(self, name):
        for scope in reversed(self.scopes):
            if name in scope:
                return scope[name]
        if name in self.globals:
            return ("mut", self.globals[name])
        raise TypeError_(f"unbound {name}")

    def block(self, stmts, loop, in_defer):
        if not isinstance(stmts, list):
            raise TypeError_("block")
        self.scopes.append({})
        for k, s in enumerate(stmts):
            self.stmt(s, loop, in_defer)
            if _exits(s) and k != len(stmts) - 1:
                raise TypeError_("unreachable code after exit")
        self.scopes.pop()

    def scalar_target(self, name):
        kind, ty = self.lookup(name)
        if kind != "mut" or ty not in SCALARS:
            raise TypeError_(f"{name} is not a mutable scalar")
        return ty

    def pure(self, e):
        """An index expression with no calls, array/slice reads or globals: evaluation order cannot matter."""
        if not isinstance(e, list) or not e or e[0] not in PURE_TAGS:
            raise TypeError_("impure index")
        if e[0] == "var" and e[1] in self.globals:
            raise TypeError_("global in an index")
        for child in e[1:]:
            if isinstance(child, list):
                self.pure(child)

    def need(self, name, kind):
        found, info = self.lookup(name)
        if found != kind:
            raise TypeError_(f"{name} is not a {kind}")
        return info

    def wide_stmt(self, s, loop, in_defer):
        tag = s[0]
        if not self.wide:
            raise TypeError_(f"statement {tag} outside the wide profile")
        if tag == "let_array":
            _, name, elems = s
            if not isinstance(elems, list) or len(elems) != ARRAY_LEN:
                raise TypeError_("array length")
            for e in elems:
                self.expr(e, "u32")
            self._declare(name, ("array", ARRAY_LEN))
        elif tag == "arr_set":
            _, name, idx, op, e = s
            self.need(name, "array")
            self.pure(idx)
            self.expr(idx, "u32")
            if op not in ("=", "+%="):
                raise TypeError_("arr_set op")
            self.expr(e, "u32")
        elif tag == "ptr_elem":
            _, name, arr, idx = s
            self.need(arr, "array")
            self.pure(idx)
            self.expr(idx, "u32")
            self._declare(name, ("ptr", "u32"))
        elif tag == "let_slice":
            _, name, arr, lo, hi = s
            self.need(arr, "array")
            if any(not isinstance(v, int) or isinstance(v, bool) for v in (lo, hi)) or not 0 <= lo <= hi <= ARRAY_LEN:
                raise TypeError_("slice bounds")
            self._declare(name, ("slice", hi - lo))
        elif tag == "for_slice":
            _, name, cap, body = s
            self.need(name, "slice")
            self.scopes.append({})
            self._declare(cap, ("val", "u32"))
            self.block(body, True, False)
            self.scopes.pop()
        elif tag == "sstore":
            _, name, idx, op, e = s
            if self.need(name, "slice") < 1 or op not in ("=", "+%="):
                raise TypeError_("sstore")
            self.pure(idx)
            self.expr(idx, "u32")
            self.expr(e, "u32")
        elif tag == "let_opt":
            _, name, cond, e = s
            self.expr(cond, "bool")
            self.expr(e, "u32")
            self._declare(name, ("opt", "u32"))
        elif tag == "set_opt":
            _, name, cond, e = s
            self.need(name, "opt")
            self.expr(cond, "bool")
            self.expr(e, "u32")
        elif tag == "if_opt":
            _, name, cap, then, other = s
            self.need(name, "opt")
            self.scopes.append({})
            self._declare(cap, ("val", "u32"))
            self.block(then, loop, in_defer)
            self.scopes.pop()
            self.block(other, loop, in_defer)
        elif tag == "let_struct":
            _, name, ex, ey = s
            self.expr(ex, "u32")
            self.expr(ey, "i32")
            self._declare(name, ("struct", "P"))
        elif tag == "set_field":
            _, name, field, op, e = s
            self.need(name, "struct")
            if field not in FIELD_TY or op not in ("=", "+%="):
                raise TypeError_("set_field")
            self.expr(e, FIELD_TY[field])
        elif tag == "copy_struct":
            _, name, source = s
            self.need(source, "struct")
            self._declare(name, ("struct", "P"))
        elif tag == "ptr_field":
            _, name, source, field = s
            self.need(source, "struct")
            if field not in FIELD_TY:
                raise TypeError_("ptr_field")
            self._declare(name, ("ptr", FIELD_TY[field]))
        elif tag == "bump_struct":
            _, name, e = s
            self.need(name, "struct")
            self.expr(e, "u32")

    def pointer_arg(self, arg):
        if arg[0] == "pvar":
            kind, ty = self.lookup(arg[1])
            if kind != "ptr" or ty != "u32":
                raise TypeError_("pointer arg")
        elif arg[0] == "addr":
            if self.scalar_target(arg[1]) != "u32":
                raise TypeError_("address arg")
        else:
            raise TypeError_("pointer arg form")

    def stmt(self, s, loop, in_defer):
        tag = s[0]
        if in_defer and tag not in ("set", "store", "helper", "if", "let"):
            raise TypeError_(f"{tag} inside defer")
        if tag in WIDE_STMT_TAGS:
            self.wide_stmt(s, loop, in_defer)
        elif tag == "let":
            _, name, ty, e = s
            if ty not in SCALARS + ("bool",) or (ty not in CORE_SCALARS + ("bool",) and not self.wide):
                raise TypeError_("let type")
            self.expr(e, ty)
            self._declare(name, ("mut", ty))
        elif tag == "set":
            _, name, op, e = s
            ty = self.scalar_target(name)
            if op not in ("=", "+%=", "^=") or (op == "^=" and ty == "i32"):
                raise TypeError_("set op")
            self.expr(e, ty)
        elif tag == "store":
            _, name, op, e = s
            kind, ty = self.lookup(name)
            if kind != "ptr" or op not in ("=", "+%="):
                raise TypeError_("store")
            self.expr(e, ty)
        elif tag == "helper":
            _, name, args = s
            if name == "bump" and len(args) == 2:
                self.pointer_arg(args[0])
                self.expr(args[1], "u32")
            elif name == "swap" and len(args) == 2:
                self.pointer_arg(args[0])
                self.pointer_arg(args[1])
            else:
                raise TypeError_("helper")
        elif tag == "ptr":
            _, name, target = s
            ty = self.scalar_target(target)
            if ty not in ("u32", "i32"):
                raise TypeError_("pointer target")
            self._declare(name, ("ptr", ty))
        elif tag == "let_union":
            _, name, t, e = s
            self.expr(e, {"a": "u32", "b": "i32"}[t])
            self._declare(name, ("union", "U"))
        elif tag == "set_union":
            _, name, t, e = s
            if self.lookup(name)[0] != "union":
                raise TypeError_("set_union")
            self.expr(e, {"a": "u32", "b": "i32"}[t])
        elif tag == "if":
            _, cond, then, other = s
            self.expr(cond, "bool")
            self.block(then, loop, in_defer)
            self.block(other, loop, in_defer)
        elif tag == "while":
            _, name, bound, body = s
            if not isinstance(bound, int) or isinstance(bound, bool) or not 0 <= bound <= MAX_LOOP:
                raise TypeError_("loop bound")
            self.scopes.append({})
            self._declare(name, ("val", "u32"))
            self.block(body, True, False)
            self.scopes.pop()
        elif tag == "switch":
            _, e, arms, other = s
            self.expr(e, "u32")
            keys = [k for k, _ in arms]
            if len(set(keys)) != len(keys) or any(not isinstance(k, int) or isinstance(k, bool)
                                                  or not 0 <= k < 4 for k in keys):
                raise TypeError_("switch keys")
            for _, body in arms:
                self.block(body, loop, False)
            self.block(other, loop, False)
        elif tag == "switch_union":
            _, name, arms = s
            if self.lookup(name)[0] != "union" or sorted(arms) != ["a", "b"]:
                raise TypeError_("switch_union")
            for t, (cap, body) in sorted(arms.items()):
                self.scopes.append({})
                self._declare(cap, ("val", {"a": "u32", "b": "i32"}[t]))
                self.block(body, loop, False)
                self.scopes.pop()
        elif tag in ("defer", "errdefer"):
            if tag == "errdefer" and not self.err:
                raise TypeError_("errdefer outside an error function")
            self.block(s[1], False, True)
        elif tag == "return":
            self.expr(s[1], "u32")
        elif tag == "fail":
            if not self.err:
                raise TypeError_("fail outside an error function")
        elif tag == "break":
            if not loop:
                raise TypeError_("break outside a loop")
        else:
            raise TypeError_(f"statement {tag}")

    def expr(self, e, ty):
        tag = e[0]
        if tag == "lit":
            if e[1] != ty:
                raise TypeError_("literal type")
            self._lit(ty, e[2])
        elif tag == "var":
            kind, t = self.lookup(e[1])
            if kind not in ("val", "mut", "param") or t != ty:
                raise TypeError_(f"var {e[1]} type")
        elif tag == "deref":
            kind, t = self.lookup(e[1])
            if kind != "ptr" or t != ty:
                raise TypeError_("deref")
        elif tag == "cmp":
            _, op, a, b = e
            if ty != "bool" or op not in ("<", "==", "!=", ">="):
                raise TypeError_("cmp")
            sub = self.infer(a)
            if sub not in SCALARS:
                raise TypeError_("cmp operand")
            self.expr(a, sub)
            self.expr(b, sub)
        elif tag == "not":
            if ty != "bool":
                raise TypeError_("not")
            self.expr(e[1], "bool")
        elif tag == "bin":
            _, op, a, b = e
            allowed = {"bool": ("and", "or"), "i32": ("+%", "-%", "*%"), "i64": ("+%", "-%", "*%"),
                       "u32": ("+%", "-%", "*%", "^", "&", "|"), "u8": ("+%", "-%", "*%", "^", "&", "|"),
                       "u16": ("+%", "-%", "*%", "^", "&", "|"), "u64": ("+%", "-%", "*%", "^", "&", "|")}
            if op not in allowed[ty]:
                raise TypeError_("bin op")
            self.expr(a, ty)
            self.expr(b, ty)
        elif tag in ("shr", "mod"):
            if ty != "u32" or not isinstance(e[2], int) or isinstance(e[2], bool) or \
                    not (0 <= e[2] <= 31 if tag == "shr" else 1 <= e[2] <= 9):
                raise TypeError_(tag)
            self.expr(e[1], "u32")
        elif tag == "cast":
            source, target, _ = CASTS[e[1]]
            if target != ty or (not self.wide and e[1] not in CORE_CASTS):
                raise TypeError_("cast")
            self.expr(e[2], source)
        elif tag in ("index", "sindex", "orelse", "field"):
            if not self.wide:
                raise TypeError_(f"expression {tag} outside the wide profile")
            if tag == "index":
                self.need(e[1], "array")
                self.pure(e[2])
                self.expr(e[2], "u32")
            elif tag == "sindex":
                if self.need(e[1], "slice") < 1:
                    raise TypeError_("sindex of an empty slice")
                self.pure(e[2])
                self.expr(e[2], "u32")
            elif tag == "orelse":
                self.need(e[1], "opt")
                self.expr(e[2], "u32")
            elif e[2] not in FIELD_TY:
                raise TypeError_("field")
            else:
                self.need(e[1], "struct")
            if ty != (FIELD_TY[e[2]] if tag == "field" else "u32"):
                raise TypeError_(f"{tag} type")
        elif tag in ("call", "catch"):
            f = self.funcs.get(e[1])
            if f is None or f["err"] != (tag == "catch") or ty != "u32" or len(e[2]) != len(f["params"]):
                raise TypeError_("call")
            for arg, (_, t) in zip(e[2], f["params"]):
                self.expr(arg, t)
            if tag == "catch":
                self.expr(e[3], "u32")
        else:
            raise TypeError_(f"expression {tag}")

    def infer(self, e):
        tag = e[0]
        if tag == "lit":
            return e[1]
        if tag in ("var", "deref"):
            return self.lookup(e[1])[1]
        if tag in ("cmp", "not"):
            return "bool"
        if tag in ("shr", "mod", "call", "catch"):
            return "u32"
        if tag == "cast":
            return CASTS[e[1]][1]
        if tag in ("index", "sindex", "orelse"):
            return "u32"
        if tag == "field":
            return FIELD_TY[e[2]]
        if tag == "bin":
            return "bool" if e[1] in ("and", "or") else self.infer(e[2])
        raise TypeError_("infer")


def typecheck(program):
    try:
        return Checker(program).check()
    except (TypeError_, KeyError, IndexError, TypeError, ValueError):
        return False


def typecheck_error(program):
    try:
        Checker(program).check()
        return None
    except (TypeError_, KeyError, IndexError, TypeError, ValueError) as error:
        return f"{type(error).__name__}: {error}"


# --- reference evaluator -----------------------------------------------------------------

class _Return(Exception):
    def __init__(self, value):
        self.value = value


class _Fail(Exception):
    pass


class _Break(Exception):
    pass


class Machine:
    def __init__(self, program, fuel=200000):
        self.var_types = _var_types(program)
        self.funcs = {f["name"]: f for f in program["funcs"]}
        self.globals = {g["name"]: [g["init"]] for g in program["globals"]}
        self.fuel = fuel

    def tick(self):
        self.fuel -= 1
        if self.fuel < 0:
            raise RuntimeError("evaluation fuel exhausted")

    def call(self, name, args):
        f = self.funcs[name]
        env = [dict(self.globals), {n: [v] for (n, _), v in zip(f["params"], args)}]
        try:
            # The final return is inside the body block: its value precedes the body's defers.
            self.block(f["body"] + [["return", f["ret"]]], env)
            raise AssertionError("function body fell through")
        except _Return as r:
            return ("ok", r.value)
        except _Fail:
            return ("err", None)

    def cell(self, env, name):
        for scope in reversed(env):
            if name in scope:
                return scope[name]
        raise KeyError(name)

    def block(self, stmts, env):
        env.append({})
        defers = []
        try:
            for s in stmts:
                self.stmt(s, env, defers)
        except _Fail:
            self.run_defers(defers, env, error=True)
            raise
        except (_Return, _Break):
            self.run_defers(defers, env, error=False)
            raise
        else:
            self.run_defers(defers, env, error=False)
        finally:
            env.pop()

    def run_defers(self, defers, env, error):
        for kind, body in reversed(defers):
            if kind == "defer" or error:
                self.block(body, env)

    def ptr_cell(self, arg, env):
        cell = self.cell(env, arg[1])
        return cell[0] if arg[0] == "pvar" else cell

    def stmt(self, s, env, defers):
        self.tick()
        tag = s[0]
        if tag == "let":
            env[-1][s[1]] = [self.expr(s[3], env)]
        elif tag in ("set", "store"):
            cell = self.cell(env, s[1])
            if tag == "store":
                cell = cell[0]
            if s[2] == "=":
                cell[0] = self.expr(s[3], env)
            else:
                # Zig loads a compound assignment's target before evaluating its operand.
                old = cell[0]
                value = self.expr(s[3], env)
                cell[0] = wrap(self.var_types[s[1]], old + value) if s[2] == "+%=" else old ^ value
        elif tag == "helper":
            if s[1] == "bump":
                p = self.ptr_cell(s[2][0], env)
                d = self.expr(s[2][1], env)
                p[0] = wrap("u32", p[0] + d)
            else:
                a, b = self.ptr_cell(s[2][0], env), self.ptr_cell(s[2][1], env)
                a[0], b[0] = b[0], a[0]
        elif tag == "ptr":
            env[-1][s[1]] = [self.cell(env, s[2])]
        elif tag in WIDE_STMT_TAGS:
            self.wide_stmt(s, env)
        elif tag in ("let_union", "set_union"):
            value = (s[2], self.expr(s[3], env))
            if tag == "let_union":
                env[-1][s[1]] = [value]
            else:
                self.cell(env, s[1])[0] = value
        elif tag == "if":
            self.block(s[2] if self.expr(s[1], env) else s[3], env)
        elif tag == "while":
            env.append({s[1]: [0]})
            try:
                while env[-1][s[1]][0] < s[2]:
                    self.tick()
                    try:
                        self.block(s[3], env)
                    except _Break:
                        break
                    env[-1][s[1]][0] += 1
            finally:
                env.pop()
        elif tag == "switch":
            key = self.expr(s[1], env)
            body = next((b for k, b in s[2] if k == key), s[3])
            self.block(body, env)
        elif tag == "switch_union":
            t, payload = self.cell(env, s[1])[0]
            cap, body = s[2][t]
            env.append({cap: [payload]})
            try:
                self.block(body, env)
            finally:
                env.pop()
        elif tag in ("defer", "errdefer"):
            defers.append((tag, s[1]))
        elif tag == "return":
            raise _Return(self.expr(s[1], env))
        elif tag == "fail":
            raise _Fail()
        elif tag == "break":
            raise _Break()

    def assign(self, cell, op, ty, value_of):
        """`cell op= value`: a compound assignment loads its target before evaluating the operand."""
        if op == "=":
            cell[0] = value_of()
        else:
            old = cell[0]
            cell[0] = wrap(ty, old + value_of())

    def wide_stmt(self, s, env):
        tag = s[0]
        if tag == "let_array":
            env[-1][s[1]] = [[[self.expr(e, env)] for e in s[2]]]
        elif tag == "arr_set":
            cell = self.cell(env, s[1])[0][self.expr(s[2], env) % ARRAY_LEN]
            self.assign(cell, s[3], "u32", lambda: self.expr(s[4], env))
        elif tag == "ptr_elem":
            env[-1][s[1]] = [self.cell(env, s[2])[0][self.expr(s[3], env) % ARRAY_LEN]]
        elif tag == "let_slice":
            env[-1][s[1]] = [self.cell(env, s[2])[0][s[3]:s[4]]]
        elif tag == "for_slice":
            for cell in list(self.cell(env, s[1])[0]):
                self.tick()
                env.append({s[2]: [cell[0]]})
                try:
                    self.block(s[3], env)
                except _Break:
                    break
                finally:
                    env.pop()
        elif tag == "sstore":
            cells = self.cell(env, s[1])[0]
            cell = cells[self.expr(s[2], env) % len(cells)]
            self.assign(cell, s[3], "u32", lambda: self.expr(s[4], env))
        elif tag in ("let_opt", "set_opt"):
            value = self.expr(s[3], env) if self.expr(s[2], env) else None
            if tag == "let_opt":
                env[-1][s[1]] = [value]
            else:
                self.cell(env, s[1])[0] = value
        elif tag == "if_opt":
            value = self.cell(env, s[1])[0]
            if value is None:
                self.block(s[4], env)
            else:
                env.append({s[2]: [value]})
                try:
                    self.block(s[3], env)
                finally:
                    env.pop()
        elif tag == "let_struct":
            x = self.expr(s[2], env)
            env[-1][s[1]] = [{"x": [x], "y": [self.expr(s[3], env)]}]
        elif tag == "set_field":
            cell = self.cell(env, s[1])[0][s[2]]
            self.assign(cell, s[3], FIELD_TY[s[2]], lambda: self.expr(s[4], env))
        elif tag == "copy_struct":
            env[-1][s[1]] = [{f: [c[0]] for f, c in self.cell(env, s[2])[0].items()}]
        elif tag == "ptr_field":
            env[-1][s[1]] = [self.cell(env, s[2])[0][s[3]]]
        elif tag == "bump_struct":
            d = self.expr(s[2], env)
            fields = self.cell(env, s[1])[0]
            fields["x"][0] = wrap("u32", fields["x"][0] + d)
            fields["y"][0] = wrap("i32", fields["y"][0] + wrap("i32", d))
        else:
            raise ValueError(tag)

    def expr(self, e, env):
        self.tick()
        tag = e[0]
        if tag == "lit":
            return e[2]
        if tag == "index":
            return self.cell(env, e[1])[0][self.expr(e[2], env) % ARRAY_LEN][0]
        if tag == "sindex":
            cells = self.cell(env, e[1])[0]
            return cells[self.expr(e[2], env) % len(cells)][0]
        if tag == "orelse":
            value = self.cell(env, e[1])[0]
            return value if value is not None else self.expr(e[2], env)
        if tag == "field":
            return self.cell(env, e[1])[0][e[2]][0]
        if tag == "var":
            return self.cell(env, e[1])[0]
        if tag == "deref":
            return self.cell(env, e[1])[0][0]
        if tag == "cmp":
            a, b = self.expr(e[2], env), self.expr(e[3], env)
            return {"<": a < b, "==": a == b, "!=": a != b, ">=": a >= b}[e[1]]
        if tag == "not":
            return not self.expr(e[1], env)
        if tag == "bin":
            op = e[1]
            if op == "and":
                return self.expr(e[2], env) and self.expr(e[3], env)
            if op == "or":
                return self.expr(e[2], env) or self.expr(e[3], env)
            ty = _infer_static(e, self.var_types)
            a, b = self.expr(e[2], env), self.expr(e[3], env)
            raw = {"+%": a + b, "-%": a - b, "*%": a * b, "^": a ^ b, "&": a & b, "|": a | b}[op]
            return wrap(ty, raw)
        if tag == "shr":
            return self.expr(e[1], env) >> e[2]
        if tag == "mod":
            return self.expr(e[1], env) % e[2]
        if tag == "cast":
            v = self.expr(e[2], env)
            _, target, form = CASTS[e[1]]
            if form == "widen":
                return v
            if form == "intcast8":
                return v & 0x7F  # @intCast(v & 0x7f)
            if form == "intcast16":
                return v & 0x7FFF  # @intCast(v & 0x7fff)
            return wrap(target, v)  # bitcast and truncate both reinterpret the low bits
        if tag in ("call", "catch"):
            args = [self.expr(a, env) for a in e[2]]
            status, value = self.call(e[1], args)
            if status == "err":
                return self.expr(e[3], env)
            return value
        raise ValueError(tag)


def _infer_static(e, var_types):
    tag = e[0]
    if tag == "lit":
        return e[1]
    if tag in ("var", "deref"):
        return var_types[e[1]]
    if tag in ("cmp", "not"):
        return "bool"
    if tag in ("shr", "mod", "call", "catch"):
        return "u32"
    if tag == "cast":
        return CASTS[e[1]][1]
    if tag in ("index", "sindex", "orelse"):
        return "u32"
    if tag == "field":
        return FIELD_TY[e[2]]
    if e[1] in ("and", "or"):
        return "bool"
    return _infer_static(e[2], var_types)


def _var_types(program):
    """Names are unique per program, so one flat name -> scalar/pointee type map suffices."""
    types = {g["name"]: g["ty"] for g in program["globals"]}

    def walk(node):
        if isinstance(node, list) and node and isinstance(node[0], str):
            tag = node[0]
            if tag == "let":
                types[node[1]] = node[2]
            elif tag == "ptr":
                types[node[1]] = types.get(node[2])
            elif tag in ("while", "for_slice", "if_opt"):
                types[node[1] if tag == "while" else node[2]] = "u32"
            elif tag == "ptr_elem":
                types[node[1]] = "u32"
            elif tag == "ptr_field":
                types[node[1]] = FIELD_TY[node[3]]
            elif tag == "switch_union":
                types[node[2]["a"][0]] = "u32"
                types[node[2]["b"][0]] = "i32"
        if isinstance(node, list):
            for child in node:
                walk(child)
        elif isinstance(node, dict):
            for child in node.values():
                walk(child)

    for f in program["funcs"]:
        for name, ty in f["params"]:
            types[name] = ty
    # Source order declares every pointer target before the pointer.
    for f in program["funcs"]:
        walk(f["body"])
    return types


def evaluate(program):
    """Expected `entry(a, b)` for each INPUTS pair; globals reset on each entry."""
    results = []
    for a, b in INPUTS:
        machine = Machine(program)
        status, value = machine.call("work", [a, b])
        assert status == "ok"
        for g in program["globals"]:
            value ^= machine.globals[g["name"]][0] & 0xFFFFFFFF
        results.append(value)
    return results


# --- renderer ----------------------------------------------------------------------------

def _refs(node, out):
    """Collect (name, how) references; how is 'read', 'write' or 'addr'."""
    if isinstance(node, dict):
        for child in node.values():
            _refs(child, out)
        return
    if not isinstance(node, list) or not node:
        return
    tag = node[0] if isinstance(node[0], str) else None
    if tag in ("var", "deref") and len(node) == 2:
        out.append((node[1], "read"))
    elif tag in ("set", "set_union") and len(node) == 4:
        out.append((node[1], "write"))
        _refs(node[3], out)
        return
    elif tag == "store" and len(node) == 4:
        out.append((node[1], "read"))
        _refs(node[3], out)
        return
    elif tag == "ptr" and len(node) == 3:
        out.append((node[2], "addr"))
        return
    elif tag in ("addr",) and len(node) == 2:
        out.append((node[1], "addr"))
        return
    elif tag == "pvar" and len(node) == 2:
        out.append((node[1], "read"))
        return
    elif tag in ("index", "sindex", "orelse", "field") and len(node) == 3:
        out.append((node[1], "read"))
        _refs(node[2], out)
        return
    elif tag in ("arr_set", "sstore", "set_field") and len(node) == 5:
        out.append((node[1], "write" if tag != "sstore" else "read"))
        _refs(node[2], out)
        _refs(node[4], out)
        return
    elif tag == "ptr_elem" and len(node) == 4:
        out.append((node[2], "addr"))
        _refs(node[3], out)
        return
    elif tag in ("let_slice", "ptr_field") and len(node) in (4, 5):
        out.append((node[2], "addr"))
        return
    elif tag == "for_slice" and len(node) == 4:
        out.append((node[1], "read"))
        _refs(node[3], out)
        return
    elif tag == "set_opt" and len(node) == 4:
        out.append((node[1], "write"))
        _refs(node[2], out)
        _refs(node[3], out)
        return
    elif tag == "if_opt" and len(node) == 5:
        out.append((node[1], "read"))
        _refs(node[3], out)
        _refs(node[4], out)
        return
    elif tag == "copy_struct" and len(node) == 3:
        out.append((node[2], "read"))
        return
    elif tag == "bump_struct" and len(node) == 3:
        out.append((node[1], "addr"))
        _refs(node[2], out)
        return
    elif tag == "switch_union" and len(node) == 3:
        out.append((node[1], "read"))
        _refs(node[2], out)
        return
    elif tag in ("let", "let_union", "let_opt") and len(node) == 4:
        _refs(node[2] if tag == "let_opt" else node[3], out)
        if tag == "let_opt":
            _refs(node[3], out)
        return
    elif tag == "let_struct" and len(node) == 4:
        _refs(node[2], out)
        _refs(node[3], out)
        return
    elif tag == "let_array" and len(node) == 3:
        _refs(node[2], out)
        return
    elif tag == "while" and len(node) == 4:
        _refs(node[3], out)
        return
    for child in node[1:] if tag else node:
        _refs(child, out)


ZTY = {ty: ty for ty in SCALARS + ("bool",)}


class Renderer:
    def __init__(self, program):
        self.program = program
        self.var_types = _var_types(program)
        self.slice_len = {}

        def walk(node):
            if isinstance(node, list):
                if len(node) == 5 and node[0] == "let_slice":
                    self.slice_len[node[1]] = node[4] - node[3]
                for child in node:
                    walk(child)
            elif isinstance(node, dict):
                for child in node.values():
                    walk(child)
        walk([f["body"] for f in program["funcs"]])

    def lit(self, ty, v):
        if ty == "bool":
            return "true" if v else "false"
        return f"@as({ty}, {v})"

    def expr(self, e):
        tag = e[0]
        if tag == "lit":
            return self.lit(e[1], e[2])
        if tag == "var":
            return e[1]
        if tag == "deref":
            return f"{e[1]}.*"
        if tag == "index":
            return f"{e[1]}[({self.expr(e[2])} % {ARRAY_LEN})]"
        if tag == "sindex":
            return f"{e[1]}[({self.expr(e[2])} % {self.slice_len[e[1]]})]"
        if tag == "orelse":
            return f"({e[1]} orelse {self.expr(e[2])})"
        if tag == "field":
            return f"{e[1]}.{e[2]}"
        if tag == "cmp":
            return f"({self.expr(e[2])} {e[1]} {self.expr(e[3])})"
        if tag == "not":
            return f"!{self.expr(e[1])}"
        if tag == "bin":
            return f"({self.expr(e[2])} {e[1]} {self.expr(e[3])})"
        if tag == "shr":
            return f"({self.expr(e[1])} >> {e[2]})"
        if tag == "mod":
            return f"({self.expr(e[1])} % {e[2]})"
        if tag == "cast":
            inner = self.expr(e[2])
            _, target, form = CASTS[e[1]]
            return {"bitcast": f"@as({target}, @bitCast({inner}))", "widen": f"@as({target}, {inner})",
                    "trunc": f"@as({target}, @truncate({inner}))",
                    "intcast8": f"@as(u8, @intCast({inner} & 0x7f))",
                    "intcast16": f"@as(u16, @intCast({inner} & 0x7fff))"}[form]
        if tag == "call":
            return f"{e[1]}({', '.join(self.expr(a) for a in e[2])})"
        if tag == "catch":
            return f"({e[1]}({', '.join(self.expr(a) for a in e[2])}) catch {self.expr(e[3])})"
        raise ValueError(tag)

    def ptr_arg(self, arg):
        return arg[1] if arg[0] == "pvar" else f"&{arg[1]}"

    def block(self, stmts, indent, refs):
        return [line for s in stmts for line in self.stmt(s, indent, refs)]

    def _uses(self, name, refs):
        return [how for n, how in refs if n == name]

    def decl(self, pad, name, ty, init, refs):
        uses = self._uses(name, refs)
        mutable = any(h in ("write", "addr") for h in uses)
        keyword = "var" if mutable else "const"
        lines = [f"{pad}{keyword} {name}: {ty} = {init};"]
        if not uses:
            lines.append(f"{pad}_ = {name};")
        return lines

    def stmt(self, s, indent, refs):
        pad = "    " * indent
        tag = s[0]
        if tag == "let":
            return self.decl(pad, s[1], ZTY[s[2]], self.expr(s[3]), refs)
        if tag == "let_union":
            return self.decl(pad, s[1], "U", f".{{ .{s[2]} = {self.expr(s[3])} }}", refs)
        if tag == "ptr":
            lines = [f"{pad}const {s[1]} = &{s[2]};"]
            if not self._uses(s[1], refs):
                lines.append(f"{pad}_ = {s[1]};")
            return lines
        if tag == "set":
            return [f"{pad}{s[1]} {s[2]} {self.expr(s[3])};"]
        if tag == "store":
            return [f"{pad}{s[1]}.* {s[2]} {self.expr(s[3])};"]
        if tag == "set_union":
            return [f"{pad}{s[1]} = .{{ .{s[2]} = {self.expr(s[3])} }};"]
        if tag in WIDE_STMT_TAGS:
            return self.wide_stmt(s, indent, refs)
        if tag == "helper":
            if s[1] == "bump":
                return [f"{pad}bump({self.ptr_arg(s[2][0])}, {self.expr(s[2][1])});"]
            return [f"{pad}swap({self.ptr_arg(s[2][0])}, {self.ptr_arg(s[2][1])});"]
        if tag == "if":
            lines = [f"{pad}if ({self.expr(s[1])}) {{"] + self.block(s[2], indent + 1, refs)
            if s[3]:
                lines += [f"{pad}}} else {{"] + self.block(s[3], indent + 1, refs)
            return lines + [f"{pad}}}"]
        if tag == "while":
            return ([f"{pad}{{", f"{pad}    var {s[1]}: u32 = 0;",
                     f"{pad}    while ({s[1]} < {s[2]}) : ({s[1]} += 1) {{"]
                    + self.block(s[3], indent + 2, refs) + [f"{pad}    }}", f"{pad}}}"])
        if tag == "switch":
            lines = [f"{pad}switch ({self.expr(s[1])}) {{"]
            for key, body in s[2]:
                lines += [f"{pad}    {key} => {{"] + self.block(body, indent + 2, refs) + [f"{pad}    }},"]
            lines += [f"{pad}    else => {{"] + self.block(s[3], indent + 2, refs) + [f"{pad}    }},"]
            return lines + [f"{pad}}}"]
        if tag == "switch_union":
            lines = [f"{pad}switch ({s[1]}) {{"]
            for t in ("a", "b"):
                cap, body = s[2][t]
                capture = f" |{cap}|" if self._uses(cap, refs) else ""
                lines += [f"{pad}    .{t} =>{capture} {{"] + self.block(body, indent + 2, refs) + [f"{pad}    }},"]
            return lines + [f"{pad}}}"]
        if tag in ("defer", "errdefer"):
            return [f"{pad}{tag} {{"] + self.block(s[1], indent + 1, refs) + [f"{pad}}}"]
        if tag == "return":
            return [f"{pad}return {self.expr(s[1])};"]
        if tag == "fail":
            return [f"{pad}return error.Fuzz;"]
        if tag == "break":
            return [f"{pad}break;"]
        raise ValueError(tag)

    def wide_stmt(self, s, indent, refs):
        pad = "    " * indent
        tag = s[0]
        if tag == "let_array":
            return self.decl(pad, s[1], f"[{ARRAY_LEN}]u32", ".{ " + ", ".join(self.expr(e) for e in s[2]) + " }", refs)
        if tag in ("arr_set", "sstore"):
            length = ARRAY_LEN if tag == "arr_set" else self.slice_len[s[1]]
            return [f"{pad}{s[1]}[({self.expr(s[2])} % {length})] {s[3]} {self.expr(s[4])};"]
        if tag == "ptr_elem":
            lines = [f"{pad}const {s[1]} = &{s[2]}[({self.expr(s[3])} % {ARRAY_LEN})];"]
        elif tag == "ptr_field":
            lines = [f"{pad}const {s[1]} = &{s[2]}.{s[3]};"]
        elif tag == "let_slice":
            return self.decl(pad, s[1], "[]u32", f"{s[2]}[{s[3]}..{s[4]}]", refs)
        elif tag == "for_slice":
            capture = s[2] if self._uses(s[2], refs) else "_"
            return ([f"{pad}for ({s[1]}) |{capture}| {{"] + self.block(s[3], indent + 1, refs) + [f"{pad}}}"])
        elif tag == "let_opt":
            return self.decl(pad, s[1], "?u32", f"if ({self.expr(s[2])}) {self.expr(s[3])} else null", refs)
        elif tag == "set_opt":
            return [f"{pad}{s[1]} = if ({self.expr(s[2])}) {self.expr(s[3])} else null;"]
        elif tag == "if_opt":
            capture = s[2] if self._uses(s[2], refs) else "_"
            lines = [f"{pad}if ({s[1]}) |{capture}| {{"] + self.block(s[3], indent + 1, refs)
            if s[4]:
                lines += [f"{pad}}} else {{"] + self.block(s[4], indent + 1, refs)
            return lines + [f"{pad}}}"]
        elif tag == "let_struct":
            return self.decl(pad, s[1], "P", f".{{ .x = {self.expr(s[2])}, .y = {self.expr(s[3])} }}", refs)
        elif tag == "set_field":
            return [f"{pad}{s[1]}.{s[2]} {s[3]} {self.expr(s[4])};"]
        elif tag == "copy_struct":
            return self.decl(pad, s[1], "P", s[2], refs)
        elif tag == "bump_struct":
            return [f"{pad}bumpP(&{s[1]}, {self.expr(s[2])});"]
        else:
            raise ValueError(tag)
        if not self._uses(s[1], refs):
            lines.append(f"{pad}_ = {s[1]};")
        return lines

    def function(self, f):
        refs = []
        _refs(f["body"], refs)
        _refs(f["ret"], refs)
        params = ", ".join(f"{n}: {t}" for n, t in f["params"])
        result = "FuzzError!u32" if f["err"] else "u32"
        lines = [f"fn {f['name']}({params}) {result} {{"]
        for name, _ in f["params"]:
            if not self._uses(name, refs):
                lines.append(f"    _ = {name};")
        lines += self.block(f["body"], 1, refs)
        lines += [f"    return {self.expr(f['ret'])};", "}", ""]
        return lines

    def source(self, module, expected):
        program = self.program
        wide = program.get("profile", "core") == "wide"
        lines = [f"// Generated by tests/roadmap/fuzz/zig_gen.py from seed {program['seed']}"
                 + ("" if not wide else " (wide profile)") + "; do not edit.",
                 'const std = @import("std");', "",
                 "const U = union(enum) { a: u32, b: i32 };",
                 "const FuzzError = error{Fuzz};", ""]
        if wide:
            lines += ["const P = struct { x: u32, y: i32 };", ""]
        for g in program["globals"]:
            lines.append(f"var {g['name']}: {g['ty']} = {g['init']};")
        lines += ["", "fn bump(p: *u32, d: u32) void {", "    p.* +%= d;", "}", "",
                  "fn swap(a: *u32, b: *u32) void {", "    const t = a.*;", "    a.* = b.*;",
                  "    b.* = t;", "}", ""]
        if wide:
            lines += ["fn bumpP(p: *P, d: u32) void {", "    p.x +%= d;", "    p.y +%= @as(i32, @bitCast(d));", "}", ""]
        for f in program["funcs"]:
            lines += self.function(f)
        lines.append("pub fn entry(a: u32, b: u32) u32 {")
        for g in program["globals"]:
            lines.append(f"    {g['name']} = {g['init']};")
        if program["globals"]:
            lines.append("    var r = work(a, b);")
            for g in program["globals"]:
                cast = g["name"] if g["ty"] == "u32" else f"@as(u32, @bitCast({g['name']}))"
                lines.append(f"    r ^= {cast};")
            lines.append("    return r;")
        else:
            lines.append("    return work(a, b);")
        lines += ["}", "", "comptime {", "    _ = &entry;", "}", "",
                  f'test "{module}" {{']
        for (a, b), value in zip(INPUTS, expected):
            lines.append(f"    try std.testing.expectEqual(@as(u32, {value}), entry({a}, {b}));")
        lines += ["}", ""]
        return "\n".join(lines)


def module_name(program):
    return f"fuzz_{'w' if program.get('profile', 'core') == 'wide' else 's'}{program['seed']}"


def render(program, module=None):
    module = module or module_name(program)
    return Renderer(program).source(module, evaluate(program))


def features(program):
    found = set()
    text = json.dumps(program)
    if program["globals"]:
        found.add("global")
    if '["ptr"' in text or '["addr"' in text or '["pvar"' in text:
        found.add("alias")
    if '["defer"' in text:
        found.add("defer")
    if '["errdefer"' in text:
        found.add("errdefer")
    if '["let_union"' in text:
        found.add("union")
    if '["cast"' in text:
        found.add("cast")
    if any(f'"{ty}"' in text for ty in ("u16", "u64", "i64")):
        found.add("wide_int")
    for feature, tag in (("array", "let_array"), ("slice", "let_slice"), ("optional", "let_opt"),
                         ("struct", "let_struct")):
        if f'["{tag}"' in text:
            found.add(feature)

    def nested(node, depth):
        if isinstance(node, list) and node and node[0] in ("while", "switch", "switch_union", "if", "for_slice",
                                                              "if_opt"):
            depth += 1
            if depth >= 2:
                return True
        if isinstance(node, list):
            return any(nested(c, depth) for c in node)
        if isinstance(node, dict):
            return any(nested(c, depth) for c in node.values())
        return False

    if any(nested(f["body"], 0) for f in program["funcs"]):
        found.add("nested_control")
    return found


# --- AST shrinker ------------------------------------------------------------------------

def _blocks(node, path=()):
    """Yield paths of every statement list in a program (function bodies and nested blocks)."""
    if isinstance(node, dict):
        for key, child in node.items():
            yield from _blocks(child, path + (key,))
        return
    if not isinstance(node, list):
        return
    if path and path[-1] == "body" or _is_block(node):
        yield path
    for k, child in enumerate(node):
        yield from _blocks(child, path + (k,))


def _tagged(node, tags):
    return isinstance(node, list) and bool(node) and isinstance(node[0], str) and node[0] in tags


def _is_block(node):
    return isinstance(node, list) and bool(node) and all(_tagged(s, STMT_TAGS) for s in node)


STMT_TAGS = {"let", "set", "store", "helper", "ptr", "let_union", "set_union", "if", "while",
             "switch", "switch_union", "defer", "errdefer", "return", "fail", "break"} | WIDE_STMT_TAGS
EXPR_TAGS = {"lit", "var", "deref", "cmp", "not", "bin", "shr", "mod", "cast", "call", "catch", "index", "sindex",
             "orelse", "field"}


def _expr_type(program, path, var_types):
    try:
        return _infer_static(_get(program, path), var_types)
    except (KeyError, IndexError, TypeError):
        return None


def _substitute(node, replace):
    """Copy of `node` with each subtree for which `replace` returns a value replaced by it."""
    new = replace(node)
    if new is not None:
        return new
    if isinstance(node, list):
        return [_substitute(child, replace) for child in node]
    if isinstance(node, dict):
        return {key: _substitute(child, replace) for key, child in node.items()}
    return node


def candidates(program):
    """Single-step reductions, largest first. Each is checked by the caller."""
    funcs = program["funcs"]
    for k in range(len(funcs) - 1):
        name = funcs[k]["name"]
        rest = funcs[:k] + funcs[k + 1:]
        yield {**program, "funcs": rest}
        # Also replace its calls by a literal, so removal is one step.
        yield {**program, "funcs": _substitute(rest, lambda n: ["lit", "u32", 0]
                                                if _tagged(n, ("call", "catch")) and n[1] == name else None)}
    for k, g in enumerate(program["globals"]):
        rest = {**program, "globals": program["globals"][:k] + program["globals"][k + 1:]}
        yield rest
        yield {**rest, "funcs": _substitute(program["funcs"], lambda n: ["lit", g["ty"], 0]
                                            if n == ["var", g["name"]] else None)}
    for path in list(_blocks(program)):
        block = _get(program, path)
        if not isinstance(block, list):
            continue
        for k, s in enumerate(block):
            yield _set(program, path, block[:k] + block[k + 1:])
            # Splice a nested block in place of its compound statement.
            inner = []
            if s[0] == "if":
                inner = [s[2], s[3]]
            elif s[0] in ("while", "for_slice"):
                inner = [s[3]]
            elif s[0] == "if_opt":
                inner = [s[3], s[4]]
            elif s[0] == "switch":
                inner = [b for _, b in s[2]] + [s[3]]
            elif s[0] == "switch_union":
                inner = [arm[1] for arm in s[2].values()]
            elif s[0] in ("defer", "errdefer"):
                inner = [s[1]]
            for body in inner:
                yield _set(program, path, block[:k] + body + block[k + 1:])
            if s[0] == "switch":
                for j in range(len(s[2])):
                    yield _set(program, path + (k, 2), s[2][:j] + s[2][j + 1:])
            if s[0] == "if" and s[3]:
                yield _set(program, path + (k, 3), [])
            if s[0] == "if_opt" and s[4]:
                yield _set(program, path + (k, 4), [])
    var_types = _var_types(program)
    for path, node in list(_nodes(program)):
        if not (path and _tagged(node, EXPR_TAGS)):
            continue
        ty = _expr_type(program, path, var_types)
        if ty is None:
            continue
        simple = ["lit", ty, False if ty == "bool" else 0]
        if node != simple:
            yield _set(program, path, simple)
        # Hoist a direct subexpression or call argument; the typechecker rejects mismatches.
        for child in node[1:]:
            if _tagged(child, EXPR_TAGS):
                yield _set(program, path, child)
            elif isinstance(child, list):
                for arg in child:
                    if _tagged(arg, EXPR_TAGS):
                        yield _set(program, path, arg)
    for path, node in list(_nodes(program)):
        if _tagged(node, ("while",)) and node[2] > 1:
            yield _set(program, path + (2,), 1)


def size(program):
    """Well-founded order for strict shrinking: serialized length, then text."""
    text = json.dumps(program, sort_keys=True)
    return (len(text), text)


def shrink(program, still_fails, budget=5000):
    """Greedy fixpoint over `candidates`: keep a strictly smaller, well-typed failing program.

    The result is 1-minimal with respect to `candidates`: no single reduction both typechecks
    and still fails.
    """
    assert typecheck(program), "shrink needs a well-typed program"
    calls = 0
    current = program
    progress = True
    while progress and calls < budget:
        progress = False
        current_size = size(current)
        for candidate in candidates(current):
            if size(candidate) >= current_size or not typecheck(candidate):
                continue
            calls += 1
            if still_fails(candidate):
                current = candidate
                progress = True
                break
            if calls >= budget:
                break
    return current


# --- commands ----------------------------------------------------------------------------

def cmd_light(args):
    counts = dict.fromkeys(PROFILES[args.profile], 0)
    for seed in range(args.start, args.start + args.seeds):
        program = generate(seed, args.profile)
        error = typecheck_error(program)
        if error:
            print(f"seed {seed}: generator produced an ill-typed program: {error}")
            return 1
        if generate(seed, args.profile) != program:
            print(f"seed {seed}: generator is not deterministic")
            return 1
        source = render(program)
        if render(json.loads(json.dumps(program))) != source:
            print(f"seed {seed}: rendering is not deterministic")
            return 1
        for feature in features(program):
            counts[feature] += 1
    missing = [f for f, n in counts.items() if n == 0]
    print(json.dumps({"profile": args.profile, "seeds": args.seeds, "start": args.start, "features": counts}))
    if missing:
        print(f"features never generated: {missing}")
        return 1
    print(f"{args.seeds} {args.profile} programs typecheck, evaluate and render deterministically")
    return 0


def write_case(program, out):
    out = Path(out)
    out.mkdir(parents=True, exist_ok=True)
    module = module_name(program)
    expected = evaluate(program)
    (out / f"{module}.zig").write_text(Renderer(program).source(module, expected))
    (out / "program.json").write_text(json.dumps(program, indent=1) + "\n")
    (out / "expected.json").write_text(json.dumps(
        {"module": module, "inputs": INPUTS, "expected": expected}) + "\n")
    return out / f"{module}.zig"


def cmd_emit(args):
    print(write_case(generate(args.seed, args.profile), args.out))
    return 0


def lean_checks(gen_text, namespace, expected):
    """#guard lines comparing the translated `entry` with the reference results."""
    memory = f"def entry (p0 : BitVec 32) (p1 : BitVec 32) : Zig.MemM" in gen_text
    pure = f"def entry (p0 : BitVec 32) (p1 : BitVec 32) : Zig.Result" in gen_text
    if not (memory or pure):
        raise ValueError("translated file has no entry (BitVec 32) (BitVec 32) definition")
    lines = ["", f"namespace {namespace}.FuzzCheck",
             "private def successful {α : Type} (r : Zig.Result α) : Option α := Option.bind r Except.toOption"]
    for (a, b), value in zip(INPUTS, expected):
        call = f"({namespace}.entry {a}#32 {b}#32)"
        run = f"({call}.run' ({namespace}.mem0 .fresh))" if memory else call
        lines.append(f"#guard successful {run} == some {value}#32")
    lines.append(f"end {namespace}.FuzzCheck")
    return "\n".join(lines) + "\n"


def cmd_lean_checks(args):
    case = json.loads(Path(args.expected).read_text())
    text = Path(args.gen).read_text()
    Path(args.out).write_text(text + lean_checks(text, args.namespace, case["expected"]))
    return 0


def cmd_shrink(args):
    program = json.loads(Path(args.program).read_text())

    def fails(candidate):
        with tempfile.TemporaryDirectory(prefix="air2lean-q01-zig-") as tmp:
            write_case(candidate, tmp)
            command = args.command.replace("{dir}", shlex.quote(tmp))
            return subprocess.run(command, shell=True, check=False).returncode != 0

    if not fails(program):
        print("the program does not fail; nothing to shrink")
        return 1
    reduced = shrink(program, fails, budget=args.budget)
    write_case(reduced, args.out)
    print(f"shrunk {size(program)} -> {size(reduced)} bytes of AST: {args.out}")
    return 0


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = parser.add_subparsers(dest="command_name", required=True)
    light = sub.add_parser("light")
    light.add_argument("--seeds", type=int, default=300)
    light.add_argument("--start", type=int, default=0)
    light.add_argument("--profile", choices=sorted(PROFILES), default="core")
    emit = sub.add_parser("emit")
    emit.add_argument("seed", type=int)
    emit.add_argument("out")
    emit.add_argument("--profile", choices=sorted(PROFILES), default="core")
    checks = sub.add_parser("lean-checks")
    checks.add_argument("expected")
    checks.add_argument("gen")
    checks.add_argument("namespace")
    checks.add_argument("out")
    shrink_ = sub.add_parser("shrink")
    shrink_.add_argument("program")
    shrink_.add_argument("--command", required=True, help="shell command; {dir} is the case directory")
    shrink_.add_argument("--budget", type=int, default=2000)
    shrink_.add_argument("out")
    args = parser.parse_args(argv)
    return {"light": cmd_light, "emit": cmd_emit, "lean-checks": cmd_lean_checks,
            "shrink": cmd_shrink}[args.command_name](args)


if __name__ == "__main__":
    sys.exit(main())
