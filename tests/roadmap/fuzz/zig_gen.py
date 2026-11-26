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
import softfloat  # noqa: E402

INPUTS = [(0, 0), (1, 2), (4294967295, 7), (305419896, 2863311530)]
# The ext profile also reaches illegal behaviour, so it runs more inputs (zero and small divisors
# and shift counts, both signs of the reinterpreted parameters).
EXT_INPUTS = INPUTS + [(7, 0), (0, 5), (2147483648, 4294967295), (100, 3)]
CORE_SCALARS = ("u32", "i32", "u8")
SCALARS = CORE_SCALARS + ("u16", "u64", "i64")  # what the typechecker accepts; the core profile uses CORE_SCALARS
MAX_INT_BITS = 128
FLOATS = tuple(softfloat.FORMATS)
MAX_LOOP = 4
ARRAY_LEN = 4
FEATURES = ("alias", "global", "defer", "errdefer", "union", "cast", "nested_control")
WIDE_FEATURES = FEATURES + ("wide_int", "array", "slice", "optional", "struct")
# The ext profile: every integer width and signedness, operations with illegal behaviour (with and
# without guards), floats, allocation through a translated allocator and generic functions.
EXT_FEATURES = WIDE_FEATURES + ("int_width", "divmod", "shift", "checked", "conv", "bounds", "unwrap", "try",
                                "float", "alloc", "generic")
PROFILES = {"core": FEATURES, "wide": WIDE_FEATURES, "ext": EXT_FEATURES}
FIELD_TY = {"x": "u32", "y": "i32"}
# The types of a program's aggregates. core/wide use this fixed shape; an ext program draws its own
# (`program["types"]`), with the integer and float types it computes in.
DEFAULT_SHAPE = {"elem": "u32", "len": ARRAY_LEN, "fields": FIELD_TY, "opt": "u32", "ints": [], "floats": []}
FBA_BYTES = 64  # the fixed buffer of an ext program's allocator: small, so allocation failure is reached
DIV_OPS = ("/", "%", "divTrunc", "divFloor", "divExact", "rem", "mod")
SHIFT_OPS = ("<<", ">>", "shlExact", "shrExact")
FLOAT_UNARY = ("sqrt", "floor", "ceil", "trunc", "round", "abs", "neg")
GENERIC_FNS = {"gsel": 3, "gmix": 2, "gany": 1}  # name -> argument count (gsel's first is a bool)


def shape_of(program):
    return program.get("types", DEFAULT_SHAPE)


def is_int(ty):
    return isinstance(ty, str) and ty[:1] in ("u", "i") and ty[1:].isdigit() and ty[1:2] != "0" \
        and 1 <= int(ty[1:]) <= MAX_INT_BITS


def bits(ty):
    return int(ty[1:])


def int_range(ty):
    return (-(1 << (bits(ty) - 1)), (1 << (bits(ty) - 1)) - 1) if ty[0] == "i" else (0, (1 << bits(ty)) - 1)


def fits(ty, v):
    lo, hi = int_range(ty)
    return lo <= v <= hi


def shift_type(ty):
    """`std.math.Log2Int(ty)`: the type of a shift count."""
    return f"u{(bits(ty) - 1).bit_length()}"


def byte_size(ty):
    """`@sizeOf` and `@alignOf` of an integer on x86_64-linux and aarch64-macos."""
    return max(1, 1 << ((bits(ty) + 7) // 8 - 1).bit_length())
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
    v &= (1 << bits(ty)) - 1
    if ty[0] == "i" and v >= 1 << (bits(ty) - 1):
        v -= 1 << bits(ty)
    return v


# --- generator ---------------------------------------------------------------------------

class Gen:
    def __init__(self, seed, profile="core"):
        self.rng = random.Random(seed)
        self.seed = seed
        self.profile = profile
        self.ext = profile == "ext"
        self.wide = profile in ("wide", "ext")
        self.scalars = SCALARS if self.wide else CORE_SCALARS
        self.shape = DEFAULT_SHAPE
        self.floats = ()
        self.in_defer = False
        if self.ext:
            self.shape = self.draw_shape()
            self.scalars += tuple(t for t in self.shape["ints"] if t not in self.scalars)
            self.floats = tuple(self.shape["floats"])
        self.elem, self.alen, self.fields, self.opt = (self.shape[k] for k in ("elem", "len", "fields", "opt"))
        self.counter = 0
        self.funcs = []
        self.globals = []

    def fresh(self, prefix):
        self.counter += 1
        return f"{prefix}{self.counter}"

    # --- ext profile: the program's own types --------------------------------------------
    EDGE_WIDTHS = (1, 2, 3, 7, 8, 9, 15, 16, 17, 24, 31, 32, 33, 48, 63, 64, 65, 127, 128)

    def int_type(self):
        """Any integer type: half the draws are widths at a byte, word or power-of-two edge."""
        rng = self.rng
        width = rng.choice(self.EDGE_WIDTHS) if rng.random() < 0.5 else rng.randint(1, MAX_INT_BITS)
        return f"{rng.choice('ui')}{width}"

    def draw_shape(self):
        rng = self.rng
        ints = []
        while len(ints) < 3:
            ty = self.int_type()
            if ty not in ints and ty not in SCALARS:
                ints.append(ty)
        return {"ints": ints, "floats": sorted(rng.sample(FLOATS, rng.randint(1, 2))),
                "elem": rng.choice(ints + ["u32"]), "len": rng.randint(1, 6),
                "fields": {"x": rng.choice(ints + ["u32"]), "y": rng.choice(ints + ["i32"])},
                "opt": rng.choice(ints + ["u32"])}

    def int_lit(self, ty):
        lo, hi = int_range(ty)
        pool = {lo, hi, 0, 1, 2, 3, 7, hi // 2, hi - 1, lo + 1, -1, self.rng.randint(lo, hi)}
        return ["lit", ty, self.rng.choice(sorted(v for v in pool if lo <= v <= hi))]

    def float_lit(self, fmt):
        rng = self.rng
        e, f = softfloat.FORMATS[fmt]
        top = softfloat.width(fmt) - 1
        named = [softfloat.from_int(fmt, v) for v in (0, 1, -1, 2, 3, 10, 255, -128, 65535)]
        named += [softfloat.zero(fmt, 1), softfloat.inf(fmt), softfloat.inf(fmt, 1), 1, softfloat.inf(fmt) - 1,
                  1 << f, softfloat.power_of_two(fmt, -1), softfloat.power_of_two(fmt, f + 1) + 1]
        pick = rng.random()
        if pick < 0.6:
            return ["lit", fmt, rng.choice(named)]
        # A finite value: any sign and fraction, an exponent near 1 or anywhere.
        bias = (1 << (e - 1)) - 1
        exp = bias + rng.randint(-4, 8) if pick < 0.85 else rng.randint(0, (1 << e) - 2)
        return ["lit", fmt, (rng.getrandbits(1) << top) | (exp << f) | rng.getrandbits(f)]

    def program(self):
        rng = self.rng
        for k in range(rng.randint(0, 2)):
            ty = rng.choice(["u32", "i32"])
            self.globals.append({"name": f"g{k}", "ty": ty, "init": rng.choice([0, 1, 5, 1000, 70000])
                                 if ty == "u32" else rng.choice([0, -1, 3, -70000])})
        for k in range(rng.randint(0, 2)):
            err = rng.random() < (0.7 if self.ext else 0.5)  # ext: `try` needs two error functions
            params = [[f"p{j}", rng.choice(["u32", "i32"])] for j in range(rng.randint(0, 2))]
            self.funcs.append(self.function(f"f{k}", params, err))
        self.funcs.append(self.function("work", [["p0", "u32"], ["p1", "u32"]], False))
        program = {"seed": self.seed, "globals": self.globals, "funcs": self.funcs}
        if self.wide:
            program["profile"] = self.profile
        if self.ext:
            program["types"] = self.shape
        return program

    def function(self, name, params, err):
        self.scope = {"vals": {n: ty for n, ty in params}, "muts": {}, "ptrs": {}, "unions": [],
                      "arrays": [], "slices": {}, "opts": [], "structs": []}
        for g in self.globals:
            self.scope["muts"][g["name"]] = g["ty"]
        self.err = err
        # ext: an error is an outcome of its own (`catch unreachable`, `try`), so half the error
        # functions start with a conditional failure over their parameters.
        guard = [["if", self.expr("bool", 1), [["fail"]], []]] if self.ext and err and self.rng.random() < 0.5 else []
        # The final return sits in the body's scope, so it may read the body's locals.
        body = guard + self.block(depth=0, loop=False, allow_exit=False, keep_scope=True)
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
                # ext: an error is an outcome of its own (`catch unreachable`, `try`), so it is likelier.
                choices += [["fail"]] * (3 if self.ext else 1)
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
            if self.ext:
                kinds += ["let", "let", "unreach_if"]
            if depth < 3:
                kinds += ["if", "while", "switch", "switch_union", "defer"]
                if self.wide:
                    kinds += ["for_slice", "for_slice", "if_opt"]
                if self.ext:
                    kinds += ["with_alloc", "with_alloc", "with_create"]
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
        ty = self.rng.choice(self.scalars + ("bool",) + self.floats)
        name = self.fresh("x")
        expr = self.expr(ty, 2)
        self.scope["muts"][name] = ty
        return ["let", name, ty, expr]

    def s_set(self, depth, loop, in_defer):
        names = [n for n, t in self.scope["muts"].items() if t in self.scalars or t in self.floats]
        if not names:
            return None
        name = self.rng.choice(names)
        ty = self.scope["muts"][name]
        if ty in FLOATS:
            return ["set", name, "=", self.expr(ty, 2)]
        return ["set", name, self.rng.choice(["=", "+%=", "^="] if ty[0] != "i" else ["=", "+%="]),
                self.expr(ty, 2)]

    # --- ext profile: statements ---------------------------------------------------------
    def s_unreach_if(self, depth, loop, in_defer):
        return ["unreach_if", ["cmp", "==", self.expr("u32", 1), self.expr("u32", 1)]]

    def s_with_alloc(self, depth, loop, in_defer):
        """A heap slice of the program's element type, visible in the body; `mode` says how it is freed."""
        rng = self.rng
        name, count = self.fresh("hp"), rng.randint(1, 5)
        built = ["with_alloc", name, count, self.expr(self.elem, 1), rng.choice(["defer", "end", "leak"]),
                 rng.choice([0, 1, 77, 4294967295])]
        self.scope["slices"][name] = count
        built.append(self.block(depth + 1, loop, False))
        del self.scope["slices"][name]
        return built

    def s_with_create(self, depth, loop, in_defer):
        rng = self.rng
        name, ty = self.fresh("hq"), rng.choice([t for t in self.scalars])
        built = ["with_create", name, ty, self.expr(ty, 1), rng.choice(["defer", "end", "leak"]),
                 rng.choice([0, 1, 77, 4294967295])]
        self.scope["ptrs"][name] = ty
        built.append(self.block(depth + 1, loop, False))
        del self.scope["ptrs"][name]
        return built

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
        names = [n for n, t in self.scope["muts"].items() if t in ("u32", "i32") or (self.ext and is_int(t))]
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
        elems = [self.expr(self.elem, 1) for _ in range(self.alen)]
        self.scope["arrays"].append(name)
        return ["let_array", name, elems]

    def s_arr_set(self, depth, loop, in_defer):
        if not self.scope["arrays"]:
            return None
        name = self.rng.choice(self.scope["arrays"])
        return ["arr_set", name, self.index(), self.rng.choice(["=", "+%="]), self.expr(self.elem, 2)]

    def s_ptr_elem(self, depth, loop, in_defer):
        if not self.scope["arrays"]:
            return None
        name = self.fresh("q")
        self.scope["ptrs"][name] = self.elem
        return ["ptr_elem", name, self.rng.choice(self.scope["arrays"]), self.index()]

    def s_let_slice(self, depth, loop, in_defer):
        if not self.scope["arrays"]:
            return None
        lo = self.rng.randint(0, self.alen - 1)
        hi = self.rng.randint(lo, self.alen)
        name = self.fresh("sl")
        self.scope["slices"][name] = hi - lo
        return ["let_slice", name, self.rng.choice(self.scope["arrays"]), lo, hi]

    def s_for_slice(self, depth, loop, in_defer):
        if not self.scope["slices"]:
            return None
        cap = self.fresh("e")
        self.scope["vals"][cap] = self.elem
        body = self.block(depth + 1, True, True)
        del self.scope["vals"][cap]
        return ["for_slice", self.rng.choice(sorted(self.scope["slices"])), cap, body]

    def s_sstore(self, depth, loop, in_defer):
        names = sorted(n for n, length in self.scope["slices"].items() if length)
        if not names:
            return None
        return ["sstore", self.rng.choice(names), self.index(), self.rng.choice(["=", "+%="]),
                self.expr(self.elem, 2)]

    def s_let_opt(self, depth, loop, in_defer):
        name = self.fresh("op")
        built = ["let_opt", name, self.expr("bool", 2), self.expr(self.opt, 2)]
        self.scope["opts"].append(name)
        return built

    def s_set_opt(self, depth, loop, in_defer):
        if not self.scope["opts"]:
            return None
        return ["set_opt", self.rng.choice(self.scope["opts"]), self.expr("bool", 2), self.expr(self.opt, 2)]

    def s_if_opt(self, depth, loop, in_defer):
        if not self.scope["opts"]:
            return None
        name, cap = self.rng.choice(self.scope["opts"]), self.fresh("o")
        self.scope["vals"][cap] = self.opt
        then = self.block(depth + 1, loop, not in_defer, in_defer)
        del self.scope["vals"][cap]
        other = self.block(depth + 1, loop, False, in_defer) if self.rng.random() < 0.6 else []
        return ["if_opt", name, cap, then, other]

    def s_let_struct(self, depth, loop, in_defer):
        name = self.fresh("st")
        built = ["let_struct", name, self.expr(self.fields["x"], 2), self.expr(self.fields["y"], 2)]
        self.scope["structs"].append(name)
        return built

    def s_set_field(self, depth, loop, in_defer):
        if not self.scope["structs"]:
            return None
        field = self.rng.choice("xy")
        return ["set_field", self.rng.choice(self.scope["structs"]), field, self.rng.choice(["=", "+%="]),
                self.expr(self.fields[field], 2)]

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
        self.scope["ptrs"][name] = self.fields[field]
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

    def s_defer(self, depth, loop, in_defer, tag="defer"):
        outer, self.in_defer = self.in_defer, True  # no `try` inside a defer
        body = self.block(depth + 1, False, False, in_defer=True)
        self.in_defer = outer
        return [tag, body]

    def s_errdefer(self, depth, loop, in_defer):
        return self.s_defer(depth, loop, in_defer, "errdefer")

    def callable(self, err):
        out = []
        for f in self.funcs:
            if f["err"] == err:
                out.append(f)
        return out

    # --- ext profile: expressions --------------------------------------------------------
    def float_expr(self, fmt, depth):
        rng = self.rng
        options = ["lit"] + ["var", "var"] * bool(self.visible(fmt))
        if depth > 0 and rng.random() >= 0.3:
            options += ["fbin", "fbin", "fun", "i2f"] + ["fconv"] * (len(self.floats) > 1)
        kind = rng.choice(options)
        if kind == "lit":
            return self.float_lit(fmt)
        if kind == "var":
            return ["var", rng.choice(self.visible(fmt))]
        if kind == "fbin":
            return ["fbin", rng.choice("+-*/"), self.float_expr(fmt, depth - 1), self.float_expr(fmt, depth - 1)]
        if kind == "fun":
            return ["fun", rng.choice(FLOAT_UNARY), self.float_expr(fmt, depth - 1)]
        if kind == "i2f":
            source = rng.choice(self.scalars)
            return ["i2f", source, fmt, self.expr(source, depth - 1)]
        source = rng.choice([f for f in self.floats if f != fmt])
        return ["fconv", source, fmt, self.float_expr(source, depth - 1)]

    def conv_forms(self, source, target):
        """The casts from one integer type to another: implicit widening, `@truncate`, `@bitCast`, `@intCast`."""
        forms = ["intcast"]
        lo, hi = int_range(source)
        if fits(target, lo) and fits(target, hi):
            forms += ["widen", "widen"]
        if source[0] == target[0] and bits(target) <= bits(source):
            forms.append("trunc")
        if bits(source) == bits(target):
            forms.append("bitcast")
        return forms

    def ext_expr(self, ty, depth):
        """An ext-only integer expression of type `ty`, or None when no form applies."""
        rng = self.rng
        kinds = []
        if ty == self.elem and self.scope["arrays"]:
            kinds.append("uindex")
        if ty == self.elem and any(self.scope["slices"].values()):
            kinds.append("usindex")
        if ty == self.opt and self.scope["opts"]:
            kinds.append("unwrap")
        if depth > 0:
            kinds += ["div", "div", "shift", "shift", "arith", "conv", "conv", "generic", "generic", "f2i"]
            if ty[0] == "i":
                kinds.append("neg")
            if ty[0] == "u" and any(softfloat.width(f) == bits(ty) for f in self.floats):
                kinds += ["fbits", "fbits"]
            if ty == "u32" and self.callable(True):
                kinds += ["cunreach"] * 3
                if self.err and not self.in_defer:
                    kinds += ["try"] * 6
        if not kinds:
            return None
        kind = rng.choice(kinds)
        sub = depth - 1
        if kind == "uindex":
            return ["uindex", rng.choice(self.scope["arrays"]), self.index()]
        if kind == "usindex":
            return ["usindex", rng.choice(sorted(n for n, length in self.scope["slices"].items() if length)),
                    self.index()]
        if kind == "unwrap":
            return ["unwrap", rng.choice(self.scope["opts"])]
        if kind == "div":
            op = rng.choice(DIV_OPS if ty[0] == "u" else DIV_OPS[2:])
            return ["div", op, ty, self.expr(ty, sub), self.expr(ty, sub), rng.random() < 0.6]
        if kind == "shift":
            op = rng.choice(SHIFT_OPS)
            count = self.expr("u32", sub) if rng.random() < 0.5 else ["lit", "u32", rng.randint(0, bits(ty) + 1)]
            return ["shift", op, ty, self.expr(ty, sub), count, op == "shrExact" or rng.random() < 0.6]
        if kind == "arith":
            # One small operand keeps overflow possible but not certain.
            small = self.int_lit(ty) if rng.random() < 0.5 else self.expr(ty, sub)
            return ["arith", rng.choice("+-*"), ty, self.expr(ty, sub), small]
        if kind == "neg":
            return ["neg", ty, self.expr(ty, sub)]
        if kind == "conv":
            source = rng.choice([t for t in self.scalars if t != ty])
            return ["conv", rng.choice(self.conv_forms(source, ty)), source, ty, self.expr(source, sub)]
        if kind == "generic":
            name = rng.choice(["gsel", "gmix", "gany", "gpair", "grep", "gscale"])
            if name == "gsel":
                return ["gcall", name, ty, [self.expr("bool", sub), self.expr(ty, sub), self.expr(ty, sub)]]
            if name in GENERIC_FNS:
                return ["gcall", name, ty, [self.expr(ty, sub) for _ in range(GENERIC_FNS[name])]]
            if name == "gpair":
                return ["gpair", ty, rng.choice(["sum", "second"]), self.expr(ty, sub), self.expr(ty, sub)]
            if name == "grep":
                return ["grep", ty, rng.randint(0, 3), self.expr(ty, sub)]
            return ["gscale", ty, rng.randint(0, min(5, int_range(ty)[1])), self.expr(ty, sub)]
        if kind == "f2i":
            fmt = rng.choice(self.floats)
            return ["f2i", fmt, ty, self.float_expr(fmt, sub), rng.random() < 0.6]
        if kind == "fbits":
            fmt = rng.choice([f for f in self.floats if softfloat.width(f) == bits(ty)])
            return ["fbits", fmt, self.float_expr(fmt, sub)]
        f = rng.choice(self.callable(True))
        return [kind, f["name"], [self.expr(t, sub) for _, t in f["params"]]]

    def expr(self, ty, depth):
        rng = self.rng
        if self.ext:
            if ty in FLOATS:
                return self.float_expr(ty, depth)
            if ty != "bool" and rng.random() < 0.4:
                built = self.ext_expr(ty, depth)
                if built is not None:
                    return built
        leaf = depth <= 0 or rng.random() < 0.3
        options = ["lit"]
        if self.visible(ty):
            options += ["var", "var"]
        if (ty in ("u32", "i32") or self.ext) and any(t == ty for t in self.scope["ptrs"].values()):
            options.append("deref")
        if self.wide and ty == self.elem:
            if self.scope["arrays"]:
                options.append("index")
            if any(length for length in self.scope["slices"].values()):
                options.append("sindex")
        if self.wide and ty == self.opt and self.scope["opts"]:
            options.append("orelse")
        if self.wide and ty in self.fields.values() and self.scope["structs"]:
            options.append("field")
        if not leaf:
            if ty == "bool":
                options += ["cmp", "cmp", "not", "logic"]
            else:
                options += ["bin", "bin"] + ["cast"] * (not self.ext or any(c[1] == ty for c in CASTS.values()))
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
            if ty != "u32":
                return self.int_lit(ty)
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
            return ["orelse", rng.choice(self.scope["opts"]), self.expr(self.opt, depth - 1)]
        if kind == "field":
            field = rng.choice([f for f, t in self.fields.items() if t == ty])
            return ["field", rng.choice(self.scope["structs"]), field]
        if kind == "cmp":
            sub = rng.choice(self.scalars + self.floats)
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
    if tag in ("with_alloc", "with_create"):
        return _block_exits(stmt[6])
    return False


def _block_exits(block):
    return any(_exits(s) for s in block)


RESERVED = {"U", "P", "FuzzError", "std", "bump", "bumpP", "swap", "entry", "r", "a", "b", "t", "p", "d",
            "fuzz_buf", "fuzz_fba", "fuzz_base","gsel", "gmix", "gany", "grep", "gscale", "GPair", "T"}
PURE_TAGS = {"lit", "var", "bin", "shr", "mod", "cast"}
EXT_STMT_TAGS = {"unreach_if", "with_alloc", "with_create"}
EXT_EXPR_TAGS = {"div", "shift", "arith", "neg", "conv", "uindex", "usindex", "unwrap", "cunreach", "try", "gcall",
                 "gpair", "grep", "gscale", "fbin", "fun", "i2f", "fconv", "f2i", "fbits"}
FREE_MODES = ("defer", "end", "leak")


def infer_type(e, name_type, shape):
    """The static type of an expression; `name_type(name)` gives a variable's or pointee's type."""
    tag = e[0]
    if tag == "lit":
        return e[1]
    if tag in ("var", "deref"):
        return name_type(e[1])
    if tag in ("cmp", "not"):
        return "bool"
    if tag in ("shr", "mod", "call", "catch", "cunreach", "try"):
        return "u32"
    if tag == "cast":
        return CASTS[e[1]][1]
    if tag in ("index", "sindex", "uindex", "usindex"):
        return shape["elem"]
    if tag in ("orelse", "unwrap"):
        return shape["opt"]
    if tag == "field":
        return shape["fields"][e[2]]
    if tag == "bin":
        return "bool" if e[1] in ("and", "or") else infer_type(e[2], name_type, shape)
    if tag in ("div", "shift", "arith", "gcall", "i2f", "f2i", "fconv"):
        return e[2]
    if tag in ("neg", "gpair", "grep", "gscale"):
        return e[1]
    if tag == "conv":
        return e[3]
    if tag in ("fbin", "fun"):
        return infer_type(e[2], name_type, shape)
    if tag == "fbits":
        return f"u{softfloat.width(e[1])}"
    raise TypeError_("infer")


class Checker:
    def __init__(self, program):
        self.program = program
        profile = program.get("profile", "core")
        if profile not in PROFILES:
            raise TypeError_("profile")
        self.ext = profile == "ext"
        self.wide = profile in ("wide", "ext")
        self.shape = shape_of(program)
        if ("types" in program) != self.ext:
            raise TypeError_("only an ext program has its own types")
        if self.ext:
            self.check_shape()
        self.in_defer = False
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

    def check_shape(self):
        shape = self.shape
        if sorted(shape) != sorted(DEFAULT_SHAPE) or sorted(shape["fields"]) != ["x", "y"]:
            raise TypeError_("types")
        ints, floats = shape["ints"], shape["floats"]
        if not all(is_int(t) for t in ints) or not floats or not all(f in FLOATS for f in floats) or \
                len(set(floats)) != len(floats):
            raise TypeError_("types: ints and floats")
        if isinstance(shape["len"], bool) or not isinstance(shape["len"], int) or not 1 <= shape["len"] <= 8:
            raise TypeError_("types: array length")
        if not all(is_int(t) for t in (shape["elem"], shape["opt"], *shape["fields"].values())):
            raise TypeError_("types: aggregate members")

    def int_ok(self, ty):
        return ty in SCALARS or (self.ext and is_int(ty))

    def float_ok(self, ty):
        return self.ext and ty in self.shape["floats"]

    def _lit(self, ty, v):
        if ty == "bool":
            if not isinstance(v, bool):
                raise TypeError_("bool literal")
            return
        if isinstance(v, bool) or not isinstance(v, int):
            raise TypeError_(f"{ty} literal {v}")
        if ty in FLOATS:
            # Bits of a number or an infinity: a NaN's sign and payload are never written down.
            if not 0 <= v < 1 << softfloat.width(ty) or softfloat.is_nan(ty, v):
                raise TypeError_(f"{ty} literal bits")
        elif not is_int(ty) or wrap(ty, v) != v:
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
        if kind != "mut" or not (self.int_ok(ty) or self.float_ok(ty)):
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
        elem, length, fields, opt = (self.shape[k] for k in ("elem", "len", "fields", "opt"))
        if tag == "let_array":
            _, name, elems = s
            if not isinstance(elems, list) or len(elems) != length:
                raise TypeError_("array length")
            for e in elems:
                self.expr(e, elem)
            self._declare(name, ("array", length))
        elif tag == "arr_set":
            _, name, idx, op, e = s
            self.need(name, "array")
            self.pure(idx)
            self.expr(idx, "u32")
            if op not in ("=", "+%="):
                raise TypeError_("arr_set op")
            self.expr(e, elem)
        elif tag == "ptr_elem":
            _, name, arr, idx = s
            self.need(arr, "array")
            self.pure(idx)
            self.expr(idx, "u32")
            self._declare(name, ("ptr", elem))
        elif tag == "let_slice":
            _, name, arr, lo, hi = s
            self.need(arr, "array")
            if any(not isinstance(v, int) or isinstance(v, bool) for v in (lo, hi)) or not 0 <= lo <= hi <= length:
                raise TypeError_("slice bounds")
            self._declare(name, ("slice", hi - lo))
        elif tag == "for_slice":
            _, name, cap, body = s
            self.need(name, "slice")
            self.scopes.append({})
            self._declare(cap, ("val", elem))
            self.block(body, True, False)
            self.scopes.pop()
        elif tag == "sstore":
            _, name, idx, op, e = s
            if self.need(name, "slice") < 1 or op not in ("=", "+%="):
                raise TypeError_("sstore")
            self.pure(idx)
            self.expr(idx, "u32")
            self.expr(e, elem)
        elif tag == "let_opt":
            _, name, cond, e = s
            self.expr(cond, "bool")
            self.expr(e, opt)
            self._declare(name, ("opt", opt))
        elif tag == "set_opt":
            _, name, cond, e = s
            self.need(name, "opt")
            self.expr(cond, "bool")
            self.expr(e, opt)
        elif tag == "if_opt":
            _, name, cap, then, other = s
            self.need(name, "opt")
            self.scopes.append({})
            self._declare(cap, ("val", opt))
            self.block(then, loop, in_defer)
            self.scopes.pop()
            self.block(other, loop, in_defer)
        elif tag == "let_struct":
            _, name, ex, ey = s
            self.expr(ex, fields["x"])
            self.expr(ey, fields["y"])
            self._declare(name, ("struct", "P"))
        elif tag == "set_field":
            _, name, field, op, e = s
            self.need(name, "struct")
            if field not in fields or op not in ("=", "+%="):
                raise TypeError_("set_field")
            self.expr(e, fields[field])
        elif tag == "copy_struct":
            _, name, source = s
            self.need(source, "struct")
            self._declare(name, ("struct", "P"))
        elif tag == "ptr_field":
            _, name, source, field = s
            self.need(source, "struct")
            if field not in fields:
                raise TypeError_("ptr_field")
            self._declare(name, ("ptr", fields[field]))
        elif tag == "bump_struct":
            _, name, e = s
            self.need(name, "struct")
            self.expr(e, "u32")

    def ext_stmt(self, s, loop, in_defer):
        tag = s[0]
        if not self.ext:
            raise TypeError_(f"statement {tag} outside the ext profile")
        if tag == "unreach_if":
            self.expr(s[1], "bool")
            return
        _, name, what, init, mode, fail, body = s
        if mode not in FREE_MODES or isinstance(fail, bool) or not isinstance(fail, int) or wrap("u32", fail) != fail:
            raise TypeError_(tag)
        self.scopes.append({})
        if tag == "with_alloc":
            if isinstance(what, bool) or not isinstance(what, int) or not 1 <= what <= 8:
                raise TypeError_("allocation length")
            self.expr(init, self.shape["elem"])
            self._declare(name, ("slice", what))
        else:
            if not self.int_ok(what):
                raise TypeError_("created type")
            self.expr(init, what)
            self._declare(name, ("ptr", what))
        self.block(body, loop, False)
        self.scopes.pop()

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
        self.in_defer = in_defer
        if tag in WIDE_STMT_TAGS:
            self.wide_stmt(s, loop, in_defer)
        elif tag in EXT_STMT_TAGS:
            self.ext_stmt(s, loop, in_defer)
        elif tag == "let":
            _, name, ty, e = s
            if not (self.int_ok(ty) or self.float_ok(ty) or ty == "bool") or \
                    (ty not in CORE_SCALARS + ("bool",) and not self.wide):
                raise TypeError_("let type")
            self.expr(e, ty)
            self._declare(name, ("mut", ty))
        elif tag == "set":
            _, name, op, e = s
            ty = self.scalar_target(name)
            if op not in ("=", "+%=", "^=") or (op == "^=" and ty[0] == "i") or (op != "=" and ty in FLOATS):
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
            if ty not in ("u32", "i32") and not (self.ext and is_int(ty)):
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
            if not (self.int_ok(sub) or self.float_ok(sub)):
                raise TypeError_("cmp operand")
            self.expr(a, sub)
            self.expr(b, sub)
        elif tag == "not":
            if ty != "bool":
                raise TypeError_("not")
            self.expr(e[1], "bool")
        elif tag == "bin":
            _, op, a, b = e
            if ty == "bool":
                allowed = ("and", "or")
            elif not self.int_ok(ty):
                raise TypeError_("bin type")
            else:
                allowed = ("+%", "-%", "*%") + (("^", "&", "|") if ty[0] == "u" else ())
            if op not in allowed:
                raise TypeError_("bin op")
            self.expr(a, ty)
            self.expr(b, ty)
        elif tag in EXT_EXPR_TAGS:
            self.ext_expr(e, ty)
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
                self.expr(e[2], self.shape["opt"])
            elif e[2] not in self.shape["fields"]:
                raise TypeError_("field")
            else:
                self.need(e[1], "struct")
            if ty != infer_type(e, None, self.shape):
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
        return infer_type(e, lambda name: self.lookup(name)[1], self.shape)

    def ext_expr(self, e, ty):
        tag = e[0]
        if not self.ext:
            raise TypeError_(f"expression {tag} outside the ext profile")
        if ty != self.infer(e):
            raise TypeError_(f"{tag} type")
        if tag in ("div", "shift"):
            _, op, _, a, b, guarded = e
            if not self.int_ok(ty) or not isinstance(guarded, bool):
                raise TypeError_(tag)
            if tag == "div":
                # Zig has no `/` or `%` for signed runtime integers.
                if op not in DIV_OPS or (ty[0] == "i" and op in ("/", "%")):
                    raise TypeError_("div op")
            elif op not in SHIFT_OPS or (op == "shrExact" and not guarded):
                # An unguarded `@shrExact` that shifts bits out is unchecked illegal behaviour in
                # ReleaseSafe (docs/illegal-behavior.md row 13): no native outcome to compare.
                raise TypeError_("shift op")
            self.expr(a, ty)
            self.expr(b, ty if tag == "div" else "u32")
        elif tag == "arith":
            _, op, _, a, b = e
            if not self.int_ok(ty) or op not in ("+", "-", "*"):
                raise TypeError_("arith")
            self.expr(a, ty)
            self.expr(b, ty)
        elif tag == "neg":
            if not self.int_ok(ty) or ty[0] != "i":
                raise TypeError_("neg")
            self.expr(e[2], ty)
        elif tag == "conv":
            _, form, source, target, inner = e
            if not (self.int_ok(source) and self.int_ok(target)):
                raise TypeError_("conv types")
            lo, hi = int_range(source)
            if not {"intcast": True, "widen": fits(target, lo) and fits(target, hi),
                    "trunc": source[0] == target[0] and bits(target) <= bits(source),
                    "bitcast": bits(source) == bits(target)}.get(form, False):
                raise TypeError_("conv form")
            self.expr(inner, source)
        elif tag in ("uindex", "usindex"):
            if self.need(e[1], "array" if tag == "uindex" else "slice") < 1:
                raise TypeError_("index of an empty slice")
            self.pure(e[2])
            self.expr(e[2], "u32")
        elif tag == "unwrap":
            self.need(e[1], "opt")
        elif tag in ("cunreach", "try"):
            f = self.funcs.get(e[1])
            if f is None or not f["err"] or len(e[2]) != len(f["params"]):
                raise TypeError_(tag)
            if tag == "try" and (not self.err or self.in_defer):
                raise TypeError_("try outside an error function or inside a defer")
            for arg, (_, t) in zip(e[2], f["params"]):
                self.expr(arg, t)
        elif tag == "gcall":
            _, name, _, args = e
            if not self.int_ok(ty) or name not in GENERIC_FNS or len(args) != GENERIC_FNS[name]:
                raise TypeError_("generic call")
            for k, arg in enumerate(args):
                self.expr(arg, "bool" if name == "gsel" and k == 0 else ty)
        elif tag == "gpair":
            if not self.int_ok(ty) or e[2] not in ("sum", "second"):
                raise TypeError_("gpair")
            self.expr(e[3], ty)
            self.expr(e[4], ty)
        elif tag in ("grep", "gscale"):
            k = e[2]
            if not self.int_ok(ty) or isinstance(k, bool) or not isinstance(k, int) or \
                    not (0 <= k <= 3 if tag == "grep" else 0 <= k and fits(ty, k)):
                raise TypeError_(tag)
            self.expr(e[3], ty)
        elif tag == "fbin":
            if not self.float_ok(ty) or e[1] not in ("+", "-", "*", "/"):
                raise TypeError_("fbin")
            self.expr(e[2], ty)
            self.expr(e[3], ty)
        elif tag == "fun":
            if not self.float_ok(ty) or e[1] not in FLOAT_UNARY:
                raise TypeError_("fun")
            self.expr(e[2], ty)
        elif tag == "i2f":
            if not self.int_ok(e[1]) or not self.float_ok(ty):
                raise TypeError_("i2f")
            self.expr(e[3], e[1])
        elif tag == "fconv":
            if not self.float_ok(e[1]) or not self.float_ok(ty) or e[1] == ty:
                raise TypeError_("fconv")
            self.expr(e[3], e[1])
        elif tag == "f2i":
            if not self.float_ok(e[1]) or not self.int_ok(ty) or not isinstance(e[4], bool):
                raise TypeError_("f2i")
            self.expr(e[3], e[1])
        elif tag == "fbits":
            if not self.float_ok(e[1]):
                raise TypeError_("fbits")
            self.expr(e[2], e[1])


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


class _Panic(Exception):
    """A safety check fired: `kind` is the `std.builtin.panic` member (scripts/panic-policy.tsv)."""

    def __init__(self, kind):
        super().__init__(kind)
        self.kind = kind


class Machine:
    def __init__(self, program, fuel=200000):
        self.var_types = _var_types(program)
        self.shape = shape_of(program)
        self.funcs = {f["name"]: f for f in program["funcs"]}
        self.globals = {g["name"]: [g["init"]] for g in program["globals"]}
        self.fuel = fuel
        self.fba_end = 0  # std.heap.FixedBufferAllocator.end_index over FBA_BYTES bytes
        self.nan_seen = False  # some float operation gave a NaN (docs/floats.md, "NaN in memory")

    def infer(self, e):
        return infer_type(e, self.var_types.get, self.shape)

    # std.heap.FixedBufferAllocator: a bump pointer; only the last allocation gives its bytes back.
    def fba_alloc(self, size, align):
        start = -(-self.fba_end // align) * align  # the buffer itself is aligned for every type
        if start + size > FBA_BYTES:
            return None
        self.fba_end = start + size
        return start

    def fba_free(self, start, size):
        if start + size == self.fba_end:
            self.fba_end -= size

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
        elif tag == "unreach_if":
            if self.expr(s[1], env):
                raise _Panic("reachedUnreachable")
        elif tag in ("with_alloc", "with_create"):
            self.with_heap(s, env)
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

    def with_heap(self, s, env):
        """`with_alloc`/`with_create`: allocate (or return `fail`), initialize, run the body, free by `mode`.

        The body is a block of its own, so its defers run before an `end` free; a `defer` free runs on
        every exit but a panic; `leak` never frees.
        """
        tag, name, what, init, mode, fail, body = s
        ty = self.shape["elem"] if tag == "with_alloc" else what
        count = what if tag == "with_alloc" else 1
        size = count * byte_size(ty)
        start = self.fba_alloc(size, byte_size(ty))
        if start is None:
            raise _Return(fail)
        value = self.expr(init, env)
        cells = [[value] for _ in range(count)]
        env.append({name: [cells if tag == "with_alloc" else cells[0]]})
        try:
            self.block(body, env)
        except (_Return, _Break, _Fail):
            if mode == "defer":
                self.fba_free(start, size)
            raise
        else:
            if mode != "leak":
                self.fba_free(start, size)
        finally:
            env.pop()

    def wide_stmt(self, s, env):
        tag = s[0]
        elem, length, fields = self.shape["elem"], self.shape["len"], self.shape["fields"]
        if tag == "let_array":
            env[-1][s[1]] = [[[self.expr(e, env)] for e in s[2]]]
        elif tag == "arr_set":
            cell = self.cell(env, s[1])[0][self.expr(s[2], env) % length]
            self.assign(cell, s[3], elem, lambda: self.expr(s[4], env))
        elif tag == "ptr_elem":
            env[-1][s[1]] = [self.cell(env, s[2])[0][self.expr(s[3], env) % length]]
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
            self.assign(cell, s[3], elem, lambda: self.expr(s[4], env))
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
            self.assign(cell, s[3], fields[s[2]], lambda: self.expr(s[4], env))
        elif tag == "copy_struct":
            env[-1][s[1]] = [{f: [c[0]] for f, c in self.cell(env, s[2])[0].items()}]
        elif tag == "ptr_field":
            env[-1][s[1]] = [self.cell(env, s[2])[0][s[3]]]
        elif tag == "bump_struct":
            d = self.expr(s[2], env)
            cells = self.cell(env, s[1])[0]
            for field in ("x", "y"):
                cells[field][0] = wrap(fields[field], cells[field][0] + d)
        else:
            raise ValueError(tag)

    def expr(self, e, env):
        self.tick()
        tag = e[0]
        if tag == "lit":
            return e[2]
        if tag == "index":
            return self.cell(env, e[1])[0][self.expr(e[2], env) % self.shape["len"]][0]
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
        if tag in EXT_EXPR_TAGS:
            return self.ext_expr(e, env)
        if tag == "cmp":
            a, b = self.expr(e[2], env), self.expr(e[3], env)
            ty = self.infer(e[2])
            if ty in FLOATS:
                return softfloat.compare(ty, e[1], a, b)
            return {"<": a < b, "==": a == b, "!=": a != b, ">=": a >= b}[e[1]]
        if tag == "not":
            return not self.expr(e[1], env)
        if tag == "bin":
            op = e[1]
            if op == "and":
                return self.expr(e[2], env) and self.expr(e[3], env)
            if op == "or":
                return self.expr(e[2], env) or self.expr(e[3], env)
            ty = self.infer(e)
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

    # --- ext profile ---------------------------------------------------------------------
    @staticmethod
    def divide(op, ty, a, b, guarded):
        """Zig's integer divisions. Unguarded, a zero divisor, `minInt / -1` and an inexact
        `@divExact` panic; guarded, they give the dividend. `@rem`/`@mod` by `-1` are 0 (rendered
        as a special case: `minInt` by `-1` is illegal behaviour that no safety check catches)."""
        overflow = ty[0] == "i" and b == -1 and a == int_range(ty)[0]
        remainder = op in ("%", "rem", "mod")
        inexact = op == "divExact" and b != 0 and not overflow and a % b != 0
        if guarded and (b == 0 or (overflow and not remainder) or inexact):
            return a
        if b == 0:
            raise _Panic("divideByZero")
        if remainder:
            if b == -1:
                return 0
            floored = a % b  # the sign of the divisor
            return floored if op == "mod" or floored == 0 or (a < 0) == (b < 0) else floored - b
        if overflow:
            raise _Panic("integerOverflow")
        if inexact:
            raise _Panic("exactDivisionRemainder")
        quotient = abs(a) // abs(b)
        if (a < 0) != (b < 0):
            quotient = -quotient if op != "divFloor" or abs(a) % abs(b) == 0 else -quotient - 1
        return quotient

    @staticmethod
    def shift(op, ty, a, count, guarded):
        """Zig's shifts by a `Log2Int` count: guarded, the count is reduced modulo the width;
        unguarded, it is truncated to the count type and a count of the width or more panics."""
        width = bits(ty)
        s = count % width if guarded else count & ((1 << (width - 1).bit_length()) - 1)
        if s >= width:
            raise _Panic("shiftRhsTooBig")
        if op in (">>", "shrExact"):  # a guarded @shrExact clears the low bits first
            return a >> s
        shifted = wrap(ty, a << s)
        if op == "shlExact" and shifted >> s != a:
            if guarded:
                return a
            raise _Panic("shlOverflow")
        return shifted

    def float_result(self, fmt, value):
        if softfloat.is_nan(fmt, value):
            self.nan_seen = True
        return value

    def float_to_int(self, fmt, ty, x, guarded):
        """`@intFromFloat`: a NaN is 0 (always guarded: unchecked illegal behaviour); an integer part
        outside the type panics, or is 0 when guarded."""
        whole = softfloat.to_int(fmt, x)
        if whole == "nan":
            return 0
        if whole == "inf" or not fits(ty, whole):
            if guarded:
                return 0
            raise _Panic("integerPartOutOfBounds")
        return whole

    def ext_expr(self, e, env):
        tag = e[0]
        if tag in ("div", "shift"):
            a, b = self.expr(e[3], env), self.expr(e[4], env)
            return (self.divide if tag == "div" else self.shift)(e[1], e[2], a, b, e[5])
        if tag == "arith":
            a, b = self.expr(e[3], env), self.expr(e[4], env)
            result = {"+": a + b, "-": a - b, "*": a * b}[e[1]]
            if not fits(e[2], result):
                raise _Panic("integerOverflow")
            return result
        if tag == "neg":
            value = -self.expr(e[2], env)
            if not fits(e[1], value):
                raise _Panic("integerOverflow")
            return value
        if tag == "conv":
            value = self.expr(e[4], env)
            if e[1] == "intcast" and not fits(e[3], value):
                raise _Panic("integerOutOfBounds")
            return wrap(e[3], value)
        if tag in ("uindex", "usindex"):
            cells = self.cell(env, e[1])[0]
            index = self.expr(e[2], env)
            if index >= len(cells):
                raise _Panic("outOfBounds")
            return cells[index][0]
        if tag == "unwrap":
            value = self.cell(env, e[1])[0]
            if value is None:
                raise _Panic("unwrapNull")
            return value
        if tag in ("cunreach", "try"):
            status, value = self.call(e[1], [self.expr(a, env) for a in e[2]])
            if status == "err":
                if tag == "try":
                    raise _Fail()
                raise _Panic("unwrapError")
            return value
        if tag == "gcall":
            ty, args = e[2], [self.expr(a, env) for a in e[3]]
            if e[1] == "gsel":
                return args[1] if args[0] else args[2]
            return wrap(ty, args[0] * args[1] + args[0]) if e[1] == "gmix" else wrap(ty, args[0] * args[0])
        if tag == "gpair":
            a, b = self.expr(e[3], env), self.expr(e[4], env)
            return wrap(e[1], a + b) if e[2] == "sum" else b
        if tag == "grep":
            x = result = self.expr(e[3], env)
            for _ in range(e[2]):
                result = wrap(e[1], result * x + x)
            return result
        if tag == "gscale":
            return wrap(e[1], self.expr(e[3], env) * e[2])
        if tag == "fbin":
            fmt = self.infer(e)
            a, b = self.expr(e[2], env), self.expr(e[3], env)
            op = {"+": softfloat.add, "-": softfloat.sub, "*": softfloat.mul, "/": softfloat.div}[e[1]]
            return self.float_result(fmt, op(fmt, a, b))
        if tag == "fun":
            fmt = self.infer(e)
            op = {"sqrt": softfloat.sqrt, "floor": softfloat.floor, "ceil": softfloat.ceil, "trunc": softfloat.trunc,
                  "round": softfloat.round_, "abs": softfloat.fabs, "neg": softfloat.neg}[e[1]]
            return self.float_result(fmt, op(fmt, self.expr(e[2], env)))
        if tag == "i2f":
            return softfloat.from_int(e[2], self.expr(e[3], env))
        if tag == "fconv":
            return self.float_result(e[2], softfloat.convert(e[1], e[2], self.expr(e[3], env)))
        if tag == "f2i":
            return self.float_to_int(e[1], e[2], self.expr(e[3], env), e[4])
        if tag == "fbits":
            return self.expr(e[2], env)  # a NaN is already the canonical quiet NaN
        raise ValueError(tag)


def _infer_static(e, var_types, shape=DEFAULT_SHAPE):
    return infer_type(e, var_types.__getitem__, shape)


def _var_types(program):
    """Names are unique per program, so one flat name -> scalar/pointee type map suffices."""
    types = {g["name"]: g["ty"] for g in program["globals"]}
    shape = shape_of(program)

    def walk(node):
        if isinstance(node, list) and node and isinstance(node[0], str):
            tag = node[0]
            if tag == "let":
                types[node[1]] = node[2]
            elif tag == "ptr":
                types[node[1]] = types.get(node[2])
            elif tag == "while":
                types[node[1]] = "u32"
            elif tag in ("for_slice", "if_opt"):
                types[node[2]] = shape["elem" if tag == "for_slice" else "opt"]
            elif tag == "ptr_elem":
                types[node[1]] = shape["elem"]
            elif tag == "ptr_field":
                types[node[1]] = shape["fields"][node[3]]
            elif tag == "with_create":
                types[node[1]] = node[2]
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


def inputs_of(program):
    return EXT_INPUTS if program.get("profile") == "ext" else INPUTS


def evaluate(program):
    """Expected `entry(a, b)` for each input pair; globals reset on each entry.

    core/wide: the values. ext: an outcome per input, `{"ok": value}` or `{"panic": kind}` (the
    safety check that fires first), with `"nan": true` when a float operation produced a NaN."""
    ext = program.get("profile") == "ext"
    results = []
    for a, b in inputs_of(program):
        machine = Machine(program)
        try:
            status, value = machine.call("work", [a, b])
            assert status == "ok"
            for g in program["globals"]:
                value ^= machine.globals[g["name"]][0] & 0xFFFFFFFF
            outcome = {"ok": value}
        except _Panic as panic:
            if not ext:
                raise
            outcome = {"panic": panic.kind}
        if machine.nan_seen:
            outcome["nan"] = True
        results.append(outcome if ext else value)
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
    if tag in ("var", "deref", "unwrap") and len(node) == 2:
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
    elif tag in ("index", "sindex", "orelse", "field", "uindex", "usindex") and len(node) == 3:
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




class Renderer:
    def __init__(self, program):
        self.program = program
        self.var_types = _var_types(program)
        self.shape = shape_of(program)
        self.slice_len = {}
        self.blocks = 0  # labels and temporaries of ext expression blocks
        self.heap = False

        def walk(node):
            if isinstance(node, list):
                if len(node) == 5 and node[0] == "let_slice":
                    self.slice_len[node[1]] = node[4] - node[3]
                if len(node) == 7 and node[0] in ("with_alloc", "with_create"):
                    self.heap = True
                    if node[0] == "with_alloc":
                        self.slice_len[node[1]] = node[2]
                for child in node:
                    walk(child)
            elif isinstance(node, dict):
                for child in node.values():
                    walk(child)
        walk([f["body"] for f in program["funcs"]])

    def lit(self, ty, v):
        if ty == "bool":
            return "true" if v else "false"
        if ty in FLOATS:  # the exact bits: no decimal rounding, and an infinity has no literal
            return f"@as({ty}, @bitCast(@as(u{softfloat.width(ty)}, 0x{v:x})))"
        return f"@as({ty}, {v})"

    def runtime(self, bindings, result):
        """A block expression whose operands are runtime values: `var`s whose address is taken, so
        Sema neither folds the operation nor rejects comptime-known illegal behaviour."""
        self.blocks += 1
        n = self.blocks
        names = [f"t{chr(ord('a') + k)}{n}" for k in range(len(bindings))]
        decls = "".join(f"var {name}: {ty} = {init}; _ = &{name}; " for name, (ty, init) in zip(names, bindings))
        return f"(blk{n}: {{ {decls}break :blk{n} {result(*names)}; }})"

    def ext_expr(self, e):
        tag = e[0]
        if tag == "div":
            _, op, ty, a, b, guarded = e
            signed, remainder = ty[0] == "i", op in ("%", "rem", "mod")

            def body(x, y):
                call = f"{x} {op} {y}" if op in ("/", "%") else f"@{op}({x}, {y})"
                if remainder and signed:  # minInt by -1 is unchecked illegal behaviour; the result is 0
                    call = f"(if ({y} == -1) @as({ty}, 0) else {call})"
                conds = []
                if guarded:
                    conds.append(f"{y} == 0")
                    if signed and not remainder:
                        conds.append(f"({x} == {int_range(ty)[0]} and {y} == -1)")
                    if op == "divExact":
                        conds.append(f"@rem({x}, {y}) != 0")
                return f"if ({' or '.join(conds)}) {x} else {call}" if conds else call
            return self.runtime([(ty, self.expr(a)), (ty, self.expr(b))], body)
        if tag == "shift":
            _, op, ty, a, b, guarded = e
            count_ty = shift_type(ty)
            count = f"@as({count_ty}, @intCast({self.expr(b)} % {bits(ty)}))" if guarded else \
                f"@as({count_ty}, @truncate({self.expr(b)}))"

            def body(x, s):
                if op in ("<<", ">>"):
                    return f"{x} {op} {s}"
                if op == "shrExact":
                    return f"@shrExact(({x} >> {s}) << {s}, {s})"
                exact = f"@shlExact({x}, {s})"
                return f"if (({x} << {s}) >> {s} != {x}) {x} else {exact}" if guarded else exact
            return self.runtime([(ty, self.expr(a)), (count_ty, count)], body)
        if tag == "arith":
            return self.runtime([(e[2], self.expr(e[3])), (e[2], self.expr(e[4]))], lambda x, y: f"{x} {e[1]} {y}")
        if tag == "neg":
            return self.runtime([(e[1], self.expr(e[2]))], lambda x: f"-{x}")
        if tag == "conv":
            _, form, source, target, inner = e
            if form == "intcast":
                return self.runtime([(source, self.expr(inner))], lambda x: f"@as({target}, @intCast({x}))")
            return {"widen": f"@as({target}, {self.expr(inner)})",
                    "trunc": f"@as({target}, @truncate({self.expr(inner)}))",
                    "bitcast": f"@as({target}, @bitCast({self.expr(inner)}))"}[form]
        if tag in ("uindex", "usindex"):
            return self.runtime([("usize", self.expr(e[2]))], lambda i: f"{e[1]}[{i}]")
        if tag == "unwrap":
            return self.runtime([(f"?{self.shape['opt']}", e[1])], lambda o: f"{o}.?")
        if tag in ("cunreach", "try"):
            call = f"{e[1]}({', '.join(self.expr(a) for a in e[2])})"
            return f"({call} catch unreachable)" if tag == "cunreach" else f"(try {call})"
        if tag == "gcall":
            args = ", ".join(self.expr(a) for a in e[3])
            return f"gany({args})" if e[1] == "gany" else f"{e[1]}({e[2]}, {args})"
        if tag == "gpair":
            pair = f"(GPair({e[1]}){{ .a = {self.expr(e[3])}, .b = {self.expr(e[4])} }})"
            return f"{pair}.sum()" if e[2] == "sum" else f"{pair}.flip().a"
        if tag in ("grep", "gscale"):
            return f"{tag}({e[1]}, {e[2]}, {self.expr(e[3])})"
        if tag == "fbin":
            return f"({self.expr(e[2])} {e[1]} {self.expr(e[3])})"
        if tag == "fun":
            inner = self.expr(e[2])
            return f"(-{inner})" if e[1] == "neg" else f"@{e[1]}({inner})"
        if tag == "i2f":
            return f"@as({e[2]}, @floatFromInt({self.expr(e[3])}))"
        if tag == "fconv":
            return f"@as({e[2]}, @floatCast({self.expr(e[3])}))"
        if tag == "f2i":
            _, fmt, ty, inner, guarded = e
            signed = ty[0] == "i"
            low = softfloat.power_of_two(fmt, bits(ty) - 1, 1) if signed else softfloat.zero(fmt)
            high = softfloat.power_of_two(fmt, bits(ty) - signed)
            low_op = ">" if low == softfloat.inf(fmt, 1) else ">="

            def body(x):
                conds = [f"{x} != {x}"]
                if guarded:  # the integer part lies in the type (an unrepresentable bound is an infinity)
                    conds += [f"!(@trunc({x}) {low_op} {self.lit(fmt, low)})", f"!(@trunc({x}) < {self.lit(fmt, high)})"]
                return f"if ({' or '.join(conds)}) @as({ty}, 0) else @as({ty}, @intFromFloat({x}))"
            return self.runtime([(fmt, self.expr(inner))], body)
        if tag == "fbits":
            word = f"u{softfloat.width(e[1])}"
            return self.runtime([(e[1], self.expr(e[2]))], lambda x: f"if ({x} != {x}) @as({word}, 0x"
                                f"{softfloat.qnan(e[1]):x}) else @as({word}, @bitCast({x}))")
        raise ValueError(tag)

    def expr(self, e):
        tag = e[0]
        if tag in EXT_EXPR_TAGS:
            return self.ext_expr(e)
        if tag == "lit":
            return self.lit(e[1], e[2])
        if tag == "var":
            return e[1]
        if tag == "deref":
            return f"{e[1]}.*"
        if tag == "index":
            return f"{e[1]}[({self.expr(e[2])} % {self.shape['len']})]"
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
            return self.decl(pad, s[1], s[2], self.expr(s[3]), refs)
        if tag == "unreach_if":
            return [f"{pad}if ({self.expr(s[1])}) unreachable;"]
        if tag in ("with_alloc", "with_create"):
            return self.heap_stmt(s, indent, refs)
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

    def heap_stmt(self, s, indent, refs):
        """An allocation from the program's FixedBufferAllocator: a failed one returns `fail`; the
        body is a block of its own (its defers run before an `end` free)."""
        tag, name, what, init, mode, fail, body = s
        pad = "    " * indent
        gpa = "fuzz_fba.allocator()"
        if tag == "with_alloc":
            get, free = f"alloc({self.shape['elem']}, {what})", f"{gpa}.free({name});"
            fill = f"@memset({name}, {self.expr(init)});"
        else:
            get, free, fill = f"create({what})", f"{gpa}.destroy({name});", f"{name}.* = {self.expr(init)};"
        lines = [f"{pad}{{", f"{pad}    const {name} = {gpa}.{get} catch return @as(u32, {fail});"]
        if mode == "defer":
            lines.append(f"{pad}    defer {free}")
        lines += [f"{pad}    {fill}", f"{pad}    {{"] + self.block(body, indent + 2, refs) + [f"{pad}    }}"]
        if mode == "end" and not _block_exits(body):
            lines.append(f"{pad}    {free}")
        return lines + [f"{pad}}}"]

    def wide_stmt(self, s, indent, refs):
        pad = "    " * indent
        tag = s[0]
        elem, length, opt = self.shape["elem"], self.shape["len"], self.shape["opt"]
        if tag == "let_array":
            return self.decl(pad, s[1], f"[{length}]{elem}", ".{ " + ", ".join(self.expr(e) for e in s[2]) + " }", refs)
        if tag in ("arr_set", "sstore"):
            length = length if tag == "arr_set" else self.slice_len[s[1]]
            return [f"{pad}{s[1]}[({self.expr(s[2])} % {length})] {s[3]} {self.expr(s[4])};"]
        if tag == "ptr_elem":
            lines = [f"{pad}const {s[1]} = &{s[2]}[({self.expr(s[3])} % {length})];"]
        elif tag == "ptr_field":
            lines = [f"{pad}const {s[1]} = &{s[2]}.{s[3]};"]
        elif tag == "let_slice":
            return self.decl(pad, s[1], f"[]{elem}", f"{s[2]}[{s[3]}..{s[4]}]", refs)
        elif tag == "for_slice":
            capture = s[2] if self._uses(s[2], refs) else "_"
            return ([f"{pad}for ({s[1]}) |{capture}| {{"] + self.block(s[3], indent + 1, refs) + [f"{pad}}}"])
        elif tag == "let_opt":
            return self.decl(pad, s[1], f"?{opt}", f"if ({self.expr(s[2])}) {self.expr(s[3])} else null", refs)
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
        profile = program.get("profile", "core")
        wide, ext, fields = profile != "core", profile == "ext", self.shape["fields"]
        lines = [f"// Generated by tests/roadmap/fuzz/zig_gen.py from seed {program['seed']}"
                 + ("" if not wide else f" ({profile} profile)") + "; do not edit.",
                 'const std = @import("std");', "",
                 "const U = union(enum) { a: u32, b: i32 };",
                 "const FuzzError = error{Fuzz};", ""]
        if wide:
            lines += [f"const P = struct {{ x: {fields['x']}, y: {fields['y']} }};", ""]
        for g in program["globals"]:
            lines.append(f"var {g['name']}: {g['ty']} = {g['init']};")
        if self.heap:
            # A buffer aligned for every type, so allocation offsets do not depend on its address. The
            # alignment must be the type's own: the AIR export does not record a declared `align(N)`,
            # so the model places `[N]u8 align(16)` at any address (`collectGlobals`, Air2Lean/Emit.lean),
            # and a pointer constant of a less aligned type (`&fuzz_buf` as bytes) caps it. `entry`
            # therefore casts the pointer at run time.
            lines += [f"var fuzz_buf: [{FBA_BYTES // 16}]u128 = undefined;",
                      "var fuzz_fba: std.heap.FixedBufferAllocator = .{ .end_index = 0, .buffer = &.{} };"]
        lines += ["", "fn bump(p: *u32, d: u32) void {", "    p.* +%= d;", "}", "",
                  "fn swap(a: *u32, b: *u32) void {", "    const t = a.*;", "    a.* = b.*;",
                  "    b.* = t;", "}", ""]
        if wide:
            lines += ["fn bumpP(p: *P, d: u32) void {"] + [f"    p.{f} +%= {self.delta(fields[f])};" for f in "xy"] \
                + ["}", ""]
        if ext:
            lines += GENERIC_SOURCE
        for f in program["funcs"]:
            lines += self.function(f)
        if ext:
            return "\n".join(lines + self.entry() + ["}", "", "comptime {", "    _ = &entry;", "}", ""])
        lines += self.entry()
        lines += ["}", "", "comptime {", "    _ = &entry;", "}", "",
                  f'test "{module}" {{']
        for (a, b), value in zip(INPUTS, expected):
            lines.append(f"    try std.testing.expectEqual(@as(u32, {value}), entry({a}, {b}));")
        lines += ["}", ""]
        return "\n".join(lines)

    @staticmethod
    def delta(ty):
        """`bumpP`'s u32 step as a field's type: truncated or zero-extended, then reinterpreted."""
        if ty == "u32":
            return "d"
        if bits(ty) > 32:
            return f"@as({ty}, d)"
        low = "d" if bits(ty) == 32 else f"@as(u{bits(ty)}, @truncate(d))"
        return f"@as({ty}, @bitCast({low}))" if ty[0] == "i" else low

    def entry(self):
        """`entry` up to its closing brace: reset the program's state, run `work`, fold in the globals."""
        program = self.program
        lines = ["pub fn entry(a: u32, b: u32) u32 {"]
        if self.heap:
            lines += [f"    var fuzz_base: *[{FBA_BYTES // 16}]u128 = &fuzz_buf;", "    _ = &fuzz_base;",
                      "    fuzz_fba = .{ .end_index = 0, .buffer = @as([*]u8, @ptrCast(fuzz_base))"
                      f"[0..{FBA_BYTES}] }};"]
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
        return lines

    def driver(self, module):
        """The native harness of an ext program: a root file that runs every input and prints one
        outcome line each. Its panic handler prints the safety check's name and goes on with the
        next input (the abandoned frames stay on the stack; `entry` resets all state)."""
        rows = ", ".join(f".{{ {a}, {b} }}" for a, b in inputs_of(self.program))
        lines = ["// Generated by tests/roadmap/fuzz/zig_gen.py; do not edit.", 'const std = @import("std");',
                 f'const fuzz = @import("{module}.zig");', "", f"const rows = [_][2]u32{{ {rows} }};",
                 "var next: usize = 0;", "",
                 "fn report(kind: []const u8) noreturn {",
                 '    std.debug.print("FUZZ {d} panic {s}\\n", .{ next - 1, kind });', "    run();", "}", "",
                 "fn run() noreturn {", "    while (next < rows.len) {", "        const row = rows[next];",
                 "        next += 1;", "        const value = fuzz.entry(row[0], row[1]);",
                 '        std.debug.print("FUZZ {d} ok {d}\\n", .{ next - 1, value });', "    }",
                 "    std.process.exit(0);", "}", "", "pub fn main() void {", "    run();", "}", "",
                 "pub const panic = struct {"]
        for name, params in PANIC_MEMBERS:
            lines += [f"    pub fn {name}({params}) noreturn {{", f'        report("{name}");', "    }"]
        return "\n".join(lines + ["};", ""])


# Every member of `std.builtin.panic` of Zig 0.14.1 to 0.17.1 (as tests/diff/common.zig): a version
# looks up only its own. `call` is `@panic`.
PANIC_MEMBERS = (
    ("call", "_: []const u8, _: ?usize"), ("sentinelMismatch", "_: anytype, _: anytype"),
    ("unwrapError", "_: anyerror"), ("outOfBounds", "_: usize, _: usize"),
    ("startGreaterThanEnd", "_: usize, _: usize"), ("inactiveUnionField", "_: anytype, _: anytype"),
    ("sliceCastLenRemainder", "_: usize"), ("unexpectedErrorCode", "_: anyerror")) + tuple(
    (name, "") for name in (
        "reachedUnreachable", "unwrapNull", "castToNull", "incorrectAlignment", "invalidErrorCode",
        "integerOutOfBounds", "integerOverflow", "shlOverflow", "shrOverflow", "divideByZero",
        "exactDivisionRemainder", "integerPartOutOfBounds", "corruptSwitch", "shiftRhsTooBig", "invalidEnumValue",
        "forLenMismatch", "copyLenMismatch", "memcpyAlias", "noreturnReturned", "castTruncatedData",
        "negativeToUnsigned", "memcpyLenMismatch", "loadUninstantiableType"))

GENERIC_SOURCE = """\
fn gsel(comptime T: type, t: bool, a: T, b: T) T {
    return if (t) a else b;
}

fn gmix(comptime T: type, a: T, b: T) T {
    return (a *% b) +% a;
}

fn gany(a: anytype) @TypeOf(a) {
    return a *% a;
}

fn grep(comptime T: type, comptime d: u8, a: T) T {
    var r = a;
    inline for (0..d) |_| {
        r = (r *% a) +% a;
    }
    return r;
}

fn gscale(comptime T: type, comptime d: comptime_int, a: T) T {
    return a *% d;
}

fn GPair(comptime T: type) type {
    return struct {
        a: T,
        b: T,

        fn sum(p: @This()) T {
            return p.a +% p.b;
        }

        fn flip(p: @This()) @This() {
            return .{ .a = p.b, .b = p.a };
        }
    };
}
""".splitlines()


def module_name(program):
    return f"fuzz_{ {'wide': 'w', 'ext': 'e'}.get(program.get('profile', 'core'), 's')}{program['seed']}"


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
    if program.get("profile") == "ext":
        body = json.dumps(program["funcs"])
        if any(f'"{ty}"' in body for ty in program["types"]["ints"]):
            found.add("int_width")
        for feature, tags in (("divmod", ("div",)), ("shift", ("shift",)), ("checked", ("arith", "neg")),
                              ("conv", ("conv",)), ("bounds", ("uindex", "usindex")),
                              ("unwrap", ("unwrap", "cunreach")), ("try", ("try",)),
                              ("float", ("fbin", "fun", "i2f", "fconv", "f2i", "fbits")),
                              ("alloc", ("with_alloc", "with_create")),
                              ("generic", ("gcall", "gpair", "grep", "gscale"))):
            if any(f'["{tag}"' in body for tag in tags):
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
             "switch", "switch_union", "defer", "errdefer", "return", "fail", "break"} | WIDE_STMT_TAGS | EXT_STMT_TAGS
EXPR_TAGS = {"lit", "var", "deref", "cmp", "not", "bin", "shr", "mod", "cast", "call", "catch", "index", "sindex",
             "orelse", "field"} | EXT_EXPR_TAGS


def _expr_type(program, path, var_types):
    try:
        return _infer_static(_get(program, path), var_types, shape_of(program))
    except (KeyError, IndexError, TypeError, TypeError_):
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
                                                if _tagged(n, ("call", "catch", "cunreach", "try")) and n[1] == name
                                                else None)}
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
            elif s[0] in ("with_alloc", "with_create"):
                inner = [s[6]]
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
        # Guard an unguarded operation (`false` -> `true` is shorter), and allocate less.
        if _tagged(node, ("div", "shift", "f2i")) and node[-1] is False:
            yield _set(program, path + (len(node) - 1,), True)
        if _tagged(node, ("with_alloc",)) and node[2] > 1:
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
    outcomes = {}
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
        if args.profile == "ext":
            for outcome in evaluate(program):
                kind = outcome.get("panic", "ok")
                outcomes[kind] = outcomes.get(kind, 0) + 1
    missing = [f for f, n in counts.items() if n == 0]
    report = {"profile": args.profile, "seeds": args.seeds, "start": args.start, "features": counts}
    if outcomes:
        report["outcomes"] = dict(sorted(outcomes.items()))
    print(json.dumps(report))
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
    renderer = Renderer(program)
    (out / f"{module}.zig").write_text(renderer.source(module, expected))
    (out / "program.json").write_text(json.dumps(program, indent=1) + "\n")
    case = {"module": module, "inputs": inputs_of(program), "expected": expected}
    if program.get("profile") == "ext":
        # The native harness, and what the translation needs beyond the module's own functions: the
        # translated allocator's code (docs/allocator-model.md) when the program allocates.
        (out / "driver.zig").write_text(renderer.driver(module))
        case["translate_args"] = ["--filter", f"{module}.,heap.FixedBufferAllocator,mem.,math.,debug.assert",
                                  "--closure", f"{module}.*", "--allocator-model", "translated"] \
            if renderer.heap else []
    (out / "expected.json").write_text(json.dumps(case) + "\n")
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
    lines = ["", f"namespace {namespace}.FuzzCheck"]
    ext = any(isinstance(outcome, dict) for outcome in expected)
    if ext:
        # One outcome line per input, compared by `lean-verify` (a `#guard` would not show the value).
        lines += ["private def outcome (r : Zig.Result (BitVec 32)) : String :=", "  match r.run with",
                  '  | some (.ok v) => s!"ok {v.toNat}"', '  | some (.error e) => s!"fail {repr e}"',
                  '  | none => "diverge"']
    else:
        lines.append("private def successful {α : Type} (r : Zig.Result α) : Option α := "
                     "Option.bind r Except.toOption")
    for k, ((a, b), value) in enumerate(zip(EXT_INPUTS if ext else INPUTS, expected)):
        call = f"({namespace}.entry {a}#32 {b}#32)"
        run = f"({call}.run' ({namespace}.mem0 .fresh))" if memory else call
        lines.append(f'#eval IO.println s!"FUZZ {k} {{outcome {run}}}"' if ext
                     else f"#guard successful {run} == some {value}#32")
    lines.append(f"end {namespace}.FuzzCheck")
    return "\n".join(lines) + "\n"


def cmd_lean_checks(args):
    case = json.loads(Path(args.expected).read_text())
    text = Path(args.gen).read_text()
    Path(args.out).write_text(text + lean_checks(text, args.namespace, case["expected"]))
    return 0


def panic_policy():
    """`std.builtin.panic` member -> the `Zig.Error` constructor of its check (scripts/panic-policy.tsv)."""
    table = Path(__file__).resolve().parents[3] / "scripts" / "panic-policy.tsv"
    return dict(line.split("\t") for line in table.read_text().splitlines() if line)


def verify(expected, text, side):
    """Compare the `FUZZ <k> ...` lines of one side with the reference outcomes; the mismatches.

    native: `ok <value>` or `panic <member>`, exactly. lean: `ok <value>` or `fail Zig.Error.<ctor>`
    with the constructor the policy table gives the member. An input whose evaluation made a NaN may
    also be `.unspecified` in the model (a stored NaN's bits are undefined there, docs/floats.md)."""
    policy = panic_policy()
    got = {}
    for line in text.splitlines():
        parts = line.split(" ", 2)
        if len(parts) == 3 and parts[0] == "FUZZ" and parts[1].isdigit():
            got[int(parts[1])] = parts[2].strip()
    errors = []
    for k, outcome in enumerate(expected):
        if "ok" in outcome:
            want = [f"ok {outcome['ok']}"]
        elif side == "native":
            want = [f"panic {outcome['panic']}"]
        else:
            want = [f"fail Zig.Error.{policy[outcome['panic']]}"]
        if side == "lean" and outcome.get("nan"):
            want.append("fail Zig.Error.unspecified")
        if got.get(k) not in want:
            errors.append(f"error: {side} input {k}: expected {want[0]}, got {got.get(k, 'no outcome line')}")
    return errors


def cmd_verify(args):
    case = json.loads(Path(args.expected).read_text())
    errors = verify(case["expected"], Path(args.output).read_text(), args.side)
    print("\n".join(errors) if errors else f"{args.side}: {len(case['expected'])} outcomes agree")
    return 1 if errors else 0


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
    verify_ = sub.add_parser("verify", help="compare an ext case's FUZZ outcome lines with expected.json")
    verify_.add_argument("side", choices=("native", "lean"))
    verify_.add_argument("expected")
    verify_.add_argument("output")
    args = parser.parse_args(argv)
    return {"light": cmd_light, "emit": cmd_emit, "lean-checks": cmd_lean_checks,
            "shrink": cmd_shrink, "verify": cmd_verify}[args.command_name](args)


if __name__ == "__main__":
    sys.exit(main())
