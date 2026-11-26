#!/usr/bin/env python3
"""Evaluate a generated Lean function on concrete inputs without Zig (P08).

Appends a small driver to a copy of a `Gen.lean` and runs it with `lake env lean --run`, so the
generated model is interpreted directly: no native toolchain, no libm archive. An optional
precondition and postcondition (Lean text over the parameter names and `r : Except Zig.Error T`)
are decided per input.

Supported functions: `Zig.Result` and `Zig.MemM` functions (the latter run from the program's
start memory `mem0 .fresh`) whose parameters and result are values. The value kinds are the
classes below, one per kind the translator emits; a type is resolved by walking the generated
Lean type and the AIR type table together, and every operation on a value (enumeration, the row
encoding, the Lean decoder and renderer, the Zig literal, reading a native result) is that
class's method, so a nested type needs nothing of its own. Anything else is `Unsupported` with
the reason (a place in memory, a float, a vector, a concurrent function, a Lean declaration that
does not line up with the AIR type); callers report it as unsolved. Nothing is guessed.

A value is written the way the native differential harness renders it (tests/diff/common.zig,
`renderPayload`): an integer, a bool, an enum's tag value, `{"field":…}` for a struct,
`{"<active field>":…}` for a tagged union, `null` or the payload for an optional,
`{"err":"Name"}` or the payload for an error union, a JSON array for a read-only slice.

Output protocol of the driver (tab separated): `O idx obs` an observation, `V idx obs` a
postcondition violation, `N idx` no result within fuel, `S checked skipped none violations`.
"""
from dataclasses import dataclass
import hashlib
import itertools
import json
import os
from pathlib import Path
import random
import re
import signal
import subprocess
import tempfile

MAX_CASES = 20000
SUPPORTED = 'integers, bool, void, enums, structs, tagged unions, optionals, error unions and read-only slices of those'
# The constructors of `Zig.Error` a recorded outcome can carry (ZigLean/Basic.lean).
ERRORS = ('overflow', 'outOfBounds', 'divByZero', 'unreachable', 'panic', 'unspecified', 'illegal', 'deadlock',
          'unsupportedTimer', 'trap', 'stackOverflow')


class Unsupported(Exception):
    pass


class Mismatch(Unsupported):
    """A JSON value that is not a value of the type."""


def lean_str(text):
    """A Lean string literal (JSON escapes are Lean escapes)."""
    return json.dumps(text)


def combine(lists, rng, cap=64):
    """Tuples over `lists`: the whole product when small, else each list varied alone (all of them, also
    beyond `cap`: every value of every list occurs) plus seeded picks up to `cap`."""
    size = 1
    for values in lists: size *= len(values)
    if size <= cap: return list(itertools.product(*lists))
    first = tuple(values[0] for values in lists)
    out = [first]
    for k, values in enumerate(lists):
        out += [first[:k] + (v,) + first[k + 1:] for v in values[1:]]
    while len(out) < cap: out.append(tuple(rng.choice(values) for values in lists))
    return out


# --- Value kinds --------------------------------------------------------------------------
# Every kind has: `lean` (the Lean type), `size()` (the number of values, None when unbounded),
# `values()` (all of them, when bounded), `boundary(rng)` and `random(rng)` (candidates),
# `shrinks(v)` (the values one step simpler than `v`, for minimizing a violating input),
# `parse(j, wide)` (a JSON value of the differential format -> the value, or Mismatch), `flat(v)`
# (the row encoding, a list of naturals), `decoder(emit)` and `renderer(emit, wide)` (the names of
# Lean functions `List Nat -> Option (T × List Nat)` and `T -> String`), `zig(v)` (a Zig
# expression, typed by its result location) and `extern()` (its C-ABI spelling, for `export fn`).


class Kind:
    # Every kind states these three itself: a kind that did not would be guessed about.
    def weight(self, v):
        """The size of a value, for the smallest-first order: the magnitude of a number, the items of a slice."""
        raise NotImplementedError

    def ints(self):
        """The integer kinds the rendered value contains (the harness quotes all of them or none)."""
        raise NotImplementedError

    def renders(self, what):
        """Whether a value can be rendered as `null` (`what='null'`) or as an object with the key `err`
        (`what='err'`): under an optional or an error union that rendering would not say which case it is."""
        raise NotImplementedError

    def extern(self):
        raise Unsupported(f'{self.lean} cannot cross an `export fn` boundary; declare the function `pub`')


@dataclass(frozen=True)
class Int(Kind):
    bits: int
    signed: bool

    @property
    def lean(self): return f'BitVec {self.bits}'
    def size(self): return 2 ** self.bits
    def of_bits(self, a): return a - 2 ** self.bits if self.signed and a >= 2 ** (self.bits - 1) else a
    def values(self): return (self.of_bits(a) for a in range(self.size()))

    def boundary(self, rng):
        top = self.size()
        vals = list(range(0, min(top, 9))) + [top - 1, top - 2, top // 2, top // 2 - 1, top // 2 + 1]
        return [self.of_bits(a) for a in sorted({v % top for v in vals})]

    def random(self, rng): return self.of_bits(rng.randrange(self.size()))

    def parse(self, j, wide=False):
        if wide and isinstance(j, str) and re.fullmatch(r'-?\d+', j): j = int(j)
        if type(j) is bool: j = int(j)
        # A signed integer is in its own range. An unsigned one may also be written as the signed value of
        # the same bits: without an AIR type table every integer is assumed unsigned, and rows carry signs.
        top = 2 ** (self.bits - 1) if self.signed else 2 ** self.bits
        if type(j) is not int or not -2 ** (self.bits - 1) <= j < top: raise Mismatch(f'{j!r} is not a {self.lean}')
        return self.of_bits(j % self.size())

    def shrinks(self, v):
        """Toward zero: zero, and `v` moved by each power of two (so a threshold is reached in few rounds)."""
        sign = 1 if v > 0 else -1
        return sorted({0} | {v - sign * 2 ** k for k in range(self.bits) if 2 ** k <= abs(v)} - {v}, key=abs)

    def weight(self, v): return abs(v)
    def ints(self): return [self]
    def renders(self, what): return False
    def flat(self, v): return [v % self.size()]
    def decoder(self, emit): return emit.define(('dec', self), f'| a :: l => some (BitVec.ofNat {self.bits} a, l)\n  | [] => none')

    def renderer(self, emit, wide):
        text = 'toString v.toInt' if self.signed else 'toString v.toNat'
        return emit.define(('ren', self, wide), 'fun v => ' + (f'"\\"" ++ {text} ++ "\\""' if wide else text))

    def zig(self, v): return str(v)
    def extern(self): return f"{'i' if self.signed else 'u'}{self.bits}"


@dataclass(frozen=True)
class Bool(Kind):
    lean = 'Bool'
    def size(self): return 2
    def values(self): return iter((False, True))
    def boundary(self, rng): return [False, True]
    def random(self, rng): return rng.random() < 0.5

    def parse(self, j, wide=False):
        if j is True or j is False: return j
        if type(j) is int and j in (0, 1): return bool(j)
        raise Mismatch(f'{j!r} is not a Bool')

    def shrinks(self, v): return [False] if v else []
    def weight(self, v): return int(v)
    def ints(self): return []
    def renders(self, what): return False
    def flat(self, v): return [int(v)]
    def decoder(self, emit): return emit.define(('dec', self), '| a :: l => some (a != 0, l)\n  | [] => none')
    def renderer(self, emit, wide): return emit.define(('ren', self), 'fun v => if v then "1" else "0"')
    def zig(self, v): return 'true' if v else 'false'
    def extern(self): return 'bool'


@dataclass(frozen=True)
class Unit(Kind):
    lean = 'Unit'
    def size(self): return 1
    def values(self): return iter((None,))
    def boundary(self, rng): return [None]
    def random(self, rng): return None

    def parse(self, j, wide=False):
        if j is not None: raise Mismatch(f'{j!r} is not void')
        return None

    def shrinks(self, v): return []
    def weight(self, v): return 0
    def ints(self): return []
    def renders(self, what): return what == 'null'
    def flat(self, v): return []
    def decoder(self, emit): return emit.define(('dec', self), 'fun l => some ((), l)')
    def renderer(self, emit, wide): return emit.define(('ren', self), 'fun _ => "null"')
    def zig(self, v): return '{}'
    def extern(self): return 'void'


@dataclass(frozen=True)
class Enum(Kind):
    """An enum is its tag value. `named` are the tag values with a name; a non-exhaustive enum has every tag value."""
    lean: str
    tag: Int
    named: tuple            # ((field name, tag value), ...)
    exhaustive: bool

    def size(self): return len(self.named) if self.exhaustive else self.tag.size()
    def values(self): return (v for _, v in self.named) if self.exhaustive else self.tag.values()

    def boundary(self, rng):
        out = [v for _, v in self.named[:16]]
        return out if self.exhaustive else out + [v for v in self.tag.boundary(rng) if v not in out]

    def random(self, rng): return rng.choice(self.named)[1] if self.exhaustive else self.tag.random(rng)

    def parse(self, j, wide=False):
        v = self.tag.parse(j)                      # the harness never quotes an enum's tag value
        if type(j) is not int or (self.exhaustive and all(v != n for _, n in self.named)): raise Mismatch(f'{j!r} is not a {self.lean}')
        return v

    def shrinks(self, v): return [n for _, n in self.named if n != v] if self.exhaustive else self.tag.shrinks(v)
    def weight(self, v): return abs(v)
    def ints(self): return []                      # a tag value is never quoted
    def renders(self, what): return False
    def flat(self, v): return self.tag.flat(v)

    def bits(self, text):
        return f'Zig.val {str(self.tag.signed).lower()} {text}'

    def decoder(self, emit):
        return emit.define(('dec', self), f'| a :: l => ({self.lean}.ofInt? ({self.bits(f"(BitVec.ofNat {self.tag.bits} a)")})).map (·, l)\n'
                                          '  | [] => none')

    def renderer(self, emit, wide):
        return emit.define(('ren', self), f'fun v => toString ({self.bits(f"({self.lean}.toBits v)")})')

    def zig(self, v):
        name = next((n for n, value in self.named if value == v), None)
        return f'.@"{name}"' if name is not None else f'@enumFromInt({v})'


@dataclass(frozen=True)
class Struct(Kind):
    lean: str
    fields: tuple           # ((Zig field name, Lean field name, kind), ...)

    def size(self):
        total = 1
        for _, _, t in self.fields:
            if t.size() is None: return None
            total *= t.size()
        return total

    def make(self, row): return {name: v for (name, _, _), v in zip(self.fields, row)}
    def values(self): return (self.make(row) for row in itertools.product(*[list(t.values()) for _, _, t in self.fields]))
    def boundary(self, rng): return [self.make(row) for row in combine([t.boundary(rng) for _, _, t in self.fields], rng)]
    def random(self, rng): return self.make([t.random(rng) for _, _, t in self.fields])

    def parse(self, j, wide=False):
        if not isinstance(j, dict) or list(j) != [name for name, _, _ in self.fields]: raise Mismatch(f'{j!r} is not a {self.lean}')
        return {name: t.parse(j[name], wide) for name, _, t in self.fields}

    def shrinks(self, v): return [{**v, name: s} for name, _, t in self.fields for s in t.shrinks(v[name])]
    def weight(self, v): return sum(t.weight(v[name]) for name, _, t in self.fields)
    def ints(self): return [i for _, _, t in self.fields for i in t.ints()]
    def renders(self, what): return what == 'err' and any(name == 'err' for name, _, _ in self.fields)
    def flat(self, v): return [a for name, _, t in self.fields for a in t.flat(v[name])]

    def decoder(self, emit):
        steps = ''.join(f'    let (f{k}, l) ← {t.decoder(emit)} l\n' for k, (_, _, t) in enumerate(self.fields))
        init = ', '.join(f'{lean} := f{k}' for k, (_, lean, _) in enumerate(self.fields))
        return emit.define(('dec', self), f'fun l => do\n{steps}    pure (({{ {init} }} : {self.lean}), l)')

    def renderer(self, emit, wide):
        parts = [lean_str((',' if k else '{') + json.dumps(name) + ':') + f' ++ {t.renderer(emit, wide)} v.{lean}'
                 for k, (name, lean, t) in enumerate(self.fields)]
        return emit.define(('ren', self, wide), 'fun v => ' + ' ++ '.join(parts + [lean_str('}')]) if parts else 'fun _ => "{}"')

    def zig(self, v): return '.{ ' + ', '.join(f'.@"{name}" = {t.zig(v[name])}' for name, _, t in self.fields) + ' }'


@dataclass(frozen=True)
class Union(Kind):
    """A tagged union: `{"<active field>": payload}`. `undef` are the Lean constructors of a payload left undefined."""
    lean: str
    fields: tuple           # ((Zig field name, payload kind), ...)
    ctors: tuple            # the Lean constructor of each field
    undef: tuple            # Lean constructor names that are no Zig value

    def size(self):
        total = 0
        for _, t in self.fields:
            if t.size() is None: return None
            total += t.size()
        return total

    def values(self): return ({name: v} for name, t in self.fields for v in t.values())
    def boundary(self, rng): return [{name: v} for name, t in self.fields for v in t.boundary(rng)[:16]]

    def random(self, rng):
        name, t = rng.choice([f for f in self.fields if f[1].size() != 0])   # a payload type without values has no value
        return {name: t.random(rng)}

    def active(self, v):
        (name, payload), = v.items()
        return next((k, t, payload) for k, (field, t) in enumerate(self.fields) if field == name)

    def parse(self, j, wide=False):
        if not isinstance(j, dict) or len(j) != 1 or next(iter(j)) not in [name for name, _ in self.fields]:
            raise Mismatch(f'{j!r} is not a {self.lean}')
        (name, payload), = j.items()
        return {name: dict(self.fields)[name].parse(payload, wide)}

    def shrinks(self, v):
        k, t, payload = self.active(v)
        return [{self.fields[k][0]: s} for s in t.shrinks(payload)]

    def weight(self, v):
        _, t, payload = self.active(v)
        return t.weight(payload)

    def ints(self): return [i for _, t in self.fields for i in t.ints()]
    def renders(self, what): return what == 'err' and any(name == 'err' for name, _ in self.fields)

    def flat(self, v):
        k, t, payload = self.active(v)
        return [k] + t.flat(payload)

    def ctor(self, k, value):
        """The Lean constructor application of field `k` (a field without payload has no argument)."""
        return f'{self.lean}.{self.ctors[k]}' + ('' if isinstance(self.fields[k][1], Unit) else f' {value}')

    def decoder(self, emit):
        arms = ''.join(f'    | {k} => ({t.decoder(emit)} l).map fun (v, l) => (({self.ctor(k, "v")}), l)\n'
                       for k, (_, t) in enumerate(self.fields))
        return emit.define(('dec', self), f'| k :: l =>\n    match k with\n{arms}    | _ => none\n  | [] => none')

    def renderer(self, emit, wide):
        arms = ''.join(f'  | {self.ctor(k, "v")} => ' + lean_str('{' + json.dumps(name) + ':')
                       + (' ++ "null}"\n' if isinstance(t, Unit) else f' ++ {t.renderer(emit, wide)} v ++ "}}"\n')
                       for k, (name, t) in enumerate(self.fields))
        # A payload that a retag left undefined is no Zig value: it never equals a native result.
        if self.undef: arms += '  | ' + ' | '.join(f'{self.lean}.{c} ..' for c in self.undef) + ' => "{\\"undefined_payload\\":null}"\n'
        return emit.define(('ren', self, wide), 'fun\n' + arms.rstrip('\n'))

    def zig(self, v):
        (name, payload), = v.items()
        return f'.{{ .@"{name}" = {dict(self.fields)[name].zig(payload)} }}'


@dataclass(frozen=True)
class Opt(Kind):
    child: Kind

    @property
    def lean(self): return f'Option ({self.child.lean})'
    def size(self): return None if self.child.size() is None else 1 + self.child.size()
    def values(self): return itertools.chain((None,), self.child.values())
    def boundary(self, rng): return [None] + self.child.boundary(rng)
    def random(self, rng): return None if self.child.size() == 0 or rng.random() < 0.25 else self.child.random(rng)
    def parse(self, j, wide=False): return None if j is None else self.child.parse(j, wide)
    def shrinks(self, v): return [] if v is None else [None] + self.child.shrinks(v)
    def weight(self, v): return 0 if v is None else self.child.weight(v)
    def ints(self): return self.child.ints()
    def renders(self, what): return what == 'null' or self.child.renders(what)
    def flat(self, v): return [0] if v is None else [1] + self.child.flat(v)

    def decoder(self, emit):
        return emit.define(('dec', self), '| 0 :: l => some (none, l)\n'
                           f'  | _ :: l => ({self.child.decoder(emit)} l).map fun (v, l) => (some v, l)\n  | [] => none')

    def renderer(self, emit, wide):
        return emit.define(('ren', self, wide), f'fun\n  | none => "null"\n  | some v => {self.child.renderer(emit, wide)} v')

    def zig(self, v): return 'null' if v is None else self.child.zig(v)


@dataclass(frozen=True)
class ErrUnion(Kind):
    errors: tuple
    payload: Kind

    @property
    def lean(self): return f'Except Zig.ErrName ({self.payload.lean})'
    def size(self): return None if self.payload.size() is None else len(self.errors) + self.payload.size()
    def error(self, v): return v['err'] if isinstance(v, dict) and list(v) == ['err'] and v['err'] in self.errors else None
    def values(self): return itertools.chain(({'err': e} for e in self.errors), self.payload.values())
    def boundary(self, rng): return [{'err': e} for e in self.errors] + self.payload.boundary(rng)

    def random(self, rng):
        error = self.errors and (self.payload.size() == 0 or rng.random() < 0.25)
        return {'err': rng.choice(self.errors)} if error else self.payload.random(rng)

    def parse(self, j, wide=False):
        if isinstance(j, dict) and list(j) == ['err']:
            if j['err'] not in self.errors: raise Mismatch(f'{j!r} is not an error of {self.lean}')
            return {'err': j['err']}
        return self.payload.parse(j, wide)

    def shrinks(self, v):
        return self.payload.shrinks(v) if self.error(v) is None else [{'err': e} for e in self.errors if e != v['err']]

    def weight(self, v): return self.payload.weight(v) if self.error(v) is None else 1
    def ints(self): return self.payload.ints()
    def renders(self, what): return what == 'err' or self.payload.renders(what)

    def flat(self, v):
        name = self.error(v)
        return [0] + self.payload.flat(v) if name is None else [1 + self.errors.index(name)]

    def decoder(self, emit):
        names = '[' + ', '.join(lean_str(e) for e in self.errors) + ']'
        return emit.define(('dec', self), f'| 0 :: l => ({self.payload.decoder(emit)} l).map fun (v, l) => (.ok v, l)\n'
                           f'  | k :: l => (({names} : List String)[k - 1]?).map fun e => (.error e, l)\n  | [] => none')

    def renderer(self, emit, wide):
        return emit.define(('ren', self, wide), 'fun\n  | .error e => "{\\"err\\":\\"" ++ e ++ "\\"}"\n'
                           f'  | .ok v => {self.payload.renderer(emit, wide)} v')

    def zig(self, v):
        name = self.error(v)
        return self.payload.zig(v) if name is None else f'error.@"{name}"'


@dataclass(frozen=True)
class Slice(Kind):
    """A read-only slice of a function that uses no memory: the translator passes its items (`Array T`)."""
    child: Kind
    MAX_LEN = 4

    @property
    def lean(self): return f'Array ({self.child.lean})'
    def size(self): return None

    def boundary(self, rng):
        items = self.child.boundary(rng)
        out = [[]] + [[a] for a in items[:8]] + [[a, b] for a in items[:3] for b in items[:3]]
        return out + [self.random(rng) for _ in range(4)]

    def random(self, rng):
        return [] if self.child.size() == 0 else [self.child.random(rng) for _ in range(rng.randrange(self.MAX_LEN + 1))]

    def parse(self, j, wide=False):
        if not isinstance(j, list): raise Mismatch(f'{j!r} is not a slice')
        return [self.child.parse(item, wide) for item in j]

    def shrinks(self, v):
        """Without one item, or with one item shrunk."""
        return [v[:k] + v[k + 1:] for k in range(len(v))] + [v[:k] + [s] + v[k + 1:] for k in range(len(v)) for s in self.child.shrinks(v[k])]

    def weight(self, v): return len(v) + sum(self.child.weight(item) for item in v)
    def ints(self): return self.child.ints()
    def renders(self, what): return False
    def flat(self, v): return [len(v)] + [a for item in v for a in self.child.flat(item)]
    def decoder(self, emit): return emit.define(('dec', self), f'| n :: l => A2LEval.many {self.child.decoder(emit)} n l\n  | [] => none')
    def renderer(self, emit, wide): raise Unsupported('a slice result is a place in memory, not a value')
    def zig(self, v): return '&.{ ' + ', '.join(self.child.zig(item) for item in v) + ' }'


class Emit:
    """The Lean functions of the kinds a driver uses: one definition per kind, shared by every use."""
    def __init__(self):
        self.names, self.text = {}, []

    def define(self, key, body):
        if key not in self.names:
            op, t = key[0], key[1]
            self.names[key] = name = f'A2LEval.{op}{len(self.names)}'
            head = f'List Nat → Option (({t.lean}) × List Nat)' if op == 'dec' else f'({t.lean}) → String'
            self.text.append(f'def {name} : {head} :=\n  {body}' if body.startswith('fun') else f'def {name} : {head}\n  {body}')
        return self.names[key]


# --- Types: the generated Lean type and the AIR type, walked together ---------------------

DECL = re.compile(r'^(structure|inductive)[ \t]+(\S+)[ \t]+where[ \t]*\n((?:[ \t]+\S.*\n)*)', re.M)
IDENT = r'[A-Za-z_][A-Za-z0-9_]*'


def groups(text):
    """(top-level parenthesized groups of `text`, the rest after them)."""
    out, text = [], text.lstrip()
    while text.startswith('('):
        depth = 0
        for k, ch in enumerate(text):
            depth += (ch == '(') - (ch == ')')
            if depth == 0: break
        else: raise Unsupported('unbalanced parentheses in the generated Lean')
        out.append(text[1:k].strip()); text = text[k + 1:].lstrip()
    return out, text


def unparen(text):
    text = text.strip()
    while text.startswith('('):
        inner, rest = groups(text)
        if rest or len(inner) != 1: break
        text = inner[0]
    return text


def lean_name(name):
    return name[1:-1] if name.startswith('«') and name.endswith('»') else name


def declarations(gen_text):
    """{type name: ('structure', [(field, type text)]) | ('inductive', [(constructor, [argument type text])])}."""
    out = {}
    for kind, name, body in DECL.findall(gen_text):
        items = []
        for line in body.splitlines():
            line = line.strip()
            if line.startswith('deriving'): break
            if kind == 'structure':
                field, sep, text = line.partition(' : ')
                if sep: items.append((field.strip(), text))
            elif line.startswith('|'):
                ctor, _, rest = line[1:].strip().partition(' ')
                items.append((ctor, [arg.partition(' : ')[2] for arg in groups(rest)[0]]))
        out[name] = (kind, items)
    return out


class Types:
    """Resolves a Lean type text against an AIR type id. Without an AIR type table only `BitVec n`
    (assumed unsigned) and `Bool` resolve."""
    def __init__(self, gen_text, namespace, air_types=None):
        self.gen_text, self.decls, self.namespace, self.air = gen_text, declarations(gen_text), namespace, air_types
        self.open = []                                    # the named types being resolved, outermost first

    def air_type(self, tid, kind, text):
        t = self.air[tid] if self.air is not None and type(tid) is int and 0 <= tid < len(self.air) else None
        if not isinstance(t, dict): raise Unsupported(f'{text}: no AIR type (the AIR type table of the function is needed)')
        if t.get('k') != kind: raise Unsupported(f'{text}: the AIR type is {t.get("k")}, not {kind}')
        return t

    def resolve(self, text, tid):
        text = unparen(text)
        m = re.fullmatch(r'BitVec\s+(\d+)', text)
        if m:
            if self.air is None: return Int(int(m.group(1)), False)
            t = self.air_type(tid, 'int', text)
            if t.get('bits') != int(m.group(1)) or type(t.get('signed')) is not bool: raise Unsupported(f'{text}: the AIR integer differs')
            return Int(t['bits'], t['signed'])
        if text == 'Bool':
            if self.air is not None: self.air_type(tid, 'bool', text)
            return Bool()
        if text == 'Unit':
            self.air_type(tid, 'void', text)
            return Unit()
        head, _, rest = text.partition(' ')
        if head == 'Option':
            child = self.resolve(rest, self.air_type(tid, 'optional', text).get('child'))
            if child.renders('null'): raise Unsupported(f'{text}: `null` would be ambiguous in the rendered value')
            return Opt(child)
        if head == 'Except' and rest.startswith('Zig.ErrName '):
            t = self.air_type(tid, 'error_union', text)
            errors = self.air_type(t.get('error'), 'error_set', text).get('errors')
            if not isinstance(errors, list) or not all(isinstance(e, str) for e in errors):
                raise Unsupported(f'{text}: the error set is not a list of names')
            payload = self.resolve(rest[len('Zig.ErrName '):], t.get('payload'))
            if payload.renders('err'): raise Unsupported(f'{text}: `{{"err":…}}` would be ambiguous in the rendered value')
            return ErrUnion(tuple(errors), payload)
        if head == 'Array':
            t = self.air_type(tid, 'ptr', text)
            if t.get('size') != 'slice' or t.get('const') is not True or t.get('sentinel') is not False:
                raise Unsupported(f'{text}: not a read-only slice without sentinel')
            return Slice(self.resolve(rest, t.get('child')))
        if text in self.decls:
            # A type that contains itself (through a slice) has no finite description here.
            if text in self.open: raise Unsupported(f'{text}: a recursive type is not covered')
            self.open.append(text)
            try: return self.named(text, tid)
            finally: self.open.pop()
        raise Unsupported(f'unsupported type {text} (supported: {SUPPORTED}; a pointer or a mutable slice is a place in '
                          'memory, floats and vectors are not covered)')

    def named(self, name, tid):
        form, items = self.decls[name]
        lean = f'{self.namespace}.{name}'
        if self.air is None: raise Unsupported(f'{name}: no AIR type (the AIR type table of the function is needed)')
        t = self.air[tid] if type(tid) is int and 0 <= tid < len(self.air) and isinstance(self.air[tid], dict) else {}
        fields = t.get('fields') if isinstance(t.get('fields'), list) else []
        if not all(isinstance(f, dict) and isinstance(f.get('name'), str) for f in fields): fields = None
        mismatch = Unsupported(f'{name}: the Lean {form} does not line up with the AIR {t.get("k")} (an extern or packed union, '
                               'a tuple or an untagged union has no value form here)')
        if fields is None: raise mismatch
        if t.get('k') == 'struct':
            if form != 'structure' or [lean_name(f) for f, _ in items] != [f['name'] for f in fields]: raise mismatch
            return Struct(lean, tuple((f['name'], field, self.resolve(text, f.get('ty'))) for f, (field, text) in zip(fields, items)))
        if t.get('k') == 'enum':
            tag = self.resolve_tag(t.get('tag'), name)
            try: named = tuple((f['name'], tag.parse(int(f['value']))) for f in fields)
            except (KeyError, TypeError, ValueError, Mismatch): raise mismatch from None
            for helper in ('ofInt?', 'toBits'):
                if not re.search(rf'^def {re.escape(name)}\.{re.escape(helper)}\s', self.gen_text, re.M): raise mismatch
            if t.get('exhaustive') is True:
                if form != 'inductive' or [(lean_name(c), a) for c, a in items] != [(f['name'], []) for f in fields]: raise mismatch
            elif t.get('exhaustive') is not False or form != 'structure' or items != [('bits', f'BitVec {tag.bits}')]: raise mismatch
            return Enum(lean, tag, named, t['exhaustive'])
        if t.get('k') == 'union':
            if form != 'inductive' or t.get('layout') != 'auto' or type(t.get('tag')) is not int: raise mismatch
            self.air_type(t['tag'], 'enum', name)
            ctors = [(c, a) for c, a in items if not c.startswith('undef_')]
            if [lean_name(c) for c, _ in ctors] != [f['name'] for f in fields]: raise mismatch
            out = []
            for f, (ctor, args) in zip(fields, ctors):
                if len(args) > 1: raise mismatch
                payload = self.resolve(args[0], f.get('ty')) if args else self.resolve('Unit', f.get('ty'))
                if isinstance(payload, Unit) and args: raise mismatch
                out.append((f['name'], payload))
            return Union(lean, tuple(out), tuple(c for c, _ in ctors), tuple(c for c, _ in items if c.startswith('undef_')))
        raise mismatch

    def resolve_tag(self, tid, name):
        t = self.air_type(tid, 'int', name)
        if type(t.get('bits')) is not int or type(t.get('signed')) is not bool: raise Unsupported(f'{name}: malformed tag type')
        return Int(t['bits'], t['signed'])


@dataclass(frozen=True)
class Signature:
    function: str           # the Lean name as declared (may be «quoted»)
    params: tuple           # ((name, kind), ...)
    ret: Kind
    memory: bool            # a `Zig.MemM` function: run from `mem0 .fresh`
    typed: bool             # resolved against the AIR type table (else integers are assumed unsigned)

    @property
    def types(self): return [t for _, t in self.params]

    @property
    def wide(self):
        """The harness's `quote_wide`: integers are rendered as strings when the result has one of 64 bits or more."""
        return any(i.bits >= 64 for i in self.ret.ints())

    def parse_args(self, raw):
        """The values of a JSON argument row, or Mismatch."""
        if not isinstance(raw, list) or len(raw) != len(self.params): raise Mismatch('the row does not have one value per parameter')
        return [t.parse(v) for (_, t), v in zip(self.params, raw)]


def namespace_of(gen_text):
    m = re.search(r'^namespace\s+(\S+)', gen_text, re.M)
    if not m: raise Unsupported('no namespace in Gen.lean')
    return m.group(1)


def signature(gen_text, function, air=None):
    """The Signature of `def function (p : T) … : Zig.Result T := do` (or `Zig.MemM`), else Unsupported.

    `air` is the function's exported AIR document (its `params`, `ret` and `types`)."""
    m = re.search(rf'^def\s+(«?{re.escape(function)}»?)[ \t]+(.*?):=\s*do\s*$', gen_text, re.M)
    if not m: raise Unsupported(f'{function} is not a generated function (missing, or not a `do` definition)')
    binders, rest = groups(m.group(2))
    if not rest.startswith(':'): raise Unsupported(f'{function} takes an environment or instance argument ({rest.split(":")[0].strip()})')
    monad, _, ret_text = rest[1:].strip().partition(' ')
    if monad not in ('Zig.Result', 'Zig.MemM'):
        raise Unsupported(f'{function} is a {monad} function; the goal search covers sequential Zig.Result and Zig.MemM functions')
    memory = monad == 'Zig.MemM'
    if memory and not re.search(r'^def mem0 ', gen_text, re.M): raise Unsupported(f'{function} uses memory and Gen.lean has no mem0')
    typed = isinstance(air, dict) and isinstance(air.get('types'), list) and isinstance(air.get('params'), list)
    if typed and len(air['params']) != len(binders): raise Unsupported(f'{function}: the AIR parameters do not line up with the generated ones')
    types = Types(gen_text, namespace_of(gen_text), air['types'] if typed else None)
    params = []
    for k, binder in enumerate(binders):
        name, sep, text = binder.partition(' : ')
        if not sep or not re.fullmatch(IDENT, name.strip()): raise Unsupported(f'{function}: unreadable parameter ({binder})')
        params.append((name.strip(), types.resolve(text, air['params'][k] if typed else None)))
    out = Signature(m.group(1), tuple(params), types.resolve(ret_text, air.get('ret') if typed else None), memory, typed)
    out.ret.renderer(Emit(), out.wide)                    # a result that cannot be rendered is unsupported here, not later
    return out


# --- Candidate inputs ---------------------------------------------------------------------


def row_key(types, row):
    """Rows are ordered smallest first: by the size of the values (each kind's `weight`), then by the row encoding."""
    return sum(t.weight(v) for t, v in zip(types, row)), [a for t, v in zip(types, row) for a in t.flat(v)]


def shrinks(types, row):
    """The rows one shrink step below `row` (one argument replaced by one of its kind's `shrinks`), smallest first."""
    key, out = row_key(types, row), {}
    for k, t in enumerate(types):
        for s in t.shrinks(row[k]):
            smaller = tuple(row[:k]) + (s,) + tuple(row[k + 1:])
            if row_key(types, smaller) < key: out.setdefault(tuple(row_key(types, smaller)[1]), smaller)
    return sorted(out.values(), key=lambda r: row_key(types, r))


def inputs(types, max_inputs, seed, randoms=256):
    """(rows of values, exhaustive?). Rows are ordered smallest first (`row_key`)."""
    total = 1
    for t in types: total = None if total is None or t.size() is None else total * t.size()
    order = lambda rows: sorted(rows, key=lambda row: row_key(types, row))
    if any(t.size() == 0 for t in types): return [], True  # a parameter type without values: there is no input at all
    if total is not None and total <= max_inputs:
        return order(itertools.product(*[list(t.values()) for t in types])), True
    rng = random.Random(seed)
    rows = {}
    def add(row): rows.setdefault(tuple(row_key(types, row)[1]), tuple(row))
    cross = [t.boundary(rng) for t in types]
    size = 1
    for c in cross: size *= len(c)
    if size <= max_inputs:
        for row in itertools.product(*cross): add(row)
    else:
        for _ in range(4 * max_inputs):                   # bounded: the boundary lists may repeat values
            if len(rows) >= max_inputs // 2: break
            add(tuple(rng.choice(c) for c in cross))
    for _ in range(min(randoms, max_inputs - len(rows))):
        add(tuple(t.random(rng) for t in types))
    return order(rows.values())[:max_inputs], False


# --- Driver -------------------------------------------------------------------------------

PRELUDE = '''
def A2LEval.many {α : Type} (dec : List Nat → Option (α × List Nat)) : Nat → List Nat → Option (Array α × List Nat)
  | 0, l => some (#[], l)
  | n + 1, l => do
    let (v, l) ← dec l
    let (vs, l) ← A2LEval.many dec n l
    pure (#[v] ++ vs, l)
'''


def driver(namespace, sig, rows, *, spec=None, pre=None, print_all=False, max_violations=1, given=None):
    """The Lean text that evaluates `sig` on `rows`.

    `given`: per row a recorded outcome, `('ok', value)` or `('error', Zig.Error constructor)`. Then
    the function is not called: `r` is that outcome, so the postcondition is decided on what another
    run (the native program) returned."""
    emit = Emit()
    decoders = [t.decoder(emit) for t in sig.types]
    render = sig.ret.renderer(emit, sig.wide)
    result = f'Except Zig.Error ({sig.ret.lean})'
    flat = lambda row: [a for t, v in zip(sig.types, row) for a in t.flat(v)]
    def outcome(o):
        if o[0] == 'ok': return [0] + sig.ret.flat(o[1])
        return [1 + ERRORS.index(o[1])]
    data = ';'.join(','.join(map(str, [i, *flat(row), *(outcome(given[i]) if given is not None else [])])) for i, row in enumerate(rows))
    lets = ''.join(f'      let some ({n}, l) := {dec} l | throw (IO.userError "malformed row")\n' for (n, _), dec in zip(sig.params, decoders))
    call = ' '.join([f'{namespace}.{sig.function}', *(n for n, _ in sig.params)])
    if given is not None:
        lets += '      let some (given, _) := A2LEval.outcome l | throw (IO.userError "malformed row")\n'
        run = 'some given'
    elif sig.memory:
        run = f'((({call}).run ({namespace}.mem0 .fresh)).run).map (·.map (·.1))'
    else:
        run = f'({call}).run'
    recorded = '' if given is None else f'''
def A2LEval.outcome : List Nat → Option (({result}) × List Nat)
  | 0 :: l => ({sig.ret.decoder(emit)} l).map fun (v, l) => (.ok v, l)
  | k :: l => (([{', '.join(f'Zig.Error.{e}' for e in ERRORS)}] : List Zig.Error)[k - 1]?).map fun e => (.error e, l)
  | [] => none
'''
    return PRELUDE + '\n\n'.join(emit.text) + f'''

def A2LEval.obs (r : {result}) : String :=
  match r with
  | .ok v => "{{\\"ok\\":" ++ {render} v ++ "}}"
  | .error e => "{{\\"fail\\":\\"" ++ reprStr e ++ "\\"}}"
{recorded}
def A2LEval.rows : List (List Nat) :=
  ("{data}".splitOn ";").filterMap fun row =>
    if row.isEmpty then none else some (row.splitOn "," |>.map String.toNat!)

open {namespace} in
def A2LEval.main : IO UInt32 := do
  let mut checked := 0
  let mut skipped := 0
  let mut none_ := 0
  let mut bad := 0
  for row in A2LEval.rows do
    match row with
    | i :: l =>
{lets}      if !({f'decide ({pre})' if pre else 'true'}) then
        skipped := skipped + 1
      else
        checked := checked + 1
        match (({run}) : Option ({result})) with
        | none =>
          none_ := none_ + 1
          IO.println s!"N\\t{{i}}"
        | some r =>
          if {str(print_all).lower()} then IO.println s!"O\\t{{i}}\\t{{A2LEval.obs r}}"
          if !({f'decide ({spec})' if spec else 'true'}) then
            bad := bad + 1
            IO.println s!"V\\t{{i}}\\t{{A2LEval.obs r}}"
    | [] => throw (IO.userError "malformed row")
    if bad >= {max_violations} then break
  IO.println s!"S\\t{{checked}}\\t{{skipped}}\\t{{none_}}\\t{{bad}}"
  return 0

def main : IO UInt32 := A2LEval.main
'''


def run(root, gen_path, text, *, timeout, runner=('lake', 'env', 'lean', '--run')):
    """Run Gen.lean + driver. Returns dict(status=ok|timeout|error, lines, detail)."""
    with tempfile.TemporaryDirectory(prefix='air2lean-eval-') as temp:
        path = Path(temp)/'Eval.lean'
        path.write_text(Path(gen_path).read_text() + text)
        # Own session: `lake` forks `lean`, and a timeout must end the whole group, not orphan the evaluator.
        try:
            proc = subprocess.Popen([*runner, str(path)], cwd=root, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                                    start_new_session=True)
        except OSError as error:
            return dict(status='error', lines=[], detail=str(error))
        try:
            stdout, stderr = proc.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            try: os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError: pass
            proc.communicate()
            return dict(status='timeout', lines=[], detail='lean evaluation timed out')
    if proc.returncode != 0:
        return dict(status='error', lines=[], detail=(stdout + stderr)[-2000:])
    return dict(status='ok', lines=[l.split('\t') for l in stdout.splitlines() if l[:2] in ('O\t', 'V\t', 'N\t', 'S\t')], detail='')


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def obs_kind(line):
    """Diff-report Kind of a legacy observation line."""
    d = json.loads(line)
    if 'ok' in d: return 'value'
    if d.get('diverge'): return 'bounded_no_result'
    e = d.get('fail', '').removeprefix('Zig.Error.')
    return e if e in ('illegal', 'unspecified', 'deadlock') else 'model_panic'
