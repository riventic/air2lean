"""Exact reference semantics of the IEEE 754 binary formats f16, f32 and f64 for zig_gen.py.

A float is its bit pattern (an int). Every rounding operation computes the exact rational
result and rounds it once to the format (nearest, ties to even), as docs/floats.md states for
the model. A NaN result is always the one canonical quiet NaN `qnan(fmt)`: Zig leaves a NaN's
sign and payload open, so the generator never lets them be observed.
"""
from fractions import Fraction
from math import isqrt

FORMATS = {"f16": (5, 10), "f32": (8, 23), "f64": (11, 52)}  # exponent bits, fraction bits


def width(fmt):
    e, f = FORMATS[fmt]
    return 1 + e + f


def _parts(fmt):
    e, f = FORMATS[fmt]
    return e, f, (1 << (e - 1)) - 1  # exponent bits, fraction bits, bias


def qnan(fmt):
    e, f, _ = _parts(fmt)
    return (((1 << e) - 1) << f) | (1 << (f - 1))


def inf(fmt, sign=0):
    e, f, _ = _parts(fmt)
    return (sign << (e + f)) | (((1 << e) - 1) << f)


def zero(fmt, sign=0):
    e, f, _ = _parts(fmt)
    return sign << (e + f)


def decode(fmt, bits):
    """('nan',), ('inf', sign) or ('num', sign, magnitude: Fraction)."""
    e, f, bias = _parts(fmt)
    sign = bits >> (e + f) & 1
    exp = bits >> f & ((1 << e) - 1)
    frac = bits & ((1 << f) - 1)
    if exp == (1 << e) - 1:
        return ("nan",) if frac else ("inf", sign)
    if exp == 0:
        return ("num", sign, Fraction(frac) * Fraction(2) ** (1 - bias - f))
    return ("num", sign, Fraction((1 << f) | frac) * Fraction(2) ** (exp - bias - f))


def is_nan(fmt, bits):
    return decode(fmt, bits)[0] == "nan"


def _floor_log2(q):
    n = q.numerator.bit_length() - q.denominator.bit_length()
    return n if Fraction(2) ** n <= q else n - 1


def _round_half_even(q):
    whole = q.numerator // q.denominator
    rest = q - whole
    if rest > Fraction(1, 2) or (rest == Fraction(1, 2) and whole & 1):
        whole += 1
    return whole


def encode(fmt, sign, magnitude):
    """Round the non-negative rational `magnitude` once to the format."""
    e, f, bias = _parts(fmt)
    if magnitude == 0:
        return zero(fmt, sign)
    exp = max(_floor_log2(magnitude), 1 - bias)
    mant = _round_half_even(magnitude / Fraction(2) ** (exp - f))
    if mant == 1 << (f + 1):
        mant, exp = 1 << f, exp + 1
    if exp > bias:
        return inf(fmt, sign)
    if mant < 1 << f:  # subnormal (exp is the minimum) or zero after rounding
        return (sign << (e + f)) | mant
    return (sign << (e + f)) | ((exp + bias) << f) | (mant - (1 << f))


def _signed(d):
    return -d[2] if d[1] else d[2]


def _from_rational(fmt, q, zero_sign=0):
    if q == 0:
        return zero(fmt, zero_sign)
    return encode(fmt, 1 if q < 0 else 0, abs(q))


def neg(fmt, a):
    return qnan(fmt) if is_nan(fmt, a) else a ^ (1 << (width(fmt) - 1))


def fabs(fmt, a):
    return qnan(fmt) if is_nan(fmt, a) else a & ((1 << (width(fmt) - 1)) - 1)


def add(fmt, a, b):
    x, y = decode(fmt, a), decode(fmt, b)
    if x[0] == "nan" or y[0] == "nan":
        return qnan(fmt)
    if x[0] == "inf" or y[0] == "inf":
        if x[0] == "inf" and y[0] == "inf":
            return a if x[1] == y[1] else qnan(fmt)
        return a if x[0] == "inf" else b
    # An exact zero sum is +0 unless both operands are -0 (round to nearest).
    return _from_rational(fmt, _signed(x) + _signed(y), x[1] & y[1] if x[2] == 0 and y[2] == 0 else 0)


def sub(fmt, a, b):
    return add(fmt, a, neg(fmt, b)) if not is_nan(fmt, b) else qnan(fmt)


def mul(fmt, a, b):
    x, y = decode(fmt, a), decode(fmt, b)
    if x[0] == "nan" or y[0] == "nan":
        return qnan(fmt)
    sign = x[1] ^ y[1]
    if x[0] == "inf" or y[0] == "inf":
        other = y if x[0] == "inf" else x
        return qnan(fmt) if other[0] == "num" and other[2] == 0 else inf(fmt, sign)
    return encode(fmt, sign, x[2] * y[2])


def div(fmt, a, b):
    x, y = decode(fmt, a), decode(fmt, b)
    if x[0] == "nan" or y[0] == "nan":
        return qnan(fmt)
    sign = x[1] ^ y[1]
    if x[0] == "inf":
        return qnan(fmt) if y[0] == "inf" else inf(fmt, sign)
    if y[0] == "inf":
        return zero(fmt, sign)
    if y[2] == 0:
        return qnan(fmt) if x[2] == 0 else inf(fmt, sign)
    return encode(fmt, sign, x[2] / y[2])


def sqrt(fmt, a):
    x = decode(fmt, a)
    if x[0] == "nan":
        return qnan(fmt)
    if x[0] == "inf":
        return qnan(fmt) if x[1] else a
    if x[2] == 0:
        return a
    if x[1]:
        return qnan(fmt)
    # Truncated root with 2**-k resolution plus a sticky half step: k is beyond every rounding
    # boundary of the format (a root is never subnormal), so the rounding decision is exact.
    _, f, bias = _parts(fmt)
    k = f + bias + 4
    scaled = x[2] * Fraction(4) ** k
    whole = scaled.numerator // scaled.denominator
    root = isqrt(whole)
    exact = root * root == whole and scaled.denominator == 1
    return encode(fmt, 0, Fraction(2 * root + (0 if exact else 1), 1 << (k + 1)))


def _integral(fmt, a, pick):
    x = decode(fmt, a)
    if x[0] == "nan":
        return qnan(fmt)
    if x[0] == "inf":
        return a
    return _from_rational(fmt, Fraction(pick(_signed(x))), x[1])


def _trunc(q):
    whole = abs(q).numerator // abs(q).denominator
    return -whole if q < 0 else whole


def _round_away(q):
    whole = (abs(q) + Fraction(1, 2)).numerator // (abs(q) + Fraction(1, 2)).denominator
    return -whole if q < 0 else whole


def floor(fmt, a):
    return _integral(fmt, a, lambda q: q.numerator // q.denominator)


def ceil(fmt, a):
    return _integral(fmt, a, lambda q: -((-q).numerator // (-q).denominator))


def trunc(fmt, a):
    return _integral(fmt, a, _trunc)


def round_(fmt, a):
    return _integral(fmt, a, _round_away)


def compare(fmt, op, a, b):
    """IEEE comparison: a NaN is unordered (only `!=` holds), and -0 == +0."""
    x, y = decode(fmt, a), decode(fmt, b)
    if x[0] == "nan" or y[0] == "nan":
        return op == "!="

    def key(d):
        if d[0] == "inf":
            return (-1 if d[1] else 1, Fraction(0))
        return (0, _signed(d))
    p, q = key(x), key(y)
    return {"<": p < q, "==": p == q, "!=": p != q, ">=": p >= q}[op]


def convert(src, dst, a):
    x = decode(src, a)
    if x[0] == "nan":
        return qnan(dst)
    if x[0] == "inf":
        return inf(dst, x[1])
    return encode(dst, x[1], x[2])


def from_int(fmt, value):
    return _from_rational(fmt, Fraction(value))


def to_int(fmt, a):
    """The truncated integer, or 'nan' / 'inf' (out of every integer range)."""
    x = decode(fmt, a)
    if x[0] != "num":
        return x[0]
    return _trunc(_signed(x))


def power_of_two(fmt, k, sign=0):
    """The bits of ±2**k, or of ±inf when 2**k is beyond the format."""
    return encode(fmt, sign, Fraction(2) ** k)
