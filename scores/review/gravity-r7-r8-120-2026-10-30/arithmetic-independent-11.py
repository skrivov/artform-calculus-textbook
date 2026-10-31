"""Distinct exact/adverse review of owned cuts and source-bearing composition.

This tests finite arithmetic interfaces; it does not extract native Hessian rows.
The Lean kernels, rather than these examples, establish universal analytic claims.
"""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import random

BASE = Path(__file__).resolve().parent
RNG = random.Random(728231)


def rational():
    return F(RNG.randrange(-29, 30), RNG.randrange(1, 18))


def solve(a, b):
    rows = [list(row) + [value] for row, value in zip(a, b)]
    n = len(rows)
    for col in range(n):
        pivot = next(r for r in range(col, n) if rows[r][col])
        rows[col], rows[pivot] = rows[pivot], rows[col]
        divisor = rows[col][col]
        rows[col] = [v / divisor for v in rows[col]]
        for r in range(n):
            if r != col:
                multiplier = rows[r][col]
                rows[r] = [x - multiplier * y for x, y in zip(rows[r], rows[col])]
    return [row[-1] for row in rows]


def middle(c, a, b, j):
    return (a + b) / 2 + j / (4 * c)


def effective(c, a, b, j):
    return c * (b - a) ** 2 / 2 - j * (a + b) / 2 - j * j / (8 * c)


def composed(c, a, b, j, ell):
    return (c * (b - a) ** 2 / 4
            - (j * (3 * a + b) + ell * (a + 3 * b)) / 4
            - (j * j + ell * ell) / (8 * c) - (j + ell) ** 2 / (16 * c))


def step(c, j, a, pin):
    return a + (pin - j / 2) / c, pin - j


checks = 0
for n in range(13):
    c, e = rational(), rational()
    u = [rational() for _ in range(n + 2)]
    v = [rational() for _ in range(n + 2)]
    action = lambda w: sum(c * (w[i + 1] - w[i]) ** 2 for i in range(n + 1))
    p = [2 * c * (u[i + 1] - u[i]) for i in range(n + 1)]
    flux = sum(p[i] * (v[i + 1] - v[i]) for i in range(n + 1))
    boundary = p[n] * v[n + 1] - p[0] * v[0]
    interior = sum((p[i + 1] - p[i]) * v[i + 1] for i in range(n))
    assert flux == boundary - interior
    assert action([a + e * b for a, b in zip(u, v)]) == action(u) + e * flux + e * e * action(v)
    checks += 2
assert 1 * (5 - 2) + 3 * (11 - 5) == 3 * 11 - 1 * 2 - (3 - 1) * 5
assert 1 * (5 - 2) + 3 * (11 - 5) != 8 * 11 - 1 * 2 - (3 - 1) * 5

# Directly eliminate THREE original details in FOUR original unit edges.
# This avoids assuming the previously reduced two-cell formula in the solve.
for c in [F(1, 101), F(2, 7), F(-3, 5)]:
    for _ in range(19):
        a, b, j, ell, da, db, dj, eps = [rational() for _ in range(8)]
        hessian = [[2 * c * (2 if r == s else -1 if abs(r - s) == 1 else 0)
                    for s in range(3)] for r in range(3)]
        rhs = [2 * c * a + j, F(0), 2 * c * b + ell]
        x1, seam, x3 = solve(hessian, rhs)
        values = [a, x1, seam, x3, b]
        raw = sum(c * (values[i + 1] - values[i]) ** 2 for i in range(4)) - j * x1 - ell * x3
        assert raw == composed(c, a, b, j, ell)
        assert seam == (a + b) / 2 + (j + ell) / (4 * c)
        pin, pout = 2 * c * (x1 - a), 2 * c * (b - x3)
        s1 = step(c, j, a, pin)
        assert s1[0] == seam
        assert step(c, ell, *s1) == (b, pout)
        assert pin - pout == j + ell
        # Same-source full simultaneous endpoint/source variation and mixed contact.
        m = middle(c, a, b, j)
        pi, po = c * (b - a) + j / 2, c * (b - a) - j / 2
        remainder = c * (db - da) ** 2 / 2 - dj * (da + db) / 2 - dj * dj / (8 * c)
        assert effective(c, a + eps * da, b + eps * db, j + eps * dj) == (
            effective(c, a, b, j) + eps * (-pi * da + po * db - m * dj) + eps * eps * remainder)
        assert effective(c, a + da, b + db, j + dj) - effective(c, a + da, b + db, j) - effective(c, a, b, j + dj) + effective(c, a, b, j) == -dj * (da + db) / 2
        checks += 8
c = F(1, 101)
assert composed(c, F(0), F(4), 2 * c, 4 * c) != composed(c, F(0), F(4), 6 * c, F(0))
assert (middle(c, -1, 3, 4 * c), effective(c, -1, 3, 4 * c)) == (2, 2 * c)
assert middle(c, -1, 3, 5 * c) - middle(c, -1, 3, 4 * c) == F(1, 4)

# All forty coordinates, signed indefinite Gram and asymmetric temporal pairings.
dim = 40
eta = [-1, 1, 1, 1]
gram = [eta[i] for i in range(4) for _ in range(4)] + [-1, -1, -1, 1, 1, 1] * 4
assert len(gram) == dim and gram.count(-1) == 16
matrices = {r: [[F(((i + 2) * (s + 3) + r * (i - s)) % 17 - 8, r + 2)
                 for s in range(dim)] for i in range(dim)] for r in range(1, 4)}
pair = lambda a, matrix, b: sum(a[i] * matrix[i][s] * b[s] for i in range(dim) for s in range(dim))
xs = lambda n: [F(n * n + (i % 7) * n + i % 3, i % 4 + 1) for i in range(dim)]
ys = lambda n: [F(n ** 3 - (i % 5) * n + i % 11, i % 3 + 1) for i in range(dim)]
edge = lambda n, r: pair(xs(n), matrices[r], ys(n + r)) - pair(ys(n), matrices[r], xs(n + r))
cut = lambda n: sum(edge(n - j, r) for r in range(1, 4) for j in range(r))
wrong_incoming_detected = False
for n in range(-4, 5):
    forward = sum(pair(xs(n), matrices[r], ys(n + r)) - pair(ys(n), matrices[r], xs(n + r)) for r in range(1, 4))
    incoming = sum(pair(ys(n - r), matrices[r], xs(n)) - pair(xs(n - r), matrices[r], ys(n)) for r in range(1, 4))
    assert cut(n) - cut(n - 1) == forward + incoming
    wrong = sum(pair(xs(n), matrices[r], ys(n - r)) - pair(ys(n), matrices[r], xs(n - r)) for r in range(1, 4))
    wrong_incoming_detected |= forward + wrong != forward + incoming
    checks += 1
assert wrong_incoming_detected and cut(0) != cut(-1)
x, y, h = xs(2), ys(-1), F(3, 8)
frame = lambda z: z[:16] + [F(0)] * 24
conn = lambda z: [F(0)] * 16 + z[16:]
physical = lambda z: z[:16] + [-h * q for q in z[16:]]
b = matrices[1]
ff, fc, cf, cc = [pair(a, b, z) for a, z in [(frame(x), frame(y)), (frame(x), conn(y)), (conn(x), frame(y)), (conn(x), conn(y))]]
assert fc != 0 and cf != 0 and fc != cf
assert pair(physical(x), b, physical(y)) == ff - h * fc - h * cf + h * h * cc
assert sum(x[i] * gram[i] * y[i] for i in range(dim)) != sum(x[i] * y[i] for i in range(dim))
assert h * (h ** 3 * pair(x, b, y)) == h ** 4 * pair(x, b, y)

# Symbolic linear circuit semantics on all rational inputs: independent interpreter.
old = [('add', ('in', 0), ('in', 1)), ('scale', F(1, 2), ('slot', 0)), ('scale', F(101, 4), ('in', 2)), ('add', ('slot', 1), ('slot', 2)), ('add', ('slot', 3), ('neg', ('in', 0))), ('scale', F(2, 101), ('slot', 4)), ('add', ('in', 1), ('neg', ('slot', 3))), ('scale', F(2, 101), ('slot', 6))]
new = [('add', ('in', 1), ('neg', ('in', 0))), ('scale', F(1, 101), ('slot', 0)), ('scale', F(1, 2), ('in', 2)), ('add', ('slot', 1), ('slot', 2)), ('add', ('slot', 1), ('neg', ('slot', 2))), ('scale', F(101, 2), ('slot', 3)), ('add', ('in', 0), ('slot', 5))]


def symbolic(program, outputs):
    registers = []

    def read(ref):
        op, value = ref
        if op == 'neg':
            return [-v for v in read(value)]
        if op == 'in':
            assert 0 <= value < 3
            return [F(i == value) for i in range(3)]
        assert 0 <= value < len(registers)
        return registers[value]

    for op, a, b in program:
        registers.append([a * v for v in read(b)] if op == 'scale' else [u + v for u, v in zip(read(a), read(b))])
    assert all(0 <= i < len(registers) for i in outputs)
    return [registers[i] for i in outputs]


expected = [[F(1, 2), F(1, 2), F(101, 4)], [-c, c, F(1, 2)], [-c, c, F(-1, 2)]]
assert symbolic(old, [3, 5, 7]) == symbolic(new, [6, 3, 4]) == expected
assert [(sum(g[0] == 'scale' for g in p), sum(g[0] == 'add' for g in p)) for p in (old, new)] == [(4, 4), (3, 4)]

# Halo counterexample: identical present/next data does not determine the range2 cut.
hx, hy = lambda n: F(n == 0), lambda n: F(n == 2)
assert hy(0) == hy(1) == 0
assert sum(hx(-j) * hy(2 - j) - hy(-j) * hx(2 - j) for j in range(2)) == 1

sources = ['arithmetic-independent-11.py', 'source-pins.json', 'retrospective-baseline-04.json', 'boundary-program-root-11.py', 'source/native-original-cut-form.md', 'source/accepted-component-boundary-benchmark.md', 'source/accepted-two-cell-source-benchmark.md']
result = {'status': 'passed', 'independent_finite_arithmetic_checks': checks,
          'owned_lengths': 13, 'direct_original_four_edge_schur_solves': 57,
          'nonzero_positive_and_negative_c': True, 'native_heldout_source_retained': True,
          'full40_asymmetric_three_range_cuts': 9, 'wrong_incoming_transpose_detected': True,
          'both_mixed_contacts_nonzero_and_unequal': True, 'signed_gram_negative_directions': 16,
          'symbolic_program_equality_for_all_rational_inputs': True,
          'program_costs': [[4, 4], [3, 4]], 'invalid_slot_read_ruled_out': True,
          'halo_adverse': True, 'new_physical_gate': 0, 'historical_runtime_credit': 0,
          'source_sha256': {str(Path('scores/review') / BASE.name / f): hashlib.sha256((BASE / f).read_bytes()).hexdigest() for f in sources}}
print(json.dumps(result, sort_keys=True))
