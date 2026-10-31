#!/usr/bin/env python3
"""Exact two-cell calculation from the separately replayed native root Hessian."""
import argparse
from fractions import Fraction
import json
from pathlib import Path

PACKET = Path(__file__).resolve().parent
F = Fraction


def rref(matrix):
    rows = [row[:] for row in matrix]
    pivots = []
    target = 0
    for column in range(len(rows[0])):
        pivot = next((k for k in range(target, len(rows)) if rows[k][column]), None)
        if pivot is None:
            continue
        rows[target], rows[pivot] = rows[pivot], rows[target]
        divisor = rows[target][column]
        rows[target] = [value / divisor for value in rows[target]]
        for k in range(len(rows)):
            if k != target and rows[k][column]:
                multiplier = rows[k][column]
                rows[k] = [x - multiplier * y for x, y in zip(rows[k], rows[target])]
        pivots.append(column)
        target += 1
        if target == len(rows):
            break
    return rows, pivots


def multiply(left, right):
    return [[sum((x * y for x, y in zip(row, column)), F(0))
             for column in zip(*right)] for row in left]


def transpose(matrix):
    return list(map(list, zip(*matrix)))


def subtract(left, right):
    return [[x - y for x, y in zip(a, b)] for a, b in zip(left, right)]


def encode(matrix):
    return [[str(value) for value in row] for row in matrix]


root = json.loads((PACKET / 'legendre-root-data.json').read_text())
h0, h1, mixed = [[[F(x) for x in row] for row in root[key]] for key in ['H0', 'H1', 'B']]
active = [i for i in range(40) if i not in [0, 4, 8, 12]]
middle = [[h0[i][j] + h1[i][j] for j in active] for i in active]
augmented = [row + [F(i == j) for j in range(36)] for i, row in enumerate(middle)]
reduced, pivots = rref(augmented)
assert pivots == list(range(36))
inverse = [[F(0)] * 40 for _ in range(40)]
for i, old_i in enumerate(active):
    for j, old_j in enumerate(active):
        inverse[old_i][old_j] = reduced[i][36 + j]
cross = [[-x for x in row] for row in multiply(multiply(mixed, inverse), mixed)]
_, cross_pivots = rref(cross)
effective_old = subtract(h0, multiply(multiply(mixed, inverse), transpose(mixed)))
effective_new = subtract(h1, multiply(multiply(transpose(mixed), inverse), mixed))
projector = [[F(i == j and i in active) for j in range(40)] for i in range(40)]
full_middle = [[h0[i][j] + h1[i][j] for j in range(40)] for i in range(40)]
assert multiply(full_middle, inverse) == multiply(inverse, full_middle) == projector
assert len(cross_pivots) == 18
assert all(not mixed[25][i] and not mixed[i][25] and not h1[i][25] for i in range(40))
assert h0[25][25] == F(4, 101)
result = {'active': active, 'middle_inverse': encode(inverse),
          'effective_mixed': encode(cross), 'effective_old': encode(effective_old),
          'effective_new': encode(effective_new), 'mixed_rank': 18,
          'source_compatibility_zero_indices': [0, 4, 8, 12],
          'nonextension': {'middle_coordinate': 25, 'next_pre_25': '-4/101',
                           'incoming_momentum_25': '0'}}
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check', action='store_true')
args = parser.parse_args()
target = PACKET / 'composition-root-data.json'
encoded = json.dumps(result, indent=2) + '\n'
if args.check:
    assert target.read_text() == encoded, 'two-cell certificate drift'
else:
    target.write_text(encoded)
print('PASS exact active36 middle solve, mixed rank18, retained source compatibility and nonextension')
