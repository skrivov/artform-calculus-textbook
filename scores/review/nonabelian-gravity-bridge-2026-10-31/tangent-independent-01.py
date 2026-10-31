#!/usr/bin/env python3
"""Independent rational 4x4-real-matrix rank and gauge-null checks.

Uses coordinate-differential cyclic trace forms from replay-independent-01,
not the author's quaternion Jet or two-direction automatic differentiation.
These finite exact checks are not global regularity/reduction theorems.
"""
from fractions import Fraction as F
from functools import lru_cache
import importlib.util
import json
from pathlib import Path

SPEC = importlib.util.spec_from_file_location(
    "review_coordinate_forms", Path(__file__).with_name("replay-independent-01.py"))
FORMS = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(FORMS)


def matrix(q):
    a, b, c, d = map(F, q)
    return (a, -b, -c, -d, b, a, -d, c, c, d, a, -b, d, -c, b, a)


IDENTITY = matrix((1, 0, 0, 0))
TAU = tuple(matrix(tuple(int(i == j) for i in range(4))) for j in range(1, 4))
ZERO = (F(0),) * 16


def mul(a, b):
    return tuple(sum((a[4 * i + k] * b[4 * k + j] for k in range(4)
                      if a[4 * i + k] and b[4 * k + j]), F(0))
                 for i in range(4) for j in range(4))


def transpose(a):
    return tuple(a[4 * j + i] for i in range(4) for j in range(4))


def combine(a, b, sign=1):
    return tuple(x + sign * y for x, y in zip(a, b))


def pairing(a, b):
    return -sum(a[4 * i + j] * b[4 * j + i] for i in range(4) for j in range(4)) / 4


def coefficients(a):
    return [pairing(t, a) for t in TAU]


def reducer(rows):
    a = [list(row) for row in rows]
    count, columns = len(a), len(a[0])
    pivots, row = [], 0
    for column in range(columns):
        found = next((j for j in range(row, count) if a[j][column]), None)
        if found is None:
            continue
        a[row], a[found] = a[found], a[row]
        divisor = a[row][column]
        a[row] = [x / divisor for x in a[row]]
        for j in range(count):
            if j != row and a[j][column]:
                factor = a[j][column]
                a[j] = [x - factor * y for x, y in zip(a[j], a[row])]
        pivots.append(column)
        row += 1
        if row == count:
            break
    basis = []
    for column in range(columns):
        if column in pivots:
            continue
        vector = [F(int(j == column)) for j in range(columns)]
        for j, pivot in enumerate(pivots):
            vector[pivot] = -a[j][column]
        basis.append(vector)
    return len(pivots), basis


def products(a, b):
    return [[sum(x * y for x, y in zip(row, column)) for column in zip(*b)]
            for row in a]


ORIGINAL = ([(i,) for i in range(1, 8)], [(i,) for i in range(8, 15)])
FORM = FORMS.twice_form(ORIGINAL)
MOMENTS = []
for vertex in FORMS.VERTICES:
    MOMENTS.append(FORMS.word(*(ORIGINAL[1][a - 1] if a > 0
                               else FORMS.source_flux(ORIGINAL, -a - 1)
                               for a in vertex)))


def at_point(values):
    @lru_cache(None)
    def evaluate(w):
        answer = IDENTITY
        for a in w:
            answer = mul(answer, values[a - 1] if a > 0 else transpose(values[-a - 1]))
        return answer

    differentials = [[mul(q, t) for t in TAU] for q in values]
    constraint = [[F(0)] * 42 for _ in range(18)]
    assert all(evaluate(w) == IDENTITY for w in MOMENTS)
    for vertex, moment in enumerate(MOMENTS):
        for coefficient, left, index, right in FORMS.derivative(moment):
            for direction in range(3):
                derivative = mul(mul(evaluate(left), differentials[index - 1][direction]),
                                 evaluate(right))
                assert sum(derivative[i * 5] for i in range(4)) == 0
                for axis, value in enumerate(coefficients(derivative)):
                    constraint[3 * vertex + axis][3 * (index - 1) + direction] += coefficient * value
    rank, tangent = reducer(constraint)
    omega = [[F(0)] * 42 for _ in range(42)]
    for (i, a, j, b), coefficient in FORM.items():
        for first in range(3):
            left = mul(differentials[i - 1][first], evaluate(a))
            for second in range(3):
                right = mul(differentials[j - 1][second], evaluate(b))
                value = coefficient * pairing(left, right) / 2
                row, column = 3 * (i - 1) + first, 3 * (j - 1) + second
                omega[row][column] += value
                omega[column][row] -= value
    verticals = []
    for vertex in range(6):
        for tau in TAU:
            vector = []
            for index, q in enumerate(values):
                edge = index % 7
                derivative = ZERO
                if FORMS.TARGETS[edge] == vertex:
                    derivative = mul(tau, q)
                if ((index < 7 and FORMS.SOURCES[edge] == vertex)
                        or (index >= 7 and FORMS.TARGETS[edge] == vertex)):
                    derivative = combine(derivative, mul(q, tau), -1)
                vector.extend(coefficients(mul(transpose(q), derivative)))
            verticals.append(vector)
    assert not any(any(value for value in row) for row in products(constraint, list(zip(*verticals))))
    restricted = products(products(tangent, omega), list(zip(*tangent)))
    gauge_null = products(products(tangent, omega), list(zip(*verticals)))
    assert not any(any(value for value in row) for row in gauge_null)
    result = {"constraint_rank": rank, "constraint_tangent_dimension": len(tangent),
              "gauge_rank": reducer(verticals)[0], "restricted_two_form_rank": reducer(restricted)[0],
              "gauge_null_errors": 0}
    assert result == {"constraint_rank": 18, "constraint_tangent_dimension": 24,
                      "gauge_rank": 18, "restricted_two_form_rank": 6, "gauge_null_errors": 0}
    return result, evaluate


def main():
    values = [IDENTITY] * 14
    values[3] = matrix((F(3, 5), F(4, 5), 0, 0))
    values[6] = matrix((F(5, 13), 0, F(12, 13), 0))
    first, evaluate = at_point(values)
    words = FORMS.link_step(FORMS.face_step(FORMS.face_step(ORIGINAL, 0), 1))
    after = [evaluate(w) for row in words for w in row]
    second, _ = at_point(after)
    print(json.dumps({"representation": "rational 4x4 real matrices and cyclic coordinate differentials",
                      "scope": "two exact points; no global regularity theorem", "results": [first, second]},
                     indent=2))


if __name__ == "__main__":
    main()
