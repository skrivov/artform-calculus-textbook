#!/usr/bin/env python3
"""Untrusted exact native history congruence generator with checked certificates.
The generic Lean certificate checker, rather than this host program, is the
formal acceptance gate. No closed rank pattern or physical mode count is used.
"""
import argparse
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path

PACKET = Path(__file__).resolve().parent


def transpose(a):
    return list(map(list, zip(*a)))


def multiply(a, b):
    if not a:
        return []
    columns = transpose(b)
    return [[sum((x * y for x, y in zip(row, col) if x and y), F(0))
             for col in columns] for row in a]


def identity(n):
    return [[F(i == j) for j in range(n)] for i in range(n)]


def congruence(matrix):
    """Return T,V,d with VT=TV=I and T^t matrix T=diag(d)."""
    n = len(matrix)
    m = [row[:] for row in matrix]
    t, v = identity(n), identity(n)
    trace = []
    for k in range(n):
        pivot = next((i for i in range(k, n) if m[i][i]), None)
        if pivot is None:
            off = next(((i, j) for i in range(k, n) for j in range(i + 1, n)
                        if m[i][j]), None)
            if off is None:
                break
            i, j = off
            # E=I+e_j e_i^t; its inverse is I-e_j e_i^t.
            for row in m:
                row[i] += row[j]
            m[i] = [x + y for x, y in zip(m[i], m[j])]
            for row in t:
                row[i] += row[j]
            v[j] = [x - y for x, y in zip(v[j], v[i])]
            trace.append({'kind': 'create_diagonal', 'i': i, 'j': j})
            pivot = i
        if pivot != k:
            m[k], m[pivot] = m[pivot], m[k]
            for row in m:
                row[k], row[pivot] = row[pivot], row[k]
            for row in t:
                row[k], row[pivot] = row[pivot], row[k]
            v[k], v[pivot] = v[pivot], v[k]
            trace.append({'kind': 'swap', 'i': k, 'j': pivot})
        d = m[k][k]
        coefficients = [F(0)] * n
        for j in range(k + 1, n):
            coefficients[j] = m[k][j] / d
        for i in range(k + 1, n):
            for j in range(i, n):
                value = m[i][j] - coefficients[i] * d * coefficients[j]
                m[i][j] = m[j][i] = value
        for j in range(k + 1, n):
            if coefficients[j]:
                for i in range(n):
                    t[i][j] -= coefficients[j] * t[i][k]
            m[k][j] = m[j][k] = F(0)
        v[k] = [v[k][i] + sum((coefficients[j] * v[j][i]
                for j in range(k + 1, n) if coefficients[j]), F(0)) for i in range(n)]
        trace.append({'kind': 'pivot', 'i': k, 'value': str(d),
                      'coefficients': {str(j): str(x) for j, x in enumerate(coefficients) if x}})
    diagonal = [m[i][i] for i in range(n)]
    target = [[diagonal[i] if i == j else F(0) for j in range(n)] for i in range(n)]
    assert m == target
    assert multiply(t, v) == multiply(v, t) == identity(n)
    assert multiply(multiply(transpose(t), matrix), t) == target
    return t, v, diagonal, trace


def native_matrix(interiors):
    data = json.loads((PACKET / 'legendre-root-data.json').read_text())
    h0, h1, b = [[[F(x) for x in row] for row in data[key]] for key in ('H0', 'H1', 'B')]
    n = interiors * 40
    h = [[F(0)] * n for _ in range(n)]
    for t in range(interiors):
        for i in range(40):
            for j in range(40):
                h[40 * t + i][40 * t + j] = h0[i][j] + h1[i][j]
                if t + 1 < interiors:
                    h[40 * t + i][40 * (t + 1) + j] = b[i][j]
                    h[40 * (t + 1) + j][40 * t + i] = b[i][j]
    return h


def sparse(a):
    return [[i, j, str(x)] for i, row in enumerate(a) for j, x in enumerate(row) if x]


def compile_native(cells):
    h = native_matrix(cells - 1)
    t, v, d, trace = congruence(h)
    return {'cells': cells, 'interior_sites': cells - 1, 'all_coordinate_dimension': len(h),
            'forward': sparse(t), 'backward': sparse(v), 'diagonal': [str(x) for x in d],
            'observed_rank': sum(bool(x) for x in d), 'radical_dimension': sum(not x for x in d),
            'exact_congruence_and_two_inverses_checked': True, 'trace': trace,
            'scope': 'All40 native coordinates retained, including four inactive coordinates per site. Zero pivots remain source guards; no universal rank formula assumed.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cells', type=int, required=True)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.cells < 1:
        parser.error('at least one cell is required')
    result = compile_native(args.cells)
    # An offdiagonal pivot is essential for indefinite forms, not just native samples.
    _, _, d, trace = congruence([[F(0), F(1)], [F(1), F(0)]])
    assert d == [F(2), F(-1, 2)] and trace[0]['kind'] == 'create_diagonal'
    result['source_sha256'] = hashlib.sha256((PACKET / 'legendre-root-data.json').read_bytes()).hexdigest()
    encoded = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(encoded)
    print(json.dumps({k: v for k, v in result.items() if k not in ('forward', 'backward', 'diagonal', 'trace')}, indent=2))


if __name__ == '__main__':
    main()
