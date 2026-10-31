#!/usr/bin/env python3
"""Matched exact Hessian comparison; timing is observational, not a theorem.
Both paths use the same pinned literal scalar density. The baseline obtains all
coefficients by dense polarization; the score compiler expands it once into a
sparse polynomial. This times quadratic Hessian compilation, not full affine momenta or score
execution. Neither is a claim about the best available general solver.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse
import hashlib
import json
import time

PACKET = Path(__file__).resolve().parent
source = (PACKET / 'legendre-root.py').read_text()
start_marker = '# The generic polynomial replaces'
end_marker = 'B=[r[40:] for r in M[:40]]'
prefix, rest = source.split(start_marker, 1)
polynomial_code = start_marker + rest.split(end_marker, 1)[0]
context = {'__file__': str(PACKET / 'legendre-root.py')}
exec(compile(prefix, 'legendre-root.py:definitions', 'exec'), context)


def literal_cut(q):
    result = F(0)
    for r, (k, _) in enumerate(context['faces']):
        C, LU, K, T, letters = context['vals'](q, 0, r)
        contact = context['Z'][:]
        for a in range(4):
            for b in range(a + 1, 4):
                contact = context['add'](contact, context['bracket'](letters[a], letters[b]))
        result += context['bp'](LU, context['star'](K))
        result += context['bp'](C, context['star'](context['scale'](F(-1, 2), contact)))
        result += F(1, 101) * (-1 if k == 0 else 1) * context['ep'](T, T)
    return result


def basis_sum(indices):
    q = context['field']()
    for index in indices:
        t, k = divmod(index, 40)
        if k < 16:
            i, j = divmod(k, 4)
            q[t][0][i][j] += 1
        else:
            i, j = divmod(k - 16, 6)
            q[t][1][i][j] += 1
    return q


def dense():
    diagonal = [literal_cut(basis_sum([i])) for i in range(80)]
    matrix = [[F(0)] * 80 for _ in range(80)]
    for i in range(80):
        matrix[i][i] = 2 * diagonal[i]
        for j in range(i):
            matrix[i][j] = matrix[j][i] = (
                literal_cut(basis_sum([i, j])) - diagonal[i] - diagonal[j])
    return matrix


def sparse():
    exec(compile(polynomial_code, 'legendre-root.py:polynomial', 'exec'), context)
    return context['M']


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', type=Path)
args = parser.parse_args()
observations = []
for algorithm in (dense, sparse):
    started = time.perf_counter()
    matrix = algorithm()
    elapsed = time.perf_counter() - started
    if algorithm is dense:
        baseline = matrix
    else:
        assert matrix == baseline
    observations.append({'method': algorithm.__name__, 'seconds': elapsed})
root = json.loads((PACKET / 'legendre-root-data.json').read_text())
for i in range(40):
    for j in range(40):
        assert baseline[i][j] == F(root['H0'][i][j])
        assert baseline[i + 40][j + 40] == F(root['H1'][i][j])
        assert baseline[i][j + 40] == baseline[j + 40][i] == F(root['B'][i][j])
result = {
    'source_sha256': hashlib.sha256(source.encode()).hexdigest(),
    'problem': 'All6400 rational Hessian coefficients of the same80-input native Full40 cut density; spatial-zero character,kappa1/101',
    'same_coefficients': True,
    'dense_scalar_density_evaluations': 3240,
    'sparse_symbolic_density_expansions': 1,
    'sparse_nonzero_monomials': len(context['ans'].d),
    'observations': observations,
    'limits': 'Single matched local run; includes each matrix construction, excludes shared definitions and output checks. Not a benchmark against optimized solvers; host load and software affect seconds. No physical or general algorithmic speedup theorem.'}
encoded = json.dumps(result, indent=2) + '\n'
if args.output:
    args.output.write_text(encoded)
print(encoded, end='')
