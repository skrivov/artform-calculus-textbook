#!/usr/bin/env python3
"""Independent exact D3 reconstruction; never import the author's producer."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import hashlib
import json
import sys

HERE = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


# D3 = Z3 semidirect Z2, with reflection S(x)=1-x and rotation R(x)=x+1.
G = list(product(range(3), range(2)))
one = (0, 0)


def mul(a, b):
    return ((a[0] + (-1)**a[1] * b[0]) % 3, (a[1] + b[1]) % 2)


def inv(a):
    return ((-(-1)**a[1] * a[0]) % 3, a[1])


def conjugate(h, a):
    return mul(mul(h, a), inv(h))


def perm(a):
    return tuple((a[0] + (i if not a[1] else 1-i)) % 3 for i in range(3))


for a, b in product(G, repeat=2):
    assert perm(mul(a, b)) == tuple(perm(a)[perm(b)[i]] for i in range(3))
    assert mul(a, inv(a)) == mul(inv(a), a) == one

X = list(product(G, repeat=2))
index = {x: i for i, x in enumerate(X)}
n = len(X)


def gauge(h, x):
    return tuple(conjugate(h, a) for a in x)


def commutator(x):
    a, b = x
    return mul(mul(mul(a, b), inv(a)), inv(b))


flat = [commutator(x) == one for x in X]
orbits = {frozenset(gauge(h, x) for h in G) for x in X}
assert len(orbits) == 11 and sum(not b for b in flat) == 18


def electric(v, edge):
    return [sum(v[index[(c, x[1]) if edge == 0 else (x[0], c)]] for c in G)/3-v[i]
            for i, x in enumerate(X)]


def magnetic(v, active=True):
    return [a if isflat or not active else -a for a, isflat in zip(v, flat)]


def apply_gate(v, slot, active=True):
    return magnetic(v, active) if slot % 3 == 0 else electric(v, (slot-1) % 3)


def tick(v, active=True):
    return electric(electric(magnetic(v, active), 0), 1)


def dot(a, b):
    return sum(x*y for x, y in zip(a, b))


def gauge_vector(h, v):
    out = [F(0)]*n
    for x, a in zip(X, v):
        out[index[gauge(h, x)]] = a
    return out


basis = [[F(i == j) for i in range(n)] for j in range(n)]
gates = [lambda v: magnetic(v), lambda v: electric(v, 0), lambda v: electric(v, 1)]
for gate in gates:
    columns = [gate(v) for v in basis]
    for i, v in enumerate(basis):
        assert gate(gate(v)) == v
        for h in G:
            assert gate(gauge_vector(h, v)) == gauge_vector(h, gate(v))
        for j in range(n):
            assert dot(columns[i], columns[j]) == F(i == j)

# Derive each actual endpoint kernel directly from six replacement events.
branch_tests = 0
for edge, x in product(range(2), X):
    v = [F(0)]*n
    endpoints = []
    for c in G:
        y = (c, x[1]) if edge == 0 else (x[0], c)
        endpoints.append(y)
        v[index[y]] += F(1, 3)-F(c == x[edge])
        for h in G:
            yc = (conjugate(h, c), gauge(h, x)[1]) if edge == 0 else (
                gauge(h, x)[0], conjugate(h, c))
            assert yc == gauge(h, y)
            assert (conjugate(h, c) == gauge(h, x)[edge]) == (c == x[edge])
            branch_tests += 1
    assert len(set(endpoints)) == 6
    assert v == electric(basis[index[x]], edge)

# Bind the separately reconstructed group to the explicit Lean element order.
by_perm = {perm(g): g for g in G}
perms = [(0, 1, 2), (1, 0, 2), (2, 1, 0), (0, 2, 1), (1, 2, 0), (2, 0, 1)]
lean_group = [by_perm[p] for p in perms]
lean_X = list(product(lean_group, repeat=2))
classes = []
codes = []
for x in lean_X:
    orbit = frozenset(gauge(h, x) for h in G)
    if orbit not in classes:
        classes.append(orbit)
    codes.append(classes.index(orbit))
weights = [len(o) for o in classes]
representatives = [next(i for i, x in enumerate(lean_X) if x in o) for o in classes]
assert weights == [1, 3, 2, 3, 3, 6, 6, 2, 6, 2, 2]
cert = json.loads((HERE/'replay-root.json').read_text())
assert codes == cert['codes'] and weights == cert['weights'] and representatives == cert['reps']
indicators = [[F(x in o) for x in X] for o in classes]
for gate in gates:
    images = [gate(v) for v in indicators]
    for i, v in enumerate(images):
        for h in G:
            assert gauge_vector(h, v) == v
        for j, w in enumerate(images):
            assert dot(v, w) == F(weights[i] if i == j else 0)
for edge in range(2):
    columns = [electric(v, edge) for v in indicators]
    for i, rep in enumerate(representatives):
        for j in range(11):
            assert columns[j][index[lean_X[rep]]]*3 == cert['electric_numerators'][edge][i][j]
assert [1 if commutator(lean_X[r]) == one else -1 for r in representatives] == cert['signs']

# The isometric inclusion's projector is exactly averaging over full gauge orbits.
for orbit in classes:
    for y in orbit:
        for x in X:
            assert F(sum(gauge(h, x) == y for h in G), 6) == F(x in orbit, len(orbit))

source_orbit = frozenset((one, conjugate(h, by_perm[(1, 0, 2)])) for h in G)
source = [F(x in source_orbit) for x in X]
assert source == indicators[1] and len(source_orbit) == 3
assert dot(source, source) == 3 and all(flat[i] for i, a in enumerate(source) if a)
divisors = [1, 1, 3, 9, 9, 27, 81]
results = {}
for active in (False, True):
    v = source
    stages = [v]
    for slot in range(6):
        v = apply_gate(v, slot, active)
        assert dot(v, v) == 3
        assert all(gauge_vector(h, v) == v for h in G)
        stages.append(v)
    assert v == tick(tick(source, active), active)
    table = cert['results'][str(active).lower()]['integer_stages']
    for step in range(7):
        for x in X:
            code = codes[lean_X.index(x)]
            assert stages[step][index[x]] == F(table[step][code], divisors[step])
    curved = sum(a*a for a, isflat in zip(v, flat) if not isflat)
    probability = curved/3
    assert probability == (F(32, 81) if active else 0)
    if not active:
        assert v == source
    results[str(active).lower()] = dict(normalized_mass='1',
                                       curvature_probability=str(probability),
                                       all_seven_stages_match=True)

# Both inverse orders for the whole tick, and an actual non-involutive tick.
def reverse_tick(v):
    return magnetic(electric(electric(v, 1), 0))


for v in basis:
    assert reverse_tick(tick(v)) == tick(reverse_tick(v)) == v
assert tick(tick(source)) != source
averaged = [(electric(basis[0], 0)[i]+basis[0][i])/2 for i in range(n)]
assert dot(averaged, averaged) == F(1, 6)  # Averaging alone is not unitary.
final = tick(tick(source))
orbit_final = [final[index[lean_X[r]]] for r in representatives]
naive = sum(a*a for a, r in zip(orbit_final, representatives)
            if commutator(lean_X[r]) != one)/sum(a*a for a in orbit_final)
assert naive != F(32, 81)  # Treating orbit representatives as unit raw vectors fails.
assert (one, one) != (by_perm[(1, 0, 2)], one)  # Same constant replacement has two inputs.

result = dict(date='2026-10-31', reviewer='/root/gravity_fidelity_review_01', passed=True,
              representation='D3 semidirect product, exact Fraction arithmetic',
              imported_author_code=False, group_order=6, raw_states=36, physical_orbits=11,
              orbit_weights=weights, nonflat_states=18, full_raw_gate_orthogonality=True,
              gauge_covariance=True, branch_endpoint_and_transport_tests=branch_tests,
              full_weighted_descent=True, normalized_projector_equals_gauge_average=True,
              reverse_tick_both_orders_all_raw_basis=True, tick_is_not_involutive=True,
              results=results, negative_controls=dict(averaging_column_norm_squared=str(dot(averaged, averaged)),
              incorrect_unweighted_orbit_probability=str(naive)),
              source_hashes={p.name: sha(p) for p in [HERE/'source-pins.json', HERE/'replay-root.json']},
              script_sha256=sha(Path(__file__)))
target = HERE/'replay-independent.json'
if '--check' in sys.argv:
    assert json.loads(target.read_text()) == result
else:
    target.write_text(json.dumps(result, indent=2)+'\n')
print('Independent D3 replay passed:36 raw,11 orbits,32/81 versus0; all fourteen stage states checked.')
