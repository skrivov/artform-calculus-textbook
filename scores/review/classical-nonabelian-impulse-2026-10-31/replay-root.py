#!/usr/bin/env python3
"""Exact author replay, not independent fidelity approval. Standard library only."""
import argparse
import hashlib
from itertools import permutations, product
import json
from pathlib import Path

REVIEW = Path(__file__).resolve().parent
PERMS = list(permutations(range(3)))
IDENTITY = tuple(range(3))
ONE = PERMS.index(IDENTITY)


def compose(a, b):
    return tuple(a[b[i]] for i in range(len(a)))


MULT = [[PERMS.index(compose(a, b)) for b in PERMS] for a in PERMS]
INV = [next(j for j in range(6) if MULT[i][j] == ONE) for i in range(6)]


def mul(*args):
    value = ONE
    for arg in args:
        value = MULT[value][arg]
    return value


def outgoing(u, p, edge):
    return mul(INV[u[edge]], INV[p[edge]], u[edge])


def defect(u, p):
    return (mul(outgoing(u, p, 0), p[3], outgoing(u, p, 4)),
            mul(outgoing(u, p, 1), p[0]),
            mul(outgoing(u, p, 2), p[1], p[4]),
            mul(outgoing(u, p, 3), p[2]))


def holonomy(u):
    return (mul(u[0], u[3], u[2], u[1]), mul(u[1], u[0], u[3], u[2]),
            mul(u[2], u[1], u[0], u[3]), mul(u[3], u[2], u[1], u[0]), ONE)


def kick(u, p, backward=False):
    return u, tuple(mul(INV[h] if backward else h, q) for h, q in zip(holonomy(u), p))


def drift(u, p, backward=False):
    return tuple(mul(INV[q] if backward else q, a) for a, q in zip(u, p)), p


def drift_link(u, p, edge):
    values = list(u)
    values[edge] = mul(p[edge], u[edge])
    return tuple(values), p


def gauge(h, u, p):
    src, tgt = (0, 1, 2, 3, 0), (1, 2, 3, 0, 2)
    return (tuple(mul(h[tgt[e]], u[e], INV[h[src[e]]]) for e in range(5)),
            tuple(mul(h[tgt[e]], p[e], INV[h[tgt[e]]]) for e in range(5)))


zero = (ONE,) * 4
rotation = PERMS.index((1, 2, 0))
reflection = PERMS.index((1, 0, 2))
initial = ((ONE, ONE, ONE, rotation, ONE),
           (reflection, reflection, ONE, ONE, INV[reflection]))
final = drift(*kick(*initial))
assert defect(*initial) == defect(*final) == zero
assert mul(rotation, reflection) != mul(reflection, rotation)
assert holonomy(initial[0])[3] != ONE and holonomy(final[0])[3] == ONE
assert kick(*initial) != initial
partial = list(initial[1])
partial[0] = mul(holonomy(initial[0])[0], partial[0])
assert defect(initial[0], partial) != zero


def wrong_star(u, p):
    return mul(outgoing(u, p, 2), p[4], p[1])


assert wrong_star(*initial) == ONE and wrong_star(*kick(*initial)) != ONE
admitted_count = 0
trace = hashlib.sha256()
for u in product(range(6), repeat=5):
    for p0, p4 in product(range(6), repeat=2):
        p1 = mul(u[1], p0, INV[u[1]])
        p2 = mul(u[2], p1, p4, INV[u[2]])
        p3 = mul(u[3], p2, INV[u[3]])
        p = (p0, p1, p2, p3, p4)
        if defect(u, p) != zero:
            continue
        admitted_count += 1
        trace.update(bytes(u + p))
        for step in (kick, drift):
            for backward in (False, True):
                result = step(u, p, backward)
                assert defect(*result) == zero
                assert step(*result, not backward) == (u, p)
assert admitted_count == 104976
raw_samples = []
for a, b, c in product(range(6), repeat=3):
    u = (a, b, c, (a + b) % 6, (b + c) % 6)
    p = (c, a, b, (a + c) % 6, (b + c) % 6)
    raw_samples.append((u, p))
    for step in (kick, drift):
        for backward in (False, True):
            result = step(u, p, backward)
            assert defect(*result) == defect(u, p)
            assert step(*result, not backward) == (u, p)
for h in product(range(6), repeat=4):
    transformed = gauge(h, *initial)
    assert defect(*transformed) == zero
    for step in (kick, drift):
        for backward in (False, True):
            assert step(*transformed, backward) == gauge(h, *step(*initial, backward))
    assert holonomy(transformed[0]) == tuple(
        mul(h[v], x, INV[h[v]]) for v, x in zip((1, 2, 3, 0, 2), holonomy(initial[0])))
    assert transformed != final
for order in permutations(range(5)):
    for start in [kick(*initial)] + raw_samples[:6]:
        current = start
        for edge in order:
            current = drift_link(*current, edge)
        assert current == drift(*start)
# A separately written semidirect representation authenticates the group table.
d3 = list(product(range(3), range(2)))

def dm(a, b):
    return ((a[0] + (-1 if a[1] else 1) * b[0]) % 3, (a[1] + b[1]) % 2)


def d3_to_perm(a):
    result = ONE
    for _ in range(a[0]):
        result = mul(result, rotation)
    return mul(result, reflection) if a[1] else result


assert len({d3_to_perm(a) for a in d3}) == 6
assert all(d3_to_perm(dm(a, b)) == mul(d3_to_perm(a), d3_to_perm(b)) for a in d3 for b in d3)
# The A5 control uses actual even permutations on5 letters, no continuous input.
r5, t5, i5 = (1, 2, 0, 3, 4), (1, 0, 2, 4, 3), tuple(range(5))

def parity(a):
    return sum(a[i] > a[j] for i in range(5) for j in range(i + 1, 5)) % 2


def pm(*args):
    result = i5
    for a in args:
        result = compose(result, a)
    return result


assert parity(r5) == parity(t5) == 0 and pm(r5, t5) != pm(t5, r5)
u5 = (i5, i5, i5, r5, i5)
p5 = (t5, t5, i5, i5, t5)
h5 = (r5, r5, r5, r5, i5)
kicked5 = tuple(pm(h, p) for h, p in zip(h5, p5))
final5 = tuple(pm(p, u) for p, u in zip(kicked5, u5))
assert pm(final5[3], final5[2], final5[1], final5[0]) == i5
receipt = dict(date='2026-10-31', author='root', independent_fidelity_review=False,
               group_order=6, raw_states=6**10, gauss_admitted_states=admitted_count,
               admitted_state_trace_sha256=trace.hexdigest(),
               raw_defect_samples=len(raw_samples), vertex_gauges_checked=6**4,
               drift_orders_checked=120, drift_inputs_per_order=7,
               d3_group_table_crosscheck=True, a5_even_permutation_control=True,
               initial=dict(U=initial[0], P=initial[1]), final=dict(U=final[0], P=final[1]),
               initial_nonflat=True, final_flat=True, noncommuting_impulses=True,
               partial_kick_rejected=True, wrong_star_order_rejected=True,
               gauss_preservation=True, both_shear_inverse_orders=True)
parser = argparse.ArgumentParser()
parser.add_argument('--check', action='store_true')
args = parser.parse_args()
target = REVIEW / 'replay-root.json'
if args.check:
    stored = json.loads(target.read_text())
    assert stored == json.loads(json.dumps(receipt))
else:
    target.write_text(json.dumps(receipt, indent=2) + '\n')
print('PASS:104976 admitted S3 states; noncommuting S3/A5 curvature-to-flat controls.')
