"""Exact exploratory gauge-score controls; not registered Lean claims.

Run from any directory. Writes only pilot_checks.json next to this script.
All examples have specified finite carriers; no continuum or physical QCD claim.
"""
from fractions import Fraction as Q
from itertools import permutations, product
import json
from pathlib import Path


def eye(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def transpose(a):
    return [list(x) for x in zip(*a)]


def mm(a, b):
    return [[sum(x * y for x, y in zip(row, col))
             for col in zip(*b)] for row in a]


def mv(a, v):
    return [sum(x * y for x, y in zip(row, v)) for row in a]


def plus(a, b):
    return [[x + y for x, y in zip(r, s)] for r, s in zip(a, b)]


def scale(c, a):
    return [[c * x for x in row] for row in a]


def block(a, b, c, d):
    return [r + s for r, s in zip(a, b)] + [r + s for r, s in zip(c, d)]


def conjugate(a, p, pi):
    return mm(mm(p, a), pi)


def canonical_processing():
    n = 5
    identity = eye(n)
    zero = scale(0, identity)
    shift = [[int(j == (i + 1) % n) for j in range(n)] for i in range(n)]
    back = transpose(shift)
    lap = plus(scale(2, identity), scale(-1, plus(shift, back)))
    tick = block(plus(identity, scale(-1, lap)), scale(-1, identity), lap, identity)
    processor = block(shift, zero, zero, back)
    inverse = block(back, zero, zero, shift)
    symplectic = block(zero, identity, scale(-1, identity), zero)
    processed = conjugate(tick, processor, inverse)
    assert mm(processor, inverse) == mm(inverse, processor) == eye(2 * n)
    assert mm(mm(transpose(tick), symplectic), tick) == symplectic
    changed = mm(mm(transpose(processed), symplectic), processed)
    assert symplectic[0][1] == 0 and changed[0][1] % 3 == 2
    # A simultaneous shift is canonical, although its Laurent determinant is x^2.
    common = block(shift, zero, zero, shift)
    assert mm(mm(transpose(common), symplectic), common) == symplectic
    return {
        'carrier': 'five periodic canonical pairs over C3',
        'original_tick': 'E+=gA; A-=E, g=2-S-S^-1',
        'processor': 'diag(S,S^-1), determinant1 as a Laurent matrix',
        'witness_input_labels': ['A0', 'A1'],
        'commutator_exponent_before': 0,
        'commutator_exponent_after_mod3': 2,
        'processed_images_mod3': [[x % 3 for x in processed_col]
                                 for processed_col in transpose(processed)[:2]],
        'common_shift_canonical': True,
        'scope': 'Necessary Weyl-label condition; no complete gauge-profile lift asserted.',
    }


def spatial_memory():
    n = 4

    def tick(state):
        a, e = state
        ep = [(e[i] + 2 * a[i] - a[(i - 1) % n] - a[(i + 1) % n]) % 8
              for i in range(n)]
        return ([(a[i] - ep[i]) % 8 for i in range(n)], ep)

    def read(state):
        a, e = state
        # Block sums of adjacent B=DA, and selected electric links.
        return [((a[(i + 2) % n] - a[i]) % 8, e[i]) for i in (0, 2)]

    s0 = ([0] * n, [0] * n)
    s1 = ([0, 1, 0, 0], [0] * n)
    assert read(s0) == read(s1)
    assert read(tick(s0)) != read(tick(s1))
    assert read(tick(s1)) == [(0, 7), (0, 7)]
    # Both are transverse vacuum-Gauss states, with all horizontal links zero.
    # Their distinct fine curvature proves this is not a pure-gauge difference.
    fine_b = [(s1[0][(i + 1) % n] - s1[0][i]) % 8 for i in range(n)]
    assert fine_b == [1, 7, 0, 0]
    return {
        'carrier': 'C8 transverse Maxwell sector, periodic width4',
        'fine_potential': s1[0], 'fine_electric': s1[1],
        'fine_curvature': fine_b,
        'common_initial_coarse_read': read(s0),
        'zero_state_next_read': read(tick(s0)),
        'hidden_curvature_state_next_read': read(tick(s1)),
        'conclusion': 'No autonomous one-tick map on exactly this coarse reading for all fine states.',
        'scope': 'Declared gauge-invariant reading, zero source; no claim about all coarse maps or cadences.',
    }


def nonabelian_score():
    group = list(permutations(range(3)))
    unit = (0, 1, 2)

    def mul(a, b):
        return tuple(a[b[i]] for i in range(3))

    def inv(a):
        return tuple(a.index(i) for i in range(3))

    def comm(a, b):
        return mul(mul(mul(a, b), inv(a)), inv(b))

    def conj(g, a):
        return mul(mul(g, a), inv(g))

    states = list(product(group, repeat=2))
    index = {s: i for i, s in enumerate(states)}
    n = len(states)
    m1 = [[Q(int(b == d), 3) - int(a == c and b == d)
           for c, d in states] for a, b in states]
    m2 = [[Q(int(a == c), 3) - int(a == c and b == d)
           for c, d in states] for a, b in states]
    k = [[int(i == j) * (1 if comm(*s) == unit else -1)
          for j in range(n)] for i, s in enumerate(states)]
    identity = eye(n)
    assert mm(m1, m1) == mm(m2, m2) == mm(k, k) == identity
    u = mm(mm(m2, m1), k)
    assert mm(transpose(u), u) == mm(u, transpose(u)) == identity
    orbit_set = {frozenset((conj(g, a), conj(g, b)) for g in group)
                 for a, b in states}
    assert len(orbit_set) == 11
    for g in group:
        perm = [index[(conj(g, a), conj(g, b))] for a, b in states]
        for i in range(n):
            for j in range(n):
                assert u[perm[i]][perm[j]] == u[i][j]
    noncommuting = [comm(*s) != unit for s in states]
    assert sum(noncommuting) == 18
    transposition = (1, 0, 2)
    source_orbit = {(conj(g, unit), conj(g, transposition)) for g in group}
    psi = [int(s in source_orbit) for s in states]
    norm = sum(x * x for x in psi)
    out = mv(u, mv(u, psi))
    assert sum(x * x for x in out) == norm == 3
    probability = sum(x * x for x, active in zip(out, noncommuting) if active) / norm
    assert probability > 0
    free = mm(m2, m1)
    assert mm(free, free) == identity
    return {
        'carrier': 'two S3 loop coordinates; one-vertex torus word aba^-1b^-1',
        'raw_states': n, 'physical_simultaneous_conjugacy_orbits': len(orbit_set),
        'noncommuting_raw_states': sum(noncommuting),
        'electric_gate': 'M_e=2P_e-I; P_e averages all six replacements of edge e',
        'curvature_gate': 'K=+1 on commuting pairs and -1 otherwise',
        'score': 'U=M2 M1 K, rightmost gate first',
        'raw_two_sided_orthogonal': True, 'gauge_commutes_exactly': True,
        'physical_orbit_source_size': norm,
        'two_tick_noncommuting_curvature_probability': str(probability),
        'same_probability_with_K_identity': '0',
        'coefficient_scope': 'raw gates rational; normalized physical orbit columns require square roots',
        'scope': 'Finite quantum prototype; constructor/legal-process packaging and Lean validation outstanding; not a classical impulse law or QCD claim.',
    }


if __name__ == '__main__':
    report = {'status': 'exact exploratory controls passed',
              'canonical_processing': canonical_processing(),
              'spatial_memory': spatial_memory(),
              'nonabelian_score': nonabelian_score(),
              'new_registered_or_approved_scores': 0}
    target = Path(__file__).with_suffix('.json')
    target.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))
