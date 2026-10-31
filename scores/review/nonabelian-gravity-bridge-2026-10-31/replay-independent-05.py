#!/usr/bin/env python3
"""Independent dipole/orthant review in free words, rational matrices and Q(r).

Here r^2=1/2. No author replay or production evaluator is imported. The
reviewer supplied earlier conceptual/convention checks, but authored none
of the six production Lean modules under review.
"""
from dataclasses import dataclass
from fractions import Fraction as F
from functools import reduce
import importlib.util
from itertools import permutations, product
import json
from pathlib import Path

SPEC = importlib.util.spec_from_file_location(
    "independent_words", Path(__file__).with_name("replay-independent-01.py"))
WORDS = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(WORDS)


@dataclass(frozen=True)
class Qr:
    a: F = F(0)
    b: F = F(0)

    def __add__(self, other):
        return Qr(self.a + other.a, self.b + other.b)

    def __neg__(self):
        return Qr(-self.a, -self.b)

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        return Qr(self.a * other.a + self.b * other.b / 2,
                  self.a * other.b + self.b * other.a)


ZERO, ONE, RADIUS = Qr(), Qr(F(1)), Qr(F(0), F(1))


def quat(*values):
    return tuple(x if isinstance(x, Qr) else Qr(F(x)) for x in values)


def qmul(a, b):
    w, x, y, z = a
    v, p, q, r = b
    return (w*v-x*p-y*q-z*r, w*p+x*v+y*r-z*q,
            w*q-x*r+y*v+z*p, w*r+x*q-y*p+z*v)


def conjugate(q):
    return (q[0], -q[1], -q[2], -q[3])


def norm(q):
    return reduce(lambda a, b: a+b, (x*x for x in q), ZERO)


class Group:
    def __init__(self, one, mul, inv):
        self.one, self.mul, self.inv = one, mul, inv

    def prod(self, *values):
        return reduce(self.mul, values, self.one)

    def gauge(self, h, state):
        return (tuple(self.prod(h[1], u, self.inv(h[0])) for u in state[0]),
                tuple(self.prod(h[1], p, self.inv(h[1])) for p in state[1]))

    def moments(self, state):
        u, p = state
        return (self.prod(*(self.prod(self.inv(a), self.inv(b), a) for a, b in zip(u, p))),
                self.prod(*p[::-1]))

    def kick(self, state, backwards=False):
        u, p = state
        k = self.mul(u[0], self.inv(u[1]))
        if backwards:
            k = self.inv(k)
        return u, (self.mul(k, p[0]), self.mul(p[1], self.inv(k)), p[2], p[3])

    def erase(self, p):
        return (self.inv(p[0]), self.one, self.one, self.one), p


def free_checks():
    g = Group((), lambda a, b: WORDS.word(a, b), WORDS.inverse)
    raw = (tuple((i,) for i in range(1, 5)), tuple((i,) for i in range(5, 9)))
    h = ((9,), (10,))
    for back in (False, True):
        after = g.kick(raw, back)
        assert g.moments(after) == g.moments(raw)
        assert g.kick(after, not back) == raw
        assert g.kick(g.gauge(h, raw), back) == g.gauge(h, after)
    p = ((1,), (2,), (3,), g.inv(g.prod((3,), (2,), (1,))))
    state = g.erase(p)
    assert g.moments(state) == ((), ())
    assert g.kick(state)[1] == ((), g.mul(p[1], p[0]), p[2], p[3])
    assert g.gauge(h, g.kick(state))[1][0] == ()
    for back in (False, True):
        assert g.kick((((),)*4, p), back) == (((),)*4, p)
    return {"raw_defects_inverse_gauges_both_signs": True,
            "universal_closed_tuple_erasure": True, "identity_link_positive_control": True}


def identity(n):
    return tuple(tuple(F(i == j) for j in range(n)) for i in range(n))


def mm(a, b):
    n = len(a)
    return tuple(tuple(sum(a[i][k]*b[k][j] for k in range(n)) for j in range(n)) for i in range(n))


def mv(a, v):
    return tuple(sum(x*y for x, y in zip(row, v)) for row in a)


def det(a):
    answer = F(0)
    for p in permutations(range(len(a))):
        sign = (-1)**sum(p[i] > p[j] for i in range(len(p)) for j in range(i+1, len(p)))
        answer += sign * reduce(lambda x, y: x*y, (a[i][p[i]] for i in range(len(a))), F(1))
    return answer


def geometric_checks():
    unit = quat(1, 0, 0, 0)
    basis = (quat(0, 1, 0, 0), quat(0, 0, 1, 0), quat(0, 0, 0, 1))
    p = (quat(RADIUS, RADIUS, 0, 0), quat(RADIUS, 0, RADIUS, 0),
         quat(RADIUS, 0, 0, RADIUS), quat(RADIUS, 0, -RADIUS, 0))
    g = Group(unit, qmul, conjugate)
    assert all(norm(q) == ONE for q in p)
    assert g.prod(*p[::-1]) == unit
    assert all(q[0]*q[0] == Qr(F(1, 2)) for q in p)

    def edge(t, s):
        a = [list(row) for row in identity(4)]
        a[t][t] = a[s][s] = F(0)
        a[t][s], a[s][t] = F(1), F(-1)
        return tuple(map(tuple, a))

    for s, t in permutations(range(4), 2):
        assert mm(edge(s, t), edge(t, s)) == identity(4)
        assert mv(edge(t, s), identity(4)[s]) == identity(4)[t]
    paths = (((3, 2), (2, 1), (1, 3)), ((3, 0), (0, 2), (2, 3)),
             ((3, 1), (1, 0), (0, 3)), ((3, 1), (1, 2), (2, 0), (0, 1), (1, 3)))
    loops = [reduce(mm, (edge(t, s) for t, s in path), identity(4)) for path in paths]
    assert reduce(mm, loops[::-1], identity(4)) == identity(4)
    rotations = [tuple(tuple(a[i][j] for j in range(3)) for i in range(3)) for a in loops]
    for f in range(4):
        assert mv(loops[f], identity(4)[3]) == identity(4)[3]
        assert det(rotations[f]) == 1
        for j in range(3):
            actual = g.prod(p[f], basis[j], conjugate(p[f]))
            assert actual == quat(0, *(rotations[f][i][j] for i in range(3)))
    normals = ((1, 0, 0), (0, 1, 0), (0, 0, 1), (0, -1, 0))
    dot = lambda a, b: sum(x*y for x, y in zip(a, b))
    cross = lambda a, b: (a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2], a[0]*b[1]-a[1]*b[0])
    exceptional = dot(normals[1], mv(rotations[0], normals[3]))
    gram = tuple(tuple(exceptional if {i, j} == {1, 3} else dot(normals[i], normals[j])
                       for j in range(4)) for i in range(4))
    ordinary = tuple(tuple(dot(a, b) for b in normals) for a in normals)
    assert gram == identity(4) and det(ordinary) == 0
    inverse_rotation2 = tuple(zip(*rotations[2]))
    triples = (dot(cross(normals[0], normals[1]), normals[2]),
               dot(cross(normals[0], normals[2]), normals[3]),
               dot(cross(normals[1], normals[0]), mv(rotations[0], normals[3])),
               dot(cross(normals[2], normals[1]), mv(inverse_rotation2, normals[3])))
    assert triples == (1, 1, 1, 1)
    state = g.erase(p)
    assert g.moments(state) == (unit, unit)
    assert all(norm(q) == ONE for row in state for q in row)
    after = g.kick(state)
    assert g.moments(after) == (unit, unit) and after[1][0] == unit
    assert g.kick(((unit,)*4, p)) == ((unit,)*4, p)
    return {"coefficient_field": "Q(r), r^2=1/2", "actual_HHR_loop_paths": 4,
            "inverse_endpoint_pairs": 12, "quaternion_basis_action_checks": 12,
            "corrected_Gram_determinant": str(det(gram)), "ordinary_Gram_determinant": str(det(ordinary)),
            "convexity_triples": [int(value) for value in triples], "unit_closed_noncentral_faces": 4,
            "erasing_fixture_Gauss_before_after": True, "collapsed_face": "identity"}


def finite_checks():
    one = (0, 0)
    mul = lambda a, b: ((a[0]+(-1 if a[1] else 1)*b[0]) % 3, (a[1]+b[1]) % 2)
    inv = lambda a: (((1 if a[1] else -1)*a[0]) % 3, a[1])
    g = Group(one, mul, inv)
    elements = tuple(product(range(3), range(2)))
    count = 0
    for p0, p1, p2 in product(elements, repeat=3):
        p = (p0, p1, p2, inv(g.prod(p2, p1, p0)))
        erased = g.erase(p)
        assert g.moments(erased) == (one, one)
        assert g.kick(erased)[1][0] == one
        assert g.kick(((one,)*4, p)) == ((one,)*4, p)
        count += 1
    return {"all_S3_closed_target_tuples": count, "erasing_and_identity_lifts": True}


if __name__ == "__main__":
    print(json.dumps({"scope": "exact finite/group data; sphere LC interpretation reviewed analytically, not replayed as a manifold theorem",
                      "free_words": free_checks(), "orthant": geometric_checks(),
                      "S3": finite_checks()}, indent=2))
