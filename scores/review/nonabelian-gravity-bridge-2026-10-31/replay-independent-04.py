#!/usr/bin/env python3
"""Independent full-presentation and non-tree gauge checks for review04.

This worker suggested the prior dictionary but authored no production Lean.
The replay uses S3 as affine transformations of Z/3 and free group words;
it imports neither production evaluators nor author arithmetic replays.
"""
import importlib.util
from itertools import product
import json
from pathlib import Path

SPEC = importlib.util.spec_from_file_location(
    "independent_words", Path(__file__).with_name("replay-independent-01.py"))
WORDS = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(WORDS)


class Operations:
    def __init__(self, one, mul, inv):
        self.one, self.mul, self.inv = one, mul, inv

    def prod(self, *values):
        answer = self.one
        for value in values:
            answer = self.mul(answer, value)
        return answer

    def pack(self, c):
        a, b, x, z = c
        axa = self.prod(self.inv(a), x, a)
        bzb = self.prod(self.inv(b), z, b)
        return ((self.one, self.one, self.one, a, self.one, self.one, b),
                (x, self.mul(axa, self.inv(z)), axa, x, bzb, bzb, z))

    def coordinates(self, state):
        return state[0][3], state[0][6], state[1][0], state[1][6]

    def relation(self, c):
        a, b, x, z = c
        return self.prod(self.inv(x), self.inv(a), x, a,
                         self.inv(z), self.inv(b), z, b)

    def gauge(self, h, state):
        return (tuple(self.prod(h[t], u, self.inv(h[s]))
                      for u, s, t in zip(state[0], WORDS.SOURCES, WORDS.TARGETS)),
                tuple(self.prod(h[t], p, self.inv(h[t]))
                      for p, t in zip(state[1], WORDS.TARGETS)))

    def normalize(self, state):
        u = state[0]
        h = (self.one, self.inv(u[0]), self.prod(self.inv(u[0]), self.inv(u[4])),
             self.prod(self.inv(u[0]), self.inv(u[1]), self.inv(u[2])),
             self.prod(self.inv(u[0]), self.inv(u[1])),
             self.prod(self.inv(u[0]), self.inv(u[4]), self.inv(u[5])))
        return self.gauge(h, state)

    def conjugate(self, h, c):
        return tuple(self.prod(h, value, self.inv(h)) for value in c)

    def moments(self, state):
        u, p = state
        q = [self.prod(self.inv(a), self.inv(b), a) for a, b in zip(u, p)]
        return tuple(self.prod(*(p[v - 1] if v > 0 else q[-v - 1]
                                 for v in vertex)) for vertex in WORDS.VERTICES)

    def twist(self, face, backwards, c):
        a, b, x, z = c
        if face == 0:
            x = self.mul(self.inv(a) if backwards else a, x)
        else:
            z = self.mul(self.inv(b) if backwards else b, z)
        return a, b, x, z

    def kick(self, face, backwards, state):
        u, p = state
        result = list(p)
        boundary = WORDS.BOUNDARIES[face]
        for index, incidence in enumerate(boundary):
            loop = boundary[index + 1:] + boundary[:index + 1]
            k = self.prod(*(u[e - 1] if e > 0 else self.inv(u[-e - 1])
                            for e in loop[::-1]))
            if backwards:
                k = self.inv(k)
            e = abs(incidence) - 1
            result[e] = (self.mul(k, p[e]) if incidence > 0
                         else self.prod(p[e], u[e], self.inv(k), self.inv(u[e])))
        return tuple(u), tuple(result)


def free_group_checks():
    group = Operations((), lambda a, b: WORDS.word(a, b), WORDS.inverse)
    c = tuple((i,) for i in range(1, 5))
    state = group.pack(c)
    assert group.moments(state) == ((), group.inv(group.relation(c)), (), (), (), ())
    gauges = tuple((i,) for i in range(5, 11))
    normalized = group.normalize(group.gauge(gauges, state))
    assert normalized == group.pack(group.conjugate(gauges[0], c))
    for face, backwards in product(range(2), (False, True)):
        changed = group.twist(face, backwards, c)
        assert group.pack(changed) == group.kick(face, backwards, state)
        assert group.relation(changed) == group.relation(c)
        assert group.twist(face, not backwards, changed) == c
        a, b, x, z = c
        generators = tuple(map(group.inv, (x, a, z, b)))
        after = tuple(map(group.inv, (changed[2], changed[0], changed[3], changed[1])))
        expected = list(generators)
        target, loop = (0, 1) if face == 0 else (2, 3)
        expected[target] = group.mul(generators[target], group.inv(generators[loop])
                                     if backwards else generators[loop])
        assert after == tuple(expected)
    return {"six_pack_defects": True, "independent_non_tree_gauges": 6,
            "normalization_residual_root_conjugation": True,
            "both_faces_both_signs": True, "all_signed_inverse_pairs": True}


def finite_checks():
    def mul(a, b):
        return ((a[0] + (-1 if a[1] else 1) * b[0]) % 3, (a[1] + b[1]) % 2)

    def inv(a):
        return (((1 if a[1] else -1) * a[0]) % 3, a[1])

    elements = tuple(product(range(3), range(2)))
    group = Operations((0, 0), mul, inv)
    representative = lambda c: min(group.conjugate(h, c) for h in elements)
    admitted = []
    classes = set()
    for c in product(elements, repeat=4):
        state = group.pack(c)
        assert group.coordinates(state) == c and group.normalize(state) == state
        assert (group.moments(state) == (group.one,) * 6) == (group.relation(c) == group.one)
        for face, backwards in product(range(2), (False, True)):
            changed = group.twist(face, backwards, c)
            assert group.pack(changed) == group.kick(face, backwards, state)
            assert group.relation(changed) == group.relation(c)
        if group.relation(c) == group.one:
            admitted.append(c)
            classes.add(representative(c))
    assert len(admitted) == 486 and len(classes) == 116
    for c in admitted:
        for d in admitted:
            assert (representative(c) == representative(d)) == any(
                group.gauge((h,) * 6, group.pack(c)) == group.pack(d) for h in elements)
    witness = ((0, 1), (1, 0), group.one, group.one)
    assert witness in admitted
    assert representative(group.twist(0, False, witness)) != representative(witness)
    state = group.pack(witness)
    non_tree_count = 0
    for h in product(elements, repeat=6):
        raw = group.gauge(h, state)
        normalized = group.normalize(raw)
        expected = group.conjugate(h[0], witness)
        assert group.moments(raw) == (group.one,) * 6
        assert normalized == group.pack(expected)
        assert representative(group.coordinates(normalized)) == representative(witness)
        non_tree_count += 1
    return {"all_coordinate_assignments": 6 ** 4, "admitted_presentations": len(admitted),
            "presentation_conjugacy_classes": len(classes),
            "all_presentation_pairs_conjugacy_tests": len(admitted) ** 2,
            "non_tree_vertex_gauge_tests": non_tree_count,
            "witness_orbit_changes": True}


if __name__ == "__main__":
    print(json.dumps({"scope": "independent algebra and finite orbit checks; no analytic/topological identification",
                      "free_group": free_group_checks(), "S3_affine": finite_checks()}, indent=2))
