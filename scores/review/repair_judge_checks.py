#!/usr/bin/env python3
"""Independent finite witnesses; stdout is the reproducible review record.

These checks support fidelity review and do not replace the Lean proofs.
"""
import itertools
import json
import math


def graph_check(n, representatives, adjacent):
    def neg(u):
        return tuple(-a % n for a in u)

    def cls(u):
        return min(u, neg(u))

    def det(u, v):
        return (u[0] * v[1] - u[1] * v[0]) % n

    primitive = [u for u in itertools.product(range(n), repeat=2)
                 if math.gcd(*u, n) == 1]
    indices = {cls(u): i for i, u in enumerate(representatives)}
    assert len(indices) == len(representatives)
    assert set(indices) == {cls(u) for u in primitive}
    edges = {frozenset((i, j)) for i, j in
             itertools.combinations(range(len(representatives)), 2) if adjacent(i, j)}
    for i, u in enumerate(representatives):
        for j, v in enumerate(representatives):
            assert adjacent(i, j) == (det(u, v) in (1, n - 1))
    # Independently construct the ledger's actual faces, then compare their
    # entire pullback with the standard graph's triangular faces.
    faces = set()
    for u, v in itertools.product(primitive, repeat=2):
        if det(u, v) == 1:
            w = tuple((a + b) % n for a, b in zip(u, v))
            faces.add(frozenset(indices[cls(z)] for z in (u, v, w)))
    triangles = {frozenset(t) for t in
                 itertools.combinations(range(len(representatives)), 3)
                 if all(frozenset(e) in edges for e in itertools.combinations(t, 2))}
    assert faces == triangles
    assert all(len(f) == 3 for f in faces)
    return {"n": n, "primitive_states": len(primitive), "vertices": len(indices),
            "edges": len(edges), "faces": len(faces),
            "all_vertices_edges_and_faces_match": True}


def ico_edge(i, j):
    # A top pole, a bottom pole, two pentagons, and staggered cross edges.
    return ((i == 0 and 2 <= j < 7) or (i == 1 and 7 <= j < 12) or
            (2 <= i < 7 and 2 <= j < 7 and j - 2 == (i - 2 + 1) % 5) or
            (7 <= i < 12 and 7 <= j < 12 and j - 7 == (i - 7 + 1) % 5) or
            (2 <= i < 7 and 7 <= j < 12 and
             j - 7 in (i - 2, (i - 2 + 4) % 5)))


def reading_check(n):
    def mul(a, b):
        return tuple(sum(a[2 * i + k] * b[2 * k + j] for k in range(2)) % n
                     for i in range(2) for j in range(2))

    observations = {}
    repeated = 0
    matrices = 0
    for a in itertools.product(range(n), repeat=4):
        if (a[0] * a[3] - a[1] * a[2]) % n != 1:
            continue
        matrices += 1
        t, r = (a[0] + a[3]) % n, a[0]
        powers, power = [], (1, 0, 0, 1)
        for _ in range(9):
            powers.append(power[0])
            power = mul(power, a)
        signature = tuple(powers[:4])
        assert observations.setdefault(signature, (t, r)) == (t, r)
        for eps in range(n):
            if eps * eps % n == 1 and 2 * eps % n == t:
                repeated += 1
                assert all(value == pow(eps, k, n) * (1 + k * (eps * r - 1)) % n
                           for k, value in enumerate(powers))
    return {"dial": n, "sl2_matrices": matrices,
            "four_tick_signatures": len(observations),
            "repeated_root_instances": repeated, "passed": True}


def singularity_checks():
    checks = []
    for p in (3, 5, 7, 11, 13):
        for q in range(2, p):
            singular = [(x, lam) for x in range(1, p) for lam in range(1, p)
                        if (x * (lam - 1)**2 - q * (x - 1)**2 * lam) % p == 0
                        and ((lam - 1)**2 - 2 * q * (x - 1) * lam) % p == 0
                        and (2 * x * (lam - 1) - q * (x - 1)**2) % p == 0]
            assert singular == [(1, 1)]
            roots = [h for h in range(p) if h * h % p == q]
            assert len(roots) in (0, 2)
            checks.append({"p": p, "q": q, "singular_points": singular,
                           "rational_tangent_roots": roots})
    return checks


def main():
    graphs = [graph_check(3, [(0, 1), (1, 0), (1, 1), (1, 2)], lambda i, j: i != j),
              graph_check(4, [(0, 1), (2, 1), (1, 0), (1, 2), (1, 1), (1, 3)],
                          lambda i, j: i // 2 != j // 2),
              graph_check(5, [(0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (1, 3),
                              (1, 4), (2, 1), (2, 3), (2, 0), (2, 2), (2, 4)],
                          lambda i, j: ico_edge(i, j) or ico_edge(j, i))]
    cycle = [0, 1, 3, 2, 4]
    increments = [(cycle[(i + 1) % 5] - x) % 5 for i, x in enumerate(cycle)]
    assert sorted(cycle) == list(range(5))
    assert increments == [1, 2, 4, 2, 1]
    assert [x for x, d in zip(cycle, increments) if d not in (1, 2)] == [3]
    print(json.dumps({"kind": "independent finite fidelity witnesses",
                      "platonic": graphs, "readings": [reading_check(n) for n in range(2, 10)],
                      "singularities": singularity_checks(),
                      "back_step": {"cycle": cycle, "increments_mod_5": increments,
                                    "unique_back_step": [3, 2]}, "passed": True}, indent=2))


if __name__ == "__main__":
    main()
