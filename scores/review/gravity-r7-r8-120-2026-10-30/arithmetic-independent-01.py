"""Independent exact finite checks of source signs and noncommuting contacts."""
from fractions import Fraction as Q
from itertools import product
import hashlib
import json
from pathlib import Path


def add(a, b):
    return [[x+y for x, y in zip(r, s)] for r, s in zip(a, b)]


def scale(c, a):
    return [[c*x for x in row] for row in a]


def mul(a, b):
    return [[sum(a[i][k]*b[k][j] for k in range(4))
             for j in range(4)] for i in range(4)]


def comm(a, b):
    return add(mul(a, b), scale(-1, mul(b, a)))


def lie(a):
    return [[Q(0), a[0], a[1], a[2]],
            [a[0], Q(0), a[5], -a[4]],
            [a[1], -a[5], Q(0), a[3]],
            [a[2], a[4], -a[3], Q(0)]]


def jet_mul(a, b):
    return [sum_matrices(mul(a[i], b[n-i]) for i in range(n+1)) for n in range(3)]


def sum_matrices(matrices):
    result = [[Q(0)]*4 for _ in range(4)]
    for m in matrices:
        result = add(result, m)
    return result


def main():
    units = [[Q(i == j) for i in range(6)] for j in range(6)]
    basis = list(map(lie, units))
    zero = [[Q(0)]*4 for _ in range(4)]
    identity = [[Q(i == j) for j in range(4)] for i in range(4)]
    eta = [-1, 1, 1, 1]
    signs = [-1]*3+[1]*3
    gram_entries = 0
    for i, a in enumerate(basis):
        for j, b in enumerate(basis):
            pair = -sum(mul(a, b)[k][k] for k in range(4))/2
            assert pair == (signs[i] if i == j else 0)
            gram_entries += 1
        assert all(eta[p]*a[p][q]+eta[q]*a[q][p] == 0
                   for p in range(4) for q in range(4))
    star = lambda a: [-a[3], -a[4], -a[5], a[0], a[1], a[2]]
    for a in units:
        assert star(star(a)) == [-x for x in a]
        for b in units:
            assert sum(signs[i]*star(a)[i]*b[i] for i in range(6)) == sum(
                signs[i]*a[i]*star(b)[i] for i in range(6))
    # Original ordered word: -Al,-SlAk,SkAl,Ak. All four values differ.
    Al, SlAk, SkAl, Ak = basis[0], basis[1], basis[2], basis[4]
    letters = [scale(-1, Al), scale(-1, SlAk), SkAl, Ak]
    jets = [[identity, x, scale(Q(1, 2), mul(x, x))] for x in letters]
    jet = [identity, zero, zero]
    for j in jets:
        jet = jet_mul(jet, j)
    inv = [identity, scale(-1, jet[1]), add(mul(jet[1], jet[1]), scale(-1, jet[2]))]
    assert jet_mul(jet, inv) == jet_mul(inv, jet) == [identity, zero, zero]
    reading = [scale(Q(-1, 2), add(jet[i], scale(-1, inv[i]))) for i in range(3)]
    ordered_comm = sum_matrices(comm(letters[i], letters[j])
                               for i in range(4) for j in range(i+1, 4))
    assert reading[2] == scale(Q(-1, 2), ordered_comm)
    assert reading[1] == add(add(SlAk, scale(-1, Ak)), add(Al, scale(-1, SkAl)))
    assert comm(basis[0], basis[1])[1][2] == 1
    assert comm(basis[1], basis[0])[1][2] == -1
    # First-order complement, with distinct path contacts and equal corner field.
    F0, Fk, Fl, Fkl, C = basis[0], basis[1], basis[2], basis[3], basis[5]
    values = [F0, add(Fk, scale(-1, comm(Ak, C))),
              add(Fl, scale(-1, comm(Al, C))),
              add(Fkl, scale(-1, comm(add(Ak, SkAl), C))),
              add(Fkl, scale(-1, comm(add(Al, SlAk), C)))]
    five = sum_matrices(scale(w, f) for w, f in zip(
        [Q(1, 4)]*3+[Q(1, 8)]*2, values))
    V = scale(Q(1, 8), sum_matrices([scale(3, Ak), SlAk, scale(3, Al), SkAl]))
    mean = scale(Q(1, 4), sum_matrices([F0, Fk, Fl, Fkl]))
    assert five == add(mean, scale(-1, comm(V, C)))
    grid = list(product(range(3), repeat=4))
    shift = lambda x, i, a: tuple((x[j]+(a if j == i else 0)) % 3 for j in range(4))
    f = lambda x: Q(sum((i+1)*v*v for i, v in enumerate(x)))
    g = lambda x: Q(1+x[0]*x[2]+2*x[1]+3*x[3]*x[3])
    for i in range(4):
        assert sum(f(shift(x, i, 1))*g(x) for x in grid) == sum(
            f(x)*g(shift(x, i, -1)) for x in grid)
        for j in range(4):
            x = tuple(2 if k == i else 0 for k in range(4))
            assert int(shift(x, j, 1) == (0, 0, 0, 0)) == int(i == j)
    # Original unordered01 face, internal direction2: negative torsion norm.
    assert Q(1, 101)*eta[0]*eta[1]*eta[2] == Q(-1, 101)
    assert 2*Q(1, 101)*eta[0]*eta[1]*eta[2] == Q(-2, 101)
    base = Path('scores/ArtformScores/GravityBridge/Native/Full40')
    files = [base/(m+'Defs.lean') for m in ['Coordinates','Shifts','Plaquette','Complement','Torsion']]
    print(json.dumps({'gram_entries': gram_entries, 'star_basis_checks': 6,
                      'periodic_sites': len(grid), 'bilinear_shift_checks': 4,
                      'unit_shift_separation_checks': 16,
                      'ordered_inverse_and_contact': True, 'two_diagonal_paths': True,
                      'torsion_unit_density': '-1/101', 'torsion_unit_derivative': '-2/101',
                      'source_sha256': {str(f): hashlib.sha256(f.read_bytes()).hexdigest() for f in files}},
                     indent=2))


if __name__ == '__main__':
    main()
