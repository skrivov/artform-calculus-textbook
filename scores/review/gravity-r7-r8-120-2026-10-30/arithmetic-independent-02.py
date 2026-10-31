"""Exact independent checks of guarded native inversion and source normalizations."""
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path

C = [[F(0), F(-1), F(-1)], [F(-1), F(0), F(1)], [F(-1), F(1), F(0)]]
T = [[F(-1), F(1), F(0)], [F(1), F(0), F(-1)], [F(0), F(-1), F(-1)]]
I = [[F(i == j) for j in range(3)] for i in range(3)]


def add(a, b):
    return [[x+y for x, y in zip(r, s)] for r, s in zip(a, b)]


def scale(c, a):
    return [[c*x for x in r] for r in a]


def mul(a, b):
    return [[sum(a[i][k]*b[k][j] for k in range(3)) for j in range(3)] for i in range(3)]


def mv(a, x):
    return [sum(u*v for u, v in zip(row, x)) for row in a]


def dot(x, y):
    return sum(u*v for u, v in zip(x, y))


def determinant(a):
    return (a[0][0]*(a[1][1]*a[2][2]-a[1][2]*a[2][1])
            -a[0][1]*(a[1][0]*a[2][2]-a[1][2]*a[2][0])
            +a[0][2]*(a[1][0]*a[2][1]-a[1][1]*a[2][0]))


def block(t):
    return add(scale(1-2*t, C), scale(-4*t, I))


def action(t, z, x):
    return -2*t*z*z+dot(x, mv(block(t), x))/2+2*t*dot(x, [0, -z, z])


def main():
    assert mul(C, C) == add(C, scale(2, I))
    assert mul(mul(list(map(list, zip(*T))), scale(-1, I)), T) == scale(-1, add(C, scale(2, I)))
    samples = []
    for t in [F(0), F(1, 101), F(1, 4), F(-1, 2), F(1, 3), F(-2)]:
        den = 2*(1-4*t)*(1+2*t)
        numerator = add(scale(6*t-1, I), scale(1-2*t, C))
        b = block(t)
        assert mul(b, numerator) == mul(numerator, b) == scale(den, I)
        assert determinant(b) == 2*(1-4*t)*(1+2*t)**2
        if den:
            inv = scale(1/den, numerator)
            assert mul(b, inv) == mul(inv, b) == I
        for z in [F(0), F(1), F(3, 7)]:
            r = [0, -z, z]
            cc = [2*t*x for x in r]
            assert mv(C, r) == [-x for x in r]
            assert [u+2*t*v for u, v in zip(mv(C, cc), r)] == [0, 0, 0]
            assert [u+2*t*v for u, v in zip(mv(b, cc), r)] == [-4*t*t*x for x in r]
            if 1+2*t:
                cb = [2*t*x/(1+2*t) for x in r]
                assert [u+2*t*v for u, v in zip(mv(b, cb), r)] == [0, 0, 0]
                assert action(t, z, cb) == -2*t*z*z/(1+2*t)
                assert action(t, z, cc)-action(t, z, cb) == -16*t**4*z*z/(1+2*t)
        samples.append({'t': str(t), 'inverse_denominator': str(den), 'determinant': str(determinant(b))})
    kappa = F(1, 101)
    inv = scale(1/(2*(1-4*kappa)*(1+2*kappa)), add(scale(6*kappa-1, I), scale(1-2*kappa, C)))
    assert inv == scale(F(1, 19982), add(scale(9999, C), scale(-9595, I)))
    cb = [0, F(-2, 103), F(2, 103)]
    assert action(kappa, F(1), cb) == F(-2, 103)
    # The original nonzero eliminated source is indispensable in the Schur toy.
    A, B, Ctoy, D, E, u, v, f, a = map(F, [2, 1, 1, 2, '1/2', 4, 5, 1, 2])
    assert D*E == E*D == 1 and A*f+B*a == u and Ctoy*f+D*a == v
    assert (A-B*E*Ctoy)*f == u-B*E*v and a == E*(v-Ctoy*f)
    assert E*(-Ctoy*f) != a
    # Complement orientations are epsilon^(ijkl), with increasing complementary i,j.
    faces = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    comp, signs = [], []
    for k, l in faces:
        i, j = [a for a in range(4) if a not in (k, l)]
        perm = [i, j, k, l]
        parity = sum(perm[a] > perm[b] for a in range(4) for b in range(a+1, 4))
        comp.append([i, j]); signs.append((-1)**parity)
    assert comp == [[2, 3], [1, 3], [1, 2], [0, 3], [0, 2], [0, 1]]
    assert signs == [1, -1, 1, 1, -1, 1]
    base = Path('scores/ArtformScores/GravityBridge/Native')
    files = [base/'Defs.lean', base/'PreparationDefs.lean',
             base/'Full40/QuadraticDefs.lean', base/'Full40/ForceDefs.lean']
    print(json.dumps({'parameter_samples': samples, 'native_preparation': list(map(str, cb)),
                      'native_effective_density': '-2/103',
                      'native_curvature_only_action_error': str(-16*kappa**4/(1+2*kappa)),
                      'complementary_pairs': comp, 'complementary_signs': signs,
                      'full_source_schur_example': True,
                      'efficiency_benchmark': False,
                      'source_sha256': {str(f): hashlib.sha256(f.read_bytes()).hexdigest() for f in files}}, indent=2))


if __name__ == '__main__':
    main()
