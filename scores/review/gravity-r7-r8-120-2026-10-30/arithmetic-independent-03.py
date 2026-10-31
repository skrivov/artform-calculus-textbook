"""Independent matrix-form replay of periodic Ward, pulse and restriction data."""
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations
import hashlib
import importlib.util
import json
from pathlib import Path

helper = Path(__file__).with_name('arithmetic-independent-01.py')
spec = importlib.util.spec_from_file_location('review_primitives', helper)
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
add, scale, mul, comm, lie = m.add, m.scale, m.mul, m.comm, m.lie
eta = [-1, 1, 1, 1]
zero = [[F(0)]*4 for _ in range(4)]
identity = [[F(i == j) for j in range(4)] for i in range(4)]
faces = list(combinations(range(4), 2))


def sub(a, b):
    return add(a, scale(-1, b))


def summ(matrices):
    return m.sum_matrices(matrices)


def pair(a, b):
    return -sum(mul(a, b)[i][i] for i in range(4))/2


def star(a):
    return lie([-a[2][3], -a[3][1], -a[1][2], a[0][1], a[0][2], a[0][3]])


def wedge(u, v):
    return [[(u[i]*v[j]-u[j]*v[i])*eta[j] for j in range(4)] for i in range(4)]


def unit(i):
    return [F(i == j) for j in range(4)]


def complement(k, l):
    i, j = [a for a in range(4) if a not in (k, l)]
    p = [i, j, k, l]
    sign = (-1)**sum(p[a] > p[b] for a in range(4) for b in range(a+1, 4))
    return i, j, sign, scale(sign, wedge(unit(i), unit(j)))


def bilinear(q, p, size, steps, kappa):
    total = F(0)
    def data(field, x, k, l):
        i, j, sign, C = complement(k, l)
        f, A = field(x)
        fk, Ak = field((x+steps[k]) % size)
        fl, Al = field((x+steps[l]) % size)
        fkl = field((x+steps[k]+steps[l]) % size)[0]
        def fw(g):
            return add(wedge([g[a][i] for a in range(4)], unit(j)),
                       wedge(unit(i), [g[a][j] for a in range(4)]))
        L = scale(F(sign, 4), summ(map(fw, [f, fk, fl, fkl])))
        V = scale(F(1, 8), summ([scale(3, A[k]), Al[k], scale(3, A[l]), Ak[l]]))
        LU = sub(L, comm(V, C))
        K = sub(sub(Al[k], A[k]), sub(Ak[l], A[l]))
        theta = [fk[a][l]-f[a][l]-fl[a][k]+f[a][k]-A[k][a][l]+A[l][a][k]
                 for a in range(4)]
        letters = [scale(-1, A[l]), scale(-1, Al[k]), Ak[l], A[k]]
        return LU, K, theta, letters
    for x in range(size):
        for k, l in faces:
            C = complement(k, l)[3]
            Lq, Kq, tq, X = data(q, x, k, l)
            Lp, Kp, tp, Y = data(p, x, k, l)
            raw = scale(F(-1, 2), summ(comm(X[a], Y[b]) for a in range(4) for b in range(a+1, 4)))
            total += pair(Lq, star(Kp))+pair(C, star(raw))
            total += kappa*eta[k]*eta[l]*sum(eta[a]*tq[a]*tp[a] for a in range(4))
    return total


def main():
    size, steps, kappa = 17, [1, 2, 4, 8], F(1, 101)
    pulse = lambda x: (identity if x == 0 else zero, [zero]*4)
    def delta(n):
        @lru_cache(None)
        def field(x):
            f = [[F(x == 0 and n == 4*i+j) for j in range(4)] for i in range(4)]
            A = [lie([F(x == 0 and n == 16+6*i+a) for a in range(6)]) for i in range(4)]
            return f, A
        return field
    action = bilinear(pulse, pulse, size, steps, kappa)
    tests = [bilinear(pulse, delta(n), size, steps, kappa)+
             bilinear(delta(n), pulse, size, steps, kappa) for n in [0, 16, 39]]
    assert action == F(12, 101) and tests == [F(12, 101), F(-2, 101), F(0)]
    @lru_cache(None)
    def q(x):
        return ([[F((x+2*a+3*i) % 5-2) for i in range(4)] for a in range(4)],
                [lie([F((3*x+2*i+a) % 5-2) for a in range(6)]) for i in range(4)])
    @lru_cache(None)
    def w(x):
        return lie([F((x+a) % 3-1) for a in range(6)])
    @lru_cache(None)
    def R(x):
        return w(x), [sub(w((x+d) % size), w(x)) for d in steps]
    mixed = bilinear(q, R, size, steps, kappa)+bilinear(R, q, size, steps, kappa)
    assert mixed == 0
    values = [F(1), F(2), F(-3)]
    restrictions = []
    for triple in combinations(range(4), 3):
        A = [zero for _ in range(4)]
        for j, i in enumerate(triple):
            A[i] = scale(values[j], wedge(unit(triple[(j+1) % 3]), unit(triple[(j+2) % 3])))
        field = lambda x: (zero, A)
        a, b, c = triple
        expected = 2*kappa*eta[a]*eta[b]*eta[c]*sum(v*v for v in values)-(1-2*kappa)*(
            eta[c]*values[0]*values[1]+eta[b]*values[0]*values[2]+eta[a]*values[1]*values[2])
        actual = bilinear(field, field, 1, [0]*4, kappa)
        assert actual == expected
        restrictions.append(str(actual))
    for b in range(4):
        A = [zero for _ in range(4)]
        for a, z in zip([i for i in range(4) if i != b], values):
            A[a] = scale(z, wedge(unit(a), unit(b)))
        field = lambda x: (zero, A)
        actual = bilinear(field, field, 1, [0]*4, kappa)
        expected = eta[b]*(kappa*sum(z*z for z in values)-sum(values[i]*values[j] for i in range(3) for j in range(i+1, 3)))
        assert actual == expected
        restrictions.append(str(actual))
    for D in [F(2), F(-2)]:
        f, u, v, B, A, E = F(1), F(4), F(5), F(1), F(3), 1/D
        returned = E*(v-B*f)
        effective = A*f*f/2-u*f-(v-B*f)*E*(v-B*f)/2
        for a in [F(-2), F(2), F(3)]:
            full = A*f*f/2+B*f*a+D*a*a/2-u*f-v*a
            assert full == effective+D*(a-returned)**2/2
        if D == 2:
            assert returned == 2 and effective == F(-13, 2)
    files = [helper]+[Path('scores/ArtformScores/GravityBridge/Native')/p for p in
        ['Full40/QuadraticDefs.lean','Full40/WardDefs.lean','Full40/FourDirectionDefs.lean',
         'Retrospective/IndexedBlocksDefs.lean','Retrospective/SourceActionDefs.lean']]
    print(json.dumps({'cyclic_sites': size, 'steps': steps, 'Cartesian_independence_claim': False,
                      'pulse_action': str(action), 'pulse_variations': list(map(str, tests)),
                      'mixed_Ward_matrix_replay': str(mixed), 'eight_restriction_samples': restrictions,
                      'source_action_positive_and_indefinite_completion': True,
                      'full24_block_diagonalization_claim': False, 'efficiency_benchmark': False,
                      'source_sha256': {str(f.relative_to(Path.cwd()) if f.is_absolute() else f):
                                        hashlib.sha256(f.read_bytes()).hexdigest() for f in files}}, indent=2))


if __name__ == '__main__':
    main()
