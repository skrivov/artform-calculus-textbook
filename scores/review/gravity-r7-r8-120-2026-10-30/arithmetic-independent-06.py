"""Independent original-matrix and exact complex-rational metric-cut audit."""
from fractions import Fraction as Q
from itertools import combinations_with_replacement
from pathlib import Path
import hashlib
import importlib.util
import json


class Gaussian:
    def __init__(self, a=0, b=0):
        if isinstance(a, Gaussian):
            self.a, self.b = a.a, a.b
        else:
            self.a, self.b = Q(a), Q(b)
    def __add__(self, z):
        z = Gaussian(z)
        return Gaussian(self.a+z.a, self.b+z.b)
    __radd__ = __add__
    def __neg__(self):
        return Gaussian(-self.a, -self.b)
    def __sub__(self, z):
        return self+-Gaussian(z)
    def __rsub__(self, z):
        return Gaussian(z)+-self
    def __mul__(self, z):
        z = Gaussian(z)
        return Gaussian(self.a*z.a-self.b*z.b, self.a*z.b+self.b*z.a)
    __rmul__ = __mul__
    def __truediv__(self, z):
        z = Gaussian(z)
        d = z.a*z.a+z.b*z.b
        assert d != 0
        return self*Gaussian(z.a/d, -z.b/d)
    def __rtruediv__(self, z):
        return Gaussian(z)/self
    def __eq__(self, z):
        z = Gaussian(z)
        return self.a == z.a and self.b == z.b
    def conjugate(self):
        return Gaussian(self.a, -self.b)
    def __repr__(self):
        return f'({self.a},{self.b})'


I = Gaussian(0, 1)
base = Path(__file__).parent
spec = importlib.util.spec_from_file_location('original_matrix_action', base/'arithmetic-independent-03.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
kappa, A, g, E = Q(1, 101), Q(101, 103), Q(101, 97), Q(202, 9991)
Hd, D, beta = Q(9999, 9991), Q(10201, 10300), Q(-2422, 29973)


def va(x, y): return [a+b for a, b in zip(x, y)]
def vs(x, y): return [a-b for a, b in zip(x, y)]
def sv(a, x): return [a*z for z in x]
def dot(x, y): return sum(a*b for a, b in zip(x, y))
def outer(x, y): return [[a*b for b in y] for a in x]
def sm(a, M): return [sv(a, r) for r in M]
def ma(X, Y): return [va(x, y) for x, y in zip(X, Y)]
def ms(X, Y): return ma(X, sm(-1, Y))
def eye(n): return [[Q(i == j) for j in range(n)] for i in range(n)]
def tr(M): return sum(M[i][i] for i in range(len(M)))
def mv(M, x): return [dot(r, x) for r in M]
def mm(X, Y): return [[sum(a*b for a, b in zip(r, c)) for c in zip(*Y)] for r in X]
def transpose(M): return list(map(list, zip(*M)))


def chart(k):
    R = dot(k, k)
    assert R != 0
    P = ms(eye(3), sm(1/R, outer(k, k)))
    def gradient(u): return sm(I, ma(outer(k, u), outer(u, k)))
    def scalar(M): return (tr(M)-dot(k, mv(M, k))/R)/2
    def coulomb(M): return sv(1/(I*R), vs(mv(M, k), sv(dot(k, mv(M, k))/(2*R), k)))
    def tt(M): return ms(ms(M, sm(scalar(M), P)), gradient(coulomb(M)))
    def compose(q, s, u): return ma(ma(q, sm(s, P)), gradient(u))
    def organize(x):
        M, Mt, shift, lapse, shift_t, lapse_t = x
        momentum = sv(Q(1, 2), va(vs(sv(R, shift), sv(dot(k, shift), k)),
                                    sv(I, vs(mv(Mt, k), sv(tr(Mt), k)))))
        return [tt(M), tt(Mt), coulomb(M), coulomb(Mt),
                (dot(k, shift)-dot(k, coulomb(Mt)))/(I*R), lapse,
                shift_t, lapse_t, R*scalar(M), momentum]
    def reconstruct(z):
        q, qt, u, velocity, chi0, lapse, shift_t, lapse_t, H, momentum = z
        return [compose(q, H/R, u), compose(qt, I*dot(k, momentum)/R, velocity),
                va(va(sv(2/R, vs(momentum, sv(dot(k, momentum)/R, k))), velocity), sv(I*chi0, k)),
                lapse, shift_t, lapse_t]
    return R, P, organize, reconstruct


def main():
    basis_checks = 0
    for k in [[Gaussian(1), Gaussian(2), Gaussian(3)], [Gaussian(1), I, Gaussian(2)]]:
        R, P, organize, reconstruct = chart(k)
        for slot in range(20):
            data, cursor = [], 0
            for _ in range(2):
                M = [[Gaussian() for _ in range(3)] for _ in range(3)]
                for i, j in combinations_with_replacement(range(3), 2):
                    M[i][j] = M[j][i] = Gaussian(slot == cursor)
                    cursor += 1
                data.append(M)
            for n in [3, 1, 3, 1]:
                values = [Gaussian(slot == cursor+j) for j in range(n)]
                cursor += n
                data.append(values if n == 3 else values[0])
            z = organize(data)
            assert reconstruct(z) == data and organize(reconstruct(z)) == z
            for q in z[:2]:
                assert q == transpose(q) and tr(q) == 0 and mv(q, k) == [0]*3
            basis_checks += 1
        J = [Gaussian(2), Gaussian(-1), Gaussian(4)]
        normal = lambda c: [Q(-101, 20600)*R*c[0], sv(beta, va(sv(-R, c[1]), sv(dot(k, c[1]), k)))]
        rhs = normal([Gaussian(3), J])
        lift = [rhs[0]/(Q(-101, 20600)*R), va(sv(-1/(beta*R), rhs[1]), sv(2, k))]
        assert dot(k, rhs[1]) == 0 and normal(lift) == rhs
        assert normal([Gaussian(), k]) == [0, [0]*3] and dot(k, k) != 0
    assert dot([Gaussian(1), I, Gaussian()], [Gaussian(1), I, Gaussian()]) == 0
    # Literal original physical columns; native coefficient A=-omega.
    C, v, w = [[Q(-1), Q(-1), Q(0)], [Q(1), Q(0), Q(-1)], [Q(0), Q(1), Q(-1)]], [Q(1), Q(1), Q(-1)], [Q(1), Q(-1), Q(-1)]
    def physical(z):
        return [m.scale(z[0], m.wedge(m.unit(1), m.unit(2))),
                m.scale(z[1], m.wedge(m.unit(0), m.unit(2))),
                m.scale(z[2], m.wedge(m.unit(0), m.unit(1))), m.zero]
    for z in [[Q(1), Q(2), Q(3)], [Q(-2, 7), Q(5, 11), Q(13, 17)]]:
        omega = physical(z)
        native = [m.scale(-1, X) for X in omega]
        theta = lambda i, j, a: -native[i][a][j]+native[j][a][i]
        assert [theta(0, 1, 2), theta(0, 2, 1), theta(1, 2, 0)] == mv(C, z)
        density = m.bilinear(lambda _: (m.zero, native), lambda _: (m.zero, native), 1, [0]*4, Q(0))
        assert density == z[0]*z[1]-z[0]*z[2]-z[1]*z[2]
    Bc, Bci = ms(outer(v, v), eye(3)), ma(sm(-1, eye(3)), sm(Q(1, 2), outer(v, v)))
    N0, H0 = ma(sm(Q(-103, 101), eye(3)), sm(2*kappa, outer(w, w))), ms(sm(-A, eye(3)), sm(E, outer(w, w)))
    assert mm(Bc, Bci) == mm(Bci, Bc) == eye(3)
    assert mm(N0, H0) == mm(H0, N0) == eye(3)
    assert ma(sm(-1, eye(3)), sm(2*kappa, mm(mm(C, Bci), transpose(C)))) == N0
    def jets(l, p, q):
        link = [[x/2 if i == j else Q(0) for j, x in enumerate([l, p, q])] for i in range(3)]
        N1 = sm(2*kappa, mm(mm(C, ms(mm(link, Bci), mm(Bci, link))), transpose(C)))
        N2 = sm(-2*kappa, mm(mm(mm(mm(C, link), Bci), link), transpose(C)))
        L = [-l-p, l+q, p+q]
        expected = ms(sm(kappa/2, ma(ma(sm(l*l, outer([-1, 1, 0], [-1, 1, 0])),
                    sm(p*p, outer([-1, 0, 1], [-1, 0, 1]))), sm(q*q, outer([0, -1, -1], [0, -1, -1])))), sm(kappa/4, outer(L, L)))
        assert N2 == expected
        H1 = sm(-1, mm(mm(H0, N1), H0))
        H2 = ms(mm(mm(mm(mm(H0, N1), H0), N1), H0), mm(mm(H0, N2), H0))
        assert H1 == sm(kappa*g*A, [[0, p-q, l-q], [q-p, 0, p-l], [q-l, l-p, 0]])
        assert ma(mm(N0, H1), mm(N1, H0)) == sm(0, eye(3))
        assert ma(ma(mm(N0, H2), mm(N1, H1)), mm(N2, H0)) == sm(0, eye(3))
        return H2
    for args in [(Q(1), Q(2), Q(3)), (Q(-2), Q(5, 7), Q(11, 13))]: jets(*args)
    H200, H020, H002 = jets(Q(1), Q(0), Q(0)), jets(Q(0), Q(1), Q(0)), jets(Q(0), Q(0), Q(1))
    contact = kappa*kappa*A*A*g
    assert mv(H200, [Q(3), Q(-2), Q(0)])[2] == 5*contact
    assert mv(ms(ms(jets(Q(1), Q(1), Q(0)), H200), H020), [Q(1), Q(1), Q(0)])[2] == contact
    assert mv(ms(ms(jets(Q(1), Q(0), Q(1)), H200), H002), [Q(1), Q(1), Q(0)])[2] == -contact
    raw, top = kappa*(Hd+(kappa*A*A+E)*(Hd-D)/Hd)/12, kappa**4*g*g*A*A/(4*beta)
    assert raw+top > kappa/24 and top < 0
    rho, u = Gaussian(2, 1), [Gaussian(1, 2), Gaussian(-2, 3), Gaussian(4, -1)]
    b = sv(-I*kappa*kappa*g*A*rho/2, u)
    assert dot(b, sv(-1/(beta*rho*rho), b)) == top*dot(u, u)
    real_b = sv(-I*kappa*kappa*g*A/2, [Q(1), Q(-2), Q(3)])
    assert dot([x.conjugate() for x in real_b], sv(-1/beta, real_b)) == -14*top
    k = [Q(1), Q(2), Q(3)]
    angular = mv(ms(eye(3), sm(1/dot(k, k), outer(k, k))), [x*x for x in k])
    assert dot(angular, angular) == Q(38, 7) and dot(k, angular) == 0
    files = [base/'arithmetic-independent-03.py', base/'arithmetic-independent-01.py']
    files += [Path('scores/ArtformScores/GravityBridge/Native')/f for f in
              ['MetricCut/CoordinatesDefs.lean', 'MetricCut/LeadingDefs.lean', 'MetricCut/QuarticDefs.lean', 'InverseJets/SignedDefs.lean']]
    print(json.dumps({'exact_complex_rational_symmetric_Cauchy_basis_roundtrips': basis_checks,
        'nonreal_nonisotropic_chart_tested': True, 'complex_isotropic_R_guard_retained': True,
        'leading_normal_lift_kernel_and_range_samples': True, 'original_physical_torsion_and_curvature_signs': True,
        'both_zero_order_inverses_and_ordered_N1_N2_H1_H2': True,
        'three_H2_temporal_mixed_contacts': str(contact), 'quartic_raw_constant': str(raw),
        'quartic_bilinear_top_return': str(top), 'quartic_complete_constant': str(raw+top),
        'Hermitian_substitution_changes_sign': True, 'angular_square_123': '38/7',
        'native_Taylor_or_physical_transfer_claim': False,
        'source_sha256': {str(f.relative_to(Path.cwd()) if f.is_absolute() else f): hashlib.sha256(f.read_bytes()).hexdigest() for f in files}}, indent=2))


if __name__ == '__main__':
    main()
