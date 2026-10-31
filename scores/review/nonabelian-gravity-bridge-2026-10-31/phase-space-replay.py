"""Exact rational SU(2) tangent probes, not a global symplectic proof."""
from dataclasses import dataclass
from fractions import Fraction as F
import json
ZERO = (F(0),) * 4
ONE = (F(1), F(0), F(0), F(0))
SRC = (0, 1, 4, 3, 1, 2, 5)
TGT = (1, 4, 3, 0, 2, 5, 4)
FACES = (((0, True), (1, True), (2, True), (3, True)), ((4, True), (5, True), (6, True), (1, False)))
STARS = (((0, False), (3, True)), ((4, False), (1, False), (0, True)), ((5, False), (4, True)), ((3, False), (2, True)), ((2, False), (1, True), (6, True)), ((6, False), (5, True)))

def add(a, b):
    return tuple((x + y for x, y in zip(a, b)))

def neg(a):
    return tuple((-x for x in a))

def mul(a, b):
    w, x, y, z = a
    v, p, q, r = b
    return (w * v - x * p - y * q - z * r, w * p + x * v + y * r - z * q, w * q - x * r + y * v + z * p, w * r + x * q - y * p + z * v)

def inv(a):
    return (a[0], -a[1], -a[2], -a[3])

@dataclass(frozen=True)
class Jet:
    q: tuple
    x: tuple = ZERO
    y: tuple = ZERO

    def __mul__(self, b):
        return Jet(mul(self.q, b.q), add(mul(self.x, b.q), mul(self.q, b.x)), add(mul(self.y, b.q), mul(self.q, b.y)))

    def inverse(self):
        a = inv(self.q)
        return Jet(a, neg(mul(mul(a, self.x), a)), neg(mul(mul(a, self.y), a)))

    def left(self):
        return (mul(inv(self.q), self.x), mul(inv(self.q), self.y))

    def right(self):
        return (mul(self.x, inv(self.q)), mul(self.y, inv(self.q)))

def prod(xs):
    a = Jet(ONE)
    for x in xs:
        a = a * x
    return a

def outgoing(s, e):
    u, p = s
    return u[e].inverse() * p[e].inverse() * u[e]

def moments(s):
    return [prod((s[1][e] if incoming else outgoing(s, e) for e, incoming in star)) for star in STARS]

def holonomy(s, f, i):
    u, _ = s
    word = FACES[f]
    word = word[i + 1:] + word[:i + 1]
    return prod((u[e] if positive else u[e].inverse() for e, positive in reversed(word)))

def kick(s, f, back=False):
    u, p = s
    p = list(p)
    for i, (e, positive) in enumerate(FACES[f]):
        k = holonomy(s, f, i)
        if back:
            k = k.inverse()
        if positive:
            p[e] = k * p[e]
        else:
            p[e] = p[e] * u[e] * k.inverse() * u[e].inverse()
    return (list(u), p)

def drift(s, back=False):
    u, p = s
    return ([(p[e].inverse() if back else p[e]) * u[e] for e in range(7)], list(p))

def wedge(a, b):
    return sum((a[0][i] * b[1][i] - a[1][i] * b[0][i] for i in range(1, 4)))

def omega(s):
    u, p = s
    value = F(0)
    for e in range(7):
        a = u[e]
        b = u[e].inverse() * p[e]
        value += (wedge(a.left(), b.right()) + wedge(a.right(), b.left())) / 2
    for star in STARS:
        cur = Jet(ONE)
        for e, incoming in star:
            m = p[e] if incoming else outgoing(s, e)
            value += wedge(cur.left(), m.right()) / 2
            cur = cur * m
    return value

def body_jet(point, x, y):
    arrays = []
    for k, qs in enumerate(point):
        arrays.append([Jet(q, mul(q, (F(0), *x[k * 21 + e * 3:k * 21 + e * 3 + 3])), mul(q, (F(0), *y[k * 21 + e * 3:k * 21 + e * 3 + 3]))) for e, q in enumerate(qs)])
    return tuple(arrays)

def nullspace(a):
    a = [list(row) for row in a]
    m = len(a)
    n = len(a[0])
    piv = []
    r = 0
    for c in range(n):
        k = next((k for k in range(r, m) if a[k][c]), None)
        if k is None:
            continue
        a[r], a[k] = (a[k], a[r])
        d = a[r][c]
        a[r] = [x / d for x in a[r]]
        for i in range(m):
            if i != r and a[i][c]:
                t = a[i][c]
                a[i] = [x - t * y for x, y in zip(a[i], a[r])]
        piv.append(c)
        r += 1
        if r == m:
            break
    basis = []
    for c in range(n):
        if c in piv:
            continue
        v = [F(0)] * n
        v[c] = F(1)
        for i, j in enumerate(piv):
            v[j] = -a[i][c]
        basis.append(v)
    return (piv, basis)

def constraint_basis(point):
    columns = []
    z = [F(0)] * 42
    for j in range(42):
        v = list(z)
        v[j] = F(1)
        ms = moments(body_jet(point, v, z))
        assert all((m.q == ONE and m.x[0] == 0 for m in ms))
        columns.append([t for m in ms for t in m.x[1:]])
    return nullspace(list(map(list, zip(*columns))))

def vertical(point, v, i):
    tau = tuple((F(j == i + 1) for j in range(4)))
    u, p = point
    out = []
    for k, qs in enumerate(point):
        for e, q in enumerate(qs):
            if k == 0:
                dq = add(mul(tau, q) if TGT[e] == v else ZERO, neg(mul(q, tau)) if SRC[e] == v else ZERO)
            else:
                dq = add(mul(tau, q), neg(mul(q, tau))) if TGT[e] == v else ZERO
            body = mul(inv(q), dq)
            assert body[0] == 0
            out.extend(body[1:])
    return out

def main():
    r = (F(3, 5), F(4, 5), F(0), F(0))
    t = (F(5, 13), F(0), F(12, 13), F(0))
    point = ([ONE, ONE, ONE, r, ONE, ONE, t], [ONE] * 7)
    points = [point]
    z = [F(0)] * 42
    moved = drift(kick(kick(body_jet(point, z, z), 0), 1))
    points.append(tuple([[j.q for j in qs] for qs in moved]))
    results = []
    for index, point in enumerate(points):
        piv, basis = constraint_basis(point)
        assert len(piv) == 18
        gauges = [vertical(point, v, i) for v in range(6) for i in range(3)]
        gauge_errors = []
        defects = []
        form_matrix = [[F(0)] * len(basis) for _ in basis]
        for x in basis:
            for g in gauges:
                value = omega(body_jet(point, x, g))
                if value:
                    gauge_errors.append(str(value))
        for i, x in enumerate(basis):
            for j, y in enumerate(basis[i + 1:], i + 1):
                s = body_jet(point, x, y)
                before = omega(s)
                form_matrix[i][j] = before
                form_matrix[j][i] = -before
                for name, after in [('face0', kick(s, 0)), ('face1', kick(s, 1)), ('drift', drift(s))]:
                    value = omega(after) - before
                    if value:
                        defects.append({'map': name, 'basis_i': i, 'basis_j': j, 'defect': str(value)})
                        if len(defects) >= 3:
                            break
                if len(defects) >= 3:
                    break
            if len(defects) >= 3:
                break
        form_rank = len(nullspace(form_matrix)[0])
        assert form_rank == 6
        gauge_rank = len(nullspace(list(map(list, zip(*gauges))))[0])
        assert gauge_rank == 18
        results.append({'gauge_rank': gauge_rank, 'restricted_two_form_rank': form_rank, 'point': index, 'constraint_rank': len(piv), 'constraint_tangent_dimension': len(basis), 'gauge_null_errors': gauge_errors[:3], 'pullback_defects': defects})
        print(json.dumps({'probe_completed': index, 'result': results[-1]}), flush=True)
    print(json.dumps({'scope': 'exact rational unit-quaternion tangent probes at two Gauss-admitted regular points; not a global pullback theorem', 'results': results}, indent=2))
if __name__ == '__main__':
    main()
