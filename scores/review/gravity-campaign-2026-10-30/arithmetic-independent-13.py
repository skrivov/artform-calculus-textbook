"""Independent exact replay of finite responses, anchoring and native cubic pivots."""
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path


def reciprocal(x):
    # Lean's rational division is totalized, including nonpositive precision cases.
    return 1 / x if x else F(0)


def precision(ct, cs, k):
    return 1 + ct * (k & 1) + cs * sum((k >> i) & 1 for i in (1, 2, 3))


def response(ct, cs, axis):
    return sum((reciprocal(precision(ct, cs, k) * precision(ct, cs, k ^ (1 << axis)))
                for k in range(16)), F(0))


def rows(R, a, G, s):
    # Direct arithmetic in the literal rowExpr; no exported coefficient is used.
    t, half = F(103, 2), F(1, 2)
    c, u, b = 1 + t, 1 + R, 2 - 3 * a
    h, D = a * s + b, 3 - s
    d = c * u**2 * (a*a + G) - (1 + t*(2*a - 1)**2 + 4*t*G)
    m = 1 + (2 + 3*t)*R + c*R*R
    v = 1 + c*R
    p, j0 = m*a - v, 1 - u*a
    w = 3*half + a - 3*a*a + s*(a - half - G)
    j, Ub = 1 + s, 2*s + b
    Vb = b*(4*a - 1) + s*(4*a - 2 - 4*G)
    f, g = 2*u*w + Ub - 3*a, Vb - a - 2*R*w
    alpha, beta = 2*R*j - 3*s - 1, 2*u*j + s + 3
    Ce, De = w*p - j*m*G, w*j0 + j*u*G
    Eo, Fo = w*u - j*j0, w*m + j*p
    Ie = Ub*p + t*Vb*j0 + G*s*(m - 3*t*u)
    Je = Vb*p - Ub*j0 + G*s*(3*m + u)
    Ko = Ub*u + Vb*m + s*(j0 - 3*p)
    Lo = t*u*Vb - m*Ub + s*(p + 3*t*j0)
    return [s*D*R*(d*f + 4*t*G*alpha) - 4*h*s*(u*Ce + t*R*De) - 2*R*h*D*Ie,
            s*D*R*(d*g + 4*G*beta) - 4*h*s*(u*De - R*Ce) - 2*R*h*D*Je,
            s*D*R*(d*alpha + 4*f) - 4*h*s*(u*Eo + R*Fo) - 2*R*h*D*Ko,
            s*D*R*(d*beta + 4*t*g) - 4*h*s*(u*Fo - t*R*Eo) - 2*R*h*D*Lo]


def main():
    equal_axis = {}
    for c in [F(-1), F(-1, 2), F(0), F(1), F(3, 2)]:
        rr = [response(c, c, i) for i in range(4)]
        assert len(set(rr)) == 1
        equal_axis[str(c)] = str(rr[0])
    # Every summand has denominator (1+c*m)*(1+c*n). These exact
    # coefficient-pair multisets establish equality for arbitrary rational c.
    symbolic = [sorted(tuple(sorted((k.bit_count(), (k ^ (1 << i)).bit_count())))
                       for k in range(16)) for i in range(4)]
    assert all(terms == symbolic[0] for terms in symbolic)
    rt, rs = response(F(2), F(1), 0), response(F(2), F(1), 1)
    assert (rt, rs, rt - rs) == (F(19, 10), F(34, 15), F(-11, 30))
    C0, C1 = -rt/4, -rs/4
    assert C0 - C1 == F(11, 120)
    assert C0 - C1 - F(16, 10000) - F(9, 100) == F(1, 15000)
    kappa, rho, j = F(1, 101), F(1), F(2, 101)
    a = b = j/(2*rho)
    action = kappa*(b-a)**2/2 - j*(a+b)/2 - j*j/(8*kappa) + rho*(a*a+b*b)/2
    minimum = -j*j/(4*rho) - j*j/(8*kappa)
    assert action == minimum
    # Native example only meets the nonzero-pivot hypothesis; it is not feasible.
    R, a, G = F(1), F(1), F(1, 36)
    nu, const = 5 - 8*a + 6*G, 2*(2 - 3*a)**2
    samples = [rows(R, a, G, s) for s in [F(0), F(1), F(-1), F(2)]]
    coefficients, ell, rem = [], [], []
    for i in range(4):
        c0 = samples[0][i]
        c2 = (samples[1][i] + samples[2][i])/2 - c0
        odd = (samples[1][i] - samples[2][i])/2
        c3 = (samples[3][i] - c0 - 4*c2 - 2*odd)/6
        c1 = odd - c3
        coefficients.append([c0, c1, c2, c3])
        ell.append(c1 - nu*c2 + (nu*nu - const)*c3)
        rem.append(c0 - const*c2 + nu*const*c3)
        # Additional direct evaluations check the same cubic and normal remainder.
        for s in [F(-2), F(1, 3), F(3, 2)]:
            val = sum(coefficients[i][p]*s**p for p in range(4))
            assert val == rows(R, a, G, s)[i]
            normal = s*s + nu*s + const
            assert val - (ell[i]*s + rem[i]) == normal*(c3*s + c2 - nu*c3)
    assert ell[0] != 0
    candidate = -rem[0]/ell[0]
    cleared = rem[0]**2 - nu*rem[0]*ell[0] + const*ell[0]**2
    assert ell[0]**2 * (candidate*candidate + nu*candidate + const) == cleared
    assert cleared != 0
    files = ['Native/R2Defs.lean', 'Native/R2Trace.lean', 'RegulatorDefs.lean',
             'LoopDefs.lean', 'TwoCellDefs.lean', 'PivotAudit.lean']
    base = Path('scores/ArtformScores/GravityBridge')
    result = {'equal_axis_sample_responses': equal_axis, 'anisotropic_responses': [str(rt), str(rs)],
              'symbolic_axis_term_multisets_equal': True,
              'loop_coefficient_gap': str(C0-C1), 'gap_margin_at_window': str(F(1, 15000)),
              'anchored_example_minimum': str(minimum), 'native_ell': list(map(str, ell)),
              'native_remainder': list(map(str, rem)), 'native_first_candidate': str(candidate),
              'native_first_cleared_normal': str(cleared), 'native_feasible_witness': False,
              'source_sha256': {str(base/f): hashlib.sha256((base/f).read_bytes()).hexdigest() for f in files}}
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
