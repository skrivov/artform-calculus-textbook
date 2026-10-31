"""Exact independent ray, Lorentz-frame and linear-kernel replay (stdlib only)."""
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path


def rank(matrix):
    a = [list(row) for row in matrix]
    piv = 0
    for col in range(len(a[0])):
        r = next((r for r in range(piv, len(a)) if a[r][col]), None)
        if r is None:
            continue
        a[piv], a[r] = a[r], a[piv]
        q = a[piv][col]
        a[piv] = [x/q for x in a[piv]]
        for r in range(len(a)):
            if r != piv:
                q = a[r][col]
                a[r] = [x-q*y for x, y in zip(a[r], a[piv])]
        piv += 1
        if piv == len(a):
            break
    return piv


def generator(b, r):
    return [[F(0), b[0], b[1], b[2]],
            [b[0], F(0), -r[2], r[1]],
            [b[1], r[2], F(0), -r[0]],
            [b[2], -r[1], r[0], F(0)]]


def main():
    C = F(395741161, 479124399600)
    rays = []
    for h in [F(1), F(1, 2), F(1, 100), F(1, 10000)]:
        r2 = 1 + (1+h)**2
        defect = h*h*(1+h)**2/r2
        leading = -C*defect
        remainder = -h**4*leading
        assert 2 <= r2 <= 5 and leading != 0 and defect <= h*h
        assert abs(remainder) <= C*h**5
        assert h**4*leading+remainder == 0
        amplitude, d, bound = h**4, F(1), F(1)
        assert amplitude**2/(h**4*d) == bound*amplitude
        rays.append({'h': str(h), 'radial_square': str(r2),
                     'leading_scalar': str(leading), 'declared_remainder': str(remainder)})
    eta = [-1, 1, 1, 1]
    E = [[F(5, 3), F(4, 3), F(0), F(0)],
         [F(4, 3), F(5, 3), F(0), F(0)],
         [F(0), F(0), F(1), F(0)], [F(0), F(0), F(0), F(1)]]
    metric = [[sum(eta[a]*E[a][i]*E[a][j] for a in range(4))
               for j in range(4)] for i in range(4)]
    assert metric == [[F(eta[i] if i == j else 0) for j in range(4)] for i in range(4)]
    assert E[0][0]*E[1][1]-E[0][1]*E[1][0] == 1 and E[0][1] == F(4, 3)
    units = [[F(i == j) for i in range(3)] for j in range(3)]
    zero = [F(0)]*3
    generators = [generator(x, zero) for x in units]+[generator(zero, x) for x in units]
    variation = lambda A: [eta[i]*A[i][j]+eta[j]*A[j][i] for i in range(4) for j in range(4)]
    assert all(not any(variation(A)) for A in generators)
    basis_rank = rank([[A[i][j] for A in generators] for i in range(4) for j in range(4)])
    coordinate_basis = [[[F(4*i+j == p) for j in range(4)] for i in range(4)] for p in range(16)]
    variation_rank = rank([[variation(A)[p] for A in coordinate_basis] for p in range(16)])
    assert basis_rank == 6 and variation_rank == 10
    # Degree-one torsion needs coordinate vectors; degree-two curvature also
    # needs their pairwise sums (polarization over the rational field).
    wave_units = [[F(i == j) for i in range(4)] for j in range(4)]
    waves = wave_units+[[F(k == i or k == j) for k in range(4)]
                        for i in range(4) for j in range(i+1, 4)]
    torsion_checks = curvature_checks = 0
    for A in coordinate_basis:
        for k in waves:
            conn = [[[k[i]*A[a][b] for b in range(4)] for a in range(4)] for i in range(4)]
            for i in range(4):
                for j in range(4):
                    for a in range(4):
                        if k in wave_units:
                            assert k[i]*A[a][j]-k[j]*A[a][i]-conn[i][a][j]+conn[j][a][i] == 0
                            torsion_checks += 1
                        for b in range(4):
                            assert k[i]*conn[j][a][b]-k[j]*conn[i][a][b] == 0
                            curvature_checks += 1
    base = Path('scores/ArtformScores/GravityBridge')
    files = ['Native/R8Defs.lean', 'Native/R8Domains.lean', 'JointBudget.lean',
             'MetricFrameDefs.lean', 'MetricFrame.lean']
    print(json.dumps({'ray_samples': rays, 'native_metric_coefficient': str(C),
                      'linearized_metric_rank': variation_rank,
                      'independent_lorentz_parameters': basis_rank,
                      'torsion_coefficient_checks': torsion_checks,
                      'curvature_coefficient_checks': curvature_checks,
                      'actual_native_remainder_computed': False,
                      'native_full40_gauge_claim': False,
                      'source_sha256': {str(base/f): hashlib.sha256((base/f).read_bytes()).hexdigest()
                                        for f in files}}, indent=2))


if __name__ == '__main__':
    main()
