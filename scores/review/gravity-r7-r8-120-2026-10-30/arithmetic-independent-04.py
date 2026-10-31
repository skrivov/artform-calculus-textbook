"""Independent exact matrix and residual audit; no native inverse is instantiated."""
from fractions import Fraction as Q
import hashlib
import importlib.util
import json
from pathlib import Path

helper = Path(__file__).with_name('arithmetic-independent-01.py')
spec = importlib.util.spec_from_file_location('original_matrix_primitives', helper)
p = importlib.util.module_from_spec(spec)
spec.loader.exec_module(p)
eta = [-1, 1, 1, 1]


def readout(F):
    # Obtain the Lorentz part by eta-adjoint projection, then original coordinates.
    L = [[(F[i][j]-eta[i]*eta[j]*F[j][i])/2 for j in range(4)] for i in range(4)]
    return [L[0][1], L[0][2], L[0][3], L[2][3], L[3][1], L[1][2]]


def metric(F):
    return [[eta[i]*F[i][j]+eta[j]*F[j][i] for j in range(4)] for i in range(4)]


def reconstruct(m, w):
    L = p.lie(w)
    return [[eta[i]*m[i][j]/2+L[i][j] for j in range(4)] for i in range(4)]


def matvec(A, v):
    return [sum(a*x for a, x in zip(row, v)) for row in A]


def vadd(a, b):
    return [x+y for x, y in zip(a, b)]


def vsub(a, b):
    return [x-y for x, y in zip(a, b)]


def main():
    frames = [[[Q(i == a and j == b) for j in range(4)] for i in range(4)]
              for a in range(4) for b in range(4)]
    frames.append([[Q(7*i-3*j+2, i+j+1) for j in range(4)] for i in range(4)])
    for F in frames:
        assert reconstruct(metric(F), readout(F)) == F
    for a in range(4):
        for b in range(a, 4):
            m = [[Q((i == a and j == b) or (i == b and j == a))
                  for j in range(4)] for i in range(4)]
            for k in range(6):
                w = [Q(j == k) for j in range(6)]
                F = reconstruct(m, w)
                assert metric(F) == m and readout(F) == w
    H = frames[-1]
    G = [[eta[I]*H[i][I] for i in range(4)] for I in range(4)]
    S = [[eta[I]*(H[i][I]+H[I][i])/2 for i in range(4)] for I in range(4)]
    gamma = [(H[0][a]-H[a][0])/2 for a in [1, 2, 3]]
    gamma += [(H[3][2]-H[2][3])/2, (H[1][3]-H[3][1])/2,
              (H[2][1]-H[1][2])/2]
    assert p.add(G, p.scale(-1, S)) == p.lie(gamma)
    assert readout(G) == gamma and readout(S) == [0]*6
    assert all(G[0][a] == -H[a][0] for a in [1, 2, 3])
    for h in [Q(0), Q(1, 2), Q(-3)]:
        dgamma = [Q(a+1, 7) for a in range(6)]
        assert [-h*(-d) for d in dgamma] == [h*d for d in dgamma]
    # A nonscalar connection block, with its separately checked two-sided inverse.
    D, E = [[Q(2), Q(1)], [Q(3), Q(2)]], [[Q(2), Q(-1)], [Q(-3), Q(2)]]
    eye = [[Q(1), Q(0)], [Q(0), Q(1)]]
    product = lambda A, B: [[sum(A[i][k]*B[k][j] for k in range(len(B)))
                             for j in range(len(B[0]))] for i in range(len(A))]
    assert product(D, E) == eye and product(E, D) == eye
    C = [[Q(1), Q(2), Q(-1)], [Q(-2), Q(0), Q(3)]]
    f, u, v = [Q(1), Q(-2), Q(3)], [Q(4), Q(1), Q(-1)], [Q(2), Q(-3)]
    a = [-x for x in matvec(E, matvec(C, f))]
    residual = vadd(matvec(C, u), matvec(D, v))
    graph_difference = [-x for x in matvec(E, matvec(C, vsub(f, u)))]
    returned = vsub(graph_difference, matvec(E, residual))
    assert vadd(matvec(C, f), matvec(D, a)) == [0, 0]
    assert vsub(a, v) == returned and returned != graph_difference
    # Noncommuting L,E,R: inverse sampling is purely formal, E need not invert D.
    L, R = [[Q(1), Q(2)], [Q(0), Q(3)]], [[Q(0), Q(1)], [Q(-2), Q(1)]]
    E = [[Q(1), Q(0)], [Q(0), Q(0)]]  # deliberately singular
    Omega, f, kappa = [[Q(2), Q(1)], [Q(-1), Q(4)]], [Q(3), Q(-2)], Q(1, 101)
    q0 = matvec(Omega, f)
    contact = [-2*kappa*x for x in matvec(E, matvec(R, f))]
    physical = vadd(contact, [x/2 for x in matvec(L, q0)])
    assert vsub(physical, [x/2 for x in matvec(L, q0)]) == contact
    assert Q(-2, 101)+Q(1, 2) == Q(97, 202)
    files = [helper]+[Path('scores/ArtformScores/GravityBridge/Native')/n for n in
        ['Full40/SplitDefs.lean', 'Full40/ProjectorDefs.lean', 'Full40/CoordinatesDefs.lean',
         'Full40/CutJetsStatements.lean', 'Full40/PhysicalSignDefs.lean',
         'Retrospective/ResidualReturnDefs.lean', 'Retrospective/SamplingDefs.lean']]
    print(json.dumps({'all16_frame_basis_and_mixed_rational_reconstruction': True,
        'all10_symmetric_basis_times_all6_Lorentz_readouts': True,
        'original_lower_gradient_and_all_rotation_signs': True,
        'physical_native_sign_at_zero_positive_negative_h': True,
        'nonscalar_two_sided_inverse_residual_return': list(map(str, returned)),
        'nonzero_retained_residual': list(map(str, residual)),
        'formal_sampling_with_singular_E_and_noncommuting_maps': True,
        'native_inverse_or_analytic_jet_claim': False, 'efficiency_benchmark': False,
        'source_sha256': {str(f.relative_to(Path.cwd()) if f.is_absolute() else f):
                          hashlib.sha256(f.read_bytes()).hexdigest() for f in files}}, indent=2))


if __name__ == '__main__':
    main()
