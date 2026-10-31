"""Independent original-matrix, full24, profile and literal-program replay."""
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import hashlib
import importlib.util
import json
import re

base = Path(__file__).parent
spec = importlib.util.spec_from_file_location('original_action', base/'arithmetic-independent-03.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
eta, zero = [-1, 1, 1, 1], m.zero
kappa = Q(1, 101)
C = [[Q(0), Q(-1), Q(-1)], [Q(-1), Q(0), Q(1)], [Q(-1), Q(1), Q(0)]]
T = [[Q(-1), Q(1), Q(0)], [Q(1), Q(0), Q(-1)], [Q(0), Q(-1), Q(-1)]]


def mm(A, B):
    return [[sum(A[i][k]*B[k][j] for k in range(len(B)))
             for j in range(len(B[0]))] for i in range(len(A))]


def mv(A, v):
    return [sum(a*x for a, x in zip(row, v)) for row in A]


def block(t):
    TT = mm(list(map(list, zip(*T))), T)
    return [[C[i][j]-2*t*TT[i][j] for j in range(3)] for i in range(3)]


def inverse(A):
    n = len(A)
    rows = [row[:]+[Q(i == j) for j in range(n)] for i, row in enumerate(A)]
    for i in range(n):
        k = next(k for k in range(i, n) if rows[k][i])
        rows[i], rows[k] = rows[k], rows[i]
        rows[i] = [x/rows[i][i] for x in rows[i]]
        for j in range(n):
            if j != i:
                a = rows[j][i]
                rows[j] = [x-a*y for x, y in zip(rows[j], rows[i])]
    return [row[n:] for row in rows]


def coordinates(A):
    return [A[0][1], A[0][2], A[0][3], A[2][3], A[3][1], A[1][2]]


def assemble(z):
    A = [zero for _ in range(4)]
    for s, triple in enumerate(combinations(range(4), 3)):
        for j, mu in enumerate(triple):
            w = m.wedge(m.unit(triple[(j+1) % 3]), m.unit(triple[(j+2) % 3]))
            A[mu] = m.add(A[mu], m.scale(z[3*s+j], w))
    for b in range(4):
        for j, mu in enumerate(i for i in range(4) if i != b):
            A[mu] = m.add(A[mu], m.scale(z[12+3*b+j], m.wedge(m.unit(mu), m.unit(b))))
    return A


def extract(A):
    def component(mu, i, j):
        return sum(x*y for x, y in zip(coordinates(m.wedge(m.unit(i), m.unit(j))), coordinates(A[mu])))
    out = [component(mu, triple[(j+1) % 3], triple[(j+2) % 3])
           for triple in combinations(range(4), 3) for j, mu in enumerate(triple)]
    return out+[component(mu, mu, b) for b in range(4) for mu in range(4) if mu != b]


def indexed_density(t, z):
    result = Q(0)
    for s, (a, b, c) in enumerate(combinations(range(4), 3)):
        x, y, w = z[3*s:3*s+3]
        result += 2*t*eta[a]*eta[b]*eta[c]*(x*x+y*y+w*w)
        result -= (1-2*t)*(eta[c]*x*y+eta[b]*x*w+eta[a]*y*w)
    for b in range(4):
        x, y, w = z[12+3*b:15+3*b]
        result += eta[b]*(t*(x*x+y*y+w*w)-x*y-x*w-y*w)
    return result


def parse_program(source, name):
    body = source.split('def '+name+' : List ScalarGate := [', 1)[1].split(']', 1)[0]
    tokens = iter(re.findall(r'\.[A-Za-z]+|-?\d+|/|[()]', body))
    def ref():
        t = next(tokens)
        if t == '(':
            r = ref()
            assert next(tokens) == ')'
            return r
        if t == '.neg':
            return ('neg', ref())
        assert t in ('.input', '.slot')
        return (t[1:], int(next(tokens)))
    gates = []
    for tag in tokens:
        if tag == '.scale':
            assert next(tokens) == '('
            numerator = int(next(tokens))
            assert next(tokens) == '/'
            denominator = int(next(tokens))
            assert next(tokens) == ')'
            gates.append(('scale', Q(numerator, denominator), ref()))
        else:
            assert tag == '.add'
            gates.append(('add', ref(), ref()))
    return gates


def run(program, outputs, z):
    registers = []
    def ref(r):
        if r[0] == 'neg':
            return -ref(r[1])
        if r[0] == 'input':
            assert r[1] < 3
            return z[r[1]]
        assert 0 <= r[1] < len(registers)
        return registers[r[1]]
    for tag, a, b in program:
        registers.append(a*ref(b) if tag == 'scale' else ref(a)+ref(b))
    assert all(j < len(registers) for j in outputs)
    ns = [abs(x.numerator).bit_length() for x in registers]
    ds = [x.denominator.bit_length() for x in registers]
    return [registers[j] for j in outputs], {'max_numerator_bits': max(ns),
        'max_denominator_bits': max(ds), 'sum_register_numerator_denominator_bits': sum(ns)+sum(ds)}


def main():
    inv = inverse(block(kappa))
    r = [Q(0), Q(-1), Q(1)]
    assert mv(inv, r) == [-101*x/103 for x in r]
    contact = [-2*kappa*x for x in mv(inv, r)]
    assert [x-2*kappa*y for x, y in zip(contact, r)] == [-Q(4, 10403)*x for x in r]
    assert mv(block(Q(1, 4)), [Q(1), Q(-1), Q(-1)]) == [0]*3
    assert mv(block(Q(-1, 2)), r) == [0]*3
    assert mv(block(Q(1, 4)), [x/3 for x in r]) == [-x/2 for x in r]
    for b in range(4):
        for t, v in [(Q(1), [Q(1)]*3), (Q(-1, 2), [Q(1), Q(-1), Q(0)])]:
            repeated = [[eta[b]*(2*t if i == j else -1) for j in range(3)] for i in range(3)]
            assert mv(repeated, v) == [0]*3
    R, L = Q(14), Q(-36, 35)
    H = 1/((1+2*kappa)*(1-kappa))
    force = kappa*kappa*R*R*L/(4*(1+2*kappa)*(1-kappa))
    assert H == Q(10201, 10300) and force == Q(-63, 12875)
    assert -force/(kappa*R*H/2) == Q(36, 505)
    for h in [Q(1), Q(1, 10), Q(-2)]:
        for a in [Q(0), Q(4), Q(-3, 7)]:
            c = h**3*a/4
            coefficient = c*(1+h*h)/(h*h)
            g = lambda t: coefficient*t*t/(1+t*t)
            assert g(0) == 0 and g(h) == c
            for t in [Q(0), h, Q(3, 2), Q(-100)]:
                assert abs(g(t)) <= abs(coefficient)
                if h > 0:
                    assert abs(g(t)) <= h*abs(a)*(1+h*h)/4
    basis = [[Q(j == i) for j in range(24)] for i in range(24)]
    connections = [assemble(z) for z in basis]
    assert all(extract(A) == z for A, z in zip(connections, basis))
    # Independently start from all24 original A_mu^(01,02,03,23,31,12) slots.
    for i in range(24):
        A = [m.lie([Q(6*mu+a == i) for a in range(6)]) for mu in range(4)]
        assert assemble(extract(A)) == A
    def mixed(A, B, t):
        q, p = lambda _: (zero, A), lambda _: (zero, B)
        return m.bilinear(q, p, 1, [0]*4, t)
    cross = 0
    for i, j in combinations(range(24), 2):
        if i//3 != j//3:
            for t in [Q(0), kappa]:
                assert mixed(connections[i], connections[j], t)+mixed(connections[j], connections[i], t) == 0
                cross += 1
    for z in [[Q(1)]*12+[Q(2)]*12, [Q(3*i-17, i+1) for i in range(24)]]:
        for t in [Q(0), kappa, Q(1, 4), Q(-1, 2)]:
            A = assemble(z)
            assert mixed(A, A, t) == indexed_density(t, z)
    assert indexed_density(kappa, [Q(1)]*12+[Q(2)]*12) == Q(-3006, 101)
    path = Path('scores/ArtformScores/GravityBridge/Native/Retrospective/BlockProgramsDefs.lean')
    source = path.read_text()
    dense, rank = [parse_program(source, name) for name in ['denseBlockProgram', 'rankBlockProgram']]
    assert [sum(g[0] == 'scale' for g in x) for x in [dense, rank]] == [9, 4]
    assert [sum(g[0] == 'add' for g in x) for x in [dense, rank]] == [6, 5]
    expected = json.loads((base/'program-traces-root-05.json').read_text())
    for row in expected['samples']:
        z = list(map(Q, row['input']))
        d, db = run(dense, [4, 9, 14], z)
        r, rb = run(rank, [6, 7, 8], z)
        assert d == r == mv(inv, z) and list(map(str, d)) == row['output']
        assert db == row['dense'] and rb == row['rank']
    extra = [Q(-5, 7), Q(11, 13), Q(17, 19)]
    assert run(rank, [6, 7, 8], extra)[0] == run(dense, [4, 9, 14], extra)[0] == mv(inv, extra)
    paths = [Path(__file__).with_name('arithmetic-independent-03.py'),
             Path(__file__).with_name('arithmetic-independent-01.py'), path,
             Path('scores/ArtformScores/GravityBridge/Native/Retrospective/HomogeneousDefs.lean'),
             Path('scores/ArtformScores/GravityBridge/Native/Full40/TemporalProfileDefs.lean')]
    print(json.dumps({'original_signed_inverse_and_contact': True,
        'singular_source_solve_and_all_repeated_null_tests': True,
        'supplied_native_force_and_principal_normalization': str(-force/(kappa*R*H/2)),
        'real_profile_endpoint_and_bound_samples': True, 'all24_partition_basis_checks_both_ways': True,
        'cross_block_polarization_checks': cross, 'full24_density_sample': '-3006/101',
        'literal_Lean_programs_parsed_and_all_register_reads_valid': True,
        'root_five_output_and_bit_trace_rows_reproduced': True, 'additional_reviewer_heldout_input': list(map(str, extra)),
        'prospective_gate_counts': {'dense': [9, 6], 'rank': [4, 5]},
        'actual_longitudinal_value_evaluated': False, 'native_physical_or_historical_efficiency_claim': False,
        'source_sha256': {str(f.relative_to(Path.cwd()) if f.is_absolute() else f): hashlib.sha256(f.read_bytes()).hexdigest() for f in paths}}, indent=2))


if __name__ == '__main__':
    main()
