"""Independent coupled linear solve, direct Q/F13 recipes and contact audit."""
from fractions import Fraction as Q
from pathlib import Path
from itertools import zip_longest
import hashlib
import importlib.util
import json
import re

base = Path(__file__).parent
spec = importlib.util.spec_from_file_location('matrix_checks', base/'arithmetic-independent-06.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)


class F13:
    def __init__(self, n):
        self.n = n.n if isinstance(n, F13) else int(n) % 13
    def __add__(self, z): return F13(self.n+F13(z).n)
    __radd__ = __add__
    def __neg__(self): return F13(-self.n)
    def __sub__(self, z): return self+-F13(z)
    def __rsub__(self, z): return F13(z)+-self
    def __mul__(self, z): return F13(self.n*F13(z).n)
    __rmul__ = __mul__
    def __truediv__(self, z):
        z = F13(z)
        assert z.n != 0
        return F13(self.n*pow(z.n, -1, 13))
    def __rtruediv__(self, z): return F13(z)/self
    def __eq__(self, z): return self.n == F13(z).n
    def __repr__(self): return str(self.n)


def solve(A, b):
    rows = [r[:]+[x] for r, x in zip(A, b)]
    n = len(rows)
    for i in range(n):
        pivot = next(j for j in range(i, n) if rows[j][i] != 0)
        rows[i], rows[pivot] = rows[pivot], rows[i]
        d = rows[i][i]
        rows[i] = [x/d for x in rows[i]]
        for j in range(n):
            if j != i:
                a = rows[j][i]
                rows[j] = [x-a*y for x, y in zip(rows[j], rows[i])]
    return [r[-1] for r in rows]


def recipe(field):
    S = lambda n, d=1: field(n)/field(d)
    kap, a, g, e, hd, dd = [S(n, d) for n, d in [(1,101),(101,103),(101,97),(202,9991),(9999,9991),(10201,10300)]]
    bp, b3, b = S(101,39964), S(1,19982), S(-10201,20600)
    cv = b3+S(2,82400)
    k = [1,2,3]
    U = [S(x,103)+2*S(y,9991)-S(z,20600) for x,y,z in zip([31,2582,-1419],[98,2716,-1218],[2059,3314,3765])]
    K = [[hd*S(i == j)+(dd-hd)*S(k[i]*k[j],14) for j in range(3)] for i in range(3)]
    w1y = [18*(hd+dd)*x+7*(dd-hd)*x*x for x in k]
    w2y = [18*(hd+dd)*x*x+49*(dd-hd)*x for x in k]
    w1c, w2c = -S(7056,5)*kap*b, (1876*hd-18144*kap*b)/5
    gamma = (1/dd-1/hd)*S(18,7)
    A = [r+[S(0)]*4 for r in K]
    rhs = [S(101,490)*u for u in U]
    A += [w1y+[7*dd,S(0),S(0),S(0)],
          [x/hd+gamma*y for x,y in zip(w2y,w1y)]+[S(0),S(7),S(0),S(0)],
          [S(10300,707)*cv*(14*x*x-36*x) for x in k]+[S(0),S(0),S(1),S(0)],
          [-202/hd*S(38,7)*cv*x for x in k]+[S(0),S(0),S(-36),S(14)]]
    rhs += [-w1c, -w2c/hd-gamma*w1c, S(-297,505), -202/hd*S(5332,5)*b3]
    y0,y1,y2,p1,p2,n1,n2 = sol = solve(A,rhs)
    assert m.mv(A,sol) == rhs
    y = [y0,y1,y2]
    M1,M2,M3 = [sum(x**n*z for x,z in zip(k,y)) for n in [1,2,3]]
    B,C,Dm,Rz = 14*p2-36*p1,-36*M2+98*M1,-14*M3+98*M1,14*n2-36*n1
    H = B-Dm
    a5,c4 = kap*a*a/12,kap*kap*a*a*g*g/2
    bc4 = (1-4*kap)*c4
    full = kap*kap*g*a*H/2-kap*e*Rz/2
    groups = [-full/6+S(1092,5)*b3-36*kap*(hd+e)*b3,
              S(3752,5)*kap*kap*g*a*bp,kap*kap*a*a*Rz/12,
              kap*((341*a5+2935*bc4)/5+S(6211,120)*e)-kap*((a5+e/24)*B+(-a5+bc4+e/24)*C+(c4-e/24)*Dm)/2]
    assert hd != 0 and dd != 0
    return sol,groups,sum(groups),sum(groups)-kap*e*Rz/12


def pa(a,b): return [x+y for x,y in zip_longest(a,b,fillvalue=Q(0))]
def ps(c,a): return [c*x for x in a]
def pm(a,b):
    out = [Q(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): out[i+j] += x*y
    while len(out)>1 and out[-1] == 0: out.pop()
    return out


def pair_polynomials(p,q,c0,ci,cj):
    L,L3 = [Q(0),Q(1)],[Q(0),Q(0),Q(0),Q(1)]
    ni,nj,M = [p*c0,ci],[q*c0,cj],[p*cj+q*ci]
    first = [ps(Q(1,2),pa(pa(pm(L,M),ps(p,nj)),ps(-q,ni))),
             ps(Q(1,2),pa(pa(pm(L,M),ps(q,ni)),ps(-p,nj))),
             ps(Q(-1,2),pa(pa(ps(p,nj),ps(q,ni)),ps(-1,pm(L,M))))]
    third = [ps(Q(1,12),pa(pa(pm(L3,M),ps(p**3,nj)),ps(-q**3,ni))),
             ps(Q(1,12),pa(pa(pm(L3,M),ps(q**3,ni)),ps(-p**3,nj))),
             ps(Q(-1,12),pa(pa(ps(p**3,nj),ps(q**3,ni)),ps(-1,pm(L3,M))))]
    d1,d3 = [[-p,1],[-q,1],[p-q]], [[-p**3,0,0,1],[-q**3,0,0,1],[p**3-q**3]]
    Z1 = [ps(Q(1,2),pm(d,f)) for d,f in zip(d1,first)]
    Z3 = [pa(ps(Q(1,2),pm(d,t)),ps(Q(-1,24),pm(c,f))) for d,t,c,f in zip(d1,third,d3,first)]
    assert all(len(z)<=3 for z in Z1) and all(len(z)<=5 for z in Z3)
    coeff = lambda z,n: z[n] if len(z)>n else Q(0)
    assert [coeff(z,2) for z in Z1] == [p*cj/2,q*ci/2,0]
    assert [coeff(z,4) for z in Z3] == [q*ci/24,p*cj/24,0]


def main():
    sol,groups,total,omitted = recipe(Q)
    fsol,fgroups,ftotal,_ = recipe(F13)
    expected = json.loads((base/'source-recipe-root-07.json').read_text())
    assert list(map(str,groups)) == expected['group_values'] and str(total) == expected['total_value']
    assert [x.n for x in fgroups] == [0,3,3,9] and ftotal.n == 2
    assert [x.n for x in fsol[:3]] == [5,7,12] and [x.n for x in fsol[3:]] == [1,0,8,12]
    assert omitted != total
    defs = Path('scores/ArtformScores/GravityBridge/Native/LongitudinalRecipe/ValueDefs.lean')
    denominators = list(map(int,re.findall(r'\d+',defs.read_text().split('def denominatorSites')[1])))
    assert all(n and n%13 for n in denominators)
    for args in [(2,3,5,7,11),(Q(2,7),Q(-3,11),Q(5,13),Q(7,17),Q(-11,19))]: pair_polynomials(*map(Q,args))
    # Both mixed orderings survive in the third inverse on noncommuting matrices.
    N1,N2 = [[Q(0),Q(1)],[Q(0),Q(0)]],[[Q(0),Q(0)],[Q(1),Q(0)]]
    assert m.mm(N1,N2) != m.mm(N2,N1)
    H1,H2,H3 = m.sm(-1,N1),m.sm(-1,N2),m.ma(m.mm(N1,N2),m.mm(N2,N1))
    assert H3 == m.eye(2)
    assert m.ma(m.ma(H3,m.mm(N1,H2)),m.mm(N2,H1)) == m.sm(0,m.eye(2))
    assert m.ma(m.ma(H3,m.mm(H2,N1)),m.mm(H1,N2)) == m.sm(0,m.eye(2))
    # Arbitrary complete electric arrays cancel before selecting a physical field.
    kap,a,g = Q(1,101),Q(101,103),Q(101,97)
    d,e,et,c = [Q(2),Q(-3),Q(5)],[[Q(2*i-j,7) for j in range(3)] for i in range(3)],[[Q(i+3*j,11) for j in range(3)] for i in range(3)],[Q(7),Q(-11),Q(13)]
    faces = [[0,c[0],c[1]],[-c[0],0,c[2]],[-c[1],-c[2],0]]
    normal = [-kap/2*(sum(d[i]*(et[i][a]-d[i]*e[i][a]) for i in range(3))-sum(d[b]*(et[a][b]-d[a]*e[a][b]) for b in range(3))-sum((d[a]-d[j])*d[j]*faces[a][j] for j in range(3))) for a in range(3)]
    primary = lambda d,c: kap*sum((d[i]-d[j])*d[i]*d[j]*v for i,j,v in [(0,1,c[0]),(0,2,c[1]),(1,2,c[2])])
    assert m.dot(d,normal) == primary(d,c)
    d,J = m.sv(m.I,[1,2,3]), m.sv(14*Q(101,39964)/35,[1,-68,45])
    curl = [d[0]*J[1]-d[1]*J[0],d[0]*J[2]-d[2]*J[0],d[1]*J[2]-d[2]*J[1]]
    assert m.dot(d,J) == 0 and primary(d,m.sv(-kap*g*a,curl)) == groups[1]
    Cstar = Q(395741161,479124399600)
    d4 = -Q(38,7)*Cstar
    ci = total/(56*d4)
    assert ci != 0 and d4 != 0
    h = Q(1,2)
    assert abs(h*h*ci) == h*h*abs(ci) and -h*h*h*ci != 0
    # At equality in the budget an error can cancel the leading term.
    assert (m.I+-m.I) == 0  # h=1,c=i,error=-i,M=1: strict inequality fails.
    paths = [base/'arithmetic-independent-06.py',base/'arithmetic-independent-03.py',base/'arithmetic-independent-01.py',defs]
    paths += [Path('scores/ArtformScores/GravityBridge/Native')/p for p in ['SelectedJets/RecurrencesDefs.lean','InverseJets/ThirdDefs.lean','InverseJets/NormalPairDefs.lean','NormalDivergence/PhysicalDefs.lean','LongitudinalRecipe/ContactDefs.lean']]
    print(json.dumps({'independent7by7_coupled_linear_solves':['Q','F13'],'all_denominator_sites_checked':len(denominators),
        'Q_group_values':list(map(str,groups)),'Q_total':str(total),'F13_groups':[x.n for x in fgroups],'F13_total':ftotal.n,
        'omitting_full_third_source_contact_changes_value':True,'bounded_degree_Z1_Z3_polynomial_construction':True,
        'noncommuting_third_inverse_both_coefficient_directions':True,'whole_electric_cancellation_and_supplied_physical_group':True,
        'reference_d4':str(d4),'reference_boost_imaginary_part':str(ci),'strict_error_budget_needed':True,
        'actual_full40_functional_or_uniform_M_identified':False,
        'source_sha256':{str(p.relative_to(Path.cwd()) if p.is_absolute() else p):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},indent=2))


if __name__ == '__main__':
    main()
