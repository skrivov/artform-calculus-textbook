"""Distinct exact incidence, full native cell and derivative replay (stdlib only)."""
from fractions import Fraction as F
from itertools import combinations,product
from pathlib import Path
import hashlib,json
BASE=Path('scores/review/gravity-r7-r8-120-2026-10-30')

class Jet:
    # Taylor coefficients at0, including the actual quadratic coefficient.
    def __init__(self,a=0,b=0,c=0):
        self.v=a.v if isinstance(a,Jet) else (F(a),F(b),F(c))
    def __add__(a,b):
        b=Jet(b);return Jet(*(x+y for x,y in zip(a.v,b.v)))
    __radd__=__add__
    def __neg__(a):return Jet(*(-x for x in a.v))
    def __sub__(a,b):return a+-Jet(b)
    def __rsub__(a,b):return Jet(b)+-a
    def __mul__(a,b):
        b=Jet(b);return Jet(*(sum(a.v[i]*b.v[n-i] for i in range(n+1)) for n in range(3)))
    __rmul__=__mul__
    def inv(a):
        x,y,z=a.v;assert x
        return Jet(1/x,-y/(x*x),y*y/(x*x*x)-z/(x*x))
    def __truediv__(a,b):return a*Jet(b).inv()
    def __rtruediv__(a,b):return Jet(b)*a.inv()
    def __bool__(a):return bool(a.v[0])
    def __eq__(a,b):return a.v==Jet(b).v

def eye(n):return [[F(i==j) for j in range(n)] for i in range(n)]
def mm(a,b):return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]
def mv(a,b):return [sum(x*y for x,y in zip(row,b)) for row in a]
def tr(a):return [list(r) for r in zip(*a)]
def sub(a,b):return [[x-y for x,y in zip(r,s)] for r,s in zip(a,b)]
def scale(c,a):return [[c*x for x in r] for r in a]
def inverse(a):
    n=len(a);rows=[r[:]+e for r,e in zip(a,eye(n))]
    for col in range(n):
        pivot=next(r for r in range(col,n) if rows[r][col])
        rows[col],rows[pivot]=rows[pivot],rows[col]
        divisor=rows[col][col];rows[col]=[v/divisor for v in rows[col]]
        for r in range(n):
            if r!=col:
                v=rows[r][col];rows[r]=[x-v*y for x,y in zip(rows[r],rows[col])]
    return [r[n:] for r in rows]
def determinant(a):
    rows=[r[:] for r in a];out=F(1)
    for col in range(len(a)):
        pivot=next(r for r in range(col,len(a)) if rows[r][col])
        if pivot!=col:rows[col],rows[pivot]=rows[pivot],rows[col];out=-out
        divisor=rows[col][col];out*=divisor
        for r in range(col+1,len(a)):
            v=rows[r][col]/divisor
            rows[r]=[x-v*y for x,y in zip(rows[r],rows[col])]
    return out
eta=[-1,1,1,1];metric=[[F(eta[i]*(i==j)) for j in range(4)] for i in range(4)]
bivs=[(0,1),(0,2),(0,3),(2,3),(3,1),(1,2)];faces=list(combinations(range(4),2));kap=F(1,101)
def wedge(a,b):return [a[i]*b[j]-a[j]*b[i] for i,j in bivs]
def star(a):return [-a[3],-a[4],-a[5],a[0],a[1],a[2]]
def pair(a,b):return sum(eta[i]*eta[j]*x*y for (i,j),x,y in zip(bivs,a,b))
def boost(q):
    a=eye(4);a[0][0]=a[1][1]=(q+1/q)/2;a[0][1]=a[1][0]=(q-1/q)/2
    return a
def eps(p):return (-1)**sum(p[i]>p[j] for i in range(4) for j in range(i+1,4))
def literal_cell(h,b,q0,q1):
    E=[[v*int(i==j) for j in range(4)] for i,v in enumerate([h,F(1),b,F(1)])]
    columns=tr(E)
    def U(i,site):return boost(q0 if site[0]==0 else q1) if i==1 else eye(4)
    root=[0]*4;curvature=F(0)
    for i,l in faces:
        xi=[int(k==i) for k in range(4)];xl=[int(k==l) for k in range(4)]
        ui,ul,uil,uli=U(i,root),U(l,root),U(i,xl),U(l,xi)
        H=mm(mm(mm(inverse(ul),inverse(uil)),uli),ui)
        rev=mm(mm(mm(inverse(ui),inverse(uli)),uil),ul)
        assert mm(H,rev)==eye(4)==mm(rev,H)
        assert inverse(H)==rev
        K=scale(F(-1,2),sub(H,inverse(H)))
        kc=[K[r][s] for r,s in bivs]
        a,d=[x for x in range(4) if x not in (i,l)]
        paths=[eye(4),ui,ul,mm(uli,ui),mm(uil,ul)]
        mean=[F(0)]*6
        for w,path in zip([F(1,4)]*3+[F(1,8)]*2,paths):
            value=wedge(mv(inverse(path),columns[a]),mv(inverse(path),columns[d]))
            mean=[x+eps([a,d,i,l])*w*y for x,y in zip(mean,value)]
        curvature+=pair(mean,star(kc))
    inv_links=[inverse(U(i,root)) for i in range(4)]
    theta={(i,l):[x-y-z+w for x,y,z,w in zip(mv(inv_links[i],columns[l]),columns[l],mv(inv_links[l],columns[i]),columns[i])] for i,l in product(range(4),repeat=2)}
    g=mm(mm(tr(E),metric),E);gi=inverse(g)
    assert mm(g,gi)==eye(4)==mm(gi,g)
    density=determinant(E)/2*sum(gi[i][k]*gi[l][m]*sum(eta[r]*theta[i,l][r]*theta[k,m][r] for r in range(4)) for i,l,k,m in product(range(4),repeat=4))
    c0,s0=(q0+1/q0)/2,(q0-1/q0)/2
    sf=(q1/q0-q0/q1)/2
    assert curvature==-b*sf and density==-2*h*b*(c0-1)
    return curvature+kap*density

# Incidence independently encoded by alternating vertex/interval coordinates.
def cells(lengths):return list(product(*(range(2*n+1) for n in lengths)))
def dim(x):return sum(a%2 for a in x)
def boundary(x):
    out={};axes=[i for i,a in enumerate(x) if a%2]
    for p,i in enumerate(axes):
        for side in [-1,1]:
            y=list(x);y[i]+=side;y=tuple(y)
            out[y]=out.get(y,0)+side*(-1)**p
    return out
ns={'__file__':str(BASE/'source/actual-curved-cube-producer.py')}
exec((BASE/'source/actual-curved-cube-producer.py').read_text().split('geometry=[]')[0],ns)
incidence=0
for lengths,expected in [([1]*4,[16,32,24,8,1]),([2,1,1,1],[24,52,42,15,2])]:
    canvas=cells(lengths);assert [sum(dim(x)==k for x in canvas) for k in range(5)]==expected
    original=ns['cells'](lengths)
    for k,layer in enumerate(original):
        encoded={tuple(2*start[i]+int(i in dirs) for i in range(4)) for dirs,start in [(x['directions'],x['start']) for x in layer]}
        assert encoded=={x for x in canvas if dim(x)==k}
    for x in canvas:
        twice={}
        for y,sgn in boundary(x).items():
            assert y in canvas and dim(y)==dim(x)-1
            for z,t in boundary(y).items():twice[z]=twice.get(z,0)+sgn*t
        assert not any(twice.values());incidence+=1
left,right=(1,1,1,1),(3,1,1,1);seam=(2,1,1,1)
assert boundary(left)[seam]==1 and boundary(right)[seam]==-1

# Full six-face/two-metric contraction, preserving actual based words.
full_cases=0
for h,b,q0,q1 in product([F(1),F(1,2),F(2,7)],[F(1),F(4,3)],[F(1),F(101,100)],[F(6,5),F(2)]):
    literal_cell(h,b,q0,q1);full_cases+=1
# A forward endpoint lacking the Lorentz guard invalidates the sign-reversed inverse.
bad=[[F(2),F(0),F(0),F(0)],[F(0),F(2),F(0),F(0)],[F(0),F(0),F(1),F(0)],[F(0),F(0),F(0),F(1)]]
assert mm(bad,bad)!=eye(4) and inverse(bad)!=bad

# Literal matrix differentiation by exact Taylor jets, including varying coframe inverse.
jet_cases=0;stationary=0;uniform=0
for q in [F(101,100),F(6,5),F(2),F(3)]:
    c,s=(q+1/q)/2,(q-1/q)/2;A,B=2*s+kap*c,kap*s;D=A*A-B*B
    assert D==4*s*s+4*kap*s*c+kap*kap>kap*kap
    assert (kap+2*c*s)**2-D==4*s**4>0
    assert 1/(q*q)<(A-B)/(A+B)<1 # exp(2*r*) lies between exp(-2u) and1.
    assert A*(-B)+B*A==0 and A*A+B*(-B)==D
    for z in [F(9,10),F(1),F(11,10)]:
        C,S=(z+1/z)/2,(z-1/z)/2
        fine=literal_cell(F(1,2),F(1),F(1),q*z)+literal_cell(F(1,2),F(1),q*z,q*q)
        assert fine==kap-A*C-B*S
        # r varies as log(z)+epsilon, with all original cells differentiated.
        mid=Jet(q*z,q*z,q*z/2)
        fj=literal_cell(F(1,2),F(1),F(1),mid)+literal_cell(F(1,2),F(1),mid,q*q)
        assert fj.v==(fine,-(A*S+B*C),-(A*C+B*S)/2)
        # Retained coframe source; differentiates det and both metric inverses too.
        bj=Jet(1,1,0)
        fb=literal_cell(F(1,2),bj,F(1),q*z)+literal_cell(F(1,2),bj,q*z,q*q)
        assert fb.v==(fine,fine,F(0))
        if z==1:
            for jsource in [F(-2,3),F(0),F(4,7)]:
                sourced=fj-Jet(0,jsource,0)
                assert sourced.v[1]==-kap*s-jsource and sourced.v[2]==-(2*s+kap*c)/2
        jet_cases+=2
    coarse=literal_cell(F(1),F(1),F(1),q*q)
    symmetric=literal_cell(F(1,2),F(1),F(1),q)+literal_cell(F(1,2),F(1),q,q*q)
    assert symmetric-coarse==(c-1)*(2*s-kap)
    stationary+=1
    # Uniform chain: exact phase/edge incidence and actual-cell derivative.
    for N in [2,3,5]:
        for k in range(1,N):
            phase=[Jet(q**i,q**i if i==k else 0,q**i/2 if i==k else 0) for i in range(N+1)]
            action=sum(literal_cell(F(1,N),F(1),phase[i],phase[i+1]) for i in range(N))
            target=-2*kap/F(N)*(q**k-q**(-k))/2
            assert phase[0]==1 and phase[-1]==q**N
            assert action.v[1]==target<0
            uniform+=1
assert literal_cell(F(1,2),F(1),F(1),F(2))+literal_cell(F(1,2),F(1),F(2),F(4))-literal_cell(F(1),F(1),F(1),F(4))==F(301,808)
files=['source-pins.json','source/actual-curved-cube-parent.md','source/actual-curved-cube-producer.py','source/original-nonlinear-torsion.md','source/original-transported-curvature.md']
print(json.dumps({'status':'passed','independent_incidence_cells':incidence,'oriented_boundary_squared_zero':True,'internal_shared_facet_cancels':True,'literal_six_face_full_cell_cases':full_cases,'exact_literal_rapidity_and_coframe_second_jets':jet_cases,'source_contacts_retained':True,'guardless_reverse_inverse_rejected':True,'stationary_discriminant_merge_and_rapidity_interval_cases':stationary,'literal_uniform_interior_derivatives':uniform,'native_q2_defect':'301/808','new_native_physical_gate':0,'efficiency_credit':0,'source_sha256':{str(BASE/f):hashlib.sha256((BASE/f).read_bytes()).hexdigest() for f in files}},sort_keys=True))
