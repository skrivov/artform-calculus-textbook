"""Original cubical incidence, full transported curvature and ordered torsion replay.

Load the exact old producer's definitions only. Never execute its receipt tail;
its old curvature sign and optional volume term are not the current action.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations, product
import hashlib
import json
import math
rdir = Path(__file__).resolve().parent
ns = {"__file__":str(rdir/"source/actual-curved-cube-producer.py")}
exec((rdir/'source/actual-curved-cube-producer.py').read_text().split('geometry=[]')[0], ns)
eye, mm, inv = (ns[x] for x in ['eye', 'mm', 'inv'])
eta = [-1, 1, 1, 1]
biv = [(0,1),(0,2),(0,3),(2,3),(3,1),(1,2)]
faces = list(combinations(range(4),2))
complement = [(2,3,1),(1,3,-1),(1,2,1),(0,3,1),(0,2,-1),(0,1,1)]
kappa = F(1,101)
def boost(q):
    c, s = (q+1/q)/2, (q-1/q)/2
    B = eye(4); B[0][0] = B[1][1] = c; B[0][1] = B[1][0] = s
    return B

def mv(A,v): return [sum(x*y for x,y in zip(row,v)) for row in A]
def sub(A,B): return [[x-y for x,y in zip(a,b)] for a,b in zip(A,B)]
def wedge(x,y): return [x[i]*y[j]-x[j]*y[i] for i,j in biv]
def addv(x,y): return [a+b for a,b in zip(x,y)]
def scalev(a,x): return [a*v for v in x]
def star(x): return [-x[3],-x[4],-x[5],x[0],x[1],x[2]]
def pair(x,y): return sum(eta[i]*eta[j]*a*b for (i,j),a,b in zip(biv,x,y))
def chain(*matrices):
    A = eye(4)
    for B in matrices: A = mm(A,B)
    return A

def literal_cell(h,b,q0,q1):
    E = [h,F(1),b,F(1)]
    columns = [[E[i]*int(i==j) for i in range(4)] for j in range(4)]
    def U(axis,forward=False): return boost(q1 if forward else q0) if axis==1 else eye(4)
    def V(axis,forward=False): return inv(U(axis,forward))
    curvature = F(0); word_count = 0
    for (i,l),(ci,cl,sign) in zip(faces,complement):
        H = chain(V(l),V(i,l==0),U(l,i==0),U(i))
        HR = chain(V(i),V(l,i==0),U(i,l==0),U(l))
        assert mm(H,HR)==eye(4)==mm(HR,H)
        K = [[-v/2 for v in row] for row in sub(H,HR)]
        f = [K[i][j] for i,j in biv]
        transports = [eye(4),V(i),V(l),mm(V(i),V(l,i==0)),mm(V(l),V(i,l==0))]
        mean = [F(0)]*6
        for weight,P in zip([F(1,4)]*3+[F(1,8)]*2,transports):
            mean = addv(mean,scalev(sign*weight,wedge(mv(P,columns[ci]),mv(P,columns[cl]))))
        curvature += pair(mean,star(f)); word_count += 1
    theta = {}
    for i,l in product(range(4),repeat=2):
        theta[i,l] = [x-y-z+w for x,y,z,w in zip(mv(V(i),columns[l]),columns[l],mv(V(l),columns[i]),columns[i])]
    gi = [F(eta[i],1)/(E[i]*E[i]) for i in range(4)]
    torsion = F(0)
    for i,j,k,l in product(range(4),repeat=4):
        # Literal inverse metric is diagonal: retain the complete ordered loop.
        gik = gi[i] if i==k else F(0); gjl = gi[j] if j==l else F(0)
        torsion += gik*gjl*sum(eta[a]*theta[i,j][a]*theta[k,l][a] for a in range(4))
    torsion *= h*b/2
    c0,s0 = (q0+1/q0)/2,(q0-1/q0)/2
    cf,sf = (q1/q0+q0/q1)/2,(q1/q0-q0/q1)/2
    assert curvature == -b*sf
    assert torsion == -2*h*b*(c0-1)
    assert theta[0,1] == [h*(1-c0),h*s0,F(0),F(0)]
    assert theta[1,0] == [-v for v in theta[0,1]]
    assert all(v==[0]*4 for key,v in theta.items() if key not in [(0,1),(1,0)])
    return curvature+kappa*torsion,word_count

geometry = []
for N,expected in [([1,1,1,1],[16,32,24,8,1]),([2,1,1,1],[24,52,42,15,2])]:
    cs=ns['cells'](N); assert [len(x) for x in cs]==expected
    names={(tuple(c['directions']),tuple(c['start'])) for layer in cs for c in layer}
    assert all((tuple(d),tuple(p)) in names for layer in cs for c in layer for d,p in c['faces'])
    geometry.append(expected)
cases=0;words=0
for h,b,q0,q1 in product([F(1),F(1,2)],[F(1),F(7,5)],[F(1),F(101,100)],[F(2),F(101,99)]):
    _,n=literal_cell(h,b,q0,q1);cases+=1;words+=n
stationary=[]
for q in [F(101,100),F(6,5),F(2),F(3),F(7,2)]:
    c,s=(q+1/q)/2,(q-1/q)/2
    parent,_=literal_cell(F(1),F(1),F(1),q*q)
    left,_=literal_cell(F(1,2),F(1),F(1),q)
    right,_=literal_cell(F(1,2),F(1),q,q*q)
    assert left+right-parent==(c-1)*(2*s-kappa)
    A,B=2*s+kappa*c,kappa*s;D=A*A-B*B
    assert D==4*s*s+4*kappa*s*c+kappa*kappa>kappa*kappa
    # The exact radical identity is checked after multiplying by sqrt(D).
    assert A*(-B)+B*A==0
    assert A*A+B*(-B)==D
    assert (kappa+2*c*s)**2-D==4*s**4>0
    assert -kappa*s<0 and -(2*s+kappa*c)<0
    for r in [F(9,10),F(1),F(11,10)]:
        C,S=(r+1/r)/2,(r-1/r)/2
        J,R=A*S+B*C,A*C+B*S
        assert R*R-J*J==D
        assert (A*R-B*J)/D==C and (A*J-B*R)/D==S
    for N in range(2,8):
        for k in range(1,N):
            residual=-2*kappa/F(N)*(q**k-q**(-k))/2
            assert residual<0
    stationary.append(str(D))
assert literal_cell(F(1,2),F(1),F(1),F(2))[0]+literal_cell(F(1,2),F(1),F(2),F(4))[0]-literal_cell(F(1),F(1),F(1),F(4))[0]==F(301,808)
pins=json.loads((rdir/'source-pins.json').read_text())['sources']
for pin in pins:
    raw=(rdir/pin['snapshot']).read_bytes()
    assert len(raw)==pin['bytes'] and hashlib.sha256(raw).hexdigest()==pin['sha256']
receipt={'status':'passed','geometry_counts':geometry,'literal_full_cell_cases':cases,
 'all_six_word_cases':words,'exact_stationary_discriminants':stationary,
 'source_pins':len(pins),'original_law':'six based/inverse words, all five transports, all ordered torsion indices; kappa1/101',
 'scope':'fixed inherited cubical coframe and01-boost family; full physical gate0; efficiency0'}
(rdir/'curved-subdivision-root-13.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
