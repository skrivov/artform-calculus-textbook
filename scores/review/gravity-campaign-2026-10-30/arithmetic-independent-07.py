from fractions import Fraction as Q
from itertools import combinations
import hashlib, json
from pathlib import Path

# Exact polynomial dictionary arithmetic; tuples carry the three spatial exponents.
def add(a,b):
    r=dict(a)
    for e,c in b.items():
        r[e]=r.get(e,Q(0))+c
        if r[e]==0: del r[e]
    return r
def scale(a,c): return {e:x*c for e,x in a.items() if x*c}
def mul(a,b):
    r={}
    for e,c in a.items():
        for f,d in b.items():
            g=tuple(x+y for x,y in zip(e,f));r[g]=r.get(g,Q(0))+c*d
    return {e:c for e,c in r.items() if c}
def power(a,n):
    r={(0,0,0):Q(1)}
    for _ in range(n):r=mul(r,a)
    return r
def summation(xs):
    r={}
    for x in xs:r=add(r,x)
    return r
x=[{tuple(int(i==j) for i in range(3)):Q(1)} for j in range(3)]
r=summation(power(t,2) for t in x)
s3=summation(power(t,3) for t in x)
s4=summation(power(t,4) for t in x)
n=add(mul(r,s4),scale(power(s3,2),-1))
pair=summation(power(mul(mul(x[i],x[j]),add(x[i],scale(x[j],-1))),2) for i,j in combinations(range(3),2))
assert pair==n
projected=summation(power(add(mul(r,power(t,2)),scale(mul(t,s3),-1)),2) for t in x)
assert projected==mul(r,n)
assert all(sum(e)==6 for e in n)

kappa=Q(1,101);A=Q(101,103);g=Q(101,97);E=Q(202,9991)
Hd=Q(9999,9991);D=Q(10201,10300);beta=-Q(2422,3*9991)
positive=kappa*(Hd+(kappa*A*A+E)*(Hd-D)/Hd)/12
negative=kappa**4*g*g*A*A/(4*beta)
C=positive+negative
assert negative<0 and C>Q(1,24*101)
assert 36*24*101==87264 and 2*87264==174528

def F(k):
    r=sum(t*t for t in k)
    return sum(t**4 for t in k)-sum(t**3 for t in k)**2/r
assert F([Q(1),Q(2),Q(3)])==Q(38,7)
assert F([Q(1),Q(0),Q(0)])==0
closest=[]
for size in range(1,4):
    for inds in combinations(range(3),size):
        k=[Q(1),Q(2),Q(3)]
        error=sum(t*t for t in k)-sum(k[i] for i in inds)**2/size
        assert error>=1
        closest.append(error)
assert min(closest)==Q(3,2)
for n0 in range(100):
    e=Q(1,n0+1);k=[Q(1),1+e,Q(0)];r2=sum(t*t for t in k)
    f=F(k);assert f==e*e*(1+e)**2/(1+(1+e)**2)
    assert 2<=r2<=5 and 0<f<=e*e
    assert 1/(C*f)>=Q((n0+1)**2)/C
assert -Q(2,101)+Q(4,10403)==-Q(2,103)
repo=Path(__file__).resolve().parents[3]
files=['R8Defs.lean','R8Statements.lean','R8Angular.lean','R8LocalInverse.lean','R8Remainder.lean','R8Domains.lean','EnergyAudit.lean']
result={'coefficient':str(C),'coefficient_positive_term':str(positive),'coefficient_negative_term':str(negative),'coefficient_lower_margin':str(C-Q(1,2424)),'polynomial_pair_monomials':len(n),'cleared_projected_monomials':len(projected),'direction123_closest_exceptional_line_distance_squared':str(min(closest)),'exact_sequence_samples':100,'source_hashes':{f:hashlib.sha256((repo/'scores/ArtformScores/GravityBridge/Native'/f).read_bytes()).hexdigest() for f in files},'scope':'Exact algebra replay; samples supplement universal Lean proofs and do not establish native finite-h transfer.'}
print(json.dumps(result,indent=2))
