#!/usr/bin/env python3
"""Standalone independent11 native contour algebra replay; no root/helper imports.
Reviewer provided prior advice and arithmetic, authored no production Lean.
"""
from functools import lru_cache
from fractions import Fraction as F
from itertools import product
N=3;Z6=(F(0),)*6;Z4=(F(0),)*4
add=lambda a,b:tuple(x+y for x,y in zip(a,b));neg=lambda a:tuple(-x for x in a);sub=lambda a,b:add(a,neg(b));sc=lambda c,a:tuple(c*x for x in a)
eta=lambda i:-1 if i==0 else 1
pairs=[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]; comps=[(2,3,1),(1,3,-1),(1,2,1),(0,3,1),(0,2,-1),(0,1,1)]
def cross(a,b):return(a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0])
def br(a,b):return add(neg(cross(a[3:],b[:3])),neg(cross(a[:3],b[3:])))+sub(cross(a[:3],b[:3]),cross(a[3:],b[3:]))
def wedge(u,v):return tuple(u[i]*v[j]-u[j]*v[i] for i,j in [(0,1),(0,2),(0,3),(2,3),(3,1),(1,2)])
basis=lambda i:tuple(F(j==i) for j in range(4))
flat=[sc(s,wedge(basis(i),basis(j))) for i,j,s in comps]
star=lambda a:(-a[3],-a[4],-a[5],a[0],a[1],a[2])
bp=lambda a,b:sum((-1 if i<3 else 1)*a[i]*b[i] for i in range(6))
def lie(a):return((0,a[0],a[1],a[2]),(a[0],0,a[5],-a[4]),(a[1],-a[5],0,a[3]),(a[2],a[4],-a[3],0))
class Pulse:
 def __init__(self,c=None,values=None):
  self.zero=([list(Z4) for _ in range(4)],[list(Z6) for _ in range(4)])
  self.value=([list(Z4) for _ in range(4)],[list(Z6) for _ in range(4)])
  if values is not None:
   for i in range(4):
    for a in range(4):self.value[0][i][a]=values[4*i+a]
    for a in range(6):self.value[1][i][a]=values[16+6*i+a]
  elif c is not None:
   if c<16:self.value[0][c//4][c%4]=F(1)
   else:self.value[1][(c-16)//6][(c-16)%6]=F(1)
 def __getitem__(self,t):return self.value if t==0 else self.zero
modulus=3
shift=lambda t,i:((t+(i==0))%modulus if modulus else t+(i==0))
A=lambda q,t,i:tuple(q[t][1][i])
def first(q,t,i,j):return add(wedge(tuple(q[t][0][a][i] for a in range(4)),basis(j)),wedge(basis(i),tuple(q[t][0][a][j] for a in range(4))))
def K(q,t,r):
 i,j=pairs[r];return sub(sub(A(q,shift(t,j),i),A(q,t,i)),sub(A(q,shift(t,i),j),A(q,t,j)))
def LU(q,t,r):
 i,j,s=comps[r];k,l=pairs[r];sites=(t,shift(t,k),shift(t,l),shift(shift(t,k),l));linear=sc(F(s,4),tuple(sum(first(q,v,i,j)[a] for v in sites) for a in range(6)))
 V=sc(F(1,8),add(add(sc(3,A(q,t,k)),A(q,shift(t,l),k)),add(sc(3,A(q,t,l)),A(q,shift(t,k),l))))
 return sub(linear,br(V,flat[r]))
def contact(q,p,t,r):
 k,l=pairs[r]
 letters=lambda q:(neg(A(q,t,l)),neg(A(q,shift(t,l),k)),A(q,shift(t,k),l),A(q,t,k))
 a,b=letters(q),letters(p)
 return sc(F(-1,2),tuple(sum(br(a[i],b[j])[c] for i in range(4) for j in range(i+1,4)) for c in range(6)))
def theta(q,t,r):
 i,j=pairs[r];Li,Lj=lie(A(q,t,i)),lie(A(q,t,j));return tuple(q[shift(t,i)][0][a][j]-q[t][0][a][j]-q[shift(t,j)][0][a][i]+q[t][0][a][i]-Li[a][j]+Lj[a][i] for a in range(4))
def density(q,p,t):
 ans=F(0)
 for r in range(6):
  i,j=pairs[r];ans+=bp(LU(q,t,r),star(K(p,t,r)))+bp(flat[r],star(contact(q,p,t,r)))
  ans+=F(1,101)*eta(i)*eta(j)*sum(eta(a)*x*y for a,(x,y) in enumerate(zip(theta(q,t,r),theta(p,t,r))))
 return ans

def bil(q,p):return sum((density(q,p,t) for t in range(3)),F(0))

from dataclasses import dataclass
@dataclass(frozen=True)
class P:
 terms:tuple=()
 def __init__(s,value=0):
  if isinstance(value,P):object.__setattr__(s,'terms',value.terms);return
  d=value if isinstance(value,dict) else {0:F(value)}
  object.__setattr__(s,'terms',tuple(sorted((k,F(v)) for k,v in d.items() if v)))
 def __add__(s,o):
  o=P(o);d=dict(s.terms)
  for k,v in o.terms:d[k]=d.get(k,F(0))+v
  return P(d)
 __radd__=__add__
 def __neg__(s):return P({k:-v for k,v in s.terms})
 def __sub__(s,o):return s+-P(o)
 def __rsub__(s,o):return -s+o
 def __mul__(s,o):
  o=P(o);d={}
  for i,a in s.terms:
   for j,b in o.terms:d[i+j]=d.get(i+j,F(0))+a*b
  return P(d)
 __rmul__=__mul__
 def __truediv__(s,o):
  o=P(o)
  assert len(o.terms)==1
  k,v=o.terms[0];return P({i-k:a/v for i,a in s.terms})
 def __bool__(s):return bool(s.terms)
 def __pow__(s,n):
  if n<0:
   assert len(s.terms)==1
   k,v=s.terms[0];return P({k*n:v**n})
  r=P(1)
  for _ in range(n):r=r*s
  return r
 def val(s,z):return sum((v*z**k for k,v in s.terms),F(0))
 def __str__(s):return str(dict(s.terms))
from dataclasses import dataclass
@dataclass(frozen=True)
class C:
 a:F=F(0)
 b:F=F(0)
 def __post_init__(s):object.__setattr__(s,'a',F(s.a));object.__setattr__(s,'b',F(s.b))
 def __add__(s,o):
  if not isinstance(o,C):o=C(o)
  return C(s.a+o.a,s.b+o.b)
 __radd__=__add__
 def __neg__(s):return C(-s.a,-s.b)
 def __sub__(s,o):return s+-o
 def __rsub__(s,o):return -s+o
 def __mul__(s,o):
  if not isinstance(o,C):o=C(o)
  return C(s.a*o.a-s.b*o.b,s.a*o.b+s.b*o.a)
 __rmul__=__mul__
 def __truediv__(s,o):
  if not isinstance(o,C):o=C(o)
  d=o.a*o.a+o.b*o.b;return C((s.a*o.a+s.b*o.b)/d,(s.b*o.a-s.a*o.b)/d)
 def __rtruediv__(s,o):return C(o)/s
 def __bool__(s):return bool(s.a or s.b)
 def __pow__(s,n):
  if n<0:return (C(1)/s)**(-n)
  out=C(1)
  for _ in range(n):out=out*s
  return out
 def __str__(s):return str(s.a)+('+' if s.b>=0 else '')+str(s.b)+'i'
shift=lambda x,i:(x[0]+(i==0),x[1]+(i==1))
class At:
 def __init__(s,c,t,z):s.p=Pulse(c);s.t=t;s.z=z
 def __getitem__(s,x):
  if x[0]!=s.t:return s.p.zero
  factor=s.z**x[1]
  return([[factor*v for v in row] for row in s.p.value[0]],[[factor*v for v in row] for row in s.p.value[1]])
def letters(q,r):
 k,l=pairs[r];x=(0,0)
 return(neg(A(q,x,l)),neg(A(q,shift(x,l),k)),A(q,shift(x,k),l),A(q,x,k))
def feat(c,t,z):
 q=At(c,t,z);return [(LU(q,(0,0),r),K(q,(0,0),r),theta(q,(0,0),r),letters(q,r)) for r in range(6)]
@lru_cache(None)
def cc(r,a,b):return bp(flat[r],star(br(a,b)))
def entry(f,g):
 value=F(0)
 for r in range(6):
  lu,k,th,ls=f[r];lu2,k2,th2,ls2=g[r];i,j=pairs[r]
  value+=bp(lu,star(k2))+bp(lu2,star(k))
  value+=F(2,101)*eta(i)*eta(j)*sum(eta(a)*x*y for a,(x,y) in enumerate(zip(th,th2)))
  for a in range(4):
   for b in range(a+1,4):
    if any(ls[a]) and any(ls2[b]):value-=F(1,2)*cc(r,ls[a],ls2[b])
    if any(ls2[a]) and any(ls[b]):value-=F(1,2)*cc(r,ls2[a],ls[b])
 return value

def rank(M):
 if not M:return 0
 R=[row[:] for row in M];i=0
 for j in range(len(M[0])):
  k=next((k for k in range(i,len(M)) if R[k][j]),None)
  if k is None:continue
  R[i],R[k]=R[k],R[i];v=R[i][j];R[i]=[a/v for a in R[i]]
  for k in range(i+1,len(M)):
   if R[k][j]:
    v=R[k][j];R[k]=[a-v*b for a,b in zip(R[k],R[i])]
  i+=1
 return i


z=P({1:1});zi=P({-1:1})
f0=[feat(c,0,z) for c in range(40)];f1=[feat(c,1,zi) for c in range(40)]
B=[[P(entry(a,b)) for b in f1] for a in f0]
assert sum(bool(v) for row in B for v in row)==88
q=(1+z)/4
for j,expected in [(22,{10:-q,15:-q}),(23,{6:q,21:q}),(24,{7:q,20:-q})]:
 assert {i:B[i][j] for i in range(40) if B[i][j]}==expected
T=10201+10589*z
weights={5:T,10:-T,15:-T,22:1196*z,29:-F(2,101)*(10201+9393*z),36:-F(2,101)*(10201+9393*z)}
for j in range(40):
 got=sum((w*B[i][j] for i,w in weights.items()),P())
 assert got==(T*(1+z)/2 if j==22 else P())
for j in (0,4,8,12,16,17,18,19,20,21,25,32,39):assert not any(B[i][j] for i in range(40))
for i in range(40):
 assert not (2*B[i][26]+(z+1)*B[i][31])
 assert not (2*B[i][27]+(z+1)*B[i][37])
 assert not (B[i][33]+B[i][38])
r=C(F(399,401),F(40,401));ri=C(1)/r
norm2=lambda w:w.a*w.a+w.b*w.b
assert norm2(r)==1 and r+ri==C(F(798,401))
for n in range(-6,7):
 rn=r**n
 assert norm2(rn)==1 and rn!=C(-1)
 output=[P(row[22]).val(rn) for row in B]
 actual=sum((norm2(v) if isinstance(v,C) else v*v for v in output),F(0))
 assert actual==norm2(C(1)+rn)/8
 sup_squared=max(norm2(v) if isinstance(v,C) else v*v for v in output)
 assert sup_squared==norm2(C(1)+rn)/16
ranks={name:rank([[v.val(symbol) for v in row] for row in B]) for name,symbol in [('one',F(1)),('minus_one',F(-1)),('current_r',r)]}
assert ranks=={'one':24,'minus_one':21,'current_r':24}
# Source zero-character blocks are derived again from the reciprocal-character density.
ff0=[feat(c,0,P(1)) for c in range(40)];ff1=[feat(c,1,P(1)) for c in range(40)]
H0=[[P(entry(a,b)).val(F(1)) for b in ff0] for a in ff0]
H1=[[P(entry(a,b)).val(F(1)) for b in ff1] for a in ff1]
B0=[[v.val(F(1)) for v in row] for row in B]
I=[i for i in range(40) if i not in (0,4,8,12)]
AA=[[H0[i][j]+H1[i][j] for j in I] for i in I];BB=[[B0[i][j] for j in I] for i in I]

B=B0
A=[[H0[i][j]+H1[i][j] for j in range(40)] for i in range(40)]
def tr(a):
    return list(map(list, zip(*a)))

def mv(a, x):
    return [sum((u * v for u, v in zip(row, x))) for row in a]

def mm(a, b):
    return [mv(tr(b), r) for r in a]

def dot(a, b):
    return sum((x * y for x, y in zip(a, b)))

def ident(n):
    return [[F(i == j) for j in range(n)] for i in range(n)]

def inverse(a):
    n = len(a)
    r = [row[:] + i for row, i in zip(a, ident(n))]
    for j in range(n):
        k = next((i for i in range(j, n) if r[i][j]))
        r[k], r[j] = (r[j], r[k])
        v = r[j][j]
        r[j] = [x / v for x in r[j]]
        for i in range(n):
            if i != j:
                v = r[i][j]
                r[i] = [x - v * y for x, y in zip(r[i], r[j])]
    return [row[n:] for row in r]

def compile(a):
    h = [r[:] for r in a]
    n = len(a)
    T = ident(n)
    fallback = 0
    for k in range(n):
        p = next((i for i in range(k, n) if h[i][i]), None)
        if p is None:
            pq = next(((i, j) for i in range(k, n) for j in range(i + 1, n) if h[i][j]), None)
            if pq is None:
                break
            p, q = pq
            fallback += 1
            for i in range(n):
                T[i][p] += T[i][q]
            old = [r[:] for r in h]
            for j in range(n):
                h[p][j] = old[p][j] + old[q][j]
                h[j][p] = old[j][p] + old[j][q]
            h[p][p] = old[p][p] + 2 * old[p][q] + old[q][q]
        if p != k:
            h[k], h[p] = (h[p], h[k])
            for row in h:
                row[k], row[p] = (row[p], row[k])
            for row in T:
                row[k], row[p] = (row[p], row[k])
        pivot = h[k][k]
        v = h[k][:]
        for j in range(k + 1, n):
            c = v[j] / pivot
            if c:
                for i in range(n):
                    T[i][j] -= c * T[i][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                h[i][j] -= v[i] * v[j] / pivot
        for j in range(k + 1, n):
            h[j][k] = h[k][j] = F(0)
    else:
        k = n
    rank = k
    diag = [h[i][i] for i in range(n)]
    assert all(diag[:rank]) and (not any(diag[rank:]))
    assert mm(mm(tr(T), a), T) == [[diag[i] if i == j else F(0) for j in range(n)] for i in range(n)]
    inv = inverse(T)
    assert mm(T, inv) == ident(n) == mm(inv, T)
    return (T, diag, rank, fallback)

def history(N):
    n = N - 1
    h = [[F(0)] * (40 * n) for _ in range(40 * n)]
    for t in range(n):
        for i in range(40):
            for j in range(40):
                h[40 * t + i][40 * t + j] = A[i][j]
                if t + 1 < n:
                    h[40 * t + i][40 * (t + 1) + j] = B[i][j]
                    h[40 * (t + 1) + j][40 * t + i] = B[i][j]
    return h

def L(u, v):
    return dot(b, [x - y for x, y in zip(u, v)]) + dot(u, mv(H0, u)) / 2 + dot(u, mv(B, v)) + dot(v, mv(H1, v)) / 2
b=[F(i in (22,29,36)) for i in range(40)]

H=history(3);T,di,rank,_=compile(H);assert rank==66
positive=sum(x>0 for x in di);negative=sum(x<0 for x in di);assert (positive,negative)==(37,29)
assert (positive-negative)%8==0 # exact phase exp(i*pi*signature/4)=1
q=[F(i==25) for i in range(80)];r=mv(H,q);rho=mv(tr(T),r)
assert r[25]==F(4,101) and not any(rho[i] for i in range(80) if not di[i])
contact=sum(rho[i]**2/di[i] for i in range(80) if di[i]);assert contact==F(4,101)
assert dot(q,mv(H,q))/2-dot(r,q)==F(-2,101)
# Full native affine/source action, including two nonzero rational endpoints.
x=[F(i%5-2,7) for i in range(40)];z=[F(i%7-3,11) for i in range(40)];trial=[F(i%9-4,13) for i in range(80)];residual=mv(H,trial);end=[F(0)]*80
for i,v in enumerate(mv(tr(B),x)):end[i]+=v
for i,v in enumerate(mv(B,z)):end[40+i]+=v
j=[u+v for u,v in zip(residual,end)];rho=mv(tr(T),residual);y=mv(T,[rho[i]/di[i] if di[i] else F(0) for i in range(80)])
endpoint=dot(b,[u-v for u,v in zip(x,z)])+dot(x,mv(H0,x))/2+dot(z,mv(H1,z))/2
three=L(x,y[:40])+L(y[:40],y[40:])+L(y[40:],z)-dot(j,y)
assert three==endpoint-sum(rho[i]**2/di[i] for i in range(80) if di[i])/2
# Exact formal scalar omega with omega^2=sign(d)*i, avoiding numerical sqrt/exponent tests.
class W:
 def __init__(self,a=0,b=0,sign=1):self.a=a if isinstance(a,C) else C(a);self.b=b if isinstance(b,C) else C(b);self.sign=sign
 def __add__(self,o):
  if not isinstance(o,W):o=W(o,sign=self.sign)
  assert self.sign==o.sign
  return W(self.a+o.a,self.b+o.b,self.sign)
 __radd__=__add__
 def __neg__(self):return W(-self.a,-self.b,self.sign)
 def __sub__(self,o):return self+-o if isinstance(o,W) else self+(-o)
 def __mul__(self,o):
  if not isinstance(o,W):o=W(o,sign=self.sign)
  assert self.sign==o.sign
  return W(self.a*o.a+self.b*o.b*C(0,self.sign),self.a*o.b+self.b*o.a,self.sign)
 __rmul__=__mul__
 def __truediv__(self,o):return self*F(1,o)
 def __eq__(self,o):return isinstance(o,W) and self.a==o.a and self.b==o.b and self.sign==o.sign
hbar=F(3,7);mode_checks=0
for i,d in enumerate(di):
 if not d:continue
 v=W(rho[i]/d,F(i%5-2,11),1 if d>0 else -1)
 lhs=(v*v*(d/2)-v*rho[i])*C(0,1)/hbar
 expected=W(C(-abs(d)*F(i%5-2,11)**2/(2*hbar),-rho[i]**2/(2*d*hbar)),sign=1 if d>0 else -1)
 assert lhs==expected;mode_checks+=1
bad=[F(i==0) for i in range(80)];bad_rho=mv(tr(T),bad);assert any(bad_rho[i] for i in range(80) if not di[i])
# 1D measure warning: scaling certificate forward by2 scales its Gaussian volume by1/2.
assert F(1,4)==F(1,2)**2
import json,hashlib
factor=F(1)
for d in di:
 if d:factor*=2/abs(d)
print(json.dumps(dict(source='standalone independent complete native Full40 density and certificate-coordinate contour controls',active=rank,positive=positive,negative=negative,rotation_phase='1',nonzero_source_component=str(r[25]),nonzero_source_contact=str(contact),stationary_source_correction='-2/101',complete_three_action_affine_source_check=True,exact_active_scalar_wick_completions=mode_checks,incompatible_source_guard=True,gaussian_normalization_squared_over_pi_hbar_power_sha256=hashlib.sha256(str(factor).encode()).hexdigest(),crosscertificate_invariance_claimed=False,analytic_status='Actual Lebesgue integrability/integral is independently reviewed in Lean; this stdlib replay checks source/congruence/exponent algebra, not numerical quadrature',scope='fixed-certificate coordinate Lebesgue reference; no common-carrier Schur composition or physical measure'),indent=2))
