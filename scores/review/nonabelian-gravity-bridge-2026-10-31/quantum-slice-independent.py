#!/usr/bin/env python3
"""Standalone independent native66-slice quantum algebra controls.
No root evaluator/data imports, helper imports, or /tmp dependencies.
Reviewer supplied conceptual advice but authored no production Lean.
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
inv=inverse
I=[i for i in range(40) if i not in (0,4,8,12)];J=[i for i in I if i not in (1,2,3,6,7,11)];assert len(I)==36 and len(J)==30
P=[[A[i][j] for j in I] for i in I];Q=[[B[i][j] for j in J] for i in I];R=[[A[i][j] for j in J] for i in J];G=[p+q for p,q in zip(P,Q)]+[q+r for q,r in zip(tr(Q),R)]
sub=lambda x,y:[[a-b for a,b in zip(r,s)] for r,s in zip(x,y)]
S=sub(R,mm(mm(tr(Q),inv(P)),Q));T=sub(P,mm(mm(Q,inv(R)),tr(Q)))
def control(M):
 _,ds,rank,fb=compile(M);assert rank==len(M)
 det=F(1)
 for v in ds:det*=v
 return {'dimension':len(M),'positive':sum(v>0 for v in ds),'negative':sum(v<0 for v in ds),'determinant':det}
g,p,r,s,t=map(control,(G,P,R,S,T))
assert g['determinant']==p['determinant']*s['determinant']==r['determinant']*t['determinant']
for key in ('positive','negative'):assert g[key]==p[key]+s[key]==r[key]+t[key]
a=[F(i%7-3,11) for i in range(36)];b=[F(i%5-2,13) for i in range(30)];rhs=a+b;dot=lambda a,b:sum(x*y for x,y in zip(a,b));full=dot(rhs,mv(inv(G),rhs));rp=mv(inv(P),a);rr=mv(inv(R),b);remp=[x-y for x,y in zip(b,mv(tr(Q),rp))];remr=[x-y for x,y in zip(a,mv(Q,rr))]
assert full==dot(a,rp)+dot(remp,mv(inv(S),remp))==dot(b,rr)+dot(remr,mv(inv(T),remr))

import json,pathlib,argparse
payload={'source':'independent complete Full40 native quadratic density transcription; full three-cell constrained coordinate slice','blocks':dict(zip(('full66','first36','second30','Schur30','Schur36'),[{**v,'determinant':str(v['determinant'])} for v in (g,p,r,s,t)])),'opposite_orders_source_contact':True,'full_signature':8,'fresnel_prefactor_hbar_positive':'(2*pi*hbar)^33/sqrt(abs(detG)); signature phase exp(i*pi*8/4)=1','scope':'Exact finite source matrix/inertia/contact controls. Coordinate Lebesgue gauge-slice/Fresnel prescription is a conditional reference, not an unreduced real80 integral or physical quantum measure.'}
parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args();out=pathlib.Path(__file__).with_name('quantum-slice-independent-data.json')
if args.write:out.write_text(json.dumps(payload,indent=2)+'\n')
elif out.exists():assert json.loads(out.read_text())==payload
print(json.dumps(payload,indent=2))
