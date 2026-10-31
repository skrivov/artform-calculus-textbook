#!/usr/bin/env python3
"""Independent review09 reciprocal-character/history/quantum screening replay.
Standalone stdlib exact arithmetic; imports no production or prior reviewer
module. Reviewer supplied prior mathematical/convention advice but authored no
production Lean. Analytical/global-operator conclusions require separate review.
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
results={}
for N in (2,3,4,5):
 n=N-1;M=[[F(0) for _ in range(36*n)] for _ in range(36*n)]
 for t in range(n):
  for i in range(36):
   for j in range(36):
    M[36*t+i][36*t+j]=AA[i][j]
    if t+1<n:M[36*t+i][36*(t+1)+j]=BB[i][j];M[36*(t+1)+j][36*t+i]=BB[i][j]
 nulls=[]
 for s in range(2,N):
  for a in range(6):
   lam=lambda t:tuple(F(t==s and j==a) for j in range(6))
   full=[]
   for t in range(1,N):
    L=lie(lam(t));value=[F(0)]*40
    for i in range(4):
     for j in range(4):value[4*i+j]=L[i][j]
    for j in range(6):value[16+j]=lam(t+1)[j]-lam(t)[j]
    full.extend(value[i] for i in I)
   assert all(sum(x*y for x,y in zip(row,full))==0 for row in M)
   nulls.append(full)
 rr=rank(M);assert rank(nulls)==len(nulls)==36*n-rr
 results[str(N)]={'active_dimension':36*n,'rank':rr,'nullity':len(nulls),'independent_projected_owned_Ward_columns':len(nulls)}
assert [results[str(N)]['rank'] for N in (2,3,4,5)]==[36,66,96,126]
# Third-cell source compatibility is stronger than pointwise inactive-coordinate guards.
first_source=[F(0)]*40;first_source[16]=1;second_source=[F(0)]*40
assert all(first_source[i]==second_source[i]==0 for i in (0,4,8,12))
w=[F(1),F(0),F(0),F(0),F(0),F(0)]
g1=[F(0)]*40;g2=[F(0)]*40
for i in range(4):
 for j in range(4):g2[4*i+j]=lie(w)[i][j]
for a in range(6):g1[16+a]=w[a];g2[16+a]=-w[a]
source_pair=sum(a*b for a,b in zip(first_source,g1))+sum(a*b for a,b in zip(second_source,g2))
assert source_pair==1
# Quantum screening controls: negative real quadratic ray and absent output coordinates.
trace=[F(i in (25,32,39)) for i in range(40)]
negative=sum(trace[i]*H0[i][j]*trace[j] for i in range(40) for j in range(40))/2
assert negative==F(-291,101)
flat_output=(0,4,8,12,16,17,18,19,20,21,25,32,39)
for j in flat_output:
 assert not any(B0[i][j] or H1[i][j] for i in range(40)) and j not in (22,29,36)
import json,hashlib
print(json.dumps({'source':'independent complete Full40 reciprocal-character density transcription','spatial_average_retained':True,'nonzero_Laurent_entries':88,'sparse_column22_response':{'10':'-(1+z)/4','15':'-(1+z)/4'},'six_row_identity':'W(z)B(z)=(10201+10589z)(1+z)e22^T/2','witness_supported_rows':[5,10,15,22,29,36],'actual_r_unit_and_trace':'|r|=1, r+r^-1=798/401','sampled_actual_harmonic_Euclidean_norm_squared':'|1+r^n|^2/8 for -6<=n<=6','sampled_actual_harmonic_Pi_sup_norm_squared':'|1+r^n|^2/16 for -6<=n<=6','sampled_symbol_ranks':ranks,'history':results,'active_thirdcell_source_rejection_pairing':'1','negative_ray_coefficient':'-291/101','flat_output_coordinates':list(flat_output),'analytic_not_numerically_proved':['irrational rotation density and all-harmonic nonresonance','actual global circle/L2 source binding and kernel-complement obstruction','Gaussian nonintegrability or constrained oscillatory kernel/measure'], 'scope':'exact finite/Fourier algebraic controls; no physical gravity selection or universal quantization no-go'},indent=2))
