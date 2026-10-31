#!/usr/bin/env python3
"""Standalone independent longer-history source controls; no root/helper imports.
Prior reviewer advice disclosed; no production Lean authorship.
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

#!/usr/bin/env python3
"""Independent successor full-coordinate correction source-jet controls.
Standalone stdlib: no root evaluator, prior helper, /tmp or production imports.
Source transcription includes both diagonal transports, curvature H-H^-1,
exponential-link contacts, coframe determinant and both inverse metrics.
Reviewer provided conceptual advice; authored no production Lean.
"""
from fractions import Fraction as F
import itertools,json
class J:
 def __init__(s,v=0):s.d={k:F(x) for k,x in (v.d if isinstance(v,J) else v if isinstance(v,dict) else {(0,0):v}).items() if x}
 def __add__(s,o):
  o=J(o);d=s.d.copy()
  for k,x in o.d.items():d[k]=d.get(k,F(0))+x
  return J(d)
 __radd__=__add__
 def __neg__(s):return J({k:-v for k,v in s.d.items()})
 def __sub__(s,o):return s+-J(o)
 def __rsub__(s,o):return J(o)+-s
 def __mul__(s,o):
  o=J(o);d={}
  for (i,j),x in s.d.items():
   for (k,l),y in o.d.items():
    if i+k+j+l<=3 and j+l<=1:d[i+k,j+l]=d.get((i+k,j+l),F(0))+x*y
  return J(d)
 __rmul__=__mul__
 def __truediv__(s,o):return s*F(1,o)
 def __bool__(s):return bool(s.d)
 def coeff(s,i,j=0):return s.d.get((i,j),F(0))
 def __repr__(s):return str(s.d)
eps=J({(1,0):1});delta=J({(0,1):1});zero=J(0)
def eye():return [[J(i==j) for j in range(4)] for i in range(4)]
def plus(a,b):return [[x+y for x,y in zip(r,s)] for r,s in zip(a,b)]
def scale(v,a):return [[v*x for x in r] for r in a]
def mm(a,b):return [[sum(a[i][k]*b[k][j] for k in range(4)) for j in range(4)] for i in range(4)]
def tr(a):return list(map(list,zip(*a)))
def exp(a):
 ans=eye();term=eye()
 for n in range(1,4):term=scale(F(1,n),mm(term,a));ans=plus(ans,term)
 return ans
eta=lambda i:-1 if i==0 else 1
pairs=[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)];comps=[(2,3,1),(1,3,-1),(1,2,1),(0,3,1),(0,2,-1),(0,1,1)]
def lie(a):return [[J(x) for x in r] for r in ((0,a[0],a[1],a[2]),(a[0],0,a[5],-a[4]),(a[1],-a[5],0,a[3]),(a[2],a[4],-a[3],0))]
def wedge(u,v):return tuple(u[i]*v[j]-u[j]*v[i] for i,j in [(0,1),(0,2),(0,3),(2,3),(3,1),(1,2)])
star=lambda a:(-a[3],-a[4],-a[5],a[0],a[1],a[2])
bp=lambda a,b:sum(eta(0) *a[i]*b[i] if i<3 else a[i]*b[i] for i in range(6))
def det(a):
 ans=J(0)
 for p in itertools.permutations(range(4)):
  term=J((-1)**sum(p[i]>p[j] for i in range(4) for j in range(i+1,4)))
  for i in range(4):term=term*a[i][p[i]]
  ans+=term
 return ans

def action(q,testcoord=None,correction=None):
 if correction is None:correction=[[F(0)]*40 for _ in range(3)]
 E=[];U=[];Ui=[]
 for t in range(3):
  e=plus(eye(),[[eps*q[t][4*i+j]+eps*eps*correction[t][4*i+j]+(delta if t==1 and 4*i+j==testcoord else 0) for j in range(4)] for i in range(4)]);E.append(e);u=[];ui=[]
  for i in range(4):
   a=plus(plus(scale(eps,lie(q[t][16+6*i:22+6*i])),scale(eps*eps,lie(correction[t][16+6*i:22+6*i]))),scale(delta,lie([F(t==1 and testcoord==16+6*i+j) for j in range(6)])));u.append(exp(a));ui.append(exp(scale(-1,a)))
  U.append(u);Ui.append(ui)
 ans=J(0)
 for t in range(2):
  shift=lambda i:t+(i==0)
  for r,(k,l) in enumerate(pairs):
   i,j,sign=comps[r];tk=shift(k);tl=shift(l);tkl=t+(k==0)+(l==0)
   # Every transport returns the endpoint coframe to the original base.
   transformed=[E[t],mm(Ui[t][k],E[tk]),mm(Ui[t][l],E[tl]),mm(mm(Ui[t][k],Ui[tk][l]),E[tkl]),mm(mm(Ui[t][l],Ui[tl][k]),E[tkl])]
   weights=[F(1,4),F(1,4),F(1,4),F(1,8),F(1,8)]
   bb=[sum(sign*w*wedge([e[a][i] for a in range(4)],[e[a][j] for a in range(4)])[c] for w,e in zip(weights,transformed)) for c in range(6)]
   hol=mm(mm(mm(Ui[t][l],Ui[tl][k]),U[tk][l]),U[t][k]);holinv=mm(mm(mm(Ui[t][k],Ui[tk][l]),U[tl][k]),U[t][l]);cur=scale(F(-1,2),plus(hol,scale(-1,holinv)));curb=[cur[0][1],cur[0][2],cur[0][3],cur[2][3],cur[3][1],cur[1][2]]
   ans+=bp(bb,star(curb))
  # Metric inverse from full coframe inverse; both factors and determinant retained.
  X=plus(E[t],scale(-1,eye()));ei=eye();power=eye()
  for n in range(1,4):power=mm(power,X);ei=plus(ei,scale((-1)**n,power))
  gi=[[sum(ei[i][a]*eta(a)*ei[j][a] for a in range(4)) for j in range(4)] for i in range(4)]
  tors=[]
  for i,j in pairs:
   a=mm(Ui[t][i],E[shift(i)]);b=mm(Ui[t][j],E[shift(j)]);tors.append([a[c][j]-E[t][c][j]-b[c][i]+E[t][c][i] for c in range(4)])
  value=J(0)
  for r,(i,j) in enumerate(pairs):
   for s,(k,l) in enumerate(pairs):
    value+=(gi[i][k]*gi[j][l]-gi[i][l]*gi[j][k])*sum(eta(a)*tors[r][a]*tors[s][a] for a in range(4))
  ans+=F(1,101)*det(E[t])*value
 return ans




f=[F(0),F(30401,82804),F(20501,41402),F(31803,82804),F(1)]
b=[F(0),F(-5150,20701),F(-200,20701),F(-5150,20701),F(0)]
q=[]
for t in range(5):
 row=[F(0)]*40
 for i in (5,10,15):row[i]=f[t]
 for i in (22,29,36):row[i]=b[t]
 q.append(row)
forces=[]
for t in range(1,4):
 owned=[sum((H0[i][j]+H1[i][j])*q[t][j]+B0[i][j]*q[t+1][j]+B0[j][i]*q[t-1][j] for j in range(40)) for i in range(40)]
 assert not any(owned)
 local=q[t-1:t+2];coefficient=action(local,0).coeff(2,1)
 assert coefficient==3*((1-F(1,101))*b[t]**2+F(1,101)*(f[t+1]-f[t])**2)>0
 correction=[[F((i*7+site*3)%11-5,13) for i in range(40)] for site in range(t-1,t+2)]
 assert action(local,0,correction).coeff(2,1)==coefficient
 forces.append(str(coefficient))
assert forces==['1263813303/6856502416','4414503/6856502416','1337735703/6856502416']
import json
print(json.dumps(dict(source='independent complete native quadratic and original nonlinear two-incident-cell source',cells=4,owned_sites=3,owned_coordinates=120,all_owned_linear_rows_zero=True,spatial_coframe_coefficients=list(map(str,f)),spatial_boost_coefficients=list(map(str,b)),original_source_lapse_jet_coefficients=forces,dense_arbitrary_full_coordinate_second_order_control=True,scope='exact finite longer-history source and nonlinear jets; analytic arbitrary-correction binding must be proved separately'),indent=2))
