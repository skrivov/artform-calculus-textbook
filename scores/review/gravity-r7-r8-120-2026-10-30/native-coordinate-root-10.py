"""Exact native polynomial, source and16-coordinate companion checks over Q(i)."""
from fractions import Fraction as F
from pathlib import Path
import hashlib,json

class C:
 def __init__(self,a=0,b=0):
  if isinstance(a,C):self.a,self.b=a.a,a.b
  else:self.a,self.b=F(a),F(b)
 def __add__(x,y):
  y=C(y);return C(x.a+y.a,x.b+y.b)
 __radd__=__add__
 def __neg__(x):return C(-x.a,-x.b)
 def __sub__(x,y):return x+-C(y)
 def __rsub__(x,y):return C(y)+-x
 def __mul__(x,y):
  y=C(y);return C(x.a*y.a-x.b*y.b,x.a*y.b+x.b*y.a)
 __rmul__=__mul__
 def inv(x):
  d=x.a*x.a+x.b*x.b;assert d
  return C(x.a/d,-x.b/d)
 def __truediv__(x,y):return x*C(y).inv()
 def __rtruediv__(x,y):return C(y)*x.inv()
 def __pow__(x,n):
  if n<0:return x.inv()**(-n)
  r=C(1)
  for _ in range(n):r=r*x
  return r
 def __eq__(x,y):
  y=C(y);return x.a==y.a and x.b==y.b
 def __bool__(x):return bool(x.a or x.b)
 def __repr__(x):return str(x.a)+'+'+str(x.b)+'i'

def mat(a):return [[C(v) for v in r] for r in a]
def eye(n):return mat([[int(i==j) for j in range(n)] for i in range(n)])
def zero(n,m):return mat([[0]*m for _ in range(n)])
def add(a,b):return [[x+y for x,y in zip(ar,br)] for ar,br in zip(a,b)]
def neg(a):return [[-x for x in r] for r in a]
def sub(a,b):return add(a,neg(b))
def scale(s,a):return [[C(s)*x for x in r] for r in a]
def mul(a,b):return [[sum(a[i][k]*b[k][j] for k in range(len(b))) for j in range(len(b[0]))] for i in range(len(a))]
def inv(a):
 n=len(a);w=[r[:]+e for r,e in zip(a,eye(n))]
 for i in range(n):
  p=next(j for j in range(i,n) if w[j][i]);w[i],w[p]=w[p],w[i]
  pivot=w[i][i];w[i]=[v/pivot for v in w[i]]
  for j in range(n):
   if j!=i:
    factor=w[j][i];w[j]=[x-factor*y for x,y in zip(w[j],w[i])]
 return [r[n:] for r in w]
def total(items):
 r=zero(len(items[0]),len(items[0][0]))
 for a in items:r=add(r,a)
 return r
sig=[C(-1),C(1),C(1),C(1)];eta=mat([[-1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]])
H=C(F(9999,9991));D=C(F(10201,10300));kap=C(F(1,101));j=C(0,1)
def dot(u,v):return sum(sig[i]*u[i]*v[i] for i in range(4))
def face(p):
 u=[x*x for x in p];return [[(u[a]*p[b]-u[b]*p[a])/2 for b in range(4)] for a in range(4)]
def disc(p):
 u=[x*x for x in p];return (dot(u,u)*dot(p,p)-dot(u,p)**2)/4
def cross(f,g):return [[sum(sig[l]*f[a][l]*g[b][l] for l in range(4)) for b in range(4)] for a in range(4)]
def pair(f,g):
 fd=sum(sig[a]*sig[b]*f[a][b]*g[a][b] for a in range(4) for b in range(4))/2
 return scale(2*kap,add(scale(H*fd,eta),scale(D-H,cross(f,g))))
def symbol(p):return pair(face(p),face(p))
def native_inv(p):
 d=disc(p);assert d
 c=mul(eta,cross(face(p),face(p)))
 numerator=add(scale(D*d,eye(4)),scale(H-D,c))
 return scale(1/(2*kap*H*D*d*d),mul(numerator,eta))
def source(p,Q):
 r=face(p)
 return [[2*j*kap*sig[a]*sum(r[i][l]*Q(i,l,a) for i in range(4) for l in range(i+1,4))] for a in range(4)]
checks=0
for raw in [[-3,1,2,2],[3,1,2,2],[-5,2,-3,4],[2,1,2,4],[-1,1,0,0]]:
 p=list(map(C,raw));c=mul(eta,cross(face(p),face(p)));d=disc(p)
 assert mul(c,c)==scale(d,c)
 a=symbol(p);ai=native_inv(p);assert mul(a,ai)==mul(ai,a)==eye(4)
 al=mul(mul(eta,a),eta);ail=mul(mul(eta,ai),eta)
 assert mul(al,ail)==mul(ail,al)==eye(4)
 checks+=1
# Derive all five original coefficient matrices from the literal temporal face.
k=list(map(C,[1,2,3]));a=face([C(0)]+k)
b=mat([[0,j*k[0]**2/2,j*k[1]**2/2,j*k[2]**2/2],[-j*k[0]**2/2,0,0,0],[-j*k[1]**2/2,0,0,0],[-j*k[2]**2/2,0,0,0]])
c=mat([[0,-k[0]/2,-k[1]/2,-k[2]/2],[k[0]/2,0,0,0],[k[1]/2,0,0,0],[k[2]/2,0,0,0]])
g=[pair(a,a),add(pair(a,b),pair(b,a)),total([pair(a,c),pair(b,b),pair(c,a)]),add(pair(b,c),pair(c,b)),pair(c,c)]
R=sum(x*x for x in k);g4=zero(4,4);g4[0][0]=D*R/202
for u in range(3):
 for v in range(3):g4[u+1][v+1]=(-H*R*int(u==v)+(H-D)*k[u]*k[v])/202
assert g[4]==g4
hi=zero(4,4);hi[0][0]=202/(D*R)
for u in range(3):
 for v in range(3):hi[u+1][v+1]=-202/R*(int(u==v)/H+(1/D-1/H)*k[u]*k[v]/R)
assert mul(hi,g4)==mul(g4,hi)==eye(4)
for z in map(C,[0,1,2,-3]):assert total([scale(z**i,g[i]) for i in range(5)])==symbol([-j*z]+k)
z=C(2);L=native_inv([-j*z]+k);N=zero(16,16)
for u in range(12):N[u][u+4]=C(1)
for v in range(4):
 block=neg(mul(hi,g[v]))
 for u in range(4):
  for w in range(4):N[12+u][4*v+w]=block[u][w]
full=inv(sub(scale(z,eye(16)),N));basis=0
for col in range(16):
 rhs=[[[C(int(4*i+u==col))] for u in range(4)] for i in range(4)]
 cq=total([mul(g[r],total([scale(z**(r-1-i),rhs[i]) for i in range(r)])) for r in range(1,5)])
 xs=[mul(L,cq)]
 for r in range(3):xs.append(sub(scale(z,xs[-1]),rhs[r]))
 flat=[row for block in xs for row in block]
 assert mul(sub(scale(z,eye(16)),N),flat)==[[C(int(i==col))] for i in range(16)]
 assert [v[0] for v in flat]==[full[i][col] for i in range(16)];basis+=1
# Axis numerator and the actual scaling source, with physical Fourier i retained.
p=list(map(C,[2,2,0,0]));assert face(p)==zero(4,4) and symbol(p)==zero(4,4)
assert source(p,lambda i,l,a:C(i+2*l+3*a))==zero(4,1)
p=list(map(C,[-1,1,0,0]));Q=lambda i,l,a:C(int((i,l,a)==(0,1,3)))
response=mul(mul(mul(eta,native_inv(p)),eta),source(p,Q))
assert response==mat([[0],[0],[0],[-j/H]])
for s in map(C,[F(1,2),F(1,7),2]):
 ps=[s*v for v in p]
 actual=mul(mul(mul(eta,native_inv(ps)),eta),source(ps,lambda i,l,a:s*s*Q(i,l,a)))
 assert actual==scale(1/s,response)
for a0 in map(C,[1,2,-3]):
 for z0 in map(C,[0,1,2,3,4]):
  pp=[-j*z0,a0,-a0,C(0)];coeff=-kap*H*a0*a0*(z0*z0-2*a0*a0)*(z0*z0+a0*a0)
  assert mul(symbol(pp),mat([[0],[0],[0],[1]]))==mat([[0],[0],[0],[coeff]])
# Native row normalization, holding cosh/cos as independent exact symbols.
for c0,t0 in [(C(0),C(0)),(C(2),C(3))]:
 scale0=-1/(kap*H);u0=scale0*(c0+2*t0-3)/6;u2=scale0*(2*c0-2*t0)/6;u4=scale0*(4*c0+2*t0)/6
 assert -kap*H*(u4-u2-2*u0)==1
rdir=Path(__file__).resolve().parent;root=rdir.parents[3];pairs=0
for item in json.loads((rdir/'source-pins.json').read_text())['sources']:
 raw=(root/item['original']).read_bytes();assert raw==(rdir/item['snapshot']).read_bytes()
 assert len(raw)==item['bytes'] and hashlib.sha256(raw).hexdigest()==item['sha256'];pairs+=1
out={'status':'passed','native_two_sided_instances':checks,'native_quartic_samples':4,'complete_native_companion_basis_sources':basis,'lower_source_scaling_instances':3,'growing_row_samples':15,'native_unit_row_normalization':True,'source_pairs':pairs,'finite_h_remainder_funded':False,'admitted_nonlinear_source_binding':False,'new_physical_gate':0,'historical_or_runtime_saving':0}
(rdir/'native-coordinate-root-10.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
