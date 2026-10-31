"""Distinct exact native replay: coefficient interpolation and rational realification."""
from fractions import Fraction as F
from pathlib import Path
from itertools import product
import json,hashlib
class Z:
 def __init__(self,x=0,y=0):
  if isinstance(x,Z):self.r,self.i=x.r,x.i
  else:self.r,self.i=F(x),F(y)
 def __add__(a,b):b=Z(b);return Z(a.r+b.r,a.i+b.i)
 __radd__=__add__
 def __neg__(a):return Z(-a.r,-a.i)
 def __sub__(a,b):return a+-Z(b)
 def __rsub__(a,b):return Z(b)+-a
 def __mul__(a,b):b=Z(b);return Z(a.r*b.r-a.i*b.i,a.r*b.i+a.i*b.r)
 __rmul__=__mul__
 def __truediv__(a,b):
  b=Z(b);d=b.r*b.r+b.i*b.i;assert d
  return a*Z(b.r/d,-b.i/d)
 def __rtruediv__(a,b):return Z(b)/a
 def __pow__(a,n):
  if n<0:return (Z(1)/a)**(-n)
  v=Z(1)
  for _ in range(n):v=v*a
  return v
 def __bool__(a):return bool(a.r or a.i)
 def __eq__(a,b):b=Z(b);return a.r==b.r and a.i==b.i
 def __repr__(a):return str(a.r)+'+('+str(a.i)+')i'
def mat(a):return [[Z(x) for x in row] for row in a]
def zero(n,m):return mat([[0]*m for _ in range(n)])
def eye(n):return mat([[i==j for j in range(n)] for i in range(n)])
def add(a,b):return [[x+y for x,y in zip(ar,br)] for ar,br in zip(a,b)]
def neg(a):return [[-x for x in row] for row in a]
def sub(a,b):return add(a,neg(b))
def scale(c,a):return [[Z(c)*x for x in row] for row in a]
def mul(a,b):return [[sum((a[i][k]*b[k][j] for k in range(len(b))),Z()) for j in range(len(b[0]))] for i in range(len(a))]
def total(items):
 out=zero(len(items[0]),len(items[0][0]))
 for a in items:out=add(out,a)
 return out
def ratinv(a):
 n=len(a);v=[list(map(F,row))+[F(i==j) for j in range(n)] for i,row in enumerate(a)]
 for j in range(n):
  p=next(i for i in range(j,n) if v[i][j]);v[p],v[j]=v[j],v[p]
  c=v[j][j];v[j]=[x/c for x in v[j]]
  for i in range(n):
   if i!=j:
    c=v[i][j];v[i]=[x-c*y for x,y in zip(v[i],v[j])]
 return [r[n:] for r in v]
def realify(a):
 n=len(a);m=len(a[0]);v=[[F(0)]*(2*m) for _ in range(2*n)]
 for i in range(n):
  for j in range(m):v[i][j]=a[i][j].r;v[i][m+j]=-a[i][j].i;v[n+i][j]=a[i][j].i;v[n+i][m+j]=a[i][j].r
 return v
def inverse(a):
 n=len(a);v=ratinv(realify(a));return [[Z(v[i][j],v[n+i][j]) for j in range(n)] for i in range(n)]
sig=(-1,1,1,1);eta=mat([[-1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]])
kap=Z(F(1,101));Hd=Z(F(9999,9991));Dd=Z(F(10201,10300));ii=Z(0,1)
def ldot(a,b):return sum((sig[i]*a[i]*b[i] for i in range(4)),Z())
def face(p):return [[(p[i]**2*p[j]-p[j]**2*p[i])/2 for j in range(4)] for i in range(4)]
def discriminant(p):
 u=[x*x for x in p];return (ldot(u,u)*ldot(p,p)-ldot(u,p)**2)/4
def fc(a,b):return [[sum((sig[l]*a[i][l]*b[j][l] for l in range(4)),Z()) for j in range(4)] for i in range(4)]
def native(p):
 d=discriminant(p);K=fc(face(p),face(p));return scale(2*kap,add(scale(Hd*d,eta),scale(Dd-Hd,K)))
def invformula(p):
 d=discriminant(p);assert d;C=mul(eta,fc(face(p),face(p)))
 return scale(1/(2*kap*Hd*Dd*d*d),mul(add(scale(Dd*d,eye(4)),scale(Hd-Dd,C)),eta))
def lower(a):return mul(mul(eta,a),eta)
# Held-out exact inverse checks use independent8-by8 rational realification.
instances=[[-2,1,-3,2],[5,-2,1,3],[-1,1,0,0],[5,0,3,4],[-5,0,3,4]]
for raw in instances:
 p=list(map(Z,raw));G=native(p);Gi=invformula(p);C=mul(eta,fc(face(p),face(p)));d=discriminant(p)
 assert mul(C,C)==scale(d,C) and Gi==inverse(G)
 assert mul(G,Gi)==mul(Gi,G)==eye(4)
 assert mul(lower(G),lower(Gi))==mul(lower(Gi),lower(G))==eye(4)
# An excluded discriminant-zero point need not have zero face; never divide there.
singular=list(map(Z,[3,0,3,4]));assert discriminant(singular)==0 and face(singular)!=zero(4,4)
# Interpolate every entry of the known quartic at five distinct z values.
# Its degree bound is established by the submitted proof, not inferred from these samples.
zs=list(map(F,[0,1,-1,2,-2]));vi=ratinv([[z**j for j in range(5)] for z in zs])
def coeffs(k):
 vals=[native([-ii*Z(z)]+list(map(Z,k))) for z in zs]
 return [[[sum((Z(vi[n][m])*vals[m][i][j] for m in range(5)),Z()) for j in range(4)] for i in range(4)] for n in range(5)]
def polynomial(g,z):return total([scale(z**n,g[n]) for n in range(5)])
# Native held-out124 companion, with complex z and a32-by32 rational inverse.
k=[1,2,4];g=coeffs(k);R=Z(sum(x*x for x in k));lead=zero(4,4);lead[0][0]=Dd*R/202
for a in range(3):
 for b in range(3):lead[a+1][b+1]=(-Hd*R*int(a==b)+(Hd-Dd)*k[a]*k[b])/202
assert g[4]==lead
H=inverse(lead);assert mul(H,lead)==mul(lead,H)==eye(4)
for z in [Z(F(1,3)),Z(0,F(2,5)),Z(F(3,2),F(1,3))]:assert polynomial(g,z)==native([-ii*z]+list(map(Z,k)))
z=Z(F(3,2),F(1,3));L=invformula([-ii*z]+list(map(Z,k)));N=zero(16,16)
for i in range(12):N[i][i+4]=Z(1)
for j in range(4):
 block=neg(mul(H,g[j]))
 for a in range(4):
  for b in range(4):N[12+a][4*j+b]=block[a][b]
ZminusN=sub(scale(z,eye(16)),N);fullreal=ratinv(realify(ZminusN))
def response(b):
 contact=total([mul(g[j],total([scale(z**(j-1-i),b[i]) for i in range(j)])) for j in range(1,5)])
 x=[mul(L,contact)]
 for j in range(3):x.append(sub(scale(z,x[-1]),b[j]))
 return [v for block in x for v in block]
for c in range(32):
 rhs=[[Z(int(i==c),int(16+i==c))] for i in range(16)];b=[rhs[4*j:4*j+4] for j in range(4)];x=response(b)
 assert mul(ZminusN,x)==rhs
 realcolumn=[v[0].r for v in x]+[v[0].i for v in x]
 assert realcolumn==[fullreal[i][c] for i in range(32)]
assert N!=zero(16,16) and mul(N,N)!=zero(16,16)
# Exact rational angular strata and fixed-band adverse examples.
angular=0
for kk in product(range(-4,5),repeat=3):
 rr=sum(t*t for t in kk)
 if not rr:continue
 s3=sum(t**3 for t in kk);s4=sum(t**4 for t in kk);psi=F(s4)-F(s3*s3,rr)
 squares=sum(kk[a]**2*kk[b]**2*(kk[a]-kk[b])**2 for a in range(3) for b in range(a+1,3))
 assert rr*psi==squares>=0 and (psi==0)==(len(set(t for t in kk if t))==1);angular+=1
for kk,value in [((3,3,0),0),((3,-3,0),162),((1,2,3),None),((1,2,4),None)]:
 rr=sum(t*t for t in kk);assert 9<=rr<=25 and all(t*t<=F(81,100)*rr for t in kk)
 if value is not None:assert F(sum(t**4 for t in kk))-F(sum(t**3 for t in kk)**2,rr)==value
# Both rational light cones for a held-out band direction.
for sign in [-1,1]:
 p=list(map(Z,[sign*5,0,3,4]));assert discriminant(p).i==0 and discriminant(p).r<=-F(729,400)
 assert mul(native(p),invformula(p))==mul(invformula(p),native(p))==eye(4)
# All six lower mixed contractions, physical imaginary factor, and frequency scaling.
def source(p,Q,j=ii):
 f=face(p);return [[2*j*kap*sig[a]*sum((f[b][c]*Q(b,c,a) for b in range(4) for c in range(b+1,4)),Z())] for a in range(4)]
for a in [Z(1),Z(2),Z(-3)]:
 aligned=[a,a,Z(),Z()];opposite=[-a,a,Z(),Z()]
 assert face(aligned)==native(aligned)==zero(4,4)
 assert source(aligned,lambda b,c,d:Z(b+2*c-3*d))==zero(4,1)
 assert discriminant(opposite)==-a**6 and mul(native(opposite),invformula(opposite))==eye(4)
p=list(map(Z,[-1,1,0,0]));Q=lambda a,b,c:Z(int((a,b,c)==(0,1,3)))
for j in [Z(1),ii]:
 out=mul(lower(invformula(p)),source(p,Q,j));assert out==[[Z()],[Z()],[Z()],[-j/Hd]]
 for s in [Z(F(1,2)),Z(F(1,11)),Z(-3)]:
  ps=[s*x for x in p];scaledQ=lambda a,b,c:s*s*Q(a,b,c)
  assert face(ps)==scale(s**3,face(p)) and discriminant(ps)==s**6*discriminant(p)
  assert native(ps)==scale(s**6,native(p)) and source(ps,scaledQ,j)==scale(s**5,source(p,Q,j))
  assert lower(invformula(ps))==scale(s**-6,lower(invformula(p)))
  assert mul(lower(invformula(ps)),source(ps,scaledQ,j))==scale(s**-1,out)
# Reconstruct the actual signed3-by3 connection block rather than its polynomial inverse.
T=[[F(-1),F(1),F(0)],[F(1),F(0),F(-1)],[F(0),F(-1),F(-1)]];C=[[F(0),F(-1),F(-1)],[F(-1),F(0),F(1)],[F(-1),F(1),F(0)]]
B=[[C[a][b]-F(2,101)*sum(T[l][a]*T[l][b] for l in range(3)) for b in range(3)] for a in range(3)];Bi=ratinv(B);r=[F(0),-F(9,4),F(9,4)]
conn=[-F(2,101)*sum(Bi[a][b]*r[b] for b in range(3)) for a in range(3)];Ci=ratinv(C);curv=[-F(2,101)*sum(Ci[a][b]*r[b] for b in range(3)) for a in range(3)]
assert conn==[0,-F(9,206),F(9,206)] and [conn[i]-curv[i] for i in range(3)]==[0,F(9,10403),-F(9,10403)]
assert -F(18,202)*(3*F(1,2)+3*F(1,2))==-F(27,101)
# All five coefficients of the unused column retain the native a² factor.
for a in [1,2,-3]:
 gg=coeffs([a,-a,0]);expected=[2*kap*Hd*a**6,Z(),kap*Hd*a**4,Z(),-kap*Hd*a*a]
 assert all(gg[n][i][3]==(expected[n] if i==3 else 0) for n in range(5) for i in range(4))
 assert expected[0]+2*a*a*expected[2]+4*a**4*expected[4]==0
 if abs(a)!=1:assert expected[4]!=-kap*Hd # omitted a² is a real coefficient error.
# Derivatives in basis(cosh, sqrt2*sinh, cos, sin, constant) use a rational matrix.
A=[[F(0),F(2),F(0),F(0),F(0)],[F(1),F(0),F(0),F(0),F(0)],[F(0),F(0),F(0),F(1),F(0)],[F(0),F(0),F(-1),F(0),F(0)],[F(0)]*5]
row=-F(101*9991,9999);jets=[[row/F(6),F(0),row/F(3),F(0),-row/F(2)]]
for n in range(4):jets.append([sum(A[i][j]*jets[-1][j] for j in range(5)) for i in range(5)])
at0=[F(1),F(0),F(1),F(0),F(1)];assert all(sum(jets[n][i]*at0[i] for i in range(5))==0 for n in range(4))
forcing=[-F(9999,101*9991)*(jets[4][i]-jets[2][i]-2*jets[0][i]) for i in range(5)];assert forcing==[0,0,0,0,1]
repo=Path.cwd();files=sorted((repo/'scores/ArtformScores/GravityBridge/Native/CoordinateSymbol').glob('*.lean'));assert len(files)==32
print(json.dumps({'status':'pass','method':'independent full-symbol Gram formula, exact five-point coefficient interpolation,8x8/32x32 rational realification, held-out124 complex-frequency companion','source_sha256':{str(p.relative_to(repo)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files},'checks':{'native_inverse_cases':len(instances),'quartic_interpolation_points':5,'native_companion_real_basis_sources':32,'heldout_native_companion_spatial_momentum':[1,2,4],'heldout_native_companion_frequency':'3/2+i/3','angular_exact_integer_cases':angular,'both_heldout_band_light_cones':True,'excluded_nonzero_face_discriminant_zero_point':[3,0,3,4],'all_six_mixed_faces_and_two_Fourier_factors':True,'frequency_source_scalings':6,'signed_connection_solved_by_Gaussian_elimination':True,'growing_column_all_five_coefficients':True,'omitted_a2_factor_rejected':True,'actual_derivative_basis_and_native_unit_force':True},'limitations':'Interpolation uses the proved degree bound. Exact pointwise native algebra does not establish finite-h remainder, uniform physical-source/history budgets, admission or a new physical gate.'},indent=2))
