#!/usr/bin/env python3
"""Independent review08 source/Legendre/composition replay.
Standalone stdlib exact arithmetic; no production evaluator or prior reviewer
helper is imported. The reviewer supplied mathematical/convention advice but
authored none of the production Lean under review.
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

class At:
 def __init__(self,c,t):self.p=Pulse(c);self.t=t
 def __getitem__(self,x):return self.p.value if x==self.t else self.p.zero

def letters(q,r):
 k,l=pairs[r];return(neg(A(q,0,l)),neg(A(q,shift(0,l),k)),A(q,shift(0,k),l),A(q,0,k))
def feat(c,t):
 q=At(c,t);return [(LU(q,0,r),K(q,0,r),theta(q,0,r),letters(q,r)) for r in range(6)]
f0=[feat(c,0) for c in range(40)];f1=[feat(c,1) for c in range(40)]
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

B=[[entry(x,y) for y in f1] for x in f0]
H0=[[entry(x,y) for y in f0] for x in f0]
H1=[[entry(x,y) for y in f1] for x in f1]
transpose=lambda M:list(map(list,zip(*M)))
mm=lambda M,N:[[sum((x*y for x,y in zip(row,col)),F(0)) for col in zip(*N)] for row in M]
mv=lambda M,v:[sum((x*y for x,y in zip(row,v)),F(0)) for row in M]
vdot=lambda a,b:sum((x*y for x,y in zip(a,b)),F(0))
vadd=lambda a,b:[x+y for x,y in zip(a,b)]
vsub=lambda a,b:[x-y for x,y in zip(a,b)]
scale=lambda c,v:[c*x for x in v]
def rank(M):
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

def inverse(M):
 n=len(M);R=[row[:]+[F(i==j) for j in range(n)] for i,row in enumerate(M)]
 for j in range(n):
  k=next(i for i in range(j,n) if R[i][j]);R[j],R[k]=R[k],R[j]
  c=R[j][j];R[j]=[a/c for a in R[j]]
  for i in range(n):
   if i!=j and R[i][j]:
    c=R[i][j];R[i]=[a-c*b for a,b in zip(R[i],R[j])]
 return [row[n:] for row in R]
assert H0==transpose(H0) and H1==transpose(H1)
assert rank(B)==24
H=[H0[i]+B[i] for i in range(40)]+[transpose(B)[i]+H1[i] for i in range(40)]
terms=[]
for i in range(80):
 for j in range(i,80):
  value=202*H[i][j]/(2 if i==j else 1)
  assert value.denominator==1
  if value:terms.append((i,j,int(value)))
assert len(terms)==204
b=[F(i in (22,29,36)) for i in range(40)]
for t in (0,1):
 coefficients=[sum(bp(flat[r],star(feat(c,t)[r][1])) for r in range(6)) for c in range(40)]
 assert coefficients==scale(1 if t==0 else -1,b)
A40=[[x+y for x,y in zip(a,b_)] for a,b_ in zip(H0,H1)]
active=[i for i in range(40) if i not in (0,4,8,12)]
Da=inverse([[A40[i][j] for j in active] for i in active])
D=[[F(0)]*40 for _ in range(40)]
for i,ii in enumerate(active):
 for j,jj in enumerate(active):D[ii][jj]=Da[i][j]
J=[[F(i==j and i in active) for j in range(40)] for i in range(40)]
assert mm(A40,D)==mm(D,A40)==J
assert D==transpose(D) and rank(A40)==36
assert mm(J,B)==B and mm(B,J)==B and mm(J,transpose(B))==transpose(B)
C=[scale(-1,row) for row in mm(mm(B,D),B)]
assert rank(C)==18

def source_action(u,v):
 class TwoTime:
  def __getitem__(self,t):
   if t==0:return Pulse(values=u).value
   if t==1:return Pulse(values=v).value
   return Pulse().zero
 q=TwoTime()
 return sum(bp(flat[r],star(K(q,0,r))) for r in range(6))+density(q,q,0)

def action(u,v):return vdot(b,vsub(u,v))+vdot(u,mv(H0,u))/2+vdot(u,mv(B,v))+vdot(v,mv(H1,v))/2
pre=lambda u,v:vsub(vsub(scale(-1,b),mv(H0,u)),mv(B,v))
post=lambda u,v:vadd(vadd(scale(-1,b),mv(transpose(B),u)),mv(H1,v))
x=[F(i%7-3,i+1) for i in range(40)]
z=[F(i%5-2,i+2) for i in range(40)]
j=[F(i%3-1,i+3) if i in active else F(0) for i in range(40)]
r=vsub(vsub(j,mv(transpose(B),x)),mv(B,z))
y=mv(D,r)
for i in (0,4,8,12):y[i]=F(i+7,11)
assert mv(A40,y)==r and vsub(post(x,y),pre(y,z))==j
assert source_action(x,y)==action(x,y)
assert source_action(y,z)==action(y,z)
effective=vdot(x,mv(H0,x))/2+vdot(z,mv(H1,z))/2+vdot(b,vsub(x,z))-vdot(r,mv(D,r))/2
assert action(x,y)+action(y,z)-vdot(j,y)==effective
# Directional variation: all endpoint coordinates remain independent.
du=[F(i%4-2,i+5) for i in range(40)];dv=[F(i%6-3,i+7) for i in range(40)];eps=F(3,7)
quadratic_direction=vdot(du,mv(H0,du))/2+vdot(du,mv(B,dv))+vdot(dv,mv(H1,dv))/2
assert source_action(vadd(x,scale(eps,du)),vadd(z,scale(eps,dv)))==action(x,z)+eps*(vdot(post(x,z),dv)-vdot(pre(x,z),du))+eps**2*quadratic_direction
# Relation-valued kick/central/kick factorization, without a bijectivity claim.
p,q=pre(x,z),post(x,z)
incoming=vadd(vadd(p,b),mv(H0,x));assert incoming==scale(-1,mv(B,z))
central_out=mv(transpose(B),x)
assert vadd(vsub(central_out,b),mv(H1,z))==q
zero=[F(0)]*40;e25=zero[:];e25[25]=1;e0=zero[:];e0[0]=1
assert pre(zero,e25)==post(zero,e25)==scale(-1,b)
assert not any(B[25]) and not any(B[i][25] for i in range(40))
assert not any(H1[i][25] for i in range(40)) and H0[25][25]==F(4,101)
assert pre(e25,z)[25]==F(-4,101) and b[25]==0
assert -D[25][25]/2==F(-9595,39964)
assert vsub(post(zero,zero),pre(zero,zero))==zero
assert mv(J,e0)!=e0 and not any(A40[0])
import hashlib,json
print(json.dumps({'coefficient_field':'Q','source':'independent transcription of complete Full40 density, including ordered contact/torsion and linear curvature','cut_quadratic_monomials':len(terms),'common_denominator':202,'independent_polynomial_terms_sha256':hashlib.sha256(json.dumps(terms,separators=(',',':')).encode()).hexdigest(),'affine_boundary_nonzeros':[22,29,36],'actual_cut_matrix_binding_dense_control':True,'directional_variation_control':True,'relation_score_factorization_control':True,'mixed_rank':24,'middle_rank':36,'effective_mixed_rank':18,'D_left_right_projector':True,'inactive_source_components':[0,4,8,12],'source_compatibility_and_stationary_action':True,'source_contact':'-9595/39964','nonextension_witness':'0->e25 admitted; future pre component25=-4/101 for every endpoint','zero_matching_control':True,'inactive_e0_source_rejected':True,'scope':'complete flat spatial-zero-character Taylor model; no quantum integral, physical mode count, gauge classification or curved-score field map'},indent=2))
