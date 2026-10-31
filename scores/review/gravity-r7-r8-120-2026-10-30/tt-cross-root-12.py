"""Exact full24 native TT cross source, prepared jet and history/current replay."""
from pathlib import Path
rdir=Path(__file__).resolve().parent
exec((rdir/'native-coordinate-root-10.py').read_text().split('checks=0')[0])
from itertools import combinations
pairs=list(combinations(range(4),2));bivs=[(0,1),(0,2),(0,3),(2,3),(3,1),(1,2)]
def wedge(i,l):return [C(int((i,l)==p)-int((l,i)==p)) for p in bivs]
def transpose(a):return [list(r) for r in zip(*a)]
def lie(a):
 return mat([[0,a[0],a[1],a[2]],[a[0],0,a[5],-a[4]],[a[1],-a[5],0,a[3]],[a[2],a[4],-a[3],0]])
P=zero(24,24);blocks=zero(24,24);col=0
for tri in combinations(range(4),3):
 for r in range(3):
  mu=tri[r];w=wedge(tri[(r+1)%3],tri[(r+2)%3])
  for a in range(6):P[6*mu+a][col+r]=w[a]
  blocks[col+r][col+r]=4*kap*sig[tri[0]]*sig[tri[1]]*sig[tri[2]]
 for r,s in combinations(range(3),2):
  other=next(t for t in range(3) if t not in (r,s));v=-(1-2*kap)*sig[tri[other]]
  blocks[col+r][col+s]=blocks[col+s][col+r]=v
 col+=3
for b in range(4):
 other=[t for t in range(4) if t!=b]
 for r,mu in enumerate(other):
  w=wedge(mu,b)
  for a in range(6):P[6*mu+a][col+r]=w[a]
  for s in range(3):blocks[col+r][col+s]=sig[b]*(2*kap if r==s else -1)
 col+=3
assert mul(P,transpose(P))==eye(24)
B=mul(mul(P,blocks),transpose(P));Bi=inv(B);M=zero(24,24)
for r,(i,l) in enumerate(pairs):
 for a in range(4):M[4*r+a][4*r+a]=sig[i]*sig[l]*sig[a]
T=zero(24,24)
for col in range(24):
 A=[lie([C(int(6*mu+a==col)) for a in range(6)]) for mu in range(4)]
 for r,(i,l) in enumerate(pairs):
  for a in range(4):T[4*r+a][col]=-A[i][a][l]+A[l][a][i]
Qop=sub(M,scale(2*kap,mul(mul(mul(mul(M,T),Bi),transpose(T)),M)))
def tt_source(k,q,lam):
 ds=[C(lam)]+[j*C(a) for a in k];m=zero(4,4)
 for a in range(3):
  for b in range(3):m[a+1][b+1]=C(q[a][b])
 Z=[]
 for i,l in pairs:
  for a in range(4):Z.append([(ds[i]-ds[l])*sig[a]*(ds[i]*m[l][a]+ds[l]*m[i][a]-ds[a]*m[i][l])/4])
 Q=mul(Qop,Z)
 return [[-2*kap*sig[a]*sum((ds[i]-ds[l])*ds[i]*ds[l]/2*Q[4*r+a][0] for r,(i,l) in enumerate(pairs))] for a in range(4)]
V=mat([[C(x)**r for r in range(6)] for x in range(6)]);Vi=inv(V)
def source_coeffs(k,q):
 vals=[tt_source(k,q,C(x)) for x in range(6)];coeffs=[mul(Vi,[[v[a][0]] for v in vals]) for a in range(4)]
 R=sum(C(t)**2 for t in k)
 c0=[sum(coeffs[a][2*r][0]*(-R)**r for r in range(3)) for a in range(4)]
 c1=[sum(coeffs[a][2*r+1][0]*(-R)**r for r in range(3)) for a in range(4)]
 return c0,c1,coeffs

import json,hashlib,random
rng=random.Random(12031);checks=0
qcross=[[0,0,1],[0,0,1],[1,1,0]]
assert sum(v*v for row in qcross for v in row)==4
for av in [F(1),F(-1),F(3,2),F(3),F(1,7)]:
 c0,c1,co=source_coeffs([av,-av,0],qcross)
 assert c0==[C(0) for _ in range(4)]
 assert c1==[C(0),C(0),C(0),C(-2*kap*F(9999,9991)*av**4)]
 assert [r[0] for r in co[3]]==[C(0),C(0),C(0),C(kap*F(9999,9991)*av**2),C(0),C(0)]
 for z in [C(0),C(1),C(F(1,2),F(1,3)),C(-2)]:
  k=[av,-av,0];p=[-j*z]+[C(v) for v in k]
  G=symbol(p);e3=[[C(0)],[C(0)],[C(0)],[C(1)]]
  expected=scale(-kap*F(9999,9991)*av**2*(z*z-2*av**2)*(z*z+av**2),e3)
  assert mul(G,e3)==expected
  ds=[z,j*av,-j*av,C(0)];m=zero(4,4)
  for a in range(3):
   for b in range(3):m[a+1][b+1]=C(qcross[a][b])
  Z=[[(ds[i]-ds[l])*sig[a]*(ds[i]*m[l][a]+ds[l]*m[i][a]-ds[a]*m[i][l])/4] for i,l in pairs for a in range(4)]
  Aret=scale(-2*kap,mul(mul(mul(Bi,transpose(T)),M),Z))
  assert add(mul(B,Aret),scale(2*kap,mul(mul(transpose(T),M),Z)))==zero(24,1)
  assert mul(M,add(Z,mul(T,Aret)))==mul(Qop,Z)
  checks+=1
H=F(9999,9991)
prep=lambda a,u:[-u[1]/(2*a*a),u[0],u[1],-2*a*a*u[0]]
step=lambda a,u:[u[1],-2*a*a*u[0]]
fstep=lambda a,u,x:x[1:]+[a*a*x[2]+2*a**4*x[0]-2*a*a*u[1]]
green=lambda a,x,y:x[0]*y[3]-x[1]*y[2]+x[2]*y[1]-x[3]*y[0]-a*a*(x[0]*y[1]-x[1]*y[0])
row=lambda a,x:x[4]-a*a*x[2]-2*a**4*x[0]
for _ in range(96):
 a=F(rng.choice([v for v in range(-9,10) if v]),rng.randint(1,9))
 u=[F(rng.randint(-12,12),rng.randint(1,8)) for _ in range(2)]
 v=[F(rng.randint(-12,12),rng.randint(1,8)) for _ in range(2)]
 x=[F(rng.randint(-12,12),rng.randint(1,8)) for _ in range(5)]
 y=[F(rng.randint(-12,12),rng.randint(1,8)) for _ in range(5)]
 assert fstep(a,u,prep(a,u))==prep(a,step(a,u))
 assert prep(a,u)[1:3]==u
 assert green(a,prep(a,u),prep(a,v))==-F(5,2)*(u[0]*v[1]-u[1]*v[0])
 assert green(a,x[1:],y[:4])+green(a,x[:4],y[1:])==x[0]*row(a,y)-row(a,x)*y[0]
 homogeneous=[F(1),F(0),-a*a,F(0),a**4]
 assert row(a,homogeneous)==0
 assert row(a,[xx+hh for xx,hh in zip(x,homogeneous)])==row(a,x)
 # Exact power-series coefficients verify the source-driven response at order0..12.
 import math
 l2=2*a*a
 ujet=[]
 for n in range(13):
  value=F(0) if n%2 else (-3*((-l2)**(n//2))-l2**(n//2)+4*((-a*a)**(n//2)))/(6*a*a)
  ujet.append(value)
 assert ujet[:4]==[0]*4
 for n in range(9):
  forcing=F(0) if n%2 else -2*a*a*((-l2)**(n//2))
  assert ujet[n+4]-a*a*ujet[n+2]-2*a**4*ujet[n]==forcing
 checks+=1
# Preserve source pins, and never execute old receipt-writing tails.
pins=json.loads((rdir/'source-pins.json').read_text())['sources']
for pin in pins:
 p=rdir/pin['snapshot'];assert p.stat().st_size==pin['bytes'] and hashlib.sha256(p.read_bytes()).hexdigest()==pin['sha256']
receipt={'status':'passed','full24_nonreal_symbol_cases':20,'rational_preparation_current_history_cases':96,
 'forced_series_orders':list(range(9)),'checks_groups':checks,'source_pins':len(pins),
 'native_credit':'limiting actual source and paired sector only; finite-h/full40 physical gate0',
 'efficiency_credit':'0; no historical or runtime claim'}
(rdir/'tt-cross-root-12.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
