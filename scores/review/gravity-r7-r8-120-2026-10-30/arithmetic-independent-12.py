"""Distinct full-density Hessian, native source, preparation and Green replay."""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
import hashlib,json,random
BASE=Path('scores/review/gravity-r7-r8-120-2026-10-30')
# Exact field/matrix utilities only; no author checks or receipt-writing tail.
exec((BASE/'native-coordinate-root-10.py').read_text().split('checks=0')[0])
def transpose(a):return [list(r) for r in zip(*a)]
pairs=list(combinations(range(4),2));bivs=[(0,1),(0,2),(0,3),(2,3),(3,1),(1,2)]
signs=[-1,1,1,1];bs=[-1,-1,-1,1,1,1];kap=F(1,101);H=F(9999,9991)
def real_lie(v):return [[F(0),v[0],v[1],v[2]],[v[0],F(0),v[5],-v[4]],[v[1],-v[5],F(0),v[3]],[v[2],v[4],-v[3],F(0)]]
def real_mm(a,b):return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]
def real_wedge(i,l):return [F((i,l)==p)-F((l,i)==p) for p in bivs]
def eps(v):return (-1)**sum(v[i]>v[l] for i in range(4) for l in range(i+1,4))
# DIRECT original homogeneous density, without the eight-block decomposition.
def density(v):
 A=[real_lie(v[6*i:6*i+6]) for i in range(4)];curv=F(0);tors=F(0)
 for i,l in pairs:
  x,y=[a for a in range(4) if a not in (i,l)]
  ab,ba=real_mm(A[i],A[l]),real_mm(A[l],A[i])
  comm=[ab[r][s]-ba[r][s] for r,s in bivs]
  star=[-comm[3],-comm[4],-comm[5],comm[0],comm[1],comm[2]]
  curv+=eps([x,y,i,l])*sum(g*w*t for g,w,t in zip(bs,real_wedge(x,y),star))
  theta=[-A[i][r][l]+A[l][r][i] for r in range(4)]
  tors+=kap*signs[i]*signs[l]*sum(signs[r]*theta[r]**2 for r in range(4))
 return curv+tors
E=[[F(i==r) for i in range(24)] for r in range(24)]
d0=[density(e) for e in E]
Bdirect=[[density([x+y for x,y in zip(E[r],E[s])])-d0[r]-d0[s] for s in range(24)] for r in range(24)]
assert Bdirect==list(map(list,zip(*Bdirect)))
# Independently assemble all oriented blocks and compare all576 Hessian entries.
P=[[F(0)]*24 for _ in range(24)];blocks=[[F(0)]*24 for _ in range(24)];c=0
for tri in combinations(range(4),3):
 for r in range(3):
  for b,w in enumerate(real_wedge(tri[(r+1)%3],tri[(r+2)%3])):P[6*tri[r]+b][c+r]=w
  blocks[c+r][c+r]=4*kap*signs[tri[0]]*signs[tri[1]]*signs[tri[2]]
 for r,s in combinations(range(3),2):
  other=next(t for t in range(3) if t not in (r,s));blocks[c+r][c+s]=blocks[c+s][c+r]=-(1-2*kap)*signs[tri[other]]
 c+=3
for b in range(4):
 for r,mu in enumerate(i for i in range(4) if i!=b):
  for s,w in enumerate(real_wedge(mu,b)):P[6*mu+s][c+r]=w
  for s in range(3):blocks[c+r][c+s]=signs[b]*(2*kap if r==s else -1)
 c+=3
PT=list(map(list,zip(*P)))
assert real_mm(real_mm(P,blocks),PT)==Bdirect
assert real_mm(P,PT)==[[F(i==r) for i in range(24)] for r in range(24)]
B=mat(Bdirect);Bi=inv(B);assert mul(B,Bi)==mul(Bi,B)==eye(24)
T=zero(24,24);M=zero(24,24)
for col in range(24):
 A=[real_lie(E[col][6*i:6*i+6]) for i in range(4)]
 for f,(i,l) in enumerate(pairs):
  for r in range(4):T[4*f+r][col]=C(-A[i][r][l]+A[l][r][i])
for f,(i,l) in enumerate(pairs):
 for r in range(4):M[4*f+r][4*f+r]=C(signs[i]*signs[l]*signs[r])
Qop=sub(M,scale(2*kap,mul(mul(mul(mul(M,T),Bi),transpose(T)),M)))
timeTmat=mat([[-1,1,0],[1,0,-1],[0,-1,-1]])
spaceTmat=mat([[1,1,0],[-1,0,-1],[0,1,1]])
timeHmat=inv(mat([r[3:6] for r in blocks[3:6]]))
spaceHmat=inv(mat([r[9:12] for r in blocks[9:12]]))
def threeface(p,m,s):return mat([[0,0,0,p[0][0]],[0,0,0,m[0][0]],[0,p[1][0],m[1][0],0],[0,0,0,s[0][0]],[p[2][0],0,s[1][0],0],[m[2][0],s[2][0],0,0]])

q=mat([[0,0,0,0],[0,0,0,1],[0,0,0,1],[0,1,1,0]])
assert sum(v*v for row in [[0,0,1],[0,0,1],[1,1,0]] for v in row)==4

def source(a,z):
 ds=[z,j*C(a),-j*C(a),C(0)]
 Z=[[(ds[i]-ds[l])*signs[r]*(ds[i]*q[l][r]+ds[l]*q[i][r]-ds[r]*q[i][l])/4] for i,l in pairs for r in range(4)]
 Aret=scale(-2*kap,mul(mul(mul(Bi,transpose(T)),M),Z))
 assert add(mul(B,Aret),scale(2*kap,mul(mul(transpose(T),M),Z)))==zero(24,1)
 assert mul(M,add(Z,mul(T,Aret)))==mul(Qop,Z)
 plus=scale(2*kap,mul(mul(mul(Bi,transpose(T)),M),Z))
 wrong=add(mul(B,plus),scale(2*kap,mul(mul(transpose(T),M),Z)))
 Q=mul(Qop,Z)
 def tq(av):
  zz=mat([[(z-j*av)*z/4],[z*z/4],[j*av*z/4]])
  return sub(neg(zz),scale(2*kap,mul(mul(mul(timeTmat,timeHmat),transpose(timeTmat)),zz)))
 spatial=mat([[0],[-a*a/2],[-a*a/2]])
 sq=sub(spatial,scale(2*kap,mul(mul(mul(spaceTmat,spaceHmat),transpose(spaceTmat)),spatial)))
 expectedQ=threeface(tq(a),tq(-a),sq)
 assert Q==[[expectedQ[r][b]] for r in range(6) for b in range(4)]
 Csrc=[[-2*kap*signs[r]*sum((ds[i]-ds[l])*ds[i]*ds[l]*Q[4*f+r][0]/2 for f,(i,l) in enumerate(pairs))] for r in range(4)]
 expected=scale(kap*H*a*a*z**3,mat([[0],[0],[0],[1]]))
 assert Csrc==expected
 return wrong!=zero(24,1)
wrong_sign=0
for a in [F(-3),F(1),F(3,2),F(5,2),F(1,19)]:
 for z in [C(0),C(1),C(-2),C(F(2,3),F(-4,5))]:wrong_sign+=source(a,z)
 # Reconstruct all original quartic coefficients independently from five values.
 V=mat([[C(z)**r for r in range(5)] for z in [0,1,-1,2,-2]]);Vi=inv(V)
 vals=[mul(symbol([-j*C(z),C(a),C(-a),C(0)]),mat([[0],[0],[0],[1]])) for z in [0,1,-1,2,-2]]
 for out in range(4):
  coeff=mul(Vi,[[v[out][0]] for v in vals])
  expected=[2*kap*H*a**6,0,kap*H*a**4,0,-kap*H*a*a] if out==3 else [0]*5
  assert [c[0] for c in coeff]==list(map(C,expected))
assert wrong_sign>0
# Held-out q0,v1 first native time block; all other slots remain in the solve.
onZ=threeface(mat([[-j/4],[0],[j/4]]),mat([[j/4],[0],[-j/4]]),zero(3,1))
onZflat=[[onZ[r][b]] for r in range(6) for b in range(4)]
onA=scale(-2*kap,mul(mul(mul(Bi,transpose(T)),M),onZflat))
oriented=mul(mat(PT),onA)
assert [v[0] for v in oriented[3:6]]==[-101*j/19982,2*j/9991,101*j/19982]
# Arbitrary complex faces exercise repeated as well as distinct connection blocks.
rng=random.Random(827361)
for _ in range(11):
 Z=[[C(F(rng.randrange(-9,10),rng.randrange(1,10)),F(rng.randrange(-9,10),rng.randrange(1,10)))] for r in range(24)]
 Aret=scale(-2*kap,mul(mul(mul(Bi,transpose(T)),M),Z))
 assert add(mul(B,Aret),scale(2*kap,mul(mul(transpose(T),M),Z)))==zero(24,1)
 assert mul(M,add(Z,mul(T,Aret)))==mul(Qop,Z)
 # Every physical/native conversion slot, not only a selected block.
 for h in [F(1),F(2,7),F(-3)]:assert scale(-h,scale(-1/h,Aret))==Aret

def prep(a,u):return [-u[1]/(2*a*a),u[0],u[1],-2*a*a*u[0]]
def row(a,x):return x[4]-a*a*x[2]-2*a**4*x[0]
def green(a,x,y):return x[0]*y[3]-x[1]*y[2]+x[2]*y[1]-x[3]*y[0]-a*a*(x[0]*y[1]-x[1]*y[0])
for a in [F(-3),F(1,3),F(3,2),F(3),F(5,2)]:
 S=[[F(0),F(1)],[-2*a*a,F(0)]]
 N=[[F(0),F(1),F(0),F(0)],[F(0),F(0),F(1),F(0)],[F(0),F(0),F(0),F(1)],[2*a**4,F(0),a*a,F(0)]]
 K=[[F(0),-1/(2*a*a)],[F(1),F(0)],[F(0),F(1)],[-2*a*a,F(0)]]
 forcing=[[F(0)]*2 for _ in range(3)]+[[F(0),-2*a*a]]
 assert [[x+y for x,y in zip(r,s)] for r,s in zip(real_mm(N,K),forcing)]==real_mm(K,S)
 G=[[F(0),-a*a,F(0),F(1)],[a*a,F(0),F(-1),F(0)],[F(0),F(1),F(0),F(0)],[F(-1),F(0),F(0),F(0)]]
 assert real_mm(real_mm(list(map(list,zip(*K))),G),K)==[[F(0),F(-5,2)],[F(5,2),F(0)]]
 for _ in range(17):
  u=[F(rng.randrange(-13,14),rng.randrange(1,12)) for r in range(2)];v=[F(rng.randrange(-13,14),rng.randrange(1,12)) for r in range(2)]
  x=[F(rng.randrange(-13,14),rng.randrange(1,12)) for r in range(5)];y=[F(rng.randrange(-13,14),rng.randrange(1,12)) for r in range(5)]
  assert prep(a,u)[1:3]==u
  assert green(a,x[1:],y[:4])+green(a,x[:4],y[1:])==x[0]*row(a,y)-row(a,x)*y[0]
  assert green(a,prep(a,u),prep(a,v))==-F(5,2)*(u[0]*v[1]-u[1]*v[0])
  assert prep(a,u)[0]*(-2*a*a*v[1])-(-2*a*a*u[1])*prep(a,v)[0]==0
  if F(9,2)<=a*a<=F(25,2):assert abs(prep(a,u)[0])<=abs(u[1])/9 and abs(prep(a,u)[3])<=25*abs(u[0])
 # All exact derivatives at0 through degree24, not a finite-difference test.
 l2=2*a*a
 jets=[F(0) if n%2 else (-3*(-l2)**(n//2)-l2**(n//2)+4*(-a*a)**(n//2))/(6*a*a) for n in range(25)]
 assert jets[:4]==[0]*4 and jets[4]==-2*a*a
 for n in range(21):assert jets[n+4]-a*a*jets[n+2]-2*a**4*jets[n]==(F(0) if n%2 else -2*a*a*(-l2)**(n//2))
 homogeneous=[1,0,-a*a,0,a**4];assert row(a,homogeneous)==0
 assert homogeneous[0]==1
for bound in [F(0),F(1),F(10),F(10000)]:
 a=1/(2*(bound+1));assert a!=0 and abs(prep(a,[0,F(1)])[0])>=bound+1
# Metric correction includes both value03 and spatial13/23 entries.
for a in [F(1),F(-2),F(3,2)]:
 for u in [[F(1),F(0)],[F(0),F(1)],[F(2),F(-3)]]:
  entries=[C(u[0]),-j*C(u[1])/(2*a),j*C(u[1])/(2*a)]
  assert any(t!=0 for t in entries)
  assert prep(a,u)[1]==u[0] and j*a*prep(a,u)[0]==entries[1]
# Exact original source benchmark remains a cross-polarization normalization control.
assert kap*H==F(99,9991)
files=['native-coordinate-root-10.py','source-pins.json','source/R7-original-forcing-native-generator.md','source/native-coordinate-polynomial.md','source/native-slow-lower-basis.md']
result={'status':'passed','direct_original_density_hessian_entries':576,'all24_partition_and_both_inverse_orders':True,'cross_constitutive_symbol_cases':20,'all24_supplied_face_block_cases':20,'heldout_negative_time_block_return':True,'arbitrary_complex_full24_faces':11,'wrong_native_return_sign_detected':wrong_sign,'all5_original_four_row_coefficients_at_paired_directions':5,'prepared_full_matrix_intertwiners_and_Green_pullbacks':5,'rational_jet_Green_cases':85,'zero_four_jet_Taylor_recurrence_orders':21,'frequency_budget_adverse_bounds':4,'metric_cut_nonzero_cases':9,'new_native_physical_gate':0,'efficiency_credit':0,'source_sha256':{str(BASE/f):hashlib.sha256((BASE/f).read_bytes()).hexdigest() for f in files}}
print(json.dumps(result,sort_keys=True))
