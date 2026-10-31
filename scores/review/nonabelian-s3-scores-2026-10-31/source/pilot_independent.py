from fractions import Fraction as F
from itertools import product
import json,hashlib
from pathlib import Path
# Scalar-entry criterion even in a ring with zero divisors.
count=0
for mod in [4,6]:
 for a,b,c,d in product(range(mod),repeat=4):
  if (a*d-b*c)%mod!=1:continue
  for A,B,C,D in product(range(mod),repeat=4):
   equations=((A*c-C*a)%mod==0 and (A*d-C*b)%mod==1 and (B*c-D*a)%mod==mod-1 and (B*d-D*b)%mod==0)
   assert equations==((A,B,C,D)==(a,b,c,d))
  count+=1
# Direct circular field update and processing, independently of matrix checker.
def lap(a,m):return [(2*a[i]-a[(i+1)%len(a)]-a[(i-1)%len(a)])%m for i in range(len(a))]
def tick(s,m):
 a,e=s;l=lap(a,m);ep=[(x+y)%m for x,y in zip(e,l)]
 return ([(x-y)%m for x,y in zip(a,ep)],ep)
def shift(v,n):return [v[(i+n)%len(v)] for i in range(len(v))]
def proc(s):return (shift(s[0],1),shift(s[1],-1))
def iproc(s):return (shift(s[0],-1),shift(s[1],1))
def processed(s):return proc(tick(iproc(s),3))
def omega(v,w,m):return sum(a*e-b*c for a,b,c,e in zip(v[0],v[1],w[0],w[1]))%m
v=([1,0,0,0,0],[0]*5);w=([0,1,0,0,0],[0]*5)
assert omega(v,w,3)==0 and omega(processed(v),processed(w),3)==2
basis=[]
for k in range(10):
 z=[0]*10;z[k]=1;basis.append((z[:5],z[5:]))
for v in basis:
 for w in basis:assert omega(tick(v,3),tick(w,3),3)==omega(v,w,3)
def reading(s):return [((s[0][(i+2)%4]-s[0][i])%8,s[1][i]) for i in [0,2]]
z=([0]*4,[0]*4);h=([0,1,0,0],[0]*4)
assert reading(z)==reading(h)==[(0,0),(0,0)]
assert reading(tick(h,8))==[(0,7),(0,7)] and reading(tick(z,8))==[(0,0),(0,0)]
# D3 model of S3, avoiding the author's permutation tables.
G=list(product(range(3),range(2)));unit=(0,0)
def mul(a,b):return ((a[0]+(-1)**a[1]*b[0])%3,(a[1]+b[1])%2)
def inverse(a):return ((-(-1)**a[1]*a[0])%3,a[1])
def conj(g,a):return mul(mul(g,a),inverse(g))
def comm(a,b):return mul(mul(mul(a,b),inverse(a)),inverse(b))
states=list(product(G,repeat=2));idx={s:i for i,s in enumerate(states)};N=len(states)
def electric(v,axis):
 return [sum(v[idx[(g,b) if axis==0 else (a,g)]] for g in G)/3-v[idx[a,b]] for a,b in states]
def curvature(v):return [x*(1 if comm(a,b)==unit else -1) for x,(a,b) in zip(v,states)]
def U(v,K=True):return electric(electric(curvature(v) if K else v,0),1)
def gauge(v,g):
 out=[F(0)]*N
 for x,(a,b) in zip(v,states):out[idx[conj(g,a),conj(g,b)]]=x
 return out
rawbasis=[[F(i==j) for i in range(N)] for j in range(N)]
columns=[]
for e in rawbasis:
 assert electric(electric(e,0),0)==electric(electric(e,1),1)==curvature(curvature(e))==e
 for g in G:
  for gate in [lambda x:electric(x,0),lambda x:electric(x,1),curvature]:assert gate(gauge(e,g))==gauge(gate(e),g)
 columns.append(U(e))
for i in range(N):
 for j in range(N):assert sum(a*b for a,b in zip(columns[i],columns[j]))==int(i==j)
orbits={frozenset((conj(g,a),conj(g,b)) for g in G) for a,b in states};assert len(orbits)==11
noncomm=[comm(a,b)!=unit for a,b in states];assert sum(noncomm)==18
# Verify the invariant subspace directly in an orbit basis with its correct weighted Gram.
phys=[list(map(lambda s:F(s in orbit),states)) for orbit in orbits]
images=[U(v) for v in phys]
for v in images:
 for g in G:assert gauge(v,g)==v
for i in range(11):
 for j in range(11):assert sum(a*b for a,b in zip(images[i],images[j]))==sum(a*b for a,b in zip(phys[i],phys[j]))
source=frozenset((unit,conj(g,(0,1))) for g in G);assert len(source)==3
psi=[F(s in source) for s in states];out=U(U(psi));free=U(U(psi,False),False)
norm=sum(x*x for x in psi);assert sum(x*x for x in out)==norm==3
p=sum(x*x for x,b in zip(out,noncomm) if b)/norm;pfree=sum(x*x for x,b in zip(free,noncomm) if b)/norm
assert p==F(32,81) and pfree==0
print(json.dumps({'status':'passed','scalar_det_one_controls_Z4_Z6':count,'five_site_Weyl_pairing':[0,2],'coarse_C8_hidden_next_electric':[7,7],'raw_S3_states':N,'physical_orbits':11,'noncommuting_raw_pairs':18,'all3_gates_individually_covariant':True,'all_raw_orthogonality_and_weighted_physical_columns':True,'physical_two_tick_probability':str(p),'without_curvature':str(pfree),'production_approvals_changed':False}))
