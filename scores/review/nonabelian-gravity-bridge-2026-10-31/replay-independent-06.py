#!/usr/bin/env python3
"""Independent exact matched-sector replay; reuses only prior reviewer arithmetic.
No production evaluator is imported. Reviewer supplied conceptual convention advice,
but authored none of the seven production Lean modules.
"""
import importlib.util
import json
import sys
from pathlib import Path
from functools import reduce
from itertools import permutations, product
from fractions import Fraction as F
spec=importlib.util.spec_from_file_location('review05',Path(__file__).with_name('replay-independent-05.py'))
a=importlib.util.module_from_spec(spec);sys.modules[spec.name]=a;spec.loader.exec_module(a)
q,mul,inv=a.quat,a.qmul,a.conjugate
one=q(1,0,0,0); basis=[q(0,1,0,0),q(0,0,1,0),q(0,0,0,1)]
r=a.RADIUS; z=a.ZERO; o=a.ONE
g=a.Group(one,mul,inv)
P=(q(r,r,0,0),q(r,0,r,0),q(r,0,0,r),q(r,0,-r,0))
U=(basis[0],basis[1],basis[2],basis[1]);state=U,P
out=lambda st:tuple(g.prod(inv(u),inv(p),u) for u,p in zip(*st))
assert out(state)==tuple(map(inv,P));assert g.moments(state)==(one,one)
assert all(a.norm(x)==o for row in state for x in row)
def edge(t,s):
 mat=[list(row) for row in a.identity(4)]
 mat[t][t]=mat[s][s]=0;mat[t][s]=1;mat[s][t]=-1
 return tuple(map(tuple,mat))
def seam(f):return tuple(tuple(F((-1 if i==f else 1) if i==j else 0) for j in range(4)) for i in range(4))
paths=(((3,2),(2,1),(1,3)),((3,0),(0,2),(2,3)),((3,1),(1,0),(0,3)),((3,1),(1,2),(2,0),(0,1),(1,3)))
loops=[reduce(a.mm,(edge(t,s) for t,s in path),a.identity(4)) for path in paths]
swap=(2,1,0,3)
for f in range(4):
 vertices=[v for v in range(4) if v!=f]
 target=[[sum(a.identity(4)[v][k]*a.identity(4)[w][k] for k in range(4)) for w in vertices] for v in vertices]
 source=[[sum(a.identity(4)[swap[swap[v]]][k]*a.identity(4)[swap[swap[w]]][k] for k in range(4)) for w in vertices] for v in vertices]
 assert tuple(map(tuple,target))==a.identity(3) and source==target
 sl=reduce(a.mm,(edge(swap[t],swap[s]) for t,s in paths[f]),a.identity(4))
 assert sl==tuple(zip(*loops[swap[f]]))
 A=seam(f) if f!=3 else a.mm(a.mm(edge(3,1),seam(3)),edge(1,3))
 R=tuple(tuple(-A[i][j] for j in range(3)) for i in range(3))
 assert a.det(R)==1
 for j in range(3):assert g.prod(U[f],basis[j],inv(U[f]))==q(0,*(R[i][j] for i in range(3)))
 for i in range(4):assert a.mv(seam(f),a.identity(4)[i])==tuple((-v if i==f else v) for v in a.identity(4)[i])
after=g.kick(state)
expected=(q(0,0,-r,-r),q(0,r,0,r),P[2],P[3]);assert after[1]==expected
assert g.moments(after)==(one,one)
n=(expected[0],expected[1],basis[2],tuple(-x for x in basis[1]))
def dot(x,y):return sum((u*v for u,v in zip(x[1:],y[1:])),z)
def gram(ns,p):
 special=dot(ns[1],g.prod(p,ns[3],inv(p)))
 return tuple(tuple(special if {i,j}=={1,3} else dot(ns[i],ns[j]) for j in range(4)) for i in range(4))
def determinant(M):
 value=z
 for perm in permutations(range(4)):
  v=a.Qr(F((-1)**sum(perm[i]>perm[j] for i in range(4) for j in range(i+1,4))))
  for i in range(4):v=v*M[i][perm[i]]
  value=value+v
 return value
cross=lambda x,y:(x[2]*y[3]-x[3]*y[2],x[3]*y[1]-x[1]*y[3],x[1]*y[2]-x[2]*y[1])
assert sum((x*y for x,y in zip(cross(n[0],n[2]),n[3][1:])),z)==z
assert determinant(gram(n,expected[0]))==a.Qr(F(-1,4))
for signs in product((1,-1),repeat=4):
 ns=tuple(tuple(x if s==1 else -x for x in v) for s,v in zip(signs,n))
 assert determinant(gram(ns,expected[0]))==a.Qr(F(-1,4))
 for h in (one,*basis,*P):
  hn=tuple(g.prod(h,v,inv(h)) for v in ns)
  assert gram(hn,g.prod(h,expected[0],inv(h)))==gram(ns,expected[0])
def drift(st,e,b=False):
 us,ps=st;us=list(us);us[e]=mul(inv(ps[e]) if b else ps[e],us[e]);return tuple(us),ps
trace=lambda st:g.prod(st[1][1],st[0][0],inv(st[0][1]))[0]
drifted=drift(state,0)
assert out(drifted)==out(state) and drifted[1]==P
assert all(a.norm(x)==o for row in drifted for x in row)
for h0,h1 in product((one,*basis,*P),repeat=2):
 assert trace(g.gauge((h0,h1),state))==trace(state)
 assert trace(g.gauge((h0,h1),drifted))==trace(drifted)
assert trace(state)==z and trace(drifted)==a.Qr(F(-1,2))
assert g.prod(drifted[0][0],basis[1],inv(drifted[0][0]))!=g.prod(U[0],basis[1],inv(U[0]))
# General drift identities independently reduced in the free group.
fg=a.Group((),lambda x,y:a.WORDS.word(x,y),a.WORDS.inverse)
raw=(tuple((i,) for i in range(1,5)),tuple((i,) for i in range(5,9)));h=((9,),(10,))
for e,b in product(range(4),(False,True)):
 def fd(st):
  us,ps=st;us=list(us);us[e]=fg.mul(fg.inv(ps[e]) if b else ps[e],us[e]);return tuple(us),ps
 aft=fd(raw)
 oq=lambda st:tuple(fg.prod(fg.inv(u),fg.inv(p),u) for u,p in zip(*st))
 assert oq(aft)==oq(raw) and aft[1]==raw[1]
 assert fg.moments(aft)==fg.moments(raw)
 assert fd(fg.gauge(h,raw))==fg.gauge(h,aft)
 us=list(aft[0]);us[e]=fg.mul(raw[1][e] if b else fg.inv(raw[1][e]),us[e])
 assert (tuple(us),aft[1])==raw
print(json.dumps({'coefficient_field':'Q(r), r^2=1/2','paired_full_face_Grams':4,'second_convexity_triple':'0','source_inverse_HHR_words':4,'seam_quaternion_actions':12,'unit_Gauss_fixture_and_kick':True,'corrected_kick_Gram_det':'-1/4','axis_sign_cases':16,'gauge_samples_per_sign':8,'free_group_signed_link_drift_cases':8,'mixed_trace':['0','-1/2'],'drift_violates_seam':True},indent=2))
