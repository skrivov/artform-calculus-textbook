"""Exact root replay; distinct review remains required. Stdlib only."""
from fractions import Fraction as Q
from pathlib import Path
import hashlib,json

def add(a,b):return [[x+y for x,y in zip(ar,br)] for ar,br in zip(a,b)]
def neg(a):return [[-x for x in ar] for ar in a]
def sub(a,b):return add(a,neg(b))
def mul(a,b):return [[sum(a[i][k]*b[k][j] for k in range(len(b))) for j in range(len(b[0]))] for i in range(len(a))]
def scale(c,a):return [[c*x for x in ar] for ar in a]
def eye(n):return [[Q(i==j) for j in range(n)] for i in range(n)]
def power(a,n):
 r=eye(len(a))
 for _ in range(n):r=mul(r,a)
 return r

def tt(x,y):return [[x,-(10*x+13*y)/4,(8*x+13*y)/6],[-(10*x+13*y)/4,y,(10*x+5*y)/12],[(8*x+13*y)/6,(10*x+5*y)/12,-x-y]]
def force(k,q):return -sum(x*x for x in k)*sum(k[i]*q[i][i] for i in range(3))/202
cases=0
for x in map(Q,range(-3,4)):
 for y in map(Q,range(-3,4)):
  q=tt(x,y);k=list(map(Q,[1,2,3]));v=force(k,q)
  assert all(q[i][j]==q[j][i] for i in range(3) for j in range(3))
  assert sum(q[i][i] for i in range(3))==0
  assert all(sum(q[i][j]*k[j] for j in range(3))==0 for i in range(3))
  assert v==Q(84,505)*q[1][2]==Q(7,101)*(q[0][0]-q[2][2])
  assert v==Q(14,101)*x+Q(7,101)*y
  cases+=1
q=[[Q(n,105) for n in ar] for ar in [[68,-74,20],[-74,-43,40],[20,40,-25]]]
assert force(list(map(Q,[1,2,4])),q)==Q(59,505)
assert sum(x*x for ar in q for x in ar)==2
p=[[Q(1),Q(0)],[Q(0),Q(0)]];a=[[Q(1),Q(2)],[Q(3),Q(4)]];qcomp=sub(eye(2),p)
def off(n):return mul(mul(qcomp,power(a,n)),p)
d=mul(mul(qcomp,a),qcomp);b=off(1)
for n in range(8):assert off(n+1)==add(mul(d,off(n)),mul(mul(b,power(a,n)),p))
# Same quadratic identity with a genuinely non-nilpotent coordinate block N=I.
s=[[Q(0),Q(1)],[-Q(14),Q(0)]];f=[[Q(36,505),Q(0)]]
k=scale(-Q(1,15),add(mul(f,s),f))
assert sub(mul(k,s),k)==f
# Arbitrary repair changes its head as well; both inverse equations restore the same image.
e=[[Q(1)],[Q(0)]];delta=[[Q(1,3)],[Q(1,4)]];j=[[Q(3,4)]]
normalized=mul(add(e,delta),j)
assert normalized==[[Q(1)],[Q(3,16)]]
assert mul(normalized,[[Q(4,3)]])==add(e,delta)
# A zero time step always preserves the chosen subspace although its generator can leak.
leak=[[Q(0),Q(0)],[Q(1),Q(0)]]
assert mul(mul(qcomp,eye(2)),p)==[[0,0],[0,0]]
assert mul(mul(qcomp,leak),p)!=[[0,0],[0,0]]
# Authenticate every original/snapshot pair without recursive archive traversal.
rdir=Path(__file__).resolve().parent;root=rdir.parents[3]
pins=json.loads((rdir/'source-pins.json').read_text());source_checks=0
for item in pins['sources']:
 raw=(root/item['original']).read_bytes();snap=(rdir/item['snapshot']).read_bytes()
 assert raw==snap and len(raw)==item['bytes'] and hashlib.sha256(raw).hexdigest()==item['sha256']
 source_checks+=1
out={'status':'passed','TT_inputs':cases,'heldout_force':'59/505','full_tensor_square':2,'noncommutative_projection_recursions':8,'non_nilpotent_Sylvester':True,'two_sided_head_reparameterization':True,'zero_step_adverse_case':True,'source_pairs':source_checks,'cost':'specified literal3scales2adds versus original full-TT one-scale output; no historical/runtime saving'}
(rdir/'r7-root-replay-08.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
