"""Exact root tests for F interfaces; no physical-domain or efficiency inference."""
from fractions import Fraction as Q
from pathlib import Path
import hashlib,json

def mat(a):return [[Q(v) for v in row] for row in a]
def eye(n):return [[Q(i==j) for j in range(n)] for i in range(n)]
def add(a,b):return [[x+y for x,y in zip(ar,br)] for ar,br in zip(a,b)]
def neg(a):return [[-x for x in ar] for ar in a]
def sub(a,b):return add(a,neg(b))
def scale(c,a):return [[c*x for x in ar] for ar in a]
def mul(a,b):return [[sum(a[i][k]*b[k][j] for k in range(len(b))) for j in range(len(b[0]))] for i in range(len(a))]
def transpose(a):return [list(r) for r in zip(*a)]
def inv(a):
 n=len(a);w=[ar[:]+ir for ar,ir in zip(a,eye(n))]
 for i in range(n):
  pivot=next(j for j in range(i,n) if w[j][i]);w[i],w[pivot]=w[pivot],w[i]
  w[i]=[v/w[i][i] for v in w[i]]
  for j in range(n):
   if j!=i:w[j]=[x-w[j][i]*y for x,y in zip(w[j],w[i])]
 return [ar[n:] for ar in w]
def sum_mat(items):
 result=scale(0,items[0])
 for a in items:result=add(result,a)
 return result

g=list(map(mat,[[[2,1],[0,3]],[[0,1],[-1,2]],[[3,0],[1,1]],[[1,2],[2,-1]],[[2,1],[1,3]]]))
z=Q(2);H=inv(g[4]);P=sum_mat([scale(z**i,g[i]) for i in range(5)]);L=inv(P)
assert mul(g[1],g[2])!=mul(g[2],g[1])
assert mul(g[4],H)==mul(H,g[4])==eye(2) and mul(P,L)==mul(L,P)==eye(2)
def cauchy(b,coeffs=g):
 return sum_mat([mul(coeffs[j],sum_mat([scale(z**(j-1-i),b[i]) for i in range(j)])) for j in range(1,5)])
def step(x):return x[1:]+[neg(mul(H,sum_mat([mul(g[i],x[i]) for i in range(4)])))]
def response(b):
 x0=mul(L,cauchy(b));x=[x0]
 for i in range(3):x.append(sub(scale(z,x[i]),b[i]))
 return x
# Independently form the8x8 companion and compare the full inverse on every basis source.
N=[[Q(0) for _ in range(8)] for _ in range(8)]
for i in range(6):N[i][i+2]=1
for j in range(4):
 block=neg(mul(H,g[j]))
 for i in range(2):
  for k in range(2):N[6+i][2*j+k]=block[i][k]
full_inverse=inv(sub(scale(z,eye(8)),N));tests=0
for column in range(8):
 b=[[[Q(2*i==column)],[Q(2*i+1==column)]] for i in range(4)]
 x=response(b);sx=step(x)
 assert all(sub(scale(z,x[i]),sx[i])==b[i] for i in range(4))
 assert [v[0] for block in x for v in block]==[full_inverse[i][column] for i in range(8)]
 tests+=1
# All4 jets and source contact undergo the same lower-coordinate basis change.
eta=mat([[-1,0],[0,1]]);b=[mat([[1],[2]]),mat([[3],[4]]),mat([[5],[6]]),mat([[7],[8]])]
assert cauchy([mul(eta,x) for x in b],[mul(mul(eta,a),eta) for a in g])==mul(eta,cauchy(b))
# Complete bilinear processing change retains the quadratic contact.
B=mat([[0,2],[-2,0]]);E=mat([[1,2],[3,4]]);D=mat([[2,0],[1,-1]])
pull=lambda F,G:mul(mul(transpose(F),B),G)
assert sub(pull(add(E,D),add(E,D)),pull(E,E))==sum_mat([pull(E,D),pull(D,E),pull(D,D)])
owner=lambda x:Q(x%5 in (0,1));f=lambda x:Q(x%5==1);h=lambda x:Q(x%5==2)
boundary=sum((owner(x)-owner(x+1))*f(x)*h(x+1) for x in range(5))
forward=sum(owner(x)*f(x)*h(x+1) for x in range(5));incoming=sum(owner(x)*f(x-1)*h(x) for x in range(5))
assert boundary==forward-incoming==1
assert [Q(7,2)*a*a for a in [1,2]]==[Q(7,2),Q(14)]
rdir=Path(__file__).resolve().parent;root=rdir.parents[3];pairs=0
for item in json.loads((rdir/'source-pins.json').read_text())['sources']:
 raw=(root/item['original']).read_bytes();assert raw==(rdir/item['snapshot']).read_bytes()
 assert len(raw)==item['bytes'] and hashlib.sha256(raw).hexdigest()==item['sha256'];pairs+=1
out={'status':'passed','full_noncommuting_companion_basis_tests':tests,'two_inverse_directions':True,'all_four_lower_basis_jets':True,'complete_current_quadratic_contact':True,'owned_corner':str(boundary),'constant_cost_energy_examples':['7/2','14'],'source_pairs':pairs,'new_physical_gate':0,'historical_or_runtime_saving':0}
(rdir/'source-interfaces-root-09.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
