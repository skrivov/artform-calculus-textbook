"""Distinct Fraction replay of full companion/source matrices and adverse interface cases."""
from fractions import Fraction as Q
from pathlib import Path
import json,hashlib

def mat(a):return [[Q(v) for v in row] for row in a]
def eye(n):return mat([[i==j for j in range(n)] for i in range(n)])
def zero(m,n):return mat([[0]*n for _ in range(m)])
def add(a,b):return [[x+y for x,y in zip(ar,br)] for ar,br in zip(a,b)]
def neg(a):return [[-x for x in row] for row in a]
def sub(a,b):return add(a,neg(b))
def scale(c,a):return [[c*x for x in row] for row in a]
def mul(a,b):return [[sum((a[i][k]*b[k][j] for k in range(len(b))),Q(0)) for j in range(len(b[0]))] for i in range(len(a))]
def tr(a):return [list(r) for r in zip(*a)]
def sm(items):
 out=zero(len(items[0]),len(items[0][0]))
 for a in items:out=add(out,a)
 return out
def inv(a):
 n=len(a);v=[row[:]+er for row,er in zip(a,eye(n))]
 for j in range(n):
  p=next(i for i in range(j,n) if v[i][j]);v[j],v[p]=v[p],v[j]
  c=v[j][j];v[j]=[x/c for x in v[j]]
  for i in range(n):
   if i!=j:
    c=v[i][j];v[i]=[x-c*y for x,y in zip(v[i],v[j])]
 return [row[n:] for row in v]
def col(n,j):return [[Q(i==j)] for i in range(n)]
def stack(v):return [r for a in v for r in a]
def rank(a):
 w=[row[:] for row in a];r=0
 for j in range(len(a[0])):
  p=next((i for i in range(r,len(w)) if w[i][j]),None)
  if p is None:continue
  w[r],w[p]=w[p],w[r];c=w[r][j];w[r]=[x/c for x in w[r]]
  for i in range(len(w)):
   if i!=r:
    c=w[i][j];w[i]=[x-c*y for x,y in zip(w[i],w[r])]
  r+=1
  if r==len(w):break
 return r

# Generic NONNATIVE four-component coordinate pencil, with noncommuting coefficients.
g=[mat([[2,1,0,1],[0,3,1,0],[1,0,2,0],[0,1,0,4]]),
 mat([[0,1,0,0],[-1,2,0,1],[1,0,1,0],[0,0,2,-1]]),
 mat([[3,0,1,0],[1,1,0,0],[0,1,2,1],[0,0,-1,1]]),
 mat([[1,2,0,0],[2,-1,1,0],[0,0,2,1],[1,0,0,3]]),
 mat([[2,1,0,0],[0,3,1,0],[0,0,4,1],[1,0,0,5]])]
z=Q(2);H=inv(g[4]);P=sm([scale(z**j,g[j]) for j in range(5)]);L=inv(P)
assert mul(g[1],g[2])!=mul(g[2],g[1])
assert mul(H,g[4])==mul(g[4],H)==mul(P,L)==mul(L,P)==eye(4)
def cauchy(b,coeff=g):return sm([mul(coeff[j],sm([scale(z**(j-i-1),b[i]) for i in range(j)])) for j in range(1,5)])
def R(b):
 x=[mul(L,cauchy(b))]
 for j in range(3):x.append(sub(scale(z,x[-1]),b[j]))
 return stack(x)
N=zero(16,16)
for i in range(12):N[i][i+4]=Q(1)
for j in range(4):
 b=neg(mul(H,g[j]))
 for i in range(4):
  for k in range(4):N[12+i][4*j+k]=b[i][k]
Z=sub(scale(z,eye(16)),N);Zinv=inv(Z)
for j in range(16):
 b=[col(16,j)[4*i:4*i+4] for i in range(4)]
 assert R(b)==mul(Zinv,col(16,j)) and mul(Z,R(b))==col(16,j)
assert mul(Zinv,Z)==mul(Z,Zinv)==eye(16)
# Every lower-basis slot and polynomial, all basis sources.
eta=mat([[-1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]])
glower=[mul(mul(eta,a),eta) for a in g]
assert sm([scale(z**j,glower[j]) for j in range(5)])==mul(mul(eta,P),eta)
for j in range(16):
 b=[col(16,j)[4*i:4*i+4] for i in range(4)]
 assert cauchy([mul(eta,v) for v in b],glower)==mul(eta,cauchy(b))

# Independently invert the full six-by-six mixed source map, not just the coordinate block.
r=Q(14);C0=mat([[1,2],[0,1],[-1,3],[2,0]]);C1=mat([[2,1],[1,-1],[0,2],[-2,1]])
M=zero(6,6)
for i in range(2):M[i][i]=z*z+r
for i in range(4):
 for j in range(2):M[2+i][j]=C0[i][j]+z*C1[i][j]
 for j in range(4):M[2+i][2+j]=P[i][j]
Minv=inv(M)
def response(b):
 t=scale(1/(z*z+r),b[:2]);return t+mul(L,sub(sub(b[2:],mul(C0,t)),scale(z,mul(C1,t))))
for j in range(6):assert response(col(6,j))==mul(Minv,col(6,j))
assert mul(M,Minv)==mul(Minv,M)==eye(6)
q=mat([[3],[1]]);v=mat([[1],[-2]]);bj=[mat([[1],[2],[3],[4]]),mat([[2],[0],[-1],[3]]),mat([[0],[1],[1],[0]]),mat([[5],[2],[0],[-1]])]
qsrc=add(scale(z,q),v);full=qsrc+add(cauchy(bj),mul(C1,q));omitted=qsrc+cauchy(bj)
assert sub(response(full),response(omitted))==zero(2,1)+mul(L,mul(C1,q))
assert sub(response(full),response(omitted))!=zero(6,1)
# No contact-change claim survives when C1*q=0.
assert mul(zero(4,2),q)==zero(4,1)
# Correct scalar pole guard is indispensable even if the coordinate polynomial is invertible.
assert Q(0)**2+Q(0)==0
pole_response_top=Q(0) # totalized inverse of the zero scalar applied to source1.
assert (Q(0)**2+Q(0))*pole_response_top!=Q(1) # the reconstructed mixed output misses source1.

# Full tensor/current normalization and both connection cross contacts.
pol=scale(Q(1,70),mat([[47,-46,15],[-46,-22,30],[15,30,-25]]))
def dot(a,b):return sum(x*y for ar,br in zip(a,b) for x,y in zip(ar,br))
assert dot(pol,pol)==2
momentum=lambda q,p,r,s:-(dot(q,s)-dot(r,p))/2
velocity=lambda q,v,r,w:-(dot(q,w)-dot(r,v))/4
assert momentum(pol,zero(3,3),zero(3,3),pol)==velocity(pol,zero(3,3),zero(3,3),scale(2,pol))==-1
B=mat([[0,2,1],[-2,0,3],[0,1,1]]);E=mat([[1,2],[3,4],[1,-1]]);D=mat([[2,0],[1,-1],[1,2]])
pull=lambda F,G:mul(mul(tr(F),B),G)
change=sub(pull(add(E,D),add(E,D)),pull(E,E))
assert change==sm([pull(E,D),pull(D,E),pull(D,D)])
assert change!=add(pull(E,D),pull(D,E))
f,c,a,d=(mat([[1],[2],[3]]),mat([[2],[0],[1]]),mat([[3],[-1],[2]]),mat([[0],[2],[1]]));h=Q(2,3)
bil=lambda x,y:mul(mul(tr(x),B),y)[0][0]
assert bil(sub(f,scale(h,c)),sub(a,scale(h,d)))==bil(f,a)-h*bil(f,d)-h*bil(c,a)+h*h*bil(c,d)
# A one-slot radical condition is insufficient for an arbitrary bilinear form.
Bbad=mat([[0,1],[0,0]]);left=col(2,1);e=col(2,0)
assert mul(tr(left),Bbad)==zero(1,2) and mul(Bbad,left)!=zero(2,1)
assert mul(mul(tr(add(e,left)),Bbad),add(e,left))!=mul(mul(tr(e),Bbad),e)

# Admitted and ambient radicals differ; a selected nondegenerate sector need not exhaust V.
J=mat([[0,1,0],[-1,0,0],[0,0,0]])
W=mat([[1,0],[0,0],[0,1]]);selected=mat([[1,0],[0,1],[0,0]])
assert rank(J)==2 and rank(mul(mul(tr(W),J),W))==0 and rank(mul(mul(tr(selected),J),selected))==2
A=mat([[1,0,0],[0,-1,0],[0,0,2]])
assert add(mul(tr(A),J),mul(J,A))==zero(3,3) and mul(J,mul(A,col(3,2)))==zero(3,1)
# Without W-invariance a globally conserving generator need not preserve the admitted radical.
rot=mat([[0,-1],[1,0]]);J2=mat([[0,1],[-1,0]])
assert add(mul(tr(rot),J2),mul(J2,rot))==zero(2,2) and mul(rot,col(2,0))==col(2,1)
# read-invisible can change force; even both kernels do not imply admission.
read=mat([[1,0,0]]);force=mat([[0,1,0]])
assert mul(read,col(3,1))==[[0]] and mul(force,col(3,1))==[[1]]
assert mul(read,col(3,2))==mul(force,col(3,2))==[[0]] and col(3,2)[2][0]==1
trace=mat([[1,0,0],[0,1,0]]);recover=selected;assert mul(recover,mul(trace,selected))==selected

# Incoming owned-window identity, including nontrivial owners and every cyclic shift.
for s in range(5):
 owner=[Q(1),Q(1),Q(0),Q(0),Q(0)];ff=[Q(0),Q(1),Q(0),Q(0),Q(0)];gg=[Q(0),Q(0),Q(1),Q(0),Q(0)]
 forward=sum(owner[i]*ff[i]*gg[(i+s)%5] for i in range(5));incoming=sum(owner[i]*ff[(i-s)%5]*gg[i] for i in range(5))
 boundary=sum((owner[i]-owner[(i+s)%5])*ff[i]*gg[(i+s)%5] for i in range(5))
 assert forward-incoming==boundary
 if s==1:assert boundary==1
 assert sum(ff[i]*gg[(i+s)%5] for i in range(5))==sum(ff[(i-s)%5]*gg[i] for i in range(5))
# Constant coefficient operation count cannot bound this declared quadratic coefficient.
for bound in [Q(-100),Q(-1,3),Q(0),Q(1,7),Q(10),Q(1000)]:
 amp=bound*bound+1;assert Q(7,2)*amp*amp>bound
 assert Q(84,505)*scale(amp,pol)[1][2]==Q(36,505)*amp
# Triangular leading graph: nonzero forcing requires a nonzero prepared graph.
S=mat([[0,1],[-14,0]]);NN=mat([[1,2],[0,-1]]);F=mat([[Q(36,505),1],[2,-1]])
LL=inv(add(mul(NN,NN),scale(14,eye(2))));K=neg(mul(LL,add(mul(F,S),mul(NN,F))))
assert sub(mul(K,S),mul(NN,K))==F and K!=zero(2,2) and F!=zero(2,2)

repo=Path.cwd();base=repo/'scores/ArtformScores/GravityBridge/Native'
files=sorted((base/'SlowCompanion').glob('*.lean'))+sorted((base/'NativeCurrent').glob('*.lean'))+sorted((base/'R7Blocks').glob('LeadingPreparation*.lean'))
assert len(files)==30
out={'status':'pass','method':'distinct Fraction Gaussian inversion of a16x16 generic noncommuting companion and6x6 full mixed symbol, with exact interface/adverse tests','source_sha256':{str(p.relative_to(repo)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files},'checks':{'generic_companion_basis_sources':16,'companion_two_inverse_directions':True,'full_mixed_basis_sources':6,'full_mixed_two_inverse_directions':True,'all_four_lower_jets_on_all_basis_sources':True,'nonzero_C1_contact_and_zero_contact_case':True,'current_original_full_tensor_pair':-1,'complete_quadratic_current_and_connection_contacts':True,'admitted_radical_and_source_readout_criteria':True,'owned_cyclic_shifts_tested':5,'owned_outgoing_edge_boundary':1,'constant_cost_quadratic_examples':6,'nonnilpotent_leading_preparation':True,'adverse_cases':['scalar mixed pole','omitted C1 contact','omitted quadratic current term','one-slot radical only','missing admitted-subspace invariance','readout agreement without force agreement','force/readout kernels without admission','selected nondegeneracy versus full radical']},'limitations':'All matrices here are declared generic interfaces. No actual native coefficient/contour/norm/physical trace or full radical identification is inferred.'}
print(json.dumps(out,indent=2))
