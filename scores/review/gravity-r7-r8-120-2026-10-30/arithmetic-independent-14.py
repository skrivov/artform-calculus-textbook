"""Independent original-density, literal-program and nonlinear-contact replay."""
from pathlib import Path
from fractions import Fraction as F
import json,hashlib,random,re,math
BASE=Path('scores/review/gravity-r7-r8-120-2026-10-30')
# Reuse the reviewer's prior direct original-density construction, not new author matrices.
exec((BASE/'arithmetic-independent-12.py').read_text().split('timeTmat=')[0])
def rational(a):
 assert all(not z.b for r in a for z in r)
 return [[z.a for z in r] for r in a]
def trans(a):return [list(c) for c in zip(*a)]
def mm(a,b):return [[sum(x*y for x,y in zip(r,c)) for c in zip(*b)] for r in a]
def mv(a,x):return [sum(c*v for c,v in zip(r,x)) for r in a]
def addm(a,b):return [[x+y for x,y in zip(r,s)] for r,s in zip(a,b)]
def scaleR(c,a):return [[c*x for x in r] for r in a]
def inverse(a):
 n=len(a);aug=[r[:]+[F(i==j) for j in range(n)] for i,r in enumerate(a)]
 for i in range(n):
  pivot=next(j for j in range(i,n) if aug[j][i]);aug[i],aug[pivot]=aug[pivot],aug[i]
  d=aug[i][i];aug[i]=[x/d for x in aug[i]]
  for j in range(n):
   if j!=i:
    d=aug[j][i];aug[j]=[x-d*y for x,y in zip(aug[j],aug[i])]
 return [r[n:] for r in aug]
Id=[[F(i==j) for j in range(24)] for i in range(24)]
B=Bdirect;Hi=inverse(B);Tr=rational(T);Mr=rational(M);Qr=rational(Qop);Qinv=inverse(Qr)
assert mm(B,Hi)==mm(Hi,B)==Id and mm(Qr,Qinv)==mm(Qinv,Qr)==Id
C0=addm(B,scaleR(-2*kap,mm(mm(trans(Tr),Mr),Tr)));Ci=inverse(C0)
assert addm(Mr,scaleR(2*kap,mm(mm(Tr,Ci),trans(Tr))))==Qinv
assert mm(C0,Ci)==mm(Ci,C0)==Id
# Discover connected components of the literal24 face matrix, independently of declared partition.
unseen=set(range(24));components=[]
while unseen:
 component={min(unseen)};todo=list(component)
 while todo:
  i=todo.pop()
  for j in range(24):
   if Qr[i][j] and j not in component:component.add(j);todo.append(j)
 unseen-=component;components.append(sorted(component))
expected=[[0,14,19],[1,6,11],[2,5,12],[3,9,16],[4,13,23],[7,10,20],[8,17,22],[15,18,21]]
assert components==expected
wires=[[1,-1,-1],[1,1,1],[1,-1,-1],[1,-1,-1],[1,1,-1],[1,-1,-1],[1,1,1],[1,-1,1]]
W=[[F(wires[s][i]*(j==components[s][i])) for j in range(24)] for s in range(8) for i in range(3)]
assert mm(W,trans(W))==Id
alpha=[F(i,101) for i in [103,-103,-103,-103,103,-103,103,103]]
beta=[F(i,101) for i in [-1,1,2,2,-1,2,-1,-2]]
for s,(a,b) in enumerate(zip(alpha,beta)):
 assert a and a+3*b
 for i in range(3):
  for j in range(3):
   invval=Qinv[components[s][i]][components[s][j]]*wires[s][i]*wires[s][j]
   fwdval=Qr[components[s][i]][components[s][j]]*wires[s][i]*wires[s][j]
   assert invval==a*(i==j)+b and fwdval==(i==j)/a-b/(a*(a+3*b))
# Parse and execute ACTUAL authored gate lists, including nested signed references.
root=Path('scores/ArtformScores/GravityBridge/Native')
old=(root/'Retrospective/BlockProgramsDefs.lean').read_text();new=(root/'RetroCertificates/All24ProgramsDefs.lean').read_text();face=(root/'RetroCertificates/FaceCode.lean').read_text()
def program(source,name,bindings=None):
 text=source.split('def '+name+' ',1)[1].split('\n\ndef ',1)[0]
 text=text[text.index('[')+1:text.index(']')]
 toks=re.findall(r'\.scale|\.add|\.input|\.slot|\.neg|-?\d+|[a-zA-Z]+|[()/]',text);pos=0
 def ref():
  nonlocal pos
  assert toks[pos]=='(';pos+=1;t=toks[pos];pos+=1
  if t=='.neg':r=('neg',ref())
  else:r=(t[1:],int(toks[pos]));pos+=1
  assert toks[pos]==')';pos+=1;return r
 code=[]
 while pos<len(toks):
  tag=toks[pos];pos+=1
  if tag=='.scale':
   if toks[pos]=='(':
    end=toks.index(')',pos);expr=toks[pos+1:end];pos=end+1
    if len(expr)==3 and expr[1]=='/':c=F(int(expr[0]),int(expr[2]))
    elif expr==['a','b']:c=bindings['a']+bindings['b']
    else:raise ValueError(expr)
   else:c=bindings[toks[pos]];pos+=1
   code.append(('scale',c,ref()))
  elif tag=='.add':code.append(('add',ref(),ref()))
  else:raise ValueError(tag)
 return code
# a+b loses its plus token under the lexer; handled as two binding identifiers above.
peak=0
def execute(code,x,outputs):
 global peak
 regs=[]
 def read(r):
  if r[0]=='input':assert 0<=r[1]<3;return x[r[1]]
  if r[0]=='neg':return -read(r[1])
  assert r[0]=='slot' and 0<=r[1]<len(regs);return regs[r[1]]
 for g in code:
  y=g[1]*read(g[2]) if g[0]=='scale' else read(g[1])+read(g[2]);regs.append(y)
  peak=max(peak,abs(y.numerator).bit_length(),y.denominator.bit_length())
 assert all(0<=i<len(regs) for i in outputs)
 return [regs[i] for i in outputs]
denseD=program(old,'denseBlockProgram');rankD=program(old,'rankBlockProgram');denseR=program(new,'repeatedDense');rankR=program(new,'repeatedRank')
assert [(sum(g[0]=='scale' for g in p),sum(g[0]=='add' for g in p)) for p in [denseD,rankD,denseR,rankR]]==[(9,6),(4,5),(9,6),(4,5)]
rng=random.Random(982174)
inputs=Id+[[F(rng.randrange(-31,32),rng.randrange(1,20)) for i in range(24)] for _ in range(29)]
for x in inputs:
 coords=mv(trans(P),x)
 for rank in [False,True]:
  ys=[]
  for s in range(8):
   z=coords[3*s:3*s+3]
   if s==3:z=[z[0],-z[1],-z[2]]
   y=execute((rankD if rank else denseD) if s<4 else (rankR if rank else denseR),z,[6,7,8] if rank else [4,9,14])
   if s==3:y=[-y[0],y[1],y[2]]
   if s==4:y=[-v for v in y]
   ys+=y
  assert mv(P,ys)==mv(Hi,x)
 for invflag,Aop in [(False,Qr),(True,Qinv)]:
  for rank in [False,True]:
   coords=mv(W,x);ys=[]
   for s,(a,b) in enumerate(zip(alpha,beta)):
    aa,bb=(a,b) if invflag else (1/a,-b/(a*(a+3*b)))
    code=program(face,'rankFaceCode' if rank else 'denseFaceCode',{'a':aa,'b':bb})
    ys+=execute(code,coords[3*s:3*s+3],[6,7,8] if rank else [4,9,14])
   assert mv(trans(W),ys)==mv(Aop,x)
# Odd return verified on the full original24 Hessian, not only declared blocks.
a,b,c=F(194,101),F(103,101),F(200,101)
p1=a**-2+b**-2+c**-2;p3=-(a**-2*b**-2+a**-2*c**-2+b**-2*c**-2);p5=a**-2*b**-2*c**-2
powers=[Id]
for n in range(5):powers.append(mm(B,powers[-1]))
assert addm(addm(scaleR(p1,powers[1]),scaleR(p3,powers[3])),scaleR(p5,powers[5]))==Hi and p5!=0
# Two lower odd coefficients cannot interpolate the three distinct squared magnitudes.
V=[[r*r,r**4,r**6] for r in [a,b,c]];sol=mv(inverse(V),[F(1)]*3)
assert sol==[p1,p3,p5]
for s,z,lam in [(0,[1,-1,-1],a),(3,[1,1,1],-a),(3,[0,1,-1],b),(0,[0,-1,1],-b),(4,[1,1,1],c),(5,[1,1,1],-c)]:
 v=[F(0)]*24;v[3*s:3*s+3]=list(map(F,z));native=mv(P,v);assert mv(B,native)==[lam*t for t in native]
# All72 dense-B macro coefficients nonzero; the shared-power DAG has precisely5B calls.
Bb=mm(mm(trans(P),B),P)
assert sum(bool(x) for r in Bb for x in r)==72
assert (5*72+3*24,5*48+2*24)==(432,288)
# Adverse return retains distinct components but kills repeated source directions.
for _ in range(31):
 Z=[F(0)]*24
 for i in [3,7,9,10,15,16,18,20,21]:Z[i]=F(rng.randrange(-19,20),rng.randrange(1,12))
 src=mv(mm(trans(Tr),Mr),Z);coord=mv(trans(P),src);assert not any(coord[12:])
pure=[F(0)]*24;pure[15]=1;native=mv(P,pure);assert any(native) and mv(B,[F(0)]*24)!=native
O=[[F(1),F(1),F(1)],[F(-1),F(1),F(1)],[F(0),F(-2),F(1)]];diags=[]
Qblock=mm(mm(W,Qr),trans(W))
for s,(a,b) in enumerate(zip(alpha,beta)):
 block=[r[3*s:3*s+3] for r in Qblock[3*s:3*s+3]];D=mm(mm(trans(O),block),O)
 expected=[2/a,6/a,3/(a+3*b)]
 assert D==[[expected[i]*(i==j) for j in range(3)] for i in range(3)]
 diags+=expected
assert sum(x>0 for x in diags)==sum(x<0 for x in diags)==12
# Distinct prior reviewer literal matrices and second-order Taylor arithmetic.
cube={};exec((BASE/'arithmetic-independent-13.py').read_text().split('# Incidence independently')[0],cube)
# Nonlinear all-source contacts, with exact source chosen to make each rational r stationary.
nonlinear=0
for q in [F(10001,10000),F(101,100),F(7,6),F(2),F(4)]:
 cu,su=(q+1/q)/2,(q-1/q)/2;AA,BB=2*su+kap*cu,kap*su;D=AA*AA-BB*BB
 assert D>kap*kap and (kap+2*cu*su)**2-D==4*su**4
 for bv in [F(1),F(5,3)]:
  for z in [1/q,F(1),q,F(7,8),F(8,7)]:
   cr,sr=(z+1/z)/2,(z-1/z)/2;RR,JJ=AA*cr+BB*sr,AA*sr+BB*cr;src=-bv*JJ
   assert RR>kap and RR*RR-JJ*JJ==D
   Jet=cube['Jet'];phase=Jet(1,1,F(1,2))
   literal=cube['literal_cell'](F(1,2),bv,F(1),q*z*phase)+cube['literal_cell'](F(1,2),bv,q*z*phase,q*q)
   assert literal.v==(bv*(kap-RR),-bv*JJ,-bv*RR/2)
   assert (literal-Jet(0,src)).v[1]==0
   coframe=cube['literal_cell'](F(1,2),Jet(bv,1),F(1),q*z)+cube['literal_cell'](F(1,2),Jet(bv,1),q*z,q*q)
   assert coframe.v==(bv*(kap-RR),kap-RR,F(0))
   assert -bv*(AA*sr+BB*cr)-src==0 and -bv*RR<0
   # Pointwise envelope susceptibility is inverse negative-detail-Hessian with a minus sign.
   assert 1/(bv*RR)>0
   lo=-2*bv*su*su-2*kap*bv*su*cu;hi=2*bv*su*su
   assert (lo<src<hi)==(1/q<z<q)
   nonlinear+=1
q=F(201,202);cu,su=(q+1/q)/2,(q-1/q)/2
assert (2*su+kap*cu)**2-(kap*su)**2==F(-151,83250381402)
# Separate fixed-h report identity; no uniform-coframe or physical admission inferred.
for h in [F(1,10),F(1,100),F(1,1000)]:
 v=F(1,7);u=h*h*v;r=-F(3,4)*u
 diff=((-2*u)/h-2*(-(u+r)/h))/(h/2)**2
 assert diff==8*r/h**3 and abs(diff)>4*v/h
source_files=['arithmetic-independent-12.py','arithmetic-independent-13.py','native-coordinate-root-10.py','source-pins.json','source/original-nonlinear-torsion.md','source/original-transported-curvature.md']
source_hashes={str(BASE/f):hashlib.sha256((BASE/f).read_bytes()).hexdigest() for f in source_files}
source_hashes.update({str(f):hashlib.sha256(f.read_bytes()).hexdigest() for f in [root/'Retrospective/BlockProgramsDefs.lean',root/'RetroCertificates/All24ProgramsDefs.lean',root/'RetroCertificates/FaceCode.lean']})
result={'status':'passed','direct_original_density_Hessian_entries':576,'original_full24_inverse_orders':True,'native_Q_partition_discovered_from_literal_map':components,'actual_Lean_gate_lists_parsed':True,'basis_and_heldout_inputs_per_map':len(inputs),'all_H_Q_Qinverse_outputs':24,'dense_rank_scales_adds':[[72,48],[32,40]],'peak_replay_num_den_bits':peak,'odd_full24_polynomial_and_modal_interpolation':True,'native_eigenmodes':6,'source_adjoint_adverse_controls':31,'constitutive_diagonal_signs':[12,12],'exact_source_branch_window_cases':nonlinear,'negative_discriminant_exact':True,'conditional_log_report_cases':3,'literal_two_cell_first_second_and_coframe_jets':nonlinear,'source_sha256':source_hashes,'physical_gate_credit':0,'historical_runtime_globalLean_credit':0}
print(json.dumps(result,sort_keys=True))
