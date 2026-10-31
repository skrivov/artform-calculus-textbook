#!/usr/bin/env python3
"""Independent12 original-action isotropic finite-boundary source replay.
Standalone stdlib: no root evaluator, prior helper, /tmp or production imports.
Source transcription includes both diagonal transports, curvature H-H^-1,
exponential-link contacts, coframe determinant and both inverse metrics.
Reviewer provided conceptual advice; authored no production Lean.
"""
from fractions import Fraction as F
import itertools,json
class J:
 def __init__(s,v=0):s.d={k:F(x) for k,x in (v.d if isinstance(v,J) else v if isinstance(v,dict) else {(0,0):v}).items() if x}
 def __add__(s,o):
  o=J(o);d=s.d.copy()
  for k,x in o.d.items():d[k]=d.get(k,F(0))+x
  return J(d)
 __radd__=__add__
 def __neg__(s):return J({k:-v for k,v in s.d.items()})
 def __sub__(s,o):return s+-J(o)
 def __rsub__(s,o):return J(o)+-s
 def __mul__(s,o):
  o=J(o);d={}
  for (i,j),x in s.d.items():
   for (k,l),y in o.d.items():
    if i+k+j+l<=3 and j+l<=1:d[i+k,j+l]=d.get((i+k,j+l),F(0))+x*y
  return J(d)
 __rmul__=__mul__
 def __truediv__(s,o):return s*F(1,o)
 def __bool__(s):return bool(s.d)
 def coeff(s,i,j=0):return s.d.get((i,j),F(0))
 def __repr__(s):return str(s.d)
eps=J({(1,0):1});delta=J({(0,1):1});zero=J(0)
def eye():return [[J(i==j) for j in range(4)] for i in range(4)]
def plus(a,b):return [[x+y for x,y in zip(r,s)] for r,s in zip(a,b)]
def scale(v,a):return [[v*x for x in r] for r in a]
def mm(a,b):return [[sum(a[i][k]*b[k][j] for k in range(4)) for j in range(4)] for i in range(4)]
def tr(a):return list(map(list,zip(*a)))
def exp(a):
 ans=eye();term=eye()
 for n in range(1,4):term=scale(F(1,n),mm(term,a));ans=plus(ans,term)
 return ans
eta=lambda i:-1 if i==0 else 1
pairs=[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)];comps=[(2,3,1),(1,3,-1),(1,2,1),(0,3,1),(0,2,-1),(0,1,1)]
def lie(a):return [[J(x) for x in r] for r in ((0,a[0],a[1],a[2]),(a[0],0,a[5],-a[4]),(a[1],-a[5],0,a[3]),(a[2],a[4],-a[3],0))]
def wedge(u,v):return tuple(u[i]*v[j]-u[j]*v[i] for i,j in [(0,1),(0,2),(0,3),(2,3),(3,1),(1,2)])
star=lambda a:(-a[3],-a[4],-a[5],a[0],a[1],a[2])
bp=lambda a,b:sum(eta(0) *a[i]*b[i] if i<3 else a[i]*b[i] for i in range(6))
def det(a):
 ans=J(0)
 for p in itertools.permutations(range(4)):
  term=J((-1)**sum(p[i]>p[j] for i in range(4) for j in range(i+1,4)))
  for i in range(4):term=term*a[i][p[i]]
  ans+=term
 return ans

def action(q,testcoord=None):
 E=[];U=[];Ui=[]
 for t in range(3):
  e=plus(eye(),[[eps*q[t][4*i+j]+(delta if t==1 and 4*i+j==testcoord else 0) for j in range(4)] for i in range(4)]);E.append(e);u=[];ui=[]
  for i in range(4):
   a=plus(scale(eps,lie(q[t][16+6*i:22+6*i])),scale(delta,lie([F(t==1 and testcoord==16+6*i+j) for j in range(6)])));u.append(exp(a));ui.append(exp(scale(-1,a)))
  U.append(u);Ui.append(ui)
 ans=J(0)
 for t in range(2):
  shift=lambda i:t+(i==0)
  for r,(k,l) in enumerate(pairs):
   i,j,sign=comps[r];tk=shift(k);tl=shift(l);tkl=t+(k==0)+(l==0)
   # Every transport returns the endpoint coframe to the original base.
   transformed=[E[t],mm(Ui[t][k],E[tk]),mm(Ui[t][l],E[tl]),mm(mm(Ui[t][k],Ui[tk][l]),E[tkl]),mm(mm(Ui[t][l],Ui[tl][k]),E[tkl])]
   weights=[F(1,4),F(1,4),F(1,4),F(1,8),F(1,8)]
   bb=[sum(sign*w*wedge([e[a][i] for a in range(4)],[e[a][j] for a in range(4)])[c] for w,e in zip(weights,transformed)) for c in range(6)]
   hol=mm(mm(mm(Ui[t][l],Ui[tl][k]),U[tk][l]),U[t][k]);holinv=mm(mm(mm(Ui[t][k],Ui[tk][l]),U[tl][k]),U[t][l]);cur=scale(F(-1,2),plus(hol,scale(-1,holinv)));curb=[cur[0][1],cur[0][2],cur[0][3],cur[2][3],cur[3][1],cur[1][2]]
   ans+=bp(bb,star(curb))
  # Metric inverse from full coframe inverse; both factors and determinant retained.
  X=plus(E[t],scale(-1,eye()));ei=eye();power=eye()
  for n in range(1,4):power=mm(power,X);ei=plus(ei,scale((-1)**n,power))
  gi=[[sum(ei[i][a]*eta(a)*ei[j][a] for a in range(4)) for j in range(4)] for i in range(4)]
  tors=[]
  for i,j in pairs:
   a=mm(Ui[t][i],E[shift(i)]);b=mm(Ui[t][j],E[shift(j)]);tors.append([a[c][j]-E[t][c][j]-b[c][i]+E[t][c][i] for c in range(4)])
  value=J(0)
  for r,(i,j) in enumerate(pairs):
   for s,(k,l) in enumerate(pairs):
    value+=(gi[i][k]*gi[j][l]-gi[i][l]*gi[j][k])*sum(eta(a)*tors[r][a]*tors[s][a] for a in range(4))
  ans+=F(1,101)*det(E[t])*value
 return ans


jet_star=star
from dataclasses import dataclass
@dataclass(frozen=True)
class P:
    terms: tuple = ()

    def __init__(s, value=0):
        if isinstance(value, P):
            object.__setattr__(s, 'terms', value.terms)
            return
        d = value if isinstance(value, dict) else {0: F(value)}
        object.__setattr__(s, 'terms', tuple(sorted(((k, F(v)) for k, v in d.items() if v))))

    def __add__(s, o):
        o = P(o)
        d = dict(s.terms)
        for k, v in o.terms:
            d[k] = d.get(k, F(0)) + v
        return P(d)
    __radd__ = __add__

    def __neg__(s):
        return P({k: -v for k, v in s.terms})

    def __sub__(s, o):
        return s + -P(o)

    def __rsub__(s, o):
        return -s + o

    def __mul__(s, o):
        o = P(o)
        d = {}
        for i, a in s.terms:
            for j, b in o.terms:
                d[i + j] = d.get(i + j, F(0)) + a * b
        return P(d)
    __rmul__ = __mul__

    def __truediv__(s, o):
        o = P(o)
        assert len(o.terms) == 1
        k, v = o.terms[0]
        return P({i - k: a / v for i, a in s.terms})

    def __bool__(s):
        return bool(s.terms)

    def __pow__(s, n):
        if n < 0:
            assert len(s.terms) == 1
            k, v = s.terms[0]
            return P({k * n: v ** n})
        r = P(1)
        for _ in range(n):
            r = r * s
        return r

    def val(s, z):
        return sum((v * z ** k for k, v in s.terms), F(0))

    def __str__(s):
        return str(dict(s.terms))
x=P({1:1});co=(x+x**-1)/2;sh=(x-x**-1)/2
I=lambda:[[P(i==j) for j in range(4)] for i in range(4)]
mm=lambda a,b:[[sum(a[i][k]*b[k][j] for k in range(4)) for j in range(4)] for i in range(4)]
wedge=lambda u,v:[u[i]*v[j]-u[j]*v[i] for i,j in ((0,1),(0,2),(0,3),(2,3),(3,1),(1,2))]
def link(a,sign):
 M=I();M[0][0]=M[a][a]=co;M[0][a]=M[a][0]=sign*sh;return M
u=[I()]+[link(i,1) for i in range(1,4)];v=[I()]+[link(i,-1) for i in range(1,4)]
force=P(0)
for k,l,i,j,sign in [(1,2,0,3,1),(1,3,0,2,-1),(2,3,0,1,1)]:
 mats=[I(),v[k],v[l],mm(v[k],v[l]),mm(v[l],v[k])];weights=[F(1,4)]*3+[F(1,8)]*2
 bb=[sum(sign*w*wedge([M[a][i] for a in range(4)],[M[a][j] for a in range(4)])[c] for M,w in zip(mats,weights)) for c in range(6)]
 H=mm(mm(mm(v[l],v[k]),u[l]),u[k]);Hi=mm(mm(mm(v[k],v[l]),u[k]),u[l]);K=[-(H[a][b]-Hi[a][b])/2 for a,b in ((0,1),(0,2),(0,3),(2,3),(3,1),(1,2))];star=[-K[3],-K[4],-K[5],K[0],K[1],K[2]]
 val=sum((-1 if c<3 else 1)*bb[c]*star[c] for c in range(6));force+=val
print('curvature lapse force/a Laurent',dict(force.terms))

candidate=F(3,2)*sh*sh*(1+2*co-co*co)
assert not force-candidate

star=jet_star
# The isotropic first-order fixture, specified explicitly rather than read from root data.
q=[[F(0)]*40 for _ in range(3)]
for i in (5,10,15):q[1][i]=F(101,402);q[2][i]=F(1)
for i in (22,29,36):q[1][i]=F(-100,201)
actual=action(q,0)
assert actual.coeff(1,1)==0
assert all(action(q,i).coeff(1,1)==0 for i in range(40))
assert actual.coeff(2,1)==F(40501,53868)
assert all(action(q,i).coeff(2,1)==0 for i in (4,8,12))
# Exact lapse-force formula from the full forward torsion contraction:
# 3*kappa*a*((c-a)^2+2*(1-cosh(b))).
A=F(101,402);B=F(-100,201);kappa=F(1,101)
curvature_coefficient=3*B*B
torsion_coefficient=3*kappa*((1-A)**2-B*B)
assert curvature_coefficient==F(10000,13467)
assert torsion_coefficient==F(167,17956)
assert actual.coeff(2,1)==curvature_coefficient+torsion_coefficient
# Independently recover the torsion split by rerunning the literal full action
# with only that coupling disabled; no selected scalar force is substituted.
import inspect
curvature_globals=globals().copy()
curvature_action_source=inspect.getsource(action).replace('ans+=F(1,101)*det(E[t])*value','ans+=F(0)*det(E[t])*value')
exec(curvature_action_source,curvature_globals)
assert curvature_globals['action'](q,0).coeff(2,1)==curvature_coefficient
# Exact finite original density on the two incident cells, not just its jets.
def finite_action(N,a,c,C,S):
 frames=[[[F(i==j) for j in range(4)] for i in range(4)],[[N if i==j==0 else a if i==j else F(0) for j in range(4)] for i in range(4)],[[F(1) if i==j==0 else c if i==j else F(0) for j in range(4)] for i in range(4)]]
 def unit():return [[F(i==j) for j in range(4)] for i in range(4)]
 def boost(k,s):
  u=unit()
  if k:u[0][0]=u[k][k]=C;u[0][k]=u[k][0]=s
  return u
 U=[[unit() for k in range(4)],[boost(k,S) for k in range(4)],[unit() for k in range(4)]];V=[[unit() for k in range(4)],[boost(k,-S) for k in range(4)],[unit() for k in range(4)]]
 cell=[]
 for t in (0,1):
  shift=lambda k:t+(k==0);curvature=F(0)
  for r,(k,l) in enumerate(pairs):
   i,j,sign=comps[r];mats=[frames[t],mm(V[t][k],frames[shift(k)]),mm(V[t][l],frames[shift(l)]),mm(mm(V[t][k],V[shift(k)][l]),frames[t+(k==0)+(l==0)]),mm(mm(V[t][l],V[shift(l)][k]),frames[t+(k==0)+(l==0)])]
   weights=[F(1,4)]*3+[F(1,8)]*2;bb=[sum(sign*w*wedge([m[p][i] for p in range(4)],[m[p][j] for p in range(4)])[h] for w,m in zip(weights,mats)) for h in range(6)]
   H=mm(mm(mm(V[t][l],V[shift(l)][k]),U[shift(k)][l]),U[t][k]);Hi=mm(mm(mm(V[t][k],V[shift(k)][l]),U[shift(l)][k]),U[t][l]);K=[-(H[p][q]-Hi[p][q])/2 for p,q in ((0,1),(0,2),(0,3),(2,3),(3,1),(1,2))];curvature+=bp(bb,jet_star(K))
  E=frames[t];inverse=[F(1)/E[i][i] for i in range(4)];gi=[[eta(i)*inverse[i]**2 if i==j else F(0) for j in range(4)] for i in range(4)];tors=[]
  for k,l in pairs:
   p=mm(V[t][k],frames[shift(k)]);q=mm(V[t][l],frames[shift(l)]);tors.append([p[i][l]-E[i][l]-q[i][k]+E[i][k] for i in range(4)])
  value=sum((gi[i][k]*gi[j][l]-gi[i][l]*gi[j][k])*sum(eta(h)*tors[r][h]*tors[s][h] for h in range(4)) for r,(i,j) in enumerate(pairs) for s,(k,l) in enumerate(pairs));torsion=F(1,101)*E[0][0]*E[1][1]*E[2][2]*E[3][3]*value;cell.append((curvature,torsion))
 return cell
finite_checks=0
for N,a,c,t in [(F(1),F(7,5),F(11,8),F(1,5)),(F(3,2),F(7,5),F(11,8),F(-1,4)),(F(-2),F(9,7),F(5,3),F(1,7))]:
 C=(1+t*t)/(1-t*t);S=2*t/(1-t*t);cells=finite_action(N,a,c,C,S);base=finite_action(F(1),a,c,C,S);f=F(3,2)*S*S*(1+2*C-C*C);assert cells[0]==base[0]
 assert sum(sum(v) for v in cells)-sum(sum(v) for v in base)==(N-1)*a*f-3*F(1,101)*a*((c-a)**2/N-(c-a)**2+2*(N-1)*(C-1));finite_checks+=1
# Exact rational Cayley force factor and its analytic removable value at epsilon0.
class RF:
 def __init__(self,n=0,d=1):self.n=P(n);self.d=P(d)
 def __add__(self,o):
  if not isinstance(o,RF):o=RF(o)
  return RF(self.n*o.d+o.n*self.d,self.d*o.d)
 __radd__=__add__
 def __neg__(self):return RF(-self.n,self.d)
 def __sub__(self,o):return self+-o if isinstance(o,RF) else self+(-o)
 def __rsub__(self,o):return RF(o)+-self
 def __mul__(self,o):
  if not isinstance(o,RF):o=RF(o)
  return RF(self.n*o.n,self.d*o.d)
 __rmul__=__mul__
 def __truediv__(self,o):
  if not isinstance(o,RF):o=RF(o)
  return RF(self.n*o.d,self.d*o.n)
 def __rtruediv__(self,o):return RF(o)/self
 def __pow__(self,n):
  out=RF(1)
  for _ in range(n):out=out*self
  return out
 def __eq__(self,o):
  if not isinstance(o,RF):o=RF(o)
  return not self.n*o.d-o.n*self.d
 def value(self,e):return self.n.val(e)/self.d.val(e)
 def derivative0(self):
  n=dict(self.n.terms);d=dict(self.d.terms);return (n.get(1,F(0))*d.get(0,F(0))-n.get(0,F(0))*d.get(1,F(0)))/d[0]**2
 def removable0(self):
  mn=min(k for k,v in self.n.terms);md=min(k for k,v in self.d.terms);assert mn>=md
  return F(0) if mn>md else dict(self.n.terms)[mn]/dict(self.d.terms)[md]
e=RF(P({1:1}));t=F(-50,201)*e;CC=(1+t*t)/(1-t*t);SS=2*t/(1-t*t);aa=1+F(101,402)*e;cc=1+e;kappa=F(1,101)
force=aa*F(3,2)*SS*SS*(1+2*CC-CC*CC)+3*kappa*aa*((cc-aa)**2-2*(CC-1))
boostcoef=(CC+1)*(1+2*CC-CC*CC)/2-F(2,101);regular=3*aa*(2*F(50,201)**2/(1-t*t)*boostcoef+kappa*F(301,402)**2)
assert force==e*e*regular
assert (force/(e*e)).removable0()==regular.value(F(0))==F(40501,53868)
assert CC.derivative0()==0 and SS.derivative0()==F(-100,201)
assert aa.derivative0()==F(101,402) and cc.derivative0()==1
assert CC.value(F(1,100))==F(161605,161603) and SS.value(F(1,100))==F(-804,161603)
assert aa.value(F(1,100))==F(40301,40200) and cc.value(F(1,100))==F(101,100)
# Explicit positivity bound for u=C-1 in[0,1/2]; the formal all-real inequality is reviewed in Lean.
assert F(7,4)-F(2,101)>0
for N in (F(1),F(3,2),F(11,7),F(-2)):
 C=CC.value(F(1,100));S=SS.value(F(1,100));a=aa.value(F(1,100));c=cc.value(F(1,100));assert 1<=C<=F(3,2) and C*C-S*S==1
 f=F(3,2)*S*S*(1+2*C-C*C);derivative=a*f+3*kappa*a*((c-a)**2/N**2-2*(C-1));assert derivative>0
# An asymmetric independently found source-jet control, outside the formal isotropic claim.
qasym=[[F(0)]*40 for _ in range(3)];qasym[0][5]=1
for k,v in {5:F(30803,41004),10:F(-101,82008),15:F(-101,82008),22:F(10301,20502),29:F(-101,41004),36:F(-101,41004)}.items():qasym[1][k]=v
assert action(qasym,0).coeff(2,1)==F(77063,124542816)
import json
print(json.dumps(dict(source='standalone independent full nonlinear five-corner curvature and complete forward-torsion source',all40_owned_first_order_forces_zero=True,exact_isotropic_curvature_laurent_identity=True,both_incident_cells_finite_checks=finite_checks,full_determinant_two_inverse_metrics=True,cayley_tangent_boost='-100/201',cayley_tangent_scale='101/402',exact_cayley_force_factor=True,analytic_removable_value='40501/53868',exp_jet_curvature='10000/13467',exp_jet_torsion='167/17956',legal_positive_branch_witness='epsilon1/100,N=1,a=40301/40200,c=101/100,C=161605/161603,S=-804/161603',algebraic_nonzero_negative_lapse_control=True,scope='exact isotropic source/constraint and actual prepared rational curve; arbitrary40 nonlinear correction/nonextension remains unproved; no physical gravity selection'),indent=2))
