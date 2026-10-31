#!/usr/bin/env python3
"""Independent original-action isotropic finite-boundary amplitude replay.
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
import json
print(json.dumps(dict(source='complete nonlinear equal-weight transported curvature plus forward torsion; unit-spacing amplitude chart',fixture='x=0,z=e5+e10+e15,y5=y10=y15=101/402,y22=y29=y36=-100/201',inactive0_force=str(actual.coeff(2,1)),curvature=str(curvature_coefficient),torsion=str(torsion_coefficient),other_inactive_forces_zero=True,all40_owned_first_order_force_zero=True,curvature_closed_formula='(3a/2)*sinh(b)^2*(1+2cosh(b)-cosh(b)^2)',torsion_lapse_action='-3*kappa*a*((c-a)^2/ell+2*(c-a)*sinh(b)+2*ell*(cosh(b)-1))',lapse_force='a*f(b)+3*kappa*a*((c-a)^2+2*(1-cosh(b)))',force_quadratic_coefficient='3*((1-kappa)*B^2+kappa*(1-A)^2)',scope='exact finite native two-cell amplitude-jet and isotropic scalar controls; arbitrary40 nonlinear nonextension is exploratory/unproved pending correction/Taylor/domain binding; no selected physical gravity dynamics'),indent=2))
