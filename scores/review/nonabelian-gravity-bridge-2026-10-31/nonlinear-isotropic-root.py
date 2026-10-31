"""Root scalar two-source jet of the pinned original nonlinear cut action."""
from fractions import Fraction as F
from pathlib import Path
from itertools import permutations
import json

class P:
 def __init__(self,x=0):self.d=x.copy() if isinstance(x,dict) else ({(0,0):F(x)} if x else {})
 @staticmethod
 def cast(x):return x if isinstance(x,P) else P(x)
 def __add__(self,o):
  o=P.cast(o);d=self.d.copy()
  for k,v in o.d.items():
   d[k]=d.get(k,F(0))+v
   if not d[k]:del d[k]
  return P(d)
 __radd__=__add__
 def __neg__(self):return P({k:-v for k,v in self.d.items()})
 def __sub__(self,o):return self+-P.cast(o)
 def __rsub__(self,o):return P.cast(o)+-self
 def __mul__(self,o):
  o=P.cast(o);d={}
  for (i,j),v in self.d.items():
   for (k,l),w in o.d.items():
    if i+j+k+l<=3 and j+l<=1:d[i+k,j+l]=d.get((i+k,j+l),F(0))+v*w
  return P({k:v for k,v in d.items() if v})
 __rmul__=__mul__
 def __truediv__(self,o):return self*F(1,o)
 def __bool__(self):return bool(self.d)

zero=lambda:[[P()for _ in range(4)]for _ in range(4)]
I=[[P(i==j)for j in range(4)]for i in range(4)]
eta=[-1,1,1,1]
add=lambda a,b:[x+y for x,y in zip(a,b)]
sub=lambda a,b:[x-y for x,y in zip(a,b)]
sc=lambda c,a:[c*x for x in a]
ma=lambda a,b:[add(r,s)for r,s in zip(a,b)]
ms=lambda c,a:[sc(c,r)for r in a]
tr=lambda a:list(map(list,zip(*a)))
mul=lambda a,b:[[sum((x*y for x,y in zip(r,c)),P())for c in zip(*b)]for r in a]
mv=lambda a,v:[sum((x*y for x,y in zip(r,v)),P())for r in a]
exp=lambda a:ma(ma(I,a),ma(ms(F(1,2),mul(a,a)),ms(F(1,6),mul(mul(a,a),a))))
def lie(a):return [[P(),a[0],a[1],a[2]],[a[0],P(),a[5],-a[4]],[a[1],-a[5],P(),a[3]],[a[2],a[4],-a[3],P()]]
def wedge(u,v):return [u[i]*v[j]-u[j]*v[i]for i,j in [(0,1),(0,2),(0,3),(2,3),(3,1),(1,2)]]
def star(a):return[-a[3],-a[4],-a[5],a[0],a[1],a[2]]
def bp(a,b):return sum(((-1 if i<3 else 1)*x*y for i,(x,y)in enumerate(zip(a,b))),P())
def ep(a,b):return sum((eta[i]*x*y for i,(x,y)in enumerate(zip(a,b))),P())
faces=[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
comp=[(2,3,1),(1,3,-1),(1,2,1),(0,3,1),(0,2,-1),(0,1,1)]
def det(a):
 result=P()
 for p in permutations(range(4)):
  term=P((-1)**sum(p[i]>p[j]for i in range(4)for j in range(i+1,4)))
  for i,j in enumerate(p):term*=a[i][j]
  result+=term
 return result

def action(first,test_site=None,test_coordinate=None,parts=False):
 E=[];U=[];Ui=[];Gi=[];De=[]
 for t,q in enumerate(first):
  a=[P({(1,0):F(x)})for x in q]
  if t==test_site:a[test_coordinate]+=P({(0,1):F(1)})
  f=[a[4*i:4*i+4]for i in range(4)]
  e=ma(I,f);E.append(tr(e));De.append(det(e))
  ei=ma(ma(I,ms(-1,f)),ma(mul(f,f),ms(-1,mul(mul(f,f),f))))
  Gi.append(mul(mul(ei,[[P(eta[i]if i==j else 0)for j in range(4)]for i in range(4)]),tr(ei)))
  u=[];ui=[]
  for k in range(4):
   l=lie(a[16+6*k:22+6*k]);u.append(exp(l));ui.append(exp(ms(-1,l)))
  U.append(u);Ui.append(ui)
 result=P();curvature=P();torsion=P()
 for x in range(len(first)-1):
  torsions=[]
  for r,(k,l)in enumerate(faces):
   xk=x+int(k==0);xl=x+int(l==0);xkl=x+int(k==0)+int(l==0)
   i,j,sg=comp[r]
   paths=[(x,I,F(1,4)),(xk,Ui[x][k],F(1,4)),(xl,Ui[x][l],F(1,4)),
     (xkl,mul(Ui[x][k],Ui[xk][l]),F(1,8)),(xkl,mul(Ui[x][l],Ui[xl][k]),F(1,8))]
   av=[P()for _ in range(6)]
   for site,path,weight in paths:av=add(av,sc(sg*weight,wedge(mv(path,E[site][i]),mv(path,E[site][j]))))
   h=mul(mul(mul(Ui[x][l],Ui[xl][k]),U[xk][l]),U[x][k])
   hi=mul(mul(mul(Ui[x][k],Ui[xk][l]),U[xl][k]),U[x][l])
   reading=ms(F(-1,2),ma(h,ms(-1,hi)))
   b=[reading[a][b]for a,b in [(0,1),(0,2),(0,3),(2,3),(3,1),(1,2)]]
   curvature+=bp(av,star(b))
   torsions.append(sub(sub(mv(Ui[x][k],E[xk][l]),E[x][l]),sub(mv(Ui[x][l],E[xl][k]),E[x][k])))
  tor=P()
  for r,(i,j)in enumerate(faces):
   for s,(k,l)in enumerate(faces):tor+=(Gi[x][i][k]*Gi[x][j][l]-Gi[x][i][l]*Gi[x][j][k])*ep(torsions[r],torsions[s])
  torsion+=F(1,101)*De[x]*tor
 return (curvature,torsion) if parts else curvature+torsion

def main():
 packet=Path(__file__).resolve().parent
 data=json.loads((packet/'legendre-root-data.json').read_text())
 h0,h1,b=[[[F(x) for x in row] for row in data[k]]for k in ('H0','H1','B')]
 D=[[F(x)for x in row]for row in json.loads((packet/'composition-root-data.json').read_text())['middle_inverse']]
 def mv(a,x):return [sum((p*q for p,q in zip(row,x)),F(0))for row in a]
 def dot(x,y):return sum((p*q for p,q in zip(x,y)),F(0))
 def quadratic(x,y):return dot(x,mv(h0,x))/2+dot(x,mv(b,y))+dot(y,mv(h1,y))/2
 def middle(x,z):return [-v for v in mv(D,add(mv(tr(b),x),mv(b,z)))]
 # Full quadratic normalization and affine endpoint checks on independent dense inputs.
 for seed in (1,2,3):
  q=[[F(((i+3)*(seed+t+2))%11-5,13+t)for i in range(40)]for t in range(3)]
  a=action(q)
  assert a.d.get((2,0),0)==quadratic(q[0],q[1])+quadratic(q[1],q[2])
  assert a.d.get((1,0),0)==sum(q[0][i]-q[2][i]for i in (22,29,36))
 x=[F(0)]*40;z=[F(i in (5,10,15))for i in range(40)];y=middle(x,z);q=[x,y,z]
 assert {i:y[i]for i in range(40)if y[i]}=={5:F(101,402),10:F(101,402),15:F(101,402),22:F(-100,201),29:F(-100,201),36:F(-100,201)}
 for i in range(40):assert action(q,1,i).d.get((1,1),0)==0
 cv,tor=action(q,1,0,parts=True)
 assert cv.d.get((2,1),0)==F(10000,13467)
 assert tor.d.get((2,1),0)==F(167,17956)
 assert (cv+tor).d.get((2,1),0)==F(40501,53868)
 for i in (4,8,12):assert action(q,1,i).d.get((2,1),0)==0
 # Cross-check the independently discovered asymmetric endpoint trial as well.
 x=[F(i==5)for i in range(40)];z=[F(0)]*40;y=middle(x,z)
 assert action([x,y,z],1,0).d.get((2,1),0)==F(77063,124542816)
 print(json.dumps({'result':'passed','scope':'exploratory exact formal jets; not a Lean analytic Taylor or nonlinear existence theorem','isotropic_inactive_force':'40501/53868','curvature':'10000/13467','torsion':'167/17956','all40_linear_owned_rows_zero':True,'dense_full_quadratic_and_affine_binding_controls':3,'asymmetric_crosscheck':'77063/124542816'},indent=2))

if __name__=='__main__':main()
