#!/usr/bin/env python3
"""Root exact polynomial expansion of the literal Full40 quadratic density.
Standard-library arithmetic only; an independent reviewer uses separate code.
Native convention: all40 old/new variables, spatial-zero character, kappa1/101.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import defaultdict
import json
import argparse
class P:
 def __init__(self,x=0):self.d=x.copy() if isinstance(x,dict) else ({():F(x)} if x else {})
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
  o=P.cast(o);d=defaultdict(F)
  for k,v in self.d.items():
   for l,w in o.d.items():d[tuple(sorted(k+l))]+=v*w
  return P({k:v for k,v in d.items() if v})
 __rmul__=__mul__
 def __truediv__(self,o):return self*F(1,o)
from fractions import Fraction as F
Z=[F(0)]*6
E=[[F(int(i==j)) for j in range(4)] for i in range(4)]
faces=[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
comps=[(2,3,1),(1,3,-1),(1,2,1),(0,3,1),(0,2,-1),(0,1,1)]
def add(a,b):return [x+y for x,y in zip(a,b)]
def scale(c,a):return [c*x for x in a]
def sub(a,b):return add(a,scale(-1,b))
def cross(a,b):return [a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0]]
def bracket(a,b):return scale(-1,add(cross(a[3:],b[:3]),cross(a[:3],b[3:])))+sub(cross(a[:3],b[:3]),cross(a[3:],b[3:]))
def wedge(u,v):return [u[i]*v[j]-u[j]*v[i] for i,j in [(0,1),(0,2),(0,3),(2,3),(3,1),(1,2)]]
def lie(a):return [[0,a[0],a[1],a[2]],[a[0],0,a[5],-a[4]],[a[1],-a[5],0,a[3]],[a[2],a[4],-a[3],0]]
def star(a):return scale(-1,a[3:])+a[:3]
def bp(a,b):return sum((-1 if i<3 else 1)*a[i]*b[i] for i in range(6))
def ep(a,b):return sum((-1 if i==0 else 1)*a[i]*b[i] for i in range(4))
def shift(x,i):return (x+int(i==0))%5
def field(coord=None):
 q=[([[F(0)]*4 for _ in range(4)],[[F(0)]*6 for _ in range(4)]) for _ in range(5)]
 if coord:
  t,typ,i,j=coord;q[t][typ][i][j]=F(1)
 return q
def fw(q,x,i,j):return add(wedge([q[x][0][a][i] for a in range(4)],E[j]),wedge(E[i],[q[x][0][a][j] for a in range(4)]))
def vals(q,x,r):
 k,l=faces[r];i,j,sgn=comps[r];xd=shift(x,k);xl=shift(x,l);xdl=shift(xd,l)
 C=scale(sgn,wedge(E[i],E[j]))
 LC=scale(F(sgn,4),add(add(fw(q,x,i,j),fw(q,xd,i,j)),add(fw(q,xl,i,j),fw(q,xdl,i,j))))
 V=scale(F(1,8),add(add(scale(3,q[x][1][k]),q[xl][1][k]),add(scale(3,q[x][1][l]),q[xd][1][l])))
 LU=sub(LC,bracket(V,C))
 K=sub(sub(q[xl][1][k],q[x][1][k]),sub(q[xd][1][l],q[x][1][l]))
 LI,LJ=lie(q[x][1][k]),lie(q[x][1][l])
 T=[q[xd][0][a][l]-q[x][0][a][l]-q[xl][0][a][k]+q[x][0][a][k]-LI[a][l]+LJ[a][k] for a in range(4)]
 L=[scale(-1,q[x][1][l]),scale(-1,q[xl][1][k]),q[xd][1][l],q[x][1][k]]
 return C,LU,K,T,L

def B(q,p):
 ans=F(0)
 for x in range(5):
  for r,(k,l) in enumerate(faces):
   C,LU,K,T,L=vals(q,x,r);_,LP,KP,TP,M=vals(p,x,r)
   R=Z[:]
   for a in range(4):
    for b in range(a+1,4):R=add(R,bracket(L[a],M[b]))
   ans+=bp(LU,star(KP))+bp(C,star(scale(F(-1,2),R)))+F(1,101)*(-1 if k==0 else 1)*ep(T,TP)
 return ans

# The generic polynomial replaces each scalar in the original independent root
# formula transcription; the native vector/face/transport conventions are unchanged.
q=[([[P() for _ in range(4)] for _ in range(4)],[[P() for _ in range(6)] for _ in range(4)]) for _ in range(5)]
for t in range(2):
 for i in range(4):
  for a in range(4):q[t][0][i][a]=P({(40*t+4*i+a,):F(1)})
  for a in range(6):q[t][1][i][a]=P({(40*t+16+6*i+a,):F(1)})
ans=P()
for r,(k,l) in enumerate(faces):
 C,LU,K,T,L=vals(q,0,r)
 R=[P() for _ in range(6)]
 for a in range(4):
  for b in range(a+1,4):R=add(R,bracket(L[a],L[b]))
 ans+=bp(LU,star(K))+bp(C,star(scale(F(-1,2),R)))+F(1,101)*(-1 if k==0 else 1)*ep(T,T)
M=[[F(0)]*80 for _ in range(80)]
for k,v in ans.d.items():
 assert len(k)==2
 i,j=k;M[i][j]+=v;M[j][i]+=v
B=[r[40:] for r in M[:40]]
def rref(a):
 a=[r[:] for r in a];piv=[];i=0
 for j in range(len(a[0])):
  p=next((p for p in range(i,len(a)) if a[p][j]),None)
  if p is None:continue
  a[p],a[i]=a[i],a[p];den=a[i][j];a[i]=[x/den for x in a[i]]
  for k in range(len(a)):
   if k!=i and a[k][j]:
    den=a[k][j];a[k]=[x-den*y for x,y in zip(a[k],a[i])]
  piv.append(j);i+=1
  if i==len(a):break
 return a,piv
R,piv=rref(B)
H0=[r[:40] for r in M[:40]];H1=[r[40:] for r in M[40:]]
interior=[[H0[i][j]+H1[i][j] for j in range(40)] for i in range(40)]
RI,pi=rref(interior)
oldnull=[i for i in range(40) if not any(B[i])];newnull=[j for j in range(40) if not any(B[i][j] for i in range(40))]
out={'density_monomials':[[list(k),str(v)] for k,v in sorted(ans.d.items())], 'H0':[[str(v) for v in r] for r in H0], 'H1':[[str(v) for v in r] for r in H1], 'B':[[str(v) for v in r] for r in B],'B_rank':len(piv),'B_pivots':piv,'B_zero_rows':oldnull,'B_zero_columns':newnull,'interior_rank':len(pi),'interior_pivots':pi}
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check', action='store_true')
args = parser.parse_args()
target = Path(__file__).resolve().parent / 'legendre-root-data.json'
encoded = json.dumps(out, indent=2) + '\n'
if args.check:
 assert target.read_text() == encoded, 'native expansion certificate drift'
else:
 target.write_text(encoded)
print(json.dumps({k:v for k,v in out.items() if k not in ['density_monomials','H0','H1','B']},indent=2))
print('monomials',len(ans.d))
