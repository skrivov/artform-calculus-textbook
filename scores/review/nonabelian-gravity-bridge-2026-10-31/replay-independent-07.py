#!/usr/bin/env python3
"""Independent review07 exact evaluation of Full40 formula definitions.
Stdlib Fraction arithmetic, no production or prior-review evaluator imports.
Reviewer supplied conceptual advice and separate arithmetic, but authored no
production Lean. Formulas below were independently transcribed from the
complete native action; all forty output coordinates are varied before
selecting the rotational three-row matrix.
"""
from fractions import Fraction as F
from itertools import product
N=3;Z6=(F(0),)*6;Z4=(F(0),)*4
add=lambda a,b:tuple(x+y for x,y in zip(a,b));neg=lambda a:tuple(-x for x in a);sub=lambda a,b:add(a,neg(b));sc=lambda c,a:tuple(c*x for x in a)
eta=lambda i:-1 if i==0 else 1
pairs=[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]; comps=[(2,3,1),(1,3,-1),(1,2,1),(0,3,1),(0,2,-1),(0,1,1)]
def cross(a,b):return(a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0])
def br(a,b):return add(neg(cross(a[3:],b[:3])),neg(cross(a[:3],b[3:])))+sub(cross(a[:3],b[:3]),cross(a[3:],b[3:]))
def wedge(u,v):return tuple(u[i]*v[j]-u[j]*v[i] for i,j in [(0,1),(0,2),(0,3),(2,3),(3,1),(1,2)])
basis=lambda i:tuple(F(j==i) for j in range(4))
flat=[sc(s,wedge(basis(i),basis(j))) for i,j,s in comps]
star=lambda a:(-a[3],-a[4],-a[5],a[0],a[1],a[2])
bp=lambda a,b:sum((-1 if i<3 else 1)*a[i]*b[i] for i in range(6))
def lie(a):return((0,a[0],a[1],a[2]),(a[0],0,a[5],-a[4]),(a[1],-a[5],0,a[3]),(a[2],a[4],-a[3],0))
class Pulse:
 def __init__(self,c=None,values=None):
  self.zero=([list(Z4) for _ in range(4)],[list(Z6) for _ in range(4)])
  self.value=([list(Z4) for _ in range(4)],[list(Z6) for _ in range(4)])
  if values is not None:
   for i in range(4):
    for a in range(4):self.value[0][i][a]=values[4*i+a]
    for a in range(6):self.value[1][i][a]=values[16+6*i+a]
  elif c is not None:
   if c<16:self.value[0][c//4][c%4]=F(1)
   else:self.value[1][(c-16)//6][(c-16)%6]=F(1)
 def __getitem__(self,t):return self.value if t==0 else self.zero
modulus=3
shift=lambda t,i:((t+(i==0))%modulus if modulus else t+(i==0))
A=lambda q,t,i:tuple(q[t][1][i])
def first(q,t,i,j):return add(wedge(tuple(q[t][0][a][i] for a in range(4)),basis(j)),wedge(basis(i),tuple(q[t][0][a][j] for a in range(4))))
def K(q,t,r):
 i,j=pairs[r];return sub(sub(A(q,shift(t,j),i),A(q,t,i)),sub(A(q,shift(t,i),j),A(q,t,j)))
def LU(q,t,r):
 i,j,s=comps[r];k,l=pairs[r];sites=(t,shift(t,k),shift(t,l),shift(shift(t,k),l));linear=sc(F(s,4),tuple(sum(first(q,v,i,j)[a] for v in sites) for a in range(6)))
 V=sc(F(1,8),add(add(sc(3,A(q,t,k)),A(q,shift(t,l),k)),add(sc(3,A(q,t,l)),A(q,shift(t,k),l))))
 return sub(linear,br(V,flat[r]))
def contact(q,p,t,r):
 k,l=pairs[r]
 letters=lambda q:(neg(A(q,t,l)),neg(A(q,shift(t,l),k)),A(q,shift(t,k),l),A(q,t,k))
 a,b=letters(q),letters(p)
 return sc(F(-1,2),tuple(sum(br(a[i],b[j])[c] for i in range(4) for j in range(i+1,4)) for c in range(6)))
def theta(q,t,r):
 i,j=pairs[r];Li,Lj=lie(A(q,t,i)),lie(A(q,t,j));return tuple(q[shift(t,i)][0][a][j]-q[t][0][a][j]-q[shift(t,j)][0][a][i]+q[t][0][a][i]-Li[a][j]+Lj[a][i] for a in range(4))
def density(q,p,t):
 ans=F(0)
 for r in range(6):
  i,j=pairs[r];ans+=bp(LU(q,t,r),star(K(p,t,r)))+bp(flat[r],star(contact(q,p,t,r)))
  ans+=F(1,101)*eta(i)*eta(j)*sum(eta(a)*x*y for a,(x,y) in enumerate(zip(theta(q,t,r),theta(p,t,r))))
 return ans

def bil(q,p):return sum((density(q,p,t) for t in range(3)),F(0))

columns=[]
for c0 in (25,32,39):
 q=Pulse(c0);column=[]
 assert bil(q,q)==F(2,101)
 for c in range(40):
  p=Pulse(c);value=bil(q,p)+bil(p,q);column.append(value)
  expected=F(4 if c==c0 else -99,101) if c in (25,32,39) else F(0)
  assert value==expected,(c0,c,value,expected)
 columns.append(column)
M=[[columns[j][c] for j in range(3)] for c in (25,32,39)]
assert [sum(row) for row in M]==[F(-194,101)]*3
for v in ((1,-1,0),(0,1,-1)):
 assert [sum(M[i][j]*v[j] for j in range(3)) for i in range(3)]==[F(103,101)*v[i] for i in range(3)]
det=sum(((-1)**sum(p[i]>p[j] for i in range(3) for j in range(i+1,3)))*M[0][p[0]]*M[1][p[1]]*M[2][p[2]] for p in __import__('itertools').permutations(range(3)))
assert det==F(-194*103**2,101**3) and det!=0
# A term-retention control: the mixed row would be wrong if the ordered
# plaquette contact or torsion term were omitted.
def pieces(q,p):
 values=[F(0)]*3
 for t,r in product(range(3),range(6)):
  i,j=pairs[r]
  values[0]+=bp(LU(q,t,r),star(K(p,t,r)))
  values[1]+=bp(flat[r],star(contact(q,p,t,r)))
  values[2]+=F(1,101)*eta(i)*eta(j)*sum(eta(a)*x*y for a,(x,y) in enumerate(zip(theta(q,t,r),theta(p,t,r))))
 return values
left,right=pieces(Pulse(25),Pulse(32)),pieces(Pulse(32),Pulse(25))
mixed_parts=[a+b for a,b in zip(left,right)]
assert mixed_parts==[F(0),F(-1),F(2,101)],mixed_parts
# Dense arbitrary coframe/connection pulses check the ownership binding without
# restricting trial/test to the three rotational fields.
u=Pulse(values=[F((i%7)-3,i+1) for i in range(40)])
v=Pulse(values=[F((i%5)-2,i+2) for i in range(40)])
cycle=[density(u,v,t) for t in range(3)]
assert cycle[1]==0
modulus=None
integer={t:density(u,v,t) for t in range(-4,5)}
assert all(val==0 for t,val in integer.items() if t not in (-1,0))
assert cycle[0]==integer[0] and cycle[2]==integer[-1]
assert sum(cycle)==integer[-1]+integer[0]
# Physical-native convention at h=1 reverses each connection coefficient;
# by bilinearity force reverses and injectivity is unaffected. This is not a
# quaternion-holonomy field map or an actual discrete score derivative.
import json
print(json.dumps({'coefficient_field':'Q','kappa':'1/101','owned_time':0,'zero_halo_storage':[1,2],'incident_integer_density_cells':[-1,0],'evaluated_owned_rows':40,'rotational_columns':3,'other_rows_zero_per_column':37,'force_matrix':[[str(x) for x in row] for row in M],'eigenvalues':{'trace':'-194/101','traceless':'103/101'},'determinant':str(det),'zero_force_iff_zero_trial':True,'basis_quadratic_energy':'2/101','mixed_row_terms':{'LU_curvature':'0','ordered_contact':'-1','torsion':'2/101'},'dense_arbitrary40_integer_cycle_density_binding':True,'integer_support_stencil':'samples only x or x+1; a pulse can contribute only at -1,0','scope':'conditional rational flat zero-spatial-character ansatz; no curved score field map'},indent=2))
