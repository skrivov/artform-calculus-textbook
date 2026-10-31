#!/usr/bin/env python3
"""Exploratory exact common-slice Schur controls, separate from Lean reference theorem."""
from fractions import Fraction as F
import importlib.util,json
from pathlib import Path
P=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('root_history_compiler',P/'history-compiler-root.py')
hc=importlib.util.module_from_spec(spec);spec.loader.exec_module(hc)
tr=hc.transpose;mm=hc.multiply

def sub(a,b):return [[x-y for x,y in zip(r,s)]for r,s in zip(a,b)]
def mv(a,v):return [sum((x*y for x,y in zip(r,v)),F(0))for r in a]
def dot(u,v):return sum((x*y for x,y in zip(u,v)),F(0))
def at(a,rows,cols):return [[a[i][j]for j in cols]for i in rows]
def inverse(a):
 n=len(a);m=[r[:]+[F(i==j)for j in range(n)]for i,r in enumerate(a)]
 for k in range(n):
  p=next(i for i in range(k,n)if m[i][k]);m[k],m[p]=m[p],m[k]
  d=m[k][k];m[k]=[x/d for x in m[k]]
  for i in range(n):
   if i!=k and m[i][k]:
    d=m[i][k];m[i]=[x-d*y for x,y in zip(m[i],m[k])]
 return [r[n:]for r in m]
def det(a):
 m=[r[:]for r in a];d=F(1)
 for k in range(len(m)):
  p=next((i for i in range(k,len(m))if m[i][k]),None)
  if p is None:return F(0)
  if p!=k:m[k],m[p]=m[p],m[k];d=-d
  pivot=m[k][k];d*=pivot
  for i in range(k+1,len(m)):
   q=m[i][k]/pivot
   if q:m[i]=[x-q*y for x,y in zip(m[i],m[k])]
 return d
def inertia(a):
 _,_,ds,_=hc.congruence(a)
 assert all(ds)
 return [sum(d>0 for d in ds),sum(d<0 for d in ds)]

def main():
 H=hc.native_matrix(2)
 first=[i for i in range(40)if i not in (0,4,8,12)]
 second=[40+i for i in range(40)if i not in (0,4,8,12,1,2,3,6,7,11)]
 keep=first+second;G=at(H,keep,keep)
 X=list(range(36));Y=list(range(36,66))
 A=at(G,X,X);B=at(G,X,Y);D=at(G,Y,Y)
 Ai,Di=inverse(A),inverse(D)
 S=sub(D,mm(mm(tr(B),Ai),B));T=sub(A,mm(mm(B,Di),tr(B)))
 Si,Ti,Gi=inverse(S),inverse(T),inverse(G)
 assert mm(G,Gi)==mm(Gi,G)==hc.identity(66)
 dg=det(G);da,dd,ds,dt=map(det,(A,D,S,T))
 assert dg==da*ds==dd*dt and dg
 ns=[inertia(m)for m in (G,A,S,D,T)]
 assert ns==[[37,29],[15,21],[22,8],[12,18],[25,11]]
 ct,_,cd,_=hc.congruence(H)
 for seed in (1,2,3):
  g=[F(((i*(seed+1)+5)%13)-6,7+seed)for i in range(66)]
  u,v=g[:36],g[36:];y=mv(Gi,g)
  contact=dot(g,y)
  s=[x-y for x,y in zip(v,mv(tr(B),mv(Ai,u)))]
  t=[x-y for x,y in zip(u,mv(B,mv(Di,v)))]
  assert contact==dot(u,mv(Ai,u))+dot(s,mv(Si,s))
  assert contact==dot(v,mv(Di,v))+dot(t,mv(Ti,t))
  # Explicit compatible full80 lift, not arbitrary full sources with deleted rows.
  full_y=[F(0)]*80
  for i,value in zip(keep,y):full_y[i]=value
  full_r=mv(H,full_y)
  assert [full_r[i]for i in keep]==g
  rho=mv(tr(ct),full_r)
  assert all(not rho[i] for i,d in enumerate(cd)if not d)
 print(json.dumps({'result':'passed','proof_status':'exploratory exact host controls; not a Lean common-carrier Schur integral or certificate-invariance theorem','slice_original_coordinate_indices':keep,'inertias_G_A_S_D_T':ns,'determinants_G_A_S_D_T':list(map(str,(dg,da,ds,dd,dt))),'opposite_order_determinant_signature_source_contacts':'agree','full80_compatible_lift_controls':3,'full80_source_guards_retained':True,'physical_measure_selected':False},indent=2))
if __name__=='__main__':main()
