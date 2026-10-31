from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json
#!/usr/bin/env python3
"""Exact permutation/Fraction producer and replay; no floating-point arithmetic.
The generated finite data are separately proved against the Lean definitions.
Use --check to compare certificates and the production OrbitData constants.
"""
import argparse
import hashlib
ROOT = Path(__file__).resolve().parents[3]
REVIEW = Path(__file__).resolve().parent

# Actual permutation multiplication, in the explicit Lean elements order.
e=(0,1,2); t01=(1,0,2);t02=(2,1,0);t12=(0,2,1)
def mul(a,b):return tuple(a[b[i]] for i in range(3))
def inv(a):return tuple(a.index(i) for i in range(3))
G=[e,t01,t02,t12,mul(t01,t12),mul(t12,t01)]
def conj(h,a):return mul(mul(h,a),inv(h))
X=list(product(G,repeat=2));idx={x:i for i,x in enumerate(X)}
classes=[];codes=[]
for x in X:
 orb={ (conj(h,x[0]),conj(h,x[1])) for h in G}
 if orb not in classes:classes.append(orb)
 codes.append(classes.index(orb))
reps=[min(idx[x] for x in O) for O in classes];weights=[len(O) for O in classes]
assert len(reps)==11
def ematrix(edge):
 return [[F(x[1-edge]==y[1-edge],3)-int(x==y) for y in X] for x in X]
Ms=[ematrix(0),ematrix(1)]
Ts=[[[sum(M[idx[X[reps[i]]]][k] for k,x in enumerate(X) if codes[k]==j) for j in range(11)] for i in range(11)] for M in Ms]
# integer matrices 3*T, directly checked via orbit-constant raw coefficients
Bs=[[[int(3*c) for c in row] for row in T] for T in Ts]
flat=[mul(x[0],x[1])==mul(x[1],x[0]) for x in X]
phases=[1 if flat[r] else -1 for r in reps]
source=[int(i==codes[idx[e,t01]]) for i in range(11)]
def mv(M,v):return [sum(a*b for a,b in zip(row,v)) for row in M]
stages=[source]
for _ in range(2):
 stages.append([a*b for a,b in zip(phases,stages[-1])])
 stages.append(mv(Bs[0],stages[-1])); stages.append(mv(Bs[1],stages[-1]))



def vec(v):return '!['+','.join(map(str,v))+']'
def mat(M):return '![\n  '+',\n  '.join(vec(row) for row in M)+']'
head='''import ArtformScores.Nonabelian.Geometry

/-! # Explicit orbit certificates for the actual S3 torus -/
set_option autoImplicit false
namespace Artform.Scores.Nonabelian
'''
s=head+'def orbitIndex (x : Raw) : Fin 11 := '+vec(codes)+' (rawEquiv.symm x)\n'
s+='def representative (i : Fin 11) : Raw := rawEquiv ('+vec(reps)+' i)\n'
s+='def orbitWeight : Fin 11 → ℕ := '+vec(weights)+'\n'
s+='def electricNumerator (e : Bool) : Matrix (Fin 11) (Fin 11) ℤ :=\n  if e then '+mat(Bs[1])+' else '+mat(Bs[0])+'\n'
s+='def orbitSign : Fin 11 → ℤ := '+vec(phases)+'\n'
s+='def stage : Fin 7 → Fin 11 → ℤ := '+mat(stages)+'\n'
s+='end Artform.Scores.Nonabelian\n'

def mm(A,B):
    return [[sum(a*b for a,b in zip(row,col)) for col in zip(*B)] for row in A]
def tr(A):return list(map(list,zip(*A)))
I=[[F(i==j) for j in range(36)] for i in range(36)]
J=[[F(codes[k]==i) for i in range(11)] for k in range(36)]
W=[[F(weights[i] if i==j else 0) for j in range(11)] for i in range(11)]
K=[[F((1 if flat[i] else -1) if i==j else 0) for j in range(36)] for i in range(36)]
for M in Ms+[K]:
    assert tr(M)==M and mm(M,M)==I
    for h in G:
        gaugeidx=[idx[(conj(h,x[0]),conj(h,x[1]))] for x in X]
        assert all(M[gaugeidx[i]][gaugeidx[j]]==M[i][j] for i in range(36) for j in range(36))
for M,T in zip(Ms,Ts):
    assert mm(M,J)==mm(J,T)
    assert mm(mm(tr(T),W),T)==W
# Derive the actual admitted-batch kernel: an empty branch of coefficient0,
# and all six constant replacements, with coefficient reading the old value.
for edge in range(2):
    for xi,x in enumerate(X):
        branch=[F(0) for _ in X]
        for c in G:
            y=(c,x[1]) if edge==0 else (x[0],c)
            branch[idx[y]]+=F(1,3)-int(c==x[edge])
        assert branch==[Ms[edge][yi][xi] for yi in range(36)]
free=[source]
for _ in range(2):
    free.append(free[-1])
    free.append(mv(Bs[0],free[-1]));free.append(mv(Bs[1],free[-1]))
divisors=[1,1,3,9,9,27,81]
results={}
for active in (False,True):
    actualK=K if active else I
    U=mm(mm(Ms[1],Ms[0]),actualK)
    assert mm(tr(U),U)==I
    rawsource=[F(i==codes[idx[e,t01]]) for i in codes]
    v=rawsource
    table=stages if active else free
    for step,M in enumerate([actualK,Ms[0],Ms[1]]*2,1):
        v=mv(M,v)
        orbitv=[F(a,divisors[step]) for a in table[step]]
        assert v==[orbitv[i] for i in codes]
        assert sum(a*a for a in v)==3
    curved=sum(a*a for a,f in zip(v,flat) if not f)
    probability=curved/3
    assert probability==(F(32,81) if active else 0)
    results[str(active).lower()]=dict(norm_squared=str(sum(a*a for a in v)/3),
        curvature_probability=str(probability),integer_stages=table)
assert free[-1]==[81*a for a in source]
assert sum(not f for f in flat)==18
assert sum(weights)==36
assert all(len(O)==weights[i] for i,O in enumerate(classes))
# Negative control: discarding the reflection's minus-identity term destroys unitarity.
P=[[F(x[1]==y[1],6) for y in X] for x in X]
assert mm(tr(P),P)!=I
certificate=dict(group_order=6,raw_states=36,physical_orbits=11,nonflat_states=18,
    reps=reps,weights=weights,codes=codes,signs=phases,electric_numerators=Bs,
    results=results,exact_raw_unitarity=True,gauge_covariance=True,
    actual_branch_kernels=True,weighted_descent=True,averager_negative_control=True)
parser=argparse.ArgumentParser();parser.add_argument('--check',action='store_true');args=parser.parse_args()
target=REVIEW/'replay-root.json'
if args.check:
    assert json.loads(target.read_text())==certificate
else:target.write_text(json.dumps(certificate,indent=2)+'\n')
assert ''.join((ROOT/'scores/ArtformScores/Nonabelian/OrbitData.lean').read_text().split())==''.join(s.split())
# Check the companion free-stage constants separately from the proof suffix.
pdata=(ROOT/'scores/ArtformScores/Nonabelian/ProbabilityData.lean').read_text()
assert ''.join(('def freeStage : Fin 7 → Fin 11 → ℤ := '+mat(free)).split()) in ''.join(pdata.split())
print('Exact S3 replay passed:36 raw,11 physical; normalized curvature32/81 versus0.')
