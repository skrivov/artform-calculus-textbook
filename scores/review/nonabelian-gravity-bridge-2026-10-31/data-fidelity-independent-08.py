#!/usr/bin/env python3
"""Independent review08 numeric-data fidelity check.
Executes only the standalone independent replay, then reads numeric Lean data.
No production evaluator is imported. All matrix entries and factor certificates
are compared against independently derived native formula values.
"""
from pathlib import Path
from fractions import Fraction as F
import re,runpy,io,contextlib
root=Path(__file__).resolve().parents[3];p=root/'scores/ArtformScores/NonabelianGravity'
with contextlib.redirect_stdout(io.StringIO()):d=runpy.run_path(str(root/'scores/review/nonabelian-gravity-bridge-2026-10-31/replay-independent-08.py'))
def matrices(file):
 text=(p/file).read_text();result={}
 pattern=r'def (\w+) : Matrix \(Fin (\d+)\) \(Fin (\d+)\) ℚ := fun i j =>\n(.*?)(?=\ndef |\nend )'
 for m in re.finditer(pattern,text,re.S):
  name,n,k,body=m.groups();M=[[F(0) for _ in range(int(k))] for _ in range(int(n))];row=None
  for line in body.splitlines():
   hit=re.fullmatch(r'  \| (\d+) => match j.val with',line)
   if hit:row=int(hit[1]);continue
   hit=re.fullmatch(r'    \| (\d+) => ([-\d /()]+)',line)
   if hit:M[row][int(hit[1])]=F(hit[2].replace(' ','').replace('(','').replace(')',''))
  result[name]=M
 return result
M=matrices('LegendreMatrixData.lean');C=matrices('LegendreCompositionData.lean')
for name,key in [('oldH','H0'),('newH','H1'),('mixed','B')]:assert M[name]==d[key],name
for name,key in [('middleInverse','D'),('composedMixed','C')]:assert C[name]==d[key],name
assert C['mixedMiddle']==d['mm'](d['B'],d['D'])
assert C['composedMixed']==[[-x for x in row] for row in d['mm'](C['mixedMiddle'],d['B'])]
mm=d['mm'];eye=lambda n:[[F(i==j) for j in range(n)] for i in range(n)]
assert mm(M['leftFactor'],M['rightFactor'])==M['mixed']
assert mm(M['leftInverse'],M['leftFactor'])==eye(24)
assert mm(M['rightFactor'],M['rightInverse'])==eye(24)
assert mm(C['composedLeft'],C['composedRight'])==C['composedMixed']
assert mm(C['composedLeftInverse'],C['composedLeft'])==eye(18)
assert mm(C['composedRight'],C['composedRightInverse'])==eye(18)
terms=[tuple(map(int,m)) for m in re.findall(r'\(\((\d+), (\d+)\), (-?\d+)\)',(p/'LegendrePolynomial.lean').read_text())]
assert terms==d['terms']
print('Independent complete numeric comparison passed:',len(M)+len(C),'matrices;',len(terms),'polynomial terms; all six factor/inverse identities')
