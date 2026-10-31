#!/usr/bin/env python3
"""Exact production-table comparison using reviewer10's standalone source replay."""
import pathlib,runpy,contextlib,io,re,ast
from fractions import Fraction as F
P=pathlib.Path(__file__).resolve().parent
with contextlib.redirect_stdout(io.StringIO()):d=runpy.run_path(str(P/'replay-independent-10.py'))
s=(P.parents[2]/'scores/ArtformScores/NonabelianGravity/HistorySampleData.lean').read_text()
def rat(v):
 v=v.strip().strip('()');a=v.split('/');return F(a[0].strip()) if len(a)==1 else F(int(a[0]),int(a[1]))
actual=[]
for name in ('sampleForward','sampleBackward'):
 body=s.split('def '+name,1)[1].split('\ndef ',1)[0];M=[[F(0)]*80 for _ in range(80)]
 for i,b in re.findall(r'^  \| (\d+) => match .*?with\n(.*?)(?=^  \||\Z)',body,re.M|re.S):
  for j,v in re.findall(r'^    \| (\d+) => ([^\n]+)',b,re.M):M[int(i)][int(j)]=rat(v)
 actual.append(M)
body=s.split('def sampleDiagonal',1)[1];D=[F(0)]*80
for i,v in re.findall(r'^  \| (\d+) => ([^\n]+)',body,re.M):D[int(i)]=rat(v)
assert tuple(actual+[D])==d['sample_independent']
print('Independent full source/compiler comparison passed: all12800 forward/backward entries and80 diagonal values match the actual Lean sample table')
