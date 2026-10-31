#!/usr/bin/env python3
"""Compare the reviewed Lean Laurent table to independent source arithmetic.
Depends explicitly on this reviewer's standalone replay-independent-09.py.
"""
import ast,contextlib,io,pathlib,re,runpy
packet=pathlib.Path(__file__).resolve().parent
with contextlib.redirect_stdout(io.StringIO()):
 d=runpy.run_path(str(packet/'replay-independent-09.py'))
P,F,B=d['P'],d['F'],d['B']
root=packet.parents[2]
s=(root/'scores/ArtformScores/NonabelianGravity/BoundarySymbol.lean').read_text()
s=s.split('def mixedApply',1)[1].split('set_option',1)[0]
class Exact(ast.NodeTransformer):
 def visit_BinOp(self,node):
  if isinstance(node.op,ast.Pow):
   node.left=self.visit(node.left);return node
  return self.generic_visit(node)
 def visit_Constant(self,node):
  return ast.copy_location(ast.Call(func=ast.Name(id='P',ctx=ast.Load()),args=[node],keywords=[]),node)
def coefficient(t):
 t=t.replace(': K','').replace('z⁻¹','(z**(-1))')
 tree=ast.fix_missing_locations(Exact().visit(ast.parse(t,mode='eval')))
 return eval(compile(tree,'<reviewed-Laurent-coefficient>','eval'),{'P':P,'z':P({1:F(1)})})
actual=[[P(0) for _ in range(40)] for _ in range(40)]
for i,expr in re.findall(r'\| (\d+) => (.*?)(?=\n  \|)',s,re.S):
 for term in re.split(r'\s*\+\s*\n\s*',expr):
  m=re.fullmatch(r'\s*(.*?)\s*\* v (\d+)\s*',term,re.S)
  assert m,(i,term)
  actual[int(i)][int(m[2])]+=coefficient(m[1])
assert actual==B,'Native mixedApply differs from independent full source transcription'
assert sum(bool(x) for row in actual for x in row)==88
print('Independent source comparison passed: all1600 Laurent entries,88 nonzero; all powers and rational coefficients exact')
cols=(root/'scores/ArtformScores/NonabelianGravity/BoundaryHistoryColumns.lean').read_text()
for name in ('firstColumns','secondColumns'):
 body=cols.split('def '+name,1)[1].split('\n\ndef ',1)[0].split('\nset_option',1)[0]
 got=[[F(0) for _ in range(6)] for _ in range(40)]
 for i,b in re.findall(r'^  \| (\d+) => match j.val with\n(.*?)(?=^  \||\Z)',body,re.M|re.S):
  for j,value in re.findall(r'^    \| (\d+) => (-?\d+)',b,re.M):got[int(i)][int(j)]=F(value)
 expected=[[F(0) for _ in range(6)] for _ in range(40)]
 for a in range(6):
  expected[16+a][a]=F(1 if name=='firstColumns' else -1)
  if name=='secondColumns':
   w=[F(j==a) for j in range(6)];L=d['lie'](w)
   for i in range(4):
    for j in range(4):expected[4*i+j][a]=F(L[i][j])
 assert got==expected,name
print('Independent source comparison passed: both complete40x6 history matrices, including inactive coframe entries')
