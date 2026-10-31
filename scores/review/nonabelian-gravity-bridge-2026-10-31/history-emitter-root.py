import argparse
import importlib.util
from pathlib import Path
parser=argparse.ArgumentParser(description='Reproduce the untrusted full80 congruence certificate emitted for Lean kernel checks.')
parser.add_argument('--write',action='store_true')
parser.add_argument('--check',action='store_true')
args=parser.parse_args()
root=Path(__file__).resolve().parents[3]
p=Path(__file__).resolve().with_name('history-compiler-root.py')
spec=importlib.util.spec_from_file_location('hc',p);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
h=m.native_matrix(2);u,v,d,tr=m.congruence(h);hu=m.multiply(h,u)
folder=root/'scores/ArtformScores/NonabelianGravity'
def emit(path,text):
 if args.write:path.write_text(text)
 else:assert path.read_text()==text,str(path.relative_to(root))
def rat(q):return str(q.numerator) if q.denominator==1 else '('+str(q.numerator)+' / '+str(q.denominator)+')'
def mat(name,a):
 s=f'def {name} : Matrix (Index 2) (Index 2) ℚ := fun i j =>\n  match 40 * i.1.val + i.2.val with\n'
 for i,row in enumerate(a):
  nz=[(j,x)for j,x in enumerate(row)if x]
  if nz:s+=f'  | {i} => match 40 * j.1.val + j.2.val with\n'+''.join(f'    | {j} => {rat(x)}\n'for j,x in nz)+'    | _ => 0\n'
 return s+'  | _ => 0\n\n'
s='import ArtformScores.NonabelianGravity.HistoryMatrix\nimport ArtformScores.NonabelianGravity.HistorySolve\n\n/-! # Untrusted generated full80 native three-cell congruence data -/\nset_option autoImplicit false\nnamespace Artform.Scores.NonabelianGravity.HistoryElimination\n\n'
for name,a in [('sampleForward',u),('sampleBackward',v),('sampleHU',hu)]:s+=mat(name,a)
s+='def sampleDiagonal : Index 2 → ℚ := fun i =>\n  match 40 * i.1.val + i.2.val with\n'+''.join(f'  | {i} => {rat(x)}\n'for i,x in enumerate(d)if x)+'  | _ => 0\n\nend Artform.Scores.NonabelianGravity.HistoryElimination\n'
emit(folder/'HistorySampleData.lean',s)
for mod,lemma,statement in [('Left','sample_left','sampleBackward * sampleForward = 1'),('Right','sample_right','sampleForward * sampleBackward = 1'),('Product','sample_product','historyMatrix 2 * sampleForward = sampleHU'),('Diagonal','sample_diagonal','sampleForward.transpose * sampleHU = Matrix.diagonal sampleDiagonal')]:
 s='import ArtformScores.NonabelianGravity.HistorySampleData\n\n/-! # Kernel check of the emitted native three-cell certificate -/\nset_option autoImplicit false\nnamespace Artform.Scores.NonabelianGravity.HistoryElimination\n\nset_option maxRecDepth 100000 in\nset_option maxHeartbeats 100000000 in\n-- All80 owned coordinates remain in this exact certificate identity.\nlemma '+lemma+' : '+statement+' := by\n  funext i\n  rcases i with ⟨t, k⟩\n  fin_cases t <;> fin_cases k <;> decide +kernel\n\nend Artform.Scores.NonabelianGravity.HistoryElimination\n'
 emit(folder/f'HistorySample{mod}.lean',s)
