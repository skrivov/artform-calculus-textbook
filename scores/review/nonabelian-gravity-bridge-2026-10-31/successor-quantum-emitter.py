"""Untrusted exact opposite native Schur certificate emitter; Lean checks all data."""
import argparse,importlib.util,json
from pathlib import Path
from fractions import Fraction as F
P=Path(__file__).resolve().parent;ROOT=P.parents[2];DEST=ROOT/'scores/ArtformScores/NonabelianGravity'
def module(name,file):
 s=importlib.util.spec_from_file_location(name,P/file);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
h=module('history_compiler','history-compiler-root.py');q=module('quantum_root','quantum-reference-root.py');mm=h.multiply;tr=h.transpose
first=[i for i in range(40)if i not in (0,4,8,12)];second=[i for i in range(40)if i not in (0,4,8,12,1,2,3,6,7,11)];keep=first+[40+i for i in second]
G=q.at(h.native_matrix(2),keep,keep);A=q.at(G,range(36),range(36));B=q.at(G,range(36),range(36,66));D=q.at(G,range(36,66),range(36,66))
Pmat=mm(q.inverse(A),B);Qmat=mm(q.inverse(D),tr(B));S=q.sub(D,mm(tr(B),Pmat));T=q.sub(A,mm(B,Qmat))
UA,_,dA,_=h.congruence(A);US,_,dS,_=h.congruence(S);UD,_,dD,_=h.congruence(D);UT,_,dT,_=h.congruence(T)
LU=[[-x for x in r]for r in mm(Pmat,US)];RL=[[-x for x in r]for r in mm(Qmat,UT)]
def block(a,b,c,d):return [x+y for x,y in zip(a,b)]+[x+y for x,y in zip(c,d)]
z=lambda m,n:[[F(0)]*n for _ in range(m)]
U=block(UA,LU,z(30,36),US);V=block(UT,z(36,30),RL,UD)
for W,ds in [(U,dA+dS),(V,dT+dD)]:
 assert all(ds) and sum(x>0 for x in ds)==37 and sum(x<0 for x in ds)==29
 assert mm(mm(tr(W),G),W)==[[ds[i]if i==j else 0 for j in range(66)]for i in range(66)]
assert mm(A,Pmat)==B and mm(D,Qmat)==tr(B)
a=argparse.ArgumentParser(description=__doc__);a.add_argument('--write',action='store_true');a.add_argument('--check',action='store_true');args=a.parse_args()
def emit(file,text):
 p=DEST/file
 text="\n".join(line.replace(" := ", " :=\n  ", 1) if len(line)>100 and " := " in line else line for line in text.split("\n"))
 if args.write:p.write_text(text)
 else:assert p.read_text()==text,file

def rat(x):return str(x.numerator)if x.denominator==1 else '('+str(x.numerator)+' / '+str(x.denominator)+')'
def mat(name,data,typ1,typ2,idx1='i.val',idx2='j.val'):
 s=f'def {name} : Matrix ({typ1}) ({typ2}) ℚ := fun i j =>\n  match {idx1} with\n'
 for i,row in enumerate(data):
  nz=[(j,x)for j,x in enumerate(row)if x]
  if nz:s+=f'  | {i} => match {idx2} with\n'+''.join(f'    | {j} => {rat(x)}\n'for j,x in nz)+'    | _ => 0\n'
 return s+'  | _ => 0\n\n'
head='import ArtformScores.NonabelianGravity.HistoryReferenceSample\n\n/-! # Emitted opposite Schur data on a fixed native principal slice -/\nset_option autoImplicit false\nnamespace Artform.Scores.NonabelianGravity.QuantumComposition\nopen HistoryElimination\n\nabbrev SliceIndex := Fin 36 ⊕ Fin 30\ndef indexCode : SliceIndex → ℕ := Sum.elim Fin.val (fun j => 36 + j.val)\n'
s=head
for name,coords in [('firstCoordinate',first),('secondCoordinate',second)]:
 n=len(coords);s+=f'\ndef {name} : Fin {n} → Fin 40 := fun i =>\n  match i.val with\n'+''.join(f'  | {i} => {v}\n'for i,v in enumerate(coords))+'  | _ => 0\n'
s+='\ndef nativeCoordinate : SliceIndex → Index 2 := Sum.elim (fun i => (0, firstCoordinate i)) (fun i => (1, secondCoordinate i))\ndef nativeSlice : Matrix SliceIndex SliceIndex ℚ := fun i j => historyMatrix 2 (nativeCoordinate i) (nativeCoordinate j)\n\n'
s+=mat('sliceData',G,'SliceIndex','SliceIndex','indexCode i','indexCode j')
for name,data,t1,t2 in [('leftA',A,'Fin 36','Fin 36'),('crossB',B,'Fin 36','Fin 30'),('rightD',D,'Fin 30','Fin 30'),('leftP',Pmat,'Fin 36','Fin 30'),('rightQ',Qmat,'Fin 30','Fin 36'),('leftBasis',UA,'Fin 36','Fin 36'),('leftSchurBasis',US,'Fin 30','Fin 30'),('rightBasis',UD,'Fin 30','Fin 30'),('rightSchurBasis',UT,'Fin 36','Fin 36'),('leftUpper',LU,'Fin 36','Fin 30'),('rightLower',RL,'Fin 30','Fin 36')]:s+=mat(name,data,t1,t2)
s+='def leftForward : Matrix SliceIndex SliceIndex ℚ := Matrix.fromBlocks leftBasis leftUpper 0 leftSchurBasis\ndef rightForward : Matrix SliceIndex SliceIndex ℚ := Matrix.fromBlocks rightSchurBasis 0 rightLower rightBasis\n\n'
for name,ds in [('leftDiagonal',dA+dS),('rightDiagonal',dT+dD)]:s+=f'def {name} : SliceIndex → ℚ := fun i =>\n  match indexCode i with\n'+''.join(f'  | {i} => {rat(x)}\n'for i,x in enumerate(ds))+'  | _ => 0\n\n'
s+='end Artform.Scores.NonabelianGravity.QuantumComposition\n';emit('QuantumSliceData.lean',s)
checks=[('Binding','slice_binding','nativeSlice = sliceData','  funext i j\n  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;> decide +kernel'),('AP','left_schur_solve','leftA * leftP = crossB','  funext i\n  fin_cases i <;> decide +kernel'),('DQ','right_schur_solve','rightD * rightQ = crossB.transpose','  funext i\n  fin_cases i <;> decide +kernel'),('Upper','left_upper_product','leftUpper = -(leftP * leftSchurBasis)','  funext i\n  fin_cases i <;> decide +kernel'),('Lower','right_lower_product','rightLower = -(rightQ * rightSchurBasis)','  funext i\n  fin_cases i <;> decide +kernel'),('Left','left_congruence_data','leftForward.transpose * sliceData * leftForward = Matrix.diagonal leftDiagonal','  funext i\n  rcases i with i | i <;> fin_cases i <;> decide +kernel'),('Right','right_congruence_data','rightForward.transpose * sliceData * rightForward = Matrix.diagonal rightDiagonal','  funext i\n  rcases i with i | i <;> fin_cases i <;> decide +kernel')]
for mod,lemma,statement,proof in checks:
 text='import ArtformScores.NonabelianGravity.QuantumSliceData\n\n/-! # Exact kernel replay of native Schur certificate data -/\nset_option autoImplicit false\nnamespace Artform.Scores.NonabelianGravity.QuantumComposition\n\nset_option maxRecDepth 100000 in\nset_option maxHeartbeats 100000000 in\n-- Finite rational native Schur identities are checked row by row in the kernel.\nlemma '+lemma+' :\n    '+statement+' := by\n'+proof+'\n\nend Artform.Scores.NonabelianGravity.QuantumComposition\n';emit('QuantumSlice'+mod+'.lean',text)
print(json.dumps({'result':'passed','scope':'untrusted generator; production identities require Lean kernel checks','dimension':66,'left_order':[36,30],'right_order':[30,36],'signature':[37,29],'native_coordinate_indices':keep,'determinant':str(q.det(G)),'generated_Lean_modules':8},indent=2))
