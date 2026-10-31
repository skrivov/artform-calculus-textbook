from fractions import Fraction as Q
import json,hashlib
from pathlib import Path
repo=Path(__file__).resolve().parents[3]
review=repo/'scores/review/gravity-r7-r8-120-2026-10-30'
a=Q(-101,103);b=Q(9999,19982);d=Q(-9595,19982)
# References are(input/slot,index,sign); negation and copies are free in the declared model.
i=lambda n:('input',n,1)
s=lambda n:('slot',n,1)
neg=lambda r:(r[0],r[1],-r[2])
dense=[('scale',d,i(0)),('scale',-b,i(1)),('add',s(0),s(1)),('scale',-b,i(2)),('add',s(2),s(3)),('scale',-b,i(0)),('scale',d,i(1)),('add',s(5),s(6)),('scale',b,i(2)),('add',s(7),s(8)),('scale',-b,i(0)),('scale',b,i(1)),('add',s(10),s(11)),('scale',d,i(2)),('add',s(12),s(13))]
rank=[('scale',a,i(0)),('scale',a,i(1)),('scale',a,i(2)),('add',i(0),neg(i(1))),('add',s(3),neg(i(2))),('scale',b,s(4)),('add',s(0),s(5)),('add',s(1),neg(s(5))),('add',s(2),neg(s(5)))]
def run(program,outputs,z):
 regs=[]
 def get(r):return (z if r[0]=='input' else regs)[r[1]]*r[2]
 for tag,u,v in program:
  value=u*get(v) if tag=='scale' else get(u)+get(v)
  regs.append(value)
 return [regs[j] for j in outputs],regs

def bits(regs):
 ns=[abs(x.numerator).bit_length() for x in regs];ds=[x.denominator.bit_length() for x in regs]
 return {'max_numerator_bits':max(ns),'max_denominator_bits':max(ds),'sum_register_numerator_denominator_bits':sum(ns)+sum(ds)}
samples=[('basis0',[Q(1),Q(0),Q(0)]),('old_selected_r',[Q(0),Q(-1),Q(1)]),('general_integer',[Q(1),Q(2),Q(3)]),('heldout_rational',[Q(1,17),Q(-23,29),Q(31,37)]),('heldout_large',[Q(2**32+1,3),Q(-2**40+1,5),Q(2**48+1,7)])]
rows=[]
for name,z in samples:
 zd,rd=run(dense,[4,9,14],z);zr,rr=run(rank,[6,7,8],z);assert zd==zr
 # Independent literal native inverse matrix, not either program's output registers.
 expected=[d*z[0]-b*z[1]-b*z[2],-b*z[0]+d*z[1]+b*z[2],-b*z[0]+b*z[1]+d*z[2]]
 assert zd==expected
 rows.append({'name':name,'input':[str(x) for x in z],'output':[str(x) for x in zd],'dense':bits(rd),'rank':bits(rr)})
path=repo/'scores/ArtformScores/GravityBridge/Native/Retrospective/BlockProgramsDefs.lean'
data={'model':'exact rational coefficient scale/add gates; fixed coefficient precomputation, negation and copying excluded; general arbitrary3-vector input; original native inverse output','lean_authority':'verified-native-block-programs; both explicit register programs checked for original inverse on every rational input','lean_defs_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'counts':{'dense':{'scale':9,'add':6},'rank':{'scale':4,'add':5}},'historical_selected_source':'The old source-specialized r/w output already needs one precomputed multiplication. Neither general program is its optimized historical implementation.','samples':rows,'runtime_claim':False,'bit_claim':'Exact register bit sizes on five finite tests only, not an asymptotic bit-complexity or universal bound.'}
(review/'program-traces-root-05.json').write_text(json.dumps(data,indent=2)+'\n')
print(json.dumps({'samples':len(rows),'all_original_inverse_outputs_equal':True,'counts':data['counts'],'bit_differences':[(r['name'],r['dense']['sum_register_numerator_denominator_bits'],r['rank']['sum_register_numerator_denominator_bits']) for r in rows]}))
