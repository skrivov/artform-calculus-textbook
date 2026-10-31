"""Matched prospective three-output component benchmark; no historical timing claim."""
from fractions import Fraction as Q
from pathlib import Path
import hashlib,json,random,statistics,sys,time,platform
old=[('add',('in',0),('in',1)),('scale',Q(1,2),('slot',0)),('scale',Q(101,4),('in',2)),('add',('slot',1),('slot',2)),('add',('slot',3),('neg',('in',0))),('scale',Q(2,101),('slot',4)),('add',('in',1),('neg',('slot',3))),('scale',Q(2,101),('slot',6))]
new=[('add',('in',1),('neg',('in',0))),('scale',Q(1,101),('slot',0)),('scale',Q(1,2),('in',2)),('add',('slot',1),('slot',2)),('add',('slot',1),('neg',('slot',2))),('scale',Q(101,2),('slot',3)),('add',('in',0),('slot',5))]
def read(ref,x,reg):
 if ref[0]=='neg':return -read(ref[1],x,reg)
 return x[ref[1]] if ref[0]=='in' else reg[ref[1]]
def run(prog,out,x):
 reg=[]
 for op,a,b in prog:reg.append(a*read(b,x,reg) if op=='scale' else read(a,x,reg)+read(b,x,reg))
 return tuple(reg[i] for i in out),reg
def actual(x):
 a,b,j=x;return ((a+b)/2+101*j/4,(b-a)/101+j/2,(b-a)/101-j/2)
generation_start=time.perf_counter_ns()
rng=random.Random(113810);inputs=[tuple(Q(rng.randint(-65536,65536),rng.randint(1,65536)) for _ in range(3)) for _ in range(512)]
inputs += [(Q(0),Q(2),Q(2,101)),(Q(-1),Q(3),Q(4,101))]
max_bits={};certs={};programs=[('literal',old,(3,5,7)),('reused',new,(6,3,4))]
for name,prog,out in programs:
 peak=0;certificate=[]
 for x in inputs:
  y,reg=run(prog,out,x);assert y==actual(x)
  peak=max(peak,max(max(abs(v.numerator).bit_length(),v.denominator.bit_length()) for v in reg))
  certificate.append({'input':list(map(str,x)),'output':list(map(str,y))})
 payload=json.dumps({'program':repr(prog),'outputs':out,'cases':certificate},sort_keys=True,separators=(',',':')).encode();certs[name]={'bytes':len(payload),'sha256':hashlib.sha256(payload).hexdigest()};max_bits[name]=peak
generation_validation_ms=(time.perf_counter_ns()-generation_start)/1e6
# Same interpreter, input array and warm-cache state. Alternate order for each repeat.
for name,prog,out in programs:
 for x in inputs:run(prog,out,x)
timings={name:[] for name,_,_ in programs}
for rep in range(9):
 for name,prog,out in (programs if rep%2==0 else list(reversed(programs))):
  start=time.perf_counter_ns()
  for _ in range(4):
   for x in inputs:run(prog,out,x)
  timings[name].append((time.perf_counter_ns()-start)/1e6)
result={'status':'passed','frozen_problem':'same original two-cell torsion contribution, kappa1/101; freely supplied rational endpoints a,b and source j; output stationary m and both endpoint momenta','input_count':len(inputs),'heldout':['0,2,2/101','-1,3,4/101'],'cost_model':'ScalarGate: precomputed rational coefficients; input/slot reads, copies and unary negations free; each scale/add charged once; no global optimality assertion','literal_cost':{'scale':4,'add':4},'reused_cost':{'scale':3,'add':4},'peak_intermediate_bitlength':max_bits,'serialized_problem_output_certificate':certs,'python':platform.python_version(),'input_certificate_generation_and_validation_ms':round(generation_validation_ms,3),'timing_protocol':{'repeats':9,'warmup_each_program':len(inputs),'evaluations_per_batch':4*len(inputs),'alternating_program_order':True,'same_interpreter':True},'timings_ms':{name:{'samples':[round(v,3) for v in values],'median':round(statistics.median(values),3),'min':round(min(values),3),'max':round(max(values),3)} for name,values in timings.items()},'scope':'fresh local Python-interpreter microbenchmark and exact operation comparison; no historical discovery, Lean compilation, full40 computation or physical resource/time credit'}
path=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).with_suffix('.json');path.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
