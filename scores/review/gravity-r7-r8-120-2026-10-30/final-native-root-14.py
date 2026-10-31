"""Exact final20 replay; old utilities are loaded only before receipt-writing tails."""
from pathlib import Path
from fractions import Fraction as F
import hashlib
import json
import random

rdir = Path(__file__).resolve().parent
algebra = {'__file__': str(rdir/'tt-cross-root-12.py')}
exec((rdir/'tt-cross-root-12.py').read_text().split('import json,hashlib,random')[0], algebra)
cube = {'__file__': str(rdir/'curved-subdivision-root-13.py')}
exec((rdir/'curved-subdivision-root-13.py').read_text().split('geometry = []')[0], cube)

def rational(A):
    assert all(not x.b for row in A for x in row)
    return [[x.a for x in row] for row in A]

def transpose(A):
    return [list(row) for row in zip(*A)]

def mm(A, B):
    return [[sum(x*y for x,y in zip(row,col)) for col in zip(*B)] for row in A]

def mv(A, x):
    return [sum(a*x[j] for j,a in enumerate(row) if a) for row in A]

def eye(n):
    return [[F(i==j) for j in range(n)] for i in range(n)]

def block(A, s):
    return [row[3*s:3*s+3] for row in A[3*s:3*s+3]]

def wire(A, x):
    out = []
    for row in A:
        nz = [(j,a) for j,a in enumerate(row) if a]
        assert len(nz)==1 and abs(nz[0][1])==1
        j,a = nz[0]
        out.append(x[j] if a==1 else -x[j])
    return out

B,H,T,M,Q,P = [rational(algebra[k]) for k in ['B','Bi','T','M','Qop','P']]
Qi = rational(algebra['inv'](algebra['Qop']))
C0 = algebra['sub'](algebra['B'], algebra['scale'](2*algebra['kap'],
    algebra['mul'](algebra['mul'](algebra['transpose'](algebra['T']),algebra['M']),algebra['T'])))
woodbury = algebra['add'](algebra['M'],algebra['scale'](2*algebra['kap'],
    algebra['mul'](algebra['mul'](algebra['T'],algebra['inv'](C0)),algebra['transpose'](algebra['T']))))
assert rational(woodbury)==Qi and mm(Q,Qi)==mm(Qi,Q)==eye(24)
assert mm(B,H)==mm(H,B)==eye(24)
groups = [[0,14,19],[1,6,11],[2,5,12],[3,9,16],[4,13,23],[7,10,20],[8,17,22],[15,18,21]]
signs = [[1,-1,-1],[1,1,1],[1,-1,-1],[1,-1,-1],[1,1,-1],[1,-1,-1],[1,1,1],[1,-1,1]]
W = [[F(signs[s][i] if j==groups[s][i] else 0) for j in range(24)] for s in range(8) for i in range(3)]
assert mm(W,transpose(W))==eye(24)
alpha = [F(v,101) for v in [103,-103,-103,-103,103,-103,103,103]]
beta = [F(v,101) for v in [-1,1,2,2,-1,2,-1,-2]]
qinv_blocks = mm(mm(W,Qi),transpose(W)); q_blocks = mm(mm(W,Q),transpose(W))
h_blocks = mm(mm(transpose(P),H),P)
h_parameters = [(F(-101,103),F(9999,19982),[1,-1,-1])]*3
h_parameters += [(F(101,103),F(-9999,19982),[1,1,1])]
h_parameters += [(F((-1 if s==0 else 1)*101,103),F((1 if s==0 else -1)*10201,20600),[1,1,1]) for s in range(4)]
q_parameters = [(1/a,-b/(a*(a+3*b)),[1,1,1]) for a,b in zip(alpha,beta)]
qi_parameters = [(a,b,[1,1,1]) for a,b in zip(alpha,beta)]

# Same literal scale/add model as the Lean3-input DSL; signed wires are free in both.
def dense_code(A):
    code=[]; outputs=[]
    for row in A:
        start=len(code)
        code += [('s',row[0],('i',0)),('s',row[1],('i',1)),('a',('r',start),('r',start+1)),
                 ('s',row[2],('i',2)),('a',('r',start+2),('r',start+3))]
        outputs.append(start+4)
    return code,outputs

def rank_code(a,b,v):
    ref=lambda i: ('i',i) if v[i]==1 else ('n',('i',i))
    refout=lambda i: ('r',5) if v[i]==1 else ('n',('r',5))
    code=[('s',a,('i',i)) for i in range(3)]
    code += [('a',ref(0),ref(1)),('a',('r',3),ref(2)),('s',b,('r',4))]
    code += [('a',('r',i),refout(i)) for i in range(3)]
    return code,[6,7,8]

peak_bits=0

def execute(packet,z):
    global peak_bits
    code,out=packet; registers=[]
    def read(ref):
        if ref[0]=='i': return z[ref[1]]
        if ref[0]=='n': return -read(ref[1])
        assert 0<=ref[1]<len(registers)
        return registers[ref[1]]
    for gate in code:
        value=gate[1]*read(gate[2]) if gate[0]=='s' else read(gate[1])+read(gate[2])
        registers.append(value)
        peak_bits=max(peak_bits,abs(value.numerator).bit_length(),value.denominator.bit_length())
    assert all(0<=i<len(registers) for i in out)
    return [registers[i] for i in out]

rng=random.Random(12043)
receipts=[]; emitted={}
for name,A,read_matrix,Ab,params in [('H',H,transpose(P),h_blocks,h_parameters),
    ('Q',Q,W,q_blocks,q_parameters),('Qinverse',Qi,W,qinv_blocks,qi_parameters)]:
    assert all(Ab[i][j]==0 for i in range(24) for j in range(24) if i//3!=j//3)
    peak_bits=0
    dense=[]; rank=[]
    for s,(a,b,v) in enumerate(params):
        exact=[[a*int(i==j)+b*v[i]*v[j] for j in range(3)] for i in range(3)]
        assert block(Ab,s)==exact
        dense.append(dense_code(exact));rank.append(rank_code(a,b,v))
    for packets,expected in [(dense,(72,48)),(rank,(32,40))]:
        assert (sum(g[0]=='s' for p,_ in packets for g in p),sum(g[0]=='a' for p,_ in packets for g in p))==expected
    for case in range(48):
        x=[F(rng.randint(-13,13),rng.randint(1,9)) for _ in range(24)]
        z=wire(read_matrix,x); expected=mv(A,x)
        for packets in [dense,rank]:
            y=sum((execute(p,z[3*s:3*s+3]) for s,p in enumerate(packets)),[])
            assert wire(transpose(read_matrix),y)==expected
    raw=json.dumps({'dense':dense,'rank':rank},default=str,separators=(',',':')).encode()
    coeff=[g[1] for packets in [dense,rank] for p,_ in packets for g in p if g[0]=='s']
    receipts.append({'operator':name,'arbitrary_heldout_inputs':48,'all_outputs':24,
        'dense_scales_adds':[72,48],'rank_scales_adds':[32,40],
        'emitted_dense_gates':120,'emitted_rank_gates':72,'serialized_program_bytes':len(raw),
        'max_coefficient_num_den_bits':max(max(abs(c.numerator).bit_length(),c.denominator.bit_length()) for c in coeff),
        'max_replayed_intermediate_bits':peak_bits,'program_sha256':hashlib.sha256(raw).hexdigest()})
    emitted[name]=json.loads(raw)

# Original full odd inverse, all six actual eigenmodes and source-only adverse control.
a,b,c=F(194,101),F(103,101),F(200,101)
p1=a**-2+b**-2+c**-2; p3=-(a**-2*b**-2+a**-2*c**-2+b**-2*c**-2);p5=a**-2*b**-2*c**-2
Bb=mm(mm(transpose(P),B),P)
for s in range(8):
    A=block(Bb,s); A2=mm(A,A);A3=mm(A2,A);A5=mm(A2,A3)
    assert [[p1*A[i][j]+p3*A3[i][j]+p5*A5[i][j] for j in range(3)] for i in range(3)]==block(h_blocks,s)
assert 5*72+3*24==432 and 5*48+2*24==288
for slot,z,lam in [(0,[1,-1,-1],a),(3,[1,1,1],-a),(3,[0,1,-1],b),(0,[0,-1,1],-b),(4,[1,1,1],c),(5,[1,1,1],-c)]:
    x=[F(0)]*24;x[3*slot:3*slot+3]=list(map(F,z));v=wire(P,x)
    assert any(v) and mv(B,v)==[lam*t for t in v]
for _ in range(24):
    Z=[F(0)]*24
    for i in [3,7,9,10,15,16,18,20,21]: Z[i]=F(rng.randint(-5,5),rng.randint(1,7))
    src=mv(mm(transpose(T),M),Z); coords=wire(transpose(P),src)
    assert coords[12:]==[0]*12
    assert mv(H,src)==wire(P,sum((mv(block(h_blocks,s),coords[3*s:3*s+3]) for s in range(4)),[])+[F(0)]*12)
repeat=[F(0)]*24;repeat[15]=1;bad_source=wire(P,repeat)
assert any(bad_source) and mv(B,[F(0)]*24)!=bad_source

# Full original quadratic congruence, rather than a physical energy claim.
O=[[F(1),F(1),F(1)],[F(-1),F(1),F(1)],[F(0),F(-2),F(1)]]
diagonal=[]
for s in range(8):
    A=mm(mm(transpose(O),block(q_blocks,s)),O)
    assert all(A[i][j]==0 for i in range(3) for j in range(3) if i!=j)
    diagonal += [A[i][i] for i in range(3)]
assert sum(x>0 for x in diagonal)==sum(x<0 for x in diagonal)==12

# Actual literal nonlinear two-cell action, all-source stationary return and source window.
kap=F(1,101); native_cases=0
for q in [F(1001,1000),F(101,100),F(6,5),F(2),F(3)]:
    cu,su=(q+1/q)/2,(q-1/q)/2; A,B=2*su+kap*cu,kap*su; D=A*A-B*B
    assert D==4*su*su+4*kap*su*cu+kap*kap>kap*kap
    assert (kap+2*cu*su)**2-D==4*su**4
    if 2*su<kap: assert q*(A-B)<A+B
    for br in [F(1),F(3,2)]:
        for rho in [1/(q*q),1/q,F(1),q,q*q,F(11,10)]:
            C,S=(rho+1/rho)/2,(rho-1/rho)/2
            R,J=A*C+B*S,A*S+B*C; j=-br*J
            assert R>kap and R*R-J*J==D
            left,_=cube['literal_cell'](F(1,2),br,F(1),q*rho)
            right,_=cube['literal_cell'](F(1,2),br,q*rho,q*q)
            assert left+right==br*(kap-R)
            assert br*(kap-R)<0 and -br*(A*S+B*C)-j==0 and 1/(br*R)>0
            lo=-2*br*su*su-2*kap*br*su*cu; hi=2*br*su*su
            assert (lo<j<hi)==(1/q<rho<q)
            native_cases+=1
q=F(201,202);cu,su=(q+1/q)/2,(q-1/q)/2
assert (2*su+kap*cu)**2-(kap*su)**2==F(-151,83250381402)
for q,bound,op in [(F(2),F(45,32),'gt'),(F(3),F(80,27),'lt')]:
    cu,su=(q+1/q)/2,(q-1/q)/2;D=(2*su+kap*cu)**2-(kap*su)**2
    assert (D>(kap+bound)**2) if op=='gt' else (D<(kap+bound)**2)

pins=json.loads((rdir/'source-pins.json').read_text())['sources']
for pin in pins:
    raw=(rdir/pin['snapshot']).read_bytes()
    assert len(raw)==pin['bytes'] and hashlib.sha256(raw).hexdigest()==pin['sha256']
receipt={'status':'passed','source_pairs':len(pins),'matched_operator_replays':receipts,
    'actual_source_adjoint_control_cases':24,'literal_current_two_cell_cases':native_cases,
    'original_native_eigenvalues':list(map(str,[a,-a,b,-b,c,-c])),
    'constitutive_diagonal_signs':[12,12],'polynomial_scales_adds':[432,288],
    'generation_policy':'fixed coefficients supplied in both routes; emitted gates/serialized bytes/bitlength recorded separately from replay; no runtime saving claimed',
    'measure_proof':'formal Lean continuous-weight, unrestricted lintegral and finite-window inequalities; no numeric improper-integral inference',
    'credit':'prospective same-input/all24-output arithmetic comparisons only; historical, global Lean, full40 and physical-resource savings0; complete physical gates0'}
(rdir/'final-native-programs-14.json').write_text(json.dumps(emitted,indent=2)+'\n')
(rdir/'final-native-root-14.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
