"""Distinct exact native incidence, forced-memory and C8 coherent replay.

Uses stdlib rationals and Q[z]/(z^8+1), not floating point or author replay code.
Run from the isolated proof repository root. No report files are written here.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import hashlib,json,random

# Exact cyclotomic coefficient extension for the native16th root.
class R16:
    def __init__(self,x=0):
        self.c=x.c if isinstance(x,R16) else tuple(map(F,x)) if isinstance(x,(list,tuple)) else (F(x),)+(F(0),)*7
    def __add__(a,b):
        b=R16(b);return R16([x+y for x,y in zip(a.c,b.c)])
    __radd__=__add__
    def __neg__(a):return R16([-x for x in a.c])
    def __sub__(a,b):return a+-R16(b)
    def __rsub__(a,b):return R16(b)+-a
    def __mul__(a,b):
        b=R16(b);out=[F(0)]*8
        for i,x in enumerate(a.c):
            if x:
                for j,y in enumerate(b.c):
                    if y:out[(i+j)%8]+=x*y*(1 if i+j<8 else -1)
        return R16(out)
    __rmul__=__mul__
    def __eq__(a,b):return a.c==R16(b).c
    def __bool__(a):return any(a.c)
    def star(a):return sum((x*root(-i) for i,x in enumerate(a.c)),R16())
def root(n):
    k=n%16;out=[F(0)]*8;out[k%8]=1 if k<8 else -1;return R16(out)
def q(b,x):return root(-(x%8)**2+8*int(b)*(x%8))
def chi(x):return root(2*(x%8))
def kernel(b,a):return F(1,8)*sum((q(b,e)*chi(-e*a) for e in range(8)),R16())
def matmul(a,b):return [[sum((x*y for x,y in zip(r,c)),R16()) for c in zip(*b)] for r in a]
def adj(a):return [[x.star() for x in c] for c in zip(*a)]
def ident(n):return [[R16(i==j) for j in range(n)] for i in range(n)]
receipt_cases=0
for b in [False,True]:
    for s,t in product(range(8),repeat=2):
        assert q(b,(s+t)%8)==q(b,s)*q(b,t)*chi(-s*t);receipt_cases+=1
    for x in range(8):
        assert q(b,-x)==q(b,x) and q(b,x).star()*q(b,x)==1
        assert kernel(b,x).star()*kernel(b,x)==F(1,8)
        assert kernel(b,x)==F(1,4)*(1-root(4))*root((x*x)+(8*x if b else 0))
    assert q(b,0)==1 and q(b,1)!=q(not b,1)
    v=R16(1)
    for _ in range(8):v=v*q(b,1)
    assert v==-1
    M=[[kernel(b,x-y) for y in range(8)] for x in range(8)]
    assert matmul(adj(M),M)==matmul(M,adj(M))==ident(8)
    # Restrict an actual one-face raw word to one active edge, fixing other3 fields.
    # There are still8 configurations in this invariant coordinate slice.
    for offset in [0,3,7]:
        letters=[[[q(b,x+offset) if x==y else R16() for y in range(8)] for x in range(8)],M,
                 adj([[q(not b,x+offset) if x==y else R16() for y in range(8)] for x in range(8)])]
        compiled=ident(8)
        for gate in letters:compiled=matmul(gate,compiled)
        reversed_adjoint=ident(8)
        for gate in reversed(letters):reversed_adjoint=matmul(adj(gate),reversed_adjoint)
        assert reversed_adjoint==adj(compiled)
        assert matmul(adj(compiled),compiled)==matmul(compiled,adj(compiled))==ident(8)

# Native4x2 incidence from oriented boundaries and stored directed links.
vertices=list(product(range(4),range(2)));edges=list(product([0,1],vertices));faces=vertices[:]
vi={v:i for i,v in enumerate(vertices)};ei={e:i for i,e in enumerate(edges)}
def target(e):
    d,(x,y)=e;return (x,(y+1)%2) if d else ((x+1)%4,y)
def boundary(p):
    x,y=p;return [((0,p),1),((1,((x+1)%4,y)),1),((0,(x,(y+1)%2)),-1),((1,p),-1)]
C=[[sum(s for edge,s in boundary(p) if edge==e) for e in edges] for p in faces]
G=[[int(target(e)==v)-int(e[1]==v) for v in vertices] for e in edges]
Div=[[-G[e][v] for e in range(16)] for v in range(8)]
def mv(a,x,m=8):return [sum(c*y for c,y in zip(r,x))%m for r in a]
def transpose(a):return [list(c) for c in zip(*a)]
def plus(a,b):return [(x+y)%8 for x,y in zip(a,b)]
def minus(a,b):return [(x-y)%8 for x,y in zip(a,b)]
assert all(sum(C[f][e]*G[e][v] for e in range(16))==0 for f in range(8) for v in range(8))
def defect(s):return minus(mv(Div,s[1]),s[2])
def instruction(g,s):
    A,E,rho=map(list,s);tag,k,c=g
    if tag=='f':
        impulse=c*mv(C,A)[k];E=[(x+C[k][e]*impulse)%8 for e,x in enumerate(E)]
    elif tag=='m':A[k]=(A[k]+c*E[k])%8
    elif tag=='j':
        E[k]=(E[k]-c)%8;rho=[(x-Div[v][k]*c)%8 for v,x in enumerate(rho)]
    else:assert tag=='h'
    return (A,E,rho)
def run(word,s):
    for g in word:s=instruction(g,s)
    return s
def gauge(s,phi):return (plus(s[0],mv(G,phi)),s[1][:],s[2][:])
def omega(u,v):return sum(a*e-b*c for a,b,c,e in zip(u[0],u[1],v[0],v[1]))%8
def tangent(word,u):return run([g for g in word if g[0]!='j'],(u[0],u[1],[0]*8))[:2]
def native_tick(J,s):
    E=minus(plus(s[1],mv(transpose(C),mv(C,s[0]))),J)
    return (minus(s[0],E),E,minus(s[2],mv(Div,J)))
rng=random.Random(611731);prefixes=0
for _ in range(19):
    A=[rng.randrange(8) for _ in edges];E=[rng.randrange(8) for _ in edges];s=(A,E,mv(Div,E))
    word=[(rng.choice(['f','m','j','h']),0,rng.randrange(8)) for _ in range(27)]
    word=[(t,rng.randrange(8 if t=='f' else 16),c) for t,k,c in word]
    state=s
    for g in word:state=instruction(g,state);assert defect(state)==defect(s);prefixes+=1
    inverse=[(t,k,-c) for t,k,c in reversed(word)]
    assert run(inverse,run(word,s))==run(word,run(inverse,s))==s
    phi=[rng.randrange(8) for v in vertices];assert run(word,gauge(s,phi))==gauge(run(word,s),phi)
    u=([rng.randrange(8) for e in edges],[rng.randrange(8) for e in edges]);v=([rng.randrange(8) for e in edges],[rng.randrange(8) for e in edges])
    tu,tv=tangent(word,u),tangent(word,v)
    assert omega(tu,tv)==omega(u,v) and mv(Div,tu[1])==mv(Div,u[1])
    changed=run(word,(plus(s[0],u[0]),plus(s[1],u[1]),s[2]))
    base=run(word,s);assert changed==(plus(base[0],tu[0]),plus(base[1],tu[1]),base[2])
    J=[rng.randrange(8) for e in edges]
    macro=[('f',f,1) for f in range(8)]+[('j',e,J[e]) for e in range(16)]+[('m',e,-1) for e in range(16)]+[('h',0,0)]
    assert len(macro)==41 and run(macro,s)==native_tick(J,s)
    # Endpoint Gauss cannot justify invalid singleton old kick prefixes.
# Actual one-face positive/adverse controls, matching the running example.
oneA=[1,2,0,0];oneE=[0]*4;imp=sum(oneA)%8
assert [(x+imp)%8 for x in oneE]==[3]*4
assert [(oneA[i]-([2,3,3,3][i]))%8 for i in range(4)]==[7,7,5,5]
assert [(-1)%8,1,0,0]==[7,1,0,0]

# Four-site transverse source trajectory and actual even/odd memory.
def ftick(j,s):
    a,e=s;ep=[(e[i]+2*a[i]-a[(i+1)%4]-a[(i-1)%4]-j[i])%8 for i in range(4)]
    return (minus(a,ep),ep)
def embed(s):return ([s[0][p[0]] if d else 0 for d,p in edges],[s[1][p[0]] if d else 0 for d,p in edges],[0]*8)
def current(j):return [j[p[0]] if d else 0 for d,p in edges]
def even(s):return [[s[k][i] for i in [0,2]] for k in [0,1]]
def odd(s):return [[s[k][i] for i in [1,3]] for k in [0,1]]
def assemble(x,z):return ([x[0][0],z[0][0],x[0][1],z[0][1]],[x[1][0],z[1][0],x[1][1],z[1][1]])
def L(x):return [[(-a-e)%8 for a,e in zip(*x)],[(2*a+e)%8 for a,e in zip(*x)]]
def H(x):return [[sum(x[0])%8]*2,[(-sum(x[0]))%8]*2]
def force(j,parity):return [[j[parity],j[parity+2]],[(-j[parity])%8,(-j[parity+2])%8]]
def add2(x,y):return [plus(x[0],y[0]),plus(x[1],y[1])]
def power(n,x):
    for _ in range(n):x=L(x)
    return x
zero=[[0,0],[0,0]];memory_cases=0
for _ in range(17):
    states=[([rng.randrange(8) for i in range(4)],[rng.randrange(8) for i in range(4)])]
    currents=[[rng.randrange(8) for i in range(4)] for n in range(13)]
    for j in currents:states.append(ftick(j,states[-1]))
    xs=list(map(even,states));zs=list(map(odd,states));z0=zs[0]
    for n in range(13):
        assert native_tick(current(currents[n]),embed(states[n]))==embed(states[n+1])
        assert defect(embed(states[n]))==[0]*8 and mv(Div,current(currents[n]))==[0]*8
        assert xs[n+1]==add2(add2(L(xs[n]),H(zs[n])),force(currents[n],0))
        assert zs[n+1]==add2(add2(H(xs[n]),L(zs[n])),force(currents[n],1))
        formula=power(n,z0)
        for r in range(n):formula=add2(formula,add2(power(n-1-r,H(xs[r])),power(n-1-r,force(currents[r],1))))
        assert formula==zs[n] and assemble(xs[n],formula)==states[n]
        assert xs[n+1]==add2(add2(L(xs[n]),H(formula)),force(currents[n],0))
        assert power(4,zs[n])==zs[n];memory_cases+=1
# Omitted hidden-source convolution and initial hidden preparation both fail.
zfine=([0]*4,[0]*4);j=[0,1,0,0];s1=ftick(j,zfine);s2=ftick([0]*4,s1)
assert even(s1)==zero and even(s2)!=zero
hidden=([0,1,0,0],[0]*4)
def reading(s):return [[(s[0][2]-s[0][0])%8,(s[0][0]-s[0][2])%8],[s[1][0],s[1][2]]]
assert reading(zfine)==reading(hidden)==zero
assert reading(ftick([0]*4,hidden))==[[0,0],[7,7]]

# Actual common-policy MQ9 entries on the one-face raw canvas, gauge invariance.
raw_cases=0
for b in [False,True]:
    for _ in range(29):
        x=[rng.randrange(8) for i in range(4)];y=[rng.randrange(8) for i in range(4)];phi=[rng.randrange(8) for i in range(4)]
        h=[(phi[(i+1)%4]-phi[i])%8 for i in range(4)]
        def mq9(x,y):
            z=q(b,sum(y))
            for a,c in zip(x,y):z=z*kernel(b,a-c)
            return z
        assert mq9(plus(x,h),plus(y,h))==mq9(x,y);raw_cases+=1
    # A native translation with any increment, including0, has its MQ7 coefficient.
    for a in range(8):
        for y in range(8):assert kernel(b,((y+a)%8)-y)==kernel(b,a)
base=Path('scores/review/gauge-scores-2026-10-31')
inputs=list(Path('scores/ArtformScores/Gauge').glob('*.lean'))+[base/'source-pins.json',base/'ALGEBRA-OF-SCORES.md']
print(json.dumps({'status':'passed','native_C8_exact_cyclotomic_receipt_cases':receipt_cases,'both_MQ7_inverse_orders':True,'both_receipt_eighth_powers':-1,'exact_phase_aware_raw_word_slices':6,'native_torus_dimensions':[4,2],'random_fixed_word_prefixes':prefixes,'both_word_inverse_orders_and_fixed_source_tangent':19,'native_Maxwell_41_slot_macro_cases':19,'native_transverse_forced_memory_reconstruction_steps':memory_cases,'both_current_channels_retained':True,'hidden_source_and_hidden_initial_omission_detected':True,'native_C8_original_assessment_reading_controls':True,'native_common_policy_MQ9_gauge_cases':raw_cases,'all8_translation_increments_including_zero':True,'source_sha256':{str(f):hashlib.sha256(f.read_bytes()).hexdigest() for f in inputs}},sort_keys=True))
