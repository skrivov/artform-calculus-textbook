"""Independent exact finite-panel, full-coordinate and source-bearing component replay."""
from pathlib import Path
from fractions import Fraction as Q
import hashlib,json,random,subprocess,sys
rdir=Path(__file__).resolve().parent
# Load only arithmetic utility definitions, leaving every published receipt untouched.
s=(rdir/'source-interfaces-root-09.py').read_text();exec(s[:s.index('g=list(map(mat,')])
rng=random.Random(118013);c=Q(1,101);cases=0
for _ in range(64):
 a,m,b,j,da,db,dj,e=[Q(rng.randint(-15,15),rng.randint(1,12)) for _ in range(8)]
 middle=lambda a,b,j:(a+b)/2+j/(4*c)
 action=lambda a,m,b,j:c*(m-a)**2+c*(b-m)**2-j*m
 eff=lambda a,b,j:c*(b-a)**2/2-j*(a+b)/2-j*j/(8*c)
 pin=lambda a,b,j:c*(b-a)+j/2
 pout=lambda a,b,j:c*(b-a)-j/2
 assert action(a,m,b,j)==eff(a,b,j)+2*c*(m-middle(a,b,j))**2
 assert pin(a,b,j)-pout(a,b,j)==j
 rem=c*(db-da)**2/2-dj*(da+db)/2-dj*dj/(8*c)
 assert eff(a+e*da,b+e*db,j+e*dj)==eff(a,b,j)+e*(-pin(a,b,j)*da+pout(a,b,j)*db-middle(a,b,j)*dj)+e*e*rem
 assert middle(a,b,j+dj)-middle(a,b,j)==dj/(4*c)
 assert eff(a+da,b+db,j+dj)-eff(a+da,b+db,j)-eff(a,b,j+dj)+eff(a,b,j)==-dj*(da+db)/2
 cases+=1
# Native component held-out values and independently composed boundary/source action.
a=Q(-1);b=Q(3);j=Q(4,101);assert (middle(a,b,j),pin(a,b,j),pout(a,b,j),eff(a,b,j))==(2,Q(6,101),Q(2,101),Q(2,101))
for _ in range(64):
 a,b,m,j,l=[Q(rng.randint(-15,15),rng.randint(1,12)) for _ in range(5)]
 ms=(a+b)/2+(j+l)/(4*c)
 ce=c*(b-a)**2/4-(j*(3*a+b)+l*(a+3*b))/4-(j*j+l*l)/(8*c)-(j+l)**2/(16*c)
 assert eff(a,m,j)+eff(m,b,l)==ce+c*(m-ms)**2
 assert pout(a,ms,j)==pin(ms,b,l)
# Full40 bilinear pairing with nonzero mixed contacts; no claim these are original A_r.
x=[[Q((i%7)-3)] for i in range(40)];y=[[Q((i%5)-2)] for i in range(40)]
B=mat([[Q(int((2*i+j)%17==0)-int((i+3*j)%19==0),3) for j in range(40)] for i in range(40)])
frame=lambda v:v[:16]+[[Q(0)] for _ in range(24)]
conn=lambda v:[[Q(0)] for _ in range(16)]+v[16:]
pair=lambda a,b:mul(mul(transpose(a),B),b)[0][0]
h=Q(2,7);px=sub(frame(x),scale(h,conn(x)));py=sub(frame(y),scale(h,conn(y)))
assert pair(px,py)==pair(frame(x),frame(y))-h*pair(frame(x),conn(y))-h*pair(conn(x),frame(y))+h*h*pair(conn(x),conn(y))
assert pair(px,py)!=pair(frame(x),frame(y))+h*h*pair(conn(x),conn(y))
# A noncommuting two-range40-coordinate stencil with true incoming transpose.
A1=B;A2=mat([[Q(int(j==(i+1)%40)) for j in range(40)] for i in range(40)])
assert mul(A1,A2)!=mul(A2,A1)
xs=lambda n:[[Q((n+1)*(i%3+1)+(i%5))] for i in range(40)]
ys=lambda n:[[Q(n*n*(i%4+1)-n*(i%2)+i%7)] for i in range(40)]
pp=lambda a,M,b:mul(mul(transpose(a),M),b)[0][0]
edge=lambda n,r:pp(xs(n),[None,A1,A2][r],ys(n+r))-pp(ys(n),[None,A1,A2][r],xs(n+r))
cut=lambda n:sum(edge(n-j,r) for r in (1,2) for j in range(r))
for n in range(-3,4):
 Jy=sum_mat([mul(A1,ys(n+1)),mul(transpose(A1),ys(n-1)),mul(A2,ys(n+2)),mul(transpose(A2),ys(n-2))])
 Jx=sum_mat([mul(A1,xs(n+1)),mul(transpose(A1),xs(n-1)),mul(A2,xs(n+2)),mul(transpose(A2),xs(n-2))])
 row=pp(xs(n),eye(40),Jy)-pp(ys(n),eye(40),Jx)
 assert cut(n)-cut(n-1)==row
 assert h*(h**3*row)==h**4*row
assert cut(0)-cut(-1)!=0
# A halo is actual additional input for an unrestricted stencil.
hx=lambda n:Q(n==0);hy=lambda n:Q(n==2)
scalar_edge=lambda n:hx(n)*hy(n+2)-hy(n)*hx(n+2)
assert hy(0)==hy(1)==0 and scalar_edge(0)+scalar_edge(-1)==1
# Source-preserving program benchmark is replayed on the same declared interpreter.
subprocess.run([sys.executable,str(rdir/'boundary-program-root-11.py')],check=True,stdout=subprocess.DEVNULL)
bench=json.loads((rdir/'boundary-program-root-11.json').read_text());assert bench['literal_cost']=={'scale':4,'add':4} and bench['reused_cost']=={'scale':3,'add':4}
root=rdir.parents[3];pairs=0
for item in json.loads((rdir/'source-pins.json').read_text())['sources']:
 raw=(root/item['original']).read_bytes();assert raw==(rdir/item['snapshot']).read_bytes()
 assert len(raw)==item['bytes'] and hashlib.sha256(raw).hexdigest()==item['sha256'];pairs+=1
out={'status':'passed','complete_source_covector_cases':cases,'composed_independent_source_cases':64,'full_coordinate_carrier':40,'full_mixed_contacts_retained':True,'noncommuting_stencil_cuts':7,'sourced_cut_not_conserved':True,'halo_adverse_case':True,'heldout':['2','6/101','2/101','2/101'],'matched_program_inputs':bench['input_count'],'same_cost_model':True,'source_pairs':pairs,'new_physical_gate':0,'historical_discovery_or_runtime_credit':0,'scope':'component/source and finite-stencil tests; original full40 current coefficients, physical/geometric move and uniform-h source estimates not inferred'}
(rdir/'green-composition-root-11.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
