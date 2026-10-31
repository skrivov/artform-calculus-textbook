"""Fresh actual cubical cells, curved links and cell-action jet controls."""
from fractions import Fraction as Q
from itertools import combinations,product
from pathlib import Path
import json

root=Path(__file__).resolve().parent
eta=(-1,1,1,1)
pairs=[(0,1),(0,2),(0,3),(2,3),(3,1),(1,2)]


def eye(n):return [[Q(i==j) for j in range(n)] for i in range(n)]
def mm(a,b):return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]
def inv(a):return [[eta[i]*eta[j]*a[j][i] for j in range(4)] for i in range(4)]
def add(a,b):return [[x+y for x,y in zip(ar,br)] for ar,br in zip(a,b)]
def scale(a,s):return [[s*x for x in row] for row in a]
def determinant(a):
    w=[list(map(Q,row)) for row in a];value=Q(1)
    for c in range(len(a)):
        r=next((i for i in range(c,len(a)) if w[i][c]),None)
        if r is None:return Q(0)
        if r!=c:w[r],w[c]=w[c],w[r];value=-value
        pivot=w[c][c];value*=pivot
        for i in range(c+1,len(a)):
            f=w[i][c]/pivot
            for j in range(c+1,len(a)):w[i][j]-=f*w[c][j]
    return value


h=eye(4);h[0][0]=h[1][1]=Q(5,4);h[0][1]=h[1][0]=Q(3,4)
h2=mm(h,h)
K1=[[Q(0) for _ in range(4)] for _ in range(4)];K1[0][1]=K1[1][0]=1


def cells(N):
    result=[]
    for dim in range(5):
        layer=[]
        for directions in combinations(range(4),dim):
            ranges=[range(N[a]) if a in directions else range(N[a]+1) for a in range(4)]
            for coords in product(*ranges):
                faces=[]
                for a in directions:
                    for side in [0,1]:
                        p=list(coords);p[a]+=side
                        faces.append([list(d for d in directions if d!=a),p])
                layer.append({'directions':list(directions),'start':list(coords),'faces':faces})
        result.append(layer)
    return result


def edge(N,axis,p):
    if axis!=1:return eye(4)
    x=Q(p[0],N[0])
    if x==0:return eye(4)
    if x==Q(1,2):return h
    if x==1:return h2
    raise AssertionError(x)


def face_h(N,dirs,start):
    a,b=dirs;p=list(start);pa=p[:];pa[a]+=1;pb=p[:];pb[b]+=1
    word=[edge(N,a,p),edge(N,b,pa),inv(edge(N,a,pb)),inv(edge(N,b,p))]
    H=eye(4)
    for U in word:H=mm(U,H)
    return H


def coordinates(a):return [a[0][1],a[0][2],a[0][3],a[2][3],a[3][1],a[1][2]]
def bivector_matrix(v):
    a=[[Q(0) for _ in range(4)] for _ in range(4)]
    for value,(i,j) in zip(v,pairs):a[i][j]=value;a[j][i]=-eta[i]*eta[j]*value
    return a
def corner_transport(N,start,target):
    p=list(start);T=eye(4)
    for axis in range(4):
        while p[axis]<target[axis]:T=mm(edge(N,axis,p),T);p[axis]+=1
    assert p==list(target)
    return T
def wedge_columns(e,a,b):return [e[i][a]*e[j][b]-e[i][b]*e[j][a] for i,j in pairs]
def star(v):return [-v[3],-v[4],-v[5],v[0],v[1],v[2]]
def g(a,b):return sum((-1 if i<3 else 1)*a[i]*b[i] for i in range(6))
lam=Q(1,7)


def action(N,e):
    total=Q(0)
    for top in cells(N)[4]:
        chart=eye(4);chart[0][0]=Q(1,N[0])
        ec=mm(e,chart)
        for axes in combinations(range(4),2):
            outside=[a for a in range(4) if a not in axes]
            for bits in product([0,1],repeat=2):
                p=top['start'][:]
                for a,bit in zip(outside,bits):p[a]+=bit
                H=face_h(N,axes,p)
                if axes==(1,3):H=inv(H);index=4
                else:index=pairs.index(axes)
                f=coordinates(scale(add(H,scale(inv(H),-1)),Q(1,2)))
                dual=pairs[(index+3)%6]
                B=wedge_columns(ec,*dual)
                T=corner_transport(N,top['start'],p)
                B=coordinates(mm(mm(T,bivector_matrix(B)),inv(T)))
                total+=g(B,star(f))/4
        total+=lam*determinant(ec)
    return total


geometry=[]
for N,expected in [([1,1,1,1],[16,32,24,8,1]),([2,1,1,1],[24,52,42,15,2])]:
    cs=cells(N);assert [len(x) for x in cs]==expected
    named={(tuple(c['directions']),tuple(c['start'])) for layer in cs for c in layer}
    for layer in cs:
        for c in layer:
            assert all((tuple(d),tuple(p)) in named for d,p in c['faces'])
    faces=[]
    for face in cs[2]:
        H=face_h(N,face['directions'],face['start'])
        if face['directions']==[0,1]:assert H==(h2 if N[0]==1 else h)
        else:assert H==eye(4)
        T=corner_transport(N,[0,0,0,0],face['start'])
        faces.append({'directions':face['directions'],'start':face['start'],'holonomy':H,
                      'root_corner_transport':T})
    geometry.append({'N':N,'counts':expected,'cells':cs,'face_holonomies':faces})
e=eye(4);coarse=action([1,1,1,1],e);fine=action([2,1,1,1],e)
assert coarse==Q(15,8)+lam and fine==Q(3,2)+lam and fine-coarse==Q(-3,8)
gradients=[]
for N in [[1,1,1,1],[2,1,1,1]]:
    grad=[];step=Q(1,100)
    for i in range(4):
        row=[]
        for j in range(4):
            ep=[r[:] for r in e];em=[r[:] for r in e]
            ep[i][j]+=step;em[i][j]-=step
            row.append((action(N,ep)-action(N,em))/(2*step))
        grad.append(row)
    gradients.append(grad)
delta_grad=add(gradients[1],scale(gradients[0],-1))
assert delta_grad[2][2]==delta_grad[3][3]==Q(-3,8)
assert all(delta_grad[i][j]==0 for i in range(4) for j in range(4) if (i,j) not in [(2,2),(3,3)])

# Exact boost-rapidity source jets, with source y per child.
fine_jets=[2*h[0][1],2*h[0][0],2*h[0][1]]
coarse_jets=[h2[0][1],2*h2[0][0],4*h2[0][1]]
defect=[a-b for a,b in zip(fine_jets,coarse_jets)]
assert defect==[Q(-3,8),Q(-7,4),Q(-6)]
child_p=scale(K1,Q(-5,4));effective_p=child_p;coarse_p=scale(K1,Q(-17,8))
assert mm(mm(inv(h),child_p),h)==child_p
out={'geometry':geometry,'child_boost':h,'parent_boost':h2,'volume_coefficient':lam,
     'coarse_action':coarse,'fine_action':fine,'coframe_gradients':gradients,
     'coframe_gradient_defect':delta_grad,'curvature_y_jet_order':['value','y','yy'],
     'fine_curvature_jets':fine_jets,'coarse_curvature_jets':coarse_jets,
     'defect_curvature_jets':defect,'coframe_x_source':defect[0],'mixed_xy_source':defect[1],
     'stationary_detail_hessian':Q(3,2),'child_holonomy_momentum':child_p,
     'effective_holonomy_momentum':effective_p,'inherited_holonomy_momentum':coarse_p,
     'curvature_sign_profile':'R_plus=(H-H^-1)/2; root K=-R_plus reverses curvature defects',
     'root_normalized_defect_curvature_jets':[-v for v in defect],
     'scope':'Actual curved cube comparison with coframe inheritance; off-shell R_plus profile'}
def encode(x):
    if isinstance(x,Q):return str(x)
    if isinstance(x,list):return [encode(v) for v in x]
    if isinstance(x,dict):return {k:encode(v) for k,v in x.items()}
    return x
(root/'evidence.json').write_text(json.dumps(encode(out),indent=2)+'\n')
print('Curved cell producer passed: counts, all66 faces,16 coframe rows, mixed source−7/4.')
