"""Free-word Maurer-Cartan checks; no analytic or native gravity identification."""
from collections import defaultdict
from fractions import Fraction as F

def red(w):
    out = []
    for x in w:
        if out and out[-1] == -x:
            out.pop()
        else:
            out.append(x)
    return tuple(out)

def mul(a, b):
    return red(a + b)

def inv(a):
    return tuple((-x for x in reversed(a)))

def combine(a, b, c=1):
    d = defaultdict(F, a)
    for k, v in b.items():
        d[k] += c * v
    return {k: v for k, v in d.items() if v}

def ad(w, a):
    d = defaultdict(F)
    for (i, t), c in a.items():
        d[i, mul(w, t)] += c
    return {k: v for k, v in d.items() if v}

def right(w):
    d = {}
    pre = ()
    for x in w:
        term = {(abs(x) - 1, () if x > 0 else (x,)): F(1 if x > 0 else -1)}
        d = combine(d, ad(pre, term))
        pre = mul(pre, (x,))
    return d

def left(w):
    return ad(inv(w), right(w))

def wedge(a, b):
    d = defaultdict(F)
    for (i, u), c in a.items():
        for (j, v), e in b.items():
            w = mul(inv(u), v)
            sgn = 1
            if i > j:
                i0, j0 = (j, i)
                w = inv(w)
                sgn = -1
            else:
                i0, j0 = (i, j)
            if i0 == j0:
                if not w:
                    continue
                iw = inv(w)
                if iw < w:
                    w = iw
                    sgn = -sgn
            d[i0, j0, w] += c * e * sgn
    return {k: v for k, v in d.items() if v}
SRC = (0, 1, 4, 3, 1, 2, 5)
TGT = (1, 4, 3, 0, 2, 5, 4)
FACES = (((0, True), (1, True), (2, True), (3, True)), ((4, True), (5, True), (6, True), (1, False)))
STARS = (((0, False), (3, True)), ((4, False), (1, False), (0, True)), ((5, False), (4, True)), ((3, False), (2, True)), ((2, False), (1, True), (6, True)), ((6, False), (5, True)))

def prod(xs):
    w = ()
    for x in xs:
        w = mul(w, x)
    return w

def outgoing(s, e):
    u, p = s
    return prod([inv(u[e]), inv(p[e]), u[e]])

def hol(s, f, i):
    u, p = s
    word = FACES[f]
    word = word[i + 1:] + word[:i + 1]
    return prod((u[e] if b else inv(u[e]) for e, b in reversed(word)))

def kick(s, f):
    u, p = s
    p = list(p)
    for i, (e, b) in enumerate(FACES[f]):
        k = hol(s, f, i)
        p[e] = mul(k, p[e]) if b else prod([p[e], u[e], inv(k), inv(u[e])])
    return (u, p)

def drift(s):
    u, p = s
    return ([mul(b, a) for a, b in zip(u, p)], p)

def omega(s, include_fusion=True):
    u, p = s
    v = {}
    for e in range(7):
        a = u[e]
        b = mul(inv(a), p[e])
        v = combine(v, wedge(left(a), right(b)), F(1, 2))
        v = combine(v, wedge(right(a), left(b)), F(1, 2))
    for star in STARS if include_fusion else []:
        pre = ()
        for e, b in star:
            m = p[e] if b else outgoing(s, e)
            v = combine(v, wedge(left(pre), right(m)), F(1, 2))
            pre = mul(pre, m)
    return v

def main():
    import json
    s = ([(i + 1,) for i in range(7)], [(i + 8,) for i in range(7)])
    base = omega(s)
    rows = []
    for name, t in [('face0', kick(s, 0)), ('face1', kick(s, 1)), ('drift', drift(s))]:
        d = combine(omega(t), base, -1)
        bad = combine(omega(t, False), omega(s, False), -1)
        assert not d
        rows.append({'map': name, 'normal_defect_terms': len(d), 'omitted_fusion_defect_terms': len(bad)})
    print(json.dumps({'scope': 'formal invariant-pairing Maurer word algebra, not an analytic or reduced-manifold theorem', 'baseline_normal_terms': len(base), 'results': rows}, indent=2))
if __name__ == '__main__':
    main()
