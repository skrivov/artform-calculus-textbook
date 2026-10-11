#!/usr/bin/env python3
"""Certificate for Proposition 12.8 (the sixty rotations of the icosahedron).

Writes, as Lean literals, the data that
`textbook/ArtformTextbook/Ch12/Icosahedron.lean` checks with `decide +kernel`:

* `vE`, the twelve vertices, in the order of `Artform.icoVertices`;
* `gE`, the sixty rotations, each as the doubled matrix `2 g` with entries in
  `Z[phi]`, one for each directed edge `(w1, w2)` of the icosahedron, in the
  lexicographic order of the vertex indices: `g` carries the frame
  `(v1, v2, v1 x v2)` of the base edge `v1 = (0, 1, phi)`, `v2 = (phi, 0, 1)`
  (vertices 0 and 4) to the frame `(w1, w2, w1 x w2)`;
* `perm`, the image of each vertex under each rotation, so that rotation `k`
  carries the base edge to `(perm k 0, perm k 4)`;
* `inv`, the index of the transpose of each rotation.

Every computation is exact, in Q(phi) with phi^2 = phi + 1, and the claims of
the proposition that Lean then checks are asserted here first. Run with no
arguments; the Lean text goes to standard output.
"""

from fractions import Fraction


class QPhi:
    """The number a + b phi of Q(phi), with phi^2 = phi + 1."""

    __slots__ = ("a", "b")

    def __init__(self, a=0, b=0):
        self.a = Fraction(a)
        self.b = Fraction(b)

    def __add__(self, o):
        return QPhi(self.a + o.a, self.b + o.b)

    def __sub__(self, o):
        return QPhi(self.a - o.a, self.b - o.b)

    def __neg__(self):
        return QPhi(-self.a, -self.b)

    def __mul__(self, o):
        return QPhi(self.a * o.a + self.b * o.b,
                    self.a * o.b + self.b * o.a + self.b * o.b)

    def scale(self, r):
        return QPhi(self.a * r, self.b * r)

    def inv(self):
        # (a + b phi)(a + b - b phi) = a^2 + a b - b^2
        n = self.a * self.a + self.a * self.b - self.b * self.b
        assert n != 0
        return QPhi((self.a + self.b) / n, -self.b / n)

    def __eq__(self, o):
        return self.a == o.a and self.b == o.b

    def __hash__(self):
        return hash((self.a, self.b))

    def key(self):
        return (self.a, self.b)


ZERO, ONE, PHI = QPhi(0), QPhi(1), QPhi(0, 1)


def vec(*xs):
    return tuple(xs)


def dot(u, v):
    return u[0] * v[0] + u[1] * v[1] + u[2] * v[2]


def cross(u, v):
    return (u[1] * v[2] - u[2] * v[1],
            u[2] * v[0] - u[0] * v[2],
            u[0] * v[1] - u[1] * v[0])


def neg(u):
    return tuple(-x for x in u)


def mat_mul(A, B):
    return [[sum((A[i][k] * B[k][j] for k in range(3)), ZERO) for j in range(3)]
            for i in range(3)]


def mat_vec(A, v):
    return tuple(sum((A[i][k] * v[k] for k in range(3)), ZERO) for i in range(3))


def transpose(A):
    return [[A[j][i] for j in range(3)] for i in range(3)]


def det(A):
    return dot(A[0], cross(A[1], A[2]))


def inverse(A):
    d = det(A)
    di = d.inv()
    # columns of the inverse: rows of the adjugate
    c0, c1, c2 = cross(A[1], A[2]), cross(A[2], A[0]), cross(A[0], A[1])
    adj_t = [c0, c1, c2]          # adjugate transposed
    return [[adj_t[j][i] * di for j in range(3)] for i in range(3)]


def columns(u, v, w):
    return [[u[i], v[i], w[i]] for i in range(3)]


# The vertices in the order of `Artform.icoVertices`.
VERTS = [
    vec(ZERO, ONE, PHI), vec(ZERO, ONE, -PHI), vec(ZERO, -ONE, PHI), vec(ZERO, -ONE, -PHI),
    vec(PHI, ZERO, ONE), vec(PHI, ZERO, -ONE), vec(-PHI, ZERO, ONE), vec(-PHI, ZERO, -ONE),
    vec(ONE, PHI, ZERO), vec(ONE, -PHI, ZERO), vec(-ONE, PHI, ZERO), vec(-ONE, -PHI, ZERO),
]
BASE1, BASE2 = 0, 4


def index_of(v):
    for i, w in enumerate(VERTS):
        if w == v:
            return i
    return None


def build():
    assert len(set(VERTS)) == 12
    assert dot(VERTS[BASE1], VERTS[BASE2]) == PHI
    edges = [(i, j) for i in range(12) for j in range(12) if dot(VERTS[i], VERTS[j]) == PHI]
    assert len(edges) == 60
    b1, b2 = VERTS[BASE1], VERTS[BASE2]
    frame_inv = inverse(columns(b1, b2, cross(b1, b2)))
    mats = []
    for (i, j) in edges:
        w1, w2 = VERTS[i], VERTS[j]
        g = mat_mul(columns(w1, w2, cross(w1, w2)), frame_inv)
        g2 = [[x.scale(2) for x in row] for row in g]
        for row in g2:
            for x in row:
                assert x.a.denominator == 1 and x.b.denominator == 1, "entry not in (1/2)Z[phi]"
        assert mat_vec(g, b1) == w1 and mat_vec(g, b2) == w2
        assert mat_vec(g, cross(b1, b2)) == cross(w1, w2)
        assert mat_mul(g, transpose(g)) == [[ONE if r == c else ZERO for c in range(3)]
                                            for r in range(3)]
        assert det(g) == ONE
        mats.append((g, g2))
    keys = [tuple(x.key() for row in g2 for x in row) for (_, g2) in mats]
    assert len(set(keys)) == 60
    perm, inv = [], []
    for (g, g2) in mats:
        p = [index_of(mat_vec(g, v)) for v in VERTS]
        assert None not in p and sorted(p) == list(range(12))
        perm.append(p)
        t = transpose(g2)
        tk = tuple(x.key() for row in t for x in row)
        inv.append(keys.index(tk))
    # traces, doubled
    traces = [g2[0][0] + g2[1][1] + g2[2][2] for (_, g2) in mats]
    count = {}
    for t in traces:
        count[t.key()] = count.get(t.key(), 0) + 1
    expected = {(6, 0): 1, (-2, 0): 15, (0, 0): 20, (0, 2): 12, (2, -2): 12}
    assert count == expected, count
    return edges, mats, perm, inv


def lean_int(x):
    assert x.denominator == 1
    n = int(x)
    return f"({n})" if n < 0 else str(n)


def lean_vec(u):
    return "v " + " ".join(lean_int(c) for x in u for c in (x.a, x.b))


def lean_mat(g2):
    return "m " + " ".join(lean_int(c) for row in g2 for x in row for c in (x.a, x.b))


def chunks(items, width, indent):
    """Join items with ", " into lines of at most width characters."""
    lines, cur = [], ""
    for it in items:
        piece = it if not cur else ", " + it
        if cur and len(indent + cur + piece) + 1 > width:
            lines.append(indent + cur + ",")
            cur = it
        else:
            cur += piece
    lines.append(indent + cur)
    return lines


def main():
    edges, mats, perm, inv = build()
    for k, (i, j) in enumerate(edges):
        assert perm[k][BASE1] == i and perm[k][BASE2] == j
    out = []
    out.append("/-- The twelve vertices, in the order of `icoVertices`. -/")
    out.append("def vE : Fin 12 → V3 := ![")
    out.extend(chunks([lean_vec(u) for u in VERTS], 100, "  "))
    out[-1] += "]"
    out.append("")
    out.append("/-- The sixty rotations, doubled: rotation `k` is `(gE k).toRealHalf`. It carries")
    out.append("the base edge `(vE 0, vE 4)` to the `k`-th directed edge in lexicographic order. -/")
    out.append("def gE : Fin 60 → M3 := ![")
    out.extend(chunks([lean_mat(g2) for (_, g2) in mats], 100, "  "))
    out[-1] += "]"
    out.append("")
    out.append("/-- `perm k i`: the vertex to which rotation `k` carries vertex `i`. -/")
    out.append("def perm : Fin 60 → Fin 12 → Fin 12 := ![")
    rows = ["![" + ", ".join(str(x) for x in p) + "]" for p in perm]
    out.extend(chunks(rows, 100, "  "))
    out[-1] += "]"
    out.append("")
    out.append("/-- `inv k`: the index of the transpose of rotation `k`. -/")
    out.append("def inv : Fin 60 → Fin 60 := ![")
    out.extend(chunks([str(x) for x in inv], 100, "  "))
    out[-1] += "]"
    print("\n".join(out))


if __name__ == "__main__":
    main()
