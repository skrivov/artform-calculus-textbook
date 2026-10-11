#!/usr/bin/env python3
"""Certificate for the models of Chapter 12 (Propositions 12.1, 12.3, 12.5-12.7, 12.10, 12.12 and
Theorem 12.4).

Writes the Lean file `textbook/ArtformTextbook/Ch12/ModelsData.lean`, whose data
`textbook/ArtformTextbook/Ch12/ModelsCheck.lean` checks with `decide +kernel`.

The computation is a port of the book's verifier (`textbook/tools/verify_matter_models.py`,
functions `omega_images`, `certified_spectrum`, `sector_spectra` and the hole map of section
13b), done exactly over the integers and the rationals, in the book's order of the modes: the mode
`(v, c, s)` of the edge is the bit `6 v + 2 c + s` of a mask, `v = 0` for `x` and `1` for `y`, `s = 0`
for up and `1` for down.

* The eight states of one vertex of Figure `fig:mm-two-slot-invariants`, as integer vectors over
  the masks of one vertex, and their sixty-four products `8 a + b` (`a` at `x`, `b` at `y`); the
  thirty-six products of the six fixed by `SU(3)`, `6 a + b`.
* The tally `3 Ω`, with and without the pair hop, in the product bases: the image of each product
  is an integer combination of products (the columns `omega1Cols`, `omega0Cols`, `omega36Cols`).
* For each spectrum, a basis of eigenvectors (integer vectors over the products, with the
  eigenvalues of `3 Ω`) and a matrix `D` with `D C = diag(d)`, `d` nonzero, `C` the eigenvectors
  as columns: the multiplicities are then those of the book.
* On the sixteen products of two quartets (numbered `4 a + b`), the operators `3 Ω`, `2 S_z` and
  `4 S²` with a common basis of eigenvectors.
* The hole map `𝒮` and the parity `(-1)^{N_x}` in the basis of the sixty-four products.

Run with no arguments; the Lean text goes to standard output.
"""

from fractions import Fraction as F
from math import gcd

UP, DN = 0, 1


# ---- occupations ---------------------------------------------------------------------------
def code(v, c, s):
    return 6 * v + 2 * c + s


def below(k, i):
    return bin(k & ((1 << i) - 1)).count("1")


def letter(cr, i, k):
    """The letter (cr, i) on the mask k: None for zero, else (sign, mask)."""
    if (k >> i & 1) == cr:
        return None
    return (-1 if below(k, i) % 2 else 1), k ^ (1 << i)


def apply_word(word, vec):
    """A word, a list of letters (cr, i), the rightmost acting first, on a dict vector."""
    out = {}
    for k, z in vec.items():
        cur = (1, k)
        for cr, i in reversed(word):
            r = letter(cr, i, cur[1])
            if r is None:
                cur = None
                break
            cur = (cur[0] * r[0], r[1])
        if cur is not None:
            out[cur[1]] = out.get(cur[1], 0) + z * cur[0]
    return {k: v for k, v in out.items() if v != 0}


def vadd(a, b, coef=1):
    out = dict(a)
    for k, v in b.items():
        out[k] = out.get(k, 0) + coef * v
    return {k: v for k, v in out.items() if v != 0}


def apply_op(op, vec):
    out = {}
    for coef, word in op:
        out = vadd(out, apply_word(word, vec), coef)
    return out


def eps(a, b, c):
    if len({a, b, c}) < 3:
        return 0
    return 1 if (a, b, c) in ((0, 1, 2), (1, 2, 0), (2, 0, 1)) else -1


# ---- the eight states of one vertex ---------------------------------------------------------
def V(c, s):
    return 2 * c + s


def word0(*modes):
    return apply_word([(1, i) for i in modes], {0: 1})


def eps_state(s1, s2, s3):
    v = {}
    for a in range(3):
        for b in range(3):
            for c in range(3):
                if eps(a, b, c):
                    v = vadd(v, word0(V(a, s1), V(b, s2), V(c, s3)), eps(a, b, c))
    return v


EMPTY = {0: 1}
PAIR = {}
for _c in range(3):
    PAIR = vadd(PAIR, word0(V(_c, UP), V(_c, DN)))
Q = [word0(V(0, UP), V(1, UP), V(2, UP)),
     {k: x // 2 for k, x in eps_state(UP, UP, DN).items()},
     {k: x // 2 for k, x in eps_state(UP, DN, DN).items()},
     word0(V(0, DN), V(1, DN), V(2, DN))]
assert all(x % 2 == 0 for x in eps_state(UP, UP, DN).values())
FULL = {63: 1}
HOLES = {}
for _c in range(3):
    HOLES = vadd(HOLES, apply_word([(0, V(_c, UP)), (0, V(_c, DN))], FULL))
EIGHT = [EMPTY, PAIR, Q[0], Q[1], Q[2], Q[3], HOLES, FULL]
SIX = [0, 2, 3, 4, 5, 7]
NQ = [0, 2, 3, 3, 3, 3, 4, 6]                 # quark numbers
SZ2 = [0, 0, 3, 1, -1, -3, 0, 0]              # twice S_z


def tensor(u, w):
    out = {}
    for k1, a in u.items():
        for k2, b in w.items():
            out[64 * k2 + k1] = out.get(64 * k2 + k1, 0) + a * b
    return out


BASIS = [tensor(EIGHT[a], EIGHT[b]) for a in range(8) for b in range(8)]
BASIS36 = [tensor(EIGHT[a], EIGHT[b]) for a in SIX for b in SIX]
BLOCK = [8 * (a + 2) + (b + 2) for a in range(4) for b in range(4)]    # the sixteen of (3, 3)


def pairing(u, w):
    return sum((F(a) * w.get(k, 0) for k, a in u.items()), F(0))


def coords(vec, basis):
    """Coordinates in a basis of products with disjoint supports, asserting no residual."""
    out = []
    rest = dict(vec)
    for b in basis:
        a = pairing(b, vec) / pairing(b, b)
        out.append(a)
        if a:
            rest = vadd(rest, b, -a)
    assert not rest, rest
    return out


def int_cols(cols):
    for col in cols:
        for x in col:
            assert F(x).denominator == 1, x
    return [[int(x) for x in col] for col in cols]


# ---- operators --------------------------------------------------------------------------
def A(c, cp):
    return [(1, [(1, code(1, c, s)), (0, code(0, cp, s))]) for s in range(2)]


def Ad(c, cp):
    return [(1, [(1, code(0, cp, s)), (0, code(1, c, s))]) for s in range(2)]


def opmul(o1, o2):
    return [(a * b, w1 + w2) for a, w1 in o1 for b, w2 in o2]


def tally3(m):
    """3 Ω: the there-and-back histories, and m times the pair hops."""
    out = []
    for c in range(3):
        for cp in range(3):
            out += opmul(Ad(c, cp), A(c, cp)) + opmul(A(c, cp), Ad(c, cp))
            if m:
                out += opmul(A(c, cp), A(c, cp)) + opmul(Ad(c, cp), Ad(c, cp))
    return out


SPLUS = [(1, [(1, code(v, c, UP)), (0, code(v, c, DN))]) for v in range(2) for c in range(3)]
SMINUS = [(1, [(1, code(v, c, DN)), (0, code(v, c, UP))]) for v in range(2) for c in range(3)]
UP_MASK = sum(1 << code(v, c, UP) for v in range(2) for c in range(3))


def spin_z2(k):
    return bin(k & UP_MASK).count("1") - bin(k & ~UP_MASK & 4095).count("1")


def apply_diag(f, vec):
    return {k: f(k) * z for k, z in vec.items() if f(k) * z != 0}


def spin_sq4(vec):
    """4 S² = (2 S_z)² + 2 (S₊ S₋ + S₋ S₊)."""
    a = apply_diag(lambda k: spin_z2(k) ** 2, vec)
    b = apply_op(opmul(SPLUS, SMINUS) + opmul(SMINUS, SPLUS), vec)
    return vadd(a, b, 2)


def hole_map(vec):
    """The verifier's hole map: a + a† at the up modes of x, a - a† at the up modes of y, then
    (-1) to the number of up quarks."""
    for v, sgn in ((0, 1), (1, -1)):
        for c in range(3):
            i = code(v, c, UP)
            out = {}
            for k, z in vec.items():
                r = letter(0, i, k)
                if r is not None:
                    out[r[1]] = out.get(r[1], 0) + z * r[0]
                r = letter(1, i, k)
                if r is not None:
                    out[r[1]] = out.get(r[1], 0) + sgn * z * r[0]
            vec = {k: x for k, x in out.items() if x != 0}
    return {k: z * (-1) ** bin(k & UP_MASK).count("1") for k, z in vec.items()}


def parity_x(vec):
    return {k: z * (-1) ** bin(k & 63).count("1") for k, z in vec.items()}


# ---- exact linear algebra ----------------------------------------------------------------
def nullspace(rows, n):
    rows = [[F(x) for x in r] for r in rows]
    piv = []
    r = 0
    for col in range(n):
        p = next((i for i in range(r, len(rows)) if rows[i][col] != 0), None)
        if p is None:
            continue
        rows[r], rows[p] = rows[p], rows[r]
        pv = rows[r][col]
        rows[r] = [x / pv for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][col] != 0:
                f = rows[i][col]
                rows[i] = [x - f * y for x, y in zip(rows[i], rows[r])]
        piv.append(col)
        r += 1
    free = [c for c in range(n) if c not in piv]
    basis = []
    for fc in free:
        v = [F(0)] * n
        v[fc] = F(1)
        for i, pc in enumerate(piv):
            v[pc] = -rows[i][fc]
        basis.append(v)
    return basis


def inverse(Mx):
    n = len(Mx)
    Aug = [[F(x) for x in row] + [F(int(i == j)) for j in range(n)] for i, row in enumerate(Mx)]
    for col in range(n):
        piv = next(r for r in range(col, n) if Aug[r][col] != 0)
        Aug[col], Aug[piv] = Aug[piv], Aug[col]
        pv = Aug[col][col]
        Aug[col] = [x / pv for x in Aug[col]]
        for r in range(n):
            if r != col and Aug[r][col] != 0:
                f = Aug[r][col]
                Aug[r] = [x - f * y for x, y in zip(Aug[r], Aug[col])]
    return [row[n:] for row in Aug]


def lcm(a, b):
    return a * b // gcd(a, b)


def int_vector(v):
    d = 1
    for x in v:
        d = lcm(d, F(x).denominator)
    w = [int(F(x) * d) for x in v]
    g = 0
    for x in w:
        g = gcd(g, abs(x))
    return [x // g for x in w] if g else w


def joint_certificate(colss, n, candss=None):
    """A common basis of eigenvectors of commuting operators given by integer columns, found by
    splitting the eigenspaces of the first by the others; `candss` lists the candidate integer
    eigenvalues of each. Returns [(values, vector)], D, d."""
    mats = [[[cols[j][i] for j in range(n)] for i in range(n)] for cols in colss]
    spaces = [([], [[F(int(i == j)) for i in range(n)] for j in range(n)])]
    if candss is None:
        candss = [range(0, 25)] * len(mats)
    for K, cands in zip(mats, candss):
        new = []
        for vals, basis in spaces:
            m = len(basis)
            Bcols = basis
            for nu in cands:
                rows = [[sum(K[i][k] * Bcols[j][k] for k in range(n)) - nu * Bcols[j][i]
                         for j in range(m)] for i in range(n)]
                sub = nullspace(rows, m)
                if sub:
                    vecs = [[sum(c[j] * Bcols[j][i] for j in range(m)) for i in range(n)]
                            for c in sub]
                    new.append((vals + [nu], vecs))
        assert sum(len(b) for _, b in new) == n
        spaces = new
    pairs = []
    for vals, basis in spaces:
        for v in basis:
            pairs.append((vals, int_vector(v)))
    assert len(pairs) == n
    C = [[pairs[k][1][i] for k in range(n)] for i in range(n)]
    Cinv = inverse(C)
    D, d = [], []
    for row in Cinv:
        den = 1
        for x in row:
            den = lcm(den, F(x).denominator)
        D.append([int(x * den) for x in row])
        d.append(den)
    for K, idx in zip(mats, range(len(mats))):
        for vals, c in pairs:
            assert [sum(K[i][j] * c[j] for j in range(n)) for i in range(n)] == \
                [vals[idx] * x for x in c]
    for k in range(n):
        Dc = [sum(D[i][j] * pairs[k][1][j] for j in range(n)) for i in range(n)]
        assert Dc == [d[k] if i == k else 0 for i in range(n)]
    return pairs, D, d


def spectrum(pairs, idx, scale):
    out = {}
    for vals, _ in pairs:
        out[F(vals[idx], scale)] = out.get(F(vals[idx], scale), 0) + 1
    return out


# ---- the computations ---------------------------------------------------------------------
def compute():
    K1 = int_cols([coords(apply_op(tally3(1), b), BASIS) for b in BASIS])
    K0 = int_cols([coords(apply_op(tally3(0), b), BASIS) for b in BASIS])
    K36 = int_cols([coords(apply_op(tally3(0), b), BASIS36) for b in BASIS36])
    p1, D1, d1 = joint_certificate([K1], 64)
    p0, D0, d0 = joint_certificate([K0], 64)
    p36, D36, d36 = joint_certificate([K36], 36)
    assert spectrum(p1, 0, 3) == {F(0): 14, F(3): 32, F(4): 10, F(20, 3): 6, F(8): 2}
    assert spectrum(p0, 0, 3) == {F(0): 9, F(2): 4, F(8, 3): 2, F(3): 32, F(10, 3): 2, F(4): 9,
                                  F(6): 2, F(20, 3): 3, F(8): 1}
    assert spectrum(p36, 0, 3) == {F(0): 9, F(3): 16, F(4): 5, F(6): 2, F(20, 3): 3, F(8): 1}
    # the sixteen products of two quartets: 3 Ω, 2 S_z, 4 S²
    B16 = [BASIS[j] for j in BLOCK]
    O16 = int_cols([coords(apply_op(tally3(1), b), B16) for b in B16])
    O16c = int_cols([coords(apply_op(tally3(0), b), B16) for b in B16])
    assert O16 == O16c                       # the pair hop does not act inside (3, 3)
    Z16 = int_cols([coords(apply_diag(spin_z2, b), B16) for b in B16])
    S16 = int_cols([coords(spin_sq4(b), B16) for b in B16])
    p16, D16, d16 = joint_certificate([O16, Z16, S16], 16,
                                      [range(0, 25), range(-6, 7), (0, 8, 24, 48)])
    # spin S (4 S² = 4 S (S + 1)) against the tally: spin 3, 2, 1, 0 carry 0, 4, 20/3, 8
    for vals, _ in p16:
        s4 = vals[2]
        spin = {48: 3, 24: 2, 8: 1, 0: 0}[s4]
        assert F(vals[0], 3) == {3: F(0), 2: F(4), 1: F(20, 3), 0: F(8)}[spin]
    # the hole map and the parity in the basis of the sixty-four products
    Hcols = int_cols([coords(hole_map(b), BASIS) for b in BASIS])
    Pcols = int_cols([coords(parity_x(b), BASIS) for b in BASIS])
    return dict(K1=K1, K0=K0, K36=K36, p1=p1, D1=D1, d1=d1, p0=p0, D0=D0, d0=d0, p36=p36,
                D36=D36, d36=d36, O16=O16, Z16=Z16, S16=S16, p16=p16, D16=D16, d16=d16,
                Hcols=Hcols, Pcols=Pcols)


# ---- Lean output ----------------------------------------------------------------------------
def wrap(items, open_, close, indent, width=98):
    """Join items into `open_ item, item, ... close`, wrapping lines at `width` characters."""
    lines = []
    cur = indent + open_
    for n, it in enumerate(items):
        piece = it + ("," if n < len(items) - 1 else close)
        if len(cur) + len(piece) + 1 > width and cur.strip() not in (open_.strip(), ""):
            lines.append(cur.rstrip())
            cur = indent + "  " + piece
        else:
            cur += ("" if cur.endswith(open_) else " ") + piece
    if not items:
        cur += close
    lines.append(cur)
    return lines


def lean_vec_items(col):
    return [f"({i}, {x})" for i, x in enumerate(col) if x]


def lean_cols(name, doc, cols):
    out = [f"/-- {doc} -/", f"def {name} : List Vec := ["]
    for j, col in enumerate(cols):
        lines = wrap(lean_vec_items(col), "[", "]", "  ")
        if j < len(cols) - 1:
            lines[-1] += ","
        out.extend(lines)
    out.append("]")
    out.append("")
    return out


def lean_eigs(name, doc, pairs, k=1):
    out = [f"/-- {doc} -/"]
    if k == 1:
        out.append(f"def {name} : List (ℤ × Vec) := [")
    else:
        out.append(f"def {name} : List (List ℤ × Vec) := [")
    for j, (vals, v) in enumerate(pairs):
        head = f"({vals[0]}, " if k == 1 else f"({list(vals)}, "
        lines = wrap(lean_vec_items(v), head + "[", "])", "  ")
        if j < len(pairs) - 1:
            lines[-1] += ","
        out.extend(lines)
    out.append("]")
    out.append("")
    return out


def lean_ints(name, doc, xs):
    out = [f"/-- {doc} -/", f"def {name} : List ℤ :="]
    out.extend(wrap([str(x) for x in xs], "[", "]", "  "))
    out.append("")
    return out


HEADER = """import ArtformTextbook.Ch12.FockCalc

/-!
# Certificate data for the models of Chapter 12

Written by `scripts/certificates/matter_models.py`; every claim about these data is checked by
`decide +kernel` in `Ch12/ModelsCheck.lean`.

A vector is a list of `(index, coefficient)`; a matrix is the list of its columns. The products of
the eight states of one vertex are numbered `8 a + b`, `a` the state at `x` and `b` the state at `y`
in the order of Figure `fig:mm-two-slot-invariants`; those of the six, `6 a + b`; the products of
two quartets, `4 a + b` for the quartet members `a` at `x` and `b` at `y`.
-/

namespace Artform.ModelsData

open FockCalc
"""


def main():
    d = compute()
    out = [HEADER]
    out += lean_cols("omega1Cols", "`3 Ω` with the pair hop in the basis of the sixty-four "
                     "products.", d["K1"])
    out += lean_cols("omega0Cols", "`3 Ω` without the pair hop in the basis of the sixty-four "
                     "products.", d["K0"])
    out += lean_cols("omega36Cols", "`3 Ω` without the pair hop in the basis of the thirty-six "
                     "products of the six.", d["K36"])
    for tag, nm in (("1", "with the pair hop, on the sixty-four"),
                    ("0", "without the pair hop, on the sixty-four"),
                    ("36", "without the pair hop, on the thirty-six")):
        out += lean_eigs(f"omega{tag}Eig", f"Eigenvectors of `3 Ω` {nm}, with the eigenvalues.",
                         d["p" + tag])
        out += lean_cols(f"omega{tag}D", "The matrix `D` with `D C = diag(d)` for the "
                         "eigenvectors `C`, by columns.", [[row[j] for row in d["D" + tag]]
                                                            for j in range(len(d["D" + tag]))])
        out += lean_ints(f"omega{tag}Dg", "The diagonal `d`.", d["d" + tag])
    out += lean_cols("block3Cols", "`3 Ω` on the sixteen products of two quartets.", d["O16"])
    out += lean_cols("blockSzCols", "`2 S_z` on the sixteen products of two quartets.", d["Z16"])
    out += lean_cols("blockSqCols", "`4 S²` on the sixteen products of two quartets.", d["S16"])
    out += lean_eigs("blockEig", "Common eigenvectors of `3 Ω`, `2 S_z` and `4 S²` on the "
                     "sixteen products,\nwith the three eigenvalues.", d["p16"], k=3)
    out += lean_cols("blockD", "The matrix `D` with `D C = diag(d)` for the common "
                     "eigenvectors, by columns.", [[row[j] for row in d["D16"]]
                                                   for j in range(16)])
    out += lean_ints("blockDg", "The diagonal `d`.", d["d16"])
    out += lean_cols("holeCols", "The hole map `𝒮` in the basis of the sixty-four products.",
                     d["Hcols"])
    out += lean_cols("parityCols", "The parity `(-1)^{N_x}` in the basis of the sixty-four "
                     "products.", d["Pcols"])
    out.append("end Artform.ModelsData")
    print("\n".join(out))


if __name__ == "__main__":
    main()
