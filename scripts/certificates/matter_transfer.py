#!/usr/bin/env python3
"""Certificate for the third-order transfer of Chapter 13 (Theorem 13.9).

Writes the Lean file `textbook/ArtformTextbook/Ch13/TransferData.lean`, whose data
`textbook/ArtformTextbook/Ch13/TransferCheck.lean` checks with `decide +kernel`.

The computation is a port of the book's verifier (`textbook/tools/verify_matter_models.py`, the
transfer section), done exactly over the integers, with the states and the order of the modes of
`scripts/certificates/matter_models.py` (the mode `(v, c, s)` of the edge is the bit
`6 v + 2 c + s`).

* The words of Theorem 13.8: `6 L = Σ_{c, c'} sgn(c) sgn(c') X_{c₃c'₃} X_{c₂c'₂} X_{c₁c'₁}`, the
  sums over the orderings `c`, `c'` of the colours, with `X = A + A†` for a real triplet, and
  `X = A` plus the adjoint words for a complex one (`L6`).
* `6 L` on the sixty-four products of the eight (real) and on the thirty-six products of the six
  (complex): the image of each product is an integer combination of products (the columns
  `transferRCols`, `transferCCols`); `coords` asserts that nothing is left over, so `L` keeps the
  zero-flux sector.
* For the real triplets a common basis of eigenvectors of the number of quarks `N` and of `6 L`;
  for the complex ones, of `N` and of `(6 L)²` (whose matrix is the square of the columns), since
  `6 L` has the irrational values `±72 √2` at `N = 6`. Each with a matrix `D`, `D C = diag(d)`.

Run with no arguments; the Lean text goes to standard output.
"""

import os
import sys
from itertools import permutations

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import matter_models as mm  # noqa: E402

code = mm.code
PERMS = list(permutations(range(3)))


def A(c, cp):
    """`A_{cc'} = Σ_s a†_{ycs} a_{xc's}`."""
    return [(1, [(1, code(1, c, s)), (0, code(0, cp, s))]) for s in range(2)]


def Ad(c, cp):
    """`A_{cc'}† = Σ_s a†_{xc's} a_{ycs}`."""
    return [(1, [(1, code(0, cp, s)), (0, code(1, c, s))]) for s in range(2)]


def B(c, cp):
    return A(c, cp) + Ad(c, cp)


def L6(vec, real):
    """`6 L` on a vector: `X_{c₁c'₁}` acts first."""
    out = {}
    for c in PERMS:
        for cp in PERMS:
            w = mm.eps(*c) * mm.eps(*cp)
            if real:
                v = mm.apply_op(B(c[0], cp[0]), vec)
                v = mm.apply_op(B(c[1], cp[1]), v)
                v = mm.apply_op(B(c[2], cp[2]), v)
                out = mm.vadd(out, v, w)
            else:
                v = mm.apply_op(A(c[0], cp[0]), vec)
                v = mm.apply_op(A(c[1], cp[1]), v)
                v = mm.apply_op(A(c[2], cp[2]), v)
                out = mm.vadd(out, v, w)
                v = mm.apply_op(Ad(c[2], cp[2]), vec)
                v = mm.apply_op(Ad(c[1], cp[1]), v)
                v = mm.apply_op(Ad(c[0], cp[0]), v)
                out = mm.vadd(out, v, w)
    return out


def matmul_cols(K, M, n):
    """Columns of `K M` from columns of `K` and `M`."""
    return [[sum(K[k][i] * M[j][k] for k in range(n)) for i in range(n)] for j in range(n)]


def compute():
    n64 = [mm.NQ[j // 8] + mm.NQ[j % 8] for j in range(64)]
    six = mm.SIX
    n36 = [mm.NQ[six[j // 6]] + mm.NQ[six[j % 6]] for j in range(36)]
    KR = mm.int_cols([mm.coords(L6(b, True), mm.BASIS) for b in mm.BASIS])
    KC = mm.int_cols([mm.coords(L6(b, False), mm.BASIS36) for b in mm.BASIS36])
    NR = [[n64[j] if i == j else 0 for i in range(64)] for j in range(64)]
    NC = [[n36[j] if i == j else 0 for i in range(36)] for j in range(36)]
    KC2 = matmul_cols(KC, KC, 36)
    pR, DR, dR = mm.joint_certificate([NR, KR], 64, [range(0, 13), (-144, -36, 0, 36, 144)])
    pC, DC, dC = mm.joint_certificate([NC, KC2], 36, [range(0, 13), (0, 1296, 10368)])
    # the values of the book's table, `L = (6 L)/6`, by the number of quarks
    spec = {}
    for vals, _ in pR:
        spec.setdefault(vals[0], {})
        spec[vals[0]][vals[1] // 6] = spec[vals[0]].get(vals[1] // 6, 0) + 1
    assert spec == {0: {0: 1}, 2: {0: 2}, 3: {-6: 4, 6: 4}, 4: {0: 3}, 5: {-6: 4, 6: 4},
                    6: {-24: 1, 0: 18, 24: 1}, 7: {-6: 4, 6: 4}, 8: {0: 3}, 9: {-6: 4, 6: 4},
                    10: {0: 2}, 12: {0: 1}}, spec
    specC = {}
    for vals, _ in pC:
        specC.setdefault(vals[0], {})
        specC[vals[0]][vals[1]] = specC[vals[0]].get(vals[1], 0) + 1
    assert specC == {0: {0: 1}, 3: {1296: 8}, 6: {0: 16, 10368: 2}, 9: {1296: 8},
                     12: {0: 1}}, specC
    # the vectors of the complex certificate with `N = 6` and `(6 L)² = 0` are killed by `6 L`
    for vals, v in pC:
        if vals == [6, 0]:
            assert all(sum(KC[j][i] * v[j] for j in range(36)) == 0 for i in range(36))
    return dict(KR=KR, KC=KC, KC2=KC2, pR=pR, DR=DR, dR=dR, pC=pC, DC=DC, dC=dC)


HEADER = """import ArtformTextbook.Ch12.FockCalc

/-!
# Certificate data for the third-order transfer of Chapter 13

Written by `scripts/certificates/matter_transfer.py`; every claim about these data is checked by
`decide +kernel` in `Ch13/TransferCheck.lean`.

A vector is a list of `(index, coefficient)`; a matrix is the list of its columns. The products
are those of `Ch12/ModelsData.lean`: `8 a + b` for the eight states of one vertex, `6 a + b` for
the six.
-/

namespace Artform.TransferData

open FockCalc
"""


def main():
    d = compute()
    out = [HEADER]
    out += mm.lean_cols("transferRCols", "`6 L` for a real triplet in the basis of the sixty-four "
                        "products.", d["KR"])
    out += mm.lean_cols("transferCCols", "`6 L` for a complex triplet in the basis of the "
                        "thirty-six products of the six.", d["KC"])
    out += mm.lean_cols("transferC2Cols", "`(6 L)²` for a complex triplet, the square of "
                        "`transferCCols`.", d["KC2"])
    out += mm.lean_eigs("transferREig", "Common eigenvectors of the number of quarks and of "
                        "`6 L`, real triplet.", d["pR"], k=2)
    out += mm.lean_cols("transferRD", "The matrix `D` with `D C = diag(d)` for the "
                        "eigenvectors `C`, by columns.",
                        [[row[j] for row in d["DR"]] for j in range(64)])
    out += mm.lean_ints("transferRDg", "The diagonal `d`.", d["dR"])
    out += mm.lean_eigs("transferCEig", "Common eigenvectors of the number of quarks and of "
                        "`(6 L)²`, complex triplet.", d["pC"], k=2)
    out += mm.lean_cols("transferCD", "The matrix `D` with `D C = diag(d)` for the "
                        "eigenvectors `C`, by columns.",
                        [[row[j] for row in d["DC"]] for j in range(36)])
    out += mm.lean_ints("transferCDg", "The diagonal `d`.", d["dC"])
    out.append("end Artform.TransferData")
    print("\n".join(out))


if __name__ == "__main__":
    main()
