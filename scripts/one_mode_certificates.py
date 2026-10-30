#!/usr/bin/env python3
"""Write the certificates of T4, completeness on one mode, for p = 5, 7, 11 and 13.

The group presented by merging (R1) and Whitehead's rule (R3) on X = M(1) and Y = K(1)
over ZMod p. For each p this script
  1. enumerates the cosets of H = <X> (Todd-Coxeter, HLT, after Holt, Eick and O'Brien,
     Handbook of Computational Group Theory, 2005, section 5.1), which gives p^2 - 1 rows;
  2. picks a word for each row along a breadth-first tree from row 0;
  3. justifies every other edge of the table by a deduction: a relator, traced from a
     row, whose other edges are justified at earlier times;
  4. writes scores/ArtformScores/Certificates/OneMode<p>.lean, which Lean checks with
     `decide +kernel` (scores/ArtformScores/Coset.lean, OneMode.lean).
The relators of the deductions are X^p, Y^p, and Whitehead's rule at every unit u with
the exponent 1, written with the exponents between -(p - 1)/2 and (p - 1)/2.

  python3 scripts/one_mode_certificates.py           writes the four files
  python3 scripts/one_mode_certificates.py --check   fails if a file differs from its output
"""
import argparse
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUT_DIR = ROOT / "scores" / "ArtformScores" / "Certificates"
PRIMES = (5, 7, 11, 13)
X, x, Y, y = 0, 1, 2, 3          # the letters X, X^-1, Y, Y^-1; g ^ 1 inverts g


# ---------------------------------------------------------------- words
def pw(g, k):
    """the power g^k as a word"""
    return [g] * k if k >= 0 else [g ^ 1] * (-k)


def reduce(word):
    out = []
    for g in word:
        if out and out[-1] == g ^ 1:
            out.pop()
        else:
            out.append(g)
    return out


def sym(k, p):
    """the representative of k mod p between -(p - 1)/2 and (p - 1)/2"""
    k %= p
    return k - p if k > p // 2 else k


def descriptors(p):
    """the relators: X^p, Y^p, then w(u) M(1) w(u)^-1 = K(-u^-2) and w(u) K(1) w(u)^-1 = M(-u^2)
    for u = 1, ..., p - 1, with w(u) = M(u) K(-u^-1) M(u); the word of each as in Lean's Desc.word"""
    inv = lambda u: pow(u, -1, p)
    ds = [(".powX", [X] * p), (".powY", [Y] * p)]
    for kind, last in ((".rm", Y), (".rk", X)):
        for u in range(1, p):
            a, b = sym(u, p), sym(-inv(u), p)
            c = sym(-(inv(u) * inv(u)), p) if kind == ".rm" else sym(-(u * u), p)
            mid = Y if kind == ".rk" else X
            word = reduce(pw(X, a) + pw(Y, b) + pw(X, a) + [mid] + pw(X, -a) + pw(Y, -b) + pw(X, -a) +
                          pw(last, -c))
            ds.append((f"{kind} {u} {inv(u)} {lean_int(a)} {lean_int(b)} {lean_int(c)}", word))
    return ds


def lean_int(k):
    return f"({k})" if k < 0 else str(k)


def standard_relators(p):
    """merging and Whitehead's rule as in the ledger's enumerator (code/scheme_presentation.py)"""
    inv = lambda u: pow(u, -1, p)
    w = lambda u: [X] * (u % p) + [Y] * (-inv(u) % p) + [X] * (u % p)
    rels = [[X] * p, [Y] * p]
    for u in range(1, p):
        wi = [g ^ 1 for g in reversed(w(u))]
        rels.append(w(u) + [X] + wi + [Y] * (inv(u) * inv(u) % p))
        rels.append(w(u) + [Y] + wi + [X] * (u * u % p))
    out = []
    for r in rels:
        r = reduce(r)
        while len(r) >= 2 and r[0] == r[-1] ^ 1:
            r = r[1:-1]
        out.append(r)
    return out


# ---------------------------------------------------------------- Todd-Coxeter (HLT)
class CosetTable:
    def __init__(self):
        self.tab, self.p = [[None] * 4], [0]

    def rep(self, k):
        l = k
        while self.p[l] != l:
            l = self.p[l]
        while self.p[k] != l:
            self.p[k], k = l, self.p[k]
        return l

    def merge(self, k, l, q):
        k, l = self.rep(k), self.rep(l)
        if k != l:
            self.p[max(k, l)] = min(k, l)
            q.append(max(k, l))

    def coincidence(self, a, b):
        q = []
        self.merge(a, b, q)
        i = 0
        while i < len(q):
            g = q[i]
            i += 1
            for s in range(4):
                d = self.tab[g][s]
                if d is None:
                    continue
                if self.tab[d][s ^ 1] == g:
                    self.tab[d][s ^ 1] = None
                mu, nu = self.rep(g), self.rep(d)
                if self.tab[mu][s] is not None:
                    self.merge(nu, self.tab[mu][s], q)
                elif self.tab[nu][s ^ 1] is not None:
                    self.merge(mu, self.tab[nu][s ^ 1], q)
                else:
                    self.tab[mu][s], self.tab[nu][s ^ 1] = nu, mu

    def define(self, c, s):
        n = len(self.tab)
        self.tab.append([None] * 4)
        self.p.append(n)
        self.tab[c][s], self.tab[n][s ^ 1] = n, c

    def scan_and_fill(self, a, w):
        r, f, i, b, j = len(w), a, 0, a, len(w) - 1
        while True:
            while i < r and self.tab[f][w[i]] is not None:
                f, i = self.tab[f][w[i]], i + 1
            if i >= r:
                if f != a:
                    self.coincidence(f, a)
                return
            while j >= i and self.tab[b][w[j] ^ 1] is not None:
                b, j = self.tab[b][w[j] ^ 1], j - 1
            if j < i:
                self.coincidence(f, b)
                return
            if i == j:
                self.tab[f][w[i]], self.tab[b][w[i] ^ 1] = b, f
                return
            self.define(f, w[i])

    def run(self, rels, subgroup):
        for w in subgroup:
            self.scan_and_fill(0, w)
        a = 0
        while a < len(self.tab):
            for w in rels:
                if self.p[a] != a:
                    break
                self.scan_and_fill(a, w)
            if self.p[a] == a:
                for s in range(4):
                    if self.tab[a][s] is None:
                        self.define(a, s)
            a += 1
        live = [c for c in range(len(self.tab)) if self.p[c] == c]
        idx = {c: k for k, c in enumerate(live)}
        return [[idx[self.rep(self.tab[c][s])] for s in range(4)] for c in live]


# ---------------------------------------------------------------- the certificate
def edge(T, c, g):
    """the edge (row, generator) a letter uses at row c, and the row it leads to"""
    if g in (X, Y):
        return (c, g), T[c][g]
    d = T[c][g]
    return (d, g ^ 1), d


def certificate(p):
    T = CosetTable().run(standard_relators(p), subgroup=([X],))
    n = len(T)
    assert n == p * p - 1, (p, n)
    words, order, just = [None] * n, [0], {}
    words[0] = []
    for c in order:
        for g in range(4):
            d = T[c][g]
            if words[d] is None:
                words[d] = words[c] + [g]
                order.append(d)
                just[(c, g) if g in (X, Y) else (d, g ^ 1)] = ".tree"
    assert T[0][X] == 0
    just[(0, X)] = ".subgroup"
    ds = descriptors(p)
    t = 0
    while len(just) < 2 * n:
        t += 1
        new = {}
        for ri, (_, w) in enumerate(ds):
            for c in range(n):
                es, cur = [], c
                for g in w:
                    e, cur = edge(T, cur, g)
                    es.append(e)
                assert cur == c, "a relator does not close"
                unknown = [k for k, e in enumerate(es) if e not in just]
                if len(unknown) == 1 and es[unknown[0]] not in new:
                    new[es[unknown[0]]] = f".deduce {t} {ri} {c} {unknown[0]}"
        assert new, f"p = {p}: the deductions stall"
        just.update(new)

    def bottom(w):
        c, d = 0, 1
        for g in w:
            c, d = {X: (c, c + d), x: (c, d - c), Y: (c + d, d), y: (c - d, d)}[g]
            c, d = c % p, d % p
        return c, d
    assert all(bottom(words[j]) != (0, 1) for j in range(1, n))
    return T, words, just, ds, t


# ---------------------------------------------------------------- Lean
def wrap(items, indent="    ", width=100):
    lines, cur = [], indent + "["
    for k, it in enumerate(items):
        piece = it + ("]" if k == len(items) - 1 else ",")
        if len(cur) + 1 + len(piece) > width and cur.strip() != "[":
            lines.append(cur)
            cur = indent + " " + piece
        else:
            cur = cur + ("" if cur.endswith("[") else " ") + piece
    lines.append(cur if items else indent + "[]")
    return "\n".join(lines)


def lean_file(p):
    T, words, just, ds, rounds = certificate(p)
    n = len(T)
    col = lambda g: wrap([str(T[i][g]) for i in range(n)])
    deductions = sum(1 for j in just.values() if j.startswith(".deduce"))
    return f"""import ArtformScores.OneMode

/-!
# The certificate of T4 at `p = {p}`

Generated by `scripts/one_mode_certificates.py`; do not edit by hand. The coset
table of `H = ⟨X⟩` in the group presented by merging and Whitehead's rule over
`ZMod {p}`: {n} rows, the action of `X` and `Y` and of their inverses, a word for
each row, and a justification for each of the {2 * n} edges. The {deductions} deductions
use {len(ds)} relators and take {rounds} rounds.
-/

namespace Artform.Scores.OneMode.Cert{p}

open Matrix (SpecialLinearGroup)

/-- The row that `X` takes each row to. -/
def fwdX : List ℕ :=
{col(X)}

/-- The row that `Y` takes each row to. -/
def fwdY : List ℕ :=
{col(Y)}

/-- The row that `X⁻¹` takes each row to. -/
def bwdX : List ℕ :=
{col(x)}

/-- The row that `Y⁻¹` takes each row to. -/
def bwdY : List ℕ :=
{col(y)}

/-- The word of each row, along a breadth-first tree from row `0`, in the letters
`0 = X`, `1 = X⁻¹`, `2 = Y` and `3 = Y⁻¹` (`letterOf`). -/
def words : List (List ℕ) :=
{wrap(["[" + ", ".join(str(g) for g in w) + "]" for w in words])}

/-- The justification of each edge `(i, X)` and `(i, Y)`, at index `2 i` and `2 i + 1`. -/
def just : List Coset.Just :=
{wrap([just[(i, g)] for i in range(n) for g in (X, Y)])}

/-- The relators of the deductions. -/
def descs : List (Desc {p}) :=
{wrap([d for d, _ in ds])}

/-- The certificate. -/
def cert : Coset.Cert Gen where
  n := {n}
  fwd a i := match a with
    | .X => fwdX.getD i 0
    | .Y => fwdY.getD i 0
  bwd a i := match a with
    | .X => bwdX.getD i 0
    | .Y => bwdY.getD i 0
  word i := (words.getD i []).map letterOf
  just i a := just.getD (2 * i + match a with | .X => 0 | .Y => 1) .tree
  rels := descs.map Desc.word

/-- T4 at `p = {p}`. -/
theorem complete :
    (∀ A : SpecialLinearGroup (Fin 2) (ZMod {p}), ∃ v, law {p} v = A) ∧
      ∀ v₁ v₂ : FreeGroup Gen, law {p} v₁ = law {p} v₂ ↔
        PresentedGroup.mk (relators {p}) v₁ = PresentedGroup.mk (relators {p}) v₂ := by
  have : Fact (Nat.Prime {p}) := ⟨by norm_num⟩
  exact complete_of_cert {p} cert descs rfl (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel)

end Artform.Scores.OneMode.Cert{p}
"""


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    bad = False
    for p in PRIMES:
        path = OUT_DIR / f"OneMode{p}.lean"
        text = lean_file(p)
        if args.check:
            if not path.exists() or path.read_text(encoding="utf-8") != text:
                print(f"problem: {path.relative_to(ROOT)} differs from the generator's output")
                bad = True
        else:
            OUT_DIR.mkdir(parents=True, exist_ok=True)
            path.write_text(text, encoding="utf-8")
            print(f"wrote {path.relative_to(ROOT)}")
    if args.check and not bad:
        print("the certificates are the generator's output")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
