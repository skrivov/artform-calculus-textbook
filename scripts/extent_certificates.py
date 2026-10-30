#!/usr/bin/env python3
"""Write the certificates of T15's extents (the ledger's finding 043, Theorems S5.3 and S5.4).

A run of a group G under steps A and B is a word in A, B, A^-1 and B^-1 (the letters 0, 1, 2 and
3) that visits every element once, left multiplication from the identity, and comes back. This
script finds
  1. a forward word on SL(2, Z/n) and PSL(2, Z/n) for n = 2, 3, 6, 7, 9 and 12, under K = K(1) and
     M = M(-1), by annealing the choice on the cosets <c> x of c = A^-1 B;
  2. a word with exactly two back-steps on SL and PSL for n = 4, 5, 10 and 13, and on the two
     squares (Theorem Y of finding 038), from the placements of the second back-step that the
     balance allows: the offset of the first lies in <c> x_1;
  3. a word with exactly three back-steps on PSL(2, Z/8);
  4. the index of the coset of each element where the extents are counted, n = 2, 3 and 6;
and writes scores/ArtformScores/Certificates/Extents.lean, which Lean checks with `decide +kernel`
(scores/ArtformScores/Runs.lean, ExtentTable.lean). The search is seeded.

  python3 scripts/extent_certificates.py           writes the file
  python3 scripts/extent_certificates.py --check   fails if the file differs from its output
"""
import argparse
import math
import random
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "scores" / "ArtformScores" / "Certificates" / "Extents.lean"
FORWARD = (2, 3, 6, 7, 9, 12)
TWO_BACK = (4, 5, 10, 13)
COUNTED = (2, 3, 6)
CHUNK = 64                       # letters to a chunk, 128 bits


# ---------------------------------------------------------------- the groups
class Group:
    """elems[0] is the identity; tab[s][i] is the index of letter(s) * elems[i]."""

    def __init__(self, elems, tab, code):
        self.elems, self.tab, self.code = elems, tab, code
        self.size = len(elems)


def closure(gens, identity, mul, canon):
    elems = [canon(identity)]
    index = {elems[0]: 0}
    i = 0
    while i < len(elems):
        x = elems[i]
        i += 1
        for s in gens:
            y = canon(mul(s, x))
            if y not in index:
                index[y] = len(elems)
                elems.append(y)
    tab = [[index[canon(mul(s, x))] for x in elems] for s in gens]
    return elems, tab


def matrices(n, proj):
    def mul(p, q):
        return ((p[0] * q[0] + p[1] * q[2]) % n, (p[0] * q[1] + p[1] * q[3]) % n,
                (p[2] * q[0] + p[3] * q[2]) % n, (p[2] * q[1] + p[3] * q[3]) % n)

    def code(x):
        return ((x[0] * n + x[1]) * n + x[2]) * n + x[3]

    def canon(x):
        return min(x, tuple((n - v) % n for v in x)) if proj else x

    gens = [(1 % n, 0, 1 % n, 1 % n), (1 % n, (n - 1) % n, 0, 1 % n),
            (1 % n, 0, (n - 1) % n, 1 % n), (1 % n, 1 % n, 0, 1 % n)]
    elems, tab = closure(gens, (1 % n, 0, 0, 1 % n), mul, canon)
    return Group(elems, tab, code)


def two_squares():
    """the book's turns of the six corners: L = (0 1 2 3), R = (1 4 5 2)"""
    left = (1, 2, 3, 0, 4, 5)
    right = (0, 4, 1, 3, 5, 2)

    def inv(p):
        q = [0] * len(p)
        for i, v in enumerate(p):
            q[v] = i
        return tuple(q)

    def mul(s, x):
        return tuple(s[v] for v in x)

    def code(x):
        out = 0
        for v in x:
            out = out * 6 + v
        return out

    gens = [left, right, inv(left), inv(right)]
    elems, tab = closure(gens, (0, 1, 2, 3, 4, 5), mul, lambda x: x)
    return Group(elems, tab, code)


# ---------------------------------------------------------------- the search
def solve(group, backs, rng, iters):
    """A word with the back-steps `backs`, a list of (element, letter 2 or 3), or None."""
    size = group.size
    t_a, t_b, t_ai, _ = group.tab
    back = dict(backs)
    targets = set()
    for v, s in backs:
        y = group.tab[s][v]
        if y in targets:
            return None
        targets.add(y)
    parent = list(range(size))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    forced = {}

    def force(x, value):
        r = find(x)
        if r in forced and forced[r] != value:
            return False
        forced[r] = value
        return True

    def union(x, y):
        rx, ry = find(x), find(y)
        if rx == ry:
            return True
        if rx in forced and ry in forced and forced[rx] != forced[ry]:
            return False
        parent[rx] = ry
        if rx in forced:
            forced[ry] = forced[rx]
        return True

    for v in range(size):
        u = t_ai[t_b[v]]             # u = c v, so A u = B v
        if t_b[v] in targets:
            if u not in back and not force(u, 1):
                return None
            if v not in back and not force(v, 0):
                return None
        elif v in back and u in back:
            return None
        elif v in back:
            if not force(u, 0):
                return None
        elif u in back:
            if not force(v, 1):
                return None
        elif not union(u, v):
            return None
    classes = {}
    for v in range(size):
        if v not in back:
            classes.setdefault(find(v), []).append(v)
    free = [r for r in classes if r not in forced]
    choice = [0] * size
    for r, members in classes.items():
        value = forced.get(r, rng.randint(0, 1))
        for v in members:
            choice[v] = value
    succ = [group.tab[back[v]][v] if v in back else (t_b[v] if choice[v] else t_a[v])
            for v in range(size)]
    if sorted(succ) != list(range(size)):
        return None

    def cycles():
        seen = bytearray(size)
        count = 0
        for i in range(size):
            if not seen[i]:
                count += 1
                j = i
                while not seen[j]:
                    seen[j] = 1
                    j = succ[j]
        return count

    current = cycles()
    temperature = 1.0
    for _ in range(iters):
        if current == 1:
            break
        if not free:
            return None
        members = classes[free[rng.randrange(len(free))]]
        for v in members:
            choice[v] ^= 1
            succ[v] = t_b[v] if choice[v] else t_a[v]
        new = cycles()
        delta = new - current
        if delta <= 0 or rng.random() < math.exp(-delta / temperature):
            current = new
        else:
            for v in members:
                choice[v] ^= 1
                succ[v] = t_b[v] if choice[v] else t_a[v]
        temperature = max(0.1, temperature * 0.999)
    if current != 1:
        return None
    word = []
    x = 0
    for _ in range(size):
        word.append(back[x] if x in back else choice[x])
        x = succ[x]
    return word


def powers_of_c(group, start):
    t_b, t_ai = group.tab[1], group.tab[2]
    out = [start]
    x = t_ai[t_b[start]]
    while x != start:
        out.append(x)
        x = t_ai[t_b[x]]
    return out


def offset(group, s, x):
    """B^-1 applied to the target of a back-step: the offset, s = 2 or 3"""
    return group.tab[3][group.tab[s][x]]


def forward_word(group, rng):
    while True:
        word = solve(group, [], rng, 200000)
        if word:
            return word


def two_back_word(group, rng):
    """the second back-step lies on the coset of the first back-step's offset"""
    while True:
        for s0 in (2, 3):
            for x1 in powers_of_c(group, offset(group, s0, 0)):
                if x1 == 0:
                    continue
                for s1 in (2, 3):
                    word = solve(group, [(0, s0), (x1, s1)], rng, 3000)
                    if word:
                        return word


def three_back_word(group, rng):
    while True:
        for s0 in (2, 3):
            for x1 in powers_of_c(group, offset(group, s0, 0)):
                for s1 in (2, 3):
                    for x2 in powers_of_c(group, offset(group, s1, x1)):
                        if 0 in (x1, x2) or x1 == x2:
                            continue
                        for s2 in (2, 3):
                            word = solve(group, [(0, s0), (x1, s1), (x2, s2)], rng, 3000)
                            if word:
                                return word


def verify(group, word):
    x = 0
    seen = set()
    for s in word:
        assert x not in seen
        seen.add(x)
        x = group.tab[s][x]
    assert x == 0 and len(seen) == group.size


def coset_table(group):
    """the digits, four bits each, of the index of the coset <c> x at the code of x"""
    index = {}
    count = 0
    for i in sorted(range(group.size), key=lambda j: group.code(group.elems[j])):
        if i not in index:
            for x in powers_of_c(group, i):
                index[x] = count
            count += 1
    table = 0
    for i, c in index.items():
        table |= c << (4 * group.code(group.elems[i]))
    return table, count


# ---------------------------------------------------------------- the file
def pack_word(word):
    chunks = []
    for i in range(0, len(word), CHUNK):
        chunks.append(sum(c << (2 * j) for j, c in enumerate(word[i:i + CHUNK])))
    return chunks


def pack_number(number):
    chunks = []
    while number:
        chunks.append(number & ((1 << 128) - 1))
        number >>= 128
    return chunks or [0]


def lean_def(name, doc, chunks):
    words = doc.split()
    head, line = [], "/--"
    for word in words:
        if len(line) + len(word) + 1 > 95:
            head.append(line)
            line = word
        else:
            line += " " + word
    head.append(line + " -/")
    lines = head + [f"def {name} : ℕ := pack ["]
    for i in range(0, len(chunks), 2):
        tail = "]" if i + 2 >= len(chunks) else ","
        lines.append("  " + ", ".join(str(c) for c in chunks[i:i + 2]) + tail)
    return "\n".join(lines)


def lean_file():
    rng = random.Random(11)
    parts = []
    letters = "`0`, `1`, `2`, `3` are `K`, `M`, `K⁻¹`, `M⁻¹`"
    for n in FORWARD:
        for proj in (False, True):
            group = matrices(n, proj)
            word = forward_word(group, rng)
            verify(group, word)
            name = "PSL" if proj else "SL"
            parts.append(lean_def(f"word{name}{n}",
                                  f"A forward extent of `{name}(2, Z/{n})`, {group.size} letters: "
                                  f"{letters}.", pack_word(word)))
    for n in TWO_BACK:
        for proj in (False, True):
            group = matrices(n, proj)
            word = two_back_word(group, rng)
            verify(group, word)
            name = "PSL" if proj else "SL"
            parts.append(lean_def(f"word{name}{n}",
                                  f"A run of `{name}(2, Z/{n})` with two back-steps, {group.size} "
                                  f"letters: {letters}.", pack_word(word)))
    group = matrices(8, True)
    word = three_back_word(group, rng)
    verify(group, word)
    parts.append(lean_def("wordPSL8", f"A run of `PSL(2, Z/8)` with three back-steps, {group.size} "
                          f"letters: {letters}.", pack_word(word)))
    group = two_squares()
    word = two_back_word(group, rng)
    verify(group, word)
    parts.append(lean_def("wordSquares", "A run of the two squares with two back-turns, 120 "
                          "letters: `0`, `1`, `2`, `3` are `L`, `R`, `L⁻¹`, `R⁻¹`.",
                          pack_word(word)))
    for n in COUNTED:
        for proj in (False, True):
            group = matrices(n, proj)
            table, count = coset_table(group)
            name = "PSL" if proj else "SL"
            parts.append(lean_def(f"cosets{name}{n}",
                                  f"The cosets of `c` in `{name}(2, Z/{n})`, {count} of them: four "
                                  f"bits at each code.", pack_number(table)))
    head = """import ArtformScores.Runs

/-!
# The certificates of T15's extents

Generated by `scripts/extent_certificates.py`; do not edit by hand. Each word is a run of a group
under its two steps, packed in base 4, the first letter lowest; `Runs.lean` checks it. The tables of
cosets serve the exact counts of extents.
-/

namespace Artform.Scores.Bells.Cert

"""
    return head + "\n\n".join(parts) + "\n\nend Artform.Scores.Bells.Cert\n"


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    text = lean_file()
    if args.check:
        if not OUT.exists() or OUT.read_text(encoding="utf-8") != text:
            print(f"problem: {OUT.relative_to(ROOT)} differs from the generator's output")
            sys.exit(1)
        print("the extent certificates are the generator's output")
    else:
        OUT.parent.mkdir(parents=True, exist_ok=True)
        OUT.write_text(text, encoding="utf-8")
        print(f"wrote {OUT.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
