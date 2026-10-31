"""Exact independent replay of the sixteen-site Grams and loop pair factors.

This supports fidelity review. It does not replace universal Lean proofs or
identify the finite Euclidean model with a native gravity regulator.
"""
from collections import Counter
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path


def character(k, x):
    return -1 if (k & x).bit_count() % 2 else 1


def gram(left, right, k, l):
    return sum((left[x][k] * right[x][l] for x in range(16)), Q(0))


def coefficients(k):
    return (1, k & 1, (k >> 1).bit_count())


def precision(k):
    a, temporal, spatial = coefficients(k)
    return Q(a + 2 * temporal + spatial)


walsh = [[Q(character(k, x), 4) for k in range(16)] for x in range(16)]
differences = [
    [[walsh[x ^ (1 << i)][k] - walsh[x][k] for k in range(16)] for x in range(16)]
    for i in range(4)
]
source_grams = []
difference_grams = []
for i in range(4):
    source = [[sum((walsh[x][k] * character(1 << i, x) * walsh[x][l]
                    for x in range(16)), Q(0)) for l in range(16)] for k in range(16)]
    difference = [[gram(differences[i], differences[i], k, l)
                   for l in range(16)] for k in range(16)]
    for k in range(16):
        for l in range(16):
            assert source[k][l] == int(l == (k ^ (1 << i)))
            assert difference[k][l] == (4 * ((k >> i) & 1) if k == l else 0)
    source_grams.append(source)
    difference_grams.append(difference)

for k in range(16):
    for l in range(16):
        mass = gram(walsh, walsh, k, l)
        assert mass == int(k == l)
        # Coefficients of 1,ct,cs in the actual local precision Gram.
        actual = (mass, difference_grams[0][k][l] / 4,
                  sum((difference_grams[i][k][l] for i in range(1, 4)), Q(0)) / 4)
        expected = coefficients(k) if k == l else (0, 0, 0)
        assert actual == expected

responses = []
pair_reciprocals = []
weight_histograms = []
symbolic_response_terms = []
for i in range(4):
    mask = 1 << i
    reps = [k for k in range(16) if not k & mask]
    pairs = [(k, k ^ mask) for k in reps]
    assert len(reps) == 8
    assert sorted(x for pair in pairs for x in pair) == list(range(16))
    assert all(a != b for a, b in pairs)
    weights = [precision(a) * precision(b) for a, b in pairs]
    assert all(precision(k) >= 1 for k in range(16))
    assert all(w >= 1 for w in weights)
    full = sum((1 / (precision(k) * precision(k ^ mask)) for k in range(16)), Q(0))
    half = sum((1 / w for w in weights), Q(0))
    assert half == full / 2
    # The local interaction has prefactor s/2, while both off-diagonal
    # Gram entries contribute; each normal pair therefore has cross term s*u*v.
    for a, b in pairs:
        assert Q(1, 2) * (source_grams[i][a][b] + source_grams[i][b][a]) == 1
    responses.append(full)
    pair_reciprocals.append(half)
    weight_histograms.append(dict(sorted(Counter(str(w) for w in weights).items())))
    symbolic_response_terms.append(Counter(
        tuple(sorted((coefficients(k), coefficients(k ^ mask)))) for k in range(16)))

assert symbolic_response_terms[1] == symbolic_response_terms[2] == symbolic_response_terms[3]
assert responses == [Q(19, 10), Q(34, 15), Q(34, 15), Q(34, 15)]
loop_coefficients = [-r / 4 for r in responses]
assert loop_coefficients[0] == -Q(19, 40)
assert loop_coefficients[1] == -Q(17, 30)
assert loop_coefficients[0] - loop_coefficients[1] == Q(11, 120)
assert 8 * Q(1, 10) ** 4 == Q(1, 1250)

repo = Path(__file__).resolve().parents[3]
files = [f"scores/ArtformScores/GravityBridge/{name}{suffix}.lean"
         for name in ("Regulator", "Loop") for suffix in ("Defs", "Statements", "")]
result = {
    "orthogonality_entries": 256,
    "source_gram_entries": 1024,
    "difference_gram_entries": 1024,
    "local_precision_coefficient_triples": 256,
    "pairs_per_axis": 8,
    "source_half_factor_checked": True,
    "generic_spatial_response_multisets_equal": True,
    "responses": [str(x) for x in responses],
    "pair_reciprocal_sums": [str(x) for x in pair_reciprocals],
    "pair_weight_histograms": weight_histograms,
    "loop_coefficients": [str(x) for x in loop_coefficients],
    "temporal_minus_spatial": str(loop_coefficients[0] - loop_coefficients[1]),
    "example_fourth_order_bound": str(8 * Q(1, 10) ** 4),
    "reviewed_file_sha256": {f: hashlib.sha256((repo / f).read_bytes()).hexdigest() for f in files},
    "scope": "Exact rational finite-regulator replay; no native or continuum-speed conclusion."
}
print(json.dumps(result, indent=2))
