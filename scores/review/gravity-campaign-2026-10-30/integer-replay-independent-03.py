#!/usr/bin/env python3
"""Independent integer convolution of the frozen native R2 unit certificate.

This does not import its producer or use the exported native row table.
The eight native definition bridges are checked separately by Lean.
"""
from fractions import Fraction
import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
CERTIFICATE = ROOT / "scores/certificates/gravity-r2-zero-row.json"
EXPECTED_SHA256 = "92369c1881fe5b7cbf1df8cc5028acc3295870bb2433d35a819ab7a75dbb7d4e"


def integer_polynomial(terms):
    result = {}
    for coefficient, exponents in terms:
        assert type(coefficient) in (int, str)
        rational = Fraction(coefficient)
        assert rational.denominator == 1
        assert len(exponents) == 3
        assert all(type(exponent) is int and exponent >= 0 for exponent in exponents)
        monomial = tuple(exponents)
        assert monomial not in result
        result[monomial] = rational.numerator
    return result


def main():
    raw = CERTIFICATE.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == EXPECTED_SHA256
    data = json.loads(raw)
    generators = [integer_polynomial(terms) for terms in data["generators"]]
    multipliers = [integer_polynomial(terms) for terms in data["multipliers"]]
    assert len(generators) == len(multipliers) == 8
    total = {}
    products = 0
    for multiplier, generator in zip(multipliers, generators):
        for left, left_coefficient in multiplier.items():
            for right, right_coefficient in generator.items():
                monomial = tuple(x + y for x, y in zip(left, right))
                total[monomial] = total.get(monomial, 0) + left_coefficient * right_coefficient
                products += 1
    nonzero = {monomial: coefficient for monomial, coefficient in total.items() if coefficient}
    constant = int(data["nonzero_constant"])
    assert constant > 0 and len(str(constant)) == 302
    assert nonzero == {(0, 0, 0): constant}
    assert products == 14912 and len(total) == 294
    print(json.dumps({"identity_verified": True, "integer_products": products,
                      "collected_monomials": len(total), "nonzero_monomials": len(nonzero),
                      "positive_constant_digits": len(str(constant)),
                      "certificate_sha256": EXPECTED_SHA256}))


if __name__ == "__main__":
    main()
