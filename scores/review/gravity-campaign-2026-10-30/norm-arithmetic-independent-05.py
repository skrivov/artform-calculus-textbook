#!/usr/bin/env python3
"""Exact original odd-norm replay for the F05/F06 fidelity audit.

Only rational polynomial arithmetic is used. Pinned source hashes bind the
replay to the reviewed definitions; the separate Lean proofs check the full
native identities and guarded equivalences in the kernel.
"""
from fractions import Fraction
import hashlib
import importlib.util
import json
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[3]
SOURCES = {
    "scores/ArtformScores/GravityBridge/Native/R2Defs.lean":
        "9c68dc22a29ced5934933f921b2e0980a358762fb649bbbb1e3ab65cbc854407",
    "scores/ArtformScores/GravityBridge/Native/R2PhaseDefs.lean":
        "9c52ebca8816fd6ab2687a237d96b6539d6ba1a4cf3fd45562e4c4d76a858d5d",
    "scores/review/gravity-campaign-2026-10-30/source-arithmetic-independent-02.py":
        "b6ac3553d0267699ed2d05528e0b02f94d509fd17518a4a55dad77f88aada2ba",
}


def main():
    for name, expected in SOURCES.items():
        assert hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == expected
    sys.dont_write_bytecode = True
    helper = Path(__file__).with_name("source-arithmetic-independent-02.py")
    spec = importlib.util.spec_from_file_location("independent_r2_polynomials", helper)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    polynomial = module.Polynomial
    variables = []
    for index in range(6):
        exponents = [0] * 6
        exponents[index] = 1
        variables.append(polynomial({tuple(exponents): Fraction(1)}))
    q, radius, a, gamma, s, imaginary = variables
    u = 1 + radius
    m = 1 + (2 + 3 * q ** 2) * radius + (1 + q ** 2) * radius ** 2
    v = 1 + (1 + q ** 2) * radius
    T = (m * a - v + imaginary * q * (1 - u * a)
         + gamma * (q * u + imaginary * m))
    even = ((1 + q ** 2) * u ** 2 * (a ** 2 + gamma ** 2)
            - (1 + q ** 2 * (2 * a - 1) ** 2 + 4 * q ** 2 * gamma ** 2))
    Delta = even + 4 * q * gamma
    h = a * s + 2 - 3 * a
    norm = 4 * h ** 2 * T * T.conjugate() - radius * s * (3 - s) * Delta ** 2
    reflected = polynomial({exponents: coefficient * (-1) ** exponents[3]
                            for exponents, coefficient in norm.terms.items()})
    difference = (norm - reflected - 16 * q * radius * gamma
                  * (2 * q ** 2 * h ** 2 - s * (3 - s) * even))
    assert not difference.terms

    # The exact necessary-domain witness uses (1+R)^2=1672/1295.
    t = Fraction(103, 2)
    G = Fraction(1, 36)
    latitude = Fraction(3, 2)
    source_h = Fraction(1, 2)
    u_squared = Fraction(1672, 1295)
    determinant_even = (1 + t) * u_squared * (1 + G) - (1 + t + 4 * t * G)
    assert determinant_even == Fraction(103, 9)
    assert latitude * (3 - latitude) * determinant_even == 2 * t * source_h ** 2
    assert u_squared > 1
    print(json.dumps({"odd_norm_identity_exact": True,
                      "difference_nonzero_coefficients": len(difference.terms),
                      "necessary_witness_even_delta": str(determinant_even),
                      "necessary_witness_one_plus_radius_squared": str(u_squared),
                      "source_sha256": SOURCES}))


if __name__ == "__main__":
    main()
