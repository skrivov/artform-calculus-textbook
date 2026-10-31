#!/usr/bin/env python3
"""Replay the exact native R2 inputs/identity and regenerate their Lean data.

Python standard library only. The Lean proof checks the identity and the native
definition bridge independently of this producer and sparse rational checker.
"""

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CERTIFICATE = ROOT / "scores/certificates/gravity-r2-zero-row.json"
ROW_INPUT = ROOT / "scores/certificates/gravity-r2-row-input.json"
LEAN = ROOT / "scores/ArtformScores/GravityBridge/Native/R2CertificateData.lean"


def polynomial(terms):
    result = {}
    for c, m in terms:
        if len(m) != 3 or any(type(e) is not int or e < 0 for e in m):
            raise ValueError("Invalid exponent")
        m = tuple(m)
        if m in result:
            raise ValueError("Repeated monomial")
        if Fraction(c):
            result[m] = Fraction(c)
    return result


def add(p, q):
    result = dict(p)
    for m, c in q.items():
        result[m] = result.get(m, Fraction(0)) + c
    return {m: c for m, c in result.items() if c}


def scale(p, c):
    return {m: Fraction(c) * a for m, a in p.items() if c * a}


def multiply(p, q):
    result = {}
    for m, c in p.items():
        for n, d in q.items():
            k = tuple(x + y for x, y in zip(m, n))
            result[k] = result.get(k, Fraction(0)) + c * d
    return {m: c for m, c in result.items() if c}


def verify(data):
    raw = ROW_INPUT.read_bytes()
    if hashlib.sha256(raw).hexdigest() != data["row_input_sha256"]:
        raise ValueError("Native input hash mismatch")
    rows = json.loads(raw)["affine_coefficients"]
    gs = [polynomial(p) for p in data["generators"]]
    ws = [polynomial(p) for p in data["multipliers"]]
    if len(gs) != 8 or len(ws) != 8:
        raise ValueError("Eight inputs and eight multipliers are required")
    b2 = {(0, 2, 0): Fraction(9), (0, 1, 0): Fraction(-12), (0, 0, 0): Fraction(4)}
    for i, name in enumerate(["Pe", "Qe", "Po", "Qo"]):
        for kind, index in [("n", i), ("ell", i + 4)]:
            record = rows[name][kind]
            source = scale(polynomial(record["terms"]), Fraction(record["content"]))
            content = Fraction(data["native_scales"][index])
            if not content:
                raise ValueError("A removed rational content is zero")
            reconstructed = scale(gs[index], content)
            if kind == "n":
                reconstructed = multiply(b2, reconstructed)
            if source != reconstructed:
                raise ValueError(f"Native input mismatch: {name} {kind}")
    d = int(data["nonzero_constant"])
    if d <= 0:
        raise ValueError("Certificate constant must be positive")
    total = {}
    for w, g in zip(ws, gs):
        total = add(total, multiply(w, g))
    if total != {(0, 0, 0): Fraction(d)}:
        raise ValueError("Exact characteristic-zero identity failed")


def expression(terms):
    result = []
    for c, m in terms:
        term = f"({c})"
        for name, power in zip(["R", "a", "G"], m):
            if power:
                term += " * " + name + (f" ^ {power}" if power > 1 else "")
        result.append(term)
    return " +\n    ".join(result) if result else "0"


def lean_source(data):
    result = '''import ArtformScores.GravityBridge.Native.R2Defs

/-! # Explicit integer data for the native R2 all-zero certificate

Each polynomial is generated from the replayed rational certificate. The
following proof module verifies their complete identity in Lean's kernel.
-/

namespace Artform.Scores.GravityBridge.Native.R2.Certificate

-- A single exact certificate integer has up to 307 digits.
set_option linter.style.longLine false

'''
    for name, key in [("g", "generators"), ("w", "multipliers")]:
        for i, terms in enumerate(data[key]):
            result += f"noncomputable def {name}{i} (R a G : ℝ) : ℝ :=\n    "
            result += expression(terms) + "\n\n"
    result += "noncomputable def nonzeroConstant : ℝ :=\n  "
    result += data["nonzero_constant"] + "\n\n"
    result += "end Artform.Scores.GravityBridge.Native.R2.Certificate\n"
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--write", action="store_true")
    group.add_argument("--check", action="store_true")
    args = parser.parse_args()
    data = json.loads(CERTIFICATE.read_text())
    verify(data)
    source = lean_source(data)
    if args.write:
        LEAN.write_text(source)
    elif LEAN.read_text() != source:
        raise SystemExit("Stale native R2 Lean certificate data")
    print(json.dumps({"identity_verified": True, "native_inputs_verified": 8,
                      "data_matches_lean": True,
                      "sha256": hashlib.sha256(CERTIFICATE.read_bytes()).hexdigest()}))


if __name__ == "__main__":
    main()
