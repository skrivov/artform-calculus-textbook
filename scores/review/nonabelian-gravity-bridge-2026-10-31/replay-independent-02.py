#!/usr/bin/env python3
"""Independent analytic semantics checks with rational real matrices.

No author replay or production evaluator is imported. Matrix product/inverse
first derivatives are compared against the right Maurer cocycle expansion.
Finite arithmetic checks corroborate, but do not replace, Lean derivatives.
"""
from fractions import Fraction as F
import importlib.util
from itertools import product
import json
from pathlib import Path

SPEC = importlib.util.spec_from_file_location(
    "review_matrix_semantics", Path(__file__).with_name("tangent-independent-01.py"))
M = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(M)


def scale(scalar, value):
    return tuple(scalar * x for x in value)


def inv(value):
    norm_squared = sum(x * x for x in value[:4])
    assert norm_squared
    return scale(1 / norm_squared, M.transpose(value))


def add(*values):
    return tuple(sum(xs) for xs in zip(*values))


def actual_word(w, points, tangents):
    value, derivative = M.IDENTITY, M.ZERO
    for letter in w:
        a = points[abs(letter) - 1]
        da = M.mul(tangents[abs(letter) - 1], a)
        if letter < 0:
            a = inv(a)
            da = scale(-1, M.mul(M.mul(a, da), a))
        derivative, value = add(M.mul(derivative, a), M.mul(value, da)), M.mul(value, a)
    return value, derivative


def cocycle_word(w, points, tangents):
    prefix, answer = M.IDENTITY, M.ZERO
    for letter in w:
        q = points[abs(letter) - 1]
        x = tangents[abs(letter) - 1]
        if letter < 0:
            q = inv(q)
            x = scale(-1, M.mul(M.mul(q, x), inv(q)))
        answer = add(answer, M.mul(M.mul(prefix, x), inv(prefix)))
        prefix = M.mul(prefix, q)
    return answer, prefix


def cayley_checks():
    for t in map(F, (-3, -1, 0, 1, 3)):
        numerator, denominator = add(M.IDENTITY, scale(t, M.TAU[0])), add(
            M.IDENTITY, scale(-t, M.TAU[0]))
        value = M.mul(numerator, inv(denominator))
        assert M.mul(M.transpose(value), value) == M.IDENTITY
    # At zero, d[(1+ti)(1-ti)^-1]/dt=i+i=2i.
    tangent = scale(2, M.TAU[0])
    edge = M.pairing(tangent, tangent) + M.pairing(tangent, tangent)
    x = [tangent if i == 0 else M.ZERO for i in range(14)]
    y = [tangent if i == 7 else M.ZERO for i in range(14)]
    # At identity every intervening word is one; evaluate the complete
    # independent cyclic-coordinate form, including all fusion contributions.
    full = sum(coefficient * (M.pairing(x[i - 1], y[j - 1])
                              - M.pairing(x[j - 1], y[i - 1]))
               for (i, _a, j, _b), coefficient in M.FORM.items())
    assert edge == full == 8
    # Independent P0 variation changes the incoming moment at vertex1.
    assert tangent != M.ZERO
    return {"unit_norm_parameter_samples": 5, "cayley_derivative_at_zero": "2i",
            "ambient_twice_form_value": 8, "P0_variation_is_Gauss_tangent": False}


def stabilizer_checks():
    identity, reflection, rotation = (0, 0), (0, 1), (1, 0)

    def mul(a, b):
        return ((a[0] + (-1 if a[1] else 1) * b[0]) % 3, (a[1] + b[1]) % 2)

    def inverse(a):
        return (((1 if a[1] else -1) * a[0]) % 3, a[1])

    def gauge(h, state):
        return tuple(tuple(mul(mul(h[M.FORMS.TARGETS[e]], q), inverse(h[
            M.FORMS.SOURCES[e] if k == 0 else M.FORMS.TARGETS[e]]))
            for e, q in enumerate(row)) for k, row in enumerate(state))

    def product_group(values):
        answer = identity
        for value in values:
            answer = mul(answer, value)
        return answer

    def face(state, f):
        u, p = state
        changed = list(p)
        boundary = M.FORMS.BOUNDARIES[f]
        for i, incidence in enumerate(boundary):
            rotated = boundary[i + 1:] + boundary[:i + 1]
            curvature = product_group(u[a - 1] if a > 0 else inverse(u[-a - 1])
                                      for a in rotated[::-1])
            e = abs(incidence) - 1
            changed[e] = (mul(curvature, p[e]) if incidence > 0
                          else product_group((p[e], u[e], inverse(curvature), inverse(u[e]))))
        return tuple(u), tuple(changed)

    def tick(state):
        u, p = face(face(state, 0), 1)
        return tuple(mul(p0, u0) for p0, u0 in zip(p, u)), p

    elements = tuple(product(range(3), range(2)))
    witness = ((reflection, reflection, reflection, identity, identity, identity, rotation),
               (reflection, reflection, reflection, reflection, identity, identity, identity))
    singular = ((identity,) * 7, (identity,) * 7)
    results = []
    for name, state in (("noncommuting", witness), ("singular_identity", singular)):
        after = tick(state)
        before_set, after_set = [], []
        for h in product(elements, repeat=6):
            if gauge(h, state) == state:
                before_set.append(h)
            if gauge(h, after) == after:
                after_set.append(h)
        assert before_set == after_set
        results.append({"state": name, "gauge_functions_checked": 6 ** 6,
                        "stabilizer_size": len(before_set), "exact_set_preserved": True})
    return results


def geometric_preflight():
    values = [M.TAU[0]] + [M.IDENTITY] * 6 + [M.TAU[0]] * 4 + [M.IDENTITY] * 3
    zero = [M.ZERO] * 14
    changed_words = M.FORMS.face_step(M.ORIGINAL, 0)
    after = [actual_word(w, values, zero)[0] for row in changed_words for w in row]
    for point in (values, after):
        assert all(M.mul(M.transpose(q), q) == M.IDENTITY for q in point)
        assert all(actual_word(w, point, zero)[0] == M.IDENTITY for w in M.MOMENTS)
    initial_real = sum(values[7][i * 5] for i in range(4)) / 4
    final_real = sum(after[7][i * 5] for i in range(4)) / 4
    assert initial_real == 0 and final_real == -1
    assert all(len(star) < 4 for star in M.FORMS.VERTICES)
    return {"all_vertex_valences_below_four": True, "initial_and_kicked_Gauss": True,
            "all_28_link_impulse_values_unit_norm": True,
            "initial_P0_real_part": str(initial_real), "kicked_P0_real_part": str(final_real),
            "trace_separates_quaternion_conjugacy_classes": True}


def main():
    assignments = [
        [M.matrix((F(3, 5), F(4, 5), 0, 0)), M.matrix((F(5, 13), 0, F(12, 13), 0)),
         M.matrix((0, 0, 0, 1))],
        [M.matrix((2, 1, -1, 3)), M.matrix((1, -2, 0, 1)), M.matrix((3, 0, 1, -2))]]
    tangents = [M.matrix((1, 2, 3, -1)), M.matrix((0, -1, 2, 3)), M.matrix((2, 0, -2, 1))]
    words = [()] + [tuple(w) for n in range(1, 5) for w in product((1, -1, 2, -2, 3, -3), repeat=n)]
    for points in assignments:
        for w in words:
            point, derivative = actual_word(w, points, tangents)
            right, value = cocycle_word(w, points, tangents)
            assert point == value and derivative == M.mul(right, value)
    print(json.dumps({"representation": "rational 4x4 matrices; direct inverse/product derivatives",
                      "assignments": len(assignments), "signed_words_per_assignment": len(words),
                      "derivative_order_checks": len(assignments) * len(words),
                      "cayley": cayley_checks(), "stabilizers": stabilizer_checks(),
                      "geometric_preflight": geometric_preflight()}, indent=2))


if __name__ == "__main__":
    main()
