#!/usr/bin/env python3
"""Independent coordinate-differential/dihedral review; no author imports.

Formal forms use bimodule monomials A dX_i B, rather than Ad-transformed
right Maurer variables. Wedges use cyclic trace representatives
tr(dX_i a wedge dX_j b), with antisymmetry under the two-factor rotation.
This finite replay is evidence for review, not a Lean geometry theorem.
"""
from collections import Counter
import json


def word(*parts):
    result = []
    for part in parts:
        for letter in part:
            if result and result[-1] == -letter:
                result.pop()
            else:
                result.append(letter)
    return tuple(result)


def inverse(value):
    return tuple(-letter for letter in value[::-1])


def derivative(value):
    """Coordinate derivative in the universal differential bimodule."""
    terms = []
    for position, letter in enumerate(value):
        prefix, suffix = value[:position], value[position + 1:]
        if letter > 0:
            terms.append((1, prefix, letter, suffix))
        else:
            terms.append((-1, word(prefix, (letter,)), -letter,
                          word((letter,), suffix)))
    return terms


def maurer(value, side):
    if side == "left":
        return [(coefficient, word(inverse(value), left), index, right)
                for coefficient, left, index, right in derivative(value)]
    return [(coefficient, left, index, word(right, inverse(value)))
            for coefficient, left, index, right in derivative(value)]


def trace_wedge(first, second):
    terms = Counter()
    for c, left, i, right in first:
        for d, other_left, j, other_right in second:
            a, b = word(right, other_left), word(other_right, left)
            key, rotated = (i, a, j, b), (j, b, i, a)
            if key == rotated:
                continue
            if rotated < key:
                key, c0 = rotated, -c * d
            else:
                c0 = c * d
            terms[key] += c0
    return {key: value for key, value in terms.items() if value}


SOURCES = (0, 1, 4, 3, 1, 2, 5)
TARGETS = (1, 4, 3, 0, 2, 5, 4)
BOUNDARIES = ((1, 2, 3, 4), (5, 6, 7, -2))
VERTICES = ((-1, 4), (-5, -2, 1), (-6, 5), (-4, 3), (-3, 2, 7), (-7, 6))


def source_flux(state, edge):
    links, impulses = state
    return word(inverse(links[edge]), inverse(impulses[edge]), links[edge])


def face_loop(state, face, position):
    boundary = BOUNDARIES[face]
    boundary = boundary[position + 1:] + boundary[:position + 1]
    return word(*(state[0][abs(edge) - 1] if edge > 0
                  else inverse(state[0][-edge - 1]) for edge in boundary[::-1]))


def face_step(state, face):
    links, impulses = state
    changed = list(impulses)
    for position, incidence in enumerate(BOUNDARIES[face]):
        edge = abs(incidence) - 1
        curvature = face_loop(state, face, position)
        changed[edge] = (word(curvature, impulses[edge]) if incidence > 0
                         else word(impulses[edge], links[edge], inverse(curvature),
                                   inverse(links[edge])))
    return links, changed


def link_step(state):
    return [word(p, u) for p, u in zip(state[1], state[0])], state[1]


def twice_form(state, fusion=True):
    result = Counter()
    for u, p in zip(*state):
        b = word(inverse(u), p)
        for first, second in ((maurer(u, "left"), maurer(b, "right")),
                              (maurer(u, "right"), maurer(b, "left"))):
            result.update(trace_wedge(first, second))
    for vertex in VERTICES if fusion else ():
        prefix = ()
        for incidence in vertex:
            edge = abs(incidence) - 1
            flux = state[1][edge] if incidence > 0 else source_flux(state, edge)
            result.update(trace_wedge(maurer(prefix, "left"), maurer(flux, "right")))
            prefix = word(prefix, flux)
    return {key: value for key, value in result.items() if value}


def difference(first, second):
    result = Counter(first)
    result.subtract(second)
    return {key: value for key, value in result.items() if value}


def dihedral_checks():
    """S3 represented as affine maps x -> (-1)^b x+a on Z/3."""
    identity = (0, 0)
    rotation, reflection = (1, 0), (0, 1)

    def times(a, b):
        return ((a[0] + (-1 if a[1] else 1) * b[0]) % 3, (a[1] + b[1]) % 2)

    def inv(a):
        return (((1 if a[1] else -1) * a[0]) % 3, a[1])

    def product(values):
        answer = identity
        for value in values:
            answer = times(answer, value)
        return answer

    def q(state, edge):
        return product((inv(state[0][edge]), inv(state[1][edge]), state[0][edge]))

    def moments(state, vertices=VERTICES):
        return [product(state[1][a - 1] if a > 0 else q(state, -a - 1)
                        for a in vertex) for vertex in vertices]

    def holonomy(state, face, position):
        boundary = BOUNDARIES[face]
        boundary = boundary[position + 1:] + boundary[:position + 1]
        return product(state[0][a - 1] if a > 0 else inv(state[0][-a - 1])
                       for a in boundary[::-1])

    def kick(state, face, backwards=False):
        links, impulses = state
        changed = list(impulses)
        for position, incidence in enumerate(BOUNDARIES[face]):
            edge = abs(incidence) - 1
            curvature = holonomy(state, face, position)
            if backwards:
                curvature = inv(curvature)
            changed[edge] = (times(curvature, impulses[edge]) if incidence > 0
                             else product((impulses[edge], links[edge], inv(curvature),
                                           inv(links[edge]))))
        return list(links), changed

    def drift(state):
        return [times(p, u) for p, u in zip(state[1], state[0])], list(state[1])

    state = ([reflection, reflection, reflection, identity, identity, identity, rotation],
             [reflection, reflection, reflection, reflection, identity, identity, identity])
    after = drift(kick(kick(state, 0), 1))
    assert moments(state) == moments(after) == [identity] * 6
    a, b = holonomy(state, 1, 3), q(state, 1)
    assert times(a, b) != times(b, a)
    assert times(holonomy(state, 0, 0), holonomy(state, 0, 0)) == identity
    assert times(holonomy(after, 0, 0), holonomy(after, 0, 0)) != identity
    partial = (state[0], list(state[1]))
    partial[1][0] = times(holonomy(state, 0, 0), state[1][0])
    assert moments(partial) != [identity] * 6
    wrong = kick(state, 1)
    wrong[1][1] = times(holonomy(state, 1, 2), state[1][1])
    assert moments(wrong) != [identity] * 6
    other = list(VERTICES)
    other[1] = (-2, -5, 1)
    assert moments(state, other)[1] == identity
    assert moments(kick(state, 1), other)[1] != identity
    assert kick(drift(kick(state, 0)), 1) != after
    for face in range(2):
        assert kick(kick(state, face), face, True) == state
    for first_back in (False, True):
        for second_back in (False, True):
            assert kick(kick(state, 0, first_back), 1, second_back) == kick(
                kick(state, 1, second_back), 0, first_back)
    return {"representation": "dihedral affine maps on Z/3", "adverse_controls": 4,
            "noncommutation": True, "holonomy_order_separates_gauge_orbits": True,
            "four_signed_face_commutations": True}


def main():
    original = ([(i,) for i in range(1, 8)], [(i,) for i in range(8, 15)])
    base = twice_form(original)
    assert base
    rows = []
    for name, changed in (("face0", face_step(original, 0)),
                          ("face1", face_step(original, 1)),
                          ("drift", link_step(original))):
        defect = difference(twice_form(changed), base)
        missing = difference(twice_form(changed, False), twice_form(original, False))
        assert not defect
        rows.append({"map": name, "cyclic_coordinate_defect_terms": len(defect),
                     "omitted_fusion_defect_terms": len(missing)})
    print(json.dumps({"scope": "independent finite coordinate-differential trace algebra",
                      "baseline_cyclic_terms": len(base), "formal_results": rows,
                      "finite_group_controls": dihedral_checks()}, indent=2))


if __name__ == "__main__":
    main()
