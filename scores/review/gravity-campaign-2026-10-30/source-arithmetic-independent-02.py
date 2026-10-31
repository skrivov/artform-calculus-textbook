#!/usr/bin/env python3
"""Independent source-input expansions for the R2 fidelity audit.

Use rational-coefficient polynomials in q,R,a,gamma,s over Q[i], i^2=-1.
This supplements the source comparison and kernel replay; it proves no native
reconstruction, phase-norm feasibility or exceptional-stratum exclusion.
"""
from fractions import Fraction


class Polynomial:
    """A finite coefficient dictionary; the last exponent is the power of i."""

    def __init__(self, value=0):
        if isinstance(value, dict):
            self.terms = {key: coefficient for key, coefficient in value.items() if coefficient}
        else:
            self.terms = {(0,) * 6: Fraction(value)} if value else {}

    def __add__(self, other):
        other = other if isinstance(other, Polynomial) else Polynomial(other)
        result = self.terms.copy()
        for key, coefficient in other.terms.items():
            result[key] = result.get(key, Fraction(0)) + coefficient
        return Polynomial(result)

    __radd__ = __add__

    def __neg__(self):
        return Polynomial({key: -coefficient for key, coefficient in self.terms.items()})

    def __sub__(self, other):
        other = other if isinstance(other, Polynomial) else Polynomial(other)
        return self + -other

    def __rsub__(self, other):
        return Polynomial(other) + -self

    def __mul__(self, other):
        other = other if isinstance(other, Polynomial) else Polynomial(other)
        result = {}
        for left, left_coefficient in self.terms.items():
            for right, right_coefficient in other.terms.items():
                exponents = [x + y for x, y in zip(left, right)]
                sign = (-1) ** (exponents[5] // 2)
                exponents[5] %= 2
                key = tuple(exponents)
                result[key] = result.get(key, Fraction(0)) + sign * left_coefficient * right_coefficient
        return Polynomial(result)

    __rmul__ = __mul__

    def __pow__(self, degree):
        result = Polynomial(1)
        for _ in range(degree):
            result = result * self
        return result

    def conjugate(self):
        return Polynomial({key: (-coefficient if key[5] else coefficient)
                           for key, coefficient in self.terms.items()})


def main():
    variables = []
    for index in range(6):
        exponents = [0] * 6
        exponents[index] = 1
        variables.append(Polynomial({tuple(exponents): Fraction(1)}))
    q, radius, a, gamma, latitude, imaginary = variables
    s, R, g, i = latitude, radius, gamma, imaginary

    # Literal original 5edba section 1 inputs, after x=1-a.
    zeta = 1 - a + i * g
    E = 1 - zeta
    Bc = 1 - i * q
    L = 1 + R - i * q * R
    source_P = (1 + R) * Bc * E
    source_Q = 1 + i * q - 2 * i * q * zeta.conjugate()

    u = 1 + R
    m = 1 + (2 + 3 * q ** 2) * R + (1 + q ** 2) * R ** 2
    v = 1 + (1 + q ** 2) * R
    T = m * a - v + i * q * (1 - u * a) + g * (q * u + i * m)
    Delta = ((1 + q ** 2) * u ** 2 * (a ** 2 + g ** 2)
             - (1 + q ** 2 * (2 * a - 1) ** 2 + 4 * q ** 2 * g ** 2) + 4 * q * g)
    h = a * s + 2 - 3 * a
    W = h ** 2 + s * (3 - s) * ((1 - a) ** 2 + g ** 2) + s * (1 + s) * zeta
    normal = s ** 2 + (5 - 8 * a + 6 * g ** 2) * s + 2 * (2 - 3 * a) ** 2
    w = Fraction(3, 2) + a - 3 * a ** 2 + s * (a - Fraction(1, 2) - g ** 2)
    Bhat = E * (s * Bc + 2 * i * q * h) + (h + 2 * s * zeta) * source_Q
    Ub = 2 * s + 2 - 3 * a
    Vb = (2 - 3 * a) * (4 * a - 1) + s * (4 * a - 2 - 4 * g ** 2)

    differences = {
        "T=conj(P)*L-Q*conj(L)": source_P.conjugate() * L - source_Q * L.conjugate() - T,
        "Delta=norm(P)^2-norm(Q)^2": source_P * source_P.conjugate() - source_Q * source_Q.conjugate() - Delta,
        "W-s*(w+i*(1+s)*gamma)=N/2": W - s * (w + i * (1 + s) * g) - Fraction(1, 2) * normal,
        "Bhat=Ub+iq*Vb+gamma*s*(-3q+i)": Bhat - (Ub + i * q * Vb + g * s * (-3 * q + i)),
    }
    for name, difference in differences.items():
        assert not difference.terms, name
        print(name + ": exact zero polynomial")


if __name__ == "__main__":
    main()
