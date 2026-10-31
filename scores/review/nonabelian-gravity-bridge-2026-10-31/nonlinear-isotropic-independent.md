# Independent isotropic nonlinear finite-boundary derivation

This is reviewer arithmetic/convention advice, not production Lean or an approval.
The standalone accompanying Python file transcribes the original nonlinear
transported equal-weight curvature and full forward-torsion density from the
pinned snapshots. Unit spacing is fixed; epsilon is field amplitude, not spacing.
The candidate is physically unselected. Original gravity files are unchanged.

Use E=diag(ell,a,a,a) at the middle site, next spatial scale c, temporal link I,
and spatial links exp(b K_0j). The lapse source varies only middle ell. Every
incident density is included. Cell0's temporal-curvature complement contains
only spatial coframes, its spatial faces do not reach time1, and its forward
0j torsion reads the next spatial coframe but not the next lapse. Hence cell0
is lapse-independent; this is an incidence statement, not deletion of a contact.

The middle spatial-face curvature term is ell*a*f(b), up to terms independent
of ell, where exact matrix products with both averaged diagonal paths give

    f(b) = (3/2) sinh(b)^2 [1+2cosh(b)-cosh(b)^2]
         = -3cosh(4b)/16 +3cosh(3b)/4 +3cosh(2b)/4
           -3cosh(b)/4 -9/16.

The replay verifies this as a Laurent identity in x=exp(b), without a commuting
boost approximation. Different spatial boosts do not commute.

Write d=c-a. For the middle forward torsion only t_0j is nonzero:

    t_0j = ell(1-cosh b) e0 + (d+ell sinh b) ej.

With detE=ell*a^3 and both inverse metrics retained, the exact torsion action is

    -3*kappa*a [d^2/ell +2d sinh b +2ell(cosh b-1)].

This requires ell*a nonzero. On a neighborhood of the flat point the positive
coframe/time branch is retained. Differentiating at ell=1 gives the total lapse
force

    a*f(b) +3*kappa*a [d^2+2(1-cosh b)].

Thus with a=1+A*epsilon, c=1+epsilon, b=B*epsilon its epsilon^2 coefficient is

    3[(1-kappa) B^2 +kappa(1-A)^2].

For the independently certified first-order two-cell fixture x=0,
z=e5+e10+e15 and y=-D*B*z,

    A=101/402, B=-100/201, kappa=1/101,
    [epsilon^2 delta] S =40501/53868,
    curvature =10000/13467, torsion =167/17956.

The standalone full matrix-jet replay also checks all40 owned first-order
forces vanish and the other inactive coframe force coefficients4,8,12 vanish.
The literal isotropic reduction is therefore checked against the full source,
not substituted as an arbitrary scalar extension of the quadratic model.

An exploratory formal-jet argument pairs this coefficient with the zero owned
Hessian row for middle F^0_0. Concluding that arbitrary40-coordinate nonlinear
second-order corrections cannot cancel it requires a complete analytic Taylor,
correction-domain and source binding. Those general bindings have not been
proved here, so arbitrary40 nonlinear nonextension remains exploratory/unproved
and is not claimed by this artifact. The checked evidence is the exact finite
jet and source-selected isotropic scalar reduction. The later formal stage may
prove exact positivity in its explicit isotropic domain without making that
stronger generalization. Neither statement is a new discovery of linearization
instability, a continuum Taub charge, a universal nonlinear impossibility, or
a contradiction of the frozen special bulk third-field/all-order constructions.
