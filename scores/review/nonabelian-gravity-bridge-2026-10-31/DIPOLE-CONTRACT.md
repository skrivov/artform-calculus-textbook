# Frozen diagnostic: can a full digon kick collapse a geometric face?

Baseline: commit27677cb. The previous surface identification is established
mathematics. This diagnostic asks a different, specific compatibility
question: does the proposed four-edge dipole score preserve even the
necessary noncentral-face condition when link transports are independent?
The target is an obstruction with a genuine one-cell spherical fixture,
not a gravity evolution law or a matched two-cell reconstruction.

## Declared carrier and map

Two vertices, four links from source0 to target1, and three non-wrapping
adjacent digons `(i+, (i+1)-)` with i=0,1,2. Declare the actual Canvas,
complete stars `Q0 Q1 Q2 Q3` and `P3 P2 P1 P0`, and
`Qe=Ue^-1 Pe^-1 Ue`. For the first digon use k=U0 U1^-1,
P0'=k P0, P1'=P1 k^-1, with U and the other P fixed. Its inverse uses
k^-1. Prove complete raw-defect preservation, inverse and independent
two-vertex gauge covariance. No cyclic digon or symplectic claim is needed.

For every closed target tuple P choose U0=P0^-1, U1=U2=U3=1.
Prove both initial stars close and the complete kick gives P0'=1 and
P1'=P1 P0. Thus any proposed invariant domain containing this lift and
requiring P0 nonidentity fails. Do not assert this lift satisfies arbitrary
additional geometric transport conditions.

## Genuine spherical target fixture

Use the positive orthant in the unit three-sphere, with vertices the four
coordinate unit vectors. Its interior contains (1/2,1/2,1/2,1/2), its vertex
Gram matrix is I, and its four faces are geodesic right spherical triangles.
Use Haggard–Han–Riello1506.03053 §2 equation12 simple paths and special
edge(24). Quarter-circle transport from vertex s to t rotates the (s,t)
plane by pi/2 and fixes its orthogonal complement. Compute the four loop
matrices, and bind them to conjugation by explicit unit quaternions

```text
P=(r(1+i), r(1+j), r(1+k), r(1-j)), r=sqrt(1/2).
```

Check closure, unit norm, the correctly transported normal Gram matrix I
(including the exceptional pair24), convexity triple-product signs, and
the noncentrality of all four P. The ordinary untransported four-normal
Gram matrix is not the geometric Gram matrix. Prove collapse for this
fixture and persistence of the collapsed identity under every gauge.

The standard interpretation of the quarter-circle formula as Levi-Civita
transport and the right spherical triangle area pi/2 is an explicit
analytic/geometric input, explained and independently reviewed in the
result note. Lean checks the stated finite matrices, quaternion action,
Gram, signs and score identities; it does not construct a sphere manifold
or formalize the general curved reconstruction theorem.

## Decision and scope

This is a diagnostic before the expensive supporting regular-reduction
binding. That changes the investigation order only: decision12 remains
unpassed, C01-D06 remain unactivated, and no additional research-round or
native-application credit is claimed. A negative answer selects geometric
admission/transport restrictions as the next dependency; it does not imply
that every restricted small-step flow or matched Regge domain fails.
In particular, two intrinsic isometric cells, a compatible connection and
an actual Levi-Civita gluing are different requirements. None follows
from this one-cell fixture plus Gauss closure alone.
