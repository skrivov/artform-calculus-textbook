# F3: exact nonlinear native isotropic lapse constraint

Registration: NGB:native-isotropic-lapse-constraint. The independent12
fidelity decision is recorded in verdict-independent-12.json. Eleven new
NonlinearIsotropic and statement/proof modules implement this result; the
original nonlinear source is pinned in followup-source-pins.json. No existing
approved source or frozen gravity programme file is edited.

Retain both incident native density cells with fixed endpoint frames. The
old endpoint has E=I and identity links; the middle has E=diag(N,a,a,a), time
linkI and three spatial boosts with common cosh/sinh entries C,S; the future
has E=diag(1,c,c,c) and identity links. Spatial shifts are the zero character.
The exact original curvature constructor keeps all6faces, all5corner weights,
both diagonal transport paths and the ordered -(H-H^-1)/2 reading. The exact
torsion constructor keeps detE, both inverse metrics and all36 unordered-pair
contractions equivalent to the original ordered antisymmetric sum. Native
signature, star and bivector conventions are unchanged. The displayed links
have certified inverse, Minkowski metric preservation and determinant1 when
C^2-S^2=1. E inverses, determinant and the native inverse metric are checked.

The preceding incident density cell is independent of the middle lapse; it
is retained, rather than dropped. The exact complete action has derivative

    dS/dN = a*f(C,S) + 3*kappa*a*((c-a)^2/N^2 - 2*(C-1)),
    f(C,S)=(3/2)*S^2*(1+2*C-C^2).

The derivative is an actual real HasDerivAt theorem at every nonzeroN, for
nonsingular spatial scalea; no unproved analytic Taylor identification is
needed. The original admitted positive coframe/time branch uses N,a,c>0.
The formula at other nonsingular values is an algebraic extension, not
admission of negative-lapse or negative-orientation coframes. The boosts
are orthochronous on the C>=1 domain used here. For kappa1/101, a>0 and1<=C<=3/2, factorization makes this derivative
nonnegative. It vanishes exactly when S=0 AND c=a. Any nonzero small spatial
boost in this isotropic domain violates the native lapse equation, for every
nonzero middle lapse. This is an exact local nonlinear constraint, stronger
than a finite-jet screening calculation.

The complete approved40-row linear momentum equations nevertheless admit the
prepared source-free history x=0, z=e5+e10+e15, with middle F diagonal spatial
entries101/402 and spatial diagonal boost entries-100/201. The actual rational
Cayley boost curve C(t)=(1+t^2)/(1-t^2), S(t)=2t/(1-t^2), t=-50*epsilon/201,
with a=1+101*epsilon/402 and c=1+epsilon has that boost tangent. Lean proves
that its original nonlinear lapse force divided by epsilon^2 tends to
40501/53868. This is an actual analytic limit, not merely a formal polynomial
coefficient. At epsilon1/100 it has legal proper Lorentz links and a nonzero
lapse derivative for every nonzero lapse. The independent full exp-link jet
calculation gives the same leading coefficient, split curvature10000/13467
and torsion167/17956, and checks all40 linear forces.

## Scope and novelty

The exact positivity theorem covers this specified isotropic nonlinear
carrier. It does NOT prove that the prepared linear history has no arbitrary
40-coordinate nonlinear correction: non-isotropic corrections are outside
the theorem. It is not a no-go for the frozen bulk all-order constructions,
which have different domains/boundary data. It does not select this candidate
as the physical gravitational law, identify a continuum Taub charge or
close R7/R8. All8 physical routes remain open.

Linearization-instability and higher-order constraint mechanisms are prior
art (PRIOR-ART-FOLLOWUP.md). The new value is a checked exact finite native
boundary example, including the complete source reduction and analytic force.
It prevents using a valid linearized score history as an automatically
admissible nonlinear or quantum history in this domain.
