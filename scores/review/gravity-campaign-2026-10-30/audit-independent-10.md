# Independent two-cell, kernel and Gaussian review, 30 October 2026

Reviewed freeze: 1e774a8c37656c2e1d39431765f6493abdbfad23.
Reviewer: the distinct `gravity_fidelity_review_01` agent, which authored none
of the fifteen submitted modules. Pre-freeze review was read-only, with its
draft outside the repository. No implementation or earlier approval changed;
all 94 previous approvals stand.

**Verdict: approve all five claims; return none.** These are finite/convergent
pilots and a scoped two-cell torsion contribution. They add **zero material
native applications**. The accepted native campaign application count remains
one; the native quantum/refinement and full40 boundary bridges remain open.

See [per-key verdicts](verdict-independent-10.json) and
[independent validation](validation-independent-10.json).
The review compared all five literal manifest quotations with ledger section 7,
findings 132–136, all fifteen new files, their approved dependencies and their
positive/adverse examples. C08 retains the earlier authenticated C07 source
coefficient, pairings, pending-review scope and complete native-force caveats.

## GAC:two-cell-torsion — approve

Both adjacent unit contributions use the pinned kappa=1/101, with middle
source -j*m. The exact completed square retains effective boundary term
kappa*(b-a)²/2, linear source -j*(a+b)/2 and contact -j²/(8*kappa).
The fixed positive coefficient makes this a genuine unique minimum over
rational m for every rational endpoint and source value.

The middle equation is p_left-p_right=j, with the source sign inherited from
-j*m. It is equivalent to m=(a+b)/2+j/(4*kappa). The endpoint momenta are
kappa*(b-a)+j/2 and kappa*(b-a)-j/2, agreeing with minus the incoming and plus
the outgoing derivative of the effective boundary action. The positive
example a=0,b=2,j=2/101 gives middle 3/2 and momenta 3/101,1/101.

At zero source the correct eliminated value is 2/101, while unmodified reuse
of the original unit-cell coefficient over the aggregate increment gives
4/101. This excludes that specific naive reuse. It does not exclude a properly
derived coarse action with its actual duration/coframe/metric/connection
normalization. Only the stated torsion contribution is reduced; other coframe
or connection variations may produce nonzero rows. No full40 solution or
physical cube/octahedron/stella refinement is asserted. The declared component
source j has not been identified with an admissible full native source class.

## GAC:weighted-kernel-algebra — approve

Associativity retains both finite intermediate sets and both declared density
functions. Only those intermediate sets need be finite; outer boundary sets
may be arbitrary. The coefficient domain is a commutative semiring, matching
the finite sum/product proof. No noncommutative coefficient extension is
silently claimed. External source/boundary labels remain pointwise parameters.

Over a field, the kernel delta(x,y)/mu(y) is the actual left and right unit
when every density value is nonzero. Necessity concerns the full algebra of
square kernels, not a chosen test family: an impulse at a zero-density state
would have to be reproduced as one but instead gives zero. The universal
criterion has no nonempty-type assumption. For the empty state type both
the universal nonzero condition and unit existence are vacuous/inhabited as
required, so it includes that edge case correctly.

The two-state positive density (1,2) gives unit diagonal value one-half at
the second state. Density (1,0) has no universal left identity. This does
not forbid a separate identity after an explicitly specified restriction to
nonzero support or physical quotient. No native measure, constrained kernel
space or preparation class is supplied by this finite algebra.

## GAC:gaussian-schur-integral — approve

The action, center and effective action preserve all signs and sources:

    S=a*z²+2*b*q*z+c*q²-2*j*z-2*k*q,
    z_*=(j-b*q)/a,
    E=(c-b²/a)*q²-2*(k-b*j/a)*q-j²/a.

Square completion and determinant identity retain a nonzero a. The determinant
is that of the displayed quadratic-coefficient matrix [[c,b],[b,a]], not an
unannounced rescaling of the full second derivative matrix.

For positive a, actual Lebesgue Integrable is proved alongside the actual
integral at every fixed q. Translation invariance and the proved mathlib real
Gaussian integral yield exp(-E)*sqrt(pi/a), retaining determinant normalization,
transformed linear source and source contact. The local mathlib statements
integrable_exp_neg_mul_sq, its iff version and integral_gaussian were inspected.
The latter is a totalized integral formula even at nonpositive coefficients;
the explicit Integrable conjunct prevents that convention from hiding divergence.

Only the eliminated z direction is positive. No positivity of c-b²/a, further
q integration, two-dimensional absolute convergence, indefinite/oscillatory
prescription or gauge-volume normalization is inferred. The a=0 constant
Gaussian is explicitly proved nonintegrable on the real line. Positive data
(a,b,c,j,k,q)=(2,1,3,4,5,1) give determinant five, center 3/2 and E=-23/2.
This is a convergent real pilot, not a native Lorentzian gravity path integral.

## GAC:finite-gaussian-phase — approve

H has the literal normalized two-point Fourier entries and S is diag(1,i).
The implementation coefficient sqrt(2)/2 equals 1/sqrt(2), with the positive
square-root normalization checked explicitly. H.conjTranspose*H=I and S.conjTranspose*S=I are checked; for these square
two-by-two complex matrices this is unitarity. The actual Weyl conjugations retain their scalar:
HXH*=Z, HZH*=X, SXS*=iXZ and SZS*=Z.

In the projective Pauli labels ordered as exponents of X and Z, those generator
actions are precisely h=[[0,1],[1,0]] and s=[[1,0],[1,1]] over F2. Their actual
matrix product has cube identity. The quantum product instead has cube
gamma*I. Gamma is computed from the actual two-point sum i^(x.val²), with
normSq one and gamma not one. No arbitrary phase was attached to a separately
chosen classical loop.

The declared separating test is the squared combined amplitude against a
fixed coherent reference one: normSq(1+gamma)=2+sqrt(2), differing from four.
It is not a normalized probability assertion or a measurement of an isolated
state's global phase. Independently rephasing the reference would change the
declared experiment. The exact finite binary Clifford/Gauss pilot is not a
continuous bosonic metaplectic representation or native TT amplitude lift.

## GAC:normalized-gaussian-gluing — approve

The real kernel has exactly exp(-(y-x)²/(2h))/sqrt(2*pi*h), with Lebesgue
intermediate measure and strictly positive h0,h1. The proof instantiates the
preceding convergent integral with

    a=(h0+h1)/(2*h0*h1)>0,
    j=x/(2*h0)+y/(2*h1),
    c=x²/(2*h0)+y²/(2*h1).

Its remaining action is (y-x)²/(2*(h0+h1)). Product integrability is explicitly
proved. The full square-root prefactor identity uses positivity before
squaring, so no sign or determinant normalization is lost. Integration gives
K_(h0+h1) with both positive durations retained.

At h=1/(2*pi)>0 and zero endpoints, fixing the midpoint at zero gives product
one, while the integrated coarse kernel is 1/sqrt(2). The strict difference
is proved. This is a precise failed detail-discarding shortcut, not a claim
that every coarse graining is unitary or that a constrained/Lorentzian native
kernel has already been constructed.

## Literature and transfer scope

The reviewer independently checked the primary abstracts of
[Guaita, Hackl and Quella](https://arxiv.org/abs/2409.11628) and
[Hoehn](https://arxiv.org/abs/1401.7731). The former concerns continuous
bosonic/fermionic Gaussian representations and cover/sign data; the latter
studies local evolution moves, constraints and coarse-graining projections
in its specified quantum setting. The findings' scoped comparisons are
accurate. Neither paper is a Lean premise, and neither result is claimed to
be formalized by these finite/positive-real pilots.

## Validation and remaining obligations

The independent full warnings-as-failures build, both reports, both status
checks, identity/tree check, all certificate checks, both empty drift checks
and five separate kernel replays passed. Every proof has its exact tagged
target and only allowed axioms. Integrability, normalization, source terms,
positive/adverse examples, inherited source qualifications and primary
literature comparisons were checked independently of successful compilation.
All 94 previous manifest entries and all fifteen submitted definition/proof
files remain unchanged by this review. Actual native boundary/source and
constraint support, full40 equations and independent connection/frame/link/
history, physical gluing measure, oscillatory convergence/phase prescription,
and continuous bosonic/native lifts remain open. No new material application
is credited merely because a Gaussian identity or a pinned contribution is
now checked.
