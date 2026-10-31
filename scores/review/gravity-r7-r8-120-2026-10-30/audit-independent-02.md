# Independent inverse and complete quadratic-force review, 30 October 2026

Reviewed freeze: 7c1988f1d54e022950100a8ca0d5286097d86ebe.
Reviewer: the distinct `gravity_fidelity_review_01` agent, which authored none
of the fifteen submitted modules. All 124 previous approvals stand. No
implementation or earlier proof was changed.

**Verdict: approve all five literal claims; return none.** The first three
provide exact signed-block reconstruction and reusable source-complete
elimination. The last two faithfully assemble the declared original periodic
flat quadratic formula and its complete coordinate force. They add zero
material native R7/R8 applications and establish no efficiency saving.

See [per-key verdicts](verdict-independent-02.json),
[independent validation](validation-independent-02.json),
[exact rational replay](arithmetic-independent-02.py) and
[actual retrospective baseline](retrospective-baseline-02.json).
The review compared all fifteen files, every example and all five literal
section 8 quotations with findings 162–166, the original frozen formulas and
the previously approved coordinate/shift/plaquette/complement/torsion layer.

## GAC2:signed-block-polynomial-inverse — approve

C,T and M are the actual previously approved signed distinct-block matrices.
Direct kernel arithmetic verifies C^2=C+2I and T-transpose*M*T=-(C+2I).
Structural matrix algebra then gives B_t=(1-2t)C-4tI and both product
identities B_t*N_t=N_t*B_t=d_t*I, where

    N_t=(6t-1)I+(1-2t)C,
    d_t=2(1-4t)(1+2t).

Both scalar nonzero guards precede division. The two-sided inverse is
identified with the actual matrix inverse, not just assigned that name.
At t=1/101 the matrix is definitionally the old connectionBlock, and its
inverse is exactly (9999C-9595I)/19982. The native positive instance meets
both guards. The independent replay also checks the two singular parameters
t=1/4 and t=-1/2 without using an inverse there.

This family has a stronger output than the old selected-source r/w solve.
Its reconstruction is valid, but stronger output is not evidence of reduced
work on the same problem. No measured or historical runtime claim is made.

## GAC2:curvature-only-force-residual — approve

The actual r=(0,-z,z) has C-eigenvalue -1 and B_t-eigenvalue -(1+2t).
Thus c_C=2t*r solves the curvature-only equation, while its full signed
residual is exactly -4t^2*r. The source-restricted full solve
c_B=2t*r/(1+2t) correctly needs only the second nonzero factor. In particular
the theorem does not invent a global inverse at t=1/4, where that source
solve still works. At the native coefficient it is the old
connectionPreparation, and curvature-only stationarity is equivalent to z=0.

The complete density retains its input-dependent term -2t*z^2. The old
completeConnectionAction is identified explicitly. The stationary effective
density is -2t*z^2/(1+2t), and the curvature-only substitution difference is
-16t^4*z^2/(1+2t). The exact replay at native z=1 gives c_B=(0,-2/103,2/103),
effective density -2/103 and difference -16/106121003. The nonzero example
fails the actual original connection equation. This is an indefinite
stationary-action difference, not an energy penalty or a minimum theorem.

## GAC2:guarded-schur-source-reconstruction — approve

The theorem quantifies over arbitrary modules over a ring. Both inverse
identities D*E=Id and E*D=Id are retained, with no commutativity or
finite-dimensional determinant shortcut. The original two equations are
equivalent in both directions to the Schur equation with A-B*E*C, shifted
source u-B*E*v and exact auxiliary reconstruction E*(v-C*f).

The example has both nonzero couplings and nonzero eliminated source:
A=D=2,B=C=1,E=1/2,u=4,v=5,f=1,a=2. It verifies both inverses and the
transformed equation/reconstruction. The replay confirms that deleting the
eliminated source changes the answer. Neither an inverse for every native
connection frequency nor a bounded-contour/domain theorem is assumed proved.

## GAC2:complete-flat-quadratic-variation — approve

The domain is an actual finite additive commutative lattice group, with all
four increments explicit and all sixteen coframe/twenty-four link components
available. The unit-spacing alpha=lambda=0,beta=sigma=1 specialization uses
the original invariant Gram and internal star; kappa remains explicit.

The new bivector bracket is checked against the original four-by-four matrix
commutator, with star equivariance and invariant pairing. Wedge coordinates
retain the original 31 orientation. For spacetime faces
(01,02,03,12,13,23), the complementary pairs are
(23,13,12,03,02,01) with signs (+,-,+,+,-,+). These are exactly the original
epsilon orientations, also independently reconstructed in the replay.

L has all four corner coframe wedges. U is minus the commutator of the
original 3/8,1/8,3/8,1/8 transport mean with the flat complement. K is the
original D_l*A_k-D_k*A_l. The raw bilinear contact is minus one half of all
six ordered letter brackets. On its diagonal it is explicitly identified
with the original inverse curvature reading, rather than an installed
logarithm or an omitted H1^2 contact. The torsion is the complete earlier
map with all six unordered faces and signed eta factors.

The declared bilinear form has diagonal exactly the complete original
quadratic formula. Its raw contact need not be symmetric; both orderings
enter B(q,p)+B(p,q), which is exactly the derivative of that diagonal.
All additivity/scalar identities and the exact epsilon expansion are proved.
The one-site constant temporal boost example has complete density 1/101.
It is a nonzero periodic normalization instance, not the independent-shift
stress test or a physical boundary solution.

This certifies the full declared flat coefficient formula. It does not
prove an analytic remainder for the nonlinear exponential action, a
nonconstant-background operator theorem or the mixed full Ward kernel.

## GAC2:full-coordinate-variational-force — approve

The field-coordinate linear equivalence is actual packing through
X times the forty slots. Each force coordinate evaluates the whole variation
on the inverse image of a unit coordinate test. The arbitrary-test pairing
identity and both directions of force-zero iff every variation vanishes
retain every independent coframe/link coordinate and every periodic owner.
No selected observable or restricted ansatz replaces those tests.

The strengthened literal statement is present and proved:

    fullForce(q)=fullJacobian.mulVec(fieldCoordinates(q)).

The matrix is symmetric under coordinate transpose. This is the actual
matrix representation of the linear force, not just symmetry of a named
basis table. The forty-times-cardinality row count is coordinate counting,
not a physical polarization or radical count.

The direct variation contains both g(L*deltaf+U*deltaA,star*K*A) and
g(L*f+U*A,star*K*deltaA), both ordered-contact polarizations paired with C,
and the full 2*kappa torsion term. Invariant g/eta conversions are already
inside these unit-test coordinate covectors. No positive Riesz map or
normal-output half/quarter rescaling is introduced.

For real coefficients the proof establishes an actual HasDerivAt at zero
of epsilon mapped to S2(q+epsilon*p). It differentiates the exact scalar
polynomial, giving B(q,p)+B(p,q), with no half force. The nonzero constant
boost self-test has variation 2/101. This is the derivative of the declared
flat quadratic action, not an asserted analytic identification of the
nonlinear full force on a larger domain. Over complex coefficients the
matrix symmetry is bilinear transpose symmetry, not Hermitian positivity.

## Baseline, custody and remaining transfer

The four files in retrospective-baseline-02.json match both their pinned
hashes/bytes and the stated old commit. They preserve the actual correct
selected r/w solution and full source-dependent density. No slow cofactor
algorithm or inflated baseline is invented. Future efficiency comparisons
must still match output/guards and separate generation, replay, rational
operations, bit sizes and runtime under the frozen ruler.

All fourteen original/snapshot pairs remain authenticated. Original invariant
Gram conventions, five-summand averaging and description001 travel with the
source. Periodic finite sums neither sum a nondecaying background action nor
supply finite-boundary contact laws. Sup background control and l2
perturbation-operator domains remain distinct. M185's unfinished publication,
M186's necessary connection-value reduction and the prospective unreviewed
longitudinal evaluation retain their earlier scope.

The independent full warnings-as-failures build, both reports, status/tree
checks, all certificates, both empty drifts and five separate kernel replays
passed. Every tagged proof has its exact target and only allowed axioms.
All 124 previous entries and all fifteen submitted modules remain unchanged.
The complete periodic quadratic operator is now reconstructed, but mixed
Ward cancellation, constrained inversion, actual target/domain estimates,
physical sources/currents/quotients and independent frame/link/history
matching remain open. No new material native application or retrospective
saving is assigned.
