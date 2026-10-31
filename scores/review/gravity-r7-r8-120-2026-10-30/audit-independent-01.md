# Independent original-coordinate and coefficient review, 30 October 2026

Reviewed freeze: 27c17c0fe8d7b7db914efa2b09760ebf7291cdce.
Reviewer: the distinct `gravity_fidelity_review_01` agent, which authored none
of the fifteen submitted Lean modules. All 119 baseline approvals stand;
no implementation was changed.

**Verdict: approve all five literal claims; return none.** These are faithful
original-coordinate and formal-coefficient reconstructions, with supporting
periodic identities. They add zero material native applications and establish
no retrospective efficiency saving. The inherited first-campaign scoped R2
application is unchanged; no new R7/R8 target is closed.

See [per-key verdicts](verdict-independent-01.json),
[independent validation](validation-independent-01.json) and
[exact arithmetic replay](arithmetic-independent-01.py).
The review inspected all fifteen modules, every example, all five literal
section 8 quotations and findings 157–161, and authenticated every original
and snapshot in the fourteen-file source inventory.

## GAC2:native-forty-coordinate-gram — approve

The coordinate type has exactly sixteen coframe and twenty-four link slots.
Both directions of packing/unpacking are proved. Frame indices are internal
row and coframe-column indices; Torsion uses f(a,j) consistently with that
choice. The six link coordinates remain independent on each of four links.

The basis is the original (01,02,03,23,31,12), including the orientation of
31. Boost entries are symmetric, while spatial matrix entries at 23,31,12
are the corresponding positive coordinates. The original sources give both
the Gram matrix diag(-I3,I3) and X^IJ=X^I_L*eta^LJ, with
g(B,F)=B^IJ*F_IJ/2. Thus -trace(lie(a)*lie(b))/2 is the actual source
normalization, not just an arbitrary invariant scale. The trace identity,
coordinate recovery and nondegeneracy are proved for arbitrary inputs.

The complete eta-skew kernel is characterized in both directions. This is
an algebraic Lorentz-matrix classification, not a physical radical or mode
count. The internal star is (-J,K), squares to minus identity and is
g-self-adjoint with the exact cross pairing. It is neither complex
conjugation nor a positive Hilbert adjoint. Both Gram conversions are
involutions; the coframe Gram multiplies the internal row by eta.

All quantified fields have characteristic zero and include the real and
complex fields. Over the complex field these are bilinear algebraic
identities, not Hermitian positivity assertions. The unit boost and unit
rotation have pairings minus one and plus one. The separate rational replay
checks all 36 basis trace-pairing entries and the star identities.

## GAC2:native-shift-adjoint — approve

The algebraic shift identities hold on any additive commutative group. The
bilinear sum identities separately require a finite group and use actual
bijective reindexing. The incoming transpose is S_-a, and the difference
transpose is S_-a minus identity. Neither is installed by a conjugation
convention. The order of the bilinear factors is retained.

The (Z/3)^4 delta example separates each pair of distinct positive unit
shifts at the selected negative unit point. The replay checks all sixteen
same/different unit evaluations and four nonconstant periodic bilinear sums
on all 81 sites. No transverse direction is silently identified with time.

This proves the periodic alternative permitted by the source. It does not
assert that every group/increment choice has four distinct generators,
sum an infinite background action, erase finite-region endpoint terms or
prove an l2 Hilbert adjoint. Compact-test and analytic extensions still need
their actual domains and the original Gram conversions.

## GAC2:native-ordered-plaquette-jet — approve

The truncated multiplication is the actual degree-two noncommutative
matrix product. The four exponential jets have coefficients I,X,X^2/2.
Their ordered product has the sum of squares divided by two and all six
ordered products, with no exchange of factor order. A unit-constant jet's
inverse is checked on both sides, retaining H1^2-H2.

Substitution into the original reading -(H-H^-1)/2 yields minus one half
of the six ordered commutators. The original signed-shift letters are
(-A_l,-S_l*A_k,S_k*A_l,A_k); their linear reading is D_l*A_k-D_k*A_l.
The two distinct boosts have a nonzero commutator and the opposite entry
when reversed. The independent rational replay also checks a four-letter
noncommuting product, both inverses and both reading coefficients.

These are formal jet identities over characteristic-zero fields. They do
not equate the reading with a logarithm, prove an analytic exponential
remainder, or reconstruct a nonlinear solution. In the later action the
quadratic contact must still be paired with the nonzero flat complement.

## GAC2:native-five-summand-complement — approve

All five weights are retained: 1/4,1/4,1/4,1/8,1/8. Equal diagonal field
values do not merge the two connection paths. Their distinct sums are
A_k+S_k*A_l and A_l+S_l*A_k, yielding exactly

    V=(3*A_k+S_l*A_k+3*A_l+S_k*A_l)/8.

The generic first coefficients sum to the four-corner mean minus [V,C].
For four arbitrary gauge values the connection differences give
V=M(omega)-omega0, and the coframe commutator mean cancels the transport
part, leaving [omega0,C]. The unit boost gives the nonzero 3/8 coefficient.
The independent replay keeps different corner and path matrices when
checking the five-summand identity.

The result is the literal first-order matrix algebra. The wedge/coframe
correspondence and complete mixed curvature cancellation against arbitrary
second tests remain to be assembled. No full40 Ward kernel, nonlinear gauge
theorem, inverse or physical quotient is proved by this partial identity.

## GAC2:native-flat-torsion-gauge — approve

The map is exactly D_i*f_j-D_j*f_i-A_i*t_j+A_j*t_i, with all sixteen
coframe and twenty-four link entries retained. Its antisymmetry is proved.
The arbitrary six-coordinate profile gives f=lie(omega) and A_i=D_i*omega;
linearity of lie cancels the torsion pointwise, and commuting lattice
increments cancel D_j*A_i-D_i*A_j. No traveling restriction is introduced.

The density enumerates the six unordered spacetime faces
(01,02,03,12,13,23). This list is distinct from the ordered internal bivector
basis; neither orientation is substituted for the other. The outer
eta_i*eta_j and internal eta pairing give the original signed density.
The exact variation has coefficient 2*kappa, without an additional half.
The unit01/internal2 example has density -1/101 and self-test derivative
-2/101, independently checked as well. It is a nonzero normalization test,
not a stationary-force or positive-energy witness.

This is the full flat torsion contribution. A zero gauge self-value or
zero torsion alone is not a full Hessian-kernel proof. Curvature cross
terms, the ordered plaquette contact and arbitrary second variations still
have to be combined, with determinant/inverse-metric contacts accounted for
at their actual orders.

## Source custody, plan publication and disposition

All fourteen snapshots match the pinned originals, hashes and byte counts.
The older one-sided cell action supplies matrix/bivector normalization;
the later transported five-summand law governs the current complement.
The exact-coordinate qualification keeps invariant vectors distinct from
coordinate covectors. Description001 controls nondecaying backgrounds in
sup norm; l2 statements apply to perturbation operators, not to an l2
background difference or a summable total background action.

M185 retains reviewed but unfinished-publication status. M186 accepts the
copied-frame necessary connection-value reduction within its mandatory
scope, not a value of divJ5. The newer four-group nonzero certificate and
its receiver qualification remain explicitly unreviewed prospective input.
Authenticating those snapshots grants them no new mathematical acceptance.

PLAN.md and PLAN.json exactly match the ledger plan previously reviewed:
120 unique questions, eighty native/stress and forty retrospective, with
publication/review at zero research count. PLAN.md was excluded by the
local ignore rule and absent from the submission commit. This publication
force-adds that exact mirror so the existing README link works. No approved
statement is edited. The frozen efficiency ruler retains the same problem,
source, guards and reconstruction, and separates rational operations from
bit cost and generation from replay. No saving is assigned to this batch.

The independent full warnings-as-failures build, both reports, status/tree
checks, all certificate checks, both empty drifts and five separate kernel
replays passed. Every tagged proof has its exact target and only allowed
axioms. All 119 baseline entries and all fifteen submitted modules remain
unchanged. Complete quadratic variation, full curvature contacts and Ward
operator, actual target evaluation, admissibility, native source/current,
physical quotient and frame/link/history transfer remain later obligations.
