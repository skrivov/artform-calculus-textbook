# Independent gravity foundation review, 30 October 2026

Reviewed freeze: `bc5571ce53e92185fbbae3ff3c4a0b54b63abead`.
Reviewer: the distinct `gravity_fidelity_review_01` agent, which authored none
of the submitted definitions, statements or proofs. The implementation was
read without mutation before the freeze; the completed freeze was then checked
independently. No implementation or original proof was changed by this review.

**Verdict: approve all seven submitted GAC entries; return none.** These are
faithful translations of the seven literal statements in ledger section 7.
The original 63 approvals stand and are not repeated by this review.

The per-key verdicts, reviewed statement hashes and input hashes are in
[verdict-independent-01.json](verdict-independent-01.json). Reproduction
results are in [validation-independent-01.json](validation-independent-01.json).
The review read the handoff, all GravityBridge definitions, statements, proofs
and positive examples, ledger section 7, findings 102–106, and the four bounded
historical source/review snapshots. All four snapshots match both their pinned
SHA-256 and the live original bytes. Each manifest quotation occurs literally
in ledger section 7. Historical OPEN/UNREVIEWED headings do not supply approval
for these new Lean entries.

## Per-key fidelity findings

### GAC:relations — approve

`Evolution X Y` is the unrestricted predicate `X → Y → Prop`.
`compose r s` uses an existential intermediate state, with r first and s
second. The statement quantifies over the four arbitrary state types and
asserts associativity, then separately quantifies over functional graphs.
`matrixGraph` uses the complete column action of an arbitrary two-by-two
matrix over every commutative ring, rather than a single preparation/readout.
Its injectivity therefore distinguishes complete matrix laws.

The final conjunct uses the existing `Score` and `realize`, whose concatenation
law is `realize (u ++ v) = realize v * realize u`. The relational extension
retains this time order. The kick-then-move example instantiates the existing
score language, and the relation allowing outputs 0 and 1 from input 0 is
genuinely multivalued. No word-injectivity or regularity claim is introduced.

### GAC:realization — approve

`Realization` retains arbitrary maps E and R with the actual left-inverse
equation `R (E y) = y`. This also implies that E is injective. The visible
law is exactly `R ∘ T ∘ E`. Forward invariance refers to the actual range of
E, and the two directions of the equivalence identify the range witness using
recovery and supply a witness from intertwining, respectively. The all-time
conclusion includes both the full embedded orbit and its visible readout,
for every natural time including zero. There is no linearity, finite dimension
or global observability premise.

The autonomous example `E y = (y,0)`, `T(y,z) = (y+1,2z)` meets invariance.
The hidden-drift example checks all-time reading equality while disproving
invariance; it is explicitly a counterexample to an unasserted converse.

### GAC:native-distinct-block — approve

The torsion rows, signed pairing `M = -I`, and curvature Hessian agree with
M162 and its distinct review. In particular the pairing has not been made
positive. Expanding the definitions gives B with diagonal `-4/101` and
off-diagonal entries `(-99/101,-99/101,99/101)` in the declared order.
Its determinant is exactly `2058146/1030301`, hence nonzero.

The proof uses the genuine matrix inverse, verifying for arbitrary rational z
that `B⁻¹ r = (0,101z/103,-101z/103)` with `r = (0,-z,z)`.
The full signed Schur expression has output `(-101z/103,-101z/103,0)`.
The last zero is computed, not omitted. The z=1 example supplies a nonzero
input and vanishing spatial-face output. Independent rational arithmetic
reproduced the determinant and all three output components.

### GAC:temporal-witness — approve

All nine rational polarization entries equal the source's
`a₀ a₀ᵀ - b₀ b₀ᵀ`, with `a₀=(2,-1,0)/√5` and
`b₀=(3,6,-5)/√70`. Symmetry, zero trace, all three transverse equations,
`ρ²=14`, contraction `-36/35`, and the positive coefficient `36/505`
are each present in the literal statement and checked independently.
The positive example has all momentum components and the response nonzero.

This approves the rational coefficient of the lower temporal symbol only.
The Fourier factor i, complete forty-equation extraction, repeated-block
reduction, admitted packet, native-step noninvariance and physical boundary
comparison are not asserted by the Lean theorem.

### GAC:defect-stability — approve

The definition is exactly `D(E)=T E-E R T E` for bounded linear maps between
real normed vector spaces. The statement has no completeness, finite-dimensional,
recovery, invariance or native-domain premise. Writing `Δ=F-E`, the checked
identity is exactly `D(F)-D(E)=T Δ-Δ R T F-E R T Δ`.
The triangle and composition-norm estimates retain every factor and yield
`‖T‖ ‖F-E‖ (1+‖R‖(‖E‖+‖F‖))`.

The gap corollary retains the same constants and its strict inequality.
The positive example changes the graph from `(y,0)` to `(y,y)`, keeps the same
exact readout, and checks a nonzero old defect and zero new defect for the
coordinate swap. Finding 104 distinguishes the generator estimate from the
order-h step defect and from a physical energy or boundary norm. The theorem
makes none of those unproved transfers.

### GAC:connection-preparation — approve

The original first-lift snapshot supplies `c=-2κ B⁻¹ r`, while the unscaled
`B⁻¹ r` is only the resolvent used in the Schur calculation. The submitted
equation is correctly `B c+2κ r=0`, with the unique correction
`c*(z)=(0,-2z/103,2z/103)`. It is the centered contorsion correction, not the
entire native connection. The determinant proves uniqueness, and the zero
preparation solves the equation exactly when z=0.

The three unordered spatial TT inputs are exactly `23/10,-3/4,-3/2` and are
all nonzero. The exact quadratic variation includes the original linear term
and `ε² δ·Bδ/2`. The input-dependent term `-2κz²` is retained in the complete
displayed block: at the preparation the partial action is `4z²/10403`, while
the retained block density is `-2z²/103`. The positive examples exhibit both
a unique nonzero correction despite a zero spatial Schur output and the
different densities at z=1. These facts were also reproduced by independent
rational arithmetic. No full effective gravity action or physical cut is
identified by this finite sub-block.

### GAC:finite-processing — approve

The kernel, weighted composition and closed amplitude are exactly the declared
finite sums over a commutative semiring. All required finite-type instances
are explicit. Bijections act by inverse substitution on functions and both
kernel arguments. Composition transports its intermediate measure; closure
transports both measures, preparation, test and kernel.

The external label has an arbitrary type J. Every bijection and datum in the
closure statement may depend on j, and equality is pointwise for every j.
It makes no derivative, continuum measure, positivity or physical quotient
claim. The two-state example uses the nonconstant measure `(1,2)` and an
actual swap, checks the complete transformation law, and computes the exact
1-versus-2 failure when the measure is left behind.

## Validation and material scope

The independent full build with warnings treated as failures, both generated
reports, both status checks, identity/tree check, both certificate checks,
and all seven module kernel replays passed. Each tagged proof proves exactly
its tagged statement and uses only the repository's allowed axioms. Approved
surface drift is empty. The original 63 manifest entries are unchanged.

The approved statements provide typed evolution, a general realization test,
an operator-norm estimate, exact native sub-block certificates and finite
processing. Their finite mathematical content is valid without pretending
that the complete native reconstruction, admitted-domain analysis, physical
source/boundary/frame/link/history equivalence or a quantum gravity model
has been formalized. Those material application obligations remain separate.
