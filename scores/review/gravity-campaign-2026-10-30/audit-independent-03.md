# Independent native R2 exception and exclusion review, 30 October 2026

Reviewed freeze: `207183698798dc782dc1b0a30aaab727544e327b`.
Reviewer: the distinct `gravity_fidelity_review_01` agent, which authored none
of the two submitted statements, their definitions, proofs or certificate.
The pre-freeze audit was read-only. No implementation or original proof was
changed by this review; all 71 earlier approvals stand.

**Verdict: approve both entries; return none.** GAC:r2-exception-cases
faithfully handles the native factor and complete affine alternatives.
GAC:r2-zero-row-exclusion proves a new, scoped native R2 problem reduction:
the explicitly open all-zero coefficient stratum is absent on the stated
large-normal chart. It does not decide the remaining force problem.

The reviewed hashes and per-key verdicts are in
[verdict-independent-03.json](verdict-independent-03.json), and reproduction
results are in [validation-independent-03.json](validation-independent-03.json).
This review compared the literal manifest quotations with ledger section 7
and findings 108–109; read the new definitions, statements, proofs, producer,
certificate and input structure; and used the original native correspondence
and scoped M178/M184/F01 baselines already audited for F02. Both quotations
are literal ledger text. The original four native row polynomials have not
been replaced or narrowed.

## GAC:r2-exception-cases — approve

At s=0, the original Pe,Qe,Po,Qo products have constant coefficient
`c0_i=-6R b² S_i`. The four S entries are exactly the source expressions
built from p,j0,u,m,t and `4a-1`. Substitution into the original monic constant
remainder `n_i=c0_i-2b²c2_i+2nu*b²c3_i` gives the displayed common factor

    n_i=b²*(-6R*S_i-2c2_i+2nu*c3_i).

The Lean proof uses the actual coefficient's evaluation at zero and the
approved row evaluation identity. It does not assume an exported coefficient.
Cancellation of b² is a separate equivalence with an explicit `b!=0` premise.

The b=0 case is retained: at a=2/3, `N=s*(s-(1/3-6G))`, so the two normal
possibilities are exactly `s=0` or `s=1/3-6G`. Consequently `N=0`, `G>=0`
and `s>1/3` imply b is nonzero. This excludes no smaller-latitude chart and
does not silently install the stronger inherited native latitude estimate.

For arbitrary real four-vectors l,n, the statement keeps the all-zero l case,
the chosen nonzero-pivot case with every corresponding minor, and the exact
Pi/Lambda filter. The latter requires both `Lambda!=0` and `Lambda*s=Pi`;
it asserts no native reconstruction or existence of such chart data.
Both directions of each equivalence are proved without division by l or n.
The zero and pivot cases cover all possible l. The native normal point and
the separate zero-vector and `(1,2,0,0)` pivot examples supply positive data
for these alternatives.

## GAC:r2-zero-row-exclusion — approve

The certificate has eight generators: the four primitive constant quotients,
then the four affine coefficients. The actual native scale signs are

    (1,-1,1,1,-1,1,-1,-1).

All eight equalities are proved from the existing `rowPolys`, `ell` and
`constantQuotient`. The universal cubic identities recover c2 from values at
0,1,-1, c3 from 0,1,-1,2, and c1 from the signed difference and c3.
The approved degree bound and row evaluation lemma apply to the actual native
polynomials before ring normalization proves each bridge. No Python table,
input checksum or coefficient claim is a Lean hypothesis.

The generated data contain exactly the eight generator and eight multiplier
definitions and the positive integer D. The producer's deterministic byte
comparison checks the entire generated Lean file, including all large
integers. Its standard-library replay checks the input hash, eight scale/factor
links to the exported table and the exact rational identity.
The certificate hash is
`92369c1881fe5b7cbf1df8cc5028acc3295870bb2433d35a819ab7a75dbb7d4e`;
the repository and ledger certificate bytes are identical.

I also replayed the certificate independently of its producer and row table.
The [separate integer convolution](integer-replay-independent-03.py) accepts
only integer coefficients, nonnegative three-variable exponents and unique
monomials. It multiplies 14,912 term pairs and collects 294 monomials. Every
nonconstant coefficient cancels, and the only nonzero result is precisely the
positive 302-digit D. This is exact integer arithmetic, not a modular test or
sample evaluation. The multiplier term counts are
`34,34,50,50,19,19,31,24`, as stated in finding 109.

Lean separately checks the complete identity `sum_i w_i*g_i=D` by ring
normalization. If every ell_i and n_i were zero with b nonzero, F03's guarded
factor equivalence and the eight bridges would make every generator zero.
The identity would then give `0=D`, which the kernel-checked numeral
calculation contradicts. This proves the first conjunct for every real R,a,G
off b=0, without any phase-norm premise.

The second conjunct derives b nonzero from exactly `N=0`, `G>=0`, `s>1/3`.
The third also requires the physical q square, gamma square, nonzero q and
gamma, and both original J equations. The approved signed-trace/monic
reduction then says `ell_i*s+n_i=0`; if all ell_i were zero, all n_i would
also be zero, contradicting the new exclusion. Thus a nonzero pivot exists
for every such simultaneous-sign candidate. It asserts no candidate existence.

The positive example inhabits the normal domain at `R=a=1`, `G=1/36`,
`s=3/2` and instantiates the nonzero-coefficient conclusion. The second
example retains an actual b=0 normal point at `G=1/36`, `s=1/6`, outside
the large-normal corollary. Neither example is presented as a surviving
phase-norm or full-force solution.

## Novelty and native scope

M178 section 6 explicitly retained `ell=n=0`, and its section 7 and distinct
review did not establish emptiness. M184's frozen R2 record retains that
exceptional locus, and F01 names its decision as an open target. The present
unit identity and its bridges therefore close an actual previously retained
native R2 branch. They depend on the specific physical-q native coefficient
polynomials. This is a new native problem reduction, beyond a generic affine
foundation or a fresh compilation of the old M178 reduction. F03 supplies its
guarded algebraic support; F04 supplies the new exclusion.

For application to the remaining regular double-norm chart, its inherited
necessary bound `s>88173/88205` is stronger than `s>1/3`, and its G is
positive. All original radius, normal reconstruction, determinant, phase-norm,
rho/Z and other chart guards remain required for a native candidate. The new
proof does not derive that stronger baseline from complete reconstruction.
Its algebraic statement is valid on a larger domain, so it also holds after
the full original chart restrictions are retained.

Excluding all eight coefficients being zero does not exclude four affine
rows meeting at one latitude. Nonzero-pivot feasibility, single-sign force
feasibility, physical handedness selection, global finiteness, full forty-row
history reconstruction and the campaign's R7/R8 target remain open. No full
gravity or quantum-parent completion follows from this approved branch result.

## Validation

The independent full warnings-as-failures build, both generated reports,
both status checks, tree/identity check, both existing certificate checks,
new gravity certificate check, independent integer replay and separate
R2Exceptions/R2ZeroRow kernel replays passed. Both tagged proofs have their
exact tagged target and only allowed axioms. Approved-surface drift is empty,
and all 71 earlier manifest entries remain unchanged.
