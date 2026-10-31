# Gravity calculus foundation submission

30 October 2026. Seven new checked proof submissions independently approved at freeze
`bc5571ce53e92185fbbae3ff3c4a0b54b63abead`; none returned. See the distinct
[audit](audit-independent-01.md), [per-key verdicts](verdict-independent-01.json) and
[independent validation](validation-independent-01.json).
The original sixty-three scores entries retain their independent approvals.

## Statements to review

| Label | Statement and proof namespace |
|---|---|
| GAC:relations | GravityBridge.Statement.typedRelations / GravityBridge.typedRelations |
| GAC:realization | GravityBridge.Statement.invariantRealization / GravityBridge.invariantRealization |
| GAC:native-distinct-block | GravityBridge.Native.Statement.distinctBlock / GravityBridge.Native.distinctBlock |
| GAC:temporal-witness | GravityBridge.Native.Statement.temporalWitness / GravityBridge.Native.temporalWitness |
| GAC:defect-stability | GravityBridge.Statement.defectStability / GravityBridge.defectStability |
| GAC:connection-preparation | GravityBridge.Native.Statement.connectionPreparationLaw / GravityBridge.Native.connectionPreparationLaw |
| GAC:finite-processing | GravityBridge.Statement.finiteProcessing / GravityBridge.finiteProcessing |

All names start with Artform.Scores. The literal source statements are quoted in scores/manifest.toml
from the lattice-waves ledger's ALGEBRA-OF-SCORES.md section 7 and findings 102–106.
Definitions, statements, proofs and positive examples are under scores/ArtformScores/GravityBridge/.

## Required fidelity checks

1. The relation layer must distinguish complete two-channel matrix laws and retain the old time-order
   realizer. It does not assert that every word is distinct or every relation canonical.
2. The realization theorem quantifies over arbitrary types, with a genuine embedding/readout recovery
   condition. Check both invariance directions and the exact orbit conclusion.
3. The all-time visible-reading counterexample is deliberately not an invariance example. Check that
   the positive autonomous example, the nonunique relation example and the score example are present.
4. Compare the signed torsion, curvature and face-pairing matrices with the M162 source and its distinct
   review. Check the actual inverse, determinant, arbitrary rational z and zero spatial-face output.
5. Check every TT entry, transversality, trace, momentum contraction and positive 36/505 coefficient.
   This theorem proves a rational symbol certificate. It does not formalize the complete forty-equation
   reduction, packet construction, native-step noninvariance or physical boundary equivalence.
6. Check the exact difference identity and operator-norm estimate in Stability.lean. The statement has no
   completeness, finite-dimensionality, recovery or native-domain assumption. Its corollary keeps every
   constant and its positive example changes the embedded graph while preserving the common readout.
   A generator bound must not silently be transferred to a step bound or to a physical energy norm.
7. Check the first-lift normalization in the additional original-source snapshot:
   c=-2*kappa*B^-1*r, with stationary equation B*c+2*kappa*r=0.
   Check its exact quadratic variation, the nonzero TT inputs and the unique prepared correction.
   The c-independent term -2*kappa*z^2 must be retained for the input-dependent effective density.
   Neither this block nor its first-lift correction is the entire native connection or gravity action.
8. Check finite kernel composition and closed amplitudes under bijections of their declared data.
   All measures, preparations, tests and kernel arguments transform. Source dependence is pointwise
   in an arbitrary external label; no derivative or continuum measure is asserted.
   Check the nonconstant two-state measure example and the exact 1-versus-2 failure when it is left behind.

The bounded historical source/review snapshots in source/ and source-pins.json preserve provenance.
Their old UNREVIEWED headings are historical; the distinct review gives the inherited scoped acceptance.
They do not approve these new Lean submissions; the distinct audit above supplies that review.

validation-checkpoint-01.json belongs to the first four submissions at the first checkpoint.
The later quantitative-defect, connection-preparation and finite-processing submissions have their own
historical validation records. Their pending-review fields describe the submission checkpoints.

## Reproduction and verdict

Run the repository's required build, reports, manifest/status and certificate checks. The targeted modules
also compile with --wfail. Read the source correspondence and positive examples independently of compilation.
Record a verdict per label. Approve only through the existing ledger_status.py tooling when fidelity passes.
Return a statement explicitly if its translation fails; preserve valid old proofs and the original verdict.

No human approval is a gate. This saved handoff requests independent agent review and does not claim it occurred.

## F02 addition: original R2 trace arithmetic

GAC:r2-trace-reduction is a separate new submission. Its exact original source snapshots are pinned in
[source-pins-R2.json](source-pins-R2.json). Check Native/R2Defs.lean against corrected original force
5edba7e6 section4 and M178 09793524: original W, Bhat, J and the unmultiplied affine trace; all four cubic
products; the latitude-independent phase determinant; both gamma signs; the genuine polynomial degree
bounds; and the exact monic identity including zero/lower-degree rows. All original denominator guards
s,3-s,E,Delta must appear in the clearing equivalence. No coefficient is divided out in the remainder.
The positive normal-chart point witnesses only the reduction hypotheses. It is not claimed to satisfy
phase norms or radial reconstruction. Finding107 and validation-F02.json give scope and build evidence.
The original70 approvals stand. This additional claim was independently approved at freeze
`a2c754a9f65f03c1bbc5fc82ab1b0874e8c05c92`; none returned. See the distinct
[R2 audit](audit-independent-02.md), [verdict](verdict-independent-02.json),
[validation](validation-independent-02.json) and
[original-input arithmetic witness](source-arithmetic-independent-02.py).

## F03–F04 additions: exceptional cases and a new native exclusion

GAC:r2-exception-cases retains every zero/pivot alternative and the actual shared b² factor. Its b=0
normal chart is classified before cancellation; N=0,G>=0,s>1/3 prove b!=0. The Pi/Lambda filter uses
only its declared nonzero Lambda and exact latitude identity. Finding108 states these scopes.

GAC:r2-zero-row-exclusion adds an exact integer unit identity and all eight native input bridges. The
replay data are scores/certificates/gravity-r2-zero-row.json and gravity-r2-row-input.json. Run
python3 scripts/gravity_r2_certificates.py --check; it checks the identity, source-input hash, all scale/factor
identities and deterministic generation of R2CertificateData.lean. R2ZeroRow.lean proves every native
coefficient equality using cubic interpolation of the actual polynomials, and checks the complete identity
with ring. No exported coefficient is a Lean hypothesis. The 302-digit positive constant cannot be zero.

Check finding109 and M178's explicit retained all-zero stratum against the new conclusion. The theorem
excludes this stratum off b=0, and hence on the original normal G>=0,s>1/3 chart. For simultaneous J zeros
it guarantees a nonzero affine pivot. The original remaining double-norm chart has the stronger reviewed
latitude bound; all its other original guards still apply. Nonzero-pivot feasibility, single-sign feasibility,
physical selection, full40 history and R7/R8 are open. This is a scoped new native R2 reduction, not a
claim of a complete gravity solution. Both additions were independently approved at freeze
`207183698798dc782dc1b0a30aaab727544e327b`; none returned. The original71 approvals stand.
See the distinct [audit](audit-independent-03.md), [per-key verdicts](verdict-independent-03.json),
[validation](validation-independent-03.json) and [integer replay](integer-replay-independent-03.py).

## B03 and D01 additions: exact memory and stencil support

GAC:block-memory and GAC:stencil-support are new foundational submissions, described in ledger
findings110 and111. The canonical statements are literal quotes in scores/manifest.toml.
Check arbitrary semiring/module quantifiers, initial auxiliary state and all finite history terms,
prepared graph invariance and the stronger full-domain autonomy criterion. The old Whitehead
score supplies the fixed-initialization non-Markov example; a nontrivial invariant graph has B!=0.

For stencil support check factor order with possibly noncommutative coefficients, faithfulness
on every field via impulses, support inclusion rather than equality, the sharp shift-radius
example, cancellation, and the original kick/move entry1+q*p. Dense averaging fixes constants
only; it leaves a local identity realization available on that restricted space. Neither foundation
is asserted to be a new native application. The full native dynamic split, stencil and domain
remain obligations. Validation-B03-D01.json records all required checks, drift checks and both
separate kernel replays; its generated reports are retained as byte counts and SHA-256 hashes.
Both foundations were independently approved at freeze
`4fc465dc188cf764eb8be326e231c84b6539f59b`; none returned. Original73 approvals stand.
See the distinct [audit](audit-independent-04.md), [per-key verdicts](verdict-independent-04.json)
and [validation](validation-independent-04.json).

## F05–F06 additions: broader norm chart and original regular phase

GAC:r2-norm-chart proves the literal odd norm identity, and excludes b=0 using only N=0, G>=0,
s>0, R>0 and the necessary odd norm constraint at q²=103/2. The b=0 contradiction compares
(3-s)*d>64/3 with (412/9)*s<=412/27. It then reuses the approved unit certificate. A simultaneous
sign full norm/trace candidate has a nonzero affine pivot without a large-latitude assumption.
The at-most-one latitude statement fixes R,a,G and requires b!=0; no existence or global count follows.
The exact positive necessary-constraint point is not asserted to satisfy full phase norms or force.

GAC:r2-phase-transfer checks the original P/Q signs, norm determinant and conjugate numerator,
the real-linear inverse, K²=s / KH=h norm equivalence, and phase+norm+unmultiplied affine-trace
equivalence with Vreg+F=0+J=0. Delta may have either sign but is nonzero. Trace clearing retains
s,D,E,Delta, and normal reconstruction is not asserted. Source pins are the existing corrected
original force5edba7e6 and four-row/review pins in source-pins-R2.json. Findings112–113 specify
precise application scope. These strengthen the same R2 reduction; no second direction or new
smaller-latitude physical candidate is claimed.

R2PhaseDefs.lean and R2PhaseStatements.lean are new; prior approved entries are unchanged.
Validation-F05-F06.json records required checks, empty drift, the R2 certificate check and both
separate kernel replays using compact hashes/sizes for the generated reports. Independent review
is requested; the original75 approvals stand.
