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
