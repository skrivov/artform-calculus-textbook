# Gravity calculus foundation submission

30 October 2026. Six new checked proof submissions; independent fidelity review pending.
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

All names start with Artform.Scores. The literal source statements are quoted in scores/manifest.toml
from the lattice-waves ledger's ALGEBRA-OF-SCORES.md section 7 and findings 102–105.
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

The bounded historical source/review snapshots in source/ and source-pins.json preserve provenance.
Their old UNREVIEWED headings are historical; the distinct review gives the inherited scoped acceptance.
They do not approve these new Lean submissions.

validation-checkpoint-01.json belongs to the first four submissions at the first checkpoint.
The later quantitative-defect submission has its own validation record.

## Reproduction and verdict

Run the repository's required build, reports, manifest/status and certificate checks. The targeted modules
also compile with --wfail. Read the source correspondence and positive examples independently of compilation.
Record a verdict per label. Approve only through the existing ledger_status.py tooling when fidelity passes.
Return a statement explicitly if its translation fails; preserve valid old proofs and the original verdict.

No human approval is a gate. This saved handoff requests independent agent review and does not claim it occurred.
