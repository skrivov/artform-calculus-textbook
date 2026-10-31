# Independent review06: matched sectors and two score updates

Reviewer: the single user-authorized Sol6.1 worker `ngb_sol61_transport_review`.
No additional workers were launched. **Contribution disclosure:** this reviewer
supplied conceptual path/frame convention advice and checked the proposed
positive comparison before implementation. Root authored all seven production
modules; this reviewer authored none of them. The present review independently
examined their actual definitions, statements, proofs and canonical literals.
It does not claim no prior involvement in problem formulation.

**Verdict: approve `NGB:matched-orthant-transport` and
`NGB:matched-score-separation`; return neither.** Preserve all269 previous
approvals and the four pending CNI submissions. These two approvals produce
275 total ledger entries,271 approved and4 pending. No new native-gravity
application, research round, smooth reduction or C/D activation is credited.

The exact source, canonical-literal, reachable-surface, replay and report hashes
are in `verdict-independent-06.json` and `validation-independent-06.json`.
The reviewer changed only review artifacts, not production code, manifest,
generated status or review log. All31 previous NGB modules retain baseline
9985bfafb9fbecf300df1186843c05a0b919ef41 bytes. The root's fresh prepared
source fingerprint and both reports were independently checked; all seven new
module kernels passed separate `leanchecker` invocations. The initial premature
attempt at the three downstream kernels encountered missing build artifacts;
all three were rerun successfully after the root build completed.

## Paired geometry and path conventions

`SphericalGluing` supplies the odd involution (3,2,1,4), coordinate-identical
paired vertices, full three-vertex face Grams and explicit seam reflections.
These are complete finite metric data for the geodesic orthant faces. The
reflection fixes every vector in the physical face hyperplane and reverses
its coordinate normal. Between target frame(-e1,-e2,-e3) and source frame
(+e1,+e2,+e3), the effective tangent coordinate matrix is its negative.
For face4 the actual based matrix includes the edge24 stem in both copies.
It is essential that the coordinate matrix and physical tangent differential
are distinguished; the production text does so.

The source HHR loop products are the target inverse loops after swapping
labels1 and3. This permutation fixes the special edge24. Independently checking
the four edge words confirms the correspondence, including the face4 stem;
no moment-map boundary path was silently changed. `SphericalTransport` binds
the lifts(i,j,k,j) to every basis-vector matrix action, and binds the outgoing
fluxes to P inverse. The source tuple(Q2,Q1,Q0,Q3), corrected Gram I and four
positive convexity triples agree with the actual source loops. Both full
ordered Gauss stars and all U/P norms are certified. The earlier erasing lift
is explicitly excluded by the stricter seam action.

The continuous interpretation is appropriately qualified. Basepoint e4 and
the edge24 stem lie on singular strata of the doubled orthant; a smooth global
LC connection there is not supplied. The declared one-sided cell-sector
transports and seam differentials define a precise discrete prescription.
For a face-interior crossing, its ambient normal is parallel along that
face, so reflection commutes with tangential transport. This explains the
based comparison and its sector limit. The finite Lean results do not claim
a general sphere-manifold or gluing theorem.

## Actual kick and invariant spherical obstruction

`TransportControls.kicked` is the actual previously defined full forward
digon kick, not a separately entered endpoint. `kicked_P` binds it to
P'=(r(-j-k),r(i+k),r(1+k),r(1-j)). Each flux has unit norm and is noncentral.
Its declared postNormal axes are pure imaginary unit vectors, bound to these
same fluxes with strictly positive sine coefficients.

The corrected Gram explicitly uses the exceptional pair24 term with Ad(P0')
in zero-based indexing. Its binding theorem computes the matrix from those
actual axes and that actual flux. Independent exact Q(r), r²=1/2 arithmetic
reproduces the exceptional entry-r, determinant-1/4 and second convexity
triple0. `SphericalGram` proves general diagonal-sign congruence and invariance
under simultaneous invertible-quaternion conjugation. Consequently the final
literal quantifies all16 axis sign assignments and all gauges; the independent
replay additionally checks all16 signs and representative gauge samples.

The relevant external necessity is the spherical Gram determinant criterion
in [Haggard–Han–Riello v1, §4](https://arxiv.org/html/1506.03053v1), using their
fixed simple paths and exceptional pair24 convention in §2 equation17.
A negative determinant excludes the declared nondegenerate spherical target
sector. The submission does not infer a valid hyperbolic reconstruction from
that determinant and does not exclude other updates or small local flows.

## Positive independent-connection comparison

`DipoleConnection` proves, for every group, both signed one-link drifts,
individual P/Q preservation, raw-defect preservation, exact reverse and
independent endpoint gauge covariance. Independent free-group reduction
reproduces these identities for every link and sign without commutativity.

`IntrinsicMatched` fixes the actual target and source face tuples and requires
unit links. `IndependentAdmitted` is its saturation under two independent
unit-norm endpoint gauges. The explicit UnitGauge guard is necessary because
the ambient Hˣ carrier also contains nonunit quaternions. The proofs establish
nonemptiness, full Gauss, all U/P norms, and invariance under every signed
one-link drift and every such gauge. This is an actual invariant domain,
rather than a stationary example or a guarded partial update.

For the actual edge0 drift, the gauge-invariant mixed real trace changes
0 to-1/2; independent quaternion computation reproduces both values. Therefore
no endpoint gauge identifies its initial and final states. Its edge0 rotation
changes from pi to3pi/2, so the fixed seam prescription fails. Intrinsic matched
cells persist, while connection-dependent strict transport does not. The
production statements and prose keep these scopes separate.

The underlying twist is established machinery: [AMM v1, Theorem4.5](https://arxiv.org/pdf/dg-ga/9707021v1).
[Freidel–Speziale v1, §§1.3,5.1](https://arxiv.org/html/1001.2748v1) supports
the flat intrinsic/connection distinction, not a new curved native dictionary.
[Anzà–Speziale v2](https://arxiv.org/abs/1409.0836v2) concerns its particular
flat dynamics and does not establish preservation for this score. These
sources were independently reopened and the stated attribution limits fit.
No Ashtekar–Barbero field, physical Hamiltonian or native R7/R8 evolution is
identified here.

## Reproduction and formal scope

`replay-independent-06.py` imports only the prior independent reviewer05
stdlib arithmetic/free-word helpers; it imports no production evaluator.
The helper's bytes were independently checked unchanged against the published
baseline, and both hashes are recorded. The replay checks full paired face
Grams, all inverse HHR paths, seam quaternion actions, initial/kicked Gauss,
actual kick axes/Gram determinant, second convexity, all sign choices,
representative gauges, general free-word drifts and the nonstationary trace.

Both canonical propositions are conjunctions of the properties actually
proved, with concrete non-vacuity examples. Fresh report entries prove exactly
their stated declarations, using only propext, Classical.choice and Quot.sound.
The separately described continuous geometric interpretation and external
spherical reconstruction necessity remain transparent dependencies. Smooth
regular reduction, native field/history binding and physical dynamics remain
open, as the frozen contract requires.

Receipt metadata correction: `canonical_file_sha256` initially held the
`claims.json` file digest through a reviewer variable selection error. It now
identifies `ALGEBRA-OF-SCORES.md`; the former value is retained separately as
`claims_file_sha256`. Both canonical literals occur byte-for-byte in that file.
Production, canonical text, per-key review hashes and approvals are unchanged.
