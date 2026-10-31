# Novelty assessment before the next research step

31 October 2026. This assessment concerns the eleven approved NGB claims
and the proposed regular-reduction/dipole continuation. Approval certifies
fidelity and proof checking; it does not certify originality. None of the
eleven claims currently establishes a new theorem about native gravity.

## What is established mathematics

| Result or target | Prior result and assessment |
|---|---|
| The double, its edge form, ordered fusion and regular reduction | AMM constructs these structures and proves fusion and reduction. Rebuilding them for our graph is a specialization/formalization task. |
| The group-valued lattice phase space and its surface interpretation | Riello constructs the graph phase space and relates it to flat connections on an auxiliary surface. Neither group-valued fluxes nor this interpretation originate here. |
| Drift as a moment-map twist | Already identified with the AMM twist. Riello also describes the corresponding cylinder twist. It is not a newly selected gravitational Hamiltonian. |
| Word differentiation and invariant quaternion pairing | Analytic product/inverse rules, trace cyclicity and their finite-word consequences are standard. Our interpreter supplies checked source-to-certificate binding. |
| Stabilizer preservation | A direct consequence of equivariance and an inverse; no new general orbit-type theorem. |
| Degree-three cancellation and pointwise norm bounds | Standard noncommutative algebra and norm estimates, instantiated for the actual oriented update. Native matching, normalization and convergence remain unproved. |
| Curved tetrahedral reconstruction | Haggard, Han and Riello already prove a reconstruction theorem with explicit geometric, path, orientation and Gram guards. Closure alone was never the complete theorem. |
| Fixed-area shape dynamics | The same paper derives reduced bending flows. A future score that merely reproduces those flows would be an implementation of known mathematics. |
| Four-link dipole/two-tetrahedron setting | Already used by Rovelli and Vidotto in dipole cosmology; choosing this graph is not a new gravitational construction. |
| Quantization of curved tetrahedral closure and shape spaces | Existing work supplies quantum-group intertwiners, area operators and coherent states. Generic quantization is not an unoccupied research target. |

The primary results are [AMM, Theorems4.5,5.1,6.1 and §9](https://arxiv.org/pdf/dg-ga/9707021v1),
[Riello, §§IV andVI](https://arxiv.org/html/1706.07811v2), and
[Haggard–Han–Riello, Theorem1 and §9](https://arxiv.org/html/1506.03053v1).
The smoothness, regular-stratum and quotient premises still need to be
bound to our exact definitions before applying those theorems. A known
general theorem is not an automatically checked theorem about our code.

For the last two rows see
[Rovelli–Vidotto, §IV](https://arxiv.org/html/0805.4585v1),
[Han–Hsiao–Pan](https://arxiv.org/abs/2311.08587), and
[Hsiao–Pan](https://arxiv.org/abs/2407.03242).
These results do not select the original gravity programme's native R7
measure, constraints or physical state. Their scope nevertheless excludes
a novelty claim based merely on obtaining a quantum curved tetrahedron.

## A sharper identification of the face maps

An explicit spanning-tree calculation gives a stronger novelty test than
the observation that the formulas resemble known twists. Set the tree
links U0,U1,U2,U4,U5 to identity and write

```text
a=U3, b=U6, x=P0, z=P6.
U=(1,1,1,a,1,1,b)
P=(x,a^-1 x a z^-1,a^-1 x a,x,b^-1 z b,b^-1 z b,z).
```

The remaining Gauss relation is

```text
(x^-1 a^-1 x a)(z^-1 b^-1 z b)=1.
```

With `A1=x^-1, B1=a^-1, A2=z^-1, B2=b^-1`, this is the genus-two
surface relator `[A1,B1][A2,B2]=1`, using `[A,B]=A B A^-1 B^-1`.
The two forward face maps become

```text
face0: A1 -> A1 B1; B1,A2,B2 fixed.
face1: A2 -> A2 B2; A1,B1,B2 fixed.
```

These are the standard disjoint-handle Dehn-twist substitutions, with the
choice of inverse twist determined by the representation-action convention.
The exact substitution appears in
[Feher–Klimcik, equations6.7 and6.13](https://arxiv.org/pdf/1101.1759v4);
the surface action is described in
[Goldman, §2.6](https://math.umd.edu/~wmg/csymp.pdf).

At this assessment checkpoint the dictionary has been derived by explicit
group algebra and independently replayed. The next implementation task is
to certify it in Lean, including coverage of the full Gauss carrier and
the residual conjugation quotient. The novelty conclusion does not claim
that a smooth or symplectic quotient equivalence has already been proved.
The drift was not classified by the two face substitutions alone.

## What this campaign actually adds so far

The concrete signed constructor, legal process packaging, adverse controls,
Lean certificate interpreter and exact checked specializations are useful
research artifacts. The claim of originality is limited to these artifacts
in this project. No priority claim is made for a first formalization:
targeted searches do not establish the absence of earlier code.

In particular, a nonzero finite Born probability or a nontrivial
character-variety motion does not by itself become new gravitational
dynamics. The earlier quantum S3 experiment remains a separate model;
it has not been identified as a quantization of this classical score.

## Decision: change what the next step is meant to accomplish

Do not spend the next research allocation presenting general AMM reduction,
curved reconstruction, a dipole graph, or a bending flow as a new physics
result. Keep their formalization obligations separate from research novelty.

First certify the exact genus-two dictionary above. This decides whether
the present face mechanism contributes new dynamics or is a known mapping-
class action expressed as a score. It is a bounded identification task,
not a new native gravity application. Existing approvals stand.

Then require an additional, source-pinned question that known surface
theory does not answer automatically: preservation or failure of actual
geometric reconstruction and shape matching, compatibility with an
original native action/constraint/history class, or a measured improvement
for the same admitted problem. The moving-area/fixed-area distinction,
SU(2)/SO(3) covering, branch and nondegeneracy guards remain essential.
Until such a result exists, credit zero new material native gravity
applications. The regular-reduction Lean binding remains unfinished;
C01-D06 are not activated by this novelty assessment.

## Follow-through in this step

The five new Surface modules implement the exact dictionary and both signed face substitutions. The full warning-free build passes. Fidelity review04 and its final receipt determine approval; see SURFACE-RESULTS.md and STATUS.md. This implementation follows the assessment above and does not change the novelty classification or activate the geometric/native allocation.
