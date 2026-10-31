# Review of the dipole obstruction and spherical orthant fixture

Reviewer: the same author-authorized `ngb_independent_review` worker. No
additional workers were launched. **Contribution disclosure:** this reviewer
previously discussed the proposed obstruction, its quantifiers and controls,
and the geometric path/frame conventions with root. Root authored all six
submitted production modules. The reviewer authored none of them and checked
their actual definitions, targets, proofs and canonical literals independently.
This is not a claim of no prior involvement in problem formulation.

**Verdict: approve NGB:dipole-oriented-score and
NGB:spherical-face-collapse; return neither.** The first is an exact
unrestricted-link admission obstruction. The second attaches genuine one-cell
geometric endpoint data to that obstruction. Neither establishes a matched
two-cell Levi-Civita configuration, a general Lean sphere-manifold theorem,
or a native gravity application. All 267 preceding approvals stand; the four
CNI submissions remain pending and outside this review.

The review did not modify production code, manifest, generated status or
review log. Exact source, literal and reachable-surface hashes appear in
[verdict-independent-05.json](verdict-independent-05.json). The frozen build
and reports were independently hash-checked against all 895 prepared source
entries. All 25 previously reviewed NGB modules retain their approved bytes.

## Full dipole carrier, order and quantified obstruction

`Dipole.lean` constructs the actual two-vertex, four-edge Canvas. All links
point from vertex0 to vertex1. The source star has outgoing factors in order
0,1,2,3; the target star has incoming factors in order3,2,1,0. Completeness,
absence of duplicates and valence four are proved, rather than inferred from
a diagram. For arbitrary group-valued U/P data, its raw defects are exactly
`Q0 Q1 Q2 Q3` and `P3 P2 P1 P0`, with `Qe=Ue^-1 Pe^-1 Ue`.

The first signed digon has based holonomy `k=U0 U1^-1`. Its forward kick is
`P0'=k P0`, `P1'=P1 k^-1`, with the other impulses and all links fixed. The
second formula is the reversed traversal update; replacing it by a second
left update would not be faithful. Both signs preserve the complete raw
defect, are two-sided inverses and commute with both independent vertex
gauges under the declared target-left link action. The submission does not
claim a legal-process realization or evolution of every digon.

`DipoleErasure.lean` applies to every tuple with `P3 P2 P1 P0=1`. The lift
`U=(P0^-1,1,1,1)` satisfies both Gauss equations, and its forward kick gives
`P'=(1,P1 P0,P2,P3)`. Conjugating the erased first impulse leaves it one.
Thus gauge quotienting cannot restore this face.

The important quantifier in `no_saturated_domain` is the proposed admission
of **every** Gauss lift above a target tuple in A. If A contains a closed
tuple and every member has `P0!=1`, that saturation is incompatible with
forward invariance. The proof does not forbid a domain that restricts U
using geometric transport or gluing conditions. The positive control is
also actual: `U=(1,1,1,1)` is a Gauss lift of every closed tuple and both kick
signs fix it. These controls rule out interpreting the result as a no-go for
all link restrictions or all local flows.

## Exact orthant data and the geometric interpretation

`SphericalOrthant.lean` uses rational coordinate vertices in four dimensions.
It proves vertex Gram I and the unit positive interior vector
`(1/2,1/2,1/2,1/2)`. The edge matrix from e_s to e_t sends e_s to e_t and
e_t to -e_s, fixing the orthogonal complement. Its inverse and endpoint
identities are checked for every distinct pair. The four submitted loop
products match the pinned special-edge convention; their restrictions at
vertex4 are the displayed quarter-turns about i,j,k,-j. Each fixes the base
vertex, is orthogonal with determinant one, and their reverse product is I.

The normal Gram uses the transported pair24 prescribed in the source, not
the ordinary dot-product matrix of four vectors in one tangent space. The
corrected Gram is I with determinant one and all four stated convexity
triple products are +1. The ordinary four-normal Gram has determinant zero,
an adverse control reproduced independently. These conventions agree with
[Haggard, Han and Riello, §2, equations12,17,24,32,33](https://arxiv.org/html/1506.03053v1).

The accompanying analytic interpretation is sound and explicitly separate
from the Lean finite data. For the quarter-circle
`gamma(t)=cos(t)e_s+sin(t)e_t`, a source tangent vector is `a e_t+w`, with w
orthogonal to both endpoints. The field
`V(t)=a(-sin(t)e_s+cos(t)e_t)+w` has derivative `-a gamma(t)`, normal to the
unit sphere. Its intrinsic covariant derivative therefore vanishes, and its
endpoint agrees with the declared matrix. The coordinate-face triangles
have three right angles and area pi/2. This supplies genuine nondegenerate
one-cell holonomies, rather than an arbitrary closed quaternion tuple.

The base tangent frame `(-e1,-e2,-e3)` is positively oriented with the
outward-normal convention for S3. In that frame the first three outward
normals have components i,j,k. The transported fourth normal has components
-j. Checking this frame is essential: using an unstated ambient frame would
obscure the axis signs. The finite matrix calculation and this analytic
argument together justify the stated one-cell interpretation; the Lean
proof alone does not construct a sphere, connection or parallel transport.

## Quaternion lift and collapse

`SphericalFixture.lean` uses the positive real branch `r=sqrt(1/2)` and
`P=(r(1+i),r(1+j),r(1+k),r(1-j))`. Its explicit inverses, unit norms,
reverse-order closure and squared real parts below one are proved. Action
on every imaginary basis vector binds these actual quaternions to the
declared rational rotation matrices. The normal components use the same
positive branch and frame, not a separately chosen quaternion dictionary.

For the erasing lift all four links and impulses have unit quaternion norm,
both Gauss equations hold and every initial face is nonidentity. After the
complete forward kick, both Gauss equations still hold but P0 is one and
stays one under every gauge. In the stated convex spherical triangle
prescription, identity rotation is incompatible with the required
noncentral-face condition. The formal target claim concerns these checked
finite matrices, quaternion data and group updates. No hidden continuum
connection hypothesis is inserted into its carrier.

The selected cross-cell U values are admitted by the unrestricted group
carrier. This review does **not** identify them with transports in a matched
two-cell Levi-Civita geometry. Source Gauss closure by itself does not prove
matching. A future proof must impose and verify actual transport/gluing
conditions before crediting a geometric dynamics result. The flat twisted
geometry comparison also distinguishes normal matching from additional
shape matching; it supplies no automatic curved dictionary here.
[Freidel and Speziale, §1.3 and §5.1](https://arxiv.org/html/1001.2748v1).

## Independent reproduction and validation

[replay-independent-05.py](replay-independent-05.py) uses a reduced free-word
representation for unrestricted group identities and an independently
implemented exact coefficient field `Q(r), r^2=1/2` for quaternions. It imports
neither the author replay nor a production evaluator. Both kick signs,
inverses, full defects and independent gauges were checked in free words,
together with the generic erasing lift and identity-link positive control.

The exact geometric replay checks all four ambient loop paths, all twelve
distinct endpoint/inverse pairs, twelve quaternion basis actions, unit norms,
closure, the corrected and ordinary Gram determinants, four convexity
triples and both Gauss defects before and after collapse. An affine S3
representation exhausts all 216 closed target tuples and checks both kinds
of lift. A routine Fraction-to-JSON output conversion was corrected in this
independent replay; all arithmetic checks then ran again successfully. This
was not a production correction.

All six modules separately passed `leanchecker`. The fresh report records
only `propext`, `Classical.choice` and `Quot.sound` for the two proofs. Book
and score status checks, tree identity and both approved-surface drift checks
passed. Receipts are in
[validation-independent-05.json](validation-independent-05.json).

This is useful diagnostic progress on an admission dependency and a checked
specialization of known geometry. It does not advance decision12 or activate
C/D, does not claim priority for the orthant or dipole mathematics, and adds
zero established native quantum-gravity applications.
