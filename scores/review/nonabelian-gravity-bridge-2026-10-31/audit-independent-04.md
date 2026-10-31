# Review of the complete presentation-orbit dictionary and signed face substitutions

Reviewer: the same author-authorized `ngb_independent_review` worker. No
additional workers were launched. **Contribution disclosure:** this reviewer
supplied the preceding conceptual tree-gauge calculation and literature
identification in novelty-review-independent-03.md. Root independently wrote
the five submitted production Lean modules. The reviewer authored none of
those modules and checked their concrete definitions, targets and proofs
against the canonical literals and independent representations. This is not
a claim of having had no prior involvement in formulating the problem.

**Verdict: approve NGB:surface-orbit-dictionary and NGB:surface-face-twists;
return neither.** These are checked identifications of known algebraic
structure. They establish no new surface-diffeomorphism theorem, symplectic
identification or native gravitational dynamics. All 265 preceding approvals
stand; the four CNI submissions remain pending and outside this review.

The review did not modify production code, manifest, generated status or
review log. Exact file, literal and reachable-surface hashes are recorded
in [verdict-independent-04.json](verdict-independent-04.json).

## The complete carrier and its residual gauges

`SurfaceCoordinates.lean` uses exactly `(a,b,x,z)=(U3,U6,P0,P6)` on the tree
slice. Its packed links and impulses match the canonical formulas. The full
six-component defect of a packed state is `(1,R^-1,1,1,1,1)`, so the admission
condition is equivalent in both directions to R=1.

The normalizing gauge is computed recursively along actual edges0,1,2,4,5,
with root gauge one at vertex0. Its order of inverses matches the production
target-left action. `normalize_tree` holds on every raw state, and gauge
covariance preserves Gauss. Five of the admitted star equations solve the
other five impulses; the remaining equation is exactly R=1. Consequently
`normalize_covers` applies to every admitted raw state. There is no extra
commutation, regularity, freeness or tree-fixed assumption on the original
state being represented.

The residual-gauge theorem derives equality of all six gauge values from the
five tree edges. It does not assume from the start that the gauge is constant.
It holds even between arbitrary packed coordinate values before imposing the
relator. Constant gauges act on all four coordinates by simultaneous
conjugation, and the converse is checked by the actual production action.
Thus no gauge orbits are identified or omitted by an informal choice of
representative.

`SurfaceQuotient.lean` defines the R=1 presentation carrier and its actual
simultaneous-conjugacy setoid. Its maps to and from the complete admitted
gauge carrier respect the full setoids. The normalized representative and
the original are related by the explicit inverse tree gauge. Both quotient
composition orders are proved, and `orbitEquiv` packages precisely those
maps as a bijection. The quotient has no topology, GIT construction or
smooth/symplectic structure in this submission; the literal explicitly
excludes them.

## Both faces, both signs and genuine quotient motion

`SurfaceTwists.lean` checks packing against the actual production kick on
every coordinate tuple, not only after assuming R=1. Forward face0 multiplies
x by a on the left; forward face1 multiplies z by b. Backward instructions
use a^-1 or b^-1 in exactly that position. The relator is preserved as an
actual group element for all four choices.

The generator dictionary is `A1=x^-1,B1=a^-1,A2=z^-1,B2=b^-1`. It gives the
written product of commutators. Taking the inverse of the changed x or z
produces right multiplication `A1 B1` or `A2 B2`; the backward cases use
the corresponding inverse B. There is no accidental interchange of left
and right multiplication or of the inverse sign. The substitutions commute
with common conjugation and therefore descend to the complete presentation
orbit set. Their intertwining with the actual gauge-reduced face instructions
is proved through the two-sided orbit dictionary, for every admitted orbit.

The running S3 example has `(a,b,x,z)=(reflection,rotation,1,1)`. Its relator
is one. Face0 changes x from one to the nonidentity reflection, which cannot
be undone by simultaneous conjugation. The Lean proof uses precisely this
orbit invariant, not merely a raw-state inequality. This is a genuine
nontrivial quotient action.

The Dehn-twist name is a literature interpretation of these standard
substitutions, with the representation-action sign convention fixed in
the novelty assessment. Lean proves the substitutions and orbit-set
intertwining. It does not construct a surface, its fundamental group or
diffeomorphism, prove the analytic form dictionary, or classify the full
drift-containing tick. The canonical scope matches those boundaries.
The source cited by root gives `T(X)=XY,T(Y)=Y` and the corresponding
double map `T(A,B)=(AB,B)` explicitly, confirming the chosen convention.
[Feher and Klimcik, equations6.7 and6.13](https://arxiv.org/pdf/1101.1759v4)
The broader representation action is also described in
[Goldman, §2.6](https://math.umd.edu/~wmg/csymp.pdf).

## Independent reproduction

[replay-independent-04.py](replay-independent-04.py) imports only the earlier
independent word representation, with neither author replay nor production
evaluator imports. Its free-group part checks all six packed defects, exact
normalization under six independent nonconstant vertex gauges, both signs
of both actual face maps, the standard substitutions and inverse pairs.

The finite part represents S3 as affine transformations of Z/3. It enumerates
all 1,296 coordinate tuples, checks full Gauss equivalence and all four signed
face formulas, and finds 486 admitted tuples in 116 simultaneous-conjugacy
classes. It checks all 236,196 pairs of admitted presentations against the
packed gauge orbits. All 46,656 vertex gauge functions on the nontrivial
witness are also tested: normalization returns the expected root conjugate,
preserves complete Gauss and gives the same presentation orbit. The quotient
witness moves as stated. These finite counts are independent replay evidence,
not new registered Lean counting theorems.

Build, separate module kernel replays, status/tree checks and source-integrity
receipts are recorded in
[validation-independent-04.json](validation-independent-04.json). The
approved literals identify known structure faithfully; no physical gravity
gate is advanced by this review.
