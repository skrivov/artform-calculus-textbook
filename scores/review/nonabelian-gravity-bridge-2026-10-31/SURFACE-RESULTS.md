# Exact identification after the novelty assessment

The novelty assessment was completed before implementing this step. It
found that the broad mathematical targets are established. The implementation
therefore checks an exact identification needed to interpret our existing
model; it is not presented as new gravitational dynamics. Read NOVELTY.md
and novelty-review-independent-03.md for prior results and their scope.

## The complete orbit-set dictionary

SurfaceCoordinates.lean constructs the explicit gauge on the spanning tree
with edges0,1,2,4,5. Every Gauss-valid state is gauge-equivalent to

```text
U=(1,1,1,a,1,1,b)
P=(x,a^-1 x a z^-1,a^-1 x a,x,b^-1 z b,b^-1 z b,z).
```

The six defects of this packed state are `(1,R^-1,1,1,1,1)`, where

```text
R=(x^-1 a^-1 x a)(z^-1 b^-1 z b).
```

Thus full Gauss is exactly R=1. No extra commutation sector or regularity
assumption was introduced. Conversely every tuple satisfying R=1 packs to
an admitted state. The five tree links force every residual vertex gauge
to have the same value at all six vertices. Therefore two packed states
are gauge-equivalent exactly when their four coordinates are simultaneously
conjugate.

SurfaceQuotient.lean supplies actual maps in both directions and proves
both inverse orders. This is a set-level equivalence between the complete
Gauss gauge-orbit set and the four-generator presentation-orbit set. For
an arbitrary group, we call it a presentation orbit set; a GIT/algebraic
character variety is not being defined by a change of terminology.

## The face maps are the standard substitutions

Write `A1=x^-1,B1=a^-1,A2=z^-1,B2=b^-1`. The relation is then exactly

```text
[A1,B1][A2,B2]=1, with [A,B]=A B A^-1 B^-1.
```

SurfaceTwists.lean proves, for every group and both forward/backward signs,
that packing the coordinate update equals the actual production kick.

| Operation | Coordinate action | Standard-generator action |
|---|---|---|
| Forward face0 | x -> a x | A1 -> A1 B1 |
| Backward face0 | x -> a^-1 x | A1 -> A1 B1^-1 |
| Forward face1 | z -> b z | A2 -> A2 B2 |
| Backward face1 | z -> b^-1 z | A2 -> A2 B2^-1 |

All other coordinates/generators in each row are fixed. Each substitution
preserves R exactly. The full orbit-set bijection intertwines these maps
with the actual signed face kicks. The forward S3 example with
`(a,b,x,z)=(reflection,rotation,1,1)` changes its orbit: x becomes a
nonidentity reflection, whereas conjugation fixes the identity.

The standard forward map is the familiar handle Dehn-twist substitution.
Its formula is explicit in
[Feher–Klimcik, equations6.7 and6.13](https://arxiv.org/pdf/1101.1759v4);
the surface representation action is described by
[Goldman, §2.6](https://math.umd.edu/~wmg/csymp.pdf).
An inverse convention changes the twist sign. Lean checks the exact
algebra and full-orbit intertwining here; the topological identification
uses those known sources. We have not constructed a surface diffeomorphism
in Lean or proved that orbitEquiv is a symplectic isomorphism. The entire
drift-containing tick is not classified by the face formulas alone.

## Consequence for the research campaign

The next useful result cannot be merely that this face mechanism is a
nontrivial reversible, canonical-looking motion on a Gauss quotient.
The exact standard substitution is already known. The drift likewise has
the earlier known AMM twist interpretation. The new value of this step is
that we can now identify that overlap precisely and stop treating it as
an unresolved source of new gravitational dynamics.

Regular reduction still needs a faithful formal binding if used by a later
application. Its existence as a general mathematical construction is
established; it should be budgeted as supporting formalization rather than
a physics discovery. The dipole and generic curved-tetrahedron quantization
are also established settings. No material native gravity result is
credited by the two new checked identifications.

A subsequent physics-oriented task must freeze one actual compatibility
question beyond this surface action: reconstruction and shared-face shape
matching, an original native action/constraint/history restriction, or a
same-problem computational comparison. Specify the exact known baseline,
the missing output and the full admissible inputs before implementation.
Do not infer a native R7 physical state or R8 geometric cell from the
character-presentation dictionary. The Q1 source correction and the
independent coframe/connection/history/halo requirements remain in force.

This revisits B06 without adding research-round counts. The twelve original
dispositions stand, C01-D06 remain unstarted, and the physical bridge is
still unestablished. The two new literals are known-mathematics
specializations approved by fidelity review04; their state is in STATUS.md.
