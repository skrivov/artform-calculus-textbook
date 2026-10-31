# Frozen continuation: matched orthant sectors and two distinct updates

Baseline9985bfafb9fbecf300df1186843c05a0b919ef41. This follows the exact
NEXT-CONTRACT.md geometric transport question. The unrestricted-link
erasing lift was not known to be geometrically matched. Here specify an
actual pair of cells and a stricter transport prescription, then test the
same full digon kick. Also test a link drift to distinguish preservation
of intrinsic geometry from preservation of that transport prescription.

## Cells, faces, orientations and sectors

Take two copies of the positive orthant in the unit three-sphere. Glue
each face to the coordinate-identical face in the other copy. The source
copy has the opposite orientation; use source vertex labels(3,2,1,4) in
target ambient labels. The resulting face pairing is1<->3,2<->2,3<->1,4<->4
in the two respective HHR labellings. Check all paired vertex positions
and the full three-vertex face Gram matrices, not areas alone.

Use target frame(-e1,-e2,-e3) and source frame(+e1,+e2,+e3) at their
respective vertex4. The source HHR simple paths are the label-swapped
target inverse paths, with the same special edge24. Thus its HHR tuple
is(Q2,Q1,Q0,Q3). Declare this correspondence and check the actual words.

Cellwise Levi-Civita transport is the existing quarter-circle formula.
Across face e, the seam differential fixes the whole physical face
tangent plane and reverses the transverse outward normal. In the copies'
ambient coordinates it is the reflection J_e in coordinate e. Its
effective coordinate matrix between the opposite oriented 3-frames is
-J_e for the three faces containing vertex4. For face4 use the declared
edge42 stem on each cell: o42 J4 o24, followed by the same frame change.
This gives SU(2) link lifts U=(i,j,k,j).

This is a **cell-sector** prescription: basepoints and stems are on
singular strata of the doubled polyhedron. Transports and frames are
one-sided cell-sector limits; they do not define a smooth global
Levi-Civita connection at those strata. An equivalent crossing in a face
interior uses cell paths followed by the totally geodesic seam reflection.
Document this qualification explicitly. Do not mistake the physical J_e
fixing tangents for the opposite-frame coordinate matrix -J_e.

## Negative test: the full digon kick

Use the previous actual target P tuple, r(1+i),r(1+j),r(1+k),r(1-j),
r=sqrt(1/2), with these four link lifts. Check unit norm, both complete
Gauss stars, transported source holonomies and geometric seam matrices.
The old erasing lift must fail this stricter link prescription explicitly.

The first full forward kick has k=U0 U1^-1=-k_quaternion and yields

```text
P'=(r(-j-k),r(i+k),r(1+k),r(1-j)).
```

All faces remain noncentral. The correctly transported target normal
Gram is

```text
[[1,-1/2,-r,r],[-1/2,1,r,-r],[-r,r,1,0],[r,-r,0,1]],
```

with determinant-1/4; the second convexity triple is0. Prove the actual
quaternion binding, not only a separately entered matrix. Check determinant
invariance under every normal-axis sign choice and simultaneous gauge
conjugation, so neither lift/branch choice nor gauge restores positivity.
Under the pinned HHR fixed-simple-path prescription, a positive-curvature
nondegenerate spherical cell has positive normal Gram determinant. Thus
the full kick leaves that admitted sector even from this matched start.
Do not reconstruct the endpoint as a hyperbolic cell merely from det<0.

## Positive comparison: independent-connection drift

For any group and chosen link, Ue -> Pe Ue with P fixed has an exact
reverse, commutes with the independent two-vertex gauge action and fixes
every outgoing Q as well as every P. Hence all source/target intrinsic
cell data and the established intrinsic face matching remain unchanged.
On the matched orthant fixture, the one-link drift at edge0 is
nonstationary even on gauge orbits: the gauge-invariant mixed trace
Re(P1 U0 U1^-1) changes from0 to-1/2.

That drift does not keep the prescribed seam differential. Verify this
failure explicitly. It is a nonstationary intrinsic-geometry-preserving
score only when the connection is admitted as independent data. It is
not an identified Ashtekar-Barbero/extrinsic-curvature law and does not
meet the stricter fixed transport contract. Its underlying target twist
is known AMM machinery, not a novel gravity mechanism.

Package the positive comparison as an actual invariant domain: fixed
target P and source Q tuples of the matched cells, unit link norm, and
its saturation under the full two-vertex unit-norm quaternion gauge action. Prove invariance
under every signed one-link drift. This packages the declared independent
connection comparison; it does not add a gravitational field identification.

## Credit and decisions

Two new canonical submissions will cover matched cell-sector data and
the negative/positive update comparison. Preserve every old proof and
approval, keep the four inherited CNI claims pending, use one Sol6.1
reviewer and publish checked results in the owned lane. This continues
the B06 compatibility diagnostic without inflating round counts or
silently activating C/D. Smooth regular reduction, a native R7/R8 field
binding and physical dynamics remain open. Zero new material native
gravity applications are credited by this contract.
