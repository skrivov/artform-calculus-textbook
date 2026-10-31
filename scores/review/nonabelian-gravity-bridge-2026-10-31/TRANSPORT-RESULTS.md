# Matched cell-sector geometry separates the two score updates

The next transport test has a negative and a positive outcome. Starting
from two intrinsically matched spherical orthants with specified sector
seam transports, the complete face kick has corrected normal Gram
determinant-1/4. It cannot represent a nondegenerate positive-curvature
target cell under the pinned simple-path convention. A one-link drift
instead preserves a nonempty domain of matched intrinsic cells and
independent connections, with genuine motion on gauge orbits. That drift
does not preserve the stricter seam prescription. Neither update is
thereby identified with a gravitational Hamiltonian.

This completes the specific diagnostic in TRANSPORT-CONTRACT.md. It closes
the earlier gap about whether the original erasing links were matched:
those links are explicitly excluded by the new seam condition, but a
different, fully prescribed starting connection still exposes a geometric
failure of the full kick. All31 prior NGB modules and269 prior approvals
are preserved. Two additive submissions undergo independent review06 by
the single user-authorized Sol6.1 worker. STATUS.md records their final state.

## An actual intrinsic face matching

Both cells are the positive orthant of the radius1 three-sphere. The
target vertices are the four coordinate vectors. The source has opposite
orientation and HHR labels(3,2,1,4) in those coordinates. The vertex-label
permutation is an involution. Pair target face1 with source face3, face2
with face2, face3 with face1, and face4 with face4. Every paired vertex
coincides in the two copies' coordinates. The full three-vertex Gram on
each face is I, so the corresponding geodesic triangular face is matched
by the coordinate identity, including its labelled tangent geometry.
These are complete face data, not an area-only matching.

The cellwise quarter-circle transport is justified in DIPOLE-RESULTS.md.
The physical seam differential J_f fixes every vector in the face
hyperplane and reverses its coordinate normal. Use target base frame
(-e1,-e2,-e3) and opposite-oriented source frame(+e1,+e2,+e3) at vertex4.
In these coordinates the first three based seams are -J_f. For face4,
whose triangle does not contain the base vertex, compose o42 J4 o24 using
the same special-edge24 stem in each cell. The resulting proper rotation
matrices have the unit-quaternion lifts

```text
U=(i,j,k,j).
```

The minus sign comes from the frame change. The matrix -J_f in oriented
three-frame coordinates does not fix the same two coordinate components;
the physical differential J_f fixes actual face tangents. Confusing these
statements would invalidate the transport dictionary.

The source simple paths are the label-swapped inverse target paths, with
the same special edge24. Its HHR holonomy tuple is(Q2,Q1,Q0,Q3). With the
previous target P tuple and these links, Qe=Pe^-1 exactly. The source axes
are(-k,-j,-i,+j); its corrected Gram is I and every convexity triple is+1.
The four source quaternion actions agree with the actual source loop
matrices. Both complete Gauss equations hold and all eight U/P values
have unit quaternion norm. The old erasing lift fails the new seam action.

## The transport is sector-based

The double has singular edges and vertices. Basepoint e4 and the edge24
stem sit on those strata. The construction uses one-sided cell frames,
intrinsic cellwise transports and the specified seam differential; it is
not a smooth global Levi-Civita connection through singular points.

One can cross a face at an interior point: move along the chosen face
within each cell, apply the seam differential and return. The coordinate
normal is parallel along the totally geodesic face, so the reflection
commutes with these tangential transports. Their one-sided endpoint
limit gives the stated based seam. The face4 comparison includes the
declared cell-sector edge stem. This fixes a precise discrete transport
prescription without assuming a nonexistent smooth connection at the
corners. It is not a native coframe/connection/history construction.

Lean checks the finite vertex/metric, reflection, path, frame and
quaternion identities. The continuous cell-sector interpretation is
reviewed mathematical reasoning, not a new formal manifold or gluing
theorem. The pinned path and Gram conventions are those of
[Haggard–Han–Riello, §§2 and4](https://arxiv.org/html/1506.03053v1).

## A stronger obstruction than the deleted-face example

For the actual matched fixture the first digon has k=U0 U1^-1=-k_quaternion.
Its complete forward kick gives

```text
P'=(r(-j-k),r(i+k),r(1+k),r(1-j)), r=sqrt(1/2).
```

Both Gauss equations still hold. All four P remain unit and noncentral.
Their normalized imaginary axes are

```text
n'=( -r(j+k), r(i+k), k, -j ).
```

The corrected pair24 uses n2' dot Ad(P1') n4', in one-based face labels.
It equals-r. Binding this formula to the actual computed P, rather than
to a separately assigned matrix, gives

```text
G'=[[1,-1/2,-r,r],[-1/2,1,r,-r],[-r,r,1,0],[r,-r,0,1]],
det(G')=-1/4.
```

The second convexity triple is0. Every choice of normal-axis signs sends
G' to D G' D with D diagonal signs, leaving its determinant unchanged.
Simultaneous quaternion conjugation also fixes the corrected Gram. Lean
proves the determinant value under all sign assignments and all invertible
quaternion gauges. A branch choice, central lift sign or frame rotation
cannot restore a positive determinant.

A nondegenerate spherical cell has positive normal Gram determinant;
this is the external geometric criterion in
[HHR, §4 equations44–45](https://arxiv.org/html/1506.03053v1).
Thus the tested full kick leaves the fixed positive-curvature sector.
Negative determinant alone does not reconstruct an admissible hyperbolic
cell, and no such reconstruction is claimed. This test does not exclude
different update laws or sufficiently small local steps.

## A nonstationary domain for independent connections

The positive comparison uses the known target moment-map twist on one
link: Ue -> Pe Ue, with P fixed. Its inverse uses Pe^-1. For every group,
Lean proves preservation of each Q as well as each P, both complete raw
defects, inverse and independent endpoint gauge covariance.

IntrinsicMatched fixes the target tuple P and source tuple Q to the two
matched cells above, with all link norms1. IndependentAdmitted is its
saturation under two independent **unit-norm quaternion** endpoint gauges.
The norm guard matters because Hˣ, used as the ambient Lean carrier,
also contains invertible quaternions whose norm differs from1.

The domain is nonempty. Every admitted state has Gauss and unit U/P.
Every signed one-link drift and every unit-norm endpoint gauge preserves
it. Consequently the already constructed cells and their complete
intrinsic face matching remain available throughout these drift histories.
This is a precise kinematical domain, not a collection of stationary inputs.

On its specified fixture, the edge0 drift changes the gauge-invariant
mixed real trace Re(P1 U0 U1^-1) from0 to-1/2. No full endpoint gauge
relates the before and after states. The drift is therefore nonstationary
even after quotienting gauges, while both intrinsic cell tuples stay fixed.

It fails the strict seam action: the edge0 rotation changes from pi to
3pi/2 about i. This is connection motion on a fixed intrinsic geometry,
not intrinsic gravitational evolution or a proof that the connection
variable is an Ashtekar–Barbero or selected extrinsic-curvature field.
An independent connection and a prescribed intrinsic seam transport are
different physical choices. The distinction is consistent with the
flat comparison in
[Freidel–Speziale, §§1.3 and5.1](https://arxiv.org/html/1001.2748v1);
that flat dictionary is not automatically a curved native-field binding.

## Novelty, consequence and next decision

The broad need to distinguish closure, shape matching and connection
constraints is established. For example,
[Anzà–Speziale](https://arxiv.org/abs/1409.0836)
derive additional conditions in a particular flat dynamics model; that
result does not supply a general preservation theorem for this curved
score. The drift itself is known AMM machinery. Our contribution here is
the explicit matched-sector dictionary, checked obstruction, invariant
independent-connection domain and gauge-orbit control. No priority or
new gravitational dynamics claim is made.

The current full face kick should no longer be treated as a candidate
universal positive-curvature geometric evolution. Retain it as the checked
gauge/surface operation that it is. The connection drift can serve as a
kinematical control and a test of score realization, but quantizing that
motion would not select a physical state or a gravitational Hamiltonian.

The next substantive target is a source-selected constraint or Hamiltonian
on the **independent** connection carrier. Before proposing a repair,
pin its geometric variables, admissible histories, boundary data and
complete constraints; derive its infinitesimal action and test a score
factorization against that action. A small-step parameter, endpoint
rejection or a generic known bending flow is not enough to identify it.
NEXT-CONTRACT.md records this priority and the retained reduction/native
gates. All eight native gravity routes remain open, no new material R7/R8
application is credited, and no additional research-round count is added.
