Current continuation: TRANSPORT-RESULTS.md records the matched cell-sector test and independent-connection comparison. STATUS.md has current review counts; the results below retain their original scope.

# A geometric admission obstruction for the unrestricted dipole kick

The full oriented digon kick can preserve both complete Gauss equations
while deleting a face of a genuine spherical target tetrahedron. The
connection choice that does this is admitted on the unrestricted group
carrier. It has not been shown to be admitted by a matched two-cell
Levi-Civita transport prescription. The result therefore rejects unrestricted
links as a sufficient geometric evolution model and selects the missing
transport/admission condition as the next research dependency.

This is the specific compatibility diagnostic frozen in DIPOLE-CONTRACT.md.
It adds no research-round count, does not pass decision12, and does not
activate C01-D06. Checking this obstruction before completing the known
smooth-reduction formalization saves work on a candidate whose geometric
domain is not yet specified. The reduction contract remains necessary for
any later use of a reduced symplectic form.

## The exact group result

Dipole.lean defines an actual two-vertex, four-link Canvas with the three
non-wrapping adjacent digon boundaries. Both ordered stars are complete,
have no duplicate half-edges and have valence4. All links point from
source0 to target1. With `Qe=Ue^-1 Pe^-1 Ue`, the raw defects are

```text
source: Q0 Q1 Q2 Q3
target: P3 P2 P1 P0.
```

Only the first digon is evolved. Its target-based holonomy is
`k=U0 U1^-1`, and the complete forward update is

```text
P0' = k P0
P1' = P1 k^-1
P2' = P2, P3' = P3, U' = U.
```

The reversed stored-edge occurrence requires this right multiplier. Lean
proves raw equality of both defects, exact inverse and two-vertex gauge
covariance for both signs. No cyclic wrapping face, symplectic statement
or continuous timestep is silently included.

For *every* target tuple with `P3 P2 P1 P0=1`, choose

```text
U=(P0^-1,1,1,1).
```

Each source flux is then `Qe=Pe^-1`, so its complete source star closes as
well. The kick has `k=P0^-1` and gives exactly

```text
P'=(1,P1 P0,P2,P3).
```

The deleted face remains identity under every gauge. More generally, let
A be any set of target tuples containing a closed tuple and requiring
P0 nonidentity. There is no forward-invariant domain obtained by imposing
only `P in A` and Gauss while retaining every independent link lift. This
quantifier is part of the registered theorem. It does **not** say that no
noncentral-face invariant domain exists: the identity-link lift of every
closed tuple is Gauss-admitted and fixed by the kick. Lean checks that
positive control too.

## A genuine spherical target, not closure alone

Take the positive orthant of the radius1 sphere in Euclidean four-space.
Its vertices are the four coordinate vectors. The positive unit vector
`(1/2,1/2,1/2,1/2)` lies in its interior. The vertex Gram is I with
determinant1. Its faces are geodesic spherical triangles with three right
angles, so each has area pi/2. Its edges have length pi/2. These metric
facts specify an actual nondegenerate convex spherical tetrahedron.

We use the simple paths and special edge(24) in
[Haggard–Han–Riello, §2 equations12,17, and convexity conditions](https://arxiv.org/html/1506.03053v1).
Here is a direct check of the connection convention. Along

```text
gamma(t)=cos(t)e_s+sin(t)e_t,
```

a tangent vector at e_s decomposes as `a e_t+w`, with w orthogonal to the
source/target plane. Its transported vector is

```text
V(t)=a(-sin(t)e_s+cos(t)e_t)+w.
```

The derivative is `-a gamma(t)`, which is normal to the sphere. Hence the
tangential covariant derivative is zero. At pi/2 this is exactly the
ambient quarter-turn matrix in SphericalOrthant.lean. This calculation
justifies its Levi-Civita interpretation; no assumption that an arbitrary
closed tuple is geometric is used.

At vertex4=e4 use the positively oriented tangent frame `(-e1,-e2,-e3)`.
The outward normals to faces1,2,3 have coordinates i,j,k. The outward
normal to face4 at vertex2 transports along edge24 to a vector with
coordinates -j. The four based loop matrices are therefore quarter turns
about i,j,k,-j. SphericalOrthant.lean checks their actual ambient products,
base vertex, tangent restrictions, orthogonality, determinant and closure.

For `r=sqrt(1/2)`, SphericalFixture.lean constructs the units

```text
P=(r(1+i),r(1+j),r(1+k),r(1-j)).
```

Conjugation by each unit on every tangent basis vector equals the declared
loop matrix. Each has unit norm and squared real part1/2, and their
reverse-order product is1. The normals give the HHR Gram I with
determinant1 and all four convexity triples+1. The exceptional pair24 uses
`n2 dot (O1 n4)`. If one mistakenly uses all four untransported normals,
the resulting Gram has determinant0; that adverse control is checked too.

The fixture thus has actual geometric target holonomies. Its erasing link
lift has all eight U/P unit norm and both complete Gauss equations. After
the full kick, both Gauss equations still hold but P0=1. A nondegenerate
convex spherical triangular face has area strictly between0 and2pi, so
its SO(3) holonomy cannot be identity under this prescription. The collapse
violates even that necessary face condition; it is stronger than the old
fixed-conjugacy adverse control, which was not a tetrahedron.

## What has and has not been formalized

Lean checks the finite vertex, edge and loop matrices, quaternion units,
adjoint action, transported Gram, convexity signs and complete score
identities. The general sphere manifold, its Levi-Civita connection,
spherical area theorem and HHR reconstruction theorem are not defined in
these new modules. Their explicit analytic interpretation above is reviewed
as mathematical source fidelity, separately from kernel verification.

The source vertex also closes, but we have not reconstructed and glued a
second cell, identified all four paired face metrics and labelled tangent
frames, or shown that U0=P0^-1 is the prescribed cross-face transport.
Normal compatibility alone would not establish those conditions.
[Freidel–Speziale, §§1.3 and5.1](https://arxiv.org/html/1001.2748v1)
distinguish intrinsic shape matching and remaining connection data in the
flat holonomy-flux setting; their dictionary is not automatically a curved
group-valued dictionary for this model.

The dipole graph, curved reconstruction and moment-map twists are known
settings. This elementary collapse argument is a checked consequence of
the declared score on a concrete geometric fixture. We make no priority
claim for the argument or for a first formalization. Its practical value
is deciding which candidate interpretation fails before investing in
quantization. It adds zero completed native R7/R8 applications.

## Next executable research question

Specify the cross-face geometric transport prescription and determine
whether it excludes the erasing lift. Start with two explicitly congruent
orthants, an exact pairing of their four faces, complete face metrics and
labelled tangent frames. Separate intrinsic shape matching, independent
connection freedom and Levi-Civita transport. Test whether a nonstationary
score stays in that admitted domain. A domain with only identity-link
stationary motion is a control, not an adequate dynamics result.

If this fails, assess a genuinely restricted or modified local update
against the *same* admitted geometry, keeping inverse, gauge, Gauss and
the chosen physical structure. Merely rejecting an endpoint, matching
areas or invoking known Dehn twists does not solve that task. Only after
this admission problem is settled should we bind regular reduction for
the selected application and attempt quantization or a native R7/R8
comparison. Original Q1, coframe/connection, source, boundary/halo and
history guards remain in force.

The two new literals are NGB:dipole-oriented-score and
NGB:spherical-face-collapse. Current review/check/publication state is
recorded in STATUS.md, audit-independent-05.md and the stage receipt.
