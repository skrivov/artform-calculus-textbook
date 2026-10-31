# Native temporal boundary relation

This continuation changes the target after the conditional compact-rotation
import failed. It derives boundary covectors from the original native source,
then asks whether they admit a useful score representation. Gravity's
programme and historical qualifications remain frozen.

## Fixed source and cut

Use the literal Full40 quadratic density pinned in native-source-pins.json,
including the transported complement, ordered plaquette contact and torsion
terms. Parameters are h=beta=sigma=1, alpha=lambda=0, kappa=1/101. This is
the flat Taylor candidate, whose physical selection remains open. The
connection convention is native A=-h*omega, internal metric(-+++), bivector
order(01,02,03,23,31,12). No nonlinear gravitational evolution is inferred.

The current formal theorem fixes the spatial-zero character. Its40-vector
contains F^I_i at4I+i and A_i^a at16+6i+a. Old/new40-vectors u,v occupy
times0,1. The cut density at0 only uses these two times: the Fin3 storage
does not wrap a face back to0. All40 coordinates remain independent.

Retain the original first-order curvature divergence when cutting the
action. It is ell(u,v)=b.(u-v), b22=b29=b36=1, all other entries0. The
affine-plus-quadratic Taylor cut action is

    L(u,v) = b.(u-v) + u.H0.u/2 + u.B.v + v.H1.v/2.

This is not the full nonlinear momentum. An endpoint counterterm changes
individual covectors; the displayed representative is fixed throughout.
Lean expands the literal density to204 monomials and binds every monomial
to the three declared Hessian blocks. The actual real directional
derivative defines

    p- = -b-H0.u-B.v,       p+ = -b+B^T.u+H1.v.

The mixed B has rank24. Its rotational diagonal rows/columns25,32,39
vanish. This rank is not a physical mode count and a null vector is not
automatically gauge. The spatial coframe diagonal pairs with boosts,
including torsion corrections, rather than the rejected rotational ansatz.

## Relation-valued score and composition

The native relation is exactly an incoming affine kick, central relation
(p=-B.v,q=B^T.u), and outgoing affine kick. The central step is singular.
This supplies a relation-valued extension of the score language; it is not
an instance of a deterministic bijective process profile.

For two cells retain the middle source -j.y. Middle matching is

    p+(x,y)-p-(y,z)=j,
    (H0+H1)y = r,          r=j-B^T.x-B.z.

Put J=diag(0,1,1,1,0,1,1,1,0,1,1,1,0,1,...,1). The explicit D obeys
(H0+H1)D=D(H0+H1)=J. The middle Hessian has rank36; matching is equivalent
to Jj=j and Jy=Dr. Thus j0=j4=j8=j12=0 is mandatory. The remaining four
middle coordinates are not silently integrated out or called gauge.

For every matched middle y, the full stationary action equals

    Seff(x,z,j) = x.H0.x/2 + z.H1.z/2 + b.(x-z) - r.D.r/2.

This retains both endpoint-source terms and the source-contact term.
For x=z=0,j=e25 it is -9595/39964, not zero. The effective mixed block is
-BDB, with exact rank18. A concrete one-cell relation from(0,-b) to
(e25,-b) exists, but its output has no continuation through any source-free second
cell under the unchanged relation: every next pre-momentum has component25=-4/101, while the incoming
component25 is0. Zero source/fields do compose; an inactive source e0 is
incompatible. These witnesses make the statements nonvacuous.

## Use and novelty boundary

Discrete Legendre relations, pre/post constraints, Schur elimination and
region-dependent physical state spaces are established machinery; see
Marsden-West(2001), Dittrich-Hoehn(2013), Hoehn(2014), in particular
https://arxiv.org/html/1407.6641v3 sections7-10. The contribution sought
here is an exact binding to the full native source, its affine boundary
term, actual ranks and extension counterexample, with checked score
factorization and source-compatible elimination. It is not priority for
the general machinery.

This is useful as a concrete R7 boundary-admission and R8 composition
test: a proposal based only on one-cell admission or a universal
40-variable bijective tick fails this native test. It does not select a
physical reduced phase space, prove a curved compact/native field map,
establish a quantum measure, identify constraints as gauge, or solve any
of the eight gravity directions.

## Successors and evidence status

The formal claims belong in ALGEBRA-OF-SCORES.md and require independent
hash-bound fidelity approval. Root exact replay scripts and independent
review calculations are separate evidence. No approval is implied by this
contract alone.

The next source-supported question is the full spatial character symbol.
An independently reproduced Laurent calculation points to rank24 on the
unit circle except rank21 at-1. Its distinct-linear-factor minor, actual
kernel-complement topology and paired real harmonics require a separate
source-bound proof. Do not infer a source-wide inverse theorem from the
zero-character calculation. A quantum kernel additionally needs an
explicit measure/domain and constraint prescription; stationary
elimination alone is not an integral or physical state selection.
