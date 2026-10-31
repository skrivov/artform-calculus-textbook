# Independent review of analytic, stabilizer and geometric-preflight submissions

Reviewer: the same distinct `ngb_independent_review` worker authorized by the
author. It authored none of the nine submitted analytic production modules,
and spawned no additional workers. The original eleven production modules and
their eight review01 approvals remain unchanged. The four CNI submissions
remain pending and are outside this review.

**Verdict: approve NGB:analytic-interpretation,
NGB:stabilizer-preservation and NGB:geometric-preflight; return none.**
The analytic result supplies an
actual quaternion curve interpretation of the finite algebra. It does not
construct a global differential-form bundle, verify all quasi-Hamiltonian
axioms or establish a regular reduced symplectic manifold. Neither result
identifies a native gravitational law or credits a material R7/R8 application.

The exact reviewed source and reachable-surface hashes are recorded in
[verdict-independent-02.json](verdict-independent-02.json). The reviewer did
not modify production files, manifest, generated status or review log.

## Analytic interpretation

`Differential.lean` evaluates a formal one-form as an integer linear
combination of actual conjugated tangent values. The proof that this value
matches `rightWord` respects the prefix convention even for inverse letters.
For an inverse, the right-trivialized derivative is
`-Ad(g^-1) x`; its product with `g^-1` gives the correctly ordered actual
inverse derivative. The analytic proof uses Mathlib's noncommutative inverse
and product rules. It does not assume a Maurer differentiation axiom.

The normed-division-ring theorem applies when every generator curve has the
written value and derivative at the selected real parameter. Its specialization
to real quaternions is faithful to the literal claim. The point values are
units. Curves need not have unit norm, and the proof does not demand global
invertibility of an arbitrary curve. The previously approved word-binding
result identifies unit-valued curve substitutions with the actual group
processes. Derivatives through an invertible point are adequate for the local
curve statement; a global manifold result is a separate question.

`QuaternionForm.lean` uses `-Re(ab)`. Cyclicity of real quaternion trace
proves conjugation invariance for arbitrary units, rather than postulating
it. On imaginary quaternions this is the positive Euclidean pairing. The
expanded two-form keys use the relative conjugation `u^-1 v`. Their second,
negative key has exchanged generator indices and relative conjugation
`v^-1 u`, matching the stated exterior evaluation. Symmetry of the trace
pairing makes the written second term the usual antisymmetrized contraction.
No positive-definiteness of this pairing on all quaternions is claimed.

`AnalyticForm.lean` defines both left and right values using `deriv` of actual
finite product/inverse curves. Their equality to the corresponding one-form
valuations is proved. The edge summands use `A=U,B=U^-1 P`; fusion multiplies
the declared prefix before its next moment and uses the original relative
sign. The fold proof binds all these actual derivative summands to the
formal two-form for every word-state substitution. The three preservation
identities then follow from the approved finite certificate under this
proved interpretation. They are no longer merely arbitrary key valuations.

The result remains a curve-evaluation theorem. In particular, it neither
asserts closedness/nondegeneracy of an ambient form nor silently regards
the entire Gauss quotient as a regular manifold. The canonical exclusions
are scientifically necessary and match the Lean target.

## Non-vacuity and its boundary

The Cayley curve `(1+t*i)(1-t*i)^-1` has a denominator with real part one,
so it is defined at every real parameter. Lean proves its norm square is
one and its derivative at zero is `2i`. Varying U0 and independently P0
gives the exact actual `analyticTwiceOmega` value eight at the all-identity
baseline. This verifies a nonzero analytic evaluation with curves entirely
inside the unit-quaternion group, rather than a freely chosen functional
on formal keys.

This baseline has a nontrivial gauge stabilizer. Moreover, the independent
P0 variation changes the incoming vertex1 moment and is not tangent to the
Gauss level. Thus eight is an **ambient** non-vacuity value. It proves neither
nondegeneracy on the constrained tangent space nor a nonzero reduced form.
The submission does not claim either conclusion; no return is needed.

## Stabilizers

The stabilizer is the exact set of functions on all six vertices fixing the
raw state under the actual production action. The score has a left inverse,
so it is injective. Gauge covariance and injectivity show both directions of
the stabilizer equality with the same gauge function. No replacement by
conjugate stabilizers, finite samples or a restricted gauge subgroup occurs.
The theorem has no Gauss or free-action hypothesis and therefore also applies
to the complete admitted carrier. It is useful for orbit-type control, but
does not show that any particular stabilizer is discrete or that reduction
is smooth.

## Geometric preflight

The finite canvas has no vertex of valence four. The explicit quaternion-i
cycle is admitted by all six Gauss equations. Its actual complete face0
kick changes the four cycle impulses from i to minus one, with all links
and impulses retaining norm square one. Real parts zero and minus one
separate P0 before and after the kick. The trace-invariance theorem rules
out conjugation by every invertible quaternion, not just sampled unit gauges.

This is a valid adverse control to a universal individual fixed-conjugacy
interpretation of the existing map. Neither state is asserted to reconstruct
a nondegenerate tetrahedron. In particular, the changed class does not rule
out moving-area geometry or a differently designed four-valent constructor.
The literal and Lean target maintain these limits.

## Independent arithmetic and checks

[replay-independent-02.py](replay-independent-02.py) imports only the earlier
independent real-matrix representation, with no author replay imports. It
compares direct matrix product/inverse differentiation with the right-Maurer
cocycle expansion for all 1,555 signed words of lengths zero through four,
at both a unit and a nonunit quaternion assignment. All 3,110 ordering checks
pass. Five rational Cayley parameters have unit norm and the ambient doubled
form value is eight. Exhaustive checks of all 46,656 S3 vertex gauges at the
noncommuting witness and the singular identity state reproduce exact
stabilizer-set preservation. Those finite sizes are replay facts, not new
registered counting theorems.
The same independent matrix replay verifies the geometric-preflight cycle,
all unit norms, both complete Gauss conditions, the valence bound and the
real-part separation of its flux classes.

Kernel replay and build receipts, exact reviewed hashes and final source
integrity checks are recorded in
[validation-independent-02.json](validation-independent-02.json). The
analytic improvement discharges the curve-semantics gap. Regular reduction,
geometric reconstruction/gluing and a native action/constraint correspondence
remain separate continuation obligations.
