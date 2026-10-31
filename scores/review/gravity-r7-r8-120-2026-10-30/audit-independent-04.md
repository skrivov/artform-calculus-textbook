# Independent coframe and connection-return review, 31 October 2026

Reviewed freeze: 912b840c561810f3491e3ef04e4498673f90eec6.
Reviewer: the distinct `gravity_fidelity_review_01` agent, which authored none
of the fifteen submitted Lean modules. All 134 previous approvals stand;
no implementation or original proof was changed.

**Verdict: approve all five literal claims; return none.** The coframe split,
supplied cut jets, retained residual, formal sampling and original sign
conversion have their stated algebraic meanings. They establish zero new
material native applications and no retrospective efficiency saving.

See [per-key verdicts](verdict-independent-04.json),
[independent validation](validation-independent-04.json) and
[exact arithmetic replay](arithmetic-independent-04.py).
The review inspected all fifteen files and their examples, compared the
five literal manifest quotations with section 8 and findings 172–176,
and authenticated all fourteen original/snapshot pairs.

## GAC2:metric-coframe-lorentz-isomorphism — approve

The metric readout uses the original internal-row eta signs:
m(F)_ij=eta_i F_ij+eta_j F_ji. Its codomain is the actual symmetric
submodule, rather than an unconstrained sixteen-coordinate substitute.
The original Lambda has symmetric boost entries and antisymmetric
23,31,12 rotation entries. The inverse is eta*m/2+lie(w), with eta
multiplying internal rows. Both readouts of that reconstruction and the
reconstruction of every original coframe are proved.

The explicit `coframeSplit` is a linear equivalence whose forward map is
exactly the declared pair of readouts. Although the registered statement
expresses existence of the equivalence, its proof is not an unrelated
dimension-count isomorphism. The injectivity implication is also explicit.
The nonzero six-coordinate Lorentz example has zero metric, so the theorem
does not identify the metric alone with the original coframe.

This agrees with the flat algebraic part of section 1 of the frozen
[connection-target reduction](source/connection-target-reduction.md).
It supplies neither an independent connection nor a physical quotient,
nonlinear frame matching or a native solution.

## GAC2:coframe-cut-value-velocity — approve

Both slots of `Fin 2 → Frame K` are supplied data. The theorem quantifies
over every such pair and proves both directions: full equality is equivalent
to equality of both metric and Lorentz readouts at each slot. Zero readout
differences are included by taking the second tuple to be zero. There is
no assumption that these arbitrary slots are derivatives of an actual
field, and no such conclusion is drawn.

The metric-only counterexample is an original nonzero boost with zero
metric variation. The independent-connection counterexample gives two
full jets with identical coframes at both slots while a connection
coefficient at the first slot differs by one. These statements are in
the registered conjunction, not merely explanatory prose. The positive
example uses a nonzero six-coordinate Lorentz coframe at both slots.

Consequently the theorem isolates precisely the algebra used after the
source has separately established metric Cauchy matching and copied the
coframe Lorentz profile all time. Actual differentiation, spatial cut
identities and native field equations remain separate premises; they
are not supplied by an algebraic two-slot representation.

## GAC2:connection-residual-return — approve

For arbitrary modules over a ring, r=Cu+Dv and A=-EC are exactly the
declared maps. From Cf+Da=0 the proof uses E(Da)=a, including the same
left-inverse identity on v, and obtains

    a-v = A(f-u)-E*r.

Conversely applying D uses D(Ew)=w and recovers the complete original
equation Cf+Da=0. The iff retains both inverse identities; they are not
interchanged or silently inferred from each other. The minus residual
sign matches section 2 of the frozen reduction and its
[independent review](source/M186-review.md).

The rational example satisfies the inverse guard, has comparison residual
one, and returned difference minus one despite graph difference zero.
Thus dropping the residual changes a concrete admitted algebraic result.
The independent replay also uses a nonscalar, nonsymmetric two-sided
inverse with nonzero residual, obtaining returned difference (17,-29).

Nothing constructs an actual J_aa inverse, validates a native source or
proves a contour estimate. The source's bounded whole-contour inverse
with temporal shifts is not replaced by an instantaneous solve or a
pointwise-in-time prescription.

## GAC2:connection-first-order-sampling — approve

`centerJet` and `physicalJet` are inverse shears on a pair of coefficients.
Their first entries are unchanged and their second entries differ by
minus or plus L*q0/2. Both compositions are proved on arbitrary modules.
The physical coefficient retains the entire contact
-2*kappa*E(R f), alongside L(Omega f)/2, and centering returns that contact.

E is arbitrary: neither inverse identity is among the hypotheses. The
independent arithmetic therefore deliberately also tests a singular E
with noncommuting L,E,R. This is valid formal sampling and provides no
native inverse. In an application the original full curvature-plus-torsion
B inverse, source R, graph Omega, derivative L and analytic remainder
must all be identified separately. The formal coefficient cannot justify
a curvature-only replacement or remove the original -2*kappa factor.

The example (1,-2/101) maps to (1,97/202) and back, with both sampling
and contact nonzero. It is a rational coefficient example, not an actual
Taylor family. Section 2 of the source and the M186 review retain exactly
that distinction between coefficient algebra and the actual graph expansion.

## GAC2:lower-boost-physical-native-sign — approve

For supplied lower-coordinate derivative slots H_iI, the gradient frame
is eta_I H_iI and its symmetric representative is
eta_I(H_iI+H_Ii)/2. Their difference is the original lie(gamma). The boost
entries are (H_0a-H_a0)/2; rotation entries use the original 23,31,12
orientation. Both Lambda identities are proved in all six coordinates.
The lower temporal row is negative: G^0_a=-H_a0. The full definitions
retain this for every spatial a; the final explicit temporal test uses a=1.

With the source's original physical column (lie(gamma),-dgamma), subtracting
that column from the zero-connection gradient leaves the symmetric frame
and positive dgamma. The native conversion P=-h*omega then maps the
physical Lorentz column to (lie(gamma),+h*dgamma), agreeing with the earlier
fixed-log +D*w convention after the actual derivative/shift identification.
This is a forward scaling identity, so it remains valid even at h=0;
it is not an invertible coordinate conversion at zero spacing.

The nonzero boost and h=1/2 connection example check both signs. The
independent matrix replay checks all lower and rotation signs on mixed
rational data. Actual derivatives, torsion-free stationarity and the
quarter-contact cut condition of section 3 of the source are not newly
proved or presumed for arbitrary H,dgamma.

## Validation and scientific scope

The independent warnings-as-failures build, both reports, status/tree
checks, all certificate checks, both empty drifts and five separate
kernel replays passed. All tagged proofs have their exact targets and
only allowed axioms. The exact arithmetic replay checks all sixteen
frame basis directions, all ten symmetric basis directions paired with
all six Lorentz basis directions, mixed rational lower-coordinate data,
nonscalar residual return and formal sampling with singular E.

An initial reviewer-only replay attempted to use the inherited four-by-four
matrix multiplier on a two-by-two block and raised IndexError. Its local
block check was corrected to use a dimension-aware multiplier and rerun
successfully. No submitted Lean file or mathematical claim changed.

All 134 earlier manifest entries and all fifteen submitted modules remain
unchanged. Original Gram/domain qualifications, M185's status at the pinned
cutoff, M186's mandatory scoped reduction and its unevaluated longitudinal
functional remain intact. Authenticating the later prospective certificate
does not accept its value. The full native contour inverse, actual analytic
sampling and graph, allowed sources/preparations, physical boundary/quotient
and independent frame/link/history prescription are still uninstantiated.
The inherited first campaign's one scoped R2 application stands; no new
material native R7/R8 gate or matched efficiency gain follows here.
