# Independent R2 trace-arithmetic review, 30 October 2026

Reviewed freeze: `a2c754a9f65f03c1bbc5fc82ab1b0874e8c05c92`.
Reviewer: the distinct `gravity_fidelity_review_01` agent, which authored none
of R2Defs, R2Statements or R2Trace. This review changes no implementation or
original proof and leaves all 70 earlier approvals intact.

**Verdict: approve GAC:r2-trace-reduction; return none.** Its five conjuncts
faithfully formalize the literal ledger section 7 statement and finding 107.
The result is exact trace arithmetic, with explicitly guarded denominator
clearing. It makes no new feasibility or native reconstruction claim.

See [verdict-independent-02.json](verdict-independent-02.json) for the reviewed
hashes and [validation-independent-02.json](validation-independent-02.json)
for the independent reproduction results. The source review read corrected
original force 5edba7e6, four-row source 09793524, its distinct review f1c17128,
F01's chart/scope record and finding 107. All six F01 hashes authenticate;
the three bounded R2 snapshots also match their pins and live originals.
Historical UNREVIEWED titles remain historical and do not approve this Lean
submission.

## Original source correspondence

The change of coordinates is exactly `x=1-a`, `b=2-3a`, `D=3-s` and
`h=as+b=s-1+(3-s)x`. Substitution into the original normal equation gives
`N=s²+(5-8a+6G)s+2b²`. The constants in `rows` and `rowPolys` are the physical
`t=103/2` and the rational half; d is independent of latitude s.

The Lean complex inputs retain `zeta=1-a+i*gamma`, `E=1-zeta`, the corrected
`Bc=1-iq`, and `Q=1+iq-2iq*conj(zeta)`. The four terms of `originalJ` agree
with corrected source section 4, including both h contacts and the factor s
in the second term. `originalW` and `originalBhat` retain their definitions
before any normal-locus simplification.

I separately expanded the original source inputs

    P=(1+R)(1-iq)E, Q=1+iq-2iq*conj(zeta), L=1+R-iqR

with exact rational-coefficient arithmetic over Q[i]. They give

    conj(P)L-Q*conj(L) = phaseT,
    P*conj(P)-Q*conj(Q) = phaseDelta.

This independently checks the phase definitions against the original P/Q
system rather than taking a formula named T or Delta on trust. In particular
Delta retains the `+4q*gamma` term. With `G=gamma²`, the same expansion gives the exact identities

    W-s*(w+i*(1+s)*gamma) = N/2,
    Bhat = Ub+iq*Vb+gamma*s*(-3q+i),

where w, Ub and Vb are the literal M178 expressions. The reproducible
[source arithmetic witness](source-arithmetic-independent-02.py) uses only
Python's rational arithmetic and reports four zero coefficient dictionaries.
It supplements the literal comparison and the Lean kernel replay.

## Four rows and monic normal reduction

Every product-table entry Ce, De, Eo, Fo, Ie, Je, Ko and Lo matches frozen
09793524 and its distinct review, including the gamma-squared signs in Ie/Je
and the original odd contribution from `-E(3+iq)`. Each of the four `rowExpr`
entries agrees with the corresponding Pe, Qe, Po or Qo product.
The registered first conjunct states their exact complex reconstruction under
`q²=103/2`, `gamma²=G` and `N=0`. It does not assume the result by definition.

`rowPolys` are genuine polynomials in s, and their evaluation lemma links them
to the scalar rows. The second conjunct bounds the latitude degree by three
for every R,a,G and every one of the four rows. It does not assert a new radius
degree bound. The third conjunct quantifies over every polynomial of degree
at most three, including the zero polynomial, and checks

    P(s)-(ell*s+n) = N(s)*(c3*s+c2-nu*c3).

Here `ell=c1-nu*c2+(nu²-k)c3` and `n=c0-k*c2+nu*k*c3`, exactly as in M178.
No leading coefficient, affine coefficient or remainder is divided out.
In particular the entire `ell=n=0` stratum remains present.

For the fourth conjunct, adding and subtracting the two signed J equations
isolates the even and odd complex parts. The explicit nonzero q and gamma
guards then identify all four real rows with zero. The monic identity gives
the equivalence to all four affine remainders at s. Both directions are
proved. The assertion concerns both signs jointly and supplies no inference
from one successful sign to the other.

## Original trace clearing and positive example

`traceResidual` retains exactly

    Atr=2LW/(sDE), Btr=Bhat/E,
    RD*Atr+R*Btr-R(3+iq)
      -2h*Atr*T/Delta-2Rh*Btr*conj(T)/(s*Delta).

The fifth conjunct independently quantifies over real q,R,a,gamma,s and keeps
all four guards `s!=0`, `3-s!=0`, `E!=0` and `Delta!=0`. Its proof checks the
identity `s*(3-s)*E*Delta*traceResidual=J` and proves that multiplier nonzero
before using the zero equivalence. It introduces no R, h, Atr or Btr division.
Although the polynomial identity can be evaluated outside the physical
chart, no such row zero is declared a reconstructed original force solution.

The positive example uses `a=1`, `s=3/2`, `G=1/36`, `gamma=1/6`, `R=1`,
and positive `q=sqrt(103/2)`. It checks the normal equation and both signed
Delta and E guards. The remaining s,D,q,gamma nonzero premises follow directly
from these nonzero constants and q positivity. In fact the signed determinants
are `2837/18 ± 2q/3`, both positive with `q<8`. This witnesses the reduction
hypotheses; it is not presented as a phase-norm or full-force solution.

## Validation and scope

The independent full warnings-as-failures build, generated book and ledger
reports, both status checks, identity/tree check, both certificate checks and
R2Trace kernel replay passed. The tagged proof has exactly the tagged target
and only the allowed axioms. All 70 earlier manifest entries remain unchanged
and approved-surface drift is empty. The approval was recorded with the
existing ledger_status machinery after adding its required empty review
metadata fields to the new entry.

This approves the already reviewed native reduction's polynomial arithmetic.
All-zero-row emptiness, feasibility or exclusion, phase norms, radial/normal
reconstruction and its guards, single-handedness selection, full forty-row
reconstruction, physical boundaries and a gravitational parent remain outside
this statement. The reviewed source's pre-existing results are not counted
as newly discovered material native applications.
