# Independent original norm and phase review, 30 October 2026

Reviewed freeze: `b3aed56aa9a985e831a1aed9308a00ee5405347a`.
Reviewer: the distinct `gravity_fidelity_review_01` agent, which authored none
of the four submitted modules or their statements. The pre-freeze audit was
read-only. No implementation or old proof was changed; all 75 earlier
approvals stand and are not reopened by this review.

**Verdict: approve both entries; return none.** F05 strengthens the same
native R2 coefficient reduction using an original necessary norm equation.
F06 supplies a checked original phase/norm/affine-trace bridge. These do not
constitute a second native direction or a new full-force feasibility result.

The per-key decisions and input hashes are in
[verdict-independent-05.json](verdict-independent-05.json), and independent
checks are in [validation-independent-05.json](validation-independent-05.json).
The literal ledger section 7 quotations, findings 112–113 and four new modules
were compared with the unchanged original corrected-force and M178 sources.
Both manifest quotations are exact ledger text. The original P/Q signs and
the meaning of the affine trace remain those audited in F02.

## GAC:r2-norm-chart — approve

`phaseNorm` retains the original expression
`4h²*normSq(T)-R*s*(3-s)*Delta²`, with h=as+2-3a. `evenDelta` is exactly the
gamma-even determinant d, so `Delta=d+4q*gamma` at G=gamma².
The first conjunct is an identity for every real q,R,a,gamma,s, including
zero values. It neither cancels nor assumes any coefficient nonzero:

    F(gamma)-F(-gamma)=16*q*R*gamma*(2q²h²-s*(3-s)*d).

The auxiliary necessary-constraint lemma cancels only q,R,gamma, each with
an explicit nonzero premise. The simultaneous-sign theorem obtains these
from the physical q square, positive R and nonzero gamma. It does not apply
this cancellation to gamma=0 or zero-radius sectors.

The b=0 contradiction checks against the exact original normal equation.
With a=2/3 and s>0, N=0 gives `s=1/3-6G`, hence `s<=1/3` when G>=0.
At physical q²=103/2,

    d(0)=(97+307s)/12>8,
    d(R)-d(0)=(1+q²)*(4/9+G)*R*(R+2)>0.

The necessary odd constraint would then imply
`(3-s)*d=(412/9)*s<=412/27`, while the left side exceeds 64/3.
Only s>0 is cancelled in this step. No normal root, determinant, h, ell
or n is divided out. Thus the stated necessary chart implies b!=0, and the
already approved exact unit certificate excludes all eight coefficient zeros.

For both original norm zeros and both original J zeros, the signed-trace
and monic identities then supply a nonzero ell pivot without an assumed
large-latitude inequality. All original native chart restrictions remain
required on application. Removing this hypothesis does not assert existence
of new smaller-latitude physical candidates, or rederive every native chart
condition from arbitrary row zeros.

For fixed R,a,G off b=0, two normal latitudes satisfying all four rows give
the same affine equations at two roots. If the roots differed, subtraction
would force all ell=0, and either root would force all n=0, contradicting the
unit identity. The last conjunct therefore proves uniqueness of that latitude,
with no existence or global-finiteness conclusion as the other parameters vary.

The exact positive necessary-domain witness has a=1,G=1/36,s=3/2,
`q=sqrt(103/2)` and `R=sqrt(1672/1295)-1>0`. It satisfies N=0 and the odd
constraint; its even determinant is exactly 103/9. It is not offered as a
solution of either full norm or full force. The
[independent rational-polynomial replay](norm-arithmetic-independent-05.py)
pins its source definitions by SHA-256, obtains the complete odd identity as
a zero polynomial, and checks the witness without numerical square roots.

## GAC:r2-phase-transfer — approve

The capital phase inputs are exactly

    zeta=1-a+i*gamma,
    P=(1+R)(1-iq)(1-zeta), Q=1+iq-2iq*conj(zeta).

They are distinct from the lowercase row coefficient p. Direct product
expansion gives both the literal determinant `normSq(P)-normSq(Q)=Delta`
and numerator `conj(P)L-Q*conj(L)=T`. In particular the Q gamma sign and
the resulting `+4q*gamma` determinant term are retained.

The auxiliary inverse treats arbitrary complex P,Q,V,C. With the real
determinant nonzero it proves both directions of

    P*V+Q*conj(V)=C
      iff V=(conj(P)*C-Q*conj(C))/(normSq(P)-normSq(Q)).

Specializing the actual real H and C=-2HL gives Vreg=-2HT/Delta. Either
nonzero determinant sign is allowed. The proof selects no gamma sign,
square-root convention or handedness.

Under K²=s and KH=h, the identity h²=sH² is exact. K!=0 supplies s!=0;
Delta!=0 supplies the nonzero squared denominator. Those are precisely the
guards used to prove `normSq(Vreg)=R*(3-s)` iff F=0. Squaring a phase sign
does not replace the original phase equation: that equation has already
been solved by the real-linear inverse.

The last conjunct combines the original phase equation, its norm equation
and `traceResidual=0` iff V=Vreg, F=0 and J=0. It retains K²=s, KH=h,
K!=0 and every explicit s,D,E,Delta clearing guard. `traceResidual` is the
unmultiplied affine trace on the phase/norm locus from the accepted source.
The theorem does not identify it with a complete off-locus original force.

Positive examples include an invertible elementary real-linear equation and
the original positive normal point a=1,gamma=1/6,s=3/2,R=1, with
K=sqrt(s), H=h/K. The latter meets all clearing guards and satisfies the
actual original phase equation at Vreg. No norm or full-force feasibility
is attributed to that example.

## Validation and retained scope

The independent full warnings-as-failures build, both generated reports,
both status checks, identity/tree check, existing certificate checks, R2
certificate replay, independent norm arithmetic and separate R2NormChart /
R2PhaseTransfer kernel replays passed. Both tagged proofs have their exact
tagged target and only allowed axioms. Both approved-surface drift checks
are clear; the 75 earlier manifest entries remain unchanged.

These results strengthen the existing regular reduced R2 system. The original
normal cubic reconstruction, zero-K, singular-phase/H=0 and zero-radius
sectors, unnormalized problems, full coframe/connection/frame/link/history
compatibility and physical phase selection retain their original external or
open scopes. Nonzero-pivot force feasibility, a global candidate count,
R7/R8 completion and a full quantum-gravity parent are not established here.
