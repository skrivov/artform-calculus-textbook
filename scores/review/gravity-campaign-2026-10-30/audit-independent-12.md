# Independent gauge-volume, scalar and finite-loop review, 30 October 2026

Reviewed freeze: ef731bfed4e627df07b67a14f212557cb515f381.
Reviewer: the distinct `gravity_fidelity_review_01` agent, which authored none
of the fifteen submitted modules. No implementation or earlier approval was
changed; all 104 previous approvals stand.

**Verdict: approve all five claims; return none.** They provide a singular
Gaussian test, a proposed scalar addition and a specified finite Euclidean
regulator/loop calculation. They add **zero material native applications**.
The accepted campaign application count remains one. The candidate addition
has not become an accepted native matter/clock law.

See [per-key verdicts](verdict-independent-12.json),
[independent validation](validation-independent-12.json) and
[exact regulator replay](regulator-arithmetic-independent-12.py).
The review compared all five literal manifest quotations with ledger section 7,
findings 142–146, all fifteen modules, each positive/adverse example and the
actual source, measure, pair-counting and normalization definitions.

## GAC:gaussian-gauge-volume — approve

The function is exactly exp(-(q²+epsilon*g²)) on the real plane, with its
actual product Lebesgue measure. Full-plane integrability at epsilon=0 is
explicitly disproved: Fubini's almost-everywhere slice implication would make
an everywhere nonzero constant integrable on an infinite-volume g line.
The proof does not treat the totalized Bochner integral of a divergent
function as a physical amplitude.

The g=0 slice is a separate integrable function with integral sqrt(pi).
For epsilon>0 both one-dimensional Gaussian factors are integrable, and the
actual product integral is sqrt(pi)*sqrt(pi/epsilon). Regulator one gives pi,
regulator four gives pi/2, and their difference is strictly proved. The
positive example includes an integrable regulated plane and a nonintegrable
unfixed plane, so neither assertion has empty hypotheses.

A slice, a regulated plane and an unfixed plane are different declared
amplitudes. No compensated quotient measure or Faddeev-Popov/gauge-group
construction follows. The native physical radical, support, Lorentzian
prescription and refinement measure remain unidentified. Neither the earlier
binary phase pilot nor M166's accepted selected-band state fills that gap.

## GAC:scalar-coframe-candidate — approve

This is an explicit proposed addition, preserving the frozen native action.
The actual diagonal coframe determinant is N*a³; for nonzero N,a, the displayed
diagonal inverse is checked on both sides. The component frame gradient is
the corresponding inverse action. The density has the chosen overall minus
sign against eta=(-+++), giving positive temporal kinetic coefficient when
N,a,lambda are positive and the stated negative spatial coefficient.
This conventional sign is specified, not derived from the native gravity law.
A positive temporal coefficient alone is not a physical-energy theorem.

The finite rational 5/3,4/3 boost is nontrivial, preserves the full displayed
Minkowski quadratic form and preserves the unit-chart density with scalar and
source unchanged. It does not keep a general coframe inside the diagonal
chart or establish full local Lorentz covariance. The non-unit example
N=2,a=3,lambda=7,phi=5,j=11,d=(1,2,0,0) gives -367/4, and the boosted unit
temporal input has Minkowski norm -1.

The exact variation holds for every rational epsilon, scalar variation v
and difference-coordinate variation e. It retains the full source covector
and quadratic remainder. For a lattice scalar equation e must subsequently
be the incidence difference of the same v, with endpoint data retained.
The nonzero chart conditions remain necessary for the inverse/coframe
interpretation even where rational identities have algebraic zero-division
extensions. No varying/native coupled40 matter law, backreaction solution,
calibration or selected Newton coefficient is obtained here.

## GAC:clock-coupling-response — approve

The temporal two-edge action is explicit and actually varies its shared
scalar value. Its first coefficient is

    (-lambda*a³*(next-2*current+prev)/N-j)*v,

with quadratic remainder epsilon²*lambda*a³*v²/N. This agrees with the
incoming/outgoing signs of the source -j*current. The declared force is
-lambda*a³*Delta2(phi)/N. Quadratic clocks have Delta2=2*acceleration at every
integer site, so the exact response retains that factor two and sign.

The affine clock has the specified values at zero and one and source-free
scalar force for every coefficient. Distinct positive couplings one and
seven satisfy that same normalized affine scalar equation, while the unit
quadratic clock at coupling seven has force -14. These examples do not
construct two completed coupled gravity solutions or select a Newton constant.

Calibration N->c*N retains nonzero c and divides the temporal weight by c.
No dimensionless coordinate step is silently given continuum units. The real
HasDerivAt proof gives d[lambda/(2N)]/dN at one equal to -lambda/2. For nonzero
lambda that lapse variation is nonzero even though the affine scalar force
vanishes. Scalar stationarity therefore does not supply coframe stationarity
or justify keeping the old gravity vacuum without a backreaction argument.

## GAC:finite-regulator-symmetry — approve

The class contains exactly four diagonal and six mixed rational homogeneous
quadratic coefficients. Independent reflections isolate every mixed term;
the two generating spatial swaps force a1=a2=a3. The converse is also proved,
leaving a0 independent. The anisotropic diagonal (2,1,1,1) is a positive
nontrivial member. This is not a classification of all operators/interactions
or a proof of native Lorentz symmetry.

The sixteen sites are genuinely (Z/2)^4 with XOR shifts. The Walsh entries
are chi_k(x)/4, including the normalization for sixteen sites. Kernel-checked
orthogonality, all four difference Grams and all four parity-source Grams
are direct identities of these finite sums. The local precision has mass
one, temporal difference weight ct/4 and spatial weights cs/4, so its diagonal
is exactly 1+ct*bit0+cs*sum_spatial bit. The source Gram couples only k with
k xor 2^i. An action prefactor s/2 then combines its two off-diagonal entries
into cross term s*u*v, exactly the precision block [[A,s],[s,B]] used later.
No exported response coefficient substitutes for this source identification.

For each axis the bit-zero representatives have cardinal eight and uniquely
partition all sixteen sites into distinct pairs. The selected A(k)>=1 bound
and reciprocal half count are proved. Generic spatial responses agree; at
ct=2,cs=1 the actual full responses are 19/10 and 34/15. These are finite
axis-mode responses, not infinitesimal-momentum limiting speeds.

The separate stdlib rational replay checks 256 orthogonality entries, 1024
source-Gram entries, 1024 difference-Gram entries and 256 coefficient triples
for the arbitrary-ct/cs precision. It independently verifies the eight-pair
partition, source half factor, generic spatial-response term multisets and
reciprocal half count. Temporal pair weights have multiplicities
3:1,8:3,15:3,24:1; spatial weights have 2:1,6:2,12:2,20:2,30:1.
The reciprocal sums are 19/20 and 17/15, exactly half the full responses.

## GAC:finite-gaussian-loop — approve

The pair density is exactly exp(-(A*u²+2*s*u*v+B*v²)/2). B>0 and positive
AB-s² imply a positive Schur coefficient c=(AB-s²)/(2B). The proof first
establishes integrability of every eliminated slice, then of the actual
norm integral on the other line, with measurability and positivity explicit.
Thus Fubini yields genuine full-plane integrability and its full factor
sqrt(pi/c)*sqrt(pi/(B/2)); it is not just a formal iterated integral.

At zero source the positive baseline is also proved. Positivity/nonzero
facts precede all logarithm and ratio manipulations, giving
log(Z_s/Z_0)=-log(1-s²/(AB))/2 with every normalization retained.
The finite-family theorem constructs integrability on the actual product
of real planes and proves the actual product integral and logarithmic ratio.
It is not a determinant assigned without a measure or convergence proof.

The elementary logarithm bound is valid for x<=1/2, with 1-x>0 retained.
For w>=1 and theta in [0,1/2], termwise bounds and the finite absolute-sum
inequality give card(I)*theta². In the regulator, theta=s² and every pair
weight is at least one, so the strict determinant window follows. The paired
measure is explicitly Lebesgue in the declared normal coordinates. The
Walsh/source matrix algebra is checked, but no full native or physical
change-of-variables theorem is inserted.

Gamma is minus the log of the actual normalized partition. There are eight
pairs while R sums all sixteen labels, hence

    C_i=-(1/2)*sum_pairs(1/(A*B))=-R_i/4.

The sign and both factors of two agree with the actual density and partition.
The error is <=8*s^4 for s²<=1/2. The exact coefficients are -19/40 and
-17/30 with gap 11/120; the temporal s=1/10 example has error <=1/1250.
The independent rational replay verifies those constants as well.
The gap concerns these quadratic background-response coefficients. It is
not an assertion of unequal continuum limiting speeds or every nonzero-
amplitude full free energy.

The heavy regulator is Euclidean and positive in this window. The background
phi is external with s=g*epsilon. No integration over arbitrary phi is
performed, and no stable global joint cubic-interaction measure is claimed.
The chosen matter/clock candidate has not been matched to this regulator's
physical measure, symmetry, source or gauge/constraint class.

## Motivation, validation and remaining transfer

The reviewer independently checked the primary abstract of
[Collins and coauthors](https://arxiv.org/abs/gr-qc/0403053). It motivates the
preferred-frame radiative question; it is not a Lean premise and supplies
none of this finite model's coefficients or a native coupling conclusion.

The independent full warnings-as-failures build, both reports, both status
checks, identity/tree check, all certificate checks, both empty drift checks
and five separate kernel replays passed. Every proof has its exact tagged
target and only allowed axioms. Every actual example, analytic convergence
guard, source/measure and pair factor was inspected; the exact rational replay
independently confirms the finite Grams, responses and coefficients.
All 104 previous manifest entries and all fifteen submitted modules remain
unchanged by this review. Native gauge volume/measure, matter and clock
selection, backreaction and full40 compatibility, regulator/symmetry/source
identification, actual physical change of variables and continuum/low-momentum
limits remain open. No universal native protection, Newton coupling or
full-parent quantization theorem is credited.
