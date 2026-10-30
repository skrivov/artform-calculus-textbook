# R7/R8: explicit temporal coordinate forcing and failure of selected TT time invariance — UNREVIEWED

ROOT manual candidate, M162, 30 October2026. Previous turn PROGRESS. Current M161 MAIN and qualified finite-N increment were authenticated88b3fc; fresh whole POSTb2effa passed on the same live handle88831. Source calculation0/description0/preparation0 at freeze. All mathematics below is manual. ROOT reported the possible mixed forcing and invariance test to Sol before freeze; that orientation is not a distinct review.

The new conclusion is a failure of invariance of two particular selected TT solution families, not a failure of the native equations or of the accepted strong symplectic form. No physical degree count, energy sign or quantum impossibility follows.

## 1. Original formulas and the actual question

Use the original physical coframe/connection, metric m=eta f+(eta f)^T, eta=(-+++), kappa=1/101 and a=1+2kappa. The native source a5570827 was freshly read7e1bc5; it gives
Z_ij^I=(partial_i-partial_j)Gamma_ij^I(m)/2,
Q=(M-2kappa M Tc B^-1 Tc^dagger M)Z,
delta q2_eff=-G^(2),mu nu delta m_mu nu/2+2kappa sum_(i<j) Q_ij,I Z_ij^I(delta m).
M is the original signed unordered-face covector pairing and B the full native connection Hessian. Its original leading derivation74fbfb6a was freshly read80a65f. Centered curvature a3f59c8f was freshly readf482ab, and the original actual coordinate map589b8b7d was freshly readce6a9a.

For a leading pure coordinate metric D0 chi, Gamma_ij^I=partial_i partial_j chi^I. Here chi is LOWER, so chi^0=-chi_0. The complete compact coordinate force on a leading homogeneous field is
C_TT=2kappa (R1 eta)^dagger Q,
(R1 chi^upper)_ij^I=(partial_i-partial_j)partial_i partial_j chi^I/2. (1)
The curvature contribution is zero on a leading TT wave. One may derive this either from the native centered displacement identity in a3f59c8f, or directly from the derivative-replaced Einstein quadratic: its exact centered gauge identity E(d_h)D(d_h)=0 gives E_C,2 D0+E0 D2=0. Taking its actual incoming transpose and applying it to E0 m_TT=0 gives D0^dagger E_C,2 m_TT=0. This argument retains the centering contacts until the leading equation is used. It does not replace the full order2 source by torsion off orbit.

The accepted slow family has actual twenty trace coordinates (t,t_t,chi,chi_t,chi_tt,chi_ttt) at the initial cut. Its leading equations, in the same LOWER basis, are
t_tt+rho² t=0,
G2(partial_t)chi=-(C0+C1 partial_t)t.                       (2)
For normalized zero coordinate jets0..3, G4 chi4=-(C0 q+2C1 p). The matrices C0,C1 are the mixed forcing reduced modulo the TT wave equation; evaluating(1) on the actual unflowed TT wave computes that right-side input. The ACTUAL leading solution includes the resulting coordinate response. We do not substitute an unflowed TT wave for the normalized solution when computing its later source time derivatives.

The full slow source eec52c84, mandatory01c258f6 and lower-basis0a10194b were completely read in M16110d66e/bb83e5/5d715f and are explicitly reused. The native selected symplectic source acb95d61 was freshly read7a0bb6. The actual finite-N trace source07a2abb9 was freshly read086f54 and has ROOT's published distinct review1fe42b76. Earlier source titles retain their historical UNREVIEWED wording; acceptance is limited to their separately recorded reviewed ledger scope.

## 2. A spatial-face cancellation in the actual signed distinct block

Take an unflowed TT wave with m00=m0i=0, spatial trace/divergence zero, m_sp(0)=q and partial_t m_sp(0)=0. Fix two distinct spatial indices i,j. The only face/internal coordinates in the distinct triple(0,i,j) are
A=Z_0i^j, Bv=Z_0j^i, C=Z_ij^0.
At the initial cut the literal Christoffel formula gives
A=Bv=partial_t² m_ij/4=:z, C=0.                          (3)
The first equality uses the zero velocity field and its spatial derivatives. It is not a general all-time equality.

To check the original signs without an invariant-vector substitution, choose connection coordinates
c0=x(t_i wedge t_j), ci=y(t_j wedge t0), cj=zeta(t0 wedge t_i).
Their torsion triple is
Tc(x,y,zeta)=(y-x, x-zeta, -y-zeta).
In this face/internal basis M=-I3. Write v=(1,-1,-1). Direct multiplication gives Tc^dagger M Tc=-(I+v v^T). The original curvature commutators contribute q_C=-xy-x zeta+y zeta, hence B_C=v v^T-I. For example their face commutators are -xy(t0 wedge t_i), -x zeta(t0 wedge t_j), and +y zeta(t_i wedge t_j), with the actual complementary epsilon/star pairings. Thus
B= -[a I+(2kappa-1)v v^T].                              (4)
This is the signed/permuted native distinct block, derived here in the displayed coordinates.

On Z=(z,z,0), r=Tc^dagger MZ=(0,-z,z) has v^T r=0. Hence B^-1 r=-r/a, Tc B^-1 r=(z/a,z/a,0), and
Q=(-z/a,-z/a,0).
In particular
Q_ij,0(0)=0 for every spatial pair i<j.                  (5)
All spatial derivatives of this equality also vanish on the initial slice. No assumption about a missing spatial face or a positive face metric was made.

## 3. Explicit nonzero mixed temporal force

For a lower temporal coordinate test alone, Z_ij^0(D0 chi)=-(partial_i-partial_j)partial_i partial_j chi_0/2. It contains three derivatives, whose formal transpose has negative sign. Equation(1) therefore gives the LOWER temporal force
(C_TT)_0=kappa sum_(i<j)(partial_i-partial_j)partial_i partial_j Q_ij,0. (6)
At the zero-velocity cut the spatial-pair terms vanish by(5). The remaining terms are
kappa sum_i (partial_t-partial_i)partial_t partial_i Q_0i,0.
The actual repeated-block source formula in a5570827 gives, for the unflowed TT wave,
Q_0i,0=kappa partial_i L_diag/[4a(1-kappa)],
L_diag=sum_j partial_j m_jj.                             (7)
Its first time derivative vanishes at the selected cut. Since the TT wave obeys partial_t² m_sp=Delta_sp m_sp, (6)-(7) give
(C_TT)_0(0)=Delta_sp² L_diag(0)/41200.                    (8)
Here kappa²/[4a(1-kappa)]=1/41200. Spatial-face cancellation was essential: (8) was not inferred from the scalar normal source F alone.

In the accepted all-direction coordinate operator, the temporal entry of G4 is kappa rho² Hrep/2, Hrep=10201/10300, with no temporal/spatial off-diagonal entries. Consequently the ACTUAL normalized leading coordinate response has
chi_0^(4)(0)=Delta_sp L_diag(0)/202.                      (9)
In Fourier variables this is -i rho² sum_j k_j q_jj/202. This is a LOWER-coordinate formula; the upper temporal component has the opposite sign. No free fourth jet was assigned.

For a concrete admitted three-dimensional direction, use k=(1,2,3), p=0,
q=a0 a0^T-b0 b0^T,
a0=(2,-1,0)/sqrt5, b0=(3,6,-5)/sqrt70.
The two vectors are unit, orthogonal and perpendicular to k. The diagonal of q is(47,-22,-25)/70, so sum_j k_j q_jj=-36/35 and rho²=14. Equations(8)-(9) give respectively -i63/12875 and +i36/505, both nonzero. Rescale k into the interior of any specified nonzero annulus, extend the TT polarization smoothly on a small angular/radial patch and reflect it evenly. A real smooth compact spectral amplitude on this patch and its reflection gives an admitted real centrally-even Schwartz TT geometry packet. The symbol remains nonzero on an open subpatch. The resulting temporal coordinate jet is real in position space but need not be even. This is a genuine packet, not an axis mode multiplied by an envelope.

## 4. Exact native slow time translation and a concrete invariance test

Let S_h be the exact twenty-trace solution map into the fixed native Lorentz slice, with T S_h=I. The whole20-root principal-part space is preserved by time translation and by partial_t: a derivative multiplies its contour amplitude by lambda and changes neither the exact characteristic set nor its finite principal-part class. Define
A_h=T partial_t S_h.                                    (10)
Then partial_t S_h=S_h A_h by the trace isomorphism and completeness of that slow space. Translation by tau is consequently S_h exp(tau A_h), including exact native one-step translation tau=h. The contour formulas and their removable h expansion prove A_h is bounded and holomorphic for small h on each compact frequency patch and converges to the mixed second/fourth-order companion matrix of(2). No uniqueness claim for the FULL native history problem or exclusion of fast roots is used.

Use data y=(q,v) with v=2p solely to make the TT trace embedding E:y->(q,v,0,0,0,0) satisfy Q_TT E=I. This constant input reparametrization does not change the native force/current normalization.

For the zero-total-Coulomb TT family, the trace image is im E. Its infinitesimal invariance defect is
D_h=(I-E Q_TT)A_h E.                                    (11)
At h=0 on the packet above, its last lower temporal-coordinate component is precisely chi_0^(4)(0) from(9), hence nonzero. Uniform contour convergence implies D_h stays nonzero on that fixed packet for all sufficiently small positive h. Thus this selected family is not closed under actual time translations. More specifically,
(I-E Q_TT)exp(h A_h)E y=h D_0 y+O(h²),                    (12)
so it is not even invariant under one native lattice time step. All remainders are in the fixed-band finite data norm, uniformly on the chosen packet. The example already fails invariance in the larger Fourier-real TT data space, so no conclusion is being driven merely by restricting inputs to central evenness.

## 5. The actual finite-N trace correction does not remove this defect

For each separately fixed N, write G_N(h)=T U_N(h) as a linear map from y=(q,v) into twenty trace coordinates, with the actual finite constructor and all its lower adjustments. Its leading value is E. The accepted finite-N comparison gives the exact metric slow trajectory S_h G_N(h)y; a copied exact Lorentz profile does not change these metric traces.

Q_TT G_N(h)->I, so it is invertible for sufficiently small h. Define the bounded projection
P_N(h)=G_N(h)[Q_TT G_N(h)]^-1 Q_TT.                       (13)
Its image is exactly the actual finite-N selected TT trace image and P_N->E Q_TT. Its invariance defect is
D_N(h)=(I-P_N(h))A_h G_N(h).
On the same fixed packet D_N(h)->D_0 y!=0. Since (I-P_N)G_N=0 exactly and A_h remains uniformly bounded,
(I-P_N)exp(h A_h)G_N y=h D_0 y+O(h²).                    (14)
For each fixed N this also disproves one-step invariance at all sufficiently small positive h, even though this family matches the actual formal physical coefficients to the accepted finite order. Constants and the small-h threshold can depend on N. No common-N statement is inferred.

The metric trace defect is unchanged by any native Lorentz representative adjustment. There is no exact native displacement Ward symmetry in the accepted premises that would make this defect automatically zero in a physical quotient.

## 6. Consequence and limits

The accepted native current remains exactly conserved between any two exact solutions, and its pullback on the selected TT data remains strongly nondegenerate. The present result says those selected solution images are not invariant under the native time-translation flow. Therefore the accepted symplecticity theorem alone does not supply an autonomous restriction of that flow or an invariant quantum dynamics on that selected TT data space. A projected Hamiltonian, if introduced, would require a separate justification that it reproduces the physical native evolution.

This does not rule out a larger invariant solution space, a different trace embedding with a different limit, an appropriately proved physical quotient, a boundary prescription tied to one distinguished initial surface, or a full gravitational parent. The twenty slow roots are still algebraic roots rather than a physical mode count. Full physical cut/range matching, energy, nonlinear amplitudes, all-order convergence and quantum state/representation remain open. R2's guarded real feasibility and all other routes remain active.

Distinct review must verify the signed distinct-block calculation(3)-(5), the lower temporal sign and spatial-face omission test in(6)-(8), normalization202 in(9), admitted packet, and both exact/limiting invariance arguments(10)-(14). ROOT self-read is custody only. No result here is accepted until the distinct review and publication checks complete.
