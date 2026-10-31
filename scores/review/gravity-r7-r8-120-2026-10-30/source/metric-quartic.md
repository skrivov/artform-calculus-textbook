# Actual quartic longitudinal scalar and patchwise full metric Cauchy-cut solve — OPEN

Manual first-seed derivation,30 October2026, own completed M157/1137 cutoff. Later reviewed research notifications are not new author intake. This source calculation0/description0/receiver0; the preceding literal-reception preparation1 belongs separately to the62d3 family, not a new incident. No scientific evaluator, new agent or live owned handle. Broad quartic/elimination orientation and an unfrozen provisional formula were disclosed to ROOT. Distinct finished-byte review is required.

## 1. Precisely the original map and the claim

Use frozen62d36f20 WITH da8912f8, and separate cubic6544a4cc. Their originals are full40 native183dbf93, actual normal source a5570827 WITH6c2dafaf, full constant-coordinate aae563c8 WITH its original qualifications, all-twenty slow map eec52c84 WITH lower0a10194b, and eaa5e9b0 WITH7533 and initial-only-T correction cb440bb2. Original coframe Schur74ba85a5 WITH4f79a845 supplies the finite coefficients below. Do not identify total-coframe Coulomb chi and constructor Phi.

Keep TT(q,2p), copy the original full coframe Lorentz profile by the EXACT native column, retain all40 equations and its independent connection. After the twelve visible metric-Cauchy rows are solved, the four remaining rows are the original leading Einstein Hamiltonian and three momentum constraints. Frozen62d3 defines their exact residual matrix K_h, its h² rank3 part, and the last scalar
 D_h=d_h-c_h A_h^-1 b_h.                                 (1)
A_h is the Hamiltonian/transverse-momentum block; b_h,c_h,d_h are its longitudinal off-diagonal and scalar blocks. Both the visible12 Schur product and the top3 product in(1) must be kept. The cubic additive gives D_h=O(h4), not exact rank3.

Set
 kappa=1/101, alpha=103/101, A=1/alpha=101/103, g=101/97,
 E=202/9991=2kappa A g, Hd=9999/9991=A+E,
 D=10201/10300=1/[alpha(1-kappa)],
 beta=-1/12+kappa(Hd+E)/4=-2422/(3*9991).                (2)
For real k put rho=|k|, P=I-kk^T/rho² and v=P k^[2], where k^[2]=(k1²,k2²,k3²). The new result is
 D_h=h4 d4+O(h5), d4=-C_* |v|²,
 C_*=kappa[Hd+(kappa A²+E)(Hd-D)/Hd]/12
                                  +kappa^4 g² A²/(4beta),
 C_*>kappa/24>0.                                        (3)
The proof below is all-direction, with true componentwise native spatial derivatives. This is not a rotation of the stencil.

## 2. An original signed distinct block and its H1/H2 coefficients

Write d_i=i k_i and lambda=partial_t. For a spatial pair i<j put p=d_i,q=d_j. Use connection columns
 omega0=x(t_i wedge t_j), omega_i=y(t0 wedge t_j), omega_j=z(t0 wedge t_i),
and face rows (Z0i^j,Z0j^i,Zij^0). The literal original Lorentz action gives
 Tc=C=[[-1,-1,0],[1,0,-1],[0,1,-1]], M=-I.
The three constant-coframe curvature brackets contribute respectively xy,-xz,-yz to the original quadratic, hence
 Bc=vv^T-I, v=(1,1,-1), B=-(alpha I+(2kappa-1)vv^T).
Here v in this paragraph is a connection three-vector, not P k^[2]. With w=(1,-1,-1), C v=-2w and C C^T=I+ww^T. This checks the spatial-face and electric covector signs directly from original183dbf93, rather than from a renamed invariant output.

Let Dlink=diag(lambda,p,q)/2. On this block m^-1=I+hDlink+O(h3), (m^-1)^dagger=I-hDlink+O(h3). Woodbury applied to the ORIGINAL full B_h in74ba(1) gives the signed face inverse
 N_h=H_h^-1=-I+2kappa C m^-1 Bc^-1(m^-1)^dagger C^T,
 Bc^-1=-I+vv^T/2, H0=-A I-Eww^T.                       (4)
This inverse is only on the original bounded temporal disk; no all-frequency averaging inverse is introduced. Put a=(-1,1,0), b=(-1,0,1), c=(0,-1,-1), L=lambda a+p b-q c. The exact coefficients through2 are
 N1=kappa(w L^T-L w^T),
 N2=(kappa/2)(lambda²aa^T+p²bb^T+q²cc^T)
                                  -(kappa/4)LL^T,
 H1=-H0 N1 H0,
 H2=H0 N1 H0 N1 H0-H0 N2 H0.                            (5)
No products commute. In particular the full H1 matrix is
 kappa g A [[0,p-q,lambda-q],[q-p,0,p-lambda],[q-lambda,lambda-p,0]]. (6)

For a checkable minimal H2 table put C2=kappa² A² g and e+=(1,1,0). Denoting coefficient extraction by brackets, direct multiplication in(5) gives
 ([lambda²]H2 x)_3=C2(x1-x2), x3=0,
 ([lambda p]H2 e+)_3=C2,
 ([lambda q]H2 e+)_3=-C2.                               (7)
For completeness the two terms in the first line of(7) are -2kappa² A g E(x1-x2) and -kappa E(g-E)(x1-x2)/2 before their subtraction; their difference is kappa A E(x1-x2)/2=C2(x1-x2). In the lambda p line the two terms are2C2 and C2; in lambda q they are-2C2 and-C2. Thus(7) includes both orders of the inverse/centering returns, not just a principal H2 approximation.

## 3. The cubic off-diagonal rows and their signs

Take the leading remaining coordinate input chi_sp,3=d phi, chi0,3=0, with all chi jets0..2 zero and TT zero. For unit longitudinal coordinate a=n.chi_sp,3, n=k/rho, phi=a/(i rho). Then Z1=0 atcut, while (Z1_0i^a)_t=d_i chi_a,3/2. The common-time repeated H1 diagonal terms cancel between the TWO electric incoming sums of the normal vector row; the spatial-face cut term is zero for this symmetric electric input. Formula(6) gives
 (H1 Z1)_0i,a,t-(H1 Z1)_0a,i,t
                    =kappa g A d_i d_a(d_i-d_a)phi.
Original a557(6), with its symmetric metric-slot factor kappa/2, therefore yields
 J3=-(kappa² g A/2)(d s3-d^[2] Delta)phi,
 F3=0, Delta=sum d_i², s_j=sum d_i^j.                   (8)
The scalar vanishes by the separate original repeated/distinct index blocks, not by dropping a temporal entry.

For a general spatial third jet c, the temporal part of(6) gives
 (H1 Z1)_ij,0|cut=-(kappa g A/2)(d_i c_j-d_j c_i).
The original longitudinal normal test has Z1 electric identically zero and Z1_ij^0=-(d_i-d_j)d_i d_j phi_test/2. Hence its incoming spatial transpose gives
 div J3=-(kappa² g A/2)[s3 V1(c)-Delta V2(c)],
 Vj(c)=sum_i d_i^j c_i.                                 (9)
There is no temporal-third-jet contribution to this left row. Converting both sides to the SAME real unit vector n=k/rho, (8)-(9) show explicitly
 b3=-i kappa² g A rho v/2, c3=b3^T,                       (10)
where b3 is transverse and the transpose is BILINEAR, not Hermitian conjugation. Fourier reflection supplies reality; replacing c3 by a conjugate would change the quartic sign. Since A2=-beta rho² on the transverse block,
 c3 A2^-1 b3=kappa^4 g² A² |v|²/(4beta).                 (11)
This is the full top-three elimination product entering(1).

## 4. Retaining the visible12 return without unknown Cauchy data

Solve the twelve visible rows at each h, retaining the pure longitudinal input at order0. At order2, K2 annihilates that input. Thus the entire order2 metric Cauchy coefficient m2 after this visible elimination is ZERO (TT pair is also zero), not only its lapse. It obeys the original leading equation G(m2)=Sigma2[m0], where Sigma2 is the a557 original graph source. Unknown first-order zero-T homogeneous coefficients contribute no metric source through E1=0; their normal E2 cut values depend only on chi jets through3. Nothing here sets those fields identically zero.

For ANY m with full metric Cauchy data zero, the literal a557(5) gives
 div G0sp^(2)[m]|cut=partial_t³ G00[m]/6.
Its torsion longitudinal normal term is zero: Z1 atcut is only the SYMMETRIC electric matrix m_sp,tt/4, and H0 maps that matrix to zero spatial-two-form/internal0. Therefore
 div Sigma2[m2]|cut=-partial_t³ F2[m0]/6.                (12)
This identity incorporates C_s,2 V0^-1 V_c,2 in the quartic normal block; it is NOT permission to discard the visible Schur product. It uses the enforced full Cauchy zero and the inhomogeneous leading constraint G00[m2]=F2[m0]. Unknown added invisible order2 coordinate jets do not alter(12).

The E3 source on an order1 homogeneous field depends at the cut only on its third coordinate jet; its zero-T part has none. The order1 top-three jet chosen to cancel b3 is -A2^-1 b3. Its contribution is precisely minus(11). Thus every lower homogeneous/coframe/connection return at order4 is either in(12), in(11), or zero by its proved initial jet value.

## 5. The actual leading coordinate recurrence and F2,ttt

Define T=Delta s4-s3² and W(chi)=Delta V2(chi_sp)-s3 V1(chi_sp), U(chi)=s4 V1(chi_sp)-s3 V2(chi_sp). These are symbols, not new freely chosen moments. Direct substitution m=D0chi into original a557(5),(8) yields
 F2=-(Delta V3-s4 V1)/6
 +(kappa D/2)(Delta chi0,ttt-2s3 chi0,tt+s4 chi0,t)
                         -(kappa² D/2)(partial_t W+U). (13)
In the temporal coordinate compatibility F2,t-div J2=0, the curvature terms cancel directly. The original full G2=D0^dagger(J2+J1Y)D0 therefore gives
 D(Delta chi0,4-2s3 chi0,3+s4 chi0,2)-Hd T chi0
                          +(E-kappa D)(W_tt+U_t)=0.    (14)
This is the actual leading coordinate equation, not an assumed exact finite-h displacement Ward identity. The off-orbit lower-adjoint and centering returns have already been retained as in a557 with6c2; leading lower residuals vanish before(14) is used.

For the initial longitudinal third jet d phi, (14) implies chi0,4=chi0,5=0, since W(d phi)=0, and
 D Delta chi0,6=-(E-kappa D)[W(chi_sp,4)+T phi].
Consequently(13) gives
 F2,ttt=-(kappa E/2)[W4+T phi], W4=W(chi_sp,4).          (15)
All these are ORIGINAL normalized leading higher jets; they are not unflowed TT substitutes.

The spatial cubic/quartic coordinate coefficients can also be read directly from the original2kappa R^dagger H0R electric contraction. Its electric r_i=d_i(lambda²-d_i lambda)/2 and original incoming transpose give
 G4,sp=(kappa/2)[Hd Delta I-(Hd-D)dd^T],
 G3,sp=(kappa/2)[-2Hd s3 I+(Hd-D)(d^[2]d^T+d(d^[2])^T)]. (16)
The initial chi0 third jet is zero; all lower coordinate jets are zero. Thus G4 chi_sp,4=-G3 d phi, retaining its longitudinal eigenvalue D Delta as well as its transverse Hd Delta. Explicitly
 chi_sp,4={2s3 d/Delta-(Hd-D)[d^[2]-(s3/Delta)d]/Hd}phi,
 W4=-(Hd-D)T phi/Hd.                                   (17)
This verifies all dependent jets used in(15) without treating W4 as free.

## 6. The complete E4 normal divergence, including the cubic test

Use the ORIGINAL finite-word entry convention from74ba(5), returned to the original coframe:
 Z3_ij^I=(d_i-d_j)Gamma2_ij^I/2-(d_i³-d_j³)Gamma0_ij^I/24,
 Gamma2_ij^I=eta^(I mu)(d_i³ m_mu j+d_j³ m_mu i-d_mu³ mij)/12. (18)
For the input above, in one pair p=d_i,q=d_j,
 (Z3)_ij^0=pq(p-q)phi/12,
 (Z3)_0i^j-(Z3)_0j^i=(q chi_i,4-p chi_j,4)/24-pq(p-q)phi/12.
Combining these with the full H0 signed block gives
 (H0 Z3)_ij,0=E(q chi_i,4-p chi_j,4)/24
                                      -(Hd+E)pq(p-q)phi/12.
Using(7), including both its mixed terms, gives
 (H2 Z1)_ij,0=(C2/2)(p chi_j,4-q chi_i,4).
Since E/24-C2/2=kappa A²/12, their sum is
 Q*_ij,0=kappa A²(q chi_i,4-p chi_j,4)/12
                                      -(Hd+E)pq(p-q)phi/12. (19)

The independent Z3 TEST term is retained as well. For delta m0i=d_i phi_test, its spatial-internal0 entry is p²q²(p-q)phi_test/24 and its electric entries are pq(p²-q²)(lambda-p)phi_test/24 and their swapped partner. Atcut H0 Z1=0, so only the incoming temporal derivative of those electric entries can contribute. Its field derivative H0(Z1_t) is symmetric electric, while the pair of electric test coefficients is antisymmetric. Their sum is exactly zero. This is a checked cubic-test cancellation, not its omission.

The centered-curvature E_C,4 divergence is also zero here: its cut expression is [Delta V3(c)-s4 V1(c)]/72 plus a transverse fifth-jet curl whose divergence is zero; c=d phi makes the first bracket zero. Therefore the COMPLETE order4 source divergence is
 div Sigma4[m0]=kappa² A² W4/12-kappa(Hd+E)T phi/12.      (20)
Applying(12),(15) to the visible-return-corrected coefficient gives
 div K4,visible=kappa[(kappa A²+E)W4-Hd T phi]/12.
Now insert(17), and convert div/(i rho) and phi=a/(i rho). Since T=-rho²|v|², the raw scalar after the visible12 elimination is
 -kappa[Hd+(kappa A²+E)(Hd-D)/Hd]|v|²/12.                (21)
Subtracting(11) proves exactly(3), with BOTH elimination products and all required lower fields included.

## 7. Nonzero patch and exact one-cut metric solvability

A<1,g<2,Hd>1,D<1,E>0 and |beta|>1/13. Thus the negative second term in C_* has absolute value less than13kappa^4<kappa/24, while its first term exceeds kappa/12. This proves C_*>kappa/24 by exact rational inequalities; no sign is inferred from a sample or a numerical evaluation.

For real nonzero k, v=0 exactly when every nonzero component of k has the SAME value. These are fourteen rays (one nonempty coordinate subset and either sign). No conclusion is obtained on those rays. On any fixed compact annular patch and its reflection with |P k^[2]|>=nu>0, (3) gives |D_h^-1|<=C|h|^-4 for sufficiently small nonzero h, uniformly with each fixed k derivative. The normalized D_h/h4 is holomorphic and uniformly invertible on a smaller complex-h disk. Original top3 inverse has only h^-2 loss and visible12 inverse is bounded.

Hence the exact metric Cauchy map with TT pair fixed is an ISOMORPHISM on this patch for small h. Given the actual original N4 targets(1) of62d3, its exact scalar equation and back-substitution produce an exact homogeneous full40 slow first field with ALL twenty original METRIC Cauchy entries equal to that target. The original Lorentz profile is copied by its exact shifted column. This is a selected one-cut LINEAR metric realization with changed coordinate trace; independent connection/frame/link/history conditions are not thereby matched, and no invariance or nonlinear branch is inferred.

Relative to W_N=S_h(TU_N)+G_h^L C_e U_N, the original qualified cut gain gives the actual reduced rhs r_delta=O(h^(N+1)) for each separately funded N>=4. Since c_h=O(h3), A_h^-1=O(h^-2), its scalar R_h is also O(h^(N+1)). Therefore the unique patchwise correction satisfies
 delta a=O(h^(N-3)), delta u=O(h^(N-2)), delta s=O(h^(N-1)). (22)
For N4 these are O(h),O(h2),O(h3); for N5 they are O(h2),O(h3),O(h4). These are bounds, not assertions of first nonzero coefficients. The first longitudinal coefficient for N4 is exactly
 [h]delta a=([h5]r_delta,long)/d4,                       (23)
because c_h A_h^-1 r_top begins at h6. For N5 replace h,h5 by h2,h6. Evaluating the original normal-target functional in(23) remains separate. No compatibility obstruction is needed on this patch: d4 is nonzero, so any actual finite smooth target is in the declared slow metric range. Keeping the ORIGINAL unchanged twenty traces instead still requires r_delta=0; this proof does not establish it.

## 8. Precise domains and limits

Use the same physical annulus, proper temporal contour, all-twenty trace normalization, lower eta and copied Lorentz as62d3. Native time +/-h, true spatial offsets and independent connection reconstruction are evaluated on the original enlarged common slab; no zero-past truncation, owned-boundary window or residual projection is inserted. Restrict the INPUT smoothly to the indicated frequency patches; this is an actual admitted annular TT seed subspace, not an axis ansatz times a physical-space envelope. Fourier reflection gives real fields. All inverses are smooth multipliers on this compact patch, with each fixed k derivative and the stated powers of h, so the original stopped weights follow with the already declared finite derivatives/Sobolev margins. A native physical coframe sample E has one further h factor.

Separately fund fixed N4 or N5 at the eaa5 target(r+6,J+8), with the ORIGINAL B_N recurrence and sufficiently small common cone; the N5 reserve is not inherited for free from N4. Smooth compact spectral data supply these finite seminorms. Constants and h radii depend on the finite N, patch gap, input target and slab/halo. There is no uniform-N limit. Formula(22) makes the metric solution removable holomorphic at h0 for these actual finite targets; it supplies no nonlinear family.

The R7 whole-trace native-step-invariance gap is not contradicted: one-cut metric equality is not an invariant physical image, and (22) alone is only an upper bound, not proof that the actual repair has or lacks an h5-leading size. This proof neither selects a physical history nor identifies constructor Phi with Coulomb chi. Original frame/link conditions, exceptional rays, a global all-frequency inverse, nonlinear compatibility, physical quotient and full parent remain open.
