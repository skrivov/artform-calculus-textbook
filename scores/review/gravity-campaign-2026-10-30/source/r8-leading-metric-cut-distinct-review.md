# Distinct ROOT review: quartic metric cut and actual R7 repair

PASS_SCOPED. Reviewer ROOT; author /root/r8_native_parent. Manual review of immutable quartic5665c33256a79a7c2124f1430c25070e167ddd607f54644cc23fc4f545c50750/16450 WITH scope7d8636c732659d5ad1a9014b46402234fefa83efbbf8f25969847655fe86523d/2149 and routingf0b00271/2878, and additive09ac99383538687c0d203a033d0eb059d9c40248cc567df282a0cfdd052d0992/6869 WITH routing11e7ac0a/2938. No findings. No mathematical evaluator was used. The separate completed Sol61 report79a6452b/10925 and scope75b5c8bc/1849 agree; its author is also distinct from the source author. This report records ROOT's checks, not a relabelling of that report as ROOT calculation.

## Original signed inverse and cubic elimination

The literal C columns and M=-I give C^T C=I+vv^T, CC^T=I+ww^T, Cv=-2w. The curvature brackets xy,-xz,-yz give Bc=vv^T-I and Bc^-1=-I+vv^T/2. The full signed Woodbury inverse yields N0=-alpha I+2kappa ww^T, H0=-AI-Eww^T, A+3E=g, and the noncommuting N1,N2 in(5). I checked H1 entrywise. For H2 the lambda-squared third component is the difference of -2kappa^2 gAE(x1-x2) and -kappa E(A+2E)(x1-x2)/2, namely C2(x1-x2). On e+=(1,1,0), the lambda-p terms are2C2 and C2 before subtraction; lambda-q gives-2C2 and-C2. Thus the mixed entries are indispensable and correct.

The original symmetric metric-slot factor gives the cubic b3 and left c3. The Fourier identity d s3-d^[2]Delta=-rho^2 v and phi=a/(i rho) give b3=-i kappa^2 gA rho v/2 and c3=b3^T. With A2=-beta rho^2, their bilinear product is kappa^4 g^2 A^2|v|^2/(4beta), negative because beta<0. Hermitian conjugation here would reverse the answer. The scalar cubic cancellation remains the separately reviewed original-block result; no spatial rotation covariance is used.

## Leading compatibility and dependent jets

I substituted m=D0 chi into the original normal rows. The electric repeated component is
 Q0i0=(D d_i/2)[-chi0,tt+d_i chi0,t+kappa(V2-d_i V1)].
It gives the scalar expression(13). For B_ij=d_i d_j(d_i-d_j), the distinct spatial component is
 Qij0=E(r_i chi_j-r_j chi_i)+Hd B_ij chi0/2,
 r_i=d_i(lambda^2-d_i lambda)/2.
The two electric sums in div J cancel by index exchange. The remaining contractions are sum B_ij^2=T and sum B_ij(r_i chi_j-r_j chi_i)=-(W_tt+U_t)/2. The original curvature terms obey div G0sp^(2)=partial_t G00^(2) on this pure coordinate input. These give exactly(14), including lower-chi0 signs and E-kappa D.

The original electric contraction gives G4,sp and G3,sp in(16): r.r=(Delta lambda^4-2s3 lambda^3+s4 lambda^2)/4 and r r^T supplies the displayed mixed tensor. The electric-spatial cross terms cannot contribute lambda^3 or lambda^4. Solving retains the longitudinal D Delta eigenvalue. The functional W annihilates d and sends d^[2] to T, so(17) gives W4=-(Hd-D)T phi/Hd. Equation(14) successively gives chi0,4=chi0,5=0 and D Delta chi0,6=-(E-kappa D)(W4+T phi). In F2,ttt the curvature term vanishes and the two kappa^2 D contacts cancel, leaving -kappa E(W4+T phi)/2. No higher jet is treated as free.

## Visible return, full Z3 field and test, and curvature

Full order-two metric Cauchy data vanish after the twelve visible equations are solved because K2 kills the longitudinal third jet and TT is fixed zero. This is not an identically zero order-two field. For a field with those Cauchy values, the original normal curvature row gives div G0sp^(2)=partial_t^3 G00/6. Cut Z1 is symmetric electric m_sp,tt/4 and H0 sends it to zero spatial-internal0. Therefore the visible return is precisely -F2,ttt/6. The lower homogeneous zero-T additions have the required cut jets zero; the nonzero first top-three adjustment is retained separately in the cubic Schur product.

I checked the direct substitutions in(18). With c=d phi, b=chi_sp,4, spatial Z3ij0=pq(p-q)phi/12. The electric entries give difference (q b_i-p b_j)/24-pq(p-q)phi/12. H0 therefore gives the first expression in(19). The lambda-squared H2 contribution contains C2[-p^2 c_j+q^2 c_i]/2 as well as the fourth jets; the mixed lambda-p/lambda-q terms give the opposite C2 pq(p-q)phi/2. They cancel. The remainder is C2(p b_j-q b_i)/2. The exact identity E/24-C2/2=kappa A^2/12 then proves Q*.

For the independent longitudinal test delta m0i=d_i phi_test, direct substitution gives Z3ij0=p^2q^2(p-q)phi_test/24. Its electric coefficients are opposite pq(p^2-q^2)/24. H0Z1 vanishes at the cut and its first time derivative is symmetric electric, so their incoming temporal terms cancel. This retains the independent cubic test.

For the centered-curvature fourth coefficient, the temporal-cubic/spatial-cubic cross term in the normal row is [s4 c_a+d_a V3(c)-2d_a^3 V1(c)]/72. Its divergence is [Delta V3(c)-s4 V1(c)]/72. The leading temporal-fifth contribution is a transverse curl and its divergence vanishes; spatial-fifth terms multiply zero lower jets. The cross term also vanishes for c=d phi. Hence the complete direct divergence is kappa^2 A^2 W4/12-kappa(Hd+E)T phi/12. Combining the visible return and the bilinear top-three product yields exactly d4=-C_*|v|^2 in(3).

## Scope of the positive solve and cross-route consequence

The inequalities Hd>1, D<1, A<1, g<2 and |beta|>1/13 make the negative term smaller than13kappa^4<kappa/24, while the positive term exceeds kappa/12. Thus C_*>kappa/24. The equation P k^[2]=0 says every nonzero k component has the same value: seven nonempty coordinate subsets and two signs, fourteen rays. Only a fixed compact reflected annular patch separated from those rays is covered.

There the bounded visible inverse, h^-2 top-three inverse and h^-4 scalar inverse give an exact one-cut twenty-METRIC-Cauchy isomorphism at fixed TT data. The actual finite-N cut residual is O(h^(N+1)), so the changes of longitudinal, top-three and visible trace coordinates are respectively O(h^(N-3)), O(h^(N-2)), O(h^(N-1)). The first longitudinal numerator [h^(N+1)]r_delta,long is not evaluated by this theorem. Neither the upper bounds nor the nonzero inverse asserts that numerator is nonzero.

I checked the additive against the already reviewed R7 original gap and whole-trace repair argument, using the original unweighted fixed-band multiplier premise authenticated and manually examined in the separate duty review. The original finite constant-coefficient constructor and proper-contour target matrices provide uniform band bounds, not merely individual smooth-seed estimates. The fixed bundle transformations are bounded, so the actual repair has norm O(h^(N-3)) in the SAME unweighted twenty-trace Hilbert completion, with TT head exactly unchanged. A small reflected neighborhood of rescaled(1,2,3) retains both v nonzero and the R7 witness. The corrected normalized graph therefore tends to the zero-coordinate graph, whereas every invariant normalized graph on that band has norm at least c_B>0. This proves noninvariance for sufficiently small h at each separately fixed N>=4, allowing its own induced TT propagator.

Actual nonlinear-constructor identification remains only on the original admitted smooth directions. Fourier-real L2 is a linear multiplier completion; weighted estimates require the separately funded finite derivatives. Original eaa5 T matching is initial-cut-only per cb440bb2. Lower Coulomb chi is not constructor Phi. Original independent connection/frame/link/history conditions, exceptional rays, other invariant spaces or order-one dressings, all-frequency and all-N limits, nonlinear lifting, physical quotient and quantum/full-parent completion remain open. All original scopes, finite budgets and actual native halos remain mandatory.

## Review custody

Current finished-byte report and scope reads are saved separately; earlier complete ROOT source/scope reads are explicitly prior, not new credit. Source author selfreads are custody only. ROOT current calculation/review/preparation/reception incidents0. Separate Sol61 reviewer metadata2 consists of two output guards before display, with whole actual61/62 families preserved and their new archives independently decoded by ROOT; those histories do not alter this mathematical verdict. The inherited R8 receiver1 and original description qualifications remain separately attributed. No source was edited, no original raw envelope was reconstructed and no historical archive was recursively decoded.
