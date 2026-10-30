# Original j2 Schur normal source and actual three-dimensional scalar trace — OPEN

Manual derivation at completed M157/1137 authority, with later reviewed-supplement notifications kept separate. New source calculation0/receiver0; no live owned process. The earlier slow-family and physical-trace sources remain unchanged. This note is unreviewed and requires distinct original-source verification. Broad centering/normal-row strategy was reported to ROOT before freeze; that orientation is not review credit.

## 1. Original maps, lower residual and return from centering

Use original physical vertex coframe f and connection a, eta=(-+++), kappa=1/101, incoming formal transposes. Original183dbf93 supplies all40 quadratic rows; original fd528a85 and c41f327c supply the complete finite-word L2/J2 recipe. Original centered-curvature a3f59c8f proves, by expanding the six noncommuting plaquette brackets and five transported complement contacts, that with
 m_i=(1+S_i^-1)/2, bar a_i=m_i a_i, d_i=sinh(h partial_i)/h,
 the COMPLETE flat curvature quadratic is its native leading Palatini quadratic with each partial_i replaced by d_i. This is an exact compact interior identity, not a finite-boundary identity. Only a formal Taylor change on the fixed physical annulus is used; no all-frequency averaging inverse is installed.

Write Omega for the leading torsion-free connection map, Tc for the algebraic torsion map, M for the original unordered-face signed covector pairing, B for the actual coordinate24 connection Hessian. At flat B is symmetric and invertible with the original repeated/distinct blocks. Put D a=(partial_i a_i/2)_i. The original first lift on a leading homogeneous field u=(f,Omega f) is
 Y_u=(0,D Omega f+c),
 Z=U1(f,Omega f)=T_f,1 f+Tc D Omega f,
 c=-2kappa B^-1 Tc^dagger M Z.                            (1)
The transformed first field is (0,c). The original coefficient residual is j2=J2u+J1Y_u. The Euler source of the field-dependent density substitution has an additional (DY)^dagger r1 contact, r1=F1+JY; after graph pullback the incoming Omega^dagger contact is also present. Neither is dropped off orbit. On the actual leading homogeneous u, J0u=0 and J1u+J0Y_u=0 in ALL forty rows, so the linearized lower-residual contact vanishes. Only at this step may the effective-density Euler source be identified with j2_e+Omega^dagger j2_a.

The centering path also has an induced second connection coefficient: since m=1-hD+h2D2+..., m(a+h(Da+c)) has second coefficient -Dc. Thus the transformed j2 and original j2 can differ by J0(0,Dc). The original graph/Schur pullback annihilates this pure-connection term exactly: (J0(0,b))_e+Omega^dagger(J0(0,b))_a=0. Therefore the coframe source below is the ORIGINAL vertex-coframe source, not a recentered cut. The exact incoming transpose and full B inverse are retained. All finite Green endpoints/left-cell/frame terms of this compact derivation remain; no boundary potential is deleted.

## 2. Exact effective quadratic source

For the metric m_mu nu=eta(f_mu,t_nu)+eta(t_mu,f_nu), tetrad compatibility gives
 partial_i f_j+Omega_i(f)t_j=Gamma^I_ij(m),
 Gamma^I_ij=(eta^I mu/2)(partial_i m_mu j+partial_j m_mu i-partial_mu m_ij),
 Z_ij^I=(partial_i-partial_j)Gamma^I_ij/2.                  (2)
This identity applies before selecting the actual TT or coordinate field; Z is independent of the leading Lorentz representative. Define the COMPLETE signed face covector
 Q=H Z, H=M-2kappa M Tc B^-1 Tc^dagger M.                  (3)
B is not replaced by its curvature block, and H is not asserted positive or a projector.

To derive(3), the order2 density on the centered first-corrected graph is
 q_C,2(f,Omega f)+kappa<Z,MZ>+2kappa c.Tc^dagger MZ+c.Bc/2.
The last B is the FULL Hessian. Substituting(1) gives q_C,2+kappa Z.Q. For curvature alone its leading connection derivative vanishes on the entire torsion-free graph, so replacing Omega_partial by Omega_d changes this coefficient only at the next order. Consequently q_C,2 is exactly the h2 coefficient of the native leading Einstein quadratic with partial replaced by d. No supplied action is used; this is the original Palatini quadratic's algebraic Schur elimination.

Let G^(2) be that derivative-replacement coefficient of the original flat Einstein tensor. Original leading force normalization is E_e=-eta G, so delta q0=-G^mu nu delta m_mu nu/2, whereas delta q2_eff=S^mu nu delta m_mu nu/2 for the source DG[m_response]=S associated with J0W=-j2. Therefore the full source is defined explicitly by
 S^mu nu delta m_mu nu/2=-G^(2),mu nu delta m_mu nu/2
                         +2kappa sum_(i<j) Q_ij,I Z_ij^I(delta m). (4)
All derivatives on the test in(4) are integrated with their TRUE formal transpose. This is a finite constant-coefficient specification of every source entry, including its spatial rows and time derivatives; no unknown source tensor is left to be chosen.

For clarity the normal curvature entries are
 G00^(2)=[sum_ij partial_i^3 partial_j m_ij-sum_i partial_i^4 tr(m_sp)]/6,
 G0a^(2)=[partial_t^3 sum_i partial_i m_ia+partial_t sum_i partial_i^3 m_ia
 -(partial_t^3 partial_a+partial_t partial_a^3)tr(m_sp)
 +partial_a^3 sum_i partial_i m_0i+partial_a sum_i partial_i^3 m_0i
 -2sum_i partial_i^4 m_0a]/12.                            (5)
Spatial indices in(5) run1..3. Time powers are not assigned improved spatial decay.

## 3. Both original normal torsion rows with their factors

Extend Q antisymmetrically in its face indices. A test delta m00=L has only Z_0i^0(delta m)=-partial_i(partial_t-partial_i)L/4. A test delta m0a=delta ma0=B_a has
 Z_0i^b=(partial_t-partial_i)(partial_i B_b-partial_b B_i)/4,
 Z_ij^0=-(partial_i-partial_j)(partial_i B_j+partial_j B_i)/4.
These are the literal two possible Christoffel-index contractions from(2). Since both contain TWO derivatives, their incoming transpose has positive sign. The off-diagonal source satisfies S^0a=-S0a. Thus, with F=S00 and J_a=S0a, the complete normal source is
 F=-G00^(2)-kappa sum_i partial_i(partial_t-partial_i)Q_0i,0,
 J_a=-G0a^(2)-(kappa/2)[sum_i partial_i(partial_t-partial_i)Q_0i,a
 -(partial_t-partial_a)sum_b partial_b Q_0a,b
 -sum_(j!=a)(partial_a-partial_j)partial_j Q_aj,0].          (6)
The half in J comes from the test coefficients in(2), not a half-force convention. Formula(4) includes BOTH symmetric metric slots; treating m0a alone without ma0 would give the wrong factor. Q includes every repeated/distinct B block and source-adjoint contribution in(3).

## 4. Exact repeated-block reduction of the scalar row

Fix spatial i. In its repeated block use actual matrices c_A=x_A(t_A wedge t_i), A in {0,1,2,3} minus{i}. Then Tc c has only (A,i) component x_A t_A, so Tc^dagger M Tc=I3 in these exact coordinates. Original curvature gives -sum_(A<B)x_A x_B: for instance [t_A wedge t_i,t_B wedge t_i]=-t_A wedge t_B and the original epsilon/star pairing of that face is -1, also for pairs containing0. Hence
 B_i=a I-11^T, a=1+2kappa,
 B_i^-1=a^-1 I+[a(a-3)]^-1 11^T.                          (7)
This verifies the signed/permuted repeated block independently; no invariant-vector output is substituted for its covector.

Put L_diag=sum_j partial_j m_jj and T_sp=tr(m_sp). The three components r_A=(Tc^dagger MZ)_A are Z_Ai^A, in particular
 r0=-partial_i(partial_t-partial_i)m00/4,
 sum_(j!=i, j spatial)r_j=partial_i(L_diag-partial_i T_sp)/4.
The temporal face metric pairing has M_0i,00=+1. From(3),(7) its EXACT coefficient, for any metric m, is
 Q_0i,0=partial_i[-(partial_t-partial_i)m00
                  +kappa(L_diag-partial_i T_sp)]/[4a(1-kappa)]. (8)
Thus the scalar source in(6) is completely explicit without any unresolved matrix inversion. Other components of Q in J remain the explicit original finite matrix(3), with all eight known blocks.

## 5. Actual admitted normalized TT cut and a nonzero scalar response

The admitted leading first field is NOT the unflowed TT wave everywhere. It is that wave plus D0 chi, with lower chi and original zero constructor displacement jets0..3 at the initial cut. These zero jets make the metric cut and the time jets needed for F VALUES and Q_t equal to the TT ones, including m00,partial_t m00,partial_t2 m00=0. Let m_sp(0)=q, partial_t m_sp(0)=2p, with q,p actual transverse trace-free annular seed directions. Then G00^(2)=0, G0a^(2)=partial_t sum_i partial_i^3 m_ia/12, and(8) and its first time derivative reduce to Q_0i,0=kappa partial_i L_diag/[4a(1-kappa)]. It follows that the actual scalar normal source VALUE is
 F(0)=-[Delta_sp partial_t-sum_i partial_i^3]L_diag/41200 at the cut. (9)
This uses kappa^2/[4(1+2kappa)(1-kappa)]=1/41200 exactly. The coordinate normalization is retained; no free fourth displacement jet is chosen.

There are genuine three-dimensional admitted data with nonzero(9). Set p=0. At k=(1,2,3), take q=a0 a0^T-b0 b0^T with a0=(2,-1,0)/sqrt5 and b0=(3,6,-5)/sqrt70. These are orthonormal and perpendicular to k. The tensor has diagonal(47,-22,-25)/70 and trace zero, so
 sum_j k_j q_jj=-36/35, sum_i k_i^3=36.
With derivative i k, (9) gives Fhat=(sum_i k_i^3)(sum_j k_j q_jj)/41200, nonzero. Scale k into any interior radius of the physical annulus, choose a smooth local TT polarization extending this one, and choose a nonnegative smooth real spectral amplitude supported on a sufficiently small patch and its reflection. The symbol remains nonzero on an open subpatch by continuity. Reflect the polarization evenly; this produces a real centrally-even Schwartz TT geometry direction, not an axis ansatz times an envelope. The actual normalized leading family is constructed on such data; its displacement change does not alter(9).

The selected scalar inverse therefore gives vhat=Fhat/(4rho2), and the actual order-h2 physical Coulomb cut value is
 chi_phys,i(0)=Fhat k_i/(2i rho4), generally NONZERO.         (10)
This proves a mismatch with the deliberately declared ZERO-TOTAL-COULOMB trace at that formal order for these admitted directions. It is not an obstruction to an original physical branch or an exact nonzero-h family with the correct physical trace.

## 6. Actual time jets and complete physical trace, not unflowed substitution

To compute S,S_t,S_tt for the complete physical trace table, insert the ACTUAL normalized leading field into(2)-(6) and differentiate. The coefficients are constant but the coordinate piece is not discarded. In the consistent lower basis, its mixed limiting equation is
 sum_(j=0..4)G_j partial_t^j chi=-(C0+C1 partial_t)t_TT,
 chi(0)=chi_t(0)=chi_tt(0)=chi_ttt(0)=0, G4=A4.
Thus chi4=-G4^-1(C0 q+2C1 p),
 chi5=-G4^-1(G3 chi4+2C0 p-rho2 C1 q),
 chi6=-G4^-1(G3 chi5+G2 chi4-rho2 C0 q-2rho2 C1 p).         (11)
Here G2 on the last line is the lambda2 COEFFICIENT G_2, not the whole polynomial. Original all-direction A4 is invertible on the physical annulus. The C matrices are the original TT forcing reduced modulo its wave equation; no new hidden coordinate trace is introduced. Formula(11) is the actual differentiated original compatibility solve, not a tunable history.

In particular (8) shows exactly why time jets cannot be read from unflowed TT alone. For a pure lower-coordinate metric D0 chi, the additional scalar values at the initial cut are
 Delta F=0,
 Delta F_t=[kappa/(2a(1-kappa))]Delta_sp chi0^(4),
 Delta F_tt=[kappa/(2a(1-kappa))]sum_i partial_i2[chi0^(5)-2partial_i chi0^(4)]. (12)
The normal curvature scalar coordinate contact has no time derivatives and vanishes through this order at the cut. The spatial-coordinate terms in(8) also vanish through this order because chi_sp jets0..3 vanish. These signs are for LOWER chi0; upper constructor displacement reverses that component. For the full source spatial rows, the explicit Gamma structure in(2) requires at most chi6 for S_tt: on a displacement Gamma_ij^I=partial_i partial_j chi^I, and an electric face has at most two time derivatives before the Euler step. No C5 transfer from mere C4 spatial values is assumed.

Finally substitute the actual F,J,S and their time jets into the earlier full physical trace table: Delta v=-F/4, P_flat X=J, p_response=LX, R=2S-eta trS; M0=4vI,M1=2p_response,M2=R_sp-rho2M0,M3=R_t,sp-rho2M1,M4=R_tt,sp-rho2R_sp+rho4M0 and N0=0,N1=-2grad v,N2=R_0sp,N3=R_t,0sp-rho2N1. Then the sixteen coordinate jets are Q_Coulomb(Mr) and [k.Nr-k.Q_Coulomb(Mr+1)]/(i rho2), r0..3. This Q_Coulomb is a spatial multiplier, distinct from the face covector Q in(3). The original symmetric lift/no-extra-h2 frame prescription and native independent connection remain to be matched after these metric traces.

## 7. Finite scope, funding and remaining gap

These are fixed-band linear first-seed coefficient identities, not an arbitrary-source example. The native L2/general Euler reserve through6, first lift through2 and Omega incoming derivative plus two time derivatives fit the previously stated safe nine native-field/ten coframe reserve. On the actual displacement metric, the explicit index inventory above reduces the needed compatibility jets to chi4..6. All matrices and inverse G4 are smooth bounded multipliers on the fixed annulus; smooth compact spectral data and the finite holomorphic time slab fund these finitely many derivatives. Reality/support/Schwartz regularity are preserved; componentwise evenness is not asserted for derived vector coordinates. Two seed derivatives are meaningful only with the constructor's actual C2 map in the same funded finite target; no additional analytic domain is silently manufactured.

The next exact-h question remains an actual physical trace/range equation. Formal source and trace matching throughh2, even with the nonzero value(10), does not select an exact h-dependent boundary/history prescription or prove exact nonzero-h matching. All finite original endpoint, frame and left-cell surfaces remain outside the compact centering identity; none is assigned zero by this bulk source computation. No exact-h inverse, nonlinear lift, infinite-order convergence, physical quotient or parent completion is claimed.
