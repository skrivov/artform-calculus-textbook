# Full original force: Ward columns and an algebraic gauge slice

Finished manual proof for distinct ROOT review after prospective fresh whole M40 PASSe3620d. Earlier Ward and flat40 OPENs remain immutable at their own cutoffs and are not accepted premises: their original-law arguments are restated here. ROOT assigned the target and supplied scope/contact cross-checks. The current M39/M40 accepted branch supplies full stationarity; nonflatness is not needed for the Ward identities. This source history is0/0/0. No restricted-action Hessian, evaluator or physical count is used.

## 1. Original variations and locality

Let z=(E_i,U_i) denote the ORIGINAL four independent coframe columns and four independent links at every vertex, with U_i near identity and the coframe matrix E invertible. Perturbations of U0 and U1 are INDEPENDENT even when their background values agree. All six Lie-algebra directions on every link and all sixteen coframe coordinates are retained. Thus the full coordinate fiber has40 entries, not the ten raw probes or the eight solved normals.

The modified transported-face curvature action and the original torsion term are exactly invariant under

 E_i(v)->G_v E_i(v),
 U_i(v)->G_(v+i) U_i(v) G_v^-1.                         (1)

For torsion this follows from its original transported difference transforming at v, with both inverse metrics and det(E) invariant. For curvature it follows from base-vertex conjugation of the original plaquette and each transported complementary bivector, including both diagonal paths. Fixed real couplings and the determinant term do not change (1).

On an infinite background the total action need not be summable. Use compactly supported variations in the local action and assemble every incoming/outgoing owner. The force and its derivative are local finite-stencil expressions, so these variational identities determine the complete original rows. On a finite owned region take gauge parameters supported away from its boundary, or retain the original endpoint terms. No periodic reindexing or background action summability is assumed.

## 2. Exact gauge column in physical and fixed-log coordinates

For an arbitrary Lorentz-algebra profile omega_v, differentiation of (1) gives

 delta E_i(v)=omega_v E_i(v),
 Y_i(v)=delta U_i(v) U_i(v)^-1
       =omega_(v+i)-Ad_(U_i(v)) omega_v.                 (2)

Y is right-trivialized at the terminal frame. The original torsion source instead uses the left-trivialized X_i=U_i^-1 delta U_i; the exact conversion is

 X_i=Ad_(U_i^-1)omega_(v+i)-omega_v.                    (3)

Equations(2)-(3) must not be interchanged without their adjoint. Let U_i=exp(P_i) on the common small full six-coordinate log chart. Its right differential is

 Phi(ad P_i) delta P_i=Y_i,
 Phi(w)=(exp(w)-1)/w, Phi(0)=1,
 delta P_i=Phi(ad P_i)^-1
           [omega_(v+i)-exp(ad P_i)omega_v].             (4)

Phi is invertible on a uniform small matrix ball. Define R_z omega to be the40-vector consisting of delta E and delta P in (2),(4). This column includes off-ansatz directions. For example a B02 parameter generally changes E0 and produces temporal/spatial coframe components forbidden by the traveling transverse ansatz. It cannot be represented by merely varying its eight connection coordinates.

## 3. Whole original Ward identity and its linearization

Write the complete first variation with right-trivialized terminal link sources p_l:

 delta S=sum_(v,i) pi_(v,i)(delta E_i(v))
                    +sum_l <p_l,delta U_l U_l^-1>.

Here pi and p are derivatives of the WHOLE original action, including torsion metrics/determinant and every incident transported curvature owner. They are not bare face bivectors or normal-output combinations. The fixed-log coordinate force is F_(P_i)=Phi(ad P_i)^* p_i, so pairing it with (4) reproduces exactly <p_i,Y_i>. No half-probe normal-output convention is introduced. Define the coframe moment covector by

 <J_v,omega>=sum_i pi_(v,i)(omega E_i(v)).

Substituting (2), using the invariant internal pairing and collecting omega_v gives exactly

 J_v+sum_(t(l)=v) p_l
       -sum_(s(l)=v) Ad_(U_l^-1)p_l=0.                  (5)

The incoming source has coefficient+1; the outgoing source has the original inverse adjoint. This is a six-component identity at every interior vertex. In shorthand R_z^* F(z)=0, where F is the complete original coordinate force and the star means the formal compact-test transpose, not an imposed Hilbert metric.

Let mathcal J_z=D F(z) in the full original coordinate chart. Differentiating the Ward identity gives

 (D R_z[eta])^* F(z)+R_z^* mathcal J_z eta=0.           (6)

At a fully stationary z*, the first term is zero. Independently, invariance of the full action maps full stationary fields to full stationary fields, so differentiation of their gauge orbit gives

 mathcal J_(z*) R_(z*) omega=0,
 R_(z*)^* mathcal J_(z*) eta=0.                         (7)

These can also be obtained from the mixed SECOND variation of the full original action; its extra D R term multiplies F(z*) and vanishes. No conclusion is drawn from differentiating the identically zero action RESTRICTED to the null/traveling family. M39 gives F(z*)=0 in ALL40 independent original rows, which is precisely the stationarity required here.

## 4. A genuine bounded ambient realization

For a concrete domain let X_m=l_infinity(Z^4;R^m) in the fixed original coordinate bases, and keep a uniform small full-field neighborhood of flat. Every lattice shift is bounded with norm1. The original finite words, exponentials, inverse coframe metrics, determinant and their finite-stencil derivatives are analytic maps on this neighborhood. Therefore the full local force F and its derivative mathcal J_z are bounded maps X40->X40 (identifying the finite output fiber with its dual by coordinates only), and R_z is bounded X6->X40. This is a direct original finite-stencil realization, not a transfer from a reduced Fourier-l1 Hessian. The gauge identities extend pointwise to bounded omega by locality; their compact-test derivation needs no infinite action sum.

The same finite-stencil argument gives bounded realizations on X_m^(2)=l2(Z^4;R^m), with the same coefficient bounds; the background itself need not be l2. This is derived from the ORIGINAL finite-stencil force, not transferred from a reduced Fourier-l1 estimate. Compact-test formal adjoints extend to the actual Hilbert adjoints by boundedness and density. In the fixed original coordinate chart, the output F is the exact physical-coframe/fixed-log coordinate covector, represented by the ordinary Euclidean coordinate Riesz vector. Its compact-test second variation is symmetric: <q,mathcal J_z h>=D²S(z)[q,h]=D²S(z)[h,q]. The relevant local sum is finite even if the background action is infinite. Boundedness and density therefore give mathcal J_z^*=mathcal J_z on this auxiliary l2 realization. This is a full-coordinate variational statement, not positivity or an adjoint claim about reduced normal outputs. The exact coordinate conversion is specified in the companion qualification.

The M39 traveling branch samples to z_epsilon=z_flat+O(epsilon) uniformly in these domains. Analyticity of the original force and the gauge chart gives

 mathcal J_(z_epsilon)=mathcal J_flat+O(epsilon),
 R_(z_epsilon)=R_flat+O(epsilon)                         (8)

in these bounded operator norms. This does NOT give epsilon analyticity of the branch or a nonflat inverse. At flat, for an arbitrary four-direction character with shifts zeta_i, the exact gauge columns are

 delta E_i=omega t_i, delta P_i=(zeta_i-1)omega,
 mathcal J_flat(zeta) R_flat(zeta)=0.                    (9)

The six columns are independent for EVERY zeta: their coframe block already determines omega. In particular transverse phases zeta2,zeta3 are not set to1 for these off-ansatz tests.

## 5. An algebraic coframe gauge projection, not a physical reduction

Let eta_M=diag(-1,1,1,1) be the internal metric and write delta E as a4x4 column matrix. For any40-direction q define

 Lambda_z q=skew_etaM(delta E E^-1),
 skew_etaM(A)=(A-eta_M^-1 A^T eta_M)/2.

Since omega is eta_M-skew, Lambda_z R_z omega=omega exactly. The guarded coframe inverse bounds Lambda_z uniformly on X40->X6, separately on the sup-norm and l2 realizations. Thus R_z is injective with a bounded left inverse, and

 P_z=I-R_z Lambda_z,
 P_z²=P_z, image(P_z)=ker(Lambda_z),
 kernel(P_z)=image(R_z).                               (10)

At full stationarity (7) implies mathcal J_z=mathcal J_z P_z. This gives an actual bounded splitting of the six local Lorentz directions in the full40-coordinate perturbation problem. It does not prove that the remaining gauge-fixed force is invertible, surjective, positive or a well-posed evolution. Neither40-6 nor the dimension of the traveling normal solve is a physical degree count.

## 6. Precise remaining calculation

The complete off-ansatz gauge-fixed finite-stencil operator mathcal J_(z_epsilon)P_(z_epsilon), including its nonconstant traveling coefficients and arbitrary independent spatial shifts, has NOT been evaluated here. Its constraint rows, characteristic propagation and any slicing/refoliation identity remain to be derived. This operator, rather than a restricted scalar derivative or ten-probe Hessian, is the next discriminating target. The original exact Lorentz Ward identity supplies no displacement/refoliation symmetry automatically. No two-polarization, gravitational-parent, continuum, quantum or physical-stability claim is made. This finished source requires distinct ROOT review and is not self-accepted. It does not include the separate ROOT fixed-complement intertwiner or compatible-source-equivalence theorem.
