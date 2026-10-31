# Complete original flat quadratic action and forty-row operator

Finished restated manual proof after fresh whole M40 PASSe3620d. The earlier complete unrestricted quadratic OPEN remains immutable at its honest M39-start cutoff and is not accepted as a premise; the original-law derivation is given below. All four shifts remain independent. ROOT supplied the target and mixed gauge/contact checks. Exact coordinate covector and invariant-pairing conversions are governed by the companion qualification. Source history0/0/0; distinct ROOT review is required.

## 1. Coordinates, pairings and normalization

Use the current original unit-spacing model h=beta=sigma=1, alpha=lambda=0, k=kappa=1/101. More generally write mathsf P=alpha I+beta star in the curvature terms; mathsf P is the FIXED INTERNAL bivector map, not a corner average. The native specialization is mathsf P=star. The coefficient k multiplies the original torsion functional C_T, with its original ordered-index factor1/2. Write t_i for the four flat internal basis vectors, eta=diag(-1,1,1,1) and s_i=eta_ii.

Take arbitrary independent perturbations

 E_i=t_i+epsilon f_i, U_i=exp(epsilon A_i), i=0,1,2,3.

Each f_i has four components and each A_i has six Lorentz-algebra components: all16+24 original coordinates are retained. Put D_i=S_i-I. S0,S1,S2,S3 are commuting independent lattice shifts; no traveling specialization is made. Work with compact variations on the full lattice, or periodic sums, so incoming adjoints are S_i^-1. Boundary versions retain the actual endpoint terms instead of this reindexing.

The invariant bivector pairing is g, and [A,B] denotes the original Lorentz action/bracket under its stated Lie-algebra/bivector identification. The quadratic coefficient means
 S(epsilon(f,A))=S(0)+epsilon S1(f,A)+epsilon² S2(f,A)+O(epsilon³).
Thus the full forty-row force linearization is D S2(f,A), not half of that derivative.

## 2. Original plaquette through second order

For each k<l the ORIGINAL ordered word is

 H_kl=exp(-epsilon A_l) exp(-epsilon S_l A_k)
          exp(epsilon S_k A_l) exp(epsilon A_k).

Set X_1=-A_l, X_2=-S_l A_k, X_3=S_k A_l, X_4=A_k. Direct ordered-product expansion and K=-(H-H^-1)/2 give

 K(H_kl)=epsilon (mathsf K A)_kl+epsilon² Q_kl(A)+O(epsilon³),
 (mathsf K A)_kl=D_l A_k-D_k A_l,
 Q_kl(A)=-1/2 sum_(a<b)[X_a,X_b].                     (1)

Indeed H1=sum X_a and H2-H1²/2=(1/2)sum_(a<b)[X_a,X_b]; the inverse in K removes the symmetric square and changes the sign. This fixes both loop orientation and the BCH contact without replacing the original reading by a logarithm. Its symmetric polarization is

 Q_kl(A,B)=-1/4 sum_(a<b)([X_a(A),X_b(B)]+[X_a(B),X_b(A)]).

In particular DQ_kl(A)[B]=2Q_kl(A,B).

## 3. Complete first transported complement

For the unique complementary i<j let e_ij,kl=epsilon^(ijkl), C_kl=e_ij,kl(t_i wedge t_j), and
 B1_ij(f)=f_i wedge t_j+t_i wedge f_j. The five original averaging summands have weights1/4,1/4,1/4,1/8,1/8. The first two diagonal-path connection sums are A_k+S_k A_l and A_l+S_l A_k. Therefore define

 mathsf A_kl=(I+S_k)(I+S_l)/4,
 V_kl(A)=[(3I+S_l)A_k+(3I+S_k)A_l]/8,
 (mathsf L f)_kl=e_ij,kl mathsf A_kl B1_ij(f),
 (mathsf U A)_kl=-[V_kl(A),C_kl].                      (2)

The signed averaged complement is C_kl+epsilon(mathsf L f+mathsf U A)_kl+O(epsilon²). Both diagonal paths are present; their1/8 weights cannot be replaced by a single untransported corner. Higher complement contacts multiply K(0)=0 and hence do not contribute at quadratic order. Conversely C_kl Q_kl is necessary since C_kl is nonzero.

## 4. Complete torsion coefficient and metric contacts

The original transported torsion has flat value zero and first coefficient

 theta_ij=D_i f_j-D_j f_i-A_i t_j+A_j t_i,
 theta_ji=-theta_ij.                                  (3)

The full det(E) and inverse-metric coefficient in C_T is its flat value plus O(epsilon). Torsion is epsilon theta+O(epsilon²), so its square is epsilon² theta theta+O(epsilon³). A first variation of det(E) or either inverse metric multiplies that square and begins at order epsilon³; second torsion contacts pair with the ZERO background torsion and likewise give no quadratic contribution. These terms are retained in the original law, rather than assumed absent. It follows exactly that

 (S2)_T=k sum_(i<j) s_i s_j eta(theta_ij,theta_ij).      (4)

The original ordered-index sum and its1/2 are precisely the unordered-face sum in(4); no further1/2 is introduced. At lambda=0 no volume quadratic remains.

## 5. Complete quadratic action

With sums over all vertices and all six k<l, the complete answer is

 S2(f,A)=sum_kl {g(mathsf L f+mathsf U A,mathsf P mathsf K A)_kl
                         +g(C_kl,mathsf P Q_kl(A))}
             +k sum_(i<j) s_i s_j eta(theta_ij,theta_ij). (5)

The linear curvature coefficient is sum g(C,mathsf P mathsf K A), an assembled total difference with constant C; it vanishes on compact/periodic tests. The torsion has no linear coefficient. Thus flat stationarity holds in the actual full coordinate chart. No pure-coframe curvature quadratic was omitted: its second complement variation multiplies K(0)=0. Equation(5) includes every curvature face, every first transport contact, the full second plaquette contact, every coframe/link torsion direction, and all incoming shifts.

## 6. Explicit forty-row operator, including the connection contact block

Write theta=T_f f+T_A A and W theta for the face covector with entries s_i s_j eta(theta_ij,.). A dagger below means the compact-test transpose/pullback of the DISPLAYED linear map, with the invariant g pairing for bivector outputs; for torsion use its displayed vector-dual pairing. Thus every shifted coefficient is transposed with S_i^-1. mathsf P^dagger is its fixed g-transpose (equal to mathsf P here). There is no canonical-normal half/quarter output rescaling.

Define H_Q by the following explicit formula. In each face put Z_kl=mathsf P^dagger C_kl and write X_a=R_a A with the four signed-shift maps in section2. Form

 Y_a=(1/2)[Z_kl,sum_(b>a)X_b-sum_(b<a)X_b],
 H_Q A=sum_(k<l) sum_(a=1)^4 R_a^dagger Y_a.            (6)

Here R_1^dagger Y contributes -Y to link l; R_2^dagger contributes -S_l^-1 Y to link k; R_3^dagger contributes S_k^-1 Y to link l; R_4^dagger contributes Y to link k. Bracket expressions are identified with covectors by g. Formula(6) follows from invariance of g and is exactly the derivative of sum g(C,mathsf P Q(A)); it is not an unknown contact operator. Equivalently its pairing with B is2 sum g(C,mathsf P Q(A,B)).

The complete full-coordinate linear force is

 F_f=2k T_f^dagger W theta+mathsf L^dagger mathsf P mathsf K A,
 F_A=2k T_A^dagger W theta+mathsf K^dagger mathsf P^dagger(mathsf L f+mathsf U A)
                   +mathsf U^dagger mathsf P mathsf K A+H_Q A. (7)

In block form its four entries are respectively
 J_ff=2k T_f^dagger W T_f,
 J_fA=mathsf L^dagger mathsf P mathsf K+2k T_f^dagger W T_A,
 J_Af=mathsf K^dagger mathsf P^dagger mathsf L+2k T_A^dagger W T_f,
 J_AA=mathsf U^dagger mathsf P mathsf K+mathsf K^dagger mathsf P^dagger mathsf U+H_Q+2k T_A^dagger W T_A.

These formulas map all16 f and24 A entries to their original coordinate covectors. For additional explicit torsion normalization, put beta_ij=s_i s_j eta(theta_ij,.) and beta_ji=-beta_ij. Its coframe row j is2k sum_i(S_i^-1-I)beta_ij, and its link row i evaluated on ANY of the six generators B is -2k sum_j beta_ij(B t_j). The curvature rows are the explicitly defined map transposes in(2),(6),(7). Thus (7) is a complete finite tensor/operator specification of all40 rows, not only an inventory of sectors awaiting missing contact blocks.

For the unrestricted four-direction symbol replace EVERY S_i by zeta_i and every incoming S_i^-1 by zeta_i^-1 in these finite maps. This gives the full40x40 Laurent matrix at arbitrary independent phases. It does not Fourier-diagonalize the nonconstant M39 branch.

## 7. Mixed six-column gauge check

At flat the exact original Lorentz column is f_i=omega t_i, A_i=D_i omega. Equation(3) gives theta=0, and mathsf K(D omega)=0. Directly from(2),

 V_kl(D omega)=(mathsf A_kl-I)omega,
 (mathsf L f+mathsf U A)_kl=[omega,C_kl].               (8)

Pure-gauge quadratic zero alone would not prove a full Hessian kernel. For an ARBITRARY second connection direction A, expand the original fixed-log gauge column at background sA:
 R_i(sA)omega=D_i omega+s R1_i(A,omega)+O(s²),
 R1_i(A,omega)=-[A_i,(I+S_i)omega]/2.
 This follows from the small-chart inverse Phi(adP), not from a chosen normal output. Exact original plaquette covariance gives at coefficient s

 mathsf K R1+2Q(A,D omega)=[omega,mathsf K A].           (9)

This identity can equivalently be checked in the six ordered commutators of(1). Substituting (8)-(9) into the derivative of(5) in the gauge direction leaves

 sum_kl {g([omega,C],mathsf P mathsf K A)
       +g(C,mathsf P[omega,mathsf K A])
       -g(C,mathsf P mathsf K R1)}.

The first two terms cancel by invariant g and equivariance of the FIXED INTERNAL mathsf P. There is no extra corner average in this cancellation. The final term is the original assembled constant-complement total difference and vanishes on compact/periodic tests, with all incoming shifts retained. The torsion mixed term is zero since theta(gauge)=0. The arbitrary second coframe direction contributes nothing because mathsf K(D omega)=0. Consequently the complete operator(7) annihilates all six Lorentz columns, not just their quadratic self-pairings.

At arbitrary phases these columns are f_i=omega t_i, A_i=(zeta_i-1)omega. They are independent because the four coframe columns determine omega. This is the original full-coordinate Ward kernel check, not a physical degree count or a reduced-force adjoint assertion.

## 8. Limits

The quadratic action and factorized operator here are complete at FLAT for unrestricted four-direction perturbations of the stated original candidate. No rank beyond the six Ward columns, inverse, physical spectrum, slicing constraint propagation, refoliation or gravitational-parent conclusion has been derived. Expansion of the nonconstant branch operator and analysis of its gauge-fixed constraints remain separate. All reasoning and algebra were manual; this finished source requires distinct ROOT review before accepted promotion and is not self-accepted.
