# Original constant-coframe Schur symbol and coordinate normalization

Finished MANUAL authored proof for DISTINCT ROOT review, not self-accepted science. The original M90 derivation is restated from accepted native formulas under prospectively received M91 (own wholeab2e3f/intake47e78f). Effective subsequent metadata preparation2 is governed by the mandatory qualification; both frozen antecedent owners remain immutable and are not scientific premises.

## Original coordinates and exact Schur contraction

Use fixed-log physical sampling E_native=h e, P_native=-h omega, physical h^4 measure and original force h^-4 R_h^*F_native. Kappa=1/101; eta=diag(-1,1,1,1). Fix a constant real coframe E=(e_i^I), v=det E>0, g_ij=eta_IJ e_i^I e_j^J, omega=0. Coordinate displacement eta^a maps to INTERNAL xi^I=e_a^I eta^a. The original leading displacement is D_e eta=(e_a partial_i eta^a,0), not an identification of coordinate and internal indices at a general coframe.

The original forward-torsion first coefficient, applied to this column, is
 R_e eta_ij = T1(D_e eta)_ij = e_a(partial_i^2 partial_j-partial_j^2 partial_i)eta^a/2.
For general torsion-free leading data write
 s_i=partial_i omega_i/2, K_ij=D_i^2 e_j-D_j^2 e_i,
 r= kappa Tc,e^dagger W_e K,
 Y=(0,s-B_e^-1 r), B_e=v M_e^T B_kappa M_e.
Here Tc,e is the original connection-to-torsion map and W_e is the actual determinant/TWO-inverse-metric torsion weight. At this constant background K=s=0, so the complete derivative is
 DY[D_e eta]=(0,-2kappa B_e^-1 Tc,e^dagger W_e R_e eta).
Derivatives of B, Tc and W multiply the zero background K here; they have not been discarded on variable backgrounds. B_e retains the full coordinate congruence and original signed connection Gram factors.

The original curvature contribution annihilates the centered column at EVERY constant e. At omega=0 the five complementary endpoints give w_kl(z)=(1+z_k)(1+z_l)/4. With j_i=(z_i-z_i^-1)/2,
 w_kl(z)(z_k^-1-1)/h=-j_k(1+z_l)/(2h).
The centered coframe column is f_i=j_i xi/h. The curvature-link cross contraction has epsilon^(ijkl) j_i j_k (e_j wedge xi)(1+z_l), which cancels under i<->k. The coframe-curvature rows at omega=0 vanish directly. This proves C_h,e D_h,e=0 in all40 original rows, without assuming general GL(4) is a native symmetry.

Completing the ORIGINAL connection quadratic, whose convention is (1/2)c^T B_e c, gives
 H_e=I-2kappa Tc,e B_e^-1 Tc,e^dagger W_e,
 G_e=D_e^dagger(J2,e+J1,e DY_e)D_e=2kappa R_e^dagger W_e H_e R_e.
One direct normalization check is the h^2 density along D_h,e+h c:
 kappa<R_e eta,W_e R_e eta>+2kappa<Tc,e c,W_e R_e eta>+(1/2)c^T B_e c.
Its stationary c is -2kappa B_e^-1 Tc,e^dagger W_e R_e eta, giving density kappa<R_e eta,W_e H_e R_e eta> and Hessian factor2kappa. D_h=D_e+h^2 Dcent2; the possible Dcent2^dagger J0 contribution vanishes in this displacement-displacement contraction because J0 D_e=0. This is an all40 Schur calculation, not a torsion-only force substitution.

## Coordinate/internal conversion of the finite original blocks

For real physical momentum p (partial -> i p), define the COMPONENTWISE native bivector
 r_ij=(p_i^2 p_j-p_j^2 p_i)/2.
Then R_e eta=-i r_ij E eta. Set U=E^-1, r'_AB=U^i_A U^j_B r_ij and xi=E eta. Pulling BOTH face indices through U converts the original weight to v times the flat eta contraction. Pulling the connection through the original contorsion map converts B_e by its actual congruence, not by an assumed gauge invariance.

The accepted repeated/distinct original connection blocks give, for ANY antisymmetric r',
 D=10201/10300, Hd=9999/9991,
 G_e(p)=2kappa v[Hd d_g g+(D-Hd)K_g],
 d_g=(1/2)r_ij r_kl g^ik g^jl, (K_g)_ab=g^jl r_aj r_bl.
To check the contraction rather than assume covariance: the common diagonal part of the two block inverses is A=101/103; repeated-block all-ones coefficient B0=101/10300 and distinct-block coefficient E0=202/9991. Thus D=A+B0 and Hd=A+E0. Diagonal repeated/distinct faces give respectively D/Hd; offdiagonal contractions give B0-E0=D-Hd. The independent signed/permuted original six-coordinate connection components are those of the accepted B-block calculation. The coordinate pullback then gives the displayed g and K_g, including v. No coframe rotation has changed the componentwise native p_i^2 in r.

The bivector r=(p^2 wedge p)/2 is simple, where p^2 denotes the componentwise-square covector, not its metric norm. Consequently
 K_g g^-1 K_g=d_g K_g, trace(g^-1 K_g)=2d_g.
For d_g!=0, Pi=g^-1 K_g/d_g is a rank2 idempotent and
 g^-1 G_e=2kappa v d_g[Hd(I-Pi)+D Pi],
 det G_e=det(g)(2kappa v)^4 D^2 Hd^2 d_g^4.
The determinant identity extends polynomially to d_g=0. This does not establish any inverse at those momenta.

## Fourth temporal coefficient and its guarded ellipticity

Let tau=dt and ell=(0,k). The highest temporal part of r is p0^2(tau wedge ell)/2; there is NO p0^3 term because a face cannot have two temporal indices. Define
 alpha=g^00, beta=g^ab k_a k_b, gamma=g^0a k_a,
 d4=(alpha beta-gamma^2)/4,
 K4=[beta tau tau^T+alpha ell ell^T-gamma(tau ell^T+ell tau^T)]/4.
The degree-six constant-coframe symbol therefore has temporal degree at most4, with
 G4,e(k)=2kappa v[Hd d4 g+(D-Hd)K4].
At flat e this is exactly
 (kappa/2)diag(D|k|^2,-Hd|k|^2 I+(Hd-D)kk^T).

On a compact sufficiently small coframe neighborhood of the identity with v>0, g^00<0 and the spatial inverse block positive, alpha beta-gamma^2<=-c|k|^2. For example ||g-eta||<=1/4 implies ||g^-1-eta||<=1/3, alpha<=-2/3, beta>=2|k|^2/3 and hence d4<=-|k|^2/9. The rank2 projector for the simple bivector tau wedge ell is bounded uniformly on this compact coframe guard and |k|=1. The explicit two-eigenvalue factorization above then gives ||G4,e(k)^-1||<=C|k|^-2 for k!=0. This is a uniformly spatially elliptic INDEFINITE matrix, not a positive-energy statement, and it gives no low-frequency or variable-background inverse.

Only the frozen homogeneous degree-six symbol has been established in this note. Exclusion of lower-differential-order fifth or higher temporal terms requires the separate full variable-background jet audit, including the derivative of the Ward column.
