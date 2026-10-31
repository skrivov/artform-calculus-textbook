# Covariant coframe cell action and a smooth source limit

A local cubical action can realize the coframe/connection contraction admitted in Development1612 while preserving exact local Lorentz covariance. Its values and first and second comparison-source derivatives converge to that conditional continuum action at rate O(h) on uniformly smooth sampled families. This provides a classical consistency bridge for a native finite profile. It does not derive the physical law from the calculus, construct the quantum measure, or prove convergence of stationary points.

## Finite coefficient profile and its action

Let the coordinate region be the oriented unit4cube, partitioned into N^4 cubes of side h=1/N. Each vertex x carries four internal vectors E_i(x), i=0,1,2,3, with det E(x) nonzero on the admitted coframe branch. Each positively oriented edge x to x+h i carries U_i(x) in SO^+(1,3). Reversed edges use the inverse. The finite carrier has the actual vertex/edge/face/cell incidences, coordinate orientations and child ancestry. Continuous coefficients belong to the conditional field profile already admitted; they are not derived from a finite palette.

Transport sends a vector at the start to a vector at the end. For the positively oriented ij loop based at x, i<j, define

    H_ij(x)=U_j(x)^-1 U_i(x+h j)^-1 U_j(x+h i) U_i(x).

Define the Lie-algebra curvature reading

    K(H)=-(H-H^-1)/2.                              (1)

Because H^-1=eta^-1 H^T eta, K obeys K^T eta+eta K=0. It is defined globally on this matrix group, conjugation-equivariant, and odd under loop reversal. The leading minus sign is tied to vector parallel transport dU/ds=-omega_s U. It is essential for K(H_ij)/h² to approach the curvature of d+omega.

Convert Lie-algebra matrices to bivectors by X^IJ=X^I_L eta^LJ. Use the root bivector metric g of signature(---+++), the oriented internal star with star²=-I, and P=alpha I+beta star for fixed real alpha,beta with alpha²+beta²>0. For i<j put B_ij=E_i wedge E_j. With epsilon^{0123}=+1 in coordinate indices, define

    S_h(E,U)=sum_cells c at x [
       sum_(i<j,k<l) epsilon^{ijkl} g(B_ij(x),P K(H_kl(x)))
       +lambda det E(x)].                         (2)

Only the six complementary ordered pairs contribute to the inner sum. There is no additional1/2. This normalization follows by writing Sigma^IJ=e^I wedge e^J=sum_(i<j) B_ij^IJ dx^i wedge dx^j and F=sum_(k<l) F_kl dx^k wedge dx^l. Since g(B,F)=B^IJ F_IJ/2, equation(2) approximates exactly

    S(e,omega)=1/2 integral Sigma^IJ wedge(PF)_IJ
                         +lambda integral det(e) d^4x. (3)

All four coframe columns and all six face sectors belong to the action even if a diagnostic family makes some terms zero. A cube uses the six lower-basepoint plaquettes and its basepoint coframe; this is a specified one-sided quadrature, not an average over its24 faces. Other quadratures need their own multiplicity and transport witnesses.

Under arbitrary vertex frames G_x in SO^+(1,3), take E_i(x) to G_x E_i(x) and U_i(x) to G_(x+h i) U_i(x) G_x^-1. The internal factors telescope in H, giving H_ij to G_x H_ij G_x^-1. Both g and star are preserved and det G_x=1, so (2) is exactly invariant. This algebraic invariance is valid at finite h and for nonsmooth coefficients. It does not establish diffeomorphism invariance or closure of all gravitational constraints.

The profile uses existing finite incidence/field, ordered product, inverse, wedge, scalar contraction and fold constructions with their law witnesses. Its choice of smooth Lorentz values, curvature reading, quadrature and alpha,beta,lambda is additional physical/model data. An expression of (2) in the native calculus is therefore a candidate finite action, not a derivation of its unique physical selection.

## Off-shell Lorentz variational identity

Let pi_(v,i) be the coframe derivative of the complete finite action and p_l its right-trivialized edge derivative at the terminal frame:

    delta S_h=sum_(v,i) pi_(v,i)(delta E_i(v))
                          +sum_edges <p_l,delta U_l U_l^-1>.

The nondegenerate invariant pairing identifies the Lie algebra dual; p_l is the derivative of the whole action, including every incident plaquette. It is generally not a bare face bivector. Define J_v by

    <J_v,epsilon>=sum_i pi_(v,i)(epsilon E_i(v)).

Infinitesimal vertex covariance gives, identically off shell,

    J_v + sum_(t(l)=v) p_l - sum_(s(l)=v) Ad_(U_l^-1) p_l=0. (4)

Indeed delta U_l U_l^-1=epsilon_t-Ad_Ul epsilon_s. Substitute in delta S_h and use invariance to collect the coefficient of each independent epsilon_v. It vanishes because S_h is invariant. The coframe term is necessary; deleting it before deriving the equations changes the identity. For this finite generating function pi is a variational coframe force. Identification with physical boundary coframe momentum still requires the boundary/bulk and polarization analysis of the R8 cell-parent programme. Equation(4) is an exact Lorentz Noether identity, not a constructed quantum Gauss operator or the Hamiltonian constraint algebra.

## Uniform classical and source consistency theorem

Let z range over a fixed compact comparison domain contained in an open source set. Let e_i(x,z) and omega_i(x,z) be real smooth coefficient fields on a neighborhood of the closed coordinate cube. Assume that e and its first spatial derivatives, and omega and its spatial derivatives through order2, have uniformly bounded source derivatives through total order2. Continuous mixed derivatives at these orders suffice. For interpretation as geometric coframes, also keep det e away from zero on the declared branch. The matrix norm, compact domain, these bounds and the fixed coefficients may enter constants. They are independent of h.

Sample

    E_i(x,z)=h e_i(x,z)

and use the exact path transports of d+omega on every edge. Then for every source multiindex a with |a|<=2 there is a common finite C such that

    sup_z |partial_z^a[S_h(E(z),U(z))-S(e(z),omega(z))]| <= C h. (5)

The theorem includes pure second and mixed source derivatives. A variation parameter for any fixed uniformly smooth coframe or connection direction may be included among z, so (5) also proves directional first/second variation consistency within those bounded families. It is not a bound uniform over arbitrary lattice directions whose gradients grow with1/h.

Proof: work in the norm

    ||A||_(z,2)=sum_(|a|<=2) sup_z ||partial_z^a A||/a!.

The Leibniz formula makes this norm submultiplicative. The edge transport integral equation and its Picard series converge in this norm, bounded by exp(h ||omega_i||_(z,2)). Taylor expansion in the spatial edge coordinate, with the stated bounded derivatives, gives uniformly

    U_i(x)=I-h omega_i(x)+h²[omega_i(x)^2-partial_i omega_i(x)]/2+O_(z,2)(h³).

The inverse is the corresponding reverse transport. Insert these expansions at x and shifted vertices into the four-edge word. All order-h terms cancel; the order-h² result is

    H_ij=I-h²[partial_i omega_j-partial_j omega_i
                                  +omega_i omega_j-omega_j omega_i]+O_(z,2)(h³)
        =I-h² F_ij+O_(z,2)(h³).                 (6)

This also fixes the sign without relying on a convention from a scalar example. To check the remainder, each shift uses a second-order spatial Taylor bound in the same source norm, and a product of four uniformly bounded factors preserves the O(h³) estimate. The inverse of H is uniformly bounded for sufficiently small h; H^-1=I+h²F_ij+O_(z,2)(h³). Consequently

    K(H_ij)=h² F_ij+O_(z,2)(h³).                (7)

B_ij=h² e_i wedge e_j exactly, and det E=h^4 det e exactly. Thus each cell summand differs from h^4 times the continuum density at its basepoint by O_(z,2)(h^5). There are N^4=h^-4 cells. The density has a uniform spatial Lipschitz bound in the same source norm, by the assumed derivatives of e and omega. Its basepoint Riemann sum differs from the integral by O_(z,2)(h). Adding both estimates proves (5). End of proof.

The proof is non-Abelian: the commutator in(6) is retained. Noncompactness of SO^+(1,3) is controlled here by the explicit bounded smooth comparison family. There is no uniform bound over all quantum configurations or all Lorentz boosts. Arbitrary vertex gauge transformations preserve the exact finite action, but the estimate is stated in a chart with controlled field/source bounds; an unbounded or rapidly varying family of gauge transformations does not inherit the same constant automatically.

## What refinement this establishes

Exact transports obey edge subdivision by ordered multiplication. The sampled coframes and their coordinate scales have actual ancestry from the same smooth field. Complementary dual areas scale as h², four-volumes as h^4. Adjacent stencils derive from the same admitted interpolation, so this consistency family has a common geometric origin. A freely assigned fine canvas does not acquire that interpolation from its individual coframe tests.

For any two sufficiently small nested sizes h and h', equation(5) gives the value/source defect bound C(h+h') between their actions on this common smooth comparison family. Exact equality at finite scales is not required for this off-shell consistency theorem. Exact integration or stationary elimination of arbitrary fine detail is a different comparison: it may induce new action and source terms. The R8 curved-cell example tests precisely that distinction on an explicit comparison manifold.

For the special constant Abelian family omega=rho x^0 dx^1 K_01 and e=diag(1,1,b,1), one has H_01=exp(-rho h² K_01), all other face curvatures zero, and (2) becomes

    S_h=b h^-2 sinh(rho h²)+lambda b.           (8)

The continuum result is b rho+lambda b. Expansion gives

    S_h-S=b rho³ h^4/6+O(h^8).                 (9)

On a fixed bounded rho/source family the same O(h^4) rate holds through second source order. This improved rate is special to the constant commuting family; it is not substituted for the general O(h) bound. The unit spatial coordinate area, dual23 area b h², curvature01 area h² and h^-4 cell count are all included in(8). Time-only subdivision with fixed other lengths instead gives b n sinh(rho/n)+lambda b and an O(n^-2) error.

For real |rho|<=R the remainder after the linear term obeys

    |sinh t-t| <= |t|³ cosh|t|/6,

from Taylor's integral remainder and the vanishing quadratic term. Thus the magnitude of the curvature defect in(8) is at most |b| |rho|³ h^4 cosh(R h²)/6. Differentiating the analytic series on a fixed compact source family bounds the first and second source errors with the same h^4 factor. No on-shell claim is made: this coframe and independent connection generally have nonzero torsion and coframe Euler force.

## Boundary amplitude and remaining physical requirements

Equation(5) gives convergence of phases and their first/second source coefficients only for fixed smooth histories and fixed nonzero hbar. It gives no dominated convergence under a path integral over unbounded, rough histories. Even pointwise convergence of exp(i S_h/hbar) cannot select compatible measures, physical states, zero modes, gauge treatment or constraint domains. R7 must supply these and the control needed to exchange refinement with integration and differentiation.

Nor does (5) imply convergence of critical points. Oscillatory lattice modes, null Hessians and insufficient compactness can defeat that inference. R5 must establish a physically selected family with uniform bounds, and R6 must extend the exact Lorentz identity to the required gravitational constraint and slicing structure. Native selection of the action, matter coupling and the full quantum parent remain open. R1 induced terms, R3 physical clocks and R4 update realizers remain active obligations.

There is established work on lattice Palatini geometry. Kur and Glasser's [Discrete Gravity with Local Lorentz Invariance](https://arxiv.org/abs/2202.02486) presents a lattice discretization preserving Lorentz symmetry and symplectic structure. Reisenberger's [left-handed simplicial action](https://arxiv.org/abs/gr-qc/9609002) includes a hypercubic counterpart in a Euclidean Plebanski setting. Their abstracts establish relevant precedence; the present proof and conventions are self-contained and do not import either paper's detailed equations or continuum theorem. Generic Lorentz-invariant gravity discretization is not claimed as a new invention.

All824 restrictions, accepted150/180, block3 30/60, checkpoint068/cycle162 OPEN and GR001–GR743 remain. Astra T1/T2 are open. The result is a conditional source-consistent classical realization of a native candidate, not completion of the full gravitational parent or quantum gravity.
