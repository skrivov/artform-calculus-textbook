# Native torsion deformation, complete sources and a rough-family lift

Development1659,14 October2026. All inherited evidence and the initial plan were frozen before this formal derivation. This is a new, explicitly declared local action candidate on the existing native profile. Its coefficient is not selected by Artform syntax or by pattern incidence. A finite construction and a smooth comparison are not a full gravitational parent.

## Fields, domain and changed action

Use the original independent coframes E_i(n)=h e_i(n) and links U_i(n) in SO^+(1,3), with eta=diag(-1,1,1,1), det e>0 and the existing orientation/time branch. The four columns of e are e_i; g=e^T eta e is invertible. For the rough-family theorem use an even periodic lattice of fixed coordinate volume V. This is a bulk test, not a physical compact-time preparation. On a region with boundary the unassembled source formula below retains every endpoint; no boundary field is silently fixed.

Extend the original torsion antisymmetrically to all ordered i,j:

    t_ij(n) = T_ij(n)/h^2
            = [U_i^-1 e_j(n+i)-e_j(n)
               -U_j^-1 e_i(n+j)+e_i(n)]/h.
    tau = eta_IJ g^{ik}g^{jl} t_ij^I t_kl^J.
    C_h^T = (h^4/2) sum_n det(e) tau.                       (1)
    S_h^new = S_h^base + gamma_h C_h^T.                      (2)

Repeated indices in (1) are all ordered indices; the factor1/2 avoids double counting antisymmetric pairs. Take S_h^base to be the equal-weight candidate at lambda0, or any source-independent normalized finite interlaced combination in Development1658, at lambda0. Gamma_h is a new real, source-independent coupling. The new term is independent of lambda, so the original lambda-volume source remains unchanged when the base coefficient sum is1.

Under G_n in SO^+(1,3), e_i -> G_n e_i and U_i -> G_(n+i) U_i G_n^-1. Thus t_ij -> G_n t_ij, while g and det e are unchanged; (1) is exactly invariant. This proves the known vertex Lorentz symmetry only, not displacement/refoliation invariance. The contraction is real and indefinite, not a positive penalty or energy.

Finite shifts, transports, contractions and guarded matrix inverses are expressible in the declared continuous-value native profile. The earlier [native-profile boundary](../cycle162-post68-pattern-coframe-curvature-parent-and-retained-refinement/native-pattern-profile-and-parent-selection-boundary.md) explicitly excluded torsion-squared terms from its narrower bilinear-curvature classification. Thus adding (1) changes the physical-law ansatz; it is not forbidden by that classification and is not selected by it. Quadratic torsion interactions have continuum precedent in [Baekler and Hehl](https://arxiv.org/abs/1105.3504); that reference does not establish this discrete action, coupling or quantum limit.

With coordinate lengths h, dimensionless e and dimensionless links, t has dimension length^-1 and C_h^T has dimension length^2. Gamma_h must have dimension action/length^2 if S has dimension action. This matches the role of a gravitational curvature coefficient but does not determine its value.

## Exact first variation in every original field

Hold h fixed and put X_i=U_i^-1 delta U_i in so(1,3), so delta U_i=U_i X_i. Use primes only for the indicated endpoint. Direct differentiation gives

    delta t_ij = (1/h)[ U_i^-1 delta e_j(n+i)-delta e_j(n)
                      -U_j^-1 delta e_i(n+j)+delta e_i(n)
                      -X_i U_i^-1 e_j(n+i)
                      +X_j U_j^-1 e_i(n+j) ],             (3)
    delta g = (delta e)^T eta e + e^T eta delta e,
    delta g^-1 = -g^-1(delta g)g^-1,
    delta det e = det e tr(e^-1 delta e).
    delta C_h^T = (h^4/2) sum_n det e {
        tr(e^-1 delta e) tau
        + eta_IJ[(delta g^{ik})g^{jl}
                  +g^{ik}(delta g^{jl})]t_ij^I t_kl^J
        + 2 eta_IJ g^{ik}g^{jl}(delta t_ij^I)t_kl^J }.      (4)

Equations(3)-(4) retain determinant, both inverse metrics, both endpoint coframes and both link contacts. They are valid for arbitrary independent original sources; delta e=delta E/h restores the original E normalization. Differentiating them further retains mixed sources without installing a restricted variation.

For clarity, the periodic assembled form exposes every force. Define the antisymmetric covector

    Pi_I^{ij}(n) = det e eta_IJ g^{ik}g^{jl}t_kl^J.

The torsion part of (4) is exactly

    2h^3 sum_(n,i,j) Pi^{ij}(n) . [
        U_i^-1 delta e_j(n+i)-delta e_j(n)
        -X_i U_i^-1 e_j(n+i)].                            (5)

Consequently its coframe force multiplying delta e_j(n) is

    2h^3 sum_i [U_i(n-i)^-T Pi^{ij}(n-i)-Pi^{ij}(n)],       (6)

in addition to the local determinant/inverse-metric variation in (4). The link equation is the covector on every X_i in so(1,3)

    -2h^3 sum_j Pi^{ij}(n) . X_i U_i^-1 e_j(n+i).          (7)

Add gamma_h times these forces to the original base equations. Equation(7) is tested on all six independent Lorentz generators per link; it is not an unconstrained sixteen-component matrix variation. Equation(6) uses periodic reindexing only. On a boundary use (3)-(5) with the owned cells and their actual endpoint sources, retaining the corresponding boundary terms.

## Exact removal of the displayed alternating scale saddles

Use the published full stationary family, not just a restriction of its action:

    e_i(n)=q(n)t_i,   q(n)=1+epsilon chi(n),
    chi(n)=(-1)^n0,   U_i(n)=I,   |epsilon|<1.             (8)

Here t_i on the right are the four internal basis vectors, distinct from the two-index torsion t_ij. The coframes/inverses are bounded on every compact epsilon interval inside(-1,1), det e=q^4>0, and the admitted time/orientation branch is retained. Development1621 and the [interlaced theorem](../cycle162-post68-extended-loop-stationary-parity-and-state-control/interlaced-loop-parity-and-original-source-theorem.md) prove S_base=0 and its full first derivative zero at lambda0.

Now g=q^2 eta, t_0a=-2epsilon chi t_a/h for a=1,2,3, and t_ab=0 for spatial a,b. Each ordered 0a or a0 term has one negative inverse-metric factor. The local q^4 from det e cancels the q^-4 from the two inverse metrics. Summing the six ordered terms yields

    C_h^T = -12 V epsilon^2/h^2,
    d_epsilon S_h^new = -24 V gamma_h epsilon/h^2.         (9)

For every gamma_h !=0 and epsilon !=0 in this admitted interval, (9) is a nonzero derivative in an allowed original-field direction. Therefore that configuration is not a full stationary point of the changed action. This conclusion needs no gauge quotient or positivity assumption. At epsilon0 the torsion and all its first action derivatives vanish; the flat base configuration stays stationary at lambda0.

This removes the displayed one-parameter family away from its flat member. It does not prove removal of all16-parity configurations, absence of other rough stationary solutions, stability, a correct spectrum or physical state selection. In particular the positive coordinate diagnostic of Development1621 was +12 V epsilon^2/h^2 on this family. It is different from (1), whose Lorentzian contraction gives the negative sign in (9).

## Fixed smooth sources and a vanishing coupling

Let e(x;s),omega(x;s) be a fixed finite-dimensional smooth source family on a compact coordinate region, with all source derivatives through order m bounded in spatial C2, det e uniformly away from zero, and inverse coframes uniformly bounded. Sample E=h e and use exact transports for d+omega with the established sign convention. On boundaries require fields on a neighborhood containing the evaluated edges and retain all sources. Uniform Taylor expansion, including those fixed source derivatives, gives

    t_ij = D_i e_j-D_j e_i + O_(C^m_s)(h)
          = mathcal T_ij + O_(C^m_s)(h),
    C_h^T = C_cont^T + O_(C^m_s)(h),
    C_cont^T = (1/2) integral det e eta_IJ
                    g^{ik}g^{jl} mathcal T_ij^I mathcal T_kl^J d^4x. (10)

Indeed U_i^-1 e_j(x+h i)=e_j+h(partial_i e_j+omega_i e_j)+O(h^2). The guarded inverse/determinant operations preserve the source estimates. A left-cell quadrature of the resulting uniformly C1 integrand has error O(h). No periodic cancellation or second-order boundary claim is needed.

For source-independent gamma_h ->0, (10) proves gamma_h C_h^T ->0 with every fixed derivative through order m on these families. It preserves the base leading smooth action and those fixed sources, when that base limit exists on its stated hypotheses. It does not give uniform control over all lattice fields, high-frequency source directions or a quantum integration domain. At a torsion-free reference t_h=O(h), the value C_h^T is O(h^2); a generic first source is only O(h), and a generic second source is O(1). Value estimates cannot replace complete source estimates.

A concrete dimensional family is

    gamma_h = kappa (h/ell)^p,   0<p<2,   kappa !=0, ell>0. (11)

Here ell is a declared comparison length, not a universal minimum interval; kappa carries the required action/length^2 dimension. Then gamma_h ->0 while |gamma_h|/h^2 ->infinity. Equations(9)-(11) separate a vanishing smooth modification from a large force/phase on a fixed alternating amplitude. Every nonzero gamma_h already removes that exact saddle; the stronger rate is relevant to the prepared oscillatory test.

The full40-variable Hessian, interactions, matter/spin torsion, clock backreaction, nonzero lambda branches, physical coupling selection, constraints and measure remain to be derived for this changed candidate. A wrong finite symmetry or an unstable new sector could invalidate it as physics. Neither (9) nor (10) completes R2,R8 or R7.

