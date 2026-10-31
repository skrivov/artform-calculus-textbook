# The local Lorentz curvature-coframe candidate class

Let V be oriented real Minkowski four-space with eta=diag(-1,1,1,1), and W=Lambda^2 V. In the ordered basis (01,02,03,23,31,12), write a bivector as(K,J). The metric pairing and internal Hodge operator are

    g_W=diag(-I_3,I_3),
    star=[[0,-I_3],[I_3,0]], star^2=-Id,
    g_W star=[[0,I_3],[I_3,0]].                     (1)

Epsilon has lower0123=+1; raising its indices uses eta. This is the LORENTZIAN internal Hodge operator, not a Euclidean one or a spacetime mesh Hodge map. Both pairings in(1) are symmetric and invariant under SO^+(1,3).

**Invariant-pairing theorem.** Every real bilinear scalar coupling C(B,F) invariant under the simultaneous bivector Lorentz action is

    C(B,F)=alpha g_W(B,F)+beta g_W(B,star F).        (2)

Proof: spatial rotations act as the same SO(3) representation on K and J. Commutation with the three infinitesimal rotations forces each3 by3 block of the bilinear matrix to be a scalar identity: no off-diagonal entries survive, and all three diagonal entries coincide. Write the four block coefficients(a,b,c,d). Invariance under a single-axis boost and rotations gives d=-a and c=b. Therefore C lies in the span of g_W and g_W star. Conversely the metric and oriented epsilon contractions are Lorentz invariant. Every proper orthochronous Lorentz transformation factors into a boost sending e_0 to its image and a rotation stabilizing e_0; differentiating and exponentiating the generator identities supplies full connected-group invariance. The fresh216-equation/36-variable rational calculation checks rank34 and this two-dimensional kernel, not just a sampled finite subgroup. Reflections outside the chosen oriented group require a separate parity convention.

For a smooth nondegenerate realization with coframe one-forms e^I and independent Lorentz connection omega, define Sigma^IJ=e^I wedge e^J and curvature F=d omega+omega wedge omega. The classified candidate, with a separate volume coupling, is

    S[e,omega]=1/2 integral Sigma^IJ wedge(P F)_IJ
                         +lambda integral vol_e,
    P=alpha Id+beta star,
    vol_e=epsilon_IJKL e^I wedge e^J wedge e^K wedge e^L/24. (3)

Equation(3) is a CONDITIONAL interpretation of the derived contraction class, not a pre-existing installed native action or a proved limit of arbitrary pattern refinements. It specifies independent variables and assumptions. The coefficients, boundary prescription and quantum measure are not selected by the classification. A discrete face fold additionally requires dual/primal matching and quadrature witnesses; an integrated bivector paired with a based face log is not declared equal to(3).

Since star^2=-Id, for real(alpha,beta) not both0,

    P^-1=(alpha Id-beta star)/(alpha^2+beta^2).      (4)

Varying omega, with its boundary term retained, gives P D Sigma=0. The boundary one-form is

    Theta=1/2 integral_boundary Sigma^IJ wedge(P delta omega)_IJ. (5)

This term cannot be erased when defining boundary reports, sewing or sources. Equation(4) implies D Sigma=0. Write T^I=D e^I, so D Sigma^IJ=T^I wedge e^J-e^I wedge T^J.

**Nondegenerate torsion theorem.** D Sigma=0 implies T=0. In the coframe basis let i_J be contraction with the dual vector, and V=sum_J i_J T^J. Contract and sum J in the preceding equation. The first term gives(4-2)T^I=2T^I; the second gives T^I-e^I wedge V. Hence T^I=-e^I wedge V. Substitution into V gives V=-3V, so V=0 and T=0. This proves injectivity for every nondegenerate coframe. The independent24 by24 canonical-basis check verifies rank24. Degenerate coframes and complex chiral P require a different analysis.

At torsion zero the first Bianchi identity gives F^I_J wedge e^J=0, removing the alpha term from the coframe equation, not from the off-shell action, quantum phase or boundary one-form. For beta!=0, the remaining vacuum equation is

    (beta/2)epsilon_IJKL e^J wedge F^KL
       +(lambda/6)epsilon_IJKL e^J wedge e^K wedge e^L=0. (6)

This is the classical tetrad Einstein equation with Lambda=-lambda/beta in these conventions. The claim is for the smooth nondegenerate, independent-connection realization of(3), with its stated variational boundary conditions. It does not construct the smooth realization, prove refinement convergence, identify the physical Newton coefficient, solve a matter-sourced spacetime or establish quantum constraints. If beta=0 and lambda=0, the coframe equation becomes empty after torsion elimination; alpha alone does not select Einstein dynamics. This is a concrete law-selection distinction inside the admitted contraction class.

The generalized Hilbert-Palatini action is established background terminology. Our new programme result is the explicit native-profile hypothesis map plus invariant/variational classification and its refinement obligations. No external quantum-gravity theorem is imported. The local theorem cannot remove the existing curved Regge displacement/source defect: exact based Bianchi transport and an off-shell action symmetry were already proved to be different.

[Profile boundary](native-pattern-profile-and-parent-selection-boundary.md) · [Existing Bianchi/action defect](../../../../../../../coxeter-geometry/research/bianchi-action-defect-theorems.md) · [Holst's original action paper](https://arxiv.org/abs/gr-qc/9511026) · [Gielen and Oriti on the additional simplicity/volume constraints](https://arxiv.org/abs/1004.5371).
