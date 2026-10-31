# Transported face averaging and the smooth modified action

13 October 2026. Development1620. This is an explicitly changed candidate in the same conditional continuous coframe/Lorentz profile. It is expressible using the admitted field, transport, wedge, scalar and finite-sum operations. Its averaging weights and interaction placement are model choices, not a physical selection theorem. The proof concerns its full action and every fixed finite source order, not a reduced rapidity or tensor action.

## The changed finite law

Retain E_i(x), U_i(x), the ordered holonomy H_kl(x), the curvature reading K(H)=-(H-H^-1)/2, the bivector pairing g, and P=alpha I+beta star from Development1614. Let B_ij(y)=E_i(y) wedge E_j(y). Matrix conjugation below denotes the equivalent Lorentz action on bivectors. For the term complementary to the curvature plane k<l, let

    T_k=U_k(x),   T_l=U_l(x),
    T_(k,l)=U_l(x+h k) U_k(x),
    T_(l,k)=U_k(x+h l) U_l(x).

These transports send the frame at x to the appropriate corner. Define

    Bbar_(ij|kl)(x) = (1/4) [B_ij(x)
      + Ad_(T_k^-1) B_ij(x+h k)
      + Ad_(T_l^-1) B_ij(x+h l)
      + (1/2) Ad_(T_(k,l)^-1) B_ij(x+h(k+l))
      + (1/2) Ad_(T_(l,k)^-1) B_ij(x+h(k+l))].         (1)

The diagonal corner has total weight1/4, split equally between its two paths. The action is

    Sbar_h = sum_x [sum_(i<j,k<l) epsilon^(ijkl)
                      g(Bbar_(ij|kl)(x),P K(H_kl(x)))
                                  +lambda det E(x)].    (2)

The six complementary terms and the original volume term remain. Every original corner coframe and edge transport is a variable of (2). No independent averaged bivector replaces them.

Under a vertex frame change G, a path transport transforms as T -> G_y T G_x^-1, and its endpoint bivector as B(y) -> Ad_(G_y) B(y). Each summand in (1) therefore transforms as Ad_(G_x); K(H_kl) transforms in the same base frame. The invariant pairing, star and determinant make (2) exactly Lorentz invariant at finite h, even for nonsmooth fields. Derivatives of the complete action consequently obey the same form of vertex Lorentz identity as before, with its new complete coframe and link forces. This proves neither a displacement identity nor the quantum Gauss constraints.

The rational weights1/4 and1/2 are admitted in the declared real continuous coefficient profile. There is no implicit division by2 or4 in a finite C8 palette, and no transfer of this law to such a palette is asserted.

## Uniform smooth expansion

Fix any finite source order m and a compact source domain. Assume source derivatives through total order m of e through spatial order2 and omega through spatial order3 exist continuously and have uniform bounds on a neighborhood of the fixed coordinate cube. The analogous periodic assumptions apply on a four-torus. Keep a common nondegenerate coframe branch when interpreting geometry. Sample E=h e and use the exact transports of d+omega. Constants below may depend on these bounds, fixed volume, couplings, source dimension and m, but not h.

Put b_ij=e_i wedge e_j and D_a B=partial_a B+[omega_a,B]. In the finite-source norm of Development1619, the expansions are

    Bbar_(ij|kl)/h²
       = b_ij + (h/2)(D_k+D_l)b_ij + O_m(h²),          (3)
    K(H_kl)/h²
       = F_kl + (h/2)(D_k+D_l)F_kl + O_m(h²).         (4)

For (3), an endpoint bivector transported back along one edge satisfies

    Ad_(U_a(x)^-1)b(x+h a)=b+h D_a b+O_m(h²).

This follows by the first-order transport equation and Taylor expansion. Either diagonal path has first correction h(D_k+D_l)b; their difference first occurs at order h² and is retained in the remainder. Inserting the four corner weights in (1) proves (3). No claim that the two paths coincide at finite h is used.

Here is an explicit derivation of (4). On a small coordinate neighborhood of the basepoint choose the radial gauge y^a omega_a(y)=0 by solving transport along each radial segment. This gauge has identity value at the basepoint. The transport integral equation controls its derivatives in the same finite-source norm. Differentiating the radial gauge condition gives

    omega_a(y)=integral_0^1 t y^b F_ba(t y) dt
       =(1/2)y^b F_ba(0)+(1/3)y^b y^c D_c F_ba(0)
                                                        +O_m(|y|³).

For completeness, y^b F_ba=y^b partial_b omega_a+omega_a in radial gauge; integrate the derivative of t omega_a(t y). At the basepoint omega=0, so partial F=D F there. This proves the displayed expansion, including its covariant interpretation after returning to the original gauge.

The radial gauge makes the two edges adjacent to the basepoint trivial transports. Along the remaining two oriented edges of the kl square the connection is O_m(h). Their ordered products differ from one minus the oriented line integral only by O_m(h^4). Direct integration of the expansion above gives

    integral_boundary omega
           = h² F_kl+(h³/2)(D_k+D_l)F_kl+O_m(h^4).

For example, the +l edge contributes h² F_kl/2+h³ D_k F_kl/3+h³ D_l F_kl/6, and the -k edge contributes h² F_kl/2+h³ D_k F_kl/6+h³ D_l F_kl/3. Our start-to-end transport convention is dU/ds=-omega_s U, so H is one minus this integral to the stated order. Forming -(H-H^-1)/2 proves (4). Gauge covariance transports the result back to arbitrary bounded smooth fields. Spatial omega derivatives through order3 bound the covariant second derivatives of F and the remainder; the finite-source norm controls every source coefficient. This is a non-Abelian derivation, not a commuting-loop approximation.

## Bulk cancellation and the boundary term

Define the signed continuum summand and full density by

    ell_(ij,kl)=epsilon^(ijkl) g(b_ij,P F_kl),
    L=sum_(i<j,k<l) ell_(ij,kl)+lambda v,   v=det e.

Because D preserves g and P, the first correction from (3)-(4) is an ordinary derivative of the scalar pairing. Thus each cell contribution is

    h^4 [L(x)+(h/2) sum_(ij,kl)(partial_k+partial_l)
                                                    ell_(ij,kl)(x)]
                                                        +O_m(h^6). (5)

Write S=integral L over a fixed unit coordinate cube. The left-endpoint Riemann sum has the more precise expansion

    h^4 sum_x L(x)
       = integral L -(h/2) sum_(a=0)^3 integral partial_a L
                                                        +O_m(h²).

Indeed, integrate L(x+y)=L(x)+sum_a y^a partial_a L(x)+O_m(h²) over each cube and sum, then replace the derivative sums by their integrals with O_m(h) error. Apply this also to the first correction in (5). Complementarity of i,j,k,l gives

    Sbar_h-S=-(h/2) B_boundary+O_m(h²),                  (6)
    B_boundary = sum_(ij,kl) integral (partial_i+partial_j)ell_(ij,kl)
                          +lambda sum_a integral partial_a v.       (7)

Each derivative integral is its difference of two opposing face integrals. Equation (6) is the boundary-aware statement; the action on a general cube has not automatically become second-order accurate. On a periodic domain B_boundary=0, so

    sup_Z |partial_z^a(Sbar_h-S)| <= C_m h², |a|<=m.    (8)

On a cube the same statement holds if the boundary term and its required source derivatives vanish, or for the comparison Sbar_h+(h/2)B_boundary when that explicit continuum boundary correction is included. The latter is a corrected comparison functional; it is not silently installed as a native boundary law. Interior-supported source derivatives of positive order may satisfy this cancellation even when the value at source zero has a nonzero boundary term. They must be checked at the actual boundary preparation.

The changed interaction relative to the original lower-basepoint action has leading difference

    Sbar_h-S_h=(h/2) integral sum_(ij,kl) epsilon^(ijkl)
               g((D_k+D_l)b_ij,P F_kl)+O_m(h²).         (9)

It comes from changing coframe placement and transport. It is not obtained by changing the curvature reading to a logarithm, deleting an equation or assuming a nonlinear gauge correction. Equation (9) explains which first-order bulk error the averaging removes. Higher terms and the finite-spacing interaction must still be tested.

The boundary qualification has an actual nondegenerate example. On the unit cube take alpha=lambda=0, beta=1, e0=(1+x0)t0, e1=t1, e2=t2, e3=t3 and omega=x2 T23 dx3. Only F23=T23 is nonzero. Its rotations fix the01 bivector, and that bivector is constant along the23 face, so averaging changes no active summand. The exact action is

    Sbar_h=h^-2 sin(h²)(3/2-h/2),   S=3/2.

Its error is -h/2+O(h^4), agreeing with (6)-(7). Every coframe has determinant1+x0>0. This off-shell boundary example is not periodic and is not a stationary gravitational solution. It shows why a periodic second-order estimate cannot be silently transferred to a general region with fixed physical boundary data.

## Interacting comparison and quantum scope

For a periodic smooth diffeomorphism pullback family, or a boundary-supported family for which the derivatives of (7) vanish, differentiating (6) gives the complete third-order Ward comparison O(h²), with the same nonlinear sampling contacts as Development1619. Require the full three-source smoothness hypotheses. This is not automatically the bare on-shell vertex of the new law; R8 reconstructs that law's full lattice waves and tangent generator separately.

On families satisfying (8), the real fixed-history phase and finite-order source estimates of Development1619 improve by replacing h with h². For example the phase difference is bounded by C h²/|hbar|, and at order m by C'_m h² sum_(j=1)^(m+1)|hbar|^(-j). The common-measure comparison bound improves only on a good set for which the new hypotheses and boundary conditions actually hold. No rough-history tail, compatible quantum measure, normalization gap, physical constraint space or matter law is provided by (8).

The changed action is therefore a better smooth periodic discretization within this candidate class if its full equations and source interpretation are retained. It remains a conditional classical action. Native physical selection, exact/limiting constraints, composition with detail, quantum amplitudes and the full gravitational parent remain open.
