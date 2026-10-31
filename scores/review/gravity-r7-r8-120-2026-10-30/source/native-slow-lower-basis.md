# Lower coordinate basis in the slow-contour source — additive convention

The frozen source uses LOWER coordinate variables chi_mu throughout its Coulomb metric decomposition, beginning with m_mu nu=xi_mu chi_nu+xi_nu chi_mu. In sections2-6 its D0 must therefore be read as D0_lower=D0_upper eta, eta=diag(-1,1,1,1); the superscripted chi in the quotation of the original highest-time N formula denotes the original upper variable, not an additional identification. This note makes that basis conversion explicit; it changes no physical field, root, trace target or frozen byte. New scientific calculation0/receiver0; ROOT requested this notation clarification during distinct review.

If G2_upper and C_upper are read directly from the original coordinate-map authority, the matrices used in the frozen source are
 G2_lower=eta^T G2_upper eta,
 C_lower=eta^T C_upper,
 (C0_lower,C1_lower)=eta^T(C0_upper,C1_upper).
These relations also follow directly by substituting D0_lower in the displayed D0^dagger(J2D0+J1DY[D0]) and its TT mixed pairing. The genuine incoming formal transpose remains the original (-lambda,-ik) transpose; eta is a constant real matrix, so there are no differentiated coefficient or endpoint terms from this change of basis.

Every G_j and C1 in the entire Cauchy polynomial B0 is in this LOWER basis, as are all four initial chi jets and the trace F_h. In particular one must not insert upper-coordinate G_j into that polynomial with lower chi data. With Q=diag(I2,eta), L_lower=Q^T L_upper Q, E_lower=E_upper Q, W_lower=W_upper Q; the exact identity J_h E=W L is preserved. The twenty-jet data transform by eta in each of their four coordinate-jet slots. Both the Cauchy polynomial and the recovered trace transform accordingly, so the limiting trace is still the identity in one consistent basis.

The displayed highest-time A4 has no temporal-spatial off-diagonal entries. Hence eta^T A4 eta=A4, explaining why its displayed diagonal and uniform inverse are unchanged. The determinant changes only by det(eta)^2=1. Thus the degree20 count, common contour, full-row reconstruction, uniform trace inverse and the O(h2) cut comparison are invariant. This does not resolve the separate original physical-trace or scalar/Navier matching obligations; all frozen scope restrictions remain.
