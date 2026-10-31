# Exact native lattice cut form and a strongly nondegenerate selected TT sector — ROOT M160

Finished manual candidate, 30 October 2026, UNREVIEWED pending distinct Sol review. Fresh M159 MAIN whole check590338 passed before this source. ROOT and Sol exchanged the contour/current strategy before freeze; that exchange is orientation, not finished-byte review. No mathematical evaluator or numerical experiment. Source calculation0, reception preparation0 at freeze. This result concerns a specified linear slow sector of the original flat lattice Hessian, with its declared coframe trace. It does not identify that trace with the complete physical constructor.

## 1. Original input and sector

Use the complete original finite-word quadratic183dbf9399f5812af0cf6531725bda7319525b1303b0ec87d97e70d76be8463d/10394, freshly read c9fb00, and its physical Hessian and exact reconstruction as proved in the reviewed slow-contour sourceeec52c8467f0d1f50e016e6208691fba2c8a26fb64533d677cb5b077d8315412/16303, freshly read7febbf. Its mandatory scope01c258f611c478294dd5d1fbcce248068dfe48ef7ca092b9fb54b8de979401f3/5313 was freshly read e1fa4c. Their original signed coordinate pairings, physical connection scaling and incoming adjoints are retained. No canonical-normal output rescaling is introduced.

Fix a compact physical spatial annulus 0<r0<=rho=|k|<=r1 and the exact small-positive-h slow solution map of that source:
 w_h[y](t,k)=(1/(2pi i)) integral_C exp(lambda t) E_h(lambda,k)L_h(lambda,k)^-1 B0(lambda,k)F_h(k)^-1 y(k) d lambda. (1)
C is one circle |lambda|=L enclosing the entire limiting slow cluster; the28 complementary inverse is holomorphic on its whole disk, and every other factor in(1) is bounded on C with every fixed k derivative. The exact full40 identity J_h E_h=W_h L_h gives all original rows J_h w_h=0. The declared actual metric trace is y=(q,2p,0,0,0,0), namely TT metric and its time derivative plus sixteen zero total-Coulomb coordinate jets. These are actual coframe projections, not zero jets of the constructor coordinate map alone. E_h reconstructs the independent connection as well as coframe. The limit contains the normalized leading coordinate flow and need not be an unflowed TT wave away from the cut.

Take first smooth real centrally-even annular TT seed pairs(q,p), as admitted in the original leading construction. Fourier reality is imposed on the reconstructed fields; derived vector components and evolved fields need not be centrally even. Use intrinsic TT projectors or a fixed finite angular cover, not a fictitious global polarization frame. Below the Hilbert completion is solely a convenient data space for this selected linear theorem.

## 2. Exact temporal cut form from the original Hessian

In original physical coordinate fields, write the finite-range self-adjoint Hessian
 J_h=sum_(r=-R..R) A_r(h,S_sp) S0^r,  A_-r=A_r^(dagger_sp). (2)
Here R is finite and independent of h; spatial shifts, all original transport contacts, eta signs and connection normalization belong to the matrices A_r. The pairing is the coordinate dual pairing, not a positive internal Lorentz pairing. For real spatial lattice fields define <x,y>_h=h^3 sum_(z in h Z^3) x(z)^T y(z). Define the cut after time n h by
 Omega_h(n;x,y)=h sum_(r=1..R) sum_(j=0..r-1)
 [<x_(n-j),A_r y_(n+r-j)>_h-<y_(n-j),A_r x_(n+r-j)>_h]. (3)
All necessary temporal halo values are supplied by(1). For Schwartz fields these sums converge absolutely. Shifting the inner index in(3), its difference from the preceding cut telescopes to
 Omega_h(n)-Omega_h(n-1)
 =h[<x_n,J_h y_n>_h-<y_n,J_h x_n>_h].                    (4)
The A0 contribution cancels after the spatial transpose; the negative-r terms are precisely the adjoints of the remaining earlier-cut terms. Thus(3) is conserved at every original lattice cut for two exact full40 fields. This is an exact finite-h statement, not conservation modulo a Taylor remainder.

To identify the normalization with the native integrated presymplectic current, start with the original action's h^4 cell measure. Antisymmetrizing its two first variations gives the right side of(4) with sign x Jy-y Jx; temporal summation by parts groups each coupling between the two sides of the cut exactly once, giving(3). Spatial shifts may be reindexed because the products are summable. Equivalently, any other finite-range integrated current obtained from that same first-variation identity differs by a quantity whose cut difference is identically zero for arbitrary compact-time test sequences. Locality makes that difference zero at a cut outside their temporal support, hence zero at every cut. Spatial-current improvements have zero full-space sum. A density total difference changes the potential by an exact field variation and changes no antisymmetrized second variation. These facts identify the full-space linear current; they do NOT erase an owned finite spatial corner, identify distinct finite boundary prescriptions, or equate arbitrary nonlocal conserved bilinear forms.

## 3. Uniform continuum limit without bounding singular stencil coefficients separately

The individual A_r can contain negative powers of h. Estimating those terms separately would not justify a limit. Instead compute their exact combined temporal boundary symbol. Complexify bilinearly, pair x(t,-k)=exp(lambda t)a(-k) with y(t,k)=exp(mu t)b(k), and set J_h(z,k)=sum_r A_r(h,k)exp(hrz). Spatial transpose gives A_r(h,-k)^T=A_-r(h,k). Summing the finite geometric series in(3) yields
 Omega_h(n;x,y)=exp((lambda+mu)n h) a(-k)^T C_h(lambda,mu,k)b(k),
 C_h(lambda,mu,k)=h [J_h(mu,k)-J_h(-lambda,k)]
                         /[1-exp(-h(lambda+mu))].           (5)
This identity is initially read away from a zero denominator and then extended analytically. Indeed sigma=lambda+mu divides the numerator identically:
 [J_h(mu,k)-J_h(-lambda,k)]/sigma
 = integral_(0..1) (partial_z J_h)(-lambda+s sigma,k) ds. (6)
For |lambda|,|mu|<=L choose h L<pi, so the other denominator zeros sigma=2pi i m/h lie outside this product disk. The factor h sigma/[1-exp(-h sigma)] is analytic and tends uniformly to1, including sigma=0. The exact physical J_h has a removable h expansion, uniformly with z and fixed k derivatives on each bounded disk, from the original finite words. Hence(5) is jointly bounded and converges uniformly there to
 C_0(lambda,mu,k)=[J_0(mu,k)-J_0(-lambda,k)]/(lambda+mu), (7)
with the derivative value at lambda+mu=0. This retains all cancellations of singular stencil coefficients. It uses neither simple roots nor a diagonalization of the slow matrix.

Insert the two contour formulas(1) into(3), or equivalently into(5). Their contour matrices converge uniformly, as do C_h and the finite trace inverse F_h^-1. The resulting double-contour integral therefore converges uniformly in k to its h=0 value. On the fixed annulus every fixed angular/Cartesian k derivative obeys the same argument. The leading current is exactly the original continuum coefficient current because(7) is its Green concomitant with the same physical normalization, not a newly supplied continuum action.

## 4. Spatial sampling, leading value and bounded operator

Choose also h r1<pi. Bandlimited spatial fields and their shifts then obey exact sampling Parseval: their h^3 lattice inner product equals the full-space integral, since the Fourier support of each product lies inside the first nonzero reciprocal-lattice radius2pi/h. This can first be proved for smooth compact spectra by Poisson summation and then extended in L2 by its isometry. Thus the double-contour form is a bounded Fourier-multiplier bilinear form on the TT data, with no unaccounted spatial lattice factor. No nonlinear mass tail is put into this bandlimited Hilbert space.

Let H be the real Hilbert space of real centrally-even TT pairs(q,p) with spectral support in the annulus, with norm squared ||q||_L2^2+||p||_L2^2 and the standard full symmetric-tensor contraction. The smooth admissible data are dense. The current has a bounded real skew-adjoint Riesz operator K_h on H. If its unrestricted multiplier does not preserve central evenness, its operator on H is the orthogonal compression Pi_even K_h Pi_even. Compression has norm at most one and preserves the following uniform convergence. Uniform symbol convergence from section3 proves
 ||K_h-K_0||_(H->H) -> 0.                                (8)
This is operator-norm convergence on an infinite-dimensional fixed-band data space, not merely convergence on each chosen wave packet.

The original native leading currentb07b424fae0bb116d99f42c2718f27764d41ee65a7d2c1d4aaa312dfc427b74b/10912, freshly read e317e5, gives
 Omega_0((q1,p1),(q2,p2))
 =-(1/2) integral_(R3) [q1:p2-q2:p1] dx.                 (9)
Here the actual metric time derivative is2p, coframe spatial derivative q/2, and the independent connection is the leading torsion-free graph at this cut. Zero coordinate jets through3 make these initial native fields agree with the admitted original leading cut; their later coordinate flow does not change(9). The sign and factor agree with that original geometry/momentum pair, which is -||q||^2/2. In particular, with Omega_h(x,y)=<x,K_h y>_H,
 K_0=[[0,-I/2],[I/2,0]],  ||K_0^-1||=2.                 (10)

## 5. Exact small-h nondegeneracy and limits of the result

Put delta_h=||K_h-K_0||. For all sufficiently small positive h, delta_h<1/2. Factor K_h=K_0[I+K_0^-1(K_h-K_0)]. The Neumann series then gives a bounded inverse and
 ||K_h^-1|| <= 2/(1-2delta_h).                            (11)
Consequently the pullback of the EXACT native conserved lattice current is strongly nondegenerate on this selected TT data space. It has no radical within H, and the associated flat linear two-form is closed because its coefficients are constant in the data. Its finite-h exactness comes from(1)-(4); its nondegeneracy follows from the uniform contour estimate rather than a claim that the finite-h current equals its continuum coefficient.

For fixed h the spatial sums defining(3) remain meaningful on this completion: finitely shifted L2 sequences have summable bilinear products by Cauchy-Schwarz, and the bandlimited solution map is bounded on each finite enlarged time slab. The operator extension agrees with the original Schwartz cut sums by density. Conservation is asserted at actual lattice cuts; no inference from h-periodicity to continuous-time constancy is needed.

This proves a strong symplectic sector for a declared exact linear slow family of the original lattice candidate. It does not prove that the complete physical scalar/Navier, lapse/shift, positive-frame and link prescription equals this zero-total-Coulomb trace. It does not determine the radical of the full solution space, quotient all gauge/refoliation directions, remove fast roots, prove positive energy or a unitary quantum representation, continue to nonlinear amplitudes, or establish any h-series convergence. The next R8 physical-trace comparison and R7 full physical radical/finite-corner questions remain open. The Hilbert completion used here is a linear data norm, not a physical quantum state space.
