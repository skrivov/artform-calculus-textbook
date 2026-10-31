# A common Weyl algebra and a controlled native stable-band spacing limit — UNREVIEWED

ROOT manual candidate, M166,30 October2026. Source science0/description0. Current qualified M165 state authenticated284e1f; previous goal turn PROGRESS. No whole-MAIN replay or new physical branch selection is claimed. This candidate extends the distinctly reviewed M163/M164 fixed-band results, whose source/read pins are stated below. Mathematics is manual; tools only read, authenticate and preserve text. ROOT shared the prospective Darboux strategy with Sol before freeze; that is orientation, not distinct finished-byte review.

## 1. Accepted native hypotheses and the gap addressed

Work on the SAME full Fourier-real TT pair Hilbert space V on a fixed compact off-axis band0<r0<=rho<=r1, max|ki|<=(1-epsilon)rho. Keep all original normalizations and a specified hbar>0 independent of h. The accepted exact native linear branch supplies bounded real operators K_h,B_h,H_h=K_h B_h with
K_h*=-K_h, B_h*K_h+K_h B_h=0, H_h*=H_h>=cI>0,
K_h->K0, B_h->B0, H_h->H0 in operator norm,
K0=[[0,-I/2],[I/2,0]], B0=[[0,2I],[-rho^2 I/2,0]],
H0=diag(rho^2 I/4,I).
The inverse bounds are uniform for sufficiently small positive h. Its exact original forty-row solutions have time translation T_h(t)=exp(tB_h), including the actual native lattice step t=h.

The accepted quantum theorem supplies J_h, positive bounded covariance mu_h=Omega_h(.,J_h.), and a Gaussian state omega_h on the Weyl C*-algebra A_h with
Omega_h(x,y)=<x,K_h y>,
W_h(x)W_h(y)=exp[-i hbar Omega_h(x,y)/2]W_h(x+y),
omega_h(W_h(x))=exp[-hbar mu_h(x,x)/4].
All mu_h are equivalent to the fixed native norm; mu_h->mu0 in bounded-bilinear-form norm, with mu0(q,p;q,p)=integral[rho|q|^2/4+|p|^2/rho]. Each state is invariant under alpha_h,t W_h(x)=W_h(T_h(t)x), with the positive Fock implementer and declared Heisenberg sign of M164.

Fresh complete inputs: M163 sourcee53a2a95/14591 read58f157 and distinct review6b636371/11081 read8ef34f; M164 source69bb9cb8/10328 read13ba67 and distinct review91267211/9861 read0343e1, ONLY jointly with mandatory sign qualificationcbdebff1/2560 read22d82b. The rejected auxiliary review identity Omega(Jx,y)=+mu(x,y) is not a premise: the correct identity is Omega(Jx,y)=-mu(x,y). All five actual ROOT request/result reads were saved before display. The sources' earlier acceptance and original native derivations retain their precise scopes.

M164 proved corresponding-label covariance convergence but left the varying symplectic algebras unidentified. The present candidate constructs an explicit identification, then proves weak-* convergence of states and compact-time correlation convergence on one algebra. It does not establish full physical refinement.

## 2. An explicit real near-identity symplectic identification

Set A_h=K0^-1 K_h=I+D_h. Since ||K0^-1||=2 and K_h->K0, shrink the allowed spacing so ||D_h||<=delta<=1/2. Define by an ABSOLUTELY operator-norm-convergent binomial series
R_h=(I+D_h)^(-1/2)=sum_(n>=0) binom(-1/2,n) D_h^n.       (1)
This is the analytic branch near I. It is NOT a positive-square-root assertion about the generally non-self-adjoint A_h in the original Hilbert metric. The series has real coefficients, so R_h preserves the real space V and its Fourier reality. It acts within the fixed band. Its inverse is the convergent binomial series(I+D_h)^(1/2), as follows by absolutely convergent Cauchy products. Both commute with A_h and
R_h^2 A_h=I,
||R_h-I||<=(1-delta)^(-1/2)-1,
||R_h-I||->0, ||R_h^-1-I||->0.                           (2)

The crucial adjoint identity follows directly from the TWO skew forms:
A_h* K0=K_h* (K0^-1)* K0=K_h=K0 A_h.
Therefore D_h* K0=K0 D_h. By induction and norm convergence, every real-coefficient series in D_h has the same K0-adjoint property, in particular R_h* K0=K0 R_h. Consequently
R_h* K_h R_h=R_h* K0 A_h R_h
            =K0 R_h A_h R_h=K0.                         (3)
Thus Omega_h(R_h x,R_h y)=Omega0(x,y) exactly. Neither a finite-dimensional Darboux theorem nor an unproved infinite-dimensional symplectic inversion is needed: (1)-(3) are bounded-operator identities on the full infinite-dimensional V.

R_h is one specified identification anchored to the native fixed TT label chart and K0. Other symplectic identifications exist; uniqueness among them or coordinate-independent physical selection is not claimed. It changes the labels used to COMPARE different spacings, not the native action, the reconstructed exact solutions or hbar. Its deviation from the original common-label comparison tends to zero.

## 3. One fixed algebra and the transported exact dynamics

Let A0 be the unital universal Weyl C*-algebra for(V,Omega0,hbar). For completeness, the finite Weyl span has universal seminorm bounded by the sum of absolute coefficients because every generator is unitary in every representation. The accepted Fock representation is nonzero. Quotienting by its universal zero seminorm and completing supplies the universal algebra used here; no new regularity or norm continuity in the labels is imposed on the universal algebra.

Equation(3) makes W_h(R_h x) obey exactly the A0 Weyl relations. Their universal property, and the inverse map induced by R_h^-1, give a unital *-isomorphism
iota_h:A0->A_h, iota_h(W0(x))=W_h(R_h x).                (4)
This is an isometric C*-isomorphism, not a claimed unitary between the different vacuum representations.

Define on the fixed A0
phi_h=omega_h composed with iota_h,
beta_h,t=iota_h^-1 alpha_h,t iota_h.
Then
phi_h(W0(x))=exp[-hbar mu_h^flat(x,x)/4],
mu_h^flat(x,y)=mu_h(R_h x,R_h y),
beta_h,t W0(x)=W0(exp(t C_h)x),
C_h=R_h^-1 B_h R_h.                                    (5)
Positivity, normalization and invariance are immediate from the *-isomorphism and the accepted omega_h. In particular phi_h beta_h,t=phi_h.

The transported generator is still symplectic:
C_h* K0+K0 C_h=0,
K0 C_h=R_h* H_h R_h.                                   (6)
The right side is positive coercive, with uniform bounds for small h. Equation(6) follows by substituting K0=R_h* K_h R_h, keeping the order of every factor. The exact native step on this common algebra is beta_h,h; the underlying native solution remains the same exact invariant branch. Its positive implementing Hamiltonian is inherited in its own pulled-back GNS/Fock representation. No common representation or strong-resolvent assertion is inferred from (6).

## 4. Norm convergence of the covariance and the label dynamics

Write M_h for the bounded real Riesz operator of mu_h. Then M_h^flat=R_h* M_h R_h and
||M_h^flat-M0||
 <=||R_h||^2 ||M_h-M0||
   +||M0|| ||R_h-I|| (||R_h||+1) ->0.                  (7)
Thus the transported covariance converges on the FIXED label space and fixed symplectic form, not just on unrelated algebras.

For the exact label generator,
||C_h-B0||
 <=||R_h^-1||[||B_h-B0|| ||R_h||
                      +2||B0|| ||R_h-I||] ->0.         (8)
These operators are uniformly bounded. Taking M as a common bound for ||C_h|| and ||B0||, the bounded-operator exponential identity gives
||exp(t C_h)-exp(t B0)||
 <=|t| exp(M|t|)||C_h-B0||.                             (9)
For negative time use the same identity for -C_h,-B0. Hence the label flow converges uniformly on every fixed compact real time interval. If the already admitted operator data have a stated h rate, the same elementary bounds transfer it; no extra rate is asserted without such an input.

This label convergence must not be confused with C*-norm convergence W0(x_h)->W0(x). Such norm continuity of the universal Weyl labels is not available here and is NOT used below. In particular no point-norm convergence or point-norm continuity of beta_h,t is claimed.

## 5. Genuine weak-* state convergence and finite-time correlations

For every fixed x, (7) gives phi_h(W0(x))->phi0(W0(x)), where
phi0(W0(x))=exp[-hbar mu0(x,x)/4].
For a finite Weyl sum the same follows by linearity. These sums are norm dense in A0 and all phi_h have norm1. Given a in A0 and a finite sum p with ||a-p||<epsilon,
|phi_h(a)-phi0(a)|<=2epsilon+|phi_h(p)-phi0(p)|.
This proves
phi_h -> phi0 in the weak-* topology of A0*.             (10)
It is convergence of positive normalized states ON ONE EXPLICITLY IDENTIFIED ALGEBRA.

More is true for the exact transported dynamics. Fix finitely many labels x_j and times t_j in a compact interval. Put z_h,j=exp(t_j C_h)x_j. The Weyl relations give the exact multi-time correlation
phi_h(product_(j=1..n) beta_h,t_j W0(x_j))
=exp[-i hbar/2 sum_(j<l) Omega0(z_h,j,z_h,l)
     -hbar/4 mu_h^flat(sum_j z_h,j,sum_j z_h,j)].          (11)
There is no time-ordering convention beyond the written product order. Equations(7),(9) and boundedness of the fixed symplectic form show uniform convergence of (11) on compact sets of the t_j to the corresponding expression with B0,mu0. This proves the convergence directly without an illicit norm limit of Weyl generators.

It also extends to any fixed finite list a_j in A0: approximate each a_j by a finite Weyl sum and use a telescoping product estimate. Every beta_h,t is an isometric *-automorphism and every phi_h has norm1, so the approximation error is bounded by a finite sum of epsilon_j times products of the other fixed norm bounds, uniformly in h and all t_j. The finite-sum correlations converge uniformly by (11); taking all epsilon_j small proves compact-time multi-time correlation convergence for arbitrary fixed bounded algebra elements. No separability or uniformity over the entire unit ball of A0 is required or claimed.

## 6. Interpretation, unresolved obligations and review

This closes the particular varying-algebra gap left by M164 on its prescribed exact stable off-axis band: an explicit real bounded symplectic identification, positive invariant states on A0, their weak-* spacing limit and compact-time correlations of the exact native selected dynamics are now derived. The proof uses the full infinite-dimensional band, not a finite-mode truncation.

The comparison is tied to the specified R_h and fixed band. It does not prove that the original physical cut/frame/link/history law selects this branch or this inter-spacing identification. It does not extend across axes, k=0, the ultraviolet, nonlinear amplitudes or a full physical quotient, derive hbar, establish local/Hadamard field behavior, identify a gluing measure or complete a physical refinement theory. The unstable-sector state exclusions retain their own different hypotheses.

No unitary equivalence or inequivalence between the h-vacuum representations is proved, and no common quantum Hamiltonian domain or strong-resolvent limit is asserted. Weak-* state and correlation convergence is the specific verified topology. Vacuum energy retains M164's convention. All finite original boundary/corner obligations remain; no physical current normalization has changed.

Distinct review must check the non-self-adjoint binomial branch, real K0-adjoint identity, exact symplectic map and direction of the algebra isomorphism, transported energy signs, both norm estimates, universal-algebra versus Weyl-label continuity distinction, density extension and multi-time product estimate. Source selfreads are custody only. No acceptance is claimed until distinct finished-byte review and publication.
