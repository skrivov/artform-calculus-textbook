# Uniform coordinate-trace gap for native-step invariant TT graphs — UNREVIEWED

Independent duty research, outside published M178. This is a new consequence of the accepted original slow-trace generator and the accepted explicit temporal forcing, not a new evaluation of the full native force. All mathematics is manual. ROOT supplied challenges about norms, induced propagators and logarithms before this freeze; those challenges are disclosed and are not independent review. No late R8 packet is a premise.

## 1. Exact native domain and fixed norm

Use the SAME original physical twenty-trace slow history space and consistent LOWER coframe coordinate of eec52c84, mandatory01c258f6 and lower-basis0a10194b. The exact original full40 reconstruction and its temporal halo are inherited, not redefined. The trace generator is A_h=T partial_t S_h, with partial_t S_h=S_h A_h, as proved in accepted M162 sourcef8c87691 and reviewed3d82b32a. Its entries and limit are bounded smooth Fourier multipliers on every fixed compact physical annulus. Accepted M163 sourcee53a2a95 gives the same generator on a full Fourier-real off-axis completion, not merely componentwise-even data.

Choose a reflection-symmetric compact off-axis band with 0<r0<=|k|<=r1 and max_i|k_i|<=(1-epsilon)|k|. For the concrete witness below require 0<epsilon<1-3/sqrt(14); choose its support strictly inside the band and annulus. This narrower choice is nonempty and explicitly contains a rescaled neighborhood of (1,2,3). No claim is made on every off-axis band or on axes, zero frequency, or an unbounded frequency domain.

Let Y be the real Hilbert space of Fourier-real TT pairs y=(q,v), where v=2p. Its fixed norm is ||q||_2^2+||v||_2^2 using the original full symmetric-tensor contraction. Let Z be the real Hilbert space of the sixteen LOWER coordinate traces (chi,chi_t,chi_tt,chi_ttt), with the direct-sum L2 norm of their four components. Put H=Y direct-sum Z, with this fixed trace norm. This is a declared data norm; it is not asserted equivalent to an unrestricted full40 physical-energy or boundary norm.

Define E y=(y,0) and Q(y,z)=y. They are fixed, bounded norm-one operators and QE=I. The complement projection R=I-EQ is also norm one. No h-dependent normalization or Lorentz representative is hidden in these definitions. The finite angular TT bundle is treated intrinsically; no global polarization frame is required.

In this SAME H completion the accepted uniform multiplier convergence gives ||A_h-A_0|| ->0. Fix a>0 and h1>0 with ||A_h||<=a for 0<=h<=h1. In particular A21(h)=R A_h E:Y->Z converges in operator norm to A21(0). All four block norms of A_h in H=Y direct-sum Z are at most a. These statements use the fixed compact band and trace normalization; they are not estimates uniform over expanding bands.

## 2. An actual lower temporal component supplies a positive bound

For a leading TT datum y=(q,0), accepted M162 equations(8)-(9) give the actual normalized LOWER temporal-coordinate fourth jet

  [A21(0)y]_(chi0_ttt slot) = chi_0^(4)(0)
                           = Delta_sp sum_j partial_j q_jj /202.       (1)

This is the last trace's derivative, not a freely assigned fourth initial jet. The original incoming signs, full signed connection inverse, spatial-face cancellation and factor202 were independently reviewed in3d82b32a; this lemma reuses those accepted identities rather than claiming a fresh full-force audit. Lorentz representative changes do not change this metric trace component.

At k=(1,2,3), take a0=(2,-1,0)/sqrt5 and b0=(3,6,-5)/sqrt70, with TT polarization q0=a0 a0^T-b0 b0^T. Then diag q0=(47,-22,-25)/70 and sum_j k_j(q0)_jj=-36/35. The Fourier multiplier in(1) is -i|k|^2 sum_j k_j q_jj/202; its value here is +i36/505, nonzero. Scaling this direction into the annulus preserves nonvanishing. Extend q0 smoothly as an intrinsic TT section on a small patch, reflect it evenly, and multiply by a nonzero real smooth compact amplitude. This gives an admitted real-even Schwartz TT q; its transformed component in(1) is Fourier-real and nonzero, although it need not remain centrally even.

Normalize the resulting y*=(q,0) to ||y*||_Y=1. Define d*=||[A21(0)y*]_(chi0_ttt slot)||_2>0. Positivity follows from nonvanishing on an open spectral subpatch, not a numerical lower-bound evaluation. Operator-norm convergence yields, after reducing h1 if necessary,

  ||A21(h)|| >= ||A21(h)y*||_Z >= d*/2.                 (2)

Thus it is the normalized infinitesimal native temporal component, of order one in this fixed trace norm, that supplies a uniform bound. We do NOT divide the O(h) one-step defect by h without an identified generator and limit.

## 3. A forward native-step invariant closed graph is generator invariant

Let K_h:Y->Z be ANY bounded real operator, not necessarily a Fourier multiplier. Its graph is range J_h, J_h y=(y,K_h y); it is closed and QJ_h=I. Suppose just forward invariance under the actual native lattice step U_h=exp(h A_h): U_h range J_h is contained in range J_h. No common prescribed TT propagator is assumed.

Choose h>0 so e^(ha)-1<1 and h<=h1. Then ||U_h-I||<=e^(ha)-1<1, and the operator series

  L_h=sum_(n>=1) (-1)^(n+1)(U_h-I)^n/n

converges in operator norm. Every summand preserves the graph: U_h and I preserve it, so their difference and every positive power do. Closedness then makes L_h preserve it. The norm-convergent power-series identity log(exp(z))=z near z=0, substituted in the bounded operator h A_h, gives L_h=h A_h. It is the local logarithm defined by this series; no global spectral-log choice or backwards invariance is needed. Consequently A_h preserves the graph.

Its induced data generator is its OWN S_h^graph=Q A_h J_h=A11+A12 K_h. It need not equal the propagator of the zero-coordinate-jet prescription or the M163 dressed branch. Generator invariance now gives the exact operator Riccati equation

  A21+A22 K_h-K_h A11-K_h A12 K_h=0.                    (3)

This removes the same-propagator restriction of a naive intertwining-distance argument. All compositions are bounded on the fixed Y,Z spaces, even when K_h mixes frequencies within the declared band.

## 4. Uniform separation and the finite-N consequence

Write k_h=||K_h||. Equations(2)-(3) and the uniform block bounds imply

  d*/2 <= ||A21|| <= 2a k_h+a k_h^2.

Since k_h>=0, every such invariant graph obeys the explicit h-uniform bound

  ||K_h|| >= c*=sqrt(1+d*/(2a))-1 >0.                   (4)

Neither constant is called universal: a,d* depend on the fixed band, trace norm and selected packet. Equation(4) excludes any bounded normalized family of native-step invariant graphs with ||K_h|| ->0 as h->0. No upper bound on ||K_h|| was assumed. In particular this is not merely a fixed-h distance that vanishes with the lattice spacing.

For any separately fixed N, accepted M162 defines the actual normalized finite-prescription graph J_N(h)=G_N(h)[Q G_N(h)]^-1, with QJ_N=I and J_N->E. Thus its coordinate graph K_N=R J_N tends to zero. Every invariant graph K_h satisfies ||K_h-K_N(h)||>=c*-||K_N(h)||>=c*/2 once h is sufficiently small for that N. No uniform-in-N threshold or convergence of the formal constructor is asserted.

The accepted M163 invariant spectral graph is consistent with this result: its coordinate trace tends to a DIFFERENT, generally order-one graph, not E. This proof does not show that graph unique, physically admissible, or forced by the native law.

## 5. Strongest honest interpretation

The selected zero-coordinate-trace chart cannot be repaired into a native-step invariant bounded graph by coordinate corrections vanishing in this fixed trace norm. Even arbitrary bounded frequency-mixing graph corrections must have an order-one size somewhere on the packet-containing band. This sharpens the accepted noninvariance of each fixed-N image, while retaining its actual native temporal forcing.

This is a linear slow-history/chart statement. It neither invalidates a physical prescription tied to a distinguished initial surface nor proves that the original complete physical coframe trace tends to E in the full history category. The total-coframe chi is NOT the constructor's Phi, as mandatory01c258f6 emphasizes. A different trace prescription, non-graph/larger invariant space, different physical topology/norm, quotient, nonlinear family, or branch not approaching E remains open. No full physical radical, full energy, boundary/frame/link/history matching or gravitational parent is supplied. All eight routes remain active; R2/R8 priorities remain.
