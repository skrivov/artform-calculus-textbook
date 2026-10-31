# Checked applications of scores to gauge fields

Applications 1 and 2 now have nine production Lean claims: a canonical and gauge-compatible score compiler, and exact sourced coarse Maxwell dynamics with retained hidden state. The main gain is a checked connection from score manipulation to actual finite-canvas field updates, quantum phase coefficients and dynamical reconstruction. Application 3, the nonabelian prototype, remains separate.

## Canonical processing and the actual field library

A determinant-one Laurent processor is admissible for the spatial canonical pairing precisely when every entry is fixed by spatial reversal. In one variable those fixed stencils are polynomials in g=2-T-T^-1, over arbitrary commutative coefficient rings, including Z/8. This supplies an exact guard for a classical score optimizer. It does not assert that every admissible processor has a factorization using only the new local generators.

The five-site Z/3 control now reaches actual Weyl operators. Processing the Maxwell tick by opposite channel shifts turns a commuting pair into a noncommuting pair. No complex linear change of quantum state coordinates can realize the completely specified processed Weyl action by conjugation. The theorem concerns that action; a different read/write contract or a scalar-rephased action is not its formal conclusion. A common translation preserves the canonical pairing and is an explicit positive control.

The native field library uses complete face-boundary electric kicks, link-potential moves and joint electric/charge current commits. Complete face commits preserve Gauss at every instruction boundary; individual per-link pieces of the old kick generally do not. Actual ProcessProfiles prove the stated local reads and writes. Their singleton batches avoid assuming disjointness of overlapping face boundaries. The compiler preserves gauge covariance, has a two-sided inverse, and preserves the ambient field-variation pairing with sources and the word held fixed. Divergence-free electric variations remain so. A reduced nondegenerate gauge-quotient pairing has not been constructed.

The grouped face score, followed by all prescribed source commits and then all link moves, equals the original Maxwell macro update exactly. The periodic realizer adds one witnessed hold to each word, including the empty word. Its prefixes and padded cycle are checked against the word. These are new grouped histories and cadence; only their complete macro endpoint is identified with the original per-link realization.

## Calibrated coherent compilation

The C8 configuration polarization keeps potentials as configurations and electric values as characters. Both monograph receipts q+ and q- are implemented, with coefficients in R16=Z[zeta16,1/2] and the field palette still C8. Their receipt equations, evenness, unit phases and distinct half-phase choices are checked. The actual MQ7 character-sum kernel is unitary and its inverse retains conjugated coefficients.

Each coherent link branch is a legal singleton-read/write translation ProcessProfile, with its actual kernel coefficient, including the zero increment. The compiler multiplies those actual matrices and the magnetic face phases, supports adjoint letters and proves full raw-space unitarity in both inverse orders. It preserves vacuum gauge-invariant amplitudes, and its inverse word and coefficient-ring membership are checked. This is a matrix compiler with gate ownership; a general weighted LawInSteps coherent realizer is a separate interface.

For one common receipt policy, the complete face-then-link word has exactly the monograph's MQ9 factorization. Mixed-policy words remain valid compiled unitary words but are not identified with that native tick. The eighth power of either receipt at field1 is nontrivial. Consequently classical relators cannot be silently removed from coherent words on the strength of their classical endpoint. The compiler retains the actual phase data. Quantum charged sources and general spatial gluing are outside this vacuum theorem.

## Exact spatial memory with sources

The spatial result is bound to a genuine periodic four-by-two square incidence canvas. Its four-site transverse sector carries arbitrary time-dependent transverse current; div J=0, so rho=0 and Gauss remain valid. The generic field compiler separately handles arbitrary prescribed currents and the required charge-continuity update.

Read the direct even state x=(Aeven,Eeven) and hidden odd state z=(Aodd,Eodd). With L(a,e)=(-a-e,2a+e) and H(a,e)_r=(a_r+a_(r+1),-a_r-a_(r+1)), the exact blocked equations are

```text
x_(n+1) = L*x_n + H*z_n + f_n,
z_(n+1) = H*x_n + L*z_n + g_n,
f_n = (j_even,n,-j_even,n),
g_n = (j_odd,n,-j_odd,n).
```

Elimination gives the exact visible memory

```text
x_(n+1) = L*x_n + H*L^n*z_0
          + sum_(r<n) H*L^(n-1-r)*H*x_r
          + sum_(r<n) H*L^(n-1-r)*g_r + f_n.
```

The hidden preparation, visible forcing and hidden-source convolution all remain. Conversely, define z from its sourced recurrence or the checked closed formula. The visible equation holds exactly when interleaving x,z solves the fine tick; deterministic fine evolution is unique from its full initial state. This makes the elimination usable for reconstruction, not merely a necessary identity for an existing trajectory.

The assessment's declared coarse observable is output(x)=(Aeven_(r+1)-Aeven_r,Eeven_r), with the first component equal to the sum of two adjacent fine curvatures. Reconstructing the fine field retains the additional even potential and holonomy information; output(x) alone does not contain it. Native Gauss-valid states with A=0 and A=(0,1,0,0), both E=0, have the same initial observable. Their next coarse electric readings are respectively(0,0) and(7,7). Thus no autonomous one-tick map on exactly this observable works for every fine state.

This is an exact finite geometry result. L^4=id does not imply least period four and supplies no decay or truncation estimate. Minimal hidden dimension over Z/8, nontransverse charged coarse dynamics, prepared autonomous closures and general spatial refinement remain further research targets. No complete quantum-gravity gate or new physical continuum theory is claimed.

## Verification and custody

The tagged propositions and proofs are in Gauge/Statements.lean and Gauge/Theorems.lean. The canonical literals, source pins and root validation are in this review packet. Independent review records approval separately. All 239 earlier approvals and their Lean definition/proof surfaces are preserved; the umbrella import is extended. Shared ledger edits by other agents are outside this campaign's dedicated directory.
