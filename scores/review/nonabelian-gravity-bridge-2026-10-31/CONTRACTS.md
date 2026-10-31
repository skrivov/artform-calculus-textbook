# First constructor and physical comparison contracts

This is the original planning contract. The two-face implementation and exact submitted scope are now recorded in RESULTS.md and ALGEBRA-OF-SCORES.md. Analytic, geometric and native comparison duties below remain separate; this planning file does not certify them.

## Two-face test canvas

Use vertices 0 through 5 and seven stored edges:

| Edge | Source | Target |
|---|---|---|
| 0 | 0 | 1 |
| 1 | 1 | 4 |
| 2 | 4 | 3 |
| 3 | 3 | 0 |
| 4 | 1 | 2 |
| 5 | 2 | 5 |
| 6 | 5 | 4 |

The two proposed face boundaries are `[(0,+),(1,+),(2,+),(3,+)]` and `[(4,+),(5,+),(6,+),(1,-)]`. The common stored edge1 is traversed in opposite directions. Transport acts on the left and path holonomies use reverse traversal-product order, as in the predecessor.

For target-based P and source-based Q=U^-1 P^-1 U, the candidate ordered stars are:

```text
mu0 = Q0 P3          mu1 = Q4 Q1 P0       mu2 = Q5 P4
mu3 = Q3 P2          mu4 = Q2 P1 P6       mu5 = Q6 P5
```

Every incident half-edge must occur exactly once, including both trivalent shared vertices. The complete admitted state predicate is all mu_v=1. Positive and negative traversals use the actual based holonomy at the target of the traversed orientation. A reversed traversal's impulse is Q; translating its left kick k back to the stored impulse requires `P' = P U k^-1 U^-1`. Derive the complete based multipliers before coding them. Preserve the inherited single-face result as a separate model.

The first comparison holds U fixed throughout face kicks. A left and right action on shared P may commute as functions while their read/write profiles conflict. Do not invoke the existing disjoint-write Batch theorem for those overlapping commits. Compare sequential face commits and, if useful, a separately specified atomic merged commit. Adding link drifts changes U and needs its own schedule-defect calculation.

Require exact reverse words, all independent vertex gauges, all admitted instruction prefixes, a noncommuting nonempty example and an observable change surviving gauge reduction. Preserve complete defects if that is proved; otherwise state explicitly the conjugation law sufficient for mu=1. This is a new model contract, not a weakening of an existing CNI statement.

## Physical phase-space comparison

Start with a compact Lie group and the chosen invariant bilinear form, not an arbitrary abstract group lacking differential geometry. Our variables are U and target flux P, with source flux Q. Compare to the source-flux convention `(h,g,tilde_g)` by the proposed dictionary `h=U`, `g=Q`, `tilde_g=P`; check gauge-parameter inversions explicitly. This matches the endpoint algebraic relation in Riello IV.1, equations IV.5-IV.8. The comparison of fused two-forms, regular reduction, measures and dynamics remains a research task. [Riello](https://arxiv.org/html/1706.07811v2)

The required calculation includes the order-dependent fusion cross terms at each vertex and the actual reduced regular domain. A direct sum of edge forms is not a sufficient replacement for the fused structure. Compare the pullback of that structure under both shears and their composition. If it fails, record an actual admitted counterexample and test one specified correction. Arbitrary replacement of the form just to make a bijection canonical does not establish the intended physical identification.

The group-valued-moment-map framework supplies the mathematical comparison, rather than an already-proved property of our process. [Alekseev, Malkin and Meinrenken](https://arxiv.org/abs/dg-ga/9707021) Usual fixed-graph loop-gravity variables have a cotangent-bundle phase space per edge. A small-flux comparison must give a domain and parameter normalization; substituting a group name alone does not provide it. [Freidel and Speziale](https://arxiv.org/abs/1001.2748)

The geometric candidate is a four-valent closure/reconstruction problem with explicit constant-curvature and nondegeneracy conditions. Reconstructible curved tetrahedra and their gluing are additional duties beyond algebraic closure. [Haggard, Han and Riello](https://arxiv.org/abs/1506.03053)

## Native-gravity acceptance

Before a native application, bind the actual action or constrained Legendre relation, allowed boundary/halo variations, source/current class, history/preparation and justified quotient. Internal Gauss preservation supplies only one part of the constraint problem. Record remaining temporal, Hamiltonian/diffeomorphism or geometricity obligations appropriate to the selected formulation, rather than silently treating them as Gauss.

Refresh the frozen P190/P179 sources before selection. Preserve Q1's spatial-versus-temporal averaging correction and all affected-source limitations. Do not infer a variable-background or full reduced34 inverse from the vector16 fixed-window smooth result, or a physical quantum state from the reference-current common domain. Earlier R7/R8 Lean tools remain useful with their original source, finite-spacing and exceptional-domain restrictions.

Quantum work is conditional on identifying the physical algebra and quantization. A permutation-unitary lift of a finite reversible map does not establish quantization of the desired holonomy-flux brackets. The previous S3 curvature probability is a separate coherent experiment. Neither it nor an SU(2) specialization of group identities establishes gravitational amplitudes, a cosmological constant or Einstein dynamics.
