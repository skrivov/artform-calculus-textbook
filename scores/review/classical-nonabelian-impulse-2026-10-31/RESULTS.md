# A classical curvature kick that preserves non-Abelian Gauss

A concrete instance of the monograph's open classical construction now has Lean proofs. On a square with an extra link, the update has exactly

```text
P'_e = H_e(U) P_e,
U'_e = P'_e U_e.
```

It preserves an explicitly ordered group-valued Gauss defect for every group G and every raw state, has an exact reverse, and commutes with all independent vertex gauges. The admitted impulse carrier is the full constraint surface mu=1, with no extra commutation restriction. An S3 example starts with noncommuting curvature and impulse and changes a nonflat face to a flat one while satisfying Gauss. The motion survives classical gauge reduction.

The constructor supplies a native classical example on the declared one-face canvas. General interacting faces, changes of local star order, orientation comparisons and a Hamiltonian or continuum interpretation require further work. The four new claim packets have checked Lean proofs and await independent fidelity review. All 254 earlier approvals remain intact. No additional worker was used.

## The canvas and its complete Gauss stars

The vertices are 0,1,2,3. Links 0,1,2,3 form the directed square 0->1->2->3->0. Link 4 runs from 0 to 2 and does not occur in the chosen face boundary. Vertices 0 and 2 have degree three. No planar embedding is assumed; this is the displayed finite cellular Canvas with its additional ordered-star data.

P_e lives at the target of e. Its source-based inverse flux is

```text
Q_e = U_e^-1 P_e^-1 U_e.
```

Declare the complete ordered stars

```text
mu_0 = Q_0 P_3 Q_4,
mu_1 = Q_1 P_0,
mu_2 = Q_2 P_1 P_4,
mu_3 = Q_3 P_2.
```

Every incident half-edge occurs exactly once in its vertex star. The cyclic order is model data. Lean proves for every group-valued word that cyclic rotation preserves the product-equals-identity condition, so a different cut in the same cyclic star gives the same Gauss predicate. Gauss means all four products equal1. With U_e->h_t U_e h_s^-1 and P_e->h_t P_e h_t^-1, every mu_v transforms by conjugation at v. This is a nontrivial state predicate with a gauge-stable admitted carrier, not an invariant-amplitude condition or a true predicate.

## Based face holonomies and exact cancellation

The holonomies are computed from rotations of the actual signed face boundary. Transport acts on the left, so composition uses reverse path order:

```text
H_0 = U_0 U_3 U_2 U_1,
H_1 = U_1 U_0 U_3 U_2,
H_2 = U_2 U_1 U_0 U_3,
H_3 = U_3 U_2 U_1 U_0,
H_4 = 1.
```

For the four face edges, previous=(3,0,1,2), and U_e^-1 H_e U_e=H_previous(e). The spectator has H_4=1. Thus the kick sends

```text
P_e -> H_e P_e,
Q_e -> Q_e H_previous(e)^-1.
```

In each declared star the changing pair is adjacent: Q_e H_previous^-1 H_previous P_previous. Its extra factors cancel without commuting any impulses or moving them past the spectator. Therefore the entire defect mu is unchanged on every raw state. The inverse kick uses H_e^-1 and has the same property because U stays fixed.

The drift keeps P fixed. Direct cancellation gives

```text
(P_e U_e)^-1 P_e^-1 (P_e U_e) = U_e^-1 P_e^-1 U_e,
```

so each outgoing Q and every mu remain unchanged. The inverse drift uses P_e^-1. Every individual link drift also preserves the defect. Fixed instruction words consequently have two-sided reversed-word inverses, exact defect preservation at every complete-instruction prefix, and full vertex-gauge covariance. Their restrictions to the admitted carrier descend to bijections of its complete classical gauge-orbit quotient.

## Actual process ownership and batch presentation

The face commit reads the four face U slots and four face P slots and writes all four face P slots atomically. It leaves both spectator slots unchanged. It has true guard. The single-link drift reads its own U/P pair and writes that U. The native two-phase LawInSteps checks Gauss at every boundary and permits no empty phase. It selects the atomic face commit and then a batch of all five compatible link drifts. Their writes are disjoint and do not change another proposal's reads. Every list permutation of that batch has the same endpoint, and the actual two slots equal the displayed tick.

An individual piece of the face kick is not admitted as a Gauss-preserving move. The noncommuting control below shows why. Independence of batch-list presentation also does not authorize changing the cyclic vertex-star order; that changes the declared constraint profile.

## A physical noncommuting control

Use G=Perm(Fin3), r=(01)(12), t=(01), and

```text
U = (1,1,1,r,1),
P = (t,t,1,1,t^-1).
```

All four initial defects are1, while H_0 and P_0 do not commute and H_3=r is nonidentity. The kick changes the state. After the full tick, H_3=1 and all defects remain1. No vertex gauge maps the initial state to this output, since conjugation cannot turn a nonidentity holonomy into identity.

Changing only P_0 to H_0 P_0 violates Gauss. Reordering the third star to Q_2 P_4 P_1 gives a second control: the same initial state satisfies that predicate, but the complete kick no longer preserves it. These are failures of those specified shortcuts, not impossibility theorems for every alternative construction.

The same positive control is proved in the actual A5 subgroup of Perm(Fin5), with r5=(01)(12) and t5=(01)(34). Both are even permutations. Its initial impulse and curvature do not commute, Gauss holds, and the tick changes the nonidentity face holonomy to1. Thus the concrete construction applies to the monograph's named A5 palette as well as S3; it does not select A5 from the dynamics.

The exact permutation replay enumerates all 104,976 Gauss-admitted S3 states, out of 60,466,176 raw U/P states, by solving three constraints and checking the fourth. Both shear orientations preserve Gauss and have exact inverses on every enumerated admitted state. Lean proves the stronger all-raw-state defect identities for arbitrary groups. The replay additionally checks all 120 drift orders and full vertex-gauge controls on the noncommuting example. Its counts are arithmetic evidence, rather than separately registered Lean counting theorems.

## The orientation boundary and next construction target

If an edge is reversed, its target-based impulse becomes U^-1 P^-1 U. A left kick k of this reversed impulse requires, in stored orientation,

```text
P' = P U k^-1 U^-1.
```

This acts on the right. A fixed right multiplier a can be written k p=p a for every p with one p-independent k exactly when a is central. The S3 rotation is not central. Thus the all-positive face constructor cannot be extended to mixed signed occurrences merely by using the same stored-edge left-kick rule. A general extension needs an explicit left/right interface, compatible ordered stars and overlap contracts. The next useful test is two adjacent faces with an oppositely traversed common link: one contributes a left multiplier and the other a right multiplier, whose compositions on that link commute while the full vertex constraints still need binding to the chosen star order.

The group-valued constraint is an explicit model choice. Group-valued moment maps have a broader quasi-Hamiltonian theory, but no quasi-Hamiltonian two-form is constructed here. [Alekseev, Malkin and Meinrenken](https://arxiv.org/abs/dg-ga/9707021) supply that separate framework. Classical lattice gauge integrators with Lie-algebra electric fields and Gauss preservation also already exist; this work does not claim their invention or identify the group impulse with their electric field. [Kurkela, Lappi and Peuron](https://arxiv.org/abs/1610.01355) give one such discretization. The current result is an exact Artform process realization with a declared group-valued carrier and constraint. Hamiltonian structure, energy, timestep accuracy, matter charges, gluing and a continuum limit remain unproved.
