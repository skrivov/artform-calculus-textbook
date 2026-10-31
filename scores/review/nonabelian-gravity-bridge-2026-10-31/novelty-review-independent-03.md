# Independent novelty assessment of the NGB campaign

Date: 31 October 2026. Reviewer: the same independently authorized
`ngb_independent_review` worker. No additional workers were launched. This is
a research assessment, not a return of any approved proof. No production
module or approval metadata was changed.

**Assessment: the eleven approved claims establish useful checked
specializations and proof infrastructure, but no new quantum-gravity result
has been established. The proposed general reduction and four-edge dipole
must not be presented as new mathematical frameworks.** There is stronger
evidence than a resemblance to existing work: after an explicit spanning-tree
gauge choice, the two face kicks become the standard disjoint genus-two
Dehn-twist automorphisms.

The conclusions below were sent to root before this document was written.
The literature search supports the stated identifications; it does not
establish a worldwide priority claim for a Lean implementation.

## Known framework and the status of the eleven claims

AMM already constructs the double, ordered fusion, regular reduction and
moment-map twist automorphisms. Its mapping-class discussion explains the
topological origin of these operations. In the present coordinates the target
twist acts as `(A,B) -> (ABA,A^-1)`; `A=U,B=U^-1 P` gives precisely
`U -> P U`, with P fixed. Therefore the drift is a coordinate implementation
of a known operation. The planned regular reduction would formalize an
existing theorem subject to its actual hypotheses, not discover that theorem.
[Alekseev, Malkin and Meinrenken, §3.2, Theorem4.5, §§5,6,9.4](https://arxiv.org/pdf/dg-ga/9707021)

Riello already applies this machinery to group-valued lattice fluxes,
identifies the reduced phase space with flat connections on a Heegaard
surface, and discusses a curved-geometric gravity interpretation. SectionVI.2
explicitly connects the double's twist with a cylinder Dehn twist. Its HTML
spells this word “Dhen”, so a search only for “Dehn” misses the passage.
Our independently checked convention translation remains important, but the
phase-space and gravity connection themselves are prior work.
[Riello, §§IV,VI,IX](https://arxiv.org/html/1706.07811v2)

| Approved key | Novelty assessment |
|---|---|
| `NGB:two-face-geometry` | New checked instance of graph incidence and group-valued closure in this ledger; no new general gauge geometry. |
| `NGB:oriented-score` | Exact explicit lift and verified inverse/quotient implementation. The reduced face maps are the known twist maps derived below. |
| `NGB:legal-overlap` | Concrete Artform process and ownership packaging. Its distinction between commuting functions and incompatible overlapping writes is useful implementation work. No new physical scheduling principle is established. |
| `NGB:noncommuting-controls` | Specific regression examples and adverse controls. These are new examples for our chosen model, not a new gravitational obstruction. |
| `NGB:double-dictionary` | Verified coordinate substitution into the known double. |
| `NGB:formal-two-form` | New finite certificate implementation and checked calculation for the chosen maps. The underlying preservation mechanism is established. |
| `NGB:word-binding` | Verified semantics for this word compiler; standard free-group reasoning implemented concretely. |
| `NGB:neighbor-scaling` | Useful noncommutative expansion and elementary conditional norm budget; no new continuum estimate or physical limit has been proved. |
| `NGB:analytic-interpretation` | A checked bridge from the compiler to actual quaternion derivatives and form evaluations. The product/inverse calculus and trace identities are standard; the assembled proof artifact is a concrete contribution. |
| `NGB:stabilizer-preservation` | A standard consequence of equivariance and invertibility, faithfully specialized to the complete gauge action. |
| `NGB:geometric-preflight` | A bounded counterexample to an unsupported fixed-conjugacy interpretation of our particular map. It does not challenge an established tetrahedron theorem. |

None of these judgments invalidates approval. Approval means fidelity and
proof correctness, not scientific originality. “Eleven approved statements”
must not become “eleven new results in quantum gravity.” A defensible current
description is: **a Lean-checked Artform realization and certificate interpreter
for specified non-Abelian lattice/character-variety operations, with explicit
controls on several proposed interpretations.**

## Exact face-kick dictionary, rather than analogy

This calculation uses the actual production edge orientations and star order.
It is an independent algebraic derivation, corroborated by free-group word
reduction. It has not yet been registered as an additional Lean claim.

Choose the spanning tree with edges0,1,2,4,5 and gauge its link variables to
one. This is possible for every group: recursively choose the vertex gauges
along the tree. Set

```text
a=U3, b=U6, x=P0, z=P6.
```

The tree links are now one. Five Gauss equations solve the remaining impulses:

```text
P3=x,
P2=a^-1 x a,
P1=a^-1 x a z^-1,
P4=P5=b^-1 z b.
```

The remaining condition is

```text
R=(x^-1 a^-1 x a)(z^-1 b^-1 z b)=1.
```

More precisely, without imposing R=1, the six displayed defects of this
parametrized state are `(1,R^-1,1,1,1,1)`. Thus this is the full Gauss carrier
in tree gauge, not an additional commuting sector. The only vertex gauges
preserving all tree links equal to one are common conjugations, because the
tree is connected.

Define four surface generators by

```text
A1=x^-1, B1=a^-1, A2=z^-1, B2=b^-1.
```

Then R is the usual genus-two relation

```text
[A1,B1] [A2,B2]=1,  [A,B]=A B A^-1 B^-1,
```

and residual gauge reduction is simultaneous conjugation of all four
generators. This supplies the group-level character-variety dictionary.

On these actual parametrized states, the face updates are exactly

```text
face0: x -> a x, with a,b,z fixed;
face1: z -> b z, with a,b,x fixed.
```

Consequently their surface-coordinate actions are

```text
face0: A1 -> A1 B1, with B1,A2,B2 fixed;
face1: A2 -> A2 B2, with A1,B1,B2 fixed.
```

Each preserves its commutator exactly, since `[AB,B]=[A,B]`. The two maps
commute because they act on different handles. An independent free-word
replay checked the six defects, both complete face updates, the relation
and the commutator identities without imposing commutativity.

These are the standard nonseparating twist automorphisms. Goldman's
section2.6 writes the representation action as multiplication of a crossing
generator by the twisting-loop holonomy, exactly the form above. Thus our
face map is a known Dehn-twist action in these reduced coordinates, with
the chosen orientation/pullback convention. Goldman–Xia section4.4 uses the
inverse representation-action convention; this changes the twist sign, not
the identification. [Goldman, §2.6](https://math.umd.edu/~wmg/csymp.pdf),
[Goldman and Xia, §4.4](https://www.math.umd.edu/~wmg/zimmer.pdf)

This establishes the group-level reduced identification. It does not by
itself add a Lean theorem identifying every framed raw-state coordinate,
the smooth quotient or the symplectic form under this dictionary. Nor does
it identify a mapping-class action with physical time evolution. The known
twist/Hamiltonian-flow relationship requires its normalization and domain;
a selected gravitational Hamiltonian has not been supplied here.

## The proposed next stages are also established settings

The four-link, two-node dipole is a long-used loop-gravity/cosmology graph.
Rovelli and Vidotto already use the two-tetrahedron construction. A future
dipole implementation could still be useful, but the graph and its basic
two-tetrahedron interpretation are not new.
[Rovelli and Vidotto, §IV](https://arxiv.org/html/0805.4585v1)

Haggard, Han and Riello already give the curved tetrahedron reconstruction
and fixed-area shape-space framework, including the path, orientation and
nondegeneracy requirements and the SU(2)/SO(3) sign issue. Formalizing these
would be infrastructure work unless an additional unresolved compatibility
problem is solved. [Haggard, Han and Riello, §§6,9–11](https://arxiv.org/html/1506.03053v1)

Even a generic proposal to quantize curved tetrahedron closure is not an
unexplored objective. Subsequent work constructs the quantum closure/intertwiner
space and curved-tetrahedron coherent states. This does not prove that all
our possible quantum process questions are settled, but it rules out claiming
the general quantization programme as newly initiated here.
[Han, Hsiao and Pan](https://arxiv.org/abs/2311.08587),
[Hsiao and Pan](https://arxiv.org/abs/2407.03242)

For the proposed cyclic dipole stars, retain the basepoint qualification:
non-wrapping adjacent pairs cancel in the fixed linear product. A wrapping
pair generally conjugates the complete defect. Gauss preservation can still
hold, but raw-defect equality must not be copied unchanged from our present
constructor.

## What could justify continued research

The next physics-oriented gate should identify a statement that the sources
do not already supply for the actual chosen gravitational model. A useful
candidate is a concrete compatibility or obstruction test: specify an admitted
native state, all coframe/connection and boundary data, an explicit dictionary
for the proposed process, and a particular unresolved native constraint or
observable. Then compute whether the process preserves that constraint or
whether its exact defect can be corrected within the same admitted problem.
Closure alone is insufficient.

An alternative useful computational target is a demonstrable improvement for
an already specified physical calculation, compared under identical sources,
domains, precision and reconstruction obligations. A theorem about a shorter
word or a faster finite replay is not automatically a physical improvement.

Without such a target, the regular-reduction/dipole work should be described
and budgeted as formalization of existing mathematics. That can be valuable,
but it does not meet the campaign's stated aim of materially affecting
quantum-gravity research. No scientifically new positive gravity result or
general no-go theorem is established by the present packet.
