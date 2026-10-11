# The pilot

Before the rest of the book was planned in detail, the pilot formalized 15
statements of the 52nd edition: 1.3, 1.29, 1.31, 4.2, 5.4, 5.6, 5.7, 5.23,
5.27, 5.38, 5.39, 5.44, 6.1, 11.5 and 12.8. Between them they cover tiers A
to D across six chapters. This file records what they cost and what they
taught. It replaces the provisional costs of the plan.

## Result

- All 15 are proved.
  - Each proof uses only the axioms `propext`, `Classical.choice` and
    `Quot.sound`.
  - `leanchecker` replays the whole library in the kernel in about 30
    seconds.
- None has been reviewed by the author yet, so `STATUS.md` lists all 15 as
  stated. `scripts/review_sheet.py` writes their review sheet.
- The pilot itself found no error in the book. Two
  statements needed a choice of reading, which the decisions below
  describe.

## What the proofs cost

Each row is one agent session that wrote the proofs. The statements and the
definitions they use already existed, and the sessions could not change
them. The eight sessions ran in parallel, and the proof stage took 26
minutes in all.

| Proof files | Statements | Tiers | Time | Lines of Lean |
|---|---|---|---|---|
| `Ch01/Rods`, `Ch05/Reversal`, `Ch05/Orbits` | 1.3, 1.31, 5.39, 5.4 | A, A, A, A | 19 min | 352 |
| `Ch05/Noether` | 5.6, 5.7 | B, A | 8 min | 130 |
| `Ch05/Holonomy` | 5.23, 5.27 | B, B | 20 min | 353 |
| `Ch05/Stokes`, `Ch06/Reversible` | 5.38, 6.1 | B, B | 14 min | 287 |
| `Ch05/Hall`, `Ch04/Counting` | 5.44, 4.2 | B, B | 12 min | 182 |
| `Ch01/Topos` | 1.29 | C | 10 min | 228 |
| `Ch11/Averaging` | 11.5 | C | 9 min | 102 |
| `Ch12/Icosahedron`, `Exact/QPhi` | 12.8 | D | 25 min | 762, and a 232-line Python certificate |

The work that came first cost more than the proofs. That work was writing
each statement and the definitions it needs, and checking every hypothesis
against the book:
- 13 files of definitions and statements, about 950 lines, drafted while
  planning and committed before any proof;
- a fidelity note for each statement, recording every way the Lean reads the
  book.

Two changes were needed once proofs began. Both were made by the
coordinator, not by a proof session:
- The holonomy of a path was first defined by well-founded recursion, which
  the kernel cannot compute with. It is now structural. The statements did
  not change.
- The frame claim of 12.8 first said "exactly one matrix carries the frame
  *and* is a rotation with entries in ½ℤ[φ]". That is weaker than the book's
  "the matrix that carries the frame". It now says that exactly one real
  matrix carries the frame, and that any matrix that does is such a
  rotation.

## Revised costs

| Tier | In the pilot | Measured | The rest of the book |
|---|---|---|---|
| A, elementary | 5 | 4 statements in one 19-minute session | 6 left; a few sessions in all |
| B, structural | 7 | 2 statements per session of 8 to 20 minutes, once the definitions exist | 35 left; the definitions they need are the larger task, about one chapter's worth per batch |
| C, Mathlib theory | 2 | 10 minutes each where Mathlib has the theory (topoi, representations) | 25 left; the cost depends on what Mathlib lacks, such as projective limits of measures, the combinatorial fundamental group, or second quantization |
| D, certified computation | 1 | 25 minutes, including the `ℤ[φ]` library | 17 left; `Exact/QPhi.lean` serves the icosahedral group, and ℚ(√5, ω) and R8 need libraries of their own |
| E, research or modelling | 0 | none | 5; each needs the author's decision first |

The proofs are no longer the bottleneck. Three things set the pace:
1. writing faithful statements and their definitions;
2. the author's review, at about two pages of review sheet per statement;
3. keeping parallel sessions apart. Each writes only its own new files, and
   the kernel replay runs only when no session is compiling: with eight
   compiling at once, the replay ran out of memory.

## The revised order

The batches of the plan stay, and they run as clusters of statements that
share definitions, several at once:
1. B1 with the growth statements of B5: laws and realizers (5.8, 5.11, 5.13),
   and growth in Chapter 3 (3.27, 3.29, 3.32, 3.33);
2. the rest of B5: recognition, metrics and measures in Chapter 3, the cube,
   and probability in Chapter 4;
3. B4: the tetractys witnesses and the Category Café;
4. B2 and B3: gauge theory in Chapter 5 and the toy electrodynamics of
   Chapter 6. Definition 5.35 (gauge-covariant law) is written once, with
   Chapter 6, and Chapter 5's 5.36 follows it.
5. B6 and B7: representations and colour first, as the later matter
   statements build on their tables, Fock space and the second quantization
   map. The certified computations of Chapters 12 and 13 come last.
6. B8: the five tier-E statements, after the author's decisions.

## Decisions the pilot raises

- **5.44 (Hall).** The Lean statement counts goods, needs and flows in whole
  units, as tokens are counted. If the book means real quantities, the
  real-valued version (Gale's theorem) is true but not stated here. Which
  reading does the book intend?
- **11.5 (averaging counts).** "The number of times ρ occurs in W" is taken
  as the dimension of the equivariant maps from ρ to W. That this equals the
  multiplicity in a decomposition into irreducibles (Maschke and Schur) is
  standard, and Mathlib has Maschke's theorem. The equality could be added
  if the author wants the multiplicity itself.
- **Compatibility (3.27 and every batch).** Two enabled applications are
  compatible when their write footprints are disjoint and neither changes a
  position the other reads. This is the reading of Section 3.8 and of the
  proof of 3.27. The more permissive conditions mentioned after
  Definition 2.6 are not covered.
- **Laws in steps (5.13).** A law in steps checks each invariant only at its
  checkpoints, while Definition 5.9 asks every move to lead to a legal state.
  The Lean statement reads legality at the boundaries of the slots: a move
  of the open step leads from a state legal at one boundary to a state legal
  at the next. This is how the book's proof uses it, and a law of Section 5.4
  is the case in which every invariant is checked at every boundary.
- **Pending work (3.30, 3.32).** With work pending from its first offer,
  Proposition 3.32 fails on a natural reading of Definition 3.30
  (`FINDINGS.md`, F1). The Lean statement counts pending work from the step
  at which it is enabled.
