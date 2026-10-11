# Findings

Errors or gaps found in the book while formalizing it. Each entry gives the
statement, what fails, a counterexample or the missing step, and a proposed
correction. The book is corrected through its own release process. A Lean
statement is never weakened to make a proof go through.

## F1. Pending work and Proposition 3.32 (Fair closure)

*Found 2026-10-11, while proving Proposition 3.32 (`prop:fair-closure`)
with Definition 3.30 (`def:fairness`). 52nd edition, Section 3.9.*

**What the book says.** An application is pending "from its first offer
until the policy selects it", and an offer is a step whose open phase lets
it be selected. Cadence fairness asks the control tapestry to keep opening
"every phase that pending work needs". Application fairness asks the
policy to select "every application that stays enabled each time its phase
is open". The proof of 3.32 uses both hypotheses: a persistently enabled
placement is "selected, by the second and third".

**What fails.** Work whose phase is never opened is never offered, so it is
never pending, and cadence fairness does not ask for its phase. The remark
after the definition reads application fairness as a condition on the
policy that a tapestry which stops offering steps defeats. Read that way, it
does not cover such work either.

**Counterexample.** Take two attachments: a1 in phase alpha and a2 in
phase beta, both enabled at the seed, with different outputs. Let the
control tapestry open alpha at every slot.
- a1 is offered, pending and selected.
- a2 is never offered, so it is never pending. Cadence fairness and
  application fairness, read as above, both hold.
- The run stops at the seed with a1's cell. That patch is not closed,
  because a2 is still enabled there.

**The other reading.** Read application fairness strictly, so that "stays
enabled each time its phase is open" holds vacuously when the phase never
opens. Then the run above is not application fair, and 3.32 holds. But
cadence fairness then plays no part in it, while the proof uses it.

**Proposed correction.** Count pending work from the step at which it is
first enabled: "The application is pending from the first step at which it
is enabled until the policy selects it." Cadence fairness then opens every
phase that enabled work needs, application fairness concerns work whose
phase keeps opening, and the proof uses both, as written.

**In the repository.** The Lean statement of 3.32 uses the corrected
reading, as its fidelity note says, and awaits the author's review.

## F2. Moves that keep the invariants only together (Definition 5.9 and the Maxwell law)

*Found 2026-10-11, while proving Theorem 6.3 (`thm:maxwell-covariant`) with
Definitions 5.9 (`def:law`) and 5.12 (`def:law-steps`). 52nd edition,
Sections 5.4 and 6.3.*

**What the book says.** Definition 5.9: "At each legal state the law lists
finitely many moves: the changes it allows there, each leading to a legal
state." Section 6.3 writes the Maxwell law in the terms of Definition 5.12.
Its moves are the kick and the Faraday move at each link and the charge
update at each site, the score is K then M, and the invariant is
div E = rho at the macro-tick checkpoints. The realizer's evidence that
every batch keeps the invariant is Theorem 6.4.

**What fails.** A kick at one link changes E there, and with it div E at
both ends of the link. The invariant holds again only after every kick and
every charge update of the phase. So a single move made at a legal state
does not lead to a legal state, as Definition 5.9 asks.

Checking the invariant only at the macro-tick checkpoints does not help.
The kick phase ends at an unchecked boundary, where every state counts as
legal. A single Faraday move made there must then lead to a state that is
legal at the next checkpoint. From a state reached by one kick, it does
not.

**Proposed correction.** In Definition 5.9, ask it of batches rather than
of single moves: "Every batch the law allows at a legal state leads to a
legal state." Alternatively, drop the clause and leave invariance to the
realizer's evidence of Definition 5.10, which Section 6.3 already cites.

**In the repository.** The library's `Law` (Definition 5.9) and
`LawInSteps` (Definition 5.12) keep the clause as printed, for single moves,
so the Maxwell law cannot be written as either of them. Theorem 6.3 gives
the law by its parts. Theorem 5.13's proof does not use the clause.

## F3. The turns of the pose law are not batches

*Found 2026-10-11, while proving Proposition 5.36 (`prop:gauge-runs`) with
its example, the pose law of Section 5.15. 52nd edition, the paragraph
after Definition 5.35.*

**What the book says.** "Each of its moves reads one link and one pose and
writes one pose, ... and the realizer that takes every move of the open
step, whatever the links say, is gauge covariant too." A realizer selects
batches (Definition 5.10), and a batch is a family of pairwise compatible
enabled applications (Definition 2.6).

**What fails.** A turn carries each pose of a square to the next corner.
The move that writes the pose at a corner v reads the pose at the corner
before v, and that pose is written by another move of the same turn. So the
moves of one turn are not compatible: one of them changes a value that
another's proposal assumed. Taking every move of the open step is then not
a batch. Made one after another, the moves of a turn carry some poses more
than one corner, and the result depends on the order. A turn is a
simultaneous update from the state before the step, as the duet's two
answers are in Chapter 2.

**Proposed correction.** Either write each turn as one move, which reads
the four poses and the links of its square and writes the four poses, or
say that the moves of a step are made from the state before the step and
extend Definitions 2.6 and 5.10 to such simultaneous steps.

**In the repository.** The example of Proposition 5.36 writes each turn as
a single move. The proposition itself does not depend on this.

## F4. The empty batch and the walker's mirror (minor)

*Found 2026-10-11, while proving Proposition 5.48 (`prop:breaking`). 52nd
edition, the remark after Proposition 5.48.*

**What the book says.** "The walker at v0 is fixed by the mirror through v0
and v2, which exchanges its two moves. No batch is fixed by the mirror, so
no deterministic realizer commutes with it." Earlier, the walker is at v1 or
v3 after one tick.

**What fails.** A batch is a finite family of compatible enabled
applications (Definition 2.6). The empty family is one, and a realizer may
select it: Definition 3.28 lets a policy choose the empty batch, and
Definition 5.12 asks a well-posed realizer for a nonempty batch only where
the score demands one. The empty batch is fixed by the mirror, so the
realizer that never moves commutes with it. In general, both sides of
5.48(ii) then hold for every law.

**Proposed correction.** Say "no nonempty batch is fixed by the mirror", or
state that the walker's realizers move at every tick, for example by a score
that allows no empty batch.

**In the repository.** Laws allow the empty batch, as Definitions 2.6, 3.28
and 5.12 read. Propositions 5.47 and 5.48 are proved as printed, and their
fidelity notes point here.
