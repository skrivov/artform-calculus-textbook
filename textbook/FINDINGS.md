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
