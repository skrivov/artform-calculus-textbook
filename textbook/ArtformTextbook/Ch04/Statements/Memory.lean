import Mathlib.Probability.ConditionalProbability
import ArtformTextbook.Ch04.Defs.Memory

/-!
# Statements of Chapter 4: records and fresh preparations (Section 4.8)

Each statement of the book is a proposition here, tagged with the book's
label. Its proof, elsewhere in the chapter's folder, is a theorem whose type
is exactly this proposition. Conditioning is Mathlib's
`ProbabilityTheory.cond`, written `P[A | E]`: the normalized restriction
`P(A ∩ E) / P(E)` of Definition 4.3. It is used here only for events `E` of
positive probability, as the definition requires.
-/

namespace Artform.Statement

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- **Proposition 4.4** (exit-level closure). Suppose that, conditional on every
positive-probability complete past, the next response pair is uniform on
`B × B`. Suppose the next exit is `x ⊕ ab`, with no further dependence on that
past, and later updates preserve the previous exit records. Then the recorded
exit process has conditional transition law `K(y | x)` of Section 4.6. Its
next-exit law given its recorded history depends only on its current exit.

The experiment is a probability space `(Ω, P)` run for `N` phrases. At the
phrase boundary `t ≤ N` the exit is `X_t = exit t`, with `X_0` the initial exit.
Before phrase `t + 1` (`t < N`) the complete past is `past t`, which takes
countably many values, and the phrase prepares the response pair
`pair t = (a, b)`. The hypotheses, in order:
* each complete past is an event, and each pair is a random variable;
* conditional on every complete past of positive probability, each of the
  four values of the next pair has probability `1/4`;
* the next exit is `X_{t+1} = X_t ⊕ ab`;
* the complete past at `t` determines `X_0, …, X_t`: it carries the current
  exit, and the records of the earlier exits survive the later updates.

The conclusions: for every recorded history `X_0 … X_t = h` of positive
probability, `P(X_{t+1} = y | X_0 … X_t = h) = K(y | h_t)`; and two recorded
histories of positive probability, of any lengths, that end in the same exit
give the same next-exit law. -/
@[book "prob:markov"]
def exitLevelClosure : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (N : ℕ)
    (S : ℕ → Type) [∀ t, Countable (S t)] (past : (t : ℕ) → Ω → S t)
    (pair : ℕ → Ω → Fin 2 × Fin 2) (exit : ℕ → Ω → Fin 2),
    (∀ t < N, ∀ σ, MeasurableSet (past t ⁻¹' {σ})) →
    (∀ t < N, Measurable (pair t)) →
    (∀ t < N, ∀ σ, P (past t ⁻¹' {σ}) ≠ 0 →
      ∀ ab, P[pair t ⁻¹' {ab} | past t ⁻¹' {σ}] = 1 / 4) →
    (∀ t < N, ∀ ω, exit (t + 1) ω = exit t ω + (pair t ω).1 * (pair t ω).2) →
    (∀ t < N, ∀ s ≤ t, ∀ ω ω', past t ω = past t ω' → exit s ω = exit s ω') →
    (∀ t < N, ∀ h : Fin (t + 1) → Fin 2, P (historyEvent exit t h) ≠ 0 →
      ∀ y, P[exit (t + 1) ⁻¹' {y} | historyEvent exit t h] =
        exitTransition y (h (Fin.last t))) ∧
    (∀ t < N, ∀ t' < N, ∀ (h : Fin (t + 1) → Fin 2) (h' : Fin (t' + 1) → Fin 2),
      P (historyEvent exit t h) ≠ 0 → P (historyEvent exit t' h') ≠ 0 →
      h (Fin.last t) = h' (Fin.last t') →
      ∀ y, P[exit (t + 1) ⁻¹' {y} | historyEvent exit t h] =
        P[exit (t' + 1) ⁻¹' {y} | historyEvent exit t' h'])

end Artform.Statement
