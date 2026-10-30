import ArtformScores.Certificates.OneMode5
import ArtformScores.Certificates.OneMode7
import ArtformScores.Certificates.OneMode11
import ArtformScores.Certificates.OneMode13

/-!
# Completeness on one mode

T4 of the algebra of scores: on one mode over `F_p`, `p = 5, 7, 11, 13`, merging
(R1) and Whitehead's rule (R3) present `SL(2, F_p)` on `X = M(1)` and `Y = K(1)`.
Every law is the law of a word, and two words have the same law exactly when the
rules turn one into the other. Each prime has its certificate, a coset table of
`⟨X⟩` with `p² - 1` rows (`Certificates/`), which Lean checks by computation
(`OneMode.lean`).
-/

namespace Artform.Scores

open Matrix (SpecialLinearGroup)

/-- **T4** (one mode on a prime dial). -/
@[ledger "T4"]
theorem oneModeComplete : Statement.oneModeComplete := by
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact OneMode.Cert5.complete
  · exact OneMode.Cert7.complete
  · exact OneMode.Cert11.complete
  · exact OneMode.Cert13.complete

/-! ## Non-vacuity

The statement asks for nothing but one of the four primes. The running example's
prime `7`, with the book's tick at pull 3: -/

/-- The book's tick at pull 3, `K(1)` then `M(-3)`, has order 3 (T13). Over `F₇` its
word `X⁻³ Y`, cubed, has the law `1`, so the two rules turn it into the empty word. -/
example : PresentedGroup.mk (OneMode.relators 7)
      ((FreeGroup.of OneMode.Gen.X ^ (-3 : ℤ) * FreeGroup.of OneMode.Gen.Y) ^ 3) =
    PresentedGroup.mk (OneMode.relators 7) 1 := by
  refine ((oneModeComplete 7 (by decide)).2 _ _).mp ?_
  rw [map_pow, map_mul, map_zpow, OneMode.law_X, OneMode.law_Y, map_one, move_sl_zpow]
  decide

end Artform.Scores
