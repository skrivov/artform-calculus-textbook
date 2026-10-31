import ArtformScores.GravityBridge.Native.R2ExceptionDefs

/-! # Complete affine-row alternatives and the retained native factor -/

namespace Artform.Scores.GravityBridge.Native.R2.Statement

/-- **GAC:r2-exception-cases** (the factor and all zero/pivot alternatives). -/
@[ledger "GAC:r2-exception-cases"]
def exceptionCases : Prop :=
  (∀ (R a G : ℝ) (i : Fin 4), remainderConst a G (rowPolys R a G i) =
    (2 - 3 * a) ^ 2 * constantQuotient R a G i) ∧
  (∀ G s : ℝ, normal (2 / 3 : ℝ) G s = 0 ↔ s = 0 ∨ s = 1 / 3 - 6 * G) ∧
  (∀ a G s : ℝ, normal a G s = 0 → 0 ≤ G → 1 / 3 < s → 2 - 3 * a ≠ 0) ∧
  (∀ R a G : ℝ, 2 - 3 * a ≠ 0 → ∀ i : Fin 4,
    remainderConst a G (rowPolys R a G i) = 0 ↔ constantQuotient R a G i = 0) ∧
  (∀ l n : Fin 4 → ℝ, (∀ i, l i = 0) → ∀ s : ℝ,
    (∀ i, l i * s + n i = 0) ↔ ∀ i, n i = 0) ∧
  (∀ (l n : Fin 4 → ℝ) (j : Fin 4), l j ≠ 0 → ∀ s : ℝ,
    (∀ i, l i * s + n i = 0) ↔
      l j * s + n j = 0 ∧ ∀ i, l j * n i - l i * n j = 0) ∧
  (∀ (l n : Fin 4 → ℝ) (Pi Lambda s : ℝ), Lambda ≠ 0 → Lambda * s = Pi →
    ((∀ i, l i * s + n i = 0) ↔ ∀ i, Pi * l i + Lambda * n i = 0))

end Artform.Scores.GravityBridge.Native.R2.Statement
