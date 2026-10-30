import ArtformScores.GravityBridge.Defs

/-! # The full realization defect of a bounded linear embedding -/

namespace Artform.Scores.GravityBridge

/-- The full-space failure of an embedding to realize its own visible law.
No image, recovery or physical-equivalence assumption is built into this definition. -/
def linearDefect {Y H : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (E : Y →L[ℝ] H) (R : H →L[ℝ] Y) (T : H →L[ℝ] H) : Y →L[ℝ] H :=
  T.comp E - E.comp (R.comp (T.comp E))

end Artform.Scores.GravityBridge
