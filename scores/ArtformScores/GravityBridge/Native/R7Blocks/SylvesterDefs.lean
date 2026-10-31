import ArtformScores.GravityBridge.Stability

/-! # A two-sided quadratic-resolvent Sylvester formula -/

namespace Artform.Scores.GravityBridge.Native.R7Blocks


variable {Y Z : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

def quadraticResolvent (r : ℝ) (N : Z →L[ℝ] Z) : Z →L[ℝ] Z :=
  N.comp N + r • ContinuousLinearMap.id ℝ Z

def quadraticSylvester (S : Y →L[ℝ] Y) (N L : Z →L[ℝ] Z) (F : Y →L[ℝ] Z) :
    Y →L[ℝ] Z := -(L.comp (F.comp S + N.comp F))

noncomputable def referenceOscillator : (ℝ × ℝ) →L[ℝ] ℝ × ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    ((-14 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ)

noncomputable def referenceForcing : (ℝ × ℝ) →L[ℝ] ℝ :=
  (36 / 505 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ

noncomputable def referenceInverse : ℝ →L[ℝ] ℝ :=
  (1 / 14 : ℝ) • ContinuousLinearMap.id ℝ ℝ

end Artform.Scores.GravityBridge.Native.R7Blocks
