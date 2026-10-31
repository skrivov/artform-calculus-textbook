import ArtformScores.GravityBridge.Stability

/-! # Complete bounded graph defect with its own propagator -/

namespace Artform.Scores.GravityBridge.Native.R7Blocks


variable {Y Z : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

def graphMap (K : Y →L[ℝ] Z) : Y →L[ℝ] Y × Z := (ContinuousLinearMap.id ℝ Y).prod K

def blockAction (A11 : Y →L[ℝ] Y) (A12 : Z →L[ℝ] Y)
    (A21 : Y →L[ℝ] Z) (A22 : Z →L[ℝ] Z) : (Y × Z) →L[ℝ] Y × Z :=
  ((A11.comp (ContinuousLinearMap.fst ℝ Y Z)) +
    (A12.comp (ContinuousLinearMap.snd ℝ Y Z))).prod
    ((A21.comp (ContinuousLinearMap.fst ℝ Y Z)) +
      (A22.comp (ContinuousLinearMap.snd ℝ Y Z)))

def ownDataAction (A11 : Y →L[ℝ] Y) (A12 : Z →L[ℝ] Y) (K : Y →L[ℝ] Z) :
    Y →L[ℝ] Y := A11 + A12.comp K

def blockDefect (A11 : Y →L[ℝ] Y) (A12 : Z →L[ℝ] Y)
    (A21 : Y →L[ℝ] Z) (A22 : Z →L[ℝ] Z) (K : Y →L[ℝ] Z) : Y →L[ℝ] Z :=
  A21 + A22.comp K - K.comp (ownDataAction A11 A12 K)

end Artform.Scores.GravityBridge.Native.R7Blocks
