import ArtformScores.GravityBridge.Native.R7Blocks.LeadingPreparationDefs

/-! # The leading prepared graph requires a changed trace -/

namespace Artform.Scores.GravityBridge.Native.R7Blocks.Statement

/-- **GAC2:leading-preparation-trace-gap**
(the leading prepared graph requires a changed trace). -/
@[ledger "GAC2:leading-preparation-trace-gap"]
def leadingPreparationLaw : Prop :=
  ∀ (Y Z : Type) [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z],
    (∀ (S : Y →L[ℝ] Y) (N : Z →L[ℝ] Z)
    (F K : Y →L[ℝ] Z),
    blockDefect S 0 F N K = 0 ↔ K.comp S - N.comp K = F) ∧
    (∀ (S : Y →L[ℝ] Y) (N : Z →L[ℝ] Z)
    (F K : Y →L[ℝ] Z) (a d : ℝ) (_ha : 0 < a) (_hw : d ≤ ‖F‖)
    (_hS : ‖S‖ ≤ a) (_hN : ‖N‖ ≤ a) (_hK : K.comp S - N.comp K = F),
    d / (2 * a) ≤ ‖K‖) ∧
    (∀ (S : Y →L[ℝ] Y) (N : Z →L[ℝ] Z)
    (F : Y →L[ℝ] Z),
    Set.MapsTo (blockAction S 0 F N) (Set.range (graphMap (0 : Y →L[ℝ] Z)))
      (Set.range (graphMap (0 : Y →L[ℝ] Z))) ↔ F = 0) ∧
    (∀ (r : ℝ) (S : Y →L[ℝ] Y)
    (N L : Z →L[ℝ] Z) (F : Y →L[ℝ] Z)
    (_hS : S.comp S = (-r) • ContinuousLinearMap.id ℝ Y)
    (_hLB : L.comp (quadraticResolvent r N) = ContinuousLinearMap.id ℝ Z)
    (_hBL : (quadraticResolvent r N).comp L = ContinuousLinearMap.id ℝ Z)
    (_hF : F ≠ 0),
    quadraticSylvester S N L F ≠ 0)

end Artform.Scores.GravityBridge.Native.R7Blocks.Statement
