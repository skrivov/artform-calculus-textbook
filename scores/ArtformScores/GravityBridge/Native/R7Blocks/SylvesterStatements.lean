import ArtformScores.GravityBridge.Native.R7Blocks.SylvesterDefs

/-! # A two-sided quadratic-resolvent Sylvester formula -/

namespace Artform.Scores.GravityBridge.Native.R7Blocks.Statement


/-- **GAC2:quadratic-resolvent-sylvester**
(a two-sided quadratic-resolvent sylvester formula). -/
@[ledger "GAC2:quadratic-resolvent-sylvester"]
def sylvesterLaw : Prop :=
  ∀ (Y Z : Type) [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z],
    (∀ (r : ℝ) (N : Z →L[ℝ] Z),
    (quadraticResolvent r N).comp N = N.comp (quadraticResolvent r N)) ∧
    (∀ (r : ℝ) (N L : Z →L[ℝ] Z)
    (_hLB : L.comp (quadraticResolvent r N) = ContinuousLinearMap.id ℝ Z)
    (_hBL : (quadraticResolvent r N).comp L = ContinuousLinearMap.id ℝ Z),
    N.comp L = L.comp N) ∧
    (∀ (r : ℝ) (S : Y →L[ℝ] Y) (N L : Z →L[ℝ] Z)
    (F : Y →L[ℝ] Z)
    (_hS : S.comp S = (-r) • ContinuousLinearMap.id ℝ Y)
    (_hLB : L.comp (quadraticResolvent r N) = ContinuousLinearMap.id ℝ Z)
    (_hBL : (quadraticResolvent r N).comp L = ContinuousLinearMap.id ℝ Z),
    (quadraticSylvester S N L F).comp S - N.comp (quadraticSylvester S N L F) = F) ∧
    (∀ (r : ℝ) (S : Y →L[ℝ] Y) (N L : Z →L[ℝ] Z)
    (F K : Y →L[ℝ] Z)
    (_hS : S.comp S = (-r) • ContinuousLinearMap.id ℝ Y)
    (_hLB : L.comp (quadraticResolvent r N) = ContinuousLinearMap.id ℝ Z)
    (_hK : K.comp S - N.comp K = F),
    K = quadraticSylvester S N L F) ∧
    (∀ (S : Y →L[ℝ] Y) (N L : Z →L[ℝ] Z)
    (F : Y →L[ℝ] Z),
    ‖quadraticSylvester S N L F‖ ≤ ‖L‖ * ‖F‖ * (‖S‖ + ‖N‖)) ∧
    (referenceOscillator.comp referenceOscillator =
      (-14 : ℝ) • ContinuousLinearMap.id ℝ (ℝ × ℝ) ∧
    referenceInverse.comp (quadraticResolvent 14 (0 : ℝ →L[ℝ] ℝ)) =
      ContinuousLinearMap.id ℝ ℝ ∧
    (quadraticResolvent 14 (0 : ℝ →L[ℝ] ℝ)).comp referenceInverse =
      ContinuousLinearMap.id ℝ ℝ) ∧
    (quadraticSylvester referenceOscillator 0 referenceInverse referenceForcing =
      (-18 / 3535 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ)

end Artform.Scores.GravityBridge.Native.R7Blocks.Statement
