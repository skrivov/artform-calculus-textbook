import ArtformScores.NonabelianGravity.BoundarySymbol
import ArtformScores.NonabelianGravity.BoundaryRotation

/-! # Binding the reciprocal symbol to the actual circle shift -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.BoundarySymbol
open Artform.Scores.GravityBridge.Native.Full40
open Artform.Scores.NonabelianGravity.Legendre (Point frameSlot connectionSlot)

abbrev CircleTime := Fin 3 × Additive Circle

noncomputable def circleStep : Fin 4 → CircleTime := twoShift (1, 0) (0, Additive.ofMul rotation)

noncomputable def circleField (n : ℤ) (u v : Point ℂ) (x : CircleTime) : Full ℂ :=
  if x.1 = 0 then
    (fun i j => ((Additive.toMul x.2 : Circle) : ℂ) ^ n * u (frameSlot i j),
     fun i a => ((Additive.toMul x.2 : Circle) : ℂ) ^ n * u (connectionSlot i a))
  else if x.1 = 1 then
    (fun i j => ((Additive.toMul x.2 : Circle) : ℂ) ^ (-n) * v (frameSlot i j),
     fun i a => ((Additive.toMul x.2 : Circle) : ℂ) ^ (-n) * v (connectionSlot i a))
  else 0

noncomputable def circleQuadratic (n : ℤ) (u v : Point ℂ) : ℂ :=
  nativeCutDensity circleStep (circleField n u v)

noncomputable def circleMixed (n : ℤ) (u v : Point ℂ) : ℂ :=
  circleQuadratic n u v - circleQuadratic n u 0 - circleQuadratic n 0 v

lemma circle_quadratic_binding (n : ℤ) (u v : Point ℂ) :
    circleQuadratic n u v = characterQuadratic (rotationValue ^ n) u v := by
  change nativeCutDensity (twoShift (1, 0) (0, Additive.ofMul rotation)) (circleField n u v) =
    nativeCutDensity (twoShift ((1, 0) : SpaceTime) (0, 1))
      (characterField (rotationValue ^ n) u v)
  apply four_corner_density
  all_goals
    apply Prod.ext <;> funext i j <;>
      simp [circleField, characterField, rotation_coe, zpow_neg]

lemma circle_mixed_formula (n : ℤ) (u v : Point ℂ) :
    circleMixed n u v = dotProduct u (mixedApply (rotationValue ^ n) v) := by
  simp only [circleMixed, circle_quadratic_binding]
  exact native_mixed_formula _ (zpow_ne_zero _ rotation_ne_zero) u v

end Artform.Scores.NonabelianGravity.BoundarySymbol
